-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Tables
-- name    : IntervalMaxCutEPTAS_Scheme_Tables
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:11.484392+00:00
-- url     : https://prove2.me/theorems/fb46ad32-13c1-446d-b7e3-41720a581b0d
-- title:
--   Allowed counts, the values val_C and the tables F_C of the dynamic program (§5.1–§5.2)
-- statement:
--   Fix the structure of §4 and $\gamma\in(0,1)$. For a group $g$, $\delta_g=\max\{1,\lfloor\gamma|g|\rfloor\}$ and the **allowed counts** are
--
--   $$D_g=\{|g|\}\cup\{j\delta_g: j\in\mathbb Z,\ 0\le j\delta_g\le|g|\}.$$
--
--   A set $S$ is **allowed** if $|S\cap g|\in D_g$ for every group. A **boundary vector** for a cell $C$ prescribes $x_g\in D_g$ for each recent group $g\in R(C)$. For an allowed $S\subseteq V_C$, $\mathrm{val}_C(S;x)$ is the number of edges of $H$ inside $V_C$ cut by $S$, plus, for each $g\in R(C)$ and each $v\in V_C$ adjacent to $g$, the number $|g|-x_g$ if $v\in S$ and $x_g$ otherwise. Then
--
--   $$F_C(x,t)=\max\{\mathrm{val}_C(S;x): S\subseteq V_C\ \text{allowed},\ |S|=t\},$$
--
--   with $F_C(x,t)=-\infty$ if there is no such $S$. The module also defines the own-group vectors $y$, $|y|$, $\mathrm{Loc}_C(x,y)$, the child boundary vectors $x^{(j)}$, and $\Delta U_j,\Delta R_j$ exactly as on PDF p. 20, which the recurrence of Lemma 5.2 combines.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §5.1–§5.2 (allowed counts, val_C, F_C, Loc_C, x^(j), ΔU_j, ΔR_j), PDF p. 19 (printed p. 18); PDF p. 20 (printed p. 19)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

open Classical

/-! # Allowed counts and the tables of the dynamic program (§5.1–§5.2)

Throughout, `γ` is the real parameter of §5 (the statements assume `γ ∈ (0, 1)`); a boundary
vector or an own-group vector is a function on group ids `Fin n → ℕ`, of which only the entries at
the relevant groups are used. -/

variable {n : ℕ} (P : Setup n) (γ : ℝ)

/-- `δ_g = max{1, ⌊γ|g|⌋}`. -/
noncomputable def delta (g : Fin n) : ℕ := max 1 ⌊γ * (gsize P g : ℝ)⌋₊

/-- The allowed counts `D_g = {|g|} ∪ {jδ_g : j ∈ ℤ, 0 ≤ jδ_g ≤ |g|}`. -/
noncomputable def Dset (g : Fin n) : Finset ℕ :=
  insert (gsize P g) ((Finset.range (gsize P g + 1)).filter (fun x => delta P γ g ∣ x))

/-- A set `S` (of retained vertices) is allowed if `|S ∩ g| ∈ D_g` for every group `g`. -/
def Allowed (S : Finset (Fin n)) : Prop :=
  ∀ g ∈ groups P, (S ∩ groupOf P g).card ∈ Dset P γ g

/-- `x` is a boundary vector for `C`: `x_g ∈ D_g` for every recent group `g ∈ R(C)`. -/
def IsBoundary (C : ℕ) (x : Fin n → ℕ) : Prop := ∀ g ∈ recent P C, x g ∈ Dset P γ g

/-- `val_C(S; x)`: the edges of `H` with both endpoints in `V_C` cut by `S`, plus, for every
`g ∈ R(C)` and every `v ∈ V_C` adjacent (in `H`) to `g`, the number `|g| − x_g` if `v ∈ S` and
`x_g` if `v ∉ S`. -/
noncomputable def val (C : ℕ) (S : Finset (Fin n)) (x : Fin n → ℕ) : ℤ :=
  (((S ×ˢ (VC P C \ S)).filter (fun p => (H P).Adj p.1 p.2)).card : ℤ) +
  ∑ g ∈ recent P C, ∑ v ∈ (VC P C).filter (fun v => (H P).Adj v g),
    (if v ∈ S then (gsize P g : ℤ) - (x g : ℤ) else (x g : ℤ))

/-- `F_C(x, t) = max{val_C(S; x) : S ⊆ V_C allowed, |S| = t}`, and `−∞` (`⊥`) if there is no
such `S`. -/
noncomputable def F (C : ℕ) (x : Fin n → ℕ) (t : ℕ) : WithBot ℤ :=
  ((Finset.univ.powerset.filter (fun S => S ⊆ VC P C ∧ Allowed P γ S ∧ S.card = t)).image
    (fun S => val P C S x)).max

/-- The vectors `y = (y_g)_{g ∈ A(C)}` of allowed counts for the own groups of `C` (extended by `0`
outside `A(C)`). -/
noncomputable def ownVecs (C : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun g => if g ∈ own P C then Dset P γ g else {0})

/-- `|y| = Σ_{g ∈ A(C)} y_g`. -/
noncomputable def ysize (C : ℕ) (y : Fin n → ℕ) : ℕ := ∑ g ∈ own P C, y g

/-- `Loc_C(x, y)`: the cut edges inside and between own groups, and between own and recent groups
(the middle sum is over unordered pairs `{g, g'} ⊆ A(C)` with `g ∼ g'`, written as `g < g'`). -/
noncomputable def Loc (C : ℕ) (x y : Fin n → ℕ) : ℤ :=
  (∑ g ∈ own P C, (y g : ℤ) * ((gsize P g : ℤ) - y g)) +
  (∑ g ∈ own P C, ∑ g' ∈ (own P C).filter (fun g' => g < g' ∧ GAdj P g g'),
    ((y g : ℤ) * ((gsize P g' : ℤ) - y g') + ((gsize P g : ℤ) - y g) * y g')) +
  (∑ g ∈ own P C, ∑ g' ∈ (recent P C).filter (fun g' => GAdj P g g'),
    ((y g : ℤ) * ((gsize P g' : ℤ) - x g') + ((gsize P g : ℤ) - y g) * x g'))

/-- `x^{(j)}`: the boundary vector for a child, `x_g` for `g ∈ R(C)` and `y_g` for `g ∈ A(C)`. -/
noncomputable def xChild (C : ℕ) (x y : Fin n → ℕ) : Fin n → ℕ :=
  fun g => if g ∈ own P C then y g else x g

/-- `ΔU_j = Σ_{g ∈ O(C_j) \ O(C)} |g|`. -/
noncomputable def dU (C C' : ℕ) : ℤ := ∑ g ∈ old P C' \ old P C, (gsize P g : ℤ)

/-- `ΔR_j = Σ_{g ∈ O(C_j) \ O(C)} x_g`. -/
noncomputable def dR (C C' : ℕ) (x : Fin n → ℕ) : ℤ := ∑ g ∈ old P C' \ old P C, (x g : ℤ)

/-- The term of the recurrence for the child `C'` of `C`:
`F_{C'}(x^{(j)}, t') + t'(ΔU_j − ΔR_j) + (W(C') − t')ΔR_j` (with `⊥ + a = ⊥`). -/
noncomputable def childTerm (C C' : ℕ) (x y : Fin n → ℕ) (t' : ℕ) : WithBot ℤ :=
  F P γ C' (xChild P C x y) t' +
    (((t' : ℤ) * (dU P C C' - dR P C C' x) + ((W P C' : ℤ) - t') * dR P C C' x : ℤ) : WithBot ℤ)

end IntervalMaxCutEPTAS.Scheme


