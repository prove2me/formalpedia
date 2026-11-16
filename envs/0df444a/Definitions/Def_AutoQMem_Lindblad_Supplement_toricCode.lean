-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_toricCode
-- name    : AutoQMem_Lindblad_Supplement_toricCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:42:17.16112+00:00
-- url     : https://prove2.me/theorems/31408fa4-0048-403c-96b7-ce239a3b3bef
-- title:
--   The 4D toric code of linear size $L$
-- statement:
--   Let $\Lambda=(\mathbb Z/L\mathbb Z)^4$, $L\ge1$, with unit vectors $u_0,\dots,u_3$. A **$k$-cell** is a pair $(x,S)$ with $x\in\Lambda$ and $S\subseteq\{0,1,2,3\}$, $|S|=k$: the cube spanned by $u_\mu$, $\mu\in S$, at $x$. Its codimension-one faces are $(x,S\setminus\{\mu\})$ and $(x+u_\mu,S\setminus\{\mu\})$ for $\mu\in S$. The **4D toric code** has one qubit per plaquette (2-cell), one X-check per edge (1-cell) and one Z-check per 3-cube, with
--   $$[H_Xx]_e=\sum_{i\supset e}x_i,\qquad [H_Zx]_c=\sum_{i\subset c}x_i\pmod 2 ,$$
--   so that $H_X=\partial_2$ and $H_Z^{\mathsf T}=\partial_3$ are the mod-2 boundary maps; the CSS condition $H_XH_Z^{\mathsf T}=0$ is $\partial_2\partial_3=0$.
--
--   This is the code of the synchronous 4D Toom memory (Theorem 3).
--
--   **Formalization Note** Cells are enumerated by $\mathrm{Fin}$ through fixed bijections; the number of qubits $n=6L^4$ is written $n'+1$. Faces are counted with multiplicity mod 2 (the cellular boundary), which for $L\ge3$ is the indicator of the face relation. The identity $\partial_2\partial_3=0$ is proved inside the definition.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 6.1, eq. (168), pp. 47–48 (PDF pp. 49–50)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **k-cells of the periodic 4D hypercubic lattice** `Λ = (ℤ/Lℤ)⁴` (Drechsler, Oreg, Aharonov,
*Autonomous Quantum Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of
2026-11-03), Definition 6.1, p. 47, PDF 49: "Δ_m(Λ) denote[s] the set of m-cells").

**Formalization Note.** The k-cell spanned by the unit vectors `u_μ`, `μ ∈ S`, at base point `x`
is the pair `(x, S)` with `x ∈ (ℤ/Lℤ)⁴` and `S ⊆ {0,1,2,3}`, `|S| = k`. -/
abbrev Cell (L k : ℕ) : Type := (Fin 4 → ZMod L) × {S : Finset (Fin 4) // S.card = k}

/-- The unit vector `u_μ` of `(ℤ/Lℤ)⁴`. -/
def unitVec (L : ℕ) (μ : Fin 4) : Fin 4 → ZMod L := Pi.single μ 1

/-- **Incidence coefficient mod 2 of the cubical boundary map** `∂`: the coefficient of the cell
`(y, T)` in `∂(x, S)`, where the codimension-one faces of `(x, S)` are `(x, S ∖ {μ})` and
`(x + u_μ, S ∖ {μ})` for `μ ∈ S` (Definition 6.1, eq. (168): `i ⊂ c` is the face relation).

**Formalization Note.** Faces are counted with multiplicity mod 2, as in the cellular chain complex
of the torus; for `L ≥ 3` all faces are distinct and this is the indicator of the face relation.
For `L = 1, 2` it is the mod-2 cellular boundary, which keeps `∂₂∂₃ = 0`. -/
def faceCoeff {L : ℕ} (x : Fin 4 → ZMod L) (S : Finset (Fin 4)) (y : Fin 4 → ZMod L)
    (T : Finset (Fin 4)) : ZMod 2 :=
  ∑ μ ∈ S, ((if y = x ∧ T = S.erase μ then 1 else 0) +
    (if y = x + unitVec L μ ∧ T = S.erase μ then 1 else 0))

section
variable (L : ℕ) [NeZero L]

theorem card_cell2_pos : 0 < Fintype.card (Cell L 2) :=
  Fintype.card_pos_iff.mpr ⟨(0, ⟨{0, 1}, by decide⟩)⟩

/-- `n' = n − 1` for the number `n = |Δ₂(Λ)|` of plaquettes (qubits) of the 4D toric code. -/
noncomputable def toricN' : ℕ := Fintype.card (Cell L 2) - 1

/-- Enumeration of the plaquettes (qubits) by `Fin n`. -/
noncomputable def encP : Fin (toricN' L + 1) ≃ Cell L 2 :=
  (finCongr (Nat.sub_add_cancel (card_cell2_pos L))).trans (Fintype.equivFin (Cell L 2)).symm

/-- Enumeration of the edges (X-checks) by `Fin m_X`. -/
noncomputable def encE : Fin (Fintype.card (Cell L 1)) ≃ Cell L 1 := (Fintype.equivFin _).symm

/-- Enumeration of the 3-cubes (Z-checks) by `Fin m_Z`. -/
noncomputable def encC : Fin (Fintype.card (Cell L 3)) ≃ Cell L 3 := (Fintype.equivFin _).symm

end

theorem sum_erase_symm {α : Type} [DecidableEq α] (S : Finset α) (G : α → α → ZMod 2)
    (hG : ∀ a b, G a b = G b a) : ∑ a ∈ S, ∑ b ∈ S.erase a, G a b = 0 := by
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.erase_insert hx]
    have hS : ∀ a ∈ S, ∑ b ∈ (insert x S).erase a, G a b = G a x + ∑ b ∈ S.erase a, G a b := by
      intro a ha
      have hxa : x ≠ a := fun h => hx (h ▸ ha)
      rw [Finset.erase_insert_of_ne hxa, Finset.sum_insert]
      intro hmem
      exact hx (Finset.mem_of_mem_erase hmem)
    rw [Finset.sum_congr rfl hS, Finset.sum_add_distrib, ih, add_zero, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun b _ => by rw [hG b x]; exact h2 _

theorem sum_cell_indicator {L k : ℕ} [NeZero L] (F : (Fin 4 → ZMod L) → Finset (Fin 4) → ZMod 2)
    (y : Fin 4 → ZMod L) (T : Finset (Fin 4)) (hT : T.card = k) :
    ∑ p : Cell L k, (if p.1 = y ∧ p.2.1 = T then (1 : ZMod 2) else 0) * F p.1 p.2.1 = F y T := by
  rw [Finset.sum_eq_single ((y, ⟨T, hT⟩) : Cell L k)]
  · simp
  · intro b _ hb
    have : ¬ (b.1 = y ∧ b.2.1 = T) := by
      rintro ⟨h1, h2⟩
      exact hb (Prod.ext h1 (Subtype.ext h2))
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_faceCoeff_mul {L k : ℕ} [NeZero L] (x : Fin 4 → ZMod L) (S : Finset (Fin 4))
    (hS : S.card = k + 1) (F : (Fin 4 → ZMod L) → Finset (Fin 4) → ZMod 2) :
    ∑ p : Cell L k, faceCoeff x S p.1 p.2.1 * F p.1 p.2.1 =
      ∑ μ ∈ S, (F x (S.erase μ) + F (x + unitVec L μ) (S.erase μ)) := by
  unfold faceCoeff
  simp_rw [Finset.sum_mul, add_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hc : (S.erase μ).card = k := by rw [Finset.card_erase_of_mem hμ, hS]; rfl
  rw [Finset.sum_add_distrib, sum_cell_indicator F x _ hc, sum_cell_indicator F _ _ hc]

theorem toric_css (L : ℕ) [NeZero L] :
    (Matrix.of fun (e : Fin (Fintype.card (Cell L 1))) (i : Fin (toricN' L + 1)) =>
        faceCoeff (encP L i).1 (encP L i).2.1 (encE L e).1 (encE L e).2.1) *
      (Matrix.of fun (c : Fin (Fintype.card (Cell L 3))) (i : Fin (toricN' L + 1)) =>
        faceCoeff (encC L c).1 (encC L c).2.1 (encP L i).1 (encP L i).2.1)ᵀ = 0 := by
  ext e c
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.zero_apply]
  set E := encE L e
  set Cc := encC L c
  refine (Equiv.sum_comp (encP L) (fun p : Cell L 2 =>
    faceCoeff p.1 p.2.1 E.1 E.2.1 * faceCoeff Cc.1 Cc.2.1 p.1 p.2.1)).trans ?_
  simp_rw [mul_comm (faceCoeff _ _ E.1 E.2.1)]
  rw [sum_faceCoeff_mul Cc.1 Cc.2.1 Cc.2.2 (fun y T => faceCoeff y T E.1 E.2.1)]
  set x := Cc.1
  set S := Cc.2.1
  have key := sum_erase_symm S (fun μ ν =>
      (if E.1 = x ∧ E.2.1 = (S.erase μ).erase ν then (1 : ZMod 2) else 0) +
      (if E.1 = x + unitVec L ν ∧ E.2.1 = (S.erase μ).erase ν then 1 else 0) +
      (if E.1 = x + unitVec L μ ∧ E.2.1 = (S.erase μ).erase ν then 1 else 0) +
      (if E.1 = x + unitVec L μ + unitVec L ν ∧ E.2.1 = (S.erase μ).erase ν then 1 else 0))
    (by
      intro μ ν
      rw [Finset.erase_right_comm, add_right_comm x (unitVec L μ) (unitVec L ν)]
      ring)
  rw [← key]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [faceCoeff]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- **The 4D toric code of linear size L.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories
from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Definition 6.1,
eq. (168), pp. 47–48 (PDF 49–50): "Let Λ = (ℤ/Lℤ)⁴ be the four-dimensional hypercubic lattice with
periodic boundary conditions … Bits reside on plaquettes … The X-checks are associated with edges
e ∈ Δ₁(Λ) and the Z-checks with three-cubes c ∈ Δ₃(Λ): for x ∈ 𝔽₂^{Δ₂(Λ)},
[H_X x]_e = Σ_{i⊃e} x_i (mod 2), [H_Z x]_c = Σ_{i⊂c} x_i (mod 2). The 4D toric code is the CSS
code of Definition 2.1 with these parity-check matrices."

**Formalization Note.**
* Plaquettes, edges and 3-cubes are the cells `(x, S)` of `Cell L 2`, `Cell L 1`, `Cell L 3`,
  enumerated by `Fin` through fixed equivalences (`encP`, `encE`, `encC`). Any other enumeration
  gives a code that differs by a relabelling of qubits and checks, under which every statement of
  the mission is invariant (Theorem 3 quantifies over all logical qubits and chooses decoders).
* `H_X e i = [e ⊂ i]` and `H_Z c i = [i ⊂ c]` mod 2, with faces counted with multiplicity
  (`faceCoeff`); `H_X H_Zᵀ = 0` is `∂₂∂₃ = 0`, proved here (`toric_css`).
* The code is stated for every `L ≥ 1` (`[NeZero L]`); `n = 6L⁴ ≥ 1` (here `n = toricN' L + 1`). -/
noncomputable def toricCode (L : ℕ) [NeZero L] :
    CSSCode (toricN' L + 1) (Fintype.card (Cell L 1)) (Fintype.card (Cell L 3)) where
  HX := Matrix.of fun e i => faceCoeff (encP L i).1 (encP L i).2.1 (encE L e).1 (encE L e).2.1
  HZ := Matrix.of fun c i => faceCoeff (encC L c).1 (encC L c).2.1 (encP L i).1 (encP L i).2.1
  css := toric_css L

end AutoQMem.Lindblad.Supplement


