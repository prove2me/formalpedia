-- Prove2me | Definitions.Def_QMA2ClassicalSep_Main_Completion
-- name    : QMA2ClassicalSep_Main_Completion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:32.270205+00:00
-- url     : https://prove2.me/theorems/8308a86a-d996-44ef-b2b9-8aa9e35ea731
-- title:
--   Algorithm 1, the completion amplitudes $a_{D,S}(\theta)$ (Def. 6.6), the completion map $W$ and $T=J_-^\dagger WJ_+$
-- statement:
--   **Algorithm 1 (peeling).** Starting from $(E,S_{\mathrm{cur}})=(D,S)$, while some entry of $E$ can be oriented as $e=(p;x\mapsto y)$ with (1) $x_A,x_B,y_A,y_B$ distinct, (2) $y_A,y_B$ in no other entry of $E$, (3) $y_A,y_B$ with the same membership in $S_{\mathrm{cur}}$: record $(e,b_e)$ with $b_e=\mathbf 1[y_A\in S_{\mathrm{cur}}]$, remove $e$, and replace $S_{\mathrm{cur}}$ by $S_{\mathrm{cur}}\triangle\partial e$ if $b_e=1$. The output is the residual database $C$, $F=S_{\mathrm{cur}}\setminus\mathrm{coords}(C)$ and the list $L$.
--
--   **Definition 6.6.** With $\beta_\theta(x)=24/K^2$ on four-label blocks and $1-(N)_4/K^2$ on the remainder,
--   $$
--   w_e(\theta)=\frac{[y\in\mathcal B_\theta(x)]}{\sqrt{\beta_\theta(x)}},\quad \lambda_e=w_e\,s_\theta(x,y)^{b_e},\quad
--   \gamma_C=K^{v/2}\mathbf 1[\theta\in\mathcal C_C],\quad
--   \gamma_F=\sqrt{\tfrac{K^f}{(N)_{2f}}}\,\beta_\theta(F)\,\mathbf 1[\theta\in\mathcal E_F],
--   $$
--   where $v=|\mathrm{coords}(C)|$, $\mathcal C_C$ requires $c_A(x_A)=(1,2)$ and $c_B(x_B)=(3,4)$ on the coordinates of $C$, $\mathcal E_F$ requires the $2f$ labels of $F$ to be distinct and $\beta_\theta(F)$ is the sign of the permutation sorting them ($\gamma_F=1$ if $F=\emptyset$). Then $a_{D,S}(\theta)=\gamma_C\gamma_F\prod_{(e,b_e)\in L}\lambda_e$, computed from a canonical execution.
--
--   **Completion and transfer.** For admissible $(D,S)$ ($|\mathrm{coords}(D)\cup S|<N/2$), $W|D,S\rangle=\sum_{\theta\in\Theta_{\mathrm{size}}}\sqrt{\nu(\theta)}\,a_{D,S}(\theta)|\theta,D_\theta,S\rangle$, and $W|D,S\rangle=0$ otherwise (13). The transfer map is $T=J_-^\dagger WJ_+$ (22).
--
--   **Formalization Note** An execution of Algorithm 1 is the inductive relation `PeelRun`; `complAmp` uses one chosen execution, and Lemma 6.7 states that every execution gives the same value. Labels are 0-based, so $(1,2)$ and $(3,4)$ are written $(0,1)$ and $(2,3)$.
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, Section 6.3: Algorithm 1, p. 31; block hit probability, pp. 31–32; Definition 6.6, p. 32; Equation (13), p. 35; Equation (22), p. 49

import Definitions.Def_QMA2ClassicalSep_Main_Compression

set_option autoImplicit false

/-!
# Section 6.3: the peeling algorithm, completion amplitudes, the completion map `W`, and the
transfer map `T = J₋† W J₊`

Grewal, Mutreja, Tomer, *A classical oracle separation between QMA and QMA(2)*, STOC 2027
submission #618: Algorithm 1 (p. 31), the block hit probability (pp. 31–32), Definition 6.6
(p. 32), the completion map, Equation (13) (p. 35), and the transfer map, Equation (22) (p. 49).
-/

namespace QMA2ClassicalSep.Main

open Matrix

attribute [local instance] Classical.propDecidable

variable {k : ℕ}

/-! ## Algorithm 1 (peeling) -/

/-- The orientation of an entry `u = (p; x ↦ y)`: `(x, y)` if `rev = false`, `(y, x)` if
`rev = true`. -/
def orient (u : Entry k) (rev : Bool) : HVtx k × HVtx k :=
  if rev then (u.2.2, u.2.1) else (u.2.1, u.2.2)

/-- The oriented entry `e = (p; x ↦ y)` as a triple. -/
def oriented (u : Entry k) (rev : Bool) : Entry k := (u.1, orient u rev)

/-- The entry `u ∈ E`, oriented as `e = (p; x ↦ y)`, can be removed from `(E, S_cur)`:
1. `x_A, x_B, y_A, y_B` are distinct (coordinates of different sides are always distinct);
2. `y_A` and `y_B` occur in no other entry of `E`;
3. `y_A` and `y_B` have the same membership in `S_cur`. -/
def Removable (E : Finset (Entry k)) (S : Finset (HCoord k)) (u : Entry k) (rev : Bool) : Prop :=
  u ∈ E ∧ (orient u rev).1.1 ≠ (orient u rev).2.1 ∧ (orient u rev).1.2 ≠ (orient u rev).2.2 ∧
    (∀ u' ∈ E, u' ≠ u →
      Sum.inl (orient u rev).2.1 ∉ coordsE u' ∧ Sum.inr (orient u rev).2.2 ∉ coordsE u') ∧
    (Sum.inl (orient u rev).2.1 ∈ S ↔ Sum.inr (orient u rev).2.2 ∈ S)

/-- The removal bit `b_e = 1[y_A ∈ S_cur]`. -/
def removalBit (S : Finset (HCoord k)) (u : Entry k) (rev : Bool) : Bool :=
  decide (Sum.inl (orient u rev).2.1 ∈ S)

/-- An execution of Algorithm 1 from `(E, S_cur)`: `PeelRun E S L C Sf` means that the loop,
started at `(E, S)`, removes the oriented entries listed in `L` (each recorded as
`(u, rev, b_e)`) in this order and stops at `(C, Sf)`, where no entry is removable. Each step
removes `u` from `E` and replaces `S_cur` by `S_cur △ ∂e` if `b_e = 1`. -/
inductive PeelRun : Finset (Entry k) → Finset (HCoord k) → List (Entry k × Bool × Bool) →
    Finset (Entry k) → Finset (HCoord k) → Prop
  | done (E : Finset (Entry k)) (S : Finset (HCoord k)) :
      (¬ ∃ u rev, Removable E S u rev) → PeelRun E S [] E S
  | step (E : Finset (Entry k)) (S : Finset (HCoord k)) (u : Entry k) (rev : Bool)
      (L : List (Entry k × Bool × Bool)) (C : Finset (Entry k)) (Sf : Finset (HCoord k)) :
      Removable E S u rev →
      PeelRun (E.erase u) (if removalBit S u rev then symmDiff S (bdry u) else S) L C Sf →
      PeelRun E S ((u, rev, removalBit S u rev) :: L) C Sf

/-! ## Definition 6.6 -/

/-- `N = 2^k` as a natural number. -/
def NN (k : ℕ) : ℕ := 2 ^ k

/-- The block hit probability `β_θ(x)`: `24/K²` if `x` lies in a four-label block, and
`1 − (N)₄/K²` if `x ∈ 𝔅_remainder`, with `(N)₄ = N(N−1)(N−2)(N−3)`. -/
noncomputable def betaθ (θ : Labeling k) (x : HVtx k) : ℝ :=
  if FourDistinct θ x then 24 / KK k ^ 2 else 1 - ((NN k).descFactorial 4 : ℝ) / KK k ^ 2

/-- `w_e(θ) = 1[y ∈ 𝔅_θ(x)] / √β_θ(x)` for an oriented entry `x ↦ y`. -/
noncomputable def wE (θ : Labeling k) (x y : HVtx k) : ℝ :=
  if SameBlock θ x y then 1 / Real.sqrt (betaθ θ x) else 0

/-- `λ_e(θ) = w_e(θ) s_θ(x, y)^{b_e}`. -/
noncomputable def lamE (θ : Labeling k) (x y : HVtx k) (b : Bool) : ℝ :=
  wE θ x y * (if b then (sθ θ x y : ℝ) else 1)

/-- The pair-label of a coordinate (`c_A` on side `A`, `c_B` on side `B`). -/
def labelPair (θ : Labeling k) : HCoord k → LPair k
  | Sum.inl x => θ.1 x
  | Sum.inr x => θ.2 x

/-- `θ ∈ 𝒞_C`: `c_A(x_A) = (1, 2)` for every `x_A ∈ 𝒳_A` appearing in `C` and
`c_B(x_B) = (3, 4)` for every `x_B ∈ 𝒳_B` appearing in `C` (labels written 0-based). -/
def InCC (θ : Labeling k) (C : Finset (Entry k)) : Prop :=
  ∀ u ∈ coords C, match u with
    | Sum.inl x => (θ.1 x).1.val = 0 ∧ (θ.1 x).2.val = 1
    | Sum.inr x => (θ.2 x).1.val = 2 ∧ (θ.2 x).2.val = 3

/-- `γ_C(θ) = K^{v/2} 1[θ ∈ 𝒞_C]`, `v = |coords(C)|`. -/
noncomputable def gammaC (θ : Labeling k) (C : Finset (Entry k)) : ℝ :=
  KK k ^ (((coords C).card : ℝ) / 2) * (if InCC θ C then 1 else 0)

/-- The label sequence `a_{u₁}, b_{u₁}, …, a_{u_f}, b_{u_f}` of a set `F` of coordinates, for the
ordering `u₁, …, u_f` given by `F.toList` (any ordering gives the same sorting sign). -/
noncomputable def labelSeq (θ : Labeling k) (F : Finset (HCoord k)) : Fin (2 * F.card) → ℕ :=
  fun j =>
    let u := F.toList.getD (j.val / 2) (Sum.inl (fun _ => false))
    if j.val % 2 = 0 then (labelPair θ u).1.val else (labelPair θ u).2.val

/-- `γ_F(θ) = √(K^f / (N)_{2f}) β_θ(F) 1[θ ∈ ℰ_F]` (and `γ_F = 1` if `F = ∅`), where `ℰ_F`: the
`2f` labels of `F` are distinct, and `β_θ(F)` is the sign of the permutation sorting them. -/
noncomputable def gammaF (θ : Labeling k) (F : Finset (HCoord k)) : ℝ :=
  if F = ∅ then 1 else
    Real.sqrt (KK k ^ F.card / ((NN k).descFactorial (2 * F.card) : ℝ)) *
      (sortSign (labelSeq θ F) : ℝ) * (if Function.Injective (labelSeq θ F) then 1 else 0)

/-- The amplitude computed from one execution `(L, C, S_f)` of Algorithm 1:
`γ_C(θ) γ_F(θ) Π_{(e, b_e) ∈ L} λ_e(θ)`, with `F = S_f ∖ coords(C)`. -/
noncomputable def ampOfRun (θ : Labeling k) (L : List (Entry k × Bool × Bool))
    (C : Finset (Entry k)) (Sf : Finset (HCoord k)) : ℝ :=
  gammaC θ C * gammaF θ (Sf \ coords C) *
    (L.map (fun t => lamE θ (orient t.1 t.2.1).1 (orient t.1 t.2.1).2 t.2.2)).prod

/-- The completion amplitude `a_{D,S}(θ)` (Definition 6.6), computed from a canonical (chosen)
execution of Algorithm 1 on `(D, S)` (Lemma 6.7: every execution gives the same value). -/
noncomputable def complAmp (D : Finset (Entry k)) (S : Finset (HCoord k)) (θ : Labeling k) : ℝ :=
  if h : ∃ t : List (Entry k × Bool × Bool) × Finset (Entry k) × Finset (HCoord k),
      PeelRun D S t.1 t.2.1 t.2.2 then
    ampOfRun θ (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2
  else 0

/-- `(D, S)` is admissible: `|coords(D) ∪ S| < N/2`. -/
def Admissible (D : Finset (Entry k)) (S : Finset (HCoord k)) : Prop :=
  2 * (coords D ∪ S).card < NN k

/-- `ν(θ)`: the uniform product distribution of the pair-labels. -/
noncomputable def nu (k : ℕ) : ℝ := 1 / (Fintype.card (Labeling k) : ℝ)

/-- The completion map `W : Rec₊ → Rec₋`, Equation (13):
`W |D, S⟩ = Σ_{θ ∈ Θ_size} √ν(θ) a_{D,S}(θ) |θ, D_θ, S⟩` for admissible `(D, S)` and `0`
otherwise (`D_θ` has the same entries as `D`; terms with zero coefficient, in particular those
with `D` not compatible with the blocks of `θ`, are omitted). -/
noncomputable def compW : Matrix (NRec k) (YRec k) ℂ :=
  fun r' r =>
    if r'.1.2.1 = r.1.1 ∧ r'.1.2.2 = r.1.2 ∧ InThetaSize r'.1.1 ∧ Admissible r.1.1 r.1.2 then
      ((Real.sqrt (nu k) * complAmp r.1.1 r.1.2 r'.1.1 : ℝ) : ℂ)
    else 0

/-- The transfer map `T = J₋† W J₊ : ℋ₊ → ℋ₋`, Equation (22). -/
noncomputable def transferT : Matrix (NOSupp k) (YESParam k) ℂ :=
  (Matrix.conjTranspose (jN (k := k)) : Matrix (NOSupp k) (NRec k) ℂ) *
    (compW (k := k) : Matrix (NRec k) (YRec k) ℂ) * (jY (k := k) : Matrix (YRec k) (YESParam k) ℂ)

end QMA2ClassicalSep.Main


