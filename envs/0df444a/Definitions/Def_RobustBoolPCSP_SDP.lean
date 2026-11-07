-- Prove2me | Definitions.Def_RobustBoolPCSP_SDP
-- name    : RobustBoolPCSP_SDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:24:22.927317+00:00
-- url     : https://prove2.me/theorems/12682f0d-28a2-450d-b7aa-0542cb3302ba
-- title:
--   Perfect basic-SDP solutions and perfect integrality gaps (Definition 3.1)
-- statement:
--   Write Boolean values in sign notation, $0\mapsto-1$, $1\mapsto+1$. A **perfect basic-SDP solution** of a signed instance assigns unit vectors $v_0$ and $v_x$ (one for each variable $x$) in a real inner-product space, and to every constraint with relation pair $(P,Q)$ of arity $r$ a probability distribution $\mu$ on $P$, such that, with $w_i$ the vector of the $i$-th literal of the scope ($v_x$ for $x$, $-v_x$ for its negation, $v_0$ for the constant $1$ and $-v_0$ for the constant $0$),
--
--   $$\mathbb E_\mu Y_i=\langle w_i,v_0\rangle,\qquad \mathbb E_\mu Y_iY_j=\langle w_i,w_j\rangle\qquad(i,j\in[r]).\qquad(7)$$
--
--   A **perfect integrality gap** for $\mathrm{fiPCSP}(\Gamma)$ is a finite signed instance that has a perfect basic-SDP solution and no assignment satisfying all its weak constraints.
--
--   The perfect gap is the obstruction on which the hardness side of the dichotomy rests.
--
--   **Formalization Note** The space is $\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`) with $d$ existential, which is equivalent because finitely many vectors span a finite-dimensional space. $\mu$ is a nonnegative function on $\{0,1\}^r$ vanishing off $P$ with total mass $1$; a constraint with $P=\emptyset$ admits none.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §3.2, Definition 3.1, p.16, display (7)

import Mathlib
import Definitions.Def_RobustBoolPCSP_Signed

set_option autoImplicit false

namespace RobustBoolPCSP

/-- Sign notation (§3.2, p.15; §4.1, p.16): `0 ↦ −1`, `1 ↦ +1`. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The vector of a literal in a basic-SDP solution (Definition 3.1, p.16): `v_x` for `x`, `−v_x` for
its negation, `v₀` for the constant `1` and `−v₀` for the constant `0`. -/
noncomputable def litVec {n d : ℕ} (v0 : EuclideanSpace ℝ (Fin d))
    (v : Fin n → EuclideanSpace ℝ (Fin d)) : Literal n → EuclideanSpace ℝ (Fin d)
  | .pos x => v x
  | .neg x => -v x
  | .one => v0
  | .zero => -v0

/-- A **perfect basic-SDP solution** of a signed instance (Definition 3.1, p.16): unit vectors `v₀`
and `v_x` in a real inner-product space and, for every constraint with pair `(P, Q)` of arity `r`, a
probability distribution `μ` on `P` (in sign notation) with
`E_μ Y_i = ⟨w_i, v₀⟩` and `E_μ Y_i Y_j = ⟨w_i, w_j⟩` for all `i, j ∈ [r]` (display (7)), where `w_i`
is the vector of the `i`-th literal of the scope.

**Formalization Note.** The space is `EuclideanSpace ℝ (Fin d)` with `d` existential; the finitely
many vectors span a finite-dimensional subspace, so this is equivalent to an arbitrary real
inner-product space. `μ` is a nonnegative function on `{0,1}^r` vanishing off `P` and summing to `1`,
one for each constraint occurrence (indexed by its position in the list); a constraint whose `P` is
empty admits no `μ`. -/
def HasPerfectSDPSol {ι : Type} {Γ : Template ι Bool Bool} (I : SignedInstance Γ) : Prop :=
  ∃ (d : ℕ) (v0 : EuclideanSpace ℝ (Fin d)) (v : Fin I.n → EuclideanSpace ℝ (Fin d)),
    ‖v0‖ = 1 ∧ (∀ x, ‖v x‖ = 1) ∧
    ∀ c ∈ I.cons, ∃ μ : (Fin (Γ.r c.1) → Bool) → ℝ,
      (∀ y, 0 ≤ μ y) ∧ (∀ y, μ y ≠ 0 → y ∈ Γ.P c.1) ∧ (∑ y, μ y = 1) ∧
      (∀ i, ∑ y, μ y * sgn (y i) = inner ℝ (litVec v0 v (c.2 i)) v0) ∧
      (∀ i j, ∑ y, μ y * (sgn (y i) * sgn (y j)) =
        inner ℝ (litVec v0 v (c.2 i)) (litVec v0 v (c.2 j)))

/-- A **perfect integrality gap** for `fiPCSP(Γ)` (Definition 3.1, p.16): "a finite signed instance
that has a perfect basic-SDP solution and no assignment satisfying all its weak constraints". -/
def IsPerfectGap {ι : Type} {Γ : Template ι Bool Bool} (I : SignedInstance Γ) : Prop :=
  HasPerfectSDPSol I ∧ ∀ b : Fin I.n → Bool, ¬ I.WeakSat b

/-- `fiPCSP(Γ)` **has a perfect integrality gap**: some signed instance of `Γ` is one. -/
def HasPerfectGap {ι : Type} (Γ : Template ι Bool Bool) : Prop :=
  ∃ I : SignedInstance Γ, IsPerfectGap I

/-- The sign vector `(sgn x_1, …, sgn x_n) ∈ {−1, 1}^n ⊆ ℝ^n` of a Boolean tuple (§4.4, p.24). -/
def sgnVec {n : ℕ} (x : Fin n → Bool) : Fin n → ℝ := fun i => sgn (x i)

end RobustBoolPCSP


