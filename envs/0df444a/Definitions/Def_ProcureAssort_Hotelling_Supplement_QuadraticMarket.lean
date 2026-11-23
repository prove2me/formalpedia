-- Prove2me | Definitions.Def_ProcureAssort_Hotelling_Supplement_QuadraticMarket
-- name    : ProcureAssort_Hotelling_Supplement_QuadraticMarket
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:25:26.061825+00:00
-- url     : https://prove2.me/theorems/24846d58-824e-42c2-8201-060cde0ceeb5
-- title:
--   Quadratic representative-consumer market, demand and active-face coefficients
-- statement:
--   A finite product market has a nonnegative vector $\alpha$ and a symmetric positive definite matrix $\Gamma$ with nonpositive off-diagonal entries. Define $D=\Gamma^{-1}$ and $c=\Gamma^{-1}\alpha$. Gross consumer surplus is
--
--   $$GCS(x)=c^\top x-\tfrac12 x^\top D x.$$
--
--   Consumers maximize $GCS(x)-p^\top x$ over the unit simplex, with quantities outside the offered assortment zero. Demand is chosen by this maximization, independently of the formula to be established in Lemma G.2. Strict concavity gives a unique choice for every nonempty assortment. The active set consists of strictly positive quantities. On a fixed active face, $F=(D_Q)^{-1}$ and the equality-constrained KKT expression defines an affine function of prices. Its price coefficients are extracted by evaluating at coordinate vectors and subtracting its value at zero.
--
--   The market is defined independently of supplier ownership, for reuse on single-product and supplier-tagged product coordinates. Strict diagonal dominance is a separate predicate used only where the source assumes it. Values of the choice operation on the empty assortment are unused; no theorem assumes that an empty assortment meets unit demand.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Example 2.2 and Appendix G.1.1, pp. 10–11, 48–49

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling.Supplement

/-- A quadratic representative-consumer market, with arbitrary finite product coordinates.
This is separate from supplier ownership and from private types. Example 2.2, pp. 10–11. -/
structure QuadraticMarket (ι : Type*) where
  alpha : ι → ℝ
  gamma : Matrix ι ι ℝ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Symmetric positive definite substitution matrix and nonnegative intercepts. -/
def QuadraticMarket.Valid (M : QuadraticMarket ι) : Prop :=
  (∀ i, 0 ≤ M.alpha i) ∧ M.gamma.PosDef ∧
  (∀ i j, i ≠ j → M.gamma i j ≤ 0)

/-- Theorem 4.2's additional condition; not imposed on Theorem G.1. -/
def QuadraticMarket.StrictDD (M : QuadraticMarket ι) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, |M.gamma i j| < |M.gamma i i|

noncomputable def QuadraticMarket.D (M : QuadraticMarket ι) : Matrix ι ι ℝ := M.gamma⁻¹
noncomputable def QuadraticMarket.c (M : QuadraticMarket ι) : ι → ℝ := M.D.mulVec M.alpha

noncomputable def QuadraticMarket.gcs (M : QuadraticMarket ι) (x : ι → ℝ) : ℝ :=
  ∑ i, M.c i * x i - (∑ i, ∑ j, x i * M.D i j * x j) / 2

def productSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- Consumer optimality on the offered face of the simplex. -/
def QuadraticMarket.IsDemand (M : QuadraticMarket ι) (Q : Finset ι) (p x : ι → ℝ) : Prop :=
  x ∈ productSimplex ι ∧ (∀ i ∉ Q, x i = 0) ∧
  ∀ y ∈ productSimplex ι, (∀ i ∉ Q, y i = 0) →
    M.gcs y - ∑ i, p i * y i ≤ M.gcs x - ∑ i, p i * x i

/-- The optimizer, chosen by its defining maximization, not by the formula of Lemma G.2.
For valid markets and nonempty Q it exists uniquely. The value on Q=∅ is unused. -/
noncomputable def QuadraticMarket.demand (M : QuadraticMarket ι) (Q : Finset ι)
    (p : ι → ℝ) : ι → ℝ := Classical.epsilon (M.IsDemand Q p)

noncomputable def QuadraticMarket.active (M : QuadraticMarket ι) (p : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => 0 < M.demand Finset.univ p i)

/-- Principal submatrix of D, not the inverse of the principal submatrix of Γ. -/
noncomputable def QuadraticMarket.faceF (M : QuadraticMarket ι) (Q : Finset ι) :
    Matrix Q Q ℝ := (M.D.submatrix (fun i : Q => i.val) (fun i : Q => i.val))⁻¹

/-- The solution of the equality-constrained KKT system on a fixed face.
No positivity condition is imposed on this algebraic expression. -/
noncomputable def QuadraticMarket.faceDemand (M : QuadraticMarket ι) (Q : Finset ι)
    (p : ι → ℝ) : Q → ℝ :=
  let F := M.faceF Q
  let u : Q → ℝ := fun i => M.c i - p i
  let lam := (1 - ∑ i : Q, ∑ j : Q, F i j * u j) / (∑ i : Q, ∑ j : Q, F i j)
  fun i => ∑ j : Q, F i j * (u j + lam)

/-- The coefficient of p_j in the fixed-face affine expression, obtained by evaluation
on the coordinate vector and at zero (Definition G.2). -/
noncomputable def QuadraticMarket.faceA (M : QuadraticMarket ι) (Q : Finset ι) :
    Matrix Q Q ℝ := fun i j =>
  M.faceDemand Q (fun k => if k = j.val then 1 else 0) i - M.faceDemand Q 0 i

end ProcureAssort.Hotelling.Supplement


