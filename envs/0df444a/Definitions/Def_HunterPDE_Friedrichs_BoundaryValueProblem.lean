-- Prove2me | Definitions.Def_HunterPDE_Friedrichs_BoundaryValueProblem
-- name    : HunterPDE_Friedrichs_BoundaryValueProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:55:41.848428+00:00
-- url     : https://prove2.me/theorems/e68efb08-e102-4fda-b0b3-a4e7881757bb
-- title:
--   The Friedrichs BVP (8.1): Definitions 8.1, 8.4, 8.5, 8.8, the boundary matrix (8.2) and the spaces D, D* (8.10)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be a bounded open set with $C^2$-boundary and outward unit normal $\nu$, and let $A^1,\dots,A^n, C, B_- : \mathbb{R}^n \to \mathbb{R}^{m\times m}$. The boundary value problem (8.1) is
--   $$A^i\partial_i u + Cu = f \ \text{ in } \Omega, \qquad B_- u = 0 \ \text{ on } \partial\Omega,$$
--   with **boundary matrix** (8.2) $B = \nu_i A^i$ on $\partial\Omega$.
--
--   - (Definition 8.1) The BVP is **smooth** if $\Omega$ is bounded with $C^2$-boundary, the $A^i$ are symmetric and continuously differentiable on $\overline\Omega$, $C$ is continuous on $\overline\Omega$, and $B_-$ is continuous on $\partial\Omega$.
--   - The boundary is **non-characteristic** if $B$ is nonsingular at every point of $\partial\Omega$.
--   - (Definition 8.4) The system is **positive symmetric with constant $c > 0$** if the $A^i$ are symmetric and $C + C^T - \partial_i A^i \ge 2cI$ as quadratic forms in $\Omega$.
--   - (Definition 8.5) The boundary condition is **maximally positive** if there is a matrix function $M$ on $\partial\Omega$ with $B = B_+ + B_-$, $B_+ = \tfrac12(B+M)$, $B_- = \tfrac12(B - M)$, $M + M^T \ge 0$, and $\mathbb{R}^m = \ker B_+ \oplus \ker B_-$.
--   - The spaces $D = \{u \in C^1(\overline\Omega) : B_- u = 0 \text{ on } \partial\Omega\}$ and (8.10) $D^* = \{v \in C^1(\overline\Omega) : B_+^T v = 0 \text{ on } \partial\Omega\}$, with $B_+ = B - B_-$.
--   - (Definition 8.8) For $f \in L^2(\Omega;\mathbb{R}^m)$, a function $u \in L^2(\Omega;\mathbb{R}^m)$ is a **weak solution** of (8.1) if
--   $$\int_\Omega u^T L^* v\,dx = \int_\Omega f^T v\,dx \qquad \text{for all } v \in D^* .$$
--
--   **Formalization Note.** $C^1(\overline\Omega;\mathbb{R}^m)$ and "continuously differentiable on $\overline\Omega$" are modelled by functions that are $C^1$ on all of $\mathbb{R}^n$ (for a bounded $C^2$ domain these restrict to exactly $C^1(\overline\Omega)$); only their values on $\overline\Omega$ enter. $\partial\Omega$ is `frontier Ω`, $\overline\Omega$ is `closure Ω`, and matrix inequalities are `Matrix.PosSemidef`. The printed Definition 8.5 (1) reads $B_\pm = B \pm M$ together with $B = B_+ + B_-$, which forces $B = 0$; the factor $\tfrac12$ restores Friedrichs' normalisation ($B_+ + B_- = B$, $B_+ - B_- = M$) and leaves $\ker B_\pm$, hence the boundary conditions, unchanged. `IsWeakSolution` includes $u \in L^2(\Omega)$ (`MemLp u 2`); inner products $u^Tv$ are the Euclidean `inner ℝ`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 223–227, Eq. (8.1), Eq. (8.2), Definition 8.1, Definition 8.4, Definition 8.5, Definition 8.8, Eq. (8.10)

import Mathlib
import Definitions.Def_HunterPDE_Friedrichs_SymmetricOperator
import Definitions.Def_HunterPDE_Friedrichs_C2Domain

open MeasureTheory Matrix

namespace HunterPDE.Friedrichs

/-- The boundary matrix of Hunter (8.2), `B = νᵢAⁱ` (summation over `i`), where `ν` is the
outward unit normal to `∂Ω`: `B(x) = ∑ᵢ νᵢ(x) Aⁱ(x)`. -/
noncomputable def boundaryMatrix {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ i, outwardNormal Ω x i • A i x

/-- Hunter, Definition 8.1: the BVP (8.1) `Aⁱ∂ᵢu + Cu = f` in `Ω`, `B₋u = 0` on `∂Ω` is smooth:
(1) `Ω` is bounded and has `C²`-boundary; (2) the matrices `Aⁱ` are symmetric on `Ω̄` and
continuously differentiable on `Ω̄` (modelled as `C¹` on all of `ℝⁿ`, whose restrictions to `Ω̄`
are exactly `C¹(Ω̄)` for such `Ω`), and `C` is continuous on `Ω̄`; (3) the boundary matrix `B₋` is
continuous on `∂Ω`. -/
def IsSmoothBVP {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (Bm : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  IsBoundedC2Domain Ω ∧
    (∀ i j k, ContDiff ℝ 1 (fun x => A i x j k)) ∧
    (∀ i, ∀ x ∈ closure Ω, (A i x)ᵀ = A i x) ∧
    (∀ j k, ContinuousOn (fun x => C x j k) (closure Ω)) ∧
    (∀ j k, ContinuousOn (fun x => Bm x j k) (frontier Ω))

/-- The boundary is non-characteristic (Hunter, §8.2): the boundary matrix `B = νᵢAⁱ` is
nonsingular at every point of `∂Ω`. -/
def IsNoncharacteristic {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ x ∈ frontier Ω, (boundaryMatrix Ω A x).det ≠ 0

/-- Hunter, Definition 8.4 with the constant `c` named: the system is a positive symmetric
system with constant `c > 0`, i.e. the `Aⁱ` are symmetric and (8.6)
`C + Cᵀ − ∂ᵢAⁱ ≥ 2cI` holds (as quadratic forms) at every point of `Ω`. -/
def IsPositiveSymmetric {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) (c : ℝ) : Prop :=
  0 < c ∧ (∀ i, ∀ x ∈ closure Ω, (A i x)ᵀ = A i x) ∧
    ∀ x ∈ Ω, (C x + (C x)ᵀ - (∑ i, matPd (A i) i x) - (2 * c) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef

/-- The adjoint boundary matrix `B₊ = B − B₋`, determined by the decomposition `B = B₊ + B₋` of
Hunter, Definition 8.5 (1). -/
noncomputable def Bplus {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (Bm : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin m) (Fin m) ℝ :=
  boundaryMatrix Ω A x - Bm x

/-- Hunter, Definition 8.5 (with the normalisation of (1) corrected, see the moderation notes):
the boundary condition `B₋u = 0` on `∂Ω` is maximally positive if there is a (not necessarily
symmetric) matrix function `M : ∂Ω → ℝ^{m×m}` such that at every `x ∈ ∂Ω`:
(1) `B = B₊ + B₋` with `B₊ = (B + M)/2`, `B₋ = (B − M)/2` (so `B₊ = B − B₋`, `B₊ − B₋ = M`);
(2) `M + Mᵀ ≥ 0`; (3) `ℝᵐ = ker B₊ ⊕ ker B₋`. -/
def IsMaximallyPositive {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (Bm : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ M : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ, ∀ x ∈ frontier Ω,
    Bm x = (1 / 2 : ℝ) • (boundaryMatrix Ω A x - M x) ∧
    Bplus Ω A Bm x = (1 / 2 : ℝ) • (boundaryMatrix Ω A x + M x) ∧
    (M x + (M x)ᵀ).PosSemidef ∧
    IsCompl (LinearMap.ker (Matrix.toEuclideanLin (Bplus Ω A Bm x)))
      (LinearMap.ker (Matrix.toEuclideanLin (Bm x)))

/-- The domain `D = {u ∈ C¹(Ω̄) : B₋u = 0 on ∂Ω}` of `L` (Hunter, p. 227); `C¹(Ω̄; ℝᵐ)` is
modelled by `C¹` functions on `ℝⁿ` (their restrictions to `Ω̄`). -/
def Dom {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (Bm : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) :
    Set (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :=
  {u | ContDiff ℝ 1 u ∧ ∀ x ∈ frontier Ω, mv (Bm x) (u x) = 0}

/-- The space of test functions (8.10), `D* = {v ∈ C¹(Ω̄) : B₊ᵀv = 0 on ∂Ω}`, with
`B₊ = B − B₋` the boundary matrix of Definition 8.5. -/
def Dstar {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (Bm : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) :
    Set (EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :=
  {v | ContDiff ℝ 1 v ∧ ∀ x ∈ frontier Ω, mv (Bplus Ω A Bm x)ᵀ (v x) = 0}

/-- Hunter, Definition 8.8: `u ∈ L²(Ω; ℝᵐ)` is a weak solution of (8.1) with right-hand side `f`
if `∫_Ω uᵀ L*v dx = ∫_Ω fᵀ v dx` for all `v ∈ D*`. -/
def IsWeakSolution {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C Bm : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (f u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) : Prop :=
  MemLp u 2 (volume.restrict Ω) ∧
    ∀ v ∈ Dstar Ω A Bm, ∫ x in Ω, inner ℝ (u x) (Ladj A C v x) = ∫ x in Ω, inner ℝ (f x) (v x)

end HunterPDE.Friedrichs


