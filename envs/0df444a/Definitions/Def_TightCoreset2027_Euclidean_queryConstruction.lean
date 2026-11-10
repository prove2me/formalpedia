-- Prove2me | Definitions.Def_TightCoreset2027_Euclidean_queryConstruction
-- name    : TightCoreset2027_Euclidean_queryConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:06:37.849725+00:00
-- url     : https://prove2.me/theorems/68ac2f38-bb64-49a3-8e57-843674907ba1
-- title:
--   Separated Euclidean data and the explicit query centers
-- statement:
--   Let $n,m,L,q\ge1$ and let $(x_s,V,\ell)$ be a projection family. Use orthogonal coordinate blocks $\mathbb R^n$, $\mathbb R^m$, $\mathbb R^{2L}$ and $\mathbb R f$, with coordinate vectors $e_j,u_i,f$. For $B$ copies, set
--
--   $$p_{b,j,i,s}=20\sqrt n\,b f+\sqrt n\,e_j+u_i+x_s,\qquad X=\bigcup_{b=0}^{B-1}\{p_{b,j,i,s}\}_{j,i,s}.$$
--
--   For an active copy $b$, a direction $v$, a sign array $\sigma_{ji}\in\{-1,1\}$ and level displacements $\delta_\ell$, the local active centers are
--
--   $$c_{i,\ell}=2\sqrt n\,u_i+\sqrt n\,t_\ell v-(-1)^\ell\delta_\ell\sum_j\sigma_{ji}e_j+\lambda_\ell f,$$
--   $$\lambda_\ell=\sqrt{4n+(\sqrt n-2n)t_\ell^2-n\delta_\ell^2},\qquad D_\ell=9n+2-4\sqrt n-\sqrt n\,t_\ell^2.$$
--
--   Translate these centers by $20\sqrt n\,bf$. In each inactive copy $b'$, include the $n$ sphere centers $20\sqrt n\,b'f+\sqrt n\,e_j$. The padding centers are $20\sqrt n(B+1+r)f$ for $0\le r<k-[n(B-1)+m(L+1)]$. Their positions are independent of the active copy, direction and signs. For squared-distance queries use $B=n$ and $\delta_\ell=1/(16L^2)$.
--
--   These are the actual dataset and queries of §§2.1–2.2, with explicit allowed choices for separation and padding. No assignment, distance bound, cardinality identity or error bound is assumed in these definitions. The unique-nearest predicate asserts membership of a center and strict distance inequality against every different selected center.
--
--   **Formalization Note** The space has $n+m+2L+1$ orthogonal real coordinates, represented by a disjoint union of finite index types. A Boolean represents either sign, without restricting any sign array. Natural subtraction in the padding count is used only under the budget hypothesis; the unused over-budget definition simply has no padding. Square roots are total functions: positivity of the prescribed radicands in the source regime is an obligation of the construction's correctness, never an input assumption.
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), §§2.1–2.2, Eq. (2), (5)–(9), printed pp. 10–13 / PDF pp. 12–15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/879.pdf

import Definitions.Def_TightCoreset2027_Euclidean_coresetModel
import Definitions.Def_TightCoreset2027_Euclidean_projectionModel
open scoped BigOperators
set_option autoImplicit false

namespace TightCoreset2027.Euclidean

/-- Mutually orthogonal sphere, label, projection and norm-adjustment blocks. -/
abbrev ConstructionSpace (n m L : ℕ) :=
  EuclideanSpace ℝ (Fin n ⊕ (Fin m ⊕ (Fin (2 * L) ⊕ Unit)))

noncomputable def sphereAxis {n m L : ℕ} (j : Fin n) : ConstructionSpace n m L :=
  EuclideanSpace.single (Sum.inl j) 1

noncomputable def labelAxis {n m L : ℕ} (i : Fin m) : ConstructionSpace n m L :=
  EuclideanSpace.single (Sum.inr (Sum.inl i)) 1

noncomputable def extraAxis (n m L : ℕ) : ConstructionSpace n m L :=
  EuclideanSpace.single (Sum.inr (Sum.inr (Sum.inr ()))) 1

noncomputable def embedProjection {n m L : ℕ} (v : ProjectionSpace L) :
    ConstructionSpace n m L :=
  WithLp.toLp 2 (fun a => match a with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl h)) => v h
    | Sum.inr (Sum.inr (Sum.inr _)) => 0)

noncomputable def localPoint {n m L q : ℕ} (G : ProjectionFamily L q)
    (j : Fin n) (i : Fin m) (s : Fin q) : ConstructionSpace n m L :=
  Real.sqrt (n : ℝ) • sphereAxis j + labelAxis i + embedProjection (G.x s)

/-- Fixed before every candidate weighting and query choice. -/
noncomputable def copyTranslation (n m L b : ℕ) : ConstructionSpace n m L :=
  (20 * Real.sqrt (n : ℝ) * (b : ℝ)) • extraAxis n m L

noncomputable def dataPoint {n m L q : ℕ} (G : ProjectionFamily L q)
    (b : ℕ) (j : Fin n) (i : Fin m) (s : Fin q) : ConstructionSpace n m L :=
  copyTranslation n m L b + localPoint G j i s

noncomputable def dataCopy (n m : ℕ) {L q : ℕ} (G : ProjectionFamily L q)
    (b : ℕ) : Finset (ConstructionSpace n m L) := by
  classical
  exact Finset.univ.image (fun a : Fin n × Fin m × Fin q =>
    dataPoint G b a.1 a.2.1 a.2.2)

noncomputable def dataset (B n m : ℕ) {L q : ℕ} (G : ProjectionFamily L q) :
    Finset (ConstructionSpace n m L) := by
  classical
  exact (Finset.range B).biUnion (dataCopy n m G)

abbrev SignArray (n m : ℕ) := Fin n → Fin m → Bool

def signValue (b : Bool) : ℝ := if b then 1 else -1

noncomputable def baseline (n L : ℕ) (ℓ : Fin (L + 1)) : ℝ :=
  9 * (n : ℝ) + 2 - 4 * Real.sqrt (n : ℝ) -
    Real.sqrt (n : ℝ) * (gridValue L ℓ) ^ 2

/-- Equation (5), with a level-dependent displacement for later use in §2.5. -/
noncomputable def localCenter {n m L : ℕ} (δ : Fin (L + 1) → ℝ)
    (v : ProjectionSpace L) (σ : SignArray n m) (i : Fin m) (ℓ : Fin (L + 1)) :
    ConstructionSpace n m L :=
  (2 * Real.sqrt (n : ℝ)) • labelAxis i +
    (Real.sqrt (n : ℝ) * gridValue L ℓ) • embedProjection v -
    (((-1 : ℝ) ^ ℓ.val) * δ ℓ) •
      (∑ j : Fin n, (signValue (σ j i)) • sphereAxis j) +
    Real.sqrt (4 * (n : ℝ) + (Real.sqrt (n : ℝ) - 2 * (n : ℝ)) *
      (gridValue L ℓ) ^ 2 - (n : ℝ) * (δ ℓ) ^ 2) • extraAxis n m L

noncomputable def displacement2 (L : ℕ) : Fin (L + 1) → ℝ :=
  fun _ => 1 / (16 * (L : ℝ) ^ 2)

noncomputable def activeCenter {n m L : ℕ} (b : ℕ) (δ : Fin (L + 1) → ℝ)
    (v : ProjectionSpace L) (σ : SignArray n m) (i : Fin m) (ℓ : Fin (L + 1)) :
    ConstructionSpace n m L :=
  copyTranslation n m L b + localCenter δ v σ i ℓ

noncomputable def inactiveCenter (n m L b : ℕ) (j : Fin n) : ConstructionSpace n m L :=
  copyTranslation n m L b + Real.sqrt (n : ℝ) • sphereAxis j

/-- Fixed remote padding, common to every active copy, direction and sign array. -/
noncomputable def paddingPoint (B n m L r : ℕ) : ConstructionSpace n m L :=
  (20 * Real.sqrt (n : ℝ) * ((B + 1 + r : ℕ) : ℝ)) • extraAxis n m L

noncomputable def queryCenters (B n m L k : ℕ) (b : Fin B)
    (δ : Fin (L + 1) → ℝ) (v : ProjectionSpace L) (σ : SignArray n m) :
    Finset (ConstructionSpace n m L) := by
  classical
  exact
    (Finset.univ.image (fun a : Fin m × Fin (L + 1) =>
      activeCenter b.val δ v σ a.1 a.2)) ∪
    ((Finset.univ.filter (fun a : Fin B × Fin n => a.1 ≠ b)).image
      (fun a => inactiveCenter n m L a.1.val a.2)) ∪
    ((Finset.range (k - (n * (B - 1) + m * (L + 1)))).image
      (paddingPoint B n m L))

/-- Unique nearest center, with strict separation from every other selected center. -/
def IsUniqueNearest {E : Type*} [PseudoMetricSpace E]
    (p : E) (C : Finset E) (c : E) : Prop :=
  c ∈ C ∧ ∀ c' ∈ C, c' ≠ c → dist p c < dist p c'

end TightCoreset2027.Euclidean


