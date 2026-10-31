-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P01
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T23:08:35.974751+00:00
-- url     : https://prove2.me/theorems/13e1c265-cb3c-4400-a4b2-3cbd7228bf4a
-- title:
--   Definitions for Quantum channels with polytopic images and image additivity
-- statement:
--   The objects the formalized statements of *Quantum channels with polytopic images and image additivity* (arXiv:1408.2340) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `channelImage`: §2, PDF p.2: the physical image, never the range on all operators.
--   - `IsVertex`: §3, Definition 3.1, PDF p.4: intersection of all supporting hyperplanes is a singleton. The ambient real space is the matrix space, including for non-Hermitian linear-map images. Membership and the singleton intersection imply the boundary condition in positive dimension. This is stronger than being an extreme point of a general convex set.
--   - `HasVertices`: §3, PDF pp.4–6: the displayed list is precisely the distinct extreme points of a polytope.
--   - `IsPolytopic`: §2, PDF p.3: finite convex hull, including the empty hull as a set-theoretic polytope. Positive-dimensional channel inputs always have a nonempty physical image.
--   - `affineDimension`: §3, PDF p.6: real affine dimension; used only on nonempty physical images.
--   - `compressToSubspace`: §3, PDF p.6: compression P_V A P_V, with no trace-one requirement on the result.
--   - `IsSupportedOn`: §3, PDF pp.5–6: operators in End(V), embedded in the ambient matrix algebra.
--   - `restrictedImage`: §3, PDF pp.5–6: physical image of the actual restriction of T to End(V). For V=0 the state set, hence this image, is empty.
--   - `vertexFibre`: §3, equation (8), PDF p.6: the subspace constructed from all pure preimages.
--   - `vertexSpace`: §3, PDF p.6: orthogonal sum of the vertex-fibre spaces (orthogonality is concluded).
--   - `BasisMeasurementOn`: §3, PDF pp.5–6: basis-measurement formula on End(V). No positivity of the output matrices is imposed here: the same definition is used for the explicitly announced linear-map extension. For CPTP T the basis outputs are density matrices.
--   - `CanonicalDecomposition`: Proposition 3.4, PDF pp.5–6: canonical subspaces, nonzero vertex fibres, orthogonality, full decomposition, and both identities in (7). Restrictions are applications of T itself. The identity is stated on all operators by complex-linear extension of (7).
--   - `TwoPureGeometry`: Lemma 3.2, PDF pp.4–5, including the moreover clause. Different pure states means different projectors. x_perp is a unit vector, and the formula is on every operator on H.
--   - `FibreSpanGeometry`: Corollary 3.3, PDF p.5: no independence or orthogonality assumption on the given vectors.
--   - `VertexDecompositionGeometry`: Proposition 3.4, PDF pp.5–6: the listed vertices need not exhaust the image. No polytopic-image assumption is used. k=0 is allowed.
--   - `PolytopeGeometry`: Theorem 3.5, PDF p.6: both directions. The forward direction uses canonical fibres. The converse quantifies over arbitrary nonzero orthogonal blocks, whose output list must be exactly the distinct vertices of its hull. Internal zero-dimensional residual blocks are allowed.
--   - `DimensionGeometry`: Corollary 3.6, PDF p.6: real affine dimension and both inequalities.
--   - `HasHolevoRepresentation`: Definition 2.1, PDF pp.2–3: the Holevo formula on all operators.
--   - `IsEssentialCQ`: Definition 2.1(2), PDF p.3: the norm is the spectral operator norm.
--   - `HasCQRepresentation`: Definition 2.1(3), PDF p.3: a full orthonormal-basis measurement.
--   - `cqMap`: §3, PDF p.6, and §7, PDF pp.13–14: the actual basis-measurement map.
--   - `diagonalBlockSum`: Lemma 7.2, PDF p.12: kill off-diagonal blocks, and add the channel actions on the two diagonal blocks. The sum-index register is canonically the (d1+d2)-dimensional input.
--   - `tensorOnFunctions`: Definition 6.1, PDF p.10: physical tensor action by matrix-unit expansion, including entangled inputs. It is not defined through the desired product-image hull.
--   - `IsImageAdditive`: Definition 6.1(i), PDF p.10: product-image convex hull.
--   - `IsUniversalImageAdditive`: Definition 6.1, PDF p.10: all other positive finite dimensions and all CPTP maps.
--   - `minimumOutputRenyiEntropy`: §4, PDF p.7: minimum output entropy. Used only for CPTP maps with nonempty finite input and p≥1. Then the set is nonempty and compact, the entropy is continuous and bounded, and this infimum is the attained minimum, not an empty/unbounded-set default.
--   - `conjugateMap`: §4, PDF p.8: conjugate all Kraus matrices, equivalently conjugate the input and output.
--   - `cesaroAverage`: §5, equation (14), PDF p.9: (1/N) sum of iterates numbered 1 through N. At N=0 this auxiliary average is zero; the limit is at infinity.
--   - `cesaroLimit`: §5, equation (14), PDF p.9: the actual pointwise Cesàro limit, with a default of zero only if convergence fails. Theorem 5.3 explicitly concludes convergence for every A.
--   - `fixedOperators`: §5, equation (16), PDF p.9: all fixed operators, not only fixed density matrices.
--   - `qubitDensityFromBloch`: Appendix A, PDF p.15: reuse the accepted Bloch state (I+w·sigma)/2, transporting false,true to the finite computational basis 0,1. Source correction: printed (22) is I/2 + sum w_j sigma_j; changed to (I + sum w_j sigma_j)/2, because the stated unit Bloch ball and the radii in Propositions 7.3-7.4 require the latter normalization.
--   - `blochDisc`: Proposition 7.3, PDF p.13: a filled centered disc of radius r, in any two-plane.
--   - `blochBall`: Proposition 7.4, PDF p.14: source's “sphere” is the filled Bloch ball.
--   - `qubitDepolarizing`: Proposition 7.4, PDF p.14: reuse accepted trace-linear depolarization. The accepted parameter is replacement probability; the paper uses retained-signal r.
--   - `trineVector`: §2, equation (4), PDF p.3: omega^(j+1) in its two REAL coordinates in C²; omega=exp(2*pi*i/3) is primitive, and the vectors have Euclidean norm one.
--   - `trineEffect`: §2, equation (4), PDF p.3: two-thirds of a rank-one trine projection.
--   - `trineMap`: §2, equation (4), PDF p.3: the actual M₂→M₃ example, in a chosen output basis.
--   - `trineCircle`: §2, PDF pp.3–4: the filled circle in the trace-one diagonal plane, parametrized by the two real Bloch coordinates that the trine measurement sees.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, https://arxiv.org/abs/1408.2340v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

/-!
Statements from Fukuda–Nechita–Wolf, arXiv:1408.2340v1.
All page numbers are PDF page numbers. Exact interfaces are reused from pinned accepted
library modules; new adapters and geometry are paper-local. Compilation is pending the
mechanical batch handoff.
Source correction: PDF p.7 prints +sum x log x at p=1; the reused entropy uses
-sum x log_2 x, agreeing with the stated p-to-1 limit. Independent moderation of
this existing correction remains required.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

-- Only pinned accepted-library modules are imported, under the independent-paper override.
open QAlgorithms.Papers.Independent.Information100.P44 (Mat)
open QAlgorithms.Papers.Independent.Information100.P07 (projection)
open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)
open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- §2, PDF p.2: the physical image, never the range on all operators. -/
def channelImage {I J : Type*} [Fintype I] (T : Superop I J) :
    Set (Matrix J J ℂ) := T '' {A | IsDensityMatrix A}

/-- §3, Definition 3.1, PDF p.4: intersection of all supporting hyperplanes is a singleton.
The ambient real space is the matrix space, including for non-Hermitian linear-map images.
Membership and the singleton intersection imply the boundary condition in positive dimension.
This is stronger than being an extreme point of a general convex set. -/
def IsVertex {n : ℕ} (C : Set (Mat n)) (x : Mat n) : Prop :=
  x ∈ C ∧ {y | ∀ f : Mat n →ₗ[ℝ] ℝ,
    f ≠ 0 → (∀ z ∈ C, f z ≤ f x) → f y = f x} = {x}

/-- §3, PDF pp.4–6: the displayed list is precisely the distinct extreme points of a polytope. -/
def HasVertices {n k : ℕ} (C : Set (Mat n)) (s : Fin k → Mat n) : Prop :=
  Function.Injective s ∧ C = convexHull ℝ (Set.range s) ∧
    C.extremePoints ℝ = Set.range s

/-- §2, PDF p.3: finite convex hull, including the empty hull as a set-theoretic polytope.
Positive-dimensional channel inputs always have a nonempty physical image. -/
def IsPolytopic {J : Type*} (C : Set (Matrix J J ℂ)) : Prop :=
  ∃ k : ℕ, ∃ s : Fin k → Matrix J J ℂ, C = convexHull ℝ (Set.range s)

/-- §3, PDF p.6: real affine dimension; used only on nonempty physical images. -/
def affineDimension {n : ℕ} (C : Set (Mat n)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ C).direction

/-- §3, PDF p.6: compression P_V A P_V, with no trace-one requirement on the result. -/
def compressToSubspace {d : ℕ} (V : Submodule ℂ (EuclideanSpace ℂ (Fin d))) (A : Mat d) : Mat d :=
  projection V * A * projection V

/-- §3, PDF pp.5–6: operators in End(V), embedded in the ambient matrix algebra. -/
def IsSupportedOn {d : ℕ} (V : Submodule ℂ (EuclideanSpace ℂ (Fin d))) (A : Mat d) : Prop :=
  compressToSubspace V A = A

/-- §3, PDF pp.5–6: physical image of the actual restriction of T to End(V).
For V=0 the state set, hence this image, is empty. -/
def restrictedImage {d n : ℕ} (T : Superop (Fin d) (Fin n))
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin d))) : Set (Mat n) :=
  T '' {A | IsDensityMatrix A ∧ IsSupportedOn V A}

/-- §3, equation (8), PDF p.6: the subspace constructed from all pure preimages. -/
def vertexFibre {d n : ℕ} (T : Superop (Fin d) (Fin n)) (s : Mat n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  Submodule.span ℂ {x | ‖x‖ = 1 ∧ T (pureDensity x) = s}

/-- §3, PDF p.6: orthogonal sum of the vertex-fibre spaces (orthogonality is concluded). -/
def vertexSpace {d n k : ℕ} (T : Superop (Fin d) (Fin n)) (s : Fin k → Mat n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin d)) := ⨆ i, vertexFibre T (s i)

/-- §3, PDF pp.5–6: basis-measurement formula on End(V). No positivity of the output
matrices is imposed here: the same definition is used for the explicitly announced linear-map
extension. For CPTP T the basis outputs are density matrices. -/
def BasisMeasurementOn {d n : ℕ} (T : Superop (Fin d) (Fin n))
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin d))) : Prop :=
  ∃ e : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
    ∃ s : Fin (Module.finrank ℂ V) → Mat n,
    ∀ A, IsSupportedOn V A → T A = ∑ i,
      (Matrix.trace (pureDensity (e i : EuclideanSpace ℂ (Fin d)) * A)) • s i

/-- Proposition 3.4, PDF pp.5–6: canonical subspaces, nonzero vertex fibres, orthogonality,
full decomposition, and both identities in (7). Restrictions are applications of T itself.
The identity is stated on all operators by complex-linear extension of (7). -/
def CanonicalDecomposition {d n k : ℕ} (T : Superop (Fin d) (Fin n))
    (s : Fin k → Mat n) : Prop :=
  let U := vertexFibre T ∘ s
  let V := vertexSpace T s
  (∀ i, 0 < Module.finrank ℂ (U i)) ∧
  (∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, inner ℂ x y = 0) ∧
  V ⊔ Vᗮ = ⊤ ∧ BasisMeasurementOn T V ∧
  ∀ A, T A = T (compressToSubspace V A) + T (compressToSubspace (Vᗮ) A) ∧
    T (compressToSubspace V A) = ∑ i, (Matrix.trace (projection (U i) * A)) • s i

/-- Lemma 3.2, PDF pp.4–5, including the moreover clause. Different pure states means
different projectors. x_perp is a unit vector, and the formula is on every operator on H. -/
def TwoPureGeometry {d n : ℕ} (T : Superop (Fin d) (Fin n)) : Prop :=
  ∀ x y : EuclideanSpace ℂ (Fin d), ‖x‖ = 1 → ‖y‖ = 1 → pureDensity x ≠ pureDensity y →
    IsVertex (channelImage T) (T (pureDensity x)) →
    let H := Submodule.span ℂ ({x, y} : Set (EuclideanSpace ℂ (Fin d)))
    (∃ z : EuclideanSpace ℂ (Fin d), ‖z‖ = 1 ∧ z ∈ H ∧ inner ℂ x z = 0 ∧
      ∀ A, IsSupportedOn H A → T A =
        (Matrix.trace (pureDensity x * A)) • T (pureDensity x) +
        (Matrix.trace (pureDensity z * A)) • T (pureDensity z)) ∧
    (IsVertex (channelImage T) (T (pureDensity y)) →
      T (pureDensity y) ≠ T (pureDensity x) → inner ℂ x y = 0)

/-- Corollary 3.3, PDF p.5: no independence or orthogonality assumption on the given vectors. -/
def FibreSpanGeometry {d n : ℕ} (T : Superop (Fin d) (Fin n)) : Prop :=
  ∀ (s : Mat n), IsVertex (channelImage T) s →
    ∀ (k : ℕ) (x : Fin k → EuclideanSpace ℂ (Fin d)),
    (∀ i, ‖x i‖ = 1 ∧ T (pureDensity (x i)) = s) →
    ∀ y ∈ Submodule.span ℂ (Set.range x), ‖y‖ = 1 → T (pureDensity y) = s

/-- Proposition 3.4, PDF pp.5–6: the listed vertices need not exhaust the image.
No polytopic-image assumption is used. k=0 is allowed. -/
def VertexDecompositionGeometry {d n : ℕ} (T : Superop (Fin d) (Fin n)) : Prop :=
  ∀ (k : ℕ) (s : Fin k → Mat n), Function.Injective s →
    (∀ i, IsVertex (channelImage T) (s i)) → CanonicalDecomposition T s

/-- Theorem 3.5, PDF p.6: both directions. The forward direction uses canonical fibres.
The converse quantifies over arbitrary nonzero orthogonal blocks, whose output list must be
exactly the distinct vertices of its hull. Internal zero-dimensional residual blocks are allowed. -/
def PolytopeGeometry {d n : ℕ} (T : Superop (Fin d) (Fin n)) : Prop :=
  (∀ (k : ℕ) (s : Fin k → Mat n), 0 < k → HasVertices (channelImage T) s →
    CanonicalDecomposition T s ∧
      restrictedImage T ((vertexSpace T s)ᗮ) ⊆ restrictedImage T (vertexSpace T s) ∧
      (∀ i, s i ∉ restrictedImage T ((vertexSpace T s)ᗮ))) ∧
  (∀ (k : ℕ) (s : Fin k → Mat n) (U : Fin k → Submodule ℂ (EuclideanSpace ℂ (Fin d))),
    0 < k → HasVertices (convexHull ℝ (Set.range s)) s →
    (∀ i, 0 < Module.finrank ℂ (U i)) →
    (∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, inner ℂ x y = 0) →
    let V := ⨆ i, U i
    (∀ A, T A = (∑ i, (Matrix.trace (projection (U i) * A)) • s i) +
      T (compressToSubspace (Vᗮ) A)) →
    restrictedImage T (Vᗮ) ⊆ restrictedImage T V →
    (∀ i, s i ∉ restrictedImage T (Vᗮ)) → HasVertices (channelImage T) s)

/-- Corollary 3.6, PDF p.6: real affine dimension and both inequalities. -/
def DimensionGeometry {d n : ℕ} (T : Superop (Fin d) (Fin n)) : Prop :=
  ∀ (k : ℕ) (s : Fin k → Mat n), 0 < k → HasVertices (channelImage T) s →
    affineDimension (channelImage T) ≤ k - 1 ∧ k - 1 ≤ d - 1

/-- Definition 2.1, PDF pp.2–3: the Holevo formula on all operators. -/
def HasHolevoRepresentation {I J : Type*} [Fintype I] {k : ℕ}
    (T : Superop I J) (M : Fin k → Matrix I I ℂ) (s : Fin k → Matrix J J ℂ) : Prop :=
  ∀ A, T A = ∑ i, (Matrix.trace (M i * A)) • s i

/-- Definition 2.1(2), PDF p.3: the norm is the spectral operator norm. -/
def IsEssentialCQ {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (T : Superop I J) : Prop :=
  ∃ k : ℕ, ∃ M : Fin k → Matrix I I ℂ, ∃ s : Fin k → Matrix J J ℂ,
    IsPOVM M ∧ (∀ i, specNorm (M i) = 1) ∧
    (∀ i, IsDensityMatrix (s i)) ∧ HasHolevoRepresentation T M s

/-- Definition 2.1(3), PDF p.3: a full orthonormal-basis measurement. -/
def HasCQRepresentation {d n : ℕ} (T : Superop (Fin d) (Fin n)) : Prop :=
  ∃ e : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)), ∃ s : Fin d → Mat n,
    (∀ i, IsDensityMatrix (s i)) ∧
    HasHolevoRepresentation T (fun i => pureDensity (e i)) s

/-- §3, PDF p.6, and §7, PDF pp.13–14: the actual basis-measurement map. -/
def cqMap {d n : ℕ} (e : OrthonormalBasis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)))
    (s : Fin d → Mat n) : Superop (Fin d) (Fin n) :=
  fun A => ∑ i, (Matrix.trace (pureDensity (e i) * A)) • s i

/-- Lemma 7.2, PDF p.12: kill off-diagonal blocks, and add the channel actions on the
two diagonal blocks. The sum-index register is canonically the (d1+d2)-dimensional input. -/
def diagonalBlockSum {I J K : Type*} (T : Superop I K) (S : Superop J K) :
    Superop (I ⊕ J) K :=
  fun A => T (A.submatrix Sum.inl Sum.inl) + S (A.submatrix Sum.inr Sum.inr)

/-- Definition 6.1, PDF p.10: physical tensor action by matrix-unit expansion,
including entangled inputs. It is not defined through the desired product-image hull. -/
def tensorOnFunctions {I J K L : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (T : Superop I K) (S : Superop J L) : Superop (I × J) (K × L) :=
  fun A => Matrix.of fun a b => ∑ i, ∑ j, ∑ k, ∑ l,
    A (i, k) (j, l) * T (Matrix.single i j 1) a.1 b.1 *
      S (Matrix.single k l 1) a.2 b.2

/-- Definition 6.1(i), PDF p.10: product-image convex hull. -/
def IsImageAdditive {I J K L : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (T : Superop I K) (S : Superop J L) : Prop :=
  channelImage (tensorOnFunctions T S) = convexHull ℝ
    {B | ∃ A ∈ channelImage T, ∃ C ∈ channelImage S, B = Matrix.kronecker A C}

/-- Definition 6.1, PDF p.10: all other positive finite dimensions and all CPTP maps. -/
def IsUniversalImageAdditive {d n : ℕ} (T : Superop (Fin d) (Fin n)) : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → ∀ S : Superop (Fin a) (Fin b),
    IsChannel S → IsImageAdditive T S

/-- §4, PDF p.7: minimum output entropy. Used only for CPTP maps with nonempty finite
input and p≥1. Then the set is nonempty and compact, the entropy is continuous and bounded,
and this infimum is the attained minimum, not an empty/unbounded-set default. -/
def minimumOutputRenyiEntropy {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (p : ℝ) (T : Superop I J) : ℝ :=
  sInf (renyiEntropy p '' channelImage T)

/-- §4, PDF p.8: conjugate all Kraus matrices, equivalently conjugate the input and output. -/
def conjugateMap {I J : Type*} (T : Superop I J) : Superop I J :=
  fun A => (T (A.map star)).map star

/-- §5, equation (14), PDF p.9: (1/N) sum of iterates numbered 1 through N. At N=0
this auxiliary average is zero; the limit is at infinity. -/
def cesaroAverage {d : ℕ} (T : Superop (Fin d) (Fin d)) (N : ℕ) (A : Mat d) : Mat d :=
  (N : ℂ)⁻¹ • ∑ j ∈ Finset.range N, (T^[j + 1]) A

/-- §5, equation (14), PDF p.9: the actual pointwise Cesàro limit, with a default of zero
only if convergence fails. Theorem 5.3 explicitly concludes convergence for every A. -/
def cesaroLimit {d : ℕ} (T : Superop (Fin d) (Fin d)) (A : Mat d) : Mat d :=
  if h : ∃ B, Tendsto (fun N => cesaroAverage T N A) atTop (nhds B) then h.choose else 0

/-- §5, equation (16), PDF p.9: all fixed operators, not only fixed density matrices. -/
def fixedOperators {d : ℕ} (T : Superop (Fin d) (Fin d)) : Set (Mat d) := {A | T A = A}

/-- Appendix A, PDF p.15: reuse the accepted Bloch state (I+w·sigma)/2,
transporting false,true to the finite computational basis 0,1.
Source correction: printed (22) is I/2 + sum w_j sigma_j; changed to
(I + sum w_j sigma_j)/2, because the stated unit Bloch ball and the radii
in Propositions 7.3-7.4 require the latter normalization. -/
def qubitDensityFromBloch (w : EuclideanSpace ℝ (Fin 3)) : Mat 2 :=
  (QAlgorithms.Papers.Independent.Information100.P59.blochState (fun j => w j)).submatrix
    (fun i : Fin 2 => i.val == 1) (fun i : Fin 2 => i.val == 1)

/-- Proposition 7.3, PDF p.13: a filled centered disc of radius r, in any two-plane. -/
def blochDisc (r : ℝ) (L : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) : Set (Mat 2) :=
  qubitDensityFromBloch '' {w | w ∈ L ∧ ‖w‖ ≤ r}

/-- Proposition 7.4, PDF p.14: source's “sphere” is the filled Bloch ball. -/
def blochBall (r : ℝ) : Set (Mat 2) := qubitDensityFromBloch '' {w | ‖w‖ ≤ r}

/-- Proposition 7.4, PDF p.14: reuse accepted trace-linear depolarization.
The accepted parameter is replacement probability; the paper uses retained-signal r. -/
def qubitDepolarizing (r : ℝ) : Superop (Fin 2) (Fin 2) :=
  QAlgorithms.Papers.Independent.Information100.P08.depolarizing 2 (1 - r)

/-- §2, equation (4), PDF p.3: omega^(j+1) in its two REAL coordinates in C²;
omega=exp(2*pi*i/3) is primitive, and the vectors have Euclidean norm one. -/
def trineVector (j : Fin 3) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![(Real.cos (2 * Real.pi * (j.val + 1) / 3) : ℂ),
    (Real.sin (2 * Real.pi * (j.val + 1) / 3) : ℂ)]

/-- §2, equation (4), PDF p.3: two-thirds of a rank-one trine projection. -/
def trineEffect (j : Fin 3) : Mat 2 := (2 / 3 : ℂ) • pureDensity (trineVector j)

/-- §2, equation (4), PDF p.3: the actual M₂→M₃ example, in a chosen output basis. -/
def trineMap : Superop (Fin 2) (Fin 3) :=
  fun A => ∑ j, (Matrix.trace (trineEffect j * A)) • pureDensity (ket j)

/-- §2, PDF pp.3–4: the filled circle in the trace-one diagonal plane, parametrized by
the two real Bloch coordinates that the trine measurement sees. -/
def trineCircle : Set (Mat 3) :=
  {A | ∃ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 ∧ A = Matrix.diagonal (fun j : Fin 3 =>
    ((1 / 3 + (a * Real.cos (4 * Real.pi * (j.val + 1) / 3) +
      b * Real.sin (4 * Real.pi * (j.val + 1) / 3)) / 3 : ℝ) : ℂ))}

/-! Small sanity examples pin definitions without proving any paper result. -/

example {d : ℕ} (V : Submodule ℂ (EuclideanSpace ℂ (Fin d))) : compressToSubspace V (0 : Mat d) = 0 := by
  simp [compressToSubspace]

example {d n : ℕ} (T : Superop (Fin d) (Fin n)) (A : Mat n) :
    A ∈ channelImage T ↔ ∃ B, IsDensityMatrix B ∧ T B = A := Iff.rfl

example {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) :
    renyiEntropy 1 A = vnEntropy A := by simp [renyiEntropy, vnEntropy]

example {d : ℕ} (T : Superop (Fin d) (Fin d)) (A : Mat d) :
    cesaroAverage T 0 A = 0 := by simp [cesaroAverage]

example : qubitDepolarizing 1 = (id : Superop (Fin 2) (Fin 2)) := by
  funext A
  simp [qubitDepolarizing, QAlgorithms.Papers.Independent.Information100.P08.depolarizing]

end QAlgorithms.Papers.Independent.Intakenext100.P01


