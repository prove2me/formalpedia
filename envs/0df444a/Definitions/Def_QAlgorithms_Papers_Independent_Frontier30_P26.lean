-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P26
-- name    : QAlgorithms_Papers_Independent_Frontier30_P26
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T17:16:04.012536+00:00
-- url     : https://prove2.me/theorems/0e506088-5da9-4c98-b879-f63730f05bcc
-- title:
--   Definitions for Elements in pointed invariant cones in Lie algebras and corresponding affine pairs
-- statement:
--   The objects the formalized statements of *Elements in pointed invariant cones in Lie algebras and corresponding affine pairs* (arXiv:2110.07297) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `recession`: Translation recession directions, Definition 2.1, PDF p. 4. Empty C gives all of E.
--   - `Pointed`: Trivial recession edge, Definition 2.1, PDF p. 4; no affine lines for nonempty closed convex C.
--   - `ClosedCone`: A closed convex cone containing zero, PDF p. 3.
--   - `closedConeHull`: The smallest closed convex cone containing S, PDF pp. 2–3; empty generators give {0}.
--   - `closedConvexHull`: Closed convex hull, PDF p. 2.
--   - `translatedSubset`: Translation by x, Lemma A.3, PDF p. 28.
--   - `setSum`: Set addition without closure, PDF pp. 11, 28.
--   - `InPointedCone`: Containment in a pointed closed convex cone, Theorem 3.20(b), PDF p. 15.
--   - `BoundedBelowOn`: Existence of an actual real lower bound, Remark 3.22, PDF p. 16.
--   - `innerWord`: Finite products of inner exponential generators, PDF p. 3; negative generators give inverses. The bundled operator exponential evaluates to the same convergent series as the imported Coordinates.expAd; the bundle is needed for composition with linear functionals.
--   - `innerAdjointOrbit`: The full Inn(g)-orbit, PDF pp. 1, 3.
--   - `Invariant`: Invariance under all generators of Inn(g), PDF p. 3.
--   - `orbitHull`: co(x), the closed convex adjoint-orbit hull, PDF p. 2.
--   - `orbitCone`: C_x, the closed adjoint-orbit cone, PDF p. 2.
--   - `pointedHullElements`: g_co, equation (2), PDF p. 2.
--   - `pointedConeElements`: g_c, equation (2), PDF p. 2.
--   - `LieAdmissible`: Definition 2.2, PDF p. 4: the witness is a convex subset, not necessarily a cone.
--   - `GeneratingInvariantCone`: Pointed generating invariant cone, PDF pp. 2–3.
--   - `bracketSpan`: Real linear span of all subspace brackets, PDF pp. 25–27.
--   - `AdNilpotent`: Ad-nilpotency, including central elements, PDF pp. 8, 24.
--   - `JordanPair`: A commuting ad-semisimple/ad-nilpotent Jordan pair, PDF pp. 10, 28.
--   - `CompactlyEmbedded`: Relative compactness of the generated adjoint group, PDF p. 3. For an operator group, compact closure in End(g) agrees with compact closure in Aut(g).
--   - `CompactCartan`: Compactly embedded and maximal abelian, the Cartan convention on PDF p. 3.
--   - `Hermitian`: Hermitian condition for a noncompact simple algebra, PDF pp. 2, 9. Simplicity is stated separately.
--   - `MaximalPointedInvariantCone`: Maximal pointed invariant cone, Proposition 3.8, PDF p. 9.
--   - `MaximalCompactIdeal`: Maximal compact ideal, Proposition 3.14, PDF p. 11.
--   - `StructuralPresentation`: Internal Spindler presentation, Definition 2.4 and Theorem 2.5(a)–(d), PDF pp. 4–5. The ambient bracket, direct-sum coordinates, and bracket conditions give exactly (5). Clause (e) is not a field. All these data are existential conclusions in the structure theorem.
--   - `zPart`: The central coordinate, Theorem 3.20, PDF p. 14.
--   - `vPart`: The module coordinate, Theorem 3.20, PDF p. 14.
--   - `lPart`: The reductive coordinate, Theorem 3.20, PDF p. 14.
--   - `centralAlternatingBracket`: Central alternating bracket beta, Definition 2.4, PDF p. 4.
--   - `scalarForm`: f composed with beta, extended by central projection, PDF pp. 5, 7.
--   - `ScalarSymplectic`: Nondegeneracy on V; alternation and module invariance are inherited, PDF p. 5.
--   - `ConvexType`: Theorem 2.5(e)'s convex-type witness, PDF p. 5.
--   - `FaithfulAction`: Faithful l-action on V, subsection 3.3, PDF p. 12.
--   - `fixedSpace`: V_{x,0}, equation (8), PDF p. 7.
--   - `movingSpace`: V_x=[x,V], equation (8), PDF p. 7.
--   - `betaPerp`: beta-orthogonality inside V, Lemma 3.1(b), PDF p. 7.
--   - `scalarPerp`: Scalar symplectic orthogonality inside V, Lemma 3.1(a), PDF p. 7.
--   - `centralQuadraticCone`: Central quadratic cone C_{x,z}, Lemma 3.6, PDF p. 9.
--   - `centralHamiltonian`: One-half-normalized central Hamiltonian, Theorem 3.20, PDF p. 14.
--   - `centralHull`: Closed convex central Hamiltonian hull co_z(x), PDF p. 14.
--   - `inducedLCone`: The central-data-induced cone in l, Lemma 3.16, PDF p. 13.
--   - `extendedFunctional`: Central functional extended by central projection, Remark 3.22, PDF p. 16.
--   - `coadjointOrbit`: Full coadjoint orbit; inverse inner automorphisms give the same set, PDF p. 16.
--   - `coadjointBoundedDomain`: Pointwise semibounded domain with actual real lower bounds, PDF p. 16.
--   - `SupportedWeights`: Diagonalizability with all real weights in a specified set, PDF pp. 21–23.
--   - `EulerLinear`: Inclusive Euler convention: diagonalizable with weights in {-1,0,1}, PDF pp. 21, 23–26.
--   - `EulerElement`: Euler element in its own algebra, PDF pp. 3, 24.
--   - `canonicalDilation`: D_can(z,v,l)=(z,v/2,0), equation (21), PDF p. 19.
--   - `linearFlow`: Real exponential flow, PDF pp. 19–20.
--   - `FlowInvariant`: Invariance at every real time, PDF p. 19.
--   - `invariantConeHull`: Smallest closed convex Inn(g)-invariant cone containing the generators, Theorem 4.7, PDF p. 22.
--   - `grade`: Real eigenspace of a linear operator, PDF pp. 25–27.
--   - `LSubmodule`: A real l-submodule of V, Theorem 4.17, PDF pp. 25–26.
--   - `EulerModuleSplit`: V_h=V_h^+⊕V_h^-, Theorem 4.17, PDF pp. 25–26.
--   - `ThreeIndependent`: Directness of a sum of three real subspaces, Theorem 4.17(c), PDF p. 26.
--   - `idealGeneratedBy`: Ideal in l generated by h, Remark 4.16, PDF p. 25.
--   - `gradedGeneratedAlgebra`: Subalgebra generated by the ±1 eigenspaces, Remark 4.16, PDF p. 25.
--   - `ConstructedEuler`: The actual constructed derivation of the proof of Lemma 4.15, PDF p. 25. Its actions on the direct module summands and the three central bracket spaces fix it uniquely; this is not an arbitrary extension of ad_l(h).
--   - `TubeType`: Tube-type condition for a simple hermitian real Lie algebra: a nonzero three-grading element. This algebraic characterization is stated in Oeh, arXiv:2007.13445v1, Section 2.2, and used in the present paper, Remark 4.10, PDF p. 23.
--   - `effectiveSpace`: Effective subspace span(s.V), Lemma 4.6, PDF p. 21.
--   - `fixedModuleSpace`: Fixed subspace V_fix,s, Lemma 4.6, PDF p. 21.
--   - `StableUnder`: Invariance of a subspace under a subalgebra action, Lemma 4.6, PDF p. 21.
--   - `ConvexSymplecticModule`: Symplectic l-module of convex type, as in Theorem 2.5(e) and Lemma 4.6, PDF pp. 5, 21.
-- source:
--   Elements in pointed invariant cones in Lie algebras and corresponding affine pairs, arXiv:2110.07297v1, https://arxiv.org/abs/2110.07297v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

/-! Neeb–Oeh, arXiv:2110.07297v1. Paper-local definitions; compilation pending batch handoff. -/
namespace QAlgorithms.Papers.Independent.Frontier30.P26

noncomputable section
open Set
open QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates (expAd)
attribute [local instance 100] LieRing.ofAssociativeRing

section Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translation recession directions, Definition 2.1, PDF p. 4. Empty C gives all of E. -/
def recession (C : Set E) : Set E := {v | ∀ c ∈ C, c + v ∈ C}

/-- Trivial recession edge, Definition 2.1, PDF p. 4; no affine lines for nonempty closed convex C. -/
def Pointed (C : Set E) : Prop := ∀ v ∈ recession C, -v ∈ recession C → v = 0

/-- A closed convex cone containing zero, PDF p. 3. -/
def ClosedCone (C : Set E) : Prop :=
  IsClosed C ∧ Convex ℝ C ∧ (0 : E) ∈ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x ∈ C, t • x ∈ C

/-- The smallest closed convex cone containing S, PDF pp. 2–3; empty generators give {0}. -/
def closedConeHull (S : Set E) : Set E := ⋂₀ {C : Set E | ClosedCone C ∧ S ⊆ C}

/-- Closed convex hull, PDF p. 2. -/
def closedConvexHull (S : Set E) : Set E := closure (convexHull ℝ S)

/-- Translation by x, Lemma A.3, PDF p. 28. -/
def translatedSubset (x : E) (C : Set E) : Set E := (fun c => x + c) '' C

/-- Set addition without closure, PDF pp. 11, 28. -/
def setSum (C D : Set E) : Set E := {x | ∃ c ∈ C, ∃ d ∈ D, x = c + d}

/-- Containment in a pointed closed convex cone, Theorem 3.20(b), PDF p. 15. -/
def InPointedCone (S : Set E) : Prop := ∃ C : Set E, ClosedCone C ∧ Pointed C ∧ S ⊆ C

/-- Existence of an actual real lower bound, Remark 3.22, PDF p. 16. -/
def BoundedBelowOn (f : E → ℝ) (S : Set E) : Prop := ∃ b : ℝ, ∀ x ∈ S, b ≤ f x

example (S : Set E) : (0 : E) ∈ closedConeHull S := by
  apply Set.mem_sInter.mpr
  intro C hC
  exact hC.1.2.2.1

example : Pointed ({0} : Set E) := by
  intro v hv _
  have h := hv 0 (by simp)
  simpa using h

example : recession (∅ : Set E) = Set.univ := by
  ext v
  simp [recession]

end Geometry

/-- A finite-basis norm induced from the given Lie algebra's actual additive group, PDF p. 3.
This prevents a second unrelated additive structure from entering the topological definitions. -/
local instance lieNormedGroup (G : Type*) [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G] :
    NormedAddCommGroup G :=
  NormedAddCommGroup.induced G (Fin (Module.finrank ℝ G) → ℝ)
    (Module.finBasis ℝ G).equivFun.toLinearMap (Module.finBasis ℝ G).equivFun.injective

/-- The induced norm uses the given real scalar action; all finite-dimensional real norms give
its usual Hausdorff vector-space topology, PDF p. 3. -/
local instance lieNormedSpace (G : Type*) [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G] :
    NormedSpace ℝ G :=
  NormedSpace.induced ℝ G (Fin (Module.finrank ℝ G) → ℝ) (Module.finBasis ℝ G).equivFun.toLinearMap

section LieGeometry
variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Finite products of inner exponential generators, PDF p. 3; negative generators give inverses.
The bundled operator exponential evaluates to the same convergent series as the imported
Coordinates.expAd; the bundle is needed for composition with linear functionals. -/
def innerWord (ys : List G) : G →L[ℝ] G :=
  ys.foldr (fun y T =>
    (NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ G y))).comp T)
    (ContinuousLinearMap.id ℝ G)

/-- The full Inn(g)-orbit, PDF pp. 1, 3. -/
def innerAdjointOrbit (x : G) : Set G := {y | ∃ ys : List G, innerWord ys x = y}

/-- Invariance under all generators of Inn(g), PDF p. 3. -/
def Invariant (C : Set G) : Prop := ∀ y : G, expAd y '' C = C

/-- co(x), the closed convex adjoint-orbit hull, PDF p. 2. -/
def orbitHull (x : G) : Set G := closedConvexHull (innerAdjointOrbit x)

/-- C_x, the closed adjoint-orbit cone, PDF p. 2. -/
def orbitCone (x : G) : Set G := closedConeHull (innerAdjointOrbit x)

/-- g_co, equation (2), PDF p. 2. -/
def pointedHullElements : Set G := {x | Pointed (orbitHull x)}

/-- g_c, equation (2), PDF p. 2. -/
def pointedConeElements : Set G := {x | Pointed (orbitCone x)}

/-- Definition 2.2, PDF p. 4: the witness is a convex subset, not necessarily a cone. -/
def LieAdmissible : Prop :=
  ∃ C : Set G, IsClosed C ∧ Convex ℝ C ∧ Pointed C ∧ Invariant C ∧ Submodule.span ℝ C = ⊤

/-- Pointed generating invariant cone, PDF pp. 2–3. -/
def GeneratingInvariantCone (C : Set G) : Prop :=
  ClosedCone C ∧ Pointed C ∧ Invariant C ∧ Submodule.span ℝ C = ⊤

/-- Real linear span of all subspace brackets, PDF pp. 25–27. -/
def bracketSpan (A B : Submodule ℝ G) : Submodule ℝ G :=
  Submodule.span ℝ {x | ∃ a ∈ A, ∃ b ∈ B, x = ⁅a, b⁆}

/-- Ad-nilpotency, including central elements, PDF pp. 8, 24. -/
def AdNilpotent (x : G) : Prop := IsNilpotent (LieAlgebra.ad ℝ G x)

/-- A commuting ad-semisimple/ad-nilpotent Jordan pair, PDF pp. 10, 28. -/
def JordanPair (xs xn : G) : Prop :=
  (LieAlgebra.ad ℝ G xs).IsSemisimple ∧ AdNilpotent xn ∧ ⁅xs, xn⁆ = 0

/-- Relative compactness of the generated adjoint group, PDF p. 3.
For an operator group, compact closure in End(g) agrees with compact closure in Aut(g). -/
def CompactlyEmbedded (S : Set G) : Prop :=
  IsCompact (closure {T : G →L[ℝ] G | ∃ ys : List G,
    (∀ y ∈ ys, y ∈ S) ∧ T = innerWord ys})

/-- Compactly embedded and maximal abelian, the Cartan convention on PDF p. 3. -/
def CompactCartan (T : LieSubalgebra ℝ G) : Prop :=
  CompactlyEmbedded (T : Set G) ∧ (∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ = 0) ∧
  ∀ x : G, (∀ y ∈ T, ⁅x, y⁆ = 0) → x ∈ T

/-- Hermitian condition for a noncompact simple algebra, PDF pp. 2, 9. Simplicity is stated separately. -/
def Hermitian : Prop :=
  ¬ CompactlyEmbedded (Set.univ : Set G) ∧
  ∃ K : LieSubalgebra ℝ G, CompactlyEmbedded (K : Set G) ∧
    (∀ K' : LieSubalgebra ℝ G, CompactlyEmbedded (K' : Set G) → K ≤ K' → K' ≤ K) ∧
    ∃ z : K, z ≠ 0 ∧ ∀ y : K, ⁅z, y⁆ = 0

/-- Maximal pointed invariant cone, Proposition 3.8, PDF p. 9. -/
def MaximalPointedInvariantCone (W : Set G) : Prop :=
  ClosedCone W ∧ Pointed W ∧ Invariant W ∧
  ∀ C : Set G, ClosedCone C → Pointed C → Invariant C → W ⊆ C → C ⊆ W

/-- Maximal compact ideal, Proposition 3.14, PDF p. 11. -/
def MaximalCompactIdeal (K : LieIdeal ℝ G) : Prop :=
  CompactlyEmbedded (K : Set G) ∧ ∀ I : LieIdeal ℝ G, CompactlyEmbedded (I : Set G) → I ≤ K

example (x : G) : x ∈ innerAdjointOrbit x := ⟨[], rfl⟩

example (y x : G) : innerWord [y] x =
    NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ G y)) x := rfl

end LieGeometry

section Presentations
variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Internal Spindler presentation, Definition 2.4 and Theorem 2.5(a)–(d), PDF pp. 4–5.
The ambient bracket, direct-sum coordinates, and bracket conditions give exactly (5).
Clause (e) is not a field. All these data are existential conclusions in the structure theorem. -/
structure StructuralPresentation where
  L : LieSubalgebra ℝ G
  V : Submodule ℝ G
  coordinates : G ≃ₗ[ℝ] ((LieAlgebra.center ℝ G) × (V × L))
  reconstruct : ∀ x : G, ((coordinates x).1 : G) + ((coordinates x).2.1 : G) + ((coordinates x).2.2 : G) = x
  v_bracket : ∀ v w : V, ⁅(v : G), (w : G)⁆ ∈ LieAlgebra.center ℝ G
  lv_bracket : ∀ l : L, ∀ v : V, ⁅(l : G), (v : G)⁆ ∈ V
  U : LieIdeal ℝ G
  u_space : U.toSubmodule = (LieAlgebra.center ℝ G).toSubmodule ⊔ V
  u_nilpotent : LieRing.IsNilpotent U
  u_maximal : ∀ I : LieIdeal ℝ G, LieRing.IsNilpotent I → I ≤ U
  l_reductive : LieAlgebra.HasCentralRadical ℝ L
  l_quasihermitian : ∀ I : LieIdeal ℝ L, LieAlgebra.IsSimple ℝ I →
    CompactlyEmbedded (Set.univ : Set I) ∨ Hermitian (G := I)
  TL : LieSubalgebra ℝ G
  tl_le : TL ≤ L
  tl_compact : CompactlyEmbedded (TL : Set G)
  tl_abelian : ∀ a ∈ TL, ∀ b ∈ TL, ⁅a, b⁆ = 0
  tl_maximal : ∀ a ∈ L, (∀ b ∈ TL, ⁅a, b⁆ = 0) → a ∈ TL
  T : LieSubalgebra ℝ G
  t_space : T.toSubmodule = (LieAlgebra.center ℝ G).toSubmodule ⊔ TL.toSubmodule
  t_cartan : CompactCartan T
  v_tu : V = bracketSpan T.toSubmodule U.toSubmodule
  v_tlv : V = bracketSpan TL.toSubmodule V

/-- The central coordinate, Theorem 3.20, PDF p. 14. -/
def zPart (P : StructuralPresentation (G := G)) (x : G) : G := (P.coordinates x).1

/-- The module coordinate, Theorem 3.20, PDF p. 14. -/
def vPart (P : StructuralPresentation (G := G)) (x : G) : G := (P.coordinates x).2.1

/-- The reductive coordinate, Theorem 3.20, PDF p. 14. -/
def lPart (P : StructuralPresentation (G := G)) (x : G) : G := (P.coordinates x).2.2

/-- Central alternating bracket beta, Definition 2.4, PDF p. 4. -/
def centralAlternatingBracket (P : StructuralPresentation (G := G)) (v w : P.V) : LieAlgebra.center ℝ G :=
  ⟨⁅(v : G), (w : G)⁆, P.v_bracket v w⟩

/-- f composed with beta, extended by central projection, PDF pp. 5, 7. -/
def scalarForm (P : StructuralPresentation (G := G))
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) (v w : G) : ℝ := f (P.coordinates ⁅v, w⁆).1

/-- Nondegeneracy on V; alternation and module invariance are inherited, PDF p. 5. -/
def ScalarSymplectic (P : StructuralPresentation (G := G))
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) : Prop :=
  ∀ v ∈ P.V, (∀ w ∈ P.V, scalarForm P f v w = 0) → v = 0

/-- Theorem 2.5(e)'s convex-type witness, PDF p. 5. -/
def ConvexType (P : StructuralPresentation (G := G)) : Prop :=
  ∃ f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ, ScalarSymplectic P f ∧
    ∃ x ∈ P.L, ∀ v ∈ P.V, v ≠ 0 → 0 < scalarForm P f ⁅x, v⁆ v

/-- Faithful l-action on V, subsection 3.3, PDF p. 12. -/
def FaithfulAction (P : StructuralPresentation (G := G)) : Prop :=
  ∀ x ∈ P.L, (∀ v ∈ P.V, ⁅x, v⁆ = 0) → x = 0

/-- V_{x,0}, equation (8), PDF p. 7. -/
def fixedSpace (P : StructuralPresentation (G := G)) (x : G) : Submodule ℝ G :=
  P.V ⊓ (LieAlgebra.ad ℝ G x).ker

/-- V_x=[x,V], equation (8), PDF p. 7. -/
def movingSpace (P : StructuralPresentation (G := G)) (x : G) : Submodule ℝ G :=
  P.V.map (LieAlgebra.ad ℝ G x)

/-- beta-orthogonality inside V, Lemma 3.1(b), PDF p. 7. -/
def betaPerp (P : StructuralPresentation (G := G)) (S : Submodule ℝ G) : Set G :=
  {v | v ∈ P.V ∧ ∀ w ∈ S, ⁅v, w⁆ = 0}

/-- Scalar symplectic orthogonality inside V, Lemma 3.1(a), PDF p. 7. -/
def scalarPerp (P : StructuralPresentation (G := G))
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) (S : Submodule ℝ G) : Set G :=
  {v | v ∈ P.V ∧ ∀ w ∈ S, scalarForm P f v w = 0}

/-- Central quadratic cone C_{x,z}, Lemma 3.6, PDF p. 9. -/
def centralQuadraticCone (P : StructuralPresentation (G := G)) (x : G) : Set G :=
  closedConeHull (Set.range fun v : P.V => ⁅(v : G), ⁅(v : G), lPart P x⁆⁆)

/-- One-half-normalized central Hamiltonian, Theorem 3.20, PDF p. 14. -/
def centralHamiltonian (P : StructuralPresentation (G := G)) (x : G) (v : P.V) : G :=
  zPart P x + ⁅(v : G), vPart P x⁆ + (1 / 2 : ℝ) • ⁅(v : G), ⁅(v : G), lPart P x⁆⁆

/-- Closed convex central Hamiltonian hull co_z(x), PDF p. 14. -/
def centralHull (P : StructuralPresentation (G := G)) (x : G) : Set G :=
  closedConvexHull (Set.range (centralHamiltonian P x))

/-- The central-data-induced cone in l, Lemma 3.16, PDF p. 13. -/
def inducedLCone (P : StructuralPresentation (G := G)) (Cz : Set G) : Set P.L :=
  {x | ∀ v : P.V, ⁅(v : G), ⁅(v : G), (x : G)⁆⁆ ∈ Cz}

example (P : StructuralPresentation (G := G)) (x : G) :
    zPart P x + vPart P x + lPart P x = x := P.reconstruct x

example (P : StructuralPresentation (G := G)) (x : G) : centralHamiltonian P x 0 = zPart P x := by
  simp [centralHamiltonian]

/-- Central functional extended by central projection, Remark 3.22, PDF p. 16. -/
def extendedFunctional (P : StructuralPresentation (G := G))
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) : G →ₗ[ℝ] ℝ :=
  f.comp ((LinearMap.fst ℝ (LieAlgebra.center ℝ G) (P.V × P.L)).comp P.coordinates.toLinearMap)

/-- Full coadjoint orbit; inverse inner automorphisms give the same set, PDF p. 16. -/
def coadjointOrbit (F : G →ₗ[ℝ] ℝ) : Set (G →ₗ[ℝ] ℝ) :=
  {H | ∃ ys : List G, H = F.comp (innerWord ys).toLinearMap}

/-- Pointwise semibounded domain with actual real lower bounds, PDF p. 16. -/
def coadjointBoundedDomain (F : G →ₗ[ℝ] ℝ) : Set G :=
  {x | ∃ b : ℝ, ∀ H ∈ coadjointOrbit F, b ≤ H x}

end Presentations

section Derivations
variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Diagonalizability with all real weights in a specified set, PDF pp. 21–23. -/
def SupportedWeights (A : G →ₗ[ℝ] G) (weights : Set ℝ) : Prop :=
  Submodule.span ℝ {v | ∃ a ∈ weights, A v = a • v} = ⊤

/-- Inclusive Euler convention: diagonalizable with weights in {-1,0,1}, PDF pp. 21, 23–26. -/
def EulerLinear (A : G →ₗ[ℝ] G) : Prop := SupportedWeights A ({-1, 0, 1} : Set ℝ)

/-- Euler element in its own algebra, PDF pp. 3, 24. -/
def EulerElement (h : G) : Prop := EulerLinear (LieAlgebra.ad ℝ G h)

/-- D_can(z,v,l)=(z,v/2,0), equation (21), PDF p. 19. -/
def canonicalDilation (P : StructuralPresentation (G := G)) : G →ₗ[ℝ] G :=
  (LieAlgebra.center ℝ G).toSubmodule.subtype.comp
    ((LinearMap.fst ℝ (LieAlgebra.center ℝ G) (P.V × P.L)).comp P.coordinates.toLinearMap) +
  (1 / 2 : ℝ) • P.V.subtype.comp
    ((LinearMap.fst ℝ P.V P.L).comp
      ((LinearMap.snd ℝ (LieAlgebra.center ℝ G) (P.V × P.L)).comp P.coordinates.toLinearMap))

/-- Real exponential flow, PDF pp. 19–20. -/
def linearFlow (A : G →ₗ[ℝ] G) (t : ℝ) : G →L[ℝ] G :=
  NormedSpace.exp (t • LinearMap.toContinuousLinearMap A)

/-- Invariance at every real time, PDF p. 19. -/
def FlowInvariant (A : G →ₗ[ℝ] G) (C : Set G) : Prop := ∀ t : ℝ, linearFlow A t '' C = C

/-- Smallest closed convex Inn(g)-invariant cone containing the generators, Theorem 4.7, PDF p. 22. -/
def invariantConeHull (S : Set G) : Set G := ⋂₀ {C : Set G | ClosedCone C ∧ Invariant C ∧ S ⊆ C}

/-- Real eigenspace of a linear operator, PDF pp. 25–27. -/
def grade (A : G →ₗ[ℝ] G) (a : ℝ) : Submodule ℝ G := (A - a • LinearMap.id).ker

/-- A real l-submodule of V, Theorem 4.17, PDF pp. 25–26. -/
def LSubmodule (P : StructuralPresentation (G := G)) (S : Submodule ℝ G) : Prop :=
  S ≤ P.V ∧ ∀ l ∈ P.L, ∀ v ∈ S, ⁅l, v⁆ ∈ S

/-- V_h=V_h^+⊕V_h^-, Theorem 4.17, PDF pp. 25–26. -/
def EulerModuleSplit (P : StructuralPresentation (G := G)) (h : G) (A B : Submodule ℝ G) : Prop :=
  LSubmodule P A ∧ LSubmodule P B ∧ Disjoint A B ∧ A ⊔ B = movingSpace P h

/-- Directness of a sum of three real subspaces, Theorem 4.17(c), PDF p. 26. -/
def ThreeIndependent (A B C : Submodule ℝ G) : Prop := Disjoint A (B ⊔ C) ∧ Disjoint B C

example : EulerLinear (0 : G →ₗ[ℝ] G) := by
  apply top_unique
  intro x _
  apply Submodule.subset_span
  exact ⟨0, by simp, by simp⟩

example (P : StructuralPresentation (G := G)) : canonicalDilation P 0 = 0 := map_zero _

/-- Ideal in l generated by h, Remark 4.16, PDF p. 25. -/
def idealGeneratedBy (h : G) : LieIdeal ℝ G := sInf {I : LieIdeal ℝ G | h ∈ I}

/-- Subalgebra generated by the ±1 eigenspaces, Remark 4.16, PDF p. 25. -/
def gradedGeneratedAlgebra (D : LieDerivation ℝ G G) : LieSubalgebra ℝ G :=
  LieSubalgebra.lieSpan ℝ G ((grade D.toLinearMap 1 : Set G) ∪ (grade D.toLinearMap (-1) : Set G))

/-- The actual constructed derivation of the proof of Lemma 4.15, PDF p. 25.
Its actions on the direct module summands and the three central bracket spaces fix it uniquely;
this is not an arbitrary extension of ad_l(h). -/
def ConstructedEuler (P : StructuralPresentation (G := G)) (h : P.L)
    (A B : Submodule ℝ G) (D : LieDerivation ℝ G G) : Prop :=
  (∀ l ∈ P.L, D l = ⁅(h : G), l⁆) ∧
  (∀ v ∈ A, D v = ⁅(h : G), v⁆ + (1 / 2 : ℝ) • v) ∧
  (∀ v ∈ B, D v = ⁅(h : G), v⁆ - (1 / 2 : ℝ) • v) ∧
  (∀ v ∈ fixedSpace P h, D v = 0) ∧
  (∀ z ∈ bracketSpan A A, D z = z) ∧
  (∀ z ∈ bracketSpan B B, D z = -z) ∧
  (∀ z ∈ bracketSpan A B ⊔ bracketSpan (fixedSpace P h) (fixedSpace P h), D z = 0)

/-- Tube-type condition for a simple hermitian real Lie algebra: a nonzero three-grading element.
This algebraic characterization is stated in Oeh, arXiv:2007.13445v1, Section 2.2,
and used in the present paper, Remark 4.10, PDF p. 23. -/
def TubeType : Prop := ∃ h : G, h ≠ 0 ∧ EulerElement h

end Derivations

section SymplecticModules
variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule L V] [LieModule ℝ L V]

/-- Effective subspace span(s.V), Lemma 4.6, PDF p. 21. -/
def effectiveSpace (S : LieSubalgebra ℝ L) : Submodule ℝ V :=
  Submodule.span ℝ {v | ∃ x ∈ S, ∃ w : V, v = ⁅x, w⁆}

/-- Fixed subspace V_fix,s, Lemma 4.6, PDF p. 21. -/
def fixedModuleSpace (S : LieSubalgebra ℝ L) : Submodule ℝ V :=
  ⨅ x : S, (LieModule.toEnd ℝ L V (x : L)).ker

/-- Invariance of a subspace under a subalgebra action, Lemma 4.6, PDF p. 21. -/
def StableUnder (S : LieSubalgebra ℝ L) (A : Submodule ℝ V) : Prop :=
  ∀ x ∈ S, ∀ v ∈ A, ⁅x, v⁆ ∈ A

/-- Symplectic l-module of convex type, as in Theorem 2.5(e) and Lemma 4.6, PDF pp. 5, 21. -/
structure ConvexSymplecticModule where
  omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  alternating : ∀ v : V, omega v v = 0
  nondegenerate : ∀ v : V, (∀ w : V, omega v w = 0) → v = 0
  invariant : ∀ x : L, ∀ v w : V, omega ⁅x, v⁆ w + omega v ⁅x, w⁆ = 0
  positive : ∃ x : L, ∀ v : V, v ≠ 0 → 0 < omega ⁅x, v⁆ v

example (M : ConvexSymplecticModule (L := L) (V := V)) (v : V) : M.omega v v = 0 :=
  M.alternating v

end SymplecticModules

end

end QAlgorithms.Papers.Independent.Frontier30.P26


