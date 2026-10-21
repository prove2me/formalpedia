-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04
-- name    : QAlgorithms_Papers_Independent_Claimed50_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T08:38:53.602675+00:00
-- url     : https://prove2.me/theorems/bead82b4-d1e5-461a-a983-1d3708fdb695
-- title:
--   Definitions for Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras
-- statement:
--   The objects the formalized statements of *Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras* (arXiv:2007.13445) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ThreeGraded`: Actual eigenspaces at -1,0,1 span E (their sum is direct in characteristic zero). Notation, PDF p. 3. Zero eigenspaces and the zero endomorphism are permitted.
--   - `ComplexEigenvalues`: Eigenvalues of the ACTUAL complexification, written in real and imaginary parts. Notation, PDF p. 3; Lemma 2.19, PDF p. 10.
--   - `Symplectic`: Alternating, nondegenerate bilinear form, Definition 2.9, PDF p. 7.
--   - `PreservesForm`: Generalized symplectic endomorphisms, PDF p. 10; retain the center-valued form.
--   - `AdjointPair`: Defining equation of the symplectic adjoint, PDF p. 9.
--   - `MaximalCompact`: Maximal compactly embedded subalgebra, PDF pp. 4–5.
--   - `Quasihermitian`: The equivalent maximal-compact centralizer characterization stated on PDF p. 4, including the existence of a compactly embedded Cartan.
--   - `MaximalNilpotent`: Maximality among ALL nilpotent ideals, Theorem 2.8, PDF pp. 6–7.
--   - `Complement`: The ambient ideal and subalgebra give an internal semidirect sum, PDF pp. 12–13.
--   - `Lineality`: Translation lineality exactly as Definition 2.1, PDF p. 4.
--   - `GeneratingCone`: No pointedness requirement; central lineality is a separate hypothesis, PDF p. 18.
--   - `HElement`: Exact-spectrum H-element, Definition 2.5, PDF p. 5.
--   - `SpindlerPresentation`: Internal Spindler construction with the original bracket and central coordinate. The linear isomorphism reconstructs G, so this is a presentation, not unrelated data. No Cartan, nilradical, convex functional, or faithful whole l-action is assumed. PDF p. 6 and Remark 2.12, PDF p. 8.
--   - `spindlerCentralCoordinate`: Central coordinate in the specified splitting, PDF p. 15.
--   - `spindlerVectorCoordinate`: Vector coordinate in that same splitting, PDF p. 15.
--   - `spindlerReductiveCoordinate`: Reductive coordinate in that same splitting, PDF p. 15.
--   - `spindlerBracket`: beta is the restricted AMBIENT bracket, Theorem 2.8(a), PDF p. 7.
--   - `spindlerAction`: Actual restricted adjoint representation, PDF pp. 6–7.
--   - `ScalarConvex`: Nondegenerate scalarization with STRICT convex type, Definition 2.9(c), PDF p. 7. Alternation and invariance follow from the actual bracket and Jacobi identity.
--   - `Wf`: Exact normalized pullback cone of equation (5), PDF p. 15 and Example 2.20, PDF p. 10: coefficient 1/2, linear sign +beta(v,a), specified presentation.
--   - `CoadjointDual`: Extend f by zero on V+l, then take the FULL inner coadjoint orbit dual. Inverse words occur because generators range over all G. Remark 3.1(a), PDF p. 15.
--   - `InvariantLevi`: A genuine semisimple complement to the SOLVABLE radical, PDF p. 13.
--   - `Stable`: A subspace is a submodule precisely when stable under the actual representation, Definition 2.9, PDF p. 7.
--   - `SymplecticModule`: Symplectic representation; both alternation and nondegeneracy are explicit, Definition 2.9(a), PDF p. 7.
--   - `StrictConvexType`: Strict convex type, NOT merely generation of the nonnegative Hamiltonian cone, Definition 2.9(c), PDF p. 7.
--   - `NondegenerateOn`: Restriction of the form to a submodule is nondegenerate, PDF p. 9. Alternation and invariance are inherited from SymplecticModule.
--   - `ConvexOn`: Positivity on the restricted module, PDF p. 9; the zero submodule is allowed.
--   - `ModuleEnd`: Actual module commutant, Proposition 2.18, PDF p. 9.
--   - `EndAlgebra`: The algebra of module endomorphisms, as an actual centralizer algebra, PDF p. 9.
--   - `SimpleModule`: Nonzero irreducible representation, Proposition 2.18(b), PDF p. 9.
--   - `representationFixedSpace`: Constructed common fixed space, Remark 2.10, PDF p. 8.
--   - `representationEffectiveSpace`: Constructed effective space span(l.V), Remark 2.10, PDF p. 8.
--   - `HamiltonianCone`: Nonnegative Hamiltonian cone (4), PDF p. 7.
--   - `heisenbergBracket`: The ACTUAL Heisenberg bracket in coordinates (v,z), Definition 3.6, PDF p. 17. Derivations below are defined by its Leibniz identity, without an axiomatized placeholder.
--   - `HeisenbergDerivation`: A linear map is a derivation of the specified bracket, PDF pp. 17–18.
--   - `BetaCompatiblePair`: beta-compatible pair, equation (6), PDF p. 17.
--   - `diagonalBlocks`: Diagonal block linear map, Proposition 3.7(b), PDF p. 18.
--   - `scalarize`: The scalarized bilinear form is COMPUTED from beta and f, Remark 2.21, PDF p. 11.
--   - `RealDiagonalizable`: Real diagonalizability, including zero-dimensional spaces, Remark 3.3(a), PDF p. 16. The supremum is in the complete lattice of subspaces, not the real numbers.
--   - `blockEnd`: Fixed diagonal-block operator in the ORIGINAL Spindler coordinates, PDF p. 20.
--   - `PreservesBeta`: The generalized symplectic condition for the CONSTRUCTED beta, PDF pp. 10, 24.
--   - `derivedSymplectic`: The actual derived subspace of generalized sp, as the span of all commutators, Remark 3.18, PDF p. 24. No abstract predicate for semisimplicity is substituted.
--   - `sl2H`: The fixed matrix H=diag(1,-1), Examples 2.4 and 2.6, PDF pp. 5–6.
--   - `sl2U`: The fixed matrix U=[[0,1],[-1,0]], PDF p. 6.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, https://arxiv.org/abs/2007.13445v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P26

/-! Oeh, arXiv:2007.13445v1. Draft statements; compilation pending batch handoff.
The import is a pinned accepted module; no unreviewed paper module is imported. -/
namespace QAlgorithms.Papers.Independent.Claimed50.P04

noncomputable section
open Set
attribute [local instance 100] LieRing.ofAssociativeRing
open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

section LinearDefinitions
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- Actual eigenspaces at -1,0,1 span E (their sum is direct in characteristic zero).
Notation, PDF p. 3. Zero eigenspaces and the zero endomorphism are permitted. -/
def ThreeGraded (T : E →ₗ[K] E) : Prop :=
  ∀ v : E, ∃ vm v0 vp : E,
    T vm = -vm ∧ T v0 = 0 ∧ T vp = vp ∧ v = vm + v0 + vp

example : ThreeGraded (0 : E →ₗ[K] E) := by
  intro v
  exact ⟨0, v, 0, by simp⟩

end LinearDefinitions

section RealLinearDefinitions
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Eigenvalues of the ACTUAL complexification, written in real and imaginary parts.
Notation, PDF p. 3; Lemma 2.19, PDF p. 10. -/
def ComplexEigenvalues (T : E →ₗ[ℝ] E) : Set ℂ :=
  {z | ∃ u v : E, (u ≠ 0 ∨ v ≠ 0) ∧
    T u = z.re • u - z.im • v ∧ T v = z.im • u + z.re • v}

/-- Alternating, nondegenerate bilinear form, Definition 2.9, PDF p. 7. -/
def Symplectic (omega : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : Prop :=
  (∀ v, omega v v = 0) ∧ (∀ v, (∀ w, omega v w = 0) → v = 0)

/-- Generalized symplectic endomorphisms, PDF p. 10; retain the center-valued form. -/
def PreservesForm {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    (spindlerBracket : E →ₗ[ℝ] E →ₗ[ℝ] Z) (T : E →ₗ[ℝ] E) : Prop :=
  ∀ v w, spindlerBracket (T v) w + spindlerBracket v (T w) = 0

/-- Defining equation of the symplectic adjoint, PDF p. 9. -/
def AdjointPair (omega : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (T S : E →ₗ[ℝ] E) : Prop :=
  ∀ v w, omega (T v) w = omega v (S w)

example (omega : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    AdjointPair omega (LinearMap.id : E →ₗ[ℝ] E) LinearMap.id := by
  intro v w
  rfl

end RealLinearDefinitions

/-- Finite-basis norm induced from the EXISTING Lie additive group, PDF p. 1. -/
local instance lieNormedGroup (G : Type*) [LieRing G] [LieAlgebra ℝ G]
    [FiniteDimensional ℝ G] : NormedAddCommGroup G :=
  NormedAddCommGroup.induced G (Fin (Module.finrank ℝ G) → ℝ)
    (Module.finBasis ℝ G).equivFun.toLinearMap (Module.finBasis ℝ G).equivFun.injective

/-- The usual finite-dimensional topology, with the original real scalar action, PDF p. 1. -/
local instance lieNormedSpace (G : Type*) [LieRing G] [LieAlgebra ℝ G]
    [FiniteDimensional ℝ G] : NormedSpace ℝ G :=
  NormedSpace.induced ℝ G (Fin (Module.finrank ℝ G) → ℝ)
    (Module.finBasis ℝ G).equivFun.toLinearMap

section LieDefinitions
variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Maximal compactly embedded subalgebra, PDF pp. 4–5. -/
def MaximalCompact (K : LieSubalgebra ℝ G) : Prop :=
  CompactlyEmbedded (K : Set G) ∧
  ∀ K' : LieSubalgebra ℝ G, CompactlyEmbedded (K' : Set G) → K ≤ K' → K' ≤ K

/-- The equivalent maximal-compact centralizer characterization stated on PDF p. 4,
including the existence of a compactly embedded Cartan. -/
def Quasihermitian : Prop :=
  ∃ T K : LieSubalgebra ℝ G, CompactCartan T ∧ T ≤ K ∧ MaximalCompact K ∧
    ∀ x : G, (∀ z : LieAlgebra.center ℝ K, ⁅x, ((z : K) : G)⁆ = 0) ↔ x ∈ K

/-- Maximality among ALL nilpotent ideals, Theorem 2.8, PDF pp. 6–7. -/
def MaximalNilpotent (U : LieIdeal ℝ G) : Prop :=
  LieRing.IsNilpotent U ∧ ∀ I : LieIdeal ℝ G, LieRing.IsNilpotent I → I ≤ U

/-- The ambient ideal and subalgebra give an internal semidirect sum, PDF pp. 12–13. -/
def Complement (U : LieIdeal ℝ G) (L : LieSubalgebra ℝ G) : Prop :=
  IsCompl U.toSubmodule L.toSubmodule

/-- Translation lineality exactly as Definition 2.1, PDF p. 4. -/
def Lineality (C : Set G) : Set G := {x | (fun c => c + x) '' C = C}

/-- No pointedness requirement; central lineality is a separate hypothesis, PDF p. 18. -/
def GeneratingCone (C : Set G) : Prop :=
  ClosedCone C ∧ Invariant C ∧ Submodule.span ℝ C = ⊤

/-- Exact-spectrum H-element, Definition 2.5, PDF p. 5. -/
def HElement (H0 : G) : Prop :=
  ∃ K : LieSubalgebra ℝ G, MaximalCompact K ∧
    (∀ x : G, x ∈ K ↔ ⁅H0, x⁆ = 0) ∧
    ComplexEigenvalues (LieAlgebra.ad ℝ G H0) = {0, Complex.I, -Complex.I}

/-- Internal Spindler construction with the original bracket and central coordinate.
The linear isomorphism reconstructs G, so this is a presentation, not unrelated data.
No Cartan, nilradical, convex functional, or faithful whole l-action is assumed.
PDF p. 6 and Remark 2.12, PDF p. 8. -/
structure SpindlerPresentation where
  L : LieSubalgebra ℝ G
  V : Submodule ℝ G
  coordinates : G ≃ₗ[ℝ] (V × (LieAlgebra.center ℝ G) × L)
  reconstruct : ∀ x : G, ((coordinates x).1 : G) +
    ((coordinates x).2.1 : G) + ((coordinates x).2.2 : G) = x
  reductive : LieAlgebra.HasCentralRadical ℝ L
  vv_central : ∀ v w : V, ⁅(v : G), (w : G)⁆ ∈ LieAlgebra.center ℝ G
  lv_stable : ∀ x : L, ∀ v : V, ⁅(x : G), (v : G)⁆ ∈ V

/-- Central coordinate in the specified splitting, PDF p. 15. -/
def spindlerCentralCoordinate (P : SpindlerPresentation (G := G)) (x : G) : LieAlgebra.center ℝ G :=
  (P.coordinates x).2.1

/-- Vector coordinate in that same splitting, PDF p. 15. -/
def spindlerVectorCoordinate (P : SpindlerPresentation (G := G)) (x : G) : P.V := (P.coordinates x).1

/-- Reductive coordinate in that same splitting, PDF p. 15. -/
def spindlerReductiveCoordinate (P : SpindlerPresentation (G := G)) (x : G) : P.L := (P.coordinates x).2.2

/-- beta is the restricted AMBIENT bracket, Theorem 2.8(a), PDF p. 7. -/
def spindlerBracket (P : SpindlerPresentation (G := G)) (v w : P.V) : LieAlgebra.center ℝ G :=
  ⟨⁅(v : G), (w : G)⁆, P.vv_central v w⟩

/-- Actual restricted adjoint representation, PDF pp. 6–7. -/
def spindlerAction (P : SpindlerPresentation (G := G)) (x : P.L) : P.V →ₗ[ℝ] P.V where
  toFun v := ⟨⁅(x : G), (v : G)⁆, P.lv_stable x v⟩
  map_add' v w := by ext; simp
  map_smul' r v := by ext; simp

/-- Nondegenerate scalarization with STRICT convex type, Definition 2.9(c), PDF p. 7.
Alternation and invariance follow from the actual bracket and Jacobi identity. -/
def ScalarConvex (P : SpindlerPresentation (G := G))
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) : Prop :=
  (∀ v : P.V, (∀ w : P.V, f (spindlerBracket P v w) = 0) → v = 0) ∧
    ∃ x : P.L, ∀ v : P.V, v ≠ 0 → 0 < f (spindlerBracket P (spindlerAction P x v) v)

/-- Exact normalized pullback cone of equation (5), PDF p. 15 and Example 2.20,
PDF p. 10: coefficient 1/2, linear sign +beta(v,a), specified presentation. -/
def Wf (P : SpindlerPresentation (G := G))
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) : Set G :=
  {x | ∀ a : P.V, (1 / 2 : ℝ) * f (spindlerBracket P (spindlerAction P (spindlerReductiveCoordinate P x) a) a) +
    f (spindlerBracket P (spindlerVectorCoordinate P x) a) + f (spindlerCentralCoordinate P x) ≥ 0}

/-- Extend f by zero on V+l, then take the FULL inner coadjoint orbit dual.
Inverse words occur because generators range over all G. Remark 3.1(a), PDF p. 15. -/
def CoadjointDual (P : SpindlerPresentation (G := G))
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) : Set G :=
  {x | ∀ ys : List G,
    0 ≤ f (spindlerCentralCoordinate P (QAlgorithms.Papers.Independent.Frontier30.P26.innerWord ys x))}

example (P : SpindlerPresentation (G := G)) (x : G) :
    (spindlerVectorCoordinate P x : G) + (spindlerCentralCoordinate P x : G) + (spindlerReductiveCoordinate P x : G) = x := P.reconstruct x

example (P : SpindlerPresentation (G := G)) : spindlerBracket P 0 0 = 0 := by
  ext
  simp [spindlerBracket]

end LieDefinitions

section Levi
variable {K G : Type*} [RCLike K] [LieRing G] [LieAlgebra K G] [FiniteDimensional K G]

/-- A genuine semisimple complement to the SOLVABLE radical, PDF p. 13. -/
def InvariantLevi (D : LieDerivation K G G) (S : LieSubalgebra K G) : Prop :=
  LieAlgebra.IsSemisimple K S ∧
    IsCompl (LieAlgebra.radical K G).toSubmodule S.toSubmodule ∧
    ∀ x : S, D (x : G) ∈ S

end Levi

section Modules
variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A subspace is a submodule precisely when stable under the actual representation,
Definition 2.9, PDF p. 7. -/
def Stable (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V) (W : Submodule ℝ V) : Prop :=
  ∀ x : L, ∀ v ∈ W, rho x v ∈ W

/-- Symplectic representation; both alternation and nondegeneracy are explicit,
Definition 2.9(a), PDF p. 7. -/
def SymplecticModule (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  Symplectic omega ∧ ∀ x : L, PreservesForm omega (rho x)

/-- Strict convex type, NOT merely generation of the nonnegative Hamiltonian cone,
Definition 2.9(c), PDF p. 7. -/
def StrictConvexType (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  ∃ x : L, ∀ v : V, v ≠ 0 → 0 < omega (rho x v) v

/-- Restriction of the form to a submodule is nondegenerate, PDF p. 9.
Alternation and invariance are inherited from SymplecticModule. -/
def NondegenerateOn (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (W : Submodule ℝ V) : Prop :=
  ∀ v ∈ W, (∀ w ∈ W, omega v w = 0) → v = 0

/-- Positivity on the restricted module, PDF p. 9; the zero submodule is allowed. -/
def ConvexOn (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (W : Submodule ℝ V) : Prop :=
  ∃ x : L, ∀ v ∈ W, v ≠ 0 → 0 < omega (rho x v) v

/-- Actual module commutant, Proposition 2.18, PDF p. 9. -/
def ModuleEnd (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V) (T : Module.End ℝ V) : Prop :=
  ∀ x : L, ∀ v : V, T (rho x v) = rho x (T v)

/-- The algebra of module endomorphisms, as an actual centralizer algebra, PDF p. 9. -/
def EndAlgebra (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V) : Subalgebra ℝ (Module.End ℝ V) :=
  Subalgebra.centralizer ℝ (Set.range rho)

/-- Nonzero irreducible representation, Proposition 2.18(b), PDF p. 9. -/
def SimpleModule (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℝ V, Stable rho W → W = ⊥ ∨ W = ⊤

/-- Constructed common fixed space, Remark 2.10, PDF p. 8. -/
def representationFixedSpace (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V) : Submodule ℝ V :=
  ⨅ x : L, (rho x).ker

/-- Constructed effective space span(l.V), Remark 2.10, PDF p. 8. -/
def representationEffectiveSpace (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V) : Submodule ℝ V :=
  Submodule.span ℝ {v | ∃ x : L, ∃ w : V, v = rho x w}

/-- Nonnegative Hamiltonian cone (4), PDF p. 7. -/
def HamiltonianCone (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Set L :=
  {x | ∀ v : V, 0 ≤ omega (rho x v) v}

example (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V) :
    ModuleEnd rho (LinearMap.id : Module.End ℝ V) := by
  intro x v
  rfl

example (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : (0 : L) ∈ HamiltonianCone rho omega := by
  simp [HamiltonianCone]

end Modules

section Heisenberg
variable {V Z : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]

/-- The ACTUAL Heisenberg bracket in coordinates (v,z), Definition 3.6, PDF p. 17.
Derivations below are defined by its Leibniz identity, without an axiomatized placeholder. -/
def heisenbergBracket (b : V →ₗ[ℝ] V →ₗ[ℝ] Z) (p q : V × Z) : V × Z :=
  (0, b p.1 q.1)

/-- A linear map is a derivation of the specified bracket, PDF pp. 17–18. -/
def HeisenbergDerivation (b : V →ₗ[ℝ] V →ₗ[ℝ] Z)
    (D : Module.End ℝ (V × Z)) : Prop :=
  ∀ p q, D (heisenbergBracket b p q) =
    heisenbergBracket b (D p) q + heisenbergBracket b p (D q)

/-- beta-compatible pair, equation (6), PDF p. 17. -/
def BetaCompatiblePair (b : V →ₗ[ℝ] V →ₗ[ℝ] Z)
    (DV : Module.End ℝ V) (DZ : Module.End ℝ Z) : Prop :=
  ∀ v w, DZ (b v w) = b (DV v) w + b v (DV w)

/-- Diagonal block linear map, Proposition 3.7(b), PDF p. 18. -/
def diagonalBlocks (DV : Module.End ℝ V) (DZ : Module.End ℝ Z) : Module.End ℝ (V × Z) :=
  DV.prodMap DZ

example (b : V →ₗ[ℝ] V →ₗ[ℝ] Z) (v : V) (z : Z) :
    heisenbergBracket b (v, z) (0, z) = 0 := by
  simp [heisenbergBracket]

/-- The scalarized bilinear form is COMPUTED from beta and f, Remark 2.21, PDF p. 11. -/
def scalarize (b : V →ₗ[ℝ] V →ₗ[ℝ] Z) (f : Z →ₗ[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun v := f.comp (b v)
  map_add' v w := by ext a; simp
  map_smul' r v := by ext a; simp

example (b : V →ₗ[ℝ] V →ₗ[ℝ] Z) (f : Z →ₗ[ℝ] ℝ) (v w : V) :
    scalarize b f v w = f (b v w) := rfl

end Heisenberg

section FurtherStructure
variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Real diagonalizability, including zero-dimensional spaces, Remark 3.3(a), PDF p. 16.
The supremum is in the complete lattice of subspaces, not the real numbers. -/
def RealDiagonalizable (T : G →ₗ[ℝ] G) : Prop :=
  (⨆ r : ℝ, Module.End.eigenspace T r) = ⊤

/-- Fixed diagonal-block operator in the ORIGINAL Spindler coordinates, PDF p. 20. -/
def blockEnd (P : SpindlerPresentation (G := G)) (DV : Module.End ℝ P.V)
    (DZ : Module.End ℝ (LieAlgebra.center ℝ G)) : Module.End ℝ G :=
  P.coordinates.symm.toLinearMap.comp
    ((DV.prodMap (DZ.prodMap (0 : Module.End ℝ P.L))).comp P.coordinates.toLinearMap)

example (P : SpindlerPresentation (G := G)) (DV : Module.End ℝ P.V)
    (DZ : Module.End ℝ (LieAlgebra.center ℝ G)) (x : G) :
    P.coordinates (blockEnd P DV DZ x) =
      (DV (spindlerVectorCoordinate P x), DZ (spindlerCentralCoordinate P x), 0) := by
  simp [blockEnd, spindlerVectorCoordinate, spindlerCentralCoordinate]

/-- The generalized symplectic condition for the CONSTRUCTED beta, PDF pp. 10, 24. -/
def PreservesBeta (P : SpindlerPresentation (G := G)) (T : Module.End ℝ P.V) : Prop :=
  ∀ v w : P.V, spindlerBracket P (T v) w + spindlerBracket P v (T w) = 0

/-- The actual derived subspace of generalized sp, as the span of all commutators,
Remark 3.18, PDF p. 24. No abstract predicate for semisimplicity is substituted. -/
def derivedSymplectic (P : SpindlerPresentation (G := G)) : Submodule ℝ (Module.End ℝ P.V) :=
  Submodule.span ℝ {T | ∃ A B : Module.End ℝ P.V,
    PreservesBeta P A ∧ PreservesBeta P B ∧ T = A.comp B - B.comp A}

end FurtherStructure

/-- The fixed matrix H=diag(1,-1), Examples 2.4 and 2.6, PDF pp. 5–6. -/
def sl2H : LieAlgebra.SpecialLinear.sl (Fin 2) ℝ :=
  ⟨!![1, 0; 0, -1], by
    simp [LieAlgebra.SpecialLinear.sl, Matrix.trace, Fin.sum_univ_two]⟩

/-- The fixed matrix U=[[0,1],[-1,0]], PDF p. 6. -/
def sl2U : LieAlgebra.SpecialLinear.sl (Fin 2) ℝ :=
  ⟨!![0, 1; -1, 0], by
    simp [LieAlgebra.SpecialLinear.sl, Matrix.trace, Fin.sum_univ_two]⟩

example : ((sl2H : Matrix (Fin 2) (Fin 2) ℝ) 0 0) = 1 := rfl

example : ((sl2U : Matrix (Fin 2) (Fin 2) ℝ) 1 0) = -1 := rfl

end
end QAlgorithms.Papers.Independent.Claimed50.P04


