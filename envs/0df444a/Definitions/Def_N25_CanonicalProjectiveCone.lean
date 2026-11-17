-- Prove2me | Definitions.Def_N25_CanonicalProjectiveCone
-- name    : N25_CanonicalProjectiveCone
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:08.2712+00:00
-- url     : https://prove2.me/theorems/9d67efc0-652c-4b66-8767-64be104a0fc8
-- title:
--   The homogeneous cone and projective canonical curve
-- statement:
--   For a field $K$, let $S=K[x_0,x_1,x_2,x_3]$, and let $Q$ and $C$ be the canonical homogeneous equations of degrees $2$ and $3$. The file defines $$I=(Q,C),\qquad A=S/I,$$ the quotient projection, the graded pieces $A_n$, the universal coordinate classes in $A_1$, the projective curve $X_K=\operatorname{Proj}(A)$, and its structure morphism $X_K→\operatorname{Spec}K$. It is the literal projective model on which the scheme-theoretic and function-field arguments are built.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalUnitPlane
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
/-! The literal homogeneous coordinate algebra of the canonical order-25 curve, its grading by the images of the
homogeneous polynomial pieces, and the projective curve `Proj` of that grading with its structure morphism.
The directness of the grading is proved here because the `GradedAlgebra` instance needs it. -/
noncomputable section
universe u
namespace N25
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev CanonicalConePolynomial25 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

def canonicalConeIdeal25 (K : Type u) [Field K] : Ideal (CanonicalConePolynomial25 K) :=
  Ideal.span {canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.X 3),
    canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.X 3)}

abbrev CanonicalConeRing25 (K : Type u) [Field K] :=
  CanonicalConePolynomial25 K ⧸ canonicalConeIdeal25 K

def canonicalConeProjection25 (K : Type u) [Field K] :
    CanonicalConePolynomial25 K →ₐ[K] CanonicalConeRing25 K :=
  Ideal.Quotient.mkₐ K (canonicalConeIdeal25 K)

def canonicalConePiece25 (K : Type u) [Field K] (n : ℕ) :
    Submodule K (CanonicalConeRing25 K) :=
  (MvPolynomial.homogeneousSubmodule (Fin 4) K n).map
    (canonicalConeProjection25 K).toLinearMap

open AlgebraicGeometry CategoryTheory DirectSum
variable (K : Type u) [Field K]

/-- The two literal equations are homogeneous of degrees two and three. -/
theorem canonicalConeIdeal25_isHomogeneous :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 4) K)
      (canonicalConeIdeal25 K) := by
  apply Ideal.homogeneous_span
  intro p hp
  rcases hp with rfl | hp
  · refine ⟨2, ?_⟩
    unfold canonicalQuadric
    have h (i : Fin 4) := MvPolynomial.isHomogeneous_X K i
    exact ((((h 0).neg.mul (h 2)).sub ((h 0).mul (h 3))).add
      ((h 1).pow 2)).add ((h 1).mul (h 2)) |>.add ((h 2).mul (h 3))
  · rcases hp with rfl | hp
    · refine ⟨3, ?_⟩
      unfold canonicalCubic
      have h (i : Fin 4) := MvPolynomial.isHomogeneous_X K i
      exact ((((((h 0).pow 2 |>.mul (h 3)).add
        (((h 0).mul (h 1)).mul (h 2))).sub
        (((h 0).mul (h 1)).mul (h 3))).sub
        (((h 0).mul (h 2)).mul (h 3))).add
        (((h 1).mul (h 2)).mul (h 3))).add
        ((h 2).pow 2 |>.mul (h 3)) |>.sub ((h 2).mul ((h 3).pow 2))

private def componentMap (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) K n →ₗ[K] canonicalConePiece25 K n :=
  { toFun := fun p => ⟨canonicalConeProjection25 K p, ⟨p, p.property, rfl⟩⟩
    map_add' := fun p q => Subtype.ext (map_add (canonicalConeProjection25 K) (p : CanonicalConePolynomial25 K) (q : CanonicalConePolynomial25 K))
    map_smul' := fun a p => Subtype.ext (map_smul (canonicalConeProjection25 K) a (p : CanonicalConePolynomial25 K)) }

private def polynomialComponents : CanonicalConePolynomial25 K →ₗ[K]
    ⨁ n, canonicalConePiece25 K n :=
  DirectSum.lmap (componentMap K) ∘ₗ
    DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule (Fin 4) K)

private theorem polynomialComponents_surjective :
    Function.Surjective (polynomialComponents K) := by
  apply Function.Surjective.comp
    ((DirectSum.lmap_surjective (componentMap K)).mpr ?_)
    (DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule (Fin 4) K)).surjective
  intro n
  rintro ⟨p, q, hq, rfl⟩
  exact ⟨⟨q, hq⟩, rfl⟩

private theorem recompose_components :
    DirectSum.coeLinearMap (canonicalConePiece25 K) ∘ₗ polynomialComponents K =
      (canonicalConeProjection25 K).toLinearMap := by
  apply DirectSum.decompose_lhom_ext (MvPolynomial.homogeneousSubmodule (Fin 4) K)
  intro n
  ext p
  simp [polynomialComponents, componentMap]

private theorem components_kernel :
    LinearMap.ker (polynomialComponents K) =
      LinearMap.ker (canonicalConeProjection25 K).toLinearMap := by
  ext p
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro hp
    simpa [hp] using (LinearMap.congr_fun (recompose_components K) p).symm
  · intro hp
    have hI : p ∈ canonicalConeIdeal25 K := Ideal.Quotient.eq_zero_iff_mem.mp hp
    have hc := (canonicalConeIdeal25_isHomogeneous K).mem_iff.mp hI
    apply DirectSum.ext
    intro n
    apply Subtype.ext
    change canonicalConeProjection25 K
      ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 4) K) p n) :
        CanonicalConePolynomial25 K) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hc n)

/-- Directness is inherited from the homogeneous ideal, not imposed on the quotient. -/
theorem canonicalConePiece25_isInternal : DirectSum.IsInternal (canonicalConePiece25 K) := by
  constructor
  · intro x y hxy
    obtain ⟨p, rfl⟩ := polynomialComponents_surjective K x
    obtain ⟨q, rfl⟩ := polynomialComponents_surjective K y
    apply sub_eq_zero.mp
    have hpq : p - q ∈ LinearMap.ker (polynomialComponents K) := by
      rw [components_kernel, LinearMap.mem_ker, map_sub, sub_eq_zero]
      calc
        canonicalConeProjection25 K p = _ :=
          (LinearMap.congr_fun (recompose_components K) p).symm
        _ = _ := hxy
        _ = canonicalConeProjection25 K q :=
          LinearMap.congr_fun (recompose_components K) q
    simpa only [LinearMap.mem_ker, map_sub] using hpq
  · intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (canonicalConeIdeal25 K) q
    exact ⟨polynomialComponents K p, LinearMap.congr_fun (recompose_components K) p⟩

noncomputable instance canonicalConePiece25_gradedAlgebra :
    GradedAlgebra (canonicalConePiece25 K) where
  one_mem := ⟨1, MvPolynomial.isHomogeneous_one _ _, (canonicalConeProjection25 K).map_one⟩
  mul_mem := by
    intro i j x y hx hy
    rcases hx with ⟨p, hp, rfl⟩
    rcases hy with ⟨q, hq, rfl⟩
    exact ⟨p*q, MvPolynomial.IsHomogeneous.mul hp hq, (canonicalConeProjection25 K).map_mul p q⟩
  decompose' := ((canonicalConePiece25_isInternal K).chooseDecomposition _).decompose'
  left_inv := ((canonicalConePiece25_isInternal K).chooseDecomposition _).left_inv
  right_inv := ((canonicalConePiece25_isInternal K).chooseDecomposition _).right_inv

noncomputable instance canonicalConePieceZero25_algebra :
    Algebra K (canonicalConePiece25 K 0) :=
  SetLike.GradeZero.instAlgebra (canonicalConePiece25 K)


/-- Evaluation at the cone vertex annihilates the defining ideal. -/
theorem canonicalConeIdeal25_le_vertexKernel :
    canonicalConeIdeal25 K ≤ RingHom.ker (MvPolynomial.eval (fun _ : Fin 4 => (0 : K))) := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with rfl | hp
  · simp [RingHom.mem_ker, canonicalQuadric]
  · rcases hp with rfl | hp
    · simp [RingHom.mem_ker, canonicalCubic]

instance canonicalConeRing25_nontrivial : Nontrivial (CanonicalConeRing25 K) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro ht
  have h := canonicalConeIdeal25_le_vertexKernel K
  have ho : (1 : CanonicalConePolynomial25 K) ∈ canonicalConeIdeal25 K := by
    rw [ht]; trivial
  have hh := h ho
  exact one_ne_zero (by simpa [RingHom.mem_ker] using hh : (1 : K) = 0)

/-- The degree-zero piece is precisely the original coefficient field. -/
theorem canonicalConePieceZero25_algebraMap_bijective :
    Function.Bijective (algebraMap K (canonicalConePiece25 K 0)) := by
  constructor
  · intro a b hab
    apply (algebraMap K (CanonicalConeRing25 K)).injective
    simpa only [SetLike.GradeZero.coe_algebraMap] using congrArg Subtype.val hab
  · rintro ⟨x, p, hp, rfl⟩
    change p ∈ MvPolynomial.homogeneousSubmodule (Fin 4) K 0 at hp
    rw [MvPolynomial.homogeneousSubmodule_zero] at hp
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp hp
    subst p
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact (canonicalConeProjection25 K).commutes a |>.symm

def canonicalConeCoordinate25 (i : Fin 4) : CanonicalConeRing25 K :=
  canonicalConeProjection25 K (MvPolynomial.X i)

theorem canonicalConeCoordinate25_mem (i : Fin 4) :
    canonicalConeCoordinate25 K i ∈ canonicalConePiece25 K 1 :=
  ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i, rfl⟩

abbrev CanonicalProjectiveCurve25 : Scheme.{u} :=
  AlgebraicGeometry.Proj (canonicalConePiece25 K)

def canonicalProjectiveCurveToSpec25 :
    CanonicalProjectiveCurve25 K ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (canonicalConePiece25 K) ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (canonicalConePiece25 K 0)))

end N25


