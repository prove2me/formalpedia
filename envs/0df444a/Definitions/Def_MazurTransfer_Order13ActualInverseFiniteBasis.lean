-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualInverseFiniteBasis
-- name    : MazurTransfer_Order13ActualInverseFiniteBasis
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T05:44:30.611542+00:00
-- url     : https://prove2.me/theorems/03ef8823-a9d3-4c78-99fe-591cb92b09a6
-- title:
--   The original three-generator basis of the actual inverse finite algebra
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. In the actual ordinary coordinate algebra localized at $t$, let $s=1/t$, $a=p/t^2$, and $b=q/t^2$. The actual inverse algebra $B=R[S][a,b]$, with $S\mapsto s$, has the original specified basis with values $1,a,b$. In particular, it is free of rank three over $R[S]$. These are the basis constructors and structural consequences used by the inverse finite-chart level sets in actual FiniteMapData.
-- source:
--   The six original declarations from MazurTheorem Order13InverseParameterFiniteAlgebraBasis.lean, using the public inverse polynomial-combination kernel and restored primitive scopes. The basis constructor body is unchanged. Two proof bodies adapt only parameter-map reflexivity and explicit unfolding of the kernel-equal generator-set alias. All six original types and the original basis constructor value are checked in the kernel. Native, strict and full frontend checks pass with standard axioms only. Original per-file header, Apache-2.0 and actual level-set downstream consumer are retained. Vas and contributors.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual inverse finite subalgebra has the explicit R[S]-basis
1,p/t²,q/t² over a noetherian integral base with 104 invertible. Named downstream consumer:
finite free level sets in single-section FiniteMapData.
The parameter S acts by s=1/t, with no assumed module basis.
-/
import Definitions.Def_MazurTransfer_Order13CanonicalFiniteMapPrimitiveScopes
import Definitions.Def_MazurTransfer_Order13InverseCombinationCoordinates
import Theorems.Thm_MazurTransfer_Order13InverseParameterPolynomialCombinationIndependence_polynomial_combination_kernel


noncomputable section
universe u
namespace MazurTransfer.Order13InverseParameterFiniteAlgebra
open Polynomial Module
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
open Order13InverseParameterPolynomialIdentities
open Order13InverseParameterPolynomialCombinationIndependence
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem generator_linearIndependent (h104 : IsUnit (104 : R)) :
    LinearIndependent (Polynomial R) (generator R) := by
  apply Fintype.linearIndependent_iff.mpr
  intro F hF
  apply polynomial_combination_kernel R h104 F
  have hmap (P : Polynomial R) :
      algebraMap (Polynomial R) (ordinaryParameterLocalization R) P = aeval (s R) P := rfl
  simpa only [Algebra.smul_def, hmap] using hF

omit [IsDomain R] [IsNoetherianRing R] in
theorem generator_range : Set.range (generator R) = generators R := by
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp [generator, generators, InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterFiniteAlgebra.generators]
  · intro hz
    simp only [generators, InverseParameterChartComparisonLibrary.MazurTransfer.Order13InverseParameterFiniteAlgebra.generators, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨0,by simp [generator]⟩
    · exact ⟨1,by simp [generator]⟩
    · exact ⟨2,by simp [generator]⟩

noncomputable def candidateBasis (h104 : IsUnit (104 : R)) :
    Basis (Fin 3) (Polynomial R) (candidateAlgebra R) := by
  change Basis (Fin 3) (Polynomial R) (candidateAlgebra R).toSubmodule
  exact (Basis.span (generator_linearIndependent R h104)).map
    (LinearEquiv.ofEq _ _ (by
      rw [generator_range]
      exact (candidateAlgebra_eq_span R (two_isUnit_of_104 R h104)).symm))

theorem candidateBasis_value (h104 : IsUnit (104 : R)) (i : Fin 3) :
    (candidateBasis R h104 i : ordinaryParameterLocalization R) = generator R i := by
  simp [candidateBasis]

theorem candidateAlgebra_free (h104 : IsUnit (104 : R)) :
    Module.Free (Polynomial R) (candidateAlgebra R) := Module.Free.of_basis (candidateBasis R h104)

theorem candidateAlgebra_finrank (h104 : IsUnit (104 : R)) :
    Module.finrank (Polynomial R) (candidateAlgebra R) = 3 := by
  simpa using Module.finrank_eq_card_basis (candidateBasis R h104)

end MazurTransfer.Order13InverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.generator_linearIndependent
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateBasis_value
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra_free
#print axioms MazurTransfer.Order13InverseParameterFiniteAlgebra.candidateAlgebra_finrank


