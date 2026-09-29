-- Prove2me | solution 1 for AlgebraicCurve.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/58e96cc1-9f56-5d64-8c0c-2a34b5872b38

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open IsDedekindDomain
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring dCoord DCoordGenerates dCoord_ne_zero mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

section Transport

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private noncomputable def _root_.AlgebraicCurve.Place.uniformizerSubring' : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose

p2m_export "AlgebraicCurve.Place" "uniformizerSubring'"
private scoped instance instSMulCommClass_subring : SMulCommClass K v.toValuationSubring F :=
  IsScalarTower.to_smulCommClass

private theorem _root_.AlgebraicCurve.Place.kaehlerMap_subring_D_uniformizer :
    KaehlerDifferential.map K K v.toValuationSubring F
      (KaehlerDifferential.D K v.toValuationSubring v.uniformizerSubring') = v.dCoord := by
  rw [KaehlerDifferential.map_D K K v.toValuationSubring F]
  rfl

p2m_export "AlgebraicCurve.Place" "kaehlerMap_subring_D_uniformizer"
end Transport

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringKaehlerSpanTop : Prop :=
  ∀ v : Place K F,
    Submodule.span v.toValuationSubring
      {KaehlerDifferential.D K v.toValuationSubring (Place.uniformizerSubring' v)} = ⊤

variable {K F}

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

open IsDedekindDomain Polynomial
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring dCoord DCoordGenerates dCoord_ne_zero mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

section CotangentEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private noncomputable def _root_.AlgebraicCurve.Place.uniformizerSubring'' : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose

p2m_export "AlgebraicCurve.Place" "uniformizerSubring''"
@[reducible] private noncomputable def _root_.AlgebraicCurve.Place.polynomialAlgebra : Algebra K[X] v.toValuationSubring :=
  (Polynomial.aeval (R := K) v.uniformizerSubring'').toRingHom.toAlgebra

p2m_export "AlgebraicCurve.Place" "polynomialAlgebra"
private theorem _root_.AlgebraicCurve.Place.polynomialAlgebra_algebraMap_X :
    letI := v.polynomialAlgebra
    algebraMap K[X] v.toValuationSubring X = v.uniformizerSubring'' :=
  aeval_X _

p2m_export "AlgebraicCurve.Place" "polynomialAlgebra_algebraMap_X"
@[reducible] private def _root_.AlgebraicCurve.Place.polynomialIsScalarTower :
    letI := v.polynomialAlgebra
    IsScalarTower K K[X] v.toValuationSubring := by
  letI := v.polynomialAlgebra
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show _ = aeval v.uniformizerSubring'' (algebraMap K K[X] a)
  simp [Polynomial.algebraMap_eq, aeval_C]

p2m_export "AlgebraicCurve.Place" "polynomialIsScalarTower"
private theorem _root_.AlgebraicCurve.Place.range_mapBaseChange_le_span_D_uniformizer :
    letI := v.polynomialAlgebra
    letI := v.polynomialIsScalarTower
    LinearMap.range (KaehlerDifferential.mapBaseChange K K[X] v.toValuationSubring)
      ≤ Submodule.span v.toValuationSubring
          {KaehlerDifferential.D K v.toValuationSubring v.uniformizerSubring''} := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  rintro _ ⟨t, rfl⟩
  induction t with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul b ω =>
    rw [KaehlerDifferential.mapBaseChange_tmul,
      show ω = (KaehlerDifferential.polynomialEquiv K ω) • (KaehlerDifferential.D K K[X] X) from
        ((KaehlerDifferential.polynomialEquiv K).symm_apply_apply ω).symm.trans
          (KaehlerDifferential.polynomialEquiv_symm K _),
      LinearMap.map_smul, KaehlerDifferential.map_D,
      show algebraMap K[X] v.toValuationSubring X = v.uniformizerSubring'' from aeval_X _,
      ← algebraMap_smul (A := v.toValuationSubring)]
    exact Submodule.smul_mem _ b
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

p2m_export "AlgebraicCurve.Place" "range_mapBaseChange_le_span_D_uniformizer"
private theorem _root_.AlgebraicCurve.Place.range_mapBaseChange_eq_top_of_subsingleton
    (hsub :
      letI := v.polynomialAlgebra
      Subsingleton Ω[v.toValuationSubring⁄K[X]]) :
    letI := v.polynomialAlgebra
    letI := v.polynomialIsScalarTower
    LinearMap.range (KaehlerDifferential.mapBaseChange K K[X] v.toValuationSubring) = ⊤ := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  rw [KaehlerDifferential.range_mapBaseChange]
  exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)

p2m_export "AlgebraicCurve.Place" "range_mapBaseChange_eq_top_of_subsingleton"
private theorem _root_.AlgebraicCurve.Place.span_D_uniformizer_eq_top_of_subsingleton
    (hsub :
      letI := v.polynomialAlgebra
      Subsingleton Ω[v.toValuationSubring⁄K[X]]) :
    Submodule.span v.toValuationSubring
      {KaehlerDifferential.D K v.toValuationSubring v.uniformizerSubring''} = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← v.range_mapBaseChange_eq_top_of_subsingleton hsub]
  exact v.range_mapBaseChange_le_span_D_uniformizer

p2m_export "AlgebraicCurve.Place" "span_D_uniformizer_eq_top_of_subsingleton"
end CotangentEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringPolynomialFormallyUnramified : Prop :=
  ∀ v : Place K F,
    letI := v.polynomialAlgebra
    Subsingleton Ω[v.toValuationSubring⁄K[X]]

variable {K F}

theorem valSubringKaehlerSpanTop_of_polynomialFormallyUnramified
    (hfu : ValSubringPolynomialFormallyUnramified K F) :
    ValSubringKaehlerSpanTop K F :=
  fun v => v.span_D_uniformizer_eq_top_of_subsingleton (hfu v)

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

open IsDedekindDomain Polynomial IsLocalRing
open scoped TensorProduct

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring dCoord DCoordGenerates dCoord_ne_zero mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

section ResidueEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private noncomputable def _root_.AlgebraicCurve.Place.uniformizerSubring''' : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose

p2m_export "AlgebraicCurve.Place" "uniformizerSubring'''"
private theorem _root_.AlgebraicCurve.Place.irreducible_uniformizerSubring''' : Irreducible v.uniformizerSubring''' :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

p2m_export "AlgebraicCurve.Place" "irreducible_uniformizerSubring'''"
private theorem _root_.AlgebraicCurve.Place.maximalIdeal_eq_span_uniformizer :
    IsLocalRing.maximalIdeal v.toValuationSubring = Ideal.span {v.uniformizerSubring'''} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp v.irreducible_uniformizerSubring'''

p2m_export "AlgebraicCurve.Place" "maximalIdeal_eq_span_uniformizer"
private theorem _root_.AlgebraicCurve.Place.D_polynomialAlgebra_uniformizer :
    letI := v.polynomialAlgebra
    KaehlerDifferential.D K[X] v.toValuationSubring v.uniformizerSubring''' = 0 := by
  letI := v.polynomialAlgebra
  rw [show v.uniformizerSubring''' = algebraMap K[X] v.toValuationSubring X from
    (v.polynomialAlgebra_algebraMap_X).symm]
  exact (KaehlerDifferential.D K[X] v.toValuationSubring).map_algebraMap X

p2m_export "AlgebraicCurve.Place" "D_polynomialAlgebra_uniformizer"
private theorem _root_.AlgebraicCurve.Place.ker_algebraMap_residueField_eq_span :
    RingHom.ker (algebraMap v.toValuationSubring v.ResidueField)
      = Ideal.span {v.uniformizerSubring'''} := by
  rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue,
    v.maximalIdeal_eq_span_uniformizer]

p2m_export "AlgebraicCurve.Place" "ker_algebraMap_residueField_eq_span"
private theorem _root_.AlgebraicCurve.Place.formallyUnramified_polynomial_residueField_of_isSeparable
    [Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)] :
    letI := v.polynomialAlgebra
    Algebra.FormallyUnramified K[X] (IsLocalRing.ResidueField v.toValuationSubring) := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  haveI : Algebra.FormallyUnramified K (IsLocalRing.ResidueField v.toValuationSubring) :=
    Algebra.FormallyUnramified.of_isSeparable K _
  exact Algebra.FormallyUnramified.of_restrictScalars K K[X] _

p2m_export "AlgebraicCurve.Place" "formallyUnramified_polynomial_residueField_of_isSeparable"
private theorem _root_.AlgebraicCurve.Place.subsingleton_residueKaehler_of_isSeparable
    [Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)] :
    letI := v.polynomialAlgebra
    Subsingleton Ω[(IsLocalRing.ResidueField v.toValuationSubring)⁄K[X]] := by
  letI := v.polynomialAlgebra
  haveI := v.formallyUnramified_polynomial_residueField_of_isSeparable
  exact Algebra.FormallyUnramified.subsingleton_kaehlerDifferential

p2m_export "AlgebraicCurve.Place" "subsingleton_residueKaehler_of_isSeparable"
private theorem _root_.AlgebraicCurve.Place.subsingleton_residueTensor_polynomialKaehler_of_isSeparable
    [Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)] :
    letI := v.polynomialAlgebra
    Subsingleton (v.ResidueField ⊗[v.toValuationSubring] Ω[v.toValuationSubring⁄K[X]]) := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  haveI := v.subsingleton_residueKaehler_of_isSeparable
  refine subsingleton_of_forall_eq 0 fun t => ?_

  obtain ⟨c, rfl⟩ :=
    ((KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange K[X]
      v.toValuationSubring v.ResidueField
      Ideal.Quotient.mk_surjective) t).mp (Subsingleton.elim _ _)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ c
  simp only [KaehlerDifferential.kerCotangentToTensor_toCotangent]

  rw [v.ker_algebraMap_residueField_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rcases hy with rfl
    rw [v.D_polynomialAlgebra_uniformizer, TensorProduct.tmul_zero]
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add, TensorProduct.tmul_add, hy, hz, add_zero]
  | smul a y hy IH =>

    have hres : (algebraMap v.toValuationSubring v.ResidueField y) = 0 := by
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff,
        v.maximalIdeal_eq_span_uniformizer]
      exact hy
    rw [smul_eq_mul, Derivation.leibniz, TensorProduct.tmul_add,
      TensorProduct.tmul_smul, IH, smul_zero, zero_add,
      ← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hres,
      TensorProduct.zero_tmul]

p2m_export "AlgebraicCurve.Place" "subsingleton_residueTensor_polynomialKaehler_of_isSeparable"
private theorem _root_.AlgebraicCurve.Place.finite_polynomialKaehler_of_finite_kaehler
    [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]] :
    letI := v.polynomialAlgebra
    Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K[X]] := by
  letI := v.polynomialAlgebra
  letI := v.polynomialIsScalarTower
  exact Module.Finite.of_surjective
    (KaehlerDifferential.map K K[X] v.toValuationSubring v.toValuationSubring)
    (KaehlerDifferential.map_surjective K K[X] v.toValuationSubring)

p2m_export "AlgebraicCurve.Place" "finite_polynomialKaehler_of_finite_kaehler"
private theorem _root_.AlgebraicCurve.Place.subsingleton_polynomialKaehler_of_isSeparable_of_finite
    [Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)]
    [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]] :
    letI := v.polynomialAlgebra
    Subsingleton Ω[v.toValuationSubring⁄K[X]] := by
  letI := v.polynomialAlgebra
  haveI := v.finite_polynomialKaehler_of_finite_kaehler
  haveI := v.subsingleton_residueTensor_polynomialKaehler_of_isSeparable
  exact (IsLocalRing.subsingleton_tensorProduct (R := v.toValuationSubring)).mp ‹_›

p2m_export "AlgebraicCurve.Place" "subsingleton_polynomialKaehler_of_isSeparable_of_finite"
end ResidueEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringKaehlerFinite : Prop :=
  ∀ v : Place K F, Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]

variable {K F}

theorem valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_isSeparable
    [∀ v : Place K F, Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)]
    (hfin : ValSubringKaehlerFinite K F) :
    ValSubringPolynomialFormallyUnramified K F := by
  intro v
  haveI := hfin v
  exact v.subsingleton_polynomialKaehler_of_isSeparable_of_finite

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

open IsDedekindDomain Polynomial IsLocalRing
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring dCoord DCoordGenerates dCoord_ne_zero mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

section EftEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.finite_kaehler_of_essFiniteType [Algebra.EssFiniteType K v.toValuationSubring] :
    Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K] :=
  KaehlerDifferential.finite K v.toValuationSubring

p2m_export "AlgebraicCurve.Place" "finite_kaehler_of_essFiniteType"
private theorem _root_.AlgebraicCurve.Place.essFiniteType_of_exists_finiteType_isLocalization
    (h : ∃ (S₀ : Subalgebra K v.toValuationSubring) (M : Submonoid S₀),
      Algebra.FiniteType K S₀ ∧ IsLocalization M v.toValuationSubring) :
    Algebra.EssFiniteType K v.toValuationSubring :=
  (Algebra.essFiniteType_iff_exists_subalgebra K v.toValuationSubring).mpr
    (h.imp fun _ ⟨M, hft, hloc⟩ => ⟨M, hft, hloc⟩)

p2m_export "AlgebraicCurve.Place" "essFiniteType_of_exists_finiteType_isLocalization"
end EftEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringEssFiniteType : Prop :=
  ∀ v : Place K F, Algebra.EssFiniteType K v.toValuationSubring

def ValSubringFiniteTypeModel : Prop :=
  ∀ v : Place K F,
    ∃ (S₀ : Subalgebra K v.toValuationSubring) (M : Submonoid S₀),
      Algebra.FiniteType K S₀ ∧ IsLocalization M v.toValuationSubring

variable {K F}

theorem valSubringKaehlerFinite_of_essFiniteType
    (heft : ValSubringEssFiniteType K F) :
    ValSubringKaehlerFinite K F := fun v =>
  haveI := heft v
  v.finite_kaehler_of_essFiniteType

theorem valSubringEssFiniteType_of_finiteTypeModel
    (hmodel : ValSubringFiniteTypeModel K F) :
    ValSubringEssFiniteType K F := fun v =>
  v.essFiniteType_of_exists_finiteType_isLocalization (hmodel v)

theorem valSubringEssFiniteType_iff_finiteTypeModel :
    ValSubringEssFiniteType K F ↔ ValSubringFiniteTypeModel K F := by
  constructor
  · intro heft v
    haveI := heft v
    exact (Algebra.essFiniteType_iff_exists_subalgebra K v.toValuationSubring).mp (heft v)
  · exact valSubringEssFiniteType_of_finiteTypeModel

theorem valSubringKaehlerFinite_of_finiteTypeModel
    (hmodel : ValSubringFiniteTypeModel K F) :
    ValSubringKaehlerFinite K F :=
  valSubringKaehlerFinite_of_essFiniteType
    (valSubringEssFiniteType_of_finiteTypeModel hmodel)

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

open IsDedekindDomain Polynomial IsLocalRing
namespace ValuationSubring
p2m_export "ValuationSubring" "comap idealOfLE mem_comap prime_idealOfLE toSubring ext zero_mem ofPrime_top mem_nonunits_iff ofPrime mem_or_inv_mem' mem_top toSubring_injective mul_mem mem_or_inv_mem add_mem eq_top_iff valuation inclusion ofPrime_idealOfLE ofPrime_bot"
p2m_open "ValuationSubring"

variable {F : Type*} [Field F]

private theorem ofPrime_congr_s12 {R : ValuationSubring F} {P Q : Ideal R}
    [P.IsPrime] [Q.IsPrime] (h : P = Q) : R.ofPrime P = R.ofPrime Q := by
  subst h; congr

theorem eq_top_of_idealOfLE_eq_bot_s12 {R S : ValuationSubring F} (h : R ≤ S)
    (hbot : idealOfLE R S h = ⊥) : S = ⊤ := by
  haveI : IsDomain R := inferInstanceAs (IsDomain R.toSubring)
  rw [← ofPrime_idealOfLE R S h, ofPrime_congr_s12 hbot, ofPrime_bot]

theorem idealOfLE_ne_bot_of_ne_top_s12 {R S : ValuationSubring F} (h : R ≤ S)
    (hS : S ≠ ⊤) : idealOfLE R S h ≠ ⊥ :=
  fun hbot => hS (eq_top_of_idealOfLE_eq_bot_s12 h hbot)

theorem eq_of_isDiscreteValuationRing_of_le_s12 {R S : ValuationSubring F}
    [IsDiscreteValuationRing R] (h : R ≤ S) (hS : S ≠ ⊤) : R = S := by

  haveI : IsDomain R := inferInstanceAs (IsDomain R.toSubring)
  haveI : IsDedekindDomain R := IsPrincipalIdealRing.isDedekindDomain R

  have hne : idealOfLE R S h ≠ ⊥ := idealOfLE_ne_bot_of_ne_top_s12 h hS
  have hmax : (idealOfLE R S h).IsMaximal := (prime_idealOfLE R S h).isMaximal hne
  have heq : idealOfLE R S h = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hmax
  rw [← ofPrime_idealOfLE R S h, ofPrime_congr_s12 heq, ofPrime_top]

end ValuationSubring
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring dCoord DCoordGenerates dCoord_ne_zero mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

section CenterIdeal

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

variable (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))

@[reducible] private noncomputable def _root_.AlgebraicCurve.Place.modelInclusion : A →+* v.toValuationSubring :=
  (Subring.inclusion (show A.toSubring ≤ v.toValuationSubring.toSubring from hA))

p2m_export "AlgebraicCurve.Place" "modelInclusion"
@[scoped simp] theorem coe_modelInclusion (a : A) :
    ((v.modelInclusion A hA a : v.toValuationSubring) : F) = (a : F) := rfl

@[reducible] private noncomputable def _root_.AlgebraicCurve.Place.modelAlgebra : Algebra A v.toValuationSubring :=
  (v.modelInclusion A hA).toAlgebra

p2m_export "AlgebraicCurve.Place" "modelAlgebra"
@[reducible] private noncomputable def _root_.AlgebraicCurve.Place.centerIdeal : Ideal A :=
  letI := v.modelAlgebra A hA
  (IsLocalRing.maximalIdeal v.toValuationSubring).comap (algebraMap A v.toValuationSubring)

p2m_export "AlgebraicCurve.Place" "centerIdeal"
scoped instance centerIdeal_isPrime : (v.centerIdeal A hA).IsPrime :=
  letI := v.modelAlgebra A hA
  Ideal.comap_isPrime _ _

private theorem _root_.AlgebraicCurve.Place.isUnit_modelInclusion_of_not_mem_centerIdeal {s : A}
    (hs : s ∉ v.centerIdeal A hA) :
    IsUnit (v.modelInclusion A hA s) := by
  letI := v.modelAlgebra A hA

  rw [centerIdeal, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not] at hs
  exact hs

p2m_export "AlgebraicCurve.Place" "isUnit_modelInclusion_of_not_mem_centerIdeal"
private theorem _root_.AlgebraicCurve.Place.isUnit_modelInclusion_of_mem_primeCompl (s : (v.centerIdeal A hA).primeCompl) :
    IsUnit (v.modelInclusion A hA (s : A)) :=
  v.isUnit_modelInclusion_of_not_mem_centerIdeal A hA s.2

p2m_export "AlgebraicCurve.Place" "isUnit_modelInclusion_of_mem_primeCompl"
private theorem _root_.AlgebraicCurve.Place.modelAlgebra_isScalarTower :
    letI := v.modelAlgebra A hA
    IsScalarTower K A v.toValuationSubring := by
  letI := v.modelAlgebra A hA
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  apply Subtype.ext
  simp only [coe_modelInclusion, RingHom.algebraMap_toAlgebra]
  rfl

p2m_export "AlgebraicCurve.Place" "modelAlgebra_isScalarTower"
private theorem _root_.AlgebraicCurve.Place.essFiniteType_of_finiteType_isLocalization_centerIdeal
    [Algebra.FiniteType K A]
    (hloc : letI := v.modelAlgebra A hA
            IsLocalization.AtPrime v.toValuationSubring (v.centerIdeal A hA)) :
    Algebra.EssFiniteType K v.toValuationSubring := by
  letI := v.modelAlgebra A hA
  haveI := v.modelAlgebra_isScalarTower A hA
  haveI : Algebra.EssFiniteType A v.toValuationSubring :=
    Algebra.EssFiniteType.of_isLocalization _ (v.centerIdeal A hA).primeCompl
  exact Algebra.EssFiniteType.comp K A v.toValuationSubring

p2m_export "AlgebraicCurve.Place" "essFiniteType_of_finiteType_isLocalization_centerIdeal"
end CenterIdeal
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringDedekindModel : Prop :=
  ∀ v : Place K F,
    ∃ (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F)),
      Algebra.FiniteType K A ∧
      (letI := v.modelAlgebra A hA
       IsLocalization.AtPrime v.toValuationSubring (v.centerIdeal A hA))

variable {K F}

theorem valSubringEssFiniteType_of_dedekindModel
    (hmodel : ValSubringDedekindModel K F) :
    ValSubringEssFiniteType K F := fun v => by
  obtain ⟨A, hA, hft, hloc⟩ := hmodel v
  exact v.essFiniteType_of_finiteType_isLocalization_centerIdeal A hA hloc

theorem valSubringFiniteTypeModel_of_dedekindModel
    (hmodel : ValSubringDedekindModel K F) :
    ValSubringFiniteTypeModel K F :=
  valSubringEssFiniteType_iff_finiteTypeModel.mp
    (valSubringEssFiniteType_of_dedekindModel hmodel)

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring dCoord DCoordGenerates dCoord_ne_zero mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

section CenterNonzero

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
  (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))

private theorem inv_mem_of_not_mem_centerIdeal {a : A} (ha : a ∉ v.centerIdeal A hA) :
    ((a : F))⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨u, hu⟩ := v.isUnit_modelInclusion_of_not_mem_centerIdeal A hA ha
  have huF : ((u : v.toValuationSubring) : F) = (a : F) :=
    congrArg (Subtype.val : v.toValuationSubring → F) hu
  have huinvF : ((u⁻¹ : v.toValuationSubringˣ).1 : F) * (a : F) = 1 := by
    have h1 : ((u⁻¹ : v.toValuationSubringˣ).1 : F) * ((u : v.toValuationSubring) : F)
        = ((1 : v.toValuationSubring) : F) :=
      congrArg (Subtype.val : v.toValuationSubring → F) u.inv_mul
    rw [huF] at h1; exact h1
  have : ((u⁻¹ : v.toValuationSubringˣ).1 : F) = (a : F)⁻¹ :=
    eq_inv_of_mul_eq_one_left huinvF
  exact this ▸ ((u⁻¹ : v.toValuationSubringˣ).1 : v.toValuationSubring).2

private theorem div_mem_of_not_mem_centerIdeal (r : A) {a : A}
    (ha : a ∉ v.centerIdeal A hA) :
    (r : F) / (a : F) ∈ v.toValuationSubring := by
  rw [div_eq_mul_inv]
  exact v.toValuationSubring.toSubring.mul_mem (hA r.2)
    (inv_mem_of_not_mem_centerIdeal v A hA ha)

private theorem _root_.AlgebraicCurve.Place.centerIdeal_ne_bot_of_isFractionRing [IsFractionRing A F] :
    v.centerIdeal A hA ≠ ⊥ := by

  obtain ⟨f, hf⟩ : ∃ f : F, f ∉ v.toValuationSubring := by
    by_contra h; push Not at h
    exact v.ne_top' (ValuationSubring.toSubring_injective (top_le_iff.mp fun x _ => h x))
  obtain ⟨r, s, hs, hfrs⟩ := IsFractionRing.div_surjective (A := A) f

  have hsP : s ∈ v.centerIdeal A hA := by
    by_contra hsP
    apply hf
    have : algebraMap A F r / algebraMap A F s ∈ v.toValuationSubring :=
      div_mem_of_not_mem_centerIdeal v A hA r hsP
    rwa [hfrs] at this

  intro hbot
  exact (nonZeroDivisors.ne_zero hs) (Ideal.mem_bot.mp (hbot ▸ hsP))

p2m_export "AlgebraicCurve.Place" "centerIdeal_ne_bot_of_isFractionRing"
end CenterNonzero
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

section LocalizationSubalgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
  (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))

@[reducible] private noncomputable def _root_.AlgebraicCurve.Place.centerLocalizationSubalgebra [IsFractionRing A F] :
    Subalgebra A F :=
  Localization.subalgebra.ofField F (v.centerIdeal A hA).primeCompl
    (v.centerIdeal A hA).primeCompl_le_nonZeroDivisors

p2m_export "AlgebraicCurve.Place" "centerLocalizationSubalgebra"
scoped instance centerLocalizationSubalgebra_isLocalization [IsFractionRing A F] :
    IsLocalization.AtPrime (v.centerLocalizationSubalgebra A hA) (v.centerIdeal A hA) :=
  Localization.subalgebra.isLocalization_ofField F _ _

scoped instance centerLocalizationSubalgebra_isDomain [IsFractionRing A F] :
    IsDomain (v.centerLocalizationSubalgebra A hA) :=
  inferInstanceAs (IsDomain (_ : Subalgebra A F))

private theorem _root_.AlgebraicCurve.Place.centerLocalizationSubalgebra_isDiscreteValuationRing
    [IsDedekindDomain A] [IsFractionRing A F] :
    IsDiscreteValuationRing (v.centerLocalizationSubalgebra A hA) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A
    (v.centerIdeal_ne_bot_of_isFractionRing A hA) _

p2m_export "AlgebraicCurve.Place" "centerLocalizationSubalgebra_isDiscreteValuationRing"
scoped instance centerLocalizationSubalgebra_isFractionRing [IsFractionRing A F] :
    IsFractionRing (v.centerLocalizationSubalgebra A hA) F :=
  inferInstanceAs (IsFractionRing (Localization.subalgebra.ofField F _ _) F)

private theorem _root_.AlgebraicCurve.Place.centerLocalizationSubalgebra_subset [IsFractionRing A F] :
    ((v.centerLocalizationSubalgebra A hA : Subalgebra A F) : Set F)
      ⊆ (v.toValuationSubring : Set F) := by
  intro x hx

  obtain ⟨a, s, hs, rfl⟩ := hx

  rw [← div_eq_mul_inv]
  exact div_mem_of_not_mem_centerIdeal v A hA a hs

p2m_export "AlgebraicCurve.Place" "centerLocalizationSubalgebra_subset"
private noncomputable def _root_.AlgebraicCurve.Place.centerLocalizationValuationSubring
    [IsDedekindDomain A] [IsFractionRing A F] : ValuationSubring F where
  toSubring := (v.centerLocalizationSubalgebra A hA).toSubring
  mem_or_inv_mem' x := by
    haveI := v.centerLocalizationSubalgebra_isDiscreteValuationRing A hA
    rcases ValuationRing.isInteger_or_isInteger (v.centerLocalizationSubalgebra A hA) x with
      ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl (ha ▸ a.2)
    · exact Or.inr (ha ▸ a.2)

p2m_export "AlgebraicCurve.Place" "centerLocalizationValuationSubring"
theorem coe_centerLocalizationValuationSubring [IsDedekindDomain A] [IsFractionRing A F] :
    ((v.centerLocalizationValuationSubring A hA : ValuationSubring F) : Set F)
      = ((v.centerLocalizationSubalgebra A hA : Subalgebra A F) : Set F) := rfl

scoped instance centerLocalizationValuationSubring_isDiscreteValuationRing
    [IsDedekindDomain A] [IsFractionRing A F] :
    IsDiscreteValuationRing (v.centerLocalizationValuationSubring A hA) :=
  v.centerLocalizationSubalgebra_isDiscreteValuationRing A hA

private theorem _root_.AlgebraicCurve.Place.centerLocalizationValuationSubring_le [IsDedekindDomain A] [IsFractionRing A F] :
    v.centerLocalizationValuationSubring A hA ≤ v.toValuationSubring :=
  v.centerLocalizationSubalgebra_subset A hA

p2m_export "AlgebraicCurve.Place" "centerLocalizationValuationSubring_le"
private theorem _root_.AlgebraicCurve.Place.centerLocalizationValuationSubring_eq [IsDedekindDomain A] [IsFractionRing A F] :
    v.centerLocalizationValuationSubring A hA = v.toValuationSubring :=
  ValuationSubring.eq_of_isDiscreteValuationRing_of_le_s12
    (v.centerLocalizationValuationSubring_le A hA) v.ne_top'

p2m_export "AlgebraicCurve.Place" "centerLocalizationValuationSubring_eq"
theorem coe_centerLocalizationSubalgebra_eq [IsDedekindDomain A] [IsFractionRing A F] :
    ((v.centerLocalizationSubalgebra A hA : Subalgebra A F) : Set F)
      = (v.toValuationSubring : Set F) := by
  rw [← coe_centerLocalizationValuationSubring]
  exact congrArg (SetLike.coe) (v.centerLocalizationValuationSubring_eq A hA)

private theorem _root_.AlgebraicCurve.Place.mem_centerLocalizationSubalgebra_of_mem [IsDedekindDomain A] [IsFractionRing A F]
    (x : F) (hx : x ∈ v.toValuationSubring) :
    x ∈ (v.centerLocalizationSubalgebra A hA : Subalgebra A F) := by
  rw [← SetLike.mem_coe, coe_centerLocalizationSubalgebra_eq]; exact hx

p2m_export "AlgebraicCurve.Place" "mem_centerLocalizationSubalgebra_of_mem"
private theorem _root_.AlgebraicCurve.Place.isLocalization_centerIdeal_of_isDedekindDomain
    [IsDedekindDomain A] [IsFractionRing A F] :
    letI := v.modelAlgebra A hA
    IsLocalization.AtPrime v.toValuationSubring (v.centerIdeal A hA) := by
  letI := v.modelAlgebra A hA
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  ·
    exact v.isUnit_modelInclusion_of_mem_primeCompl A hA
  ·

    intro x
    have hxP : (x : F) ∈ (v.centerLocalizationSubalgebra A hA : Subalgebra A F) :=
      v.mem_centerLocalizationSubalgebra_of_mem A hA (x : F) x.2
    obtain ⟨a, s, hs, hxeq⟩ := hxP

    refine ⟨⟨a, ⟨s, hs⟩⟩, Subtype.ext ?_⟩
    show (x : F) * ((s : A) : F) = ((a : A) : F)
    have halg_s : algebraMap A F s = ((s : A) : F) := rfl
    have halg_a : algebraMap A F a = ((a : A) : F) := rfl
    have hs0 : algebraMap A F s ≠ 0 := by
      intro hF
      have hsne : s ≠ 0 := fun h => (h ▸ hs) (Ideal.zero_mem _)
      exact hsne (Subtype.ext (p := (· ∈ A)) (halg_s ▸ hF))
    rw [← halg_s, ← halg_a, hxeq, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  ·
    intro a₁ a₂ h
    have hF : (a₁ : F) = (a₂ : F) :=
      congrArg (Subtype.val : v.toValuationSubring → F) h
    exact ⟨1, by rw [show a₁ = a₂ from Subtype.ext hF]⟩

p2m_export "AlgebraicCurve.Place" "isLocalization_centerIdeal_of_isDedekindDomain"
end LocalizationSubalgebra
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def ValSubringDedekindFractionModel : Prop :=
  ∀ v : Place K F,
    ∃ (A : Subalgebra K F) (_ : (A : Set F) ⊆ (v.toValuationSubring : Set F)),
      Algebra.FiniteType K A ∧ IsDedekindDomain A ∧ IsFractionRing A F

variable {K F}

theorem valSubringDedekindModel_of_dedekindFractionModel
    (hfrac : ValSubringDedekindFractionModel K F) :
    ValSubringDedekindModel K F := fun v => by
  obtain ⟨A, hA, hft, hded, hfracA⟩ := hfrac v
  exact ⟨A, hA, hft, v.isLocalization_centerIdeal_of_isDedekindDomain A hA⟩

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring dCoord DCoordGenerates dCoord_ne_zero mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

section IntegrallyClosed

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.isIntegrallyClosed_toValuationSubring :
    IsIntegrallyClosed v.toValuationSubring := inferInstance

p2m_export "AlgebraicCurve.Place" "isIntegrallyClosed_toValuationSubring"
private theorem _root_.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral {x : F}
    (hx : IsIntegral v.toValuationSubring x) :
    x ∈ v.toValuationSubring := by
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff F).mp (v.isIntegrallyClosed_toValuationSubring) hx
  exact hy ▸ y.2

p2m_export "AlgebraicCurve.Place" "mem_valuationSubring_of_isIntegral"
variable (B : Subalgebra K F) (hB : (B : Set F) ⊆ (v.toValuationSubring : Set F))

include hB in
private theorem _root_.AlgebraicCurve.Place.modelAlgebra_isScalarTower_top :
    letI := v.modelAlgebra B hB
    IsScalarTower B v.toValuationSubring F := by
  letI := v.modelAlgebra B hB
  refine IsScalarTower.of_algebraMap_eq fun b => ?_
  rfl

p2m_export "AlgebraicCurve.Place" "modelAlgebra_isScalarTower_top"
include hB in
private theorem _root_.AlgebraicCurve.Place.mem_valuationSubring_of_isIntegral_subalgebra {x : F}
    (hx : IsIntegral B x) :
    x ∈ v.toValuationSubring := by
  letI := v.modelAlgebra B hB
  haveI := v.modelAlgebra_isScalarTower_top B hB
  exact v.mem_valuationSubring_of_isIntegral (hx.tower_top (A := v.toValuationSubring))

p2m_export "AlgebraicCurve.Place" "mem_valuationSubring_of_isIntegral_subalgebra"
include hB in
private theorem _root_.AlgebraicCurve.Place.integralClosure_subset_valuationSubring :
    ((integralClosure B F : Subalgebra B F) : Set F)
      ⊆ (v.toValuationSubring : Set F) := fun _ hx =>
  v.mem_valuationSubring_of_isIntegral_subalgebra B hB hx

p2m_export "AlgebraicCurve.Place" "integralClosure_subset_valuationSubring"
end IntegrallyClosed
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

section TwoCharts

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def IsAffineChart (A : Subalgebra K F) : Prop :=
  Algebra.FiniteType K A ∧ IsDedekindDomain A ∧ IsFractionRing A F

def ValSubringTwoAffineCharts : Prop :=
  ∃ A₀ A₁ : Subalgebra K F, IsAffineChart K F A₀ ∧ IsAffineChart K F A₁
    ∧ ∀ v : Place K F, (A₀ : Set F) ⊆ (v.toValuationSubring : Set F)
        ∨ (A₁ : Set F) ⊆ (v.toValuationSubring : Set F)

variable {K F}

theorem valSubringDedekindFractionModel_of_twoAffineCharts
    (h : ValSubringTwoAffineCharts K F) :
    ValSubringDedekindFractionModel K F := fun v => by
  obtain ⟨A₀, A₁, ⟨hft₀, hded₀, hfrac₀⟩, ⟨hft₁, hded₁, hfrac₁⟩, hcover⟩ := h
  rcases hcover v with h₀ | h₁
  · exact ⟨A₀, h₀, hft₀, hded₀, hfrac₀⟩
  · exact ⟨A₁, h₁, hft₁, hded₁, hfrac₁⟩

theorem valSubringDedekindModel_of_twoAffineCharts
    (h : ValSubringTwoAffineCharts K F) :
    ValSubringDedekindModel K F :=
  valSubringDedekindModel_of_dedekindFractionModel
    (valSubringDedekindFractionModel_of_twoAffineCharts h)

end TwoCharts
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

section Gates

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring dCoord DCoordGenerates dCoord_ne_zero mem_maximalIdeal_iff_ord_pos" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
@[reducible] private noncomputable def _root_.AlgebraicCurve.Place.toKSubalgebra (v : Place K F) : Subalgebra K F where
  __ := v.toValuationSubring.toSubring
  algebraMap_mem' c := v.algebraMap_mem' c

end Place
p2m_export "AlgebraicCurve" "Place.toKSubalgebra"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.coe_toKSubalgebra (v : Place K F) :
    (v.toKSubalgebra : Set F) = (v.toValuationSubring : Set F) := rfl

end Place
p2m_export "AlgebraicCurve" "Place.coe_toKSubalgebra"
theorem gate_adjoin_subset_valuationSubring_of_mem (v : Place K F) {t : F}
    (ht : t ∈ v.toValuationSubring) :
    ((Algebra.adjoin K {t} : Subalgebra K F) : Set F)
      ⊆ (v.toValuationSubring : Set F) := by
  rw [← v.coe_toKSubalgebra]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)

end Gates
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

p2m_open "IsLocalRing IntermediateField P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.IntermediateField IntermediateField.algebraAdjoinAdjoin"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

section AdjoinRingProperties

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.Transcendental.isPrincipalIdealRing_adjoin_s12 {t : F} (ht : Transcendental K t) :
    IsPrincipalIdealRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  IsPrincipalIdealRing.of_surjective
    (Polynomial.algEquivOfTranscendental K t ht).toRingHom
    (Polynomial.algEquivOfTranscendental K t ht).surjective

p2m_alias "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.Transcendental.isPrincipalIdealRing_adjoin_s12" "Transcendental.isPrincipalIdealRing_adjoin_s12"
private theorem _root_.Transcendental.isDedekindDomain_adjoin_s12 {t : F} (ht : Transcendental K t) :
    IsDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isPrincipalIdealRing_adjoin_s12
  inferInstance

p2m_alias "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.Transcendental.isDedekindDomain_adjoin_s12" "Transcendental.isDedekindDomain_adjoin_s12"
private theorem _root_.Transcendental.isIntegrallyClosed_adjoin_s12 {t : F} (ht : Transcendental K t) :
    IsIntegrallyClosed ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isDedekindDomain_adjoin_s12
  inferInstance

p2m_alias "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.Transcendental.isIntegrallyClosed_adjoin_s12" "Transcendental.isIntegrallyClosed_adjoin_s12"
private theorem _root_.Transcendental.isNoetherianRing_adjoin_s12 {t : F} (ht : Transcendental K t) :
    IsNoetherianRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := ht.isPrincipalIdealRing_adjoin_s12
  inferInstance

p2m_alias "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.Transcendental.isNoetherianRing_adjoin_s12" "Transcendental.isNoetherianRing_adjoin_s12"
private theorem _root_.Algebra.FiniteType.adjoin_singleton_s12 (t : F) :
    Algebra.FiniteType K ↥(Algebra.adjoin K ({t} : Set F)) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)

p2m_alias "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.Algebra.FiniteType.adjoin_singleton_s12" "Algebra.FiniteType.adjoin_singleton_s12"
private theorem _root_.Transcendental.inv_s12 {t : F} (ht : Transcendental K t) :
    Transcendental K t⁻¹ := by
  rw [Transcendental, IsAlgebraic.inv_iff]; exact ht

p2m_alias "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.Transcendental.inv_s12" "Transcendental.inv_s12"
end AdjoinRingProperties
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

section TranscendentalChart

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]

@[reducible] noncomputable def transcendentalChart (t : F) : Subalgebra K F :=
  (integralClosure (Algebra.adjoin K ({t} : Set F)) F).restrictScalars K

theorem coe_transcendentalChart (t : F) :
    (transcendentalChart K t : Set F)
      = ((integralClosure (Algebra.adjoin K ({t} : Set F)) F : Subalgebra _ F) : Set F) :=
  rfl

variable {K}

theorem transcendentalChart_subset_valuationSubring_of_mem (v : Place K F)
    {t : F} (ht : t ∈ v.toValuationSubring) :
    (transcendentalChart K t : Set F) ⊆ (v.toValuationSubring : Set F) := by
  rw [coe_transcendentalChart]
  exact v.integralClosure_subset_valuationSubring _
    (gate_adjoin_subset_valuationSubring_of_mem v ht)

theorem transcendentalChart_subset_or_inv_subset (v : Place K F) (t : F) :
    (transcendentalChart K t : Set F) ⊆ (v.toValuationSubring : Set F)
      ∨ (transcendentalChart K t⁻¹ : Set F) ⊆ (v.toValuationSubring : Set F) :=
  (v.toValuationSubring.mem_or_inv_mem t).imp
    (transcendentalChart_subset_valuationSubring_of_mem v)
    (transcendentalChart_subset_valuationSubring_of_mem v)

end TranscendentalChart
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

section IsAffineChartEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section

variable (B : Subalgebra K F)

theorem isScalarTower_integralClosure_subalgebra :
    IsScalarTower K B ↥(integralClosure B F) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  exact Subtype.ext rfl

theorem finiteType_integralClosure_of_moduleFinite (hft : Algebra.FiniteType K B)
    (hfin : Module.Finite B ↥(integralClosure B F)) :
    Algebra.FiniteType K ↥(integralClosure B F) :=
  haveI := isScalarTower_integralClosure_subalgebra B
  haveI := hfin
  Algebra.FiniteType.trans (S := B) hft inferInstance

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

theorem isDedekindDomain_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    IsDedekindDomain ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) := by
  haveI := ht.isDedekindDomain_adjoin_s12
  exact integralClosure.isDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) ↥(K⟮t⟯) F

theorem isFractionRing_integralClosure_adjoin (t : F) [FiniteDimensional K⟮t⟯ F] :
    IsFractionRing ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) F :=
  integralClosure.isFractionRing_of_finite_extension
    (A := ↥(Algebra.adjoin K ({t} : Set F))) ↥(K⟮t⟯) F

theorem moduleFinite_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    Module.Finite ↥(Algebra.adjoin K ({t} : Set F))
      ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) := by
  haveI := ht.isIntegrallyClosed_adjoin_s12
  haveI := ht.isNoetherianRing_adjoin_s12
  exact IsIntegralClosure.finite (A := ↥(Algebra.adjoin K ({t} : Set F)))
    (K := ↥(K⟮t⟯)) (L := F) (integralClosure ↥(Algebra.adjoin K ({t} : Set F)) F)

theorem finiteType_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.FiniteType K ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) :=
  finiteType_integralClosure_of_moduleFinite (Algebra.adjoin K {t})
    (Algebra.FiniteType.adjoin_singleton_s12 t) (moduleFinite_integralClosure_adjoin ht)

theorem isAffineChart_restrictScalars_integralClosure (B : Subalgebra K F)
    (hft : Algebra.FiniteType K ↥(integralClosure B F))
    (hded : IsDedekindDomain ↥(integralClosure B F))
    (hfrac : IsFractionRing ↥(integralClosure B F) F) :
    IsAffineChart K F ((integralClosure B F).restrictScalars K) :=
  ⟨hft, hded, hfrac⟩

theorem isAffineChart_transcendentalChart {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    IsAffineChart K F (transcendentalChart K t) :=
  isAffineChart_restrictScalars_integralClosure (Algebra.adjoin K {t})
    (finiteType_integralClosure_adjoin ht)
    (isDedekindDomain_integralClosure_adjoin ht)
    (isFractionRing_integralClosure_adjoin t)

end IsAffineChartEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

section SeparatingTranscendental

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def HasSeparatingTranscendental : Prop :=
  ∃ t : F, Transcendental K t
    ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F
    ∧ FiniteDimensional K⟮t⁻¹⟯ F ∧ Algebra.IsSeparable K⟮t⁻¹⟯ F

variable {K F}

theorem valSubringTwoAffineCharts_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringTwoAffineCharts K F := by
  obtain ⟨t, ht, hfin, hsep, hfin', hsep'⟩ := h
  exact ⟨transcendentalChart K t, transcendentalChart K t⁻¹,
    isAffineChart_transcendentalChart ht,
    isAffineChart_transcendentalChart ht.inv_s12,
    fun v => transcendentalChart_subset_or_inv_subset v t⟩

theorem valSubringDedekindModel_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringDedekindModel K F :=
  valSubringDedekindModel_of_twoAffineCharts
    (valSubringTwoAffineCharts_of_hasSeparatingTranscendental h)

end SeparatingTranscendental
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

p2m_open "IntermediateField P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.IntermediateField"

namespace IntermediateField
p2m_export "IntermediateField" "toAlgebra val inclusion ext adjoin_simple_le_iff equivOfEq adjoin comap mem_top restrictScalars mem_bot mem_adjoin_simple_self smul_mem map"
p2m_open "IntermediateField"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adjoin_simple_inv_s12 (t : F) : K⟮t⁻¹⟯ = K⟮t⟯ := by
  refine le_antisymm (adjoin_simple_le_iff.mpr ?_) (adjoin_simple_le_iff.mpr ?_)
  · exact inv_mem (mem_adjoin_simple_self K t)
  · have h : (t⁻¹)⁻¹ ∈ (K⟮t⁻¹⟯ : IntermediateField K F) :=
      inv_mem (mem_adjoin_simple_self K t⁻¹)
    rwa [inv_inv] at h

theorem algebraMap_comp_equivOfEq_s12 {S T : IntermediateField K F} (h : S = T) :
    (algebraMap T F).comp ((IntermediateField.equivOfEq h).toRingEquiv : S →+* T)
      = ((RingEquiv.refl F : F ≃+* F) : F →+* F).comp (algebraMap S F) := by
  ext x; rfl

theorem finiteDimensional_of_eq_s12 {S T : IntermediateField K F} (h : S = T)
    [FiniteDimensional ↥S F] : FiniteDimensional ↥T F :=
  Module.Finite.of_equiv_equiv (IntermediateField.equivOfEq h).toRingEquiv (RingEquiv.refl F)
    (algebraMap_comp_equivOfEq_s12 h)

theorem isSeparable_of_eq_s12 {S T : IntermediateField K F} (h : S = T)
    [Algebra.IsSeparable ↥S F] : Algebra.IsSeparable ↥T F :=
  Algebra.IsSeparable.of_equiv_equiv (IntermediateField.equivOfEq h).toRingEquiv
    (RingEquiv.refl F) (algebraMap_comp_equivOfEq_s12 h)

theorem finiteDimensional_adjoin_inv_s12 (t : F) [FiniteDimensional K⟮t⟯ F] :
    FiniteDimensional K⟮t⁻¹⟯ F :=
  finiteDimensional_of_eq_s12 (adjoin_simple_inv_s12 t).symm

theorem isSeparable_adjoin_inv_s12 (t : F) [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.IsSeparable K⟮t⁻¹⟯ F :=
  isSeparable_of_eq_s12 (adjoin_simple_inv_s12 t).symm

end IntermediateField
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

p2m_open "IntermediateField P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.IntermediateField"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

section AbstractEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (hspan : ValSubringKaehlerSpanTop K F) (v : Place K F) :
    v.DCoordGenerates := by
  constructor
  rw [eq_top_iff,
    ← KaehlerDifferential.span_range_map_derivation_of_isLocalization (R := K)
      (S := v.toValuationSubring) (T := F) (nonZeroDivisors v.toValuationSubring),
    Submodule.span_le]
  rintro _ ⟨f, rfl⟩

  have hDf : KaehlerDifferential.D K v.toValuationSubring f
      ∈ (⊤ : Submodule v.toValuationSubring Ω[v.toValuationSubring⁄K]) := Submodule.mem_top
  rw [← hspan v] at hDf
  have hmap : (KaehlerDifferential.map K K v.toValuationSubring F ∘
        KaehlerDifferential.D K v.toValuationSubring) f
      ∈ Submodule.map (KaehlerDifferential.map K K v.toValuationSubring F)
        (Submodule.span v.toValuationSubring _) :=
    Submodule.mem_map_of_mem hDf
  rw [Submodule.map_span, Set.image_singleton,
    v.kaehlerMap_subring_D_uniformizer] at hmap

  exact Submodule.span_le_restrictScalars v.toValuationSubring F {v.dCoord} hmap

end AbstractEngine
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

noncomputable section

set_option linter.unusedSectionVars false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

section PerPlaceSupply

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.isSeparable_residueField_of_perfectField_of_finiteResidue
    [PerfectField K] (v : Place K F) [v.FiniteResidue] :
    Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) := by
  haveI : Module.Finite K (IsLocalRing.ResidueField v.toValuationSubring) :=
    Place.FiniteResidue.finite
  haveI : Algebra.IsAlgebraic K (IsLocalRing.ResidueField v.toValuationSubring) :=
    Algebra.IsAlgebraic.of_finite K _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end Place
p2m_export "AlgebraicCurve" "Place.isSeparable_residueField_of_perfectField_of_finiteResidue"
theorem isSeparable_residueField_forall_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue] :
    ∀ v : Place K F,
      Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) :=
  fun v => v.isSeparable_residueField_of_perfectField_of_finiteResidue

end PerPlaceSupply
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

section IsSeparableEngines

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerSpanTop_of_kaehlerFinite_of_isSeparable
    [∀ v : Place K F, Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)]
    (hfin : ValSubringKaehlerFinite K F) :
    ValSubringKaehlerSpanTop K F :=
  valSubringKaehlerSpanTop_of_polynomialFormallyUnramified
    (valSubringPolynomialFormallyUnramified_of_kaehlerFinite_of_isSeparable hfin)

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_isSeparable
    [∀ v : Place K F, Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring)]
    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerSpanTop
    (valSubringKaehlerSpanTop_of_kaehlerFinite_of_isSeparable hfin) v

end IsSeparableEngines
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

section PerfectFieldEngines

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]
    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :
    v.DCoordGenerates :=
  haveI : ∀ v : Place K F,
      Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) :=
    isSeparable_residueField_forall_of_perfectField
  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_isSeparable hfin v

end PerfectFieldEngines
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

section S12ChainWires

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.dCoordGenerates_of_valSubringFiniteTypeModel_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]
    (hmodel : ValSubringFiniteTypeModel K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField
    (valSubringKaehlerFinite_of_finiteTypeModel hmodel) v

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.dCoordGenerates_of_valSubringDedekindModel_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]
    (hmodel : ValSubringDedekindModel K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringFiniteTypeModel_of_perfectField
    (valSubringFiniteTypeModel_of_dedekindModel hmodel) v

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.dCoordGenerates_of_hasSeparatingTranscendental_of_perfectField
    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]
    (hsep : HasSeparatingTranscendental K F) (v : Place K F) :
    v.DCoordGenerates :=
  Place.dCoordGenerates_of_valSubringDedekindModel_of_perfectField
    (valSubringDedekindModel_of_hasSeparatingTranscendental hsep) v

open _root_.IntermediateField _root_.P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.IntermediateField in
theorem hasSeparatingTranscendental_of_isCurveOver_of_perfectField
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    HasSeparatingTranscendental K F := by
  obtain ⟨t, htr, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  exact ⟨t, htr, hfd, hsep,
    IntermediateField.finiteDimensional_adjoin_inv_s12 t,
    IntermediateField.isSeparable_adjoin_inv_s12 t⟩

end S12ChainWires
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue Place.FiniteResidue.finite IsCurveOver.exists_separating_transcendental"
p2m_open "AlgebraicCurve"

section S12WellDefined

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField_s12
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ValSubringKaehlerSpanTop K F :=
  haveI : ∀ v : Place K F,
      Algebra.IsSeparable K (IsLocalRing.ResidueField v.toValuationSubring) :=
    isSeparable_residueField_forall_of_perfectField
  valSubringKaehlerSpanTop_of_kaehlerFinite_of_isSeparable
    (valSubringKaehlerFinite_of_finiteTypeModel
      (valSubringFiniteTypeModel_of_dedekindModel
        (valSubringDedekindModel_of_hasSeparatingTranscendental
          (hasSeparatingTranscendental_of_isCurveOver_of_perfectField (K := K) (F := F)))))

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField FiniteResidue ord ord_zero ord_mul ord_inv ord_coe_unit ord_coe_irreducible ord_unit_smul_zpow exists_unit_mul_zpow ne_top' FiniteResidue.finite algebraMap_mem' toValuationSubring dCoord DCoordGenerates dCoord_ne_zero mem_maximalIdeal_iff_ord_pos"
p2m_open "AlgebraicCurve.Place"

variable (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_s12 {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem_s12"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_s12 {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg_s12"
private theorem _root_.AlgebraicCurve.Place.ord_uniformizerSubring'_s12 : v.ord (uniformizerSubring' v : F) = 1 :=
  v.ord_coe_irreducible (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

p2m_export "AlgebraicCurve.Place" "ord_uniformizerSubring'_s12"
private theorem _root_.AlgebraicCurve.Place.dCoord_eq_D_uniformizerSubring'_s12 :
    v.dCoord = KaehlerDifferential.D K F (uniformizerSubring' v : F) := rfl

p2m_export "AlgebraicCurve.Place" "dCoord_eq_D_uniformizerSubring'_s12"

private theorem _root_.AlgebraicCurve.Place.exists_mem_D_eq_smul_dCoord_s12 (hspan : ValSubringKaehlerSpanTop K F)
    {x : F} (hx : x ∈ v.toValuationSubring) :
    ∃ c : F, c ∈ v.toValuationSubring ∧ KaehlerDifferential.D K F x = c • v.dCoord := by
  have hmem : KaehlerDifferential.D K v.toValuationSubring (⟨x, hx⟩ : v.toValuationSubring)
      ∈ Submodule.span v.toValuationSubring
          {KaehlerDifferential.D K v.toValuationSubring (uniformizerSubring' v)} := by
    rw [hspan v]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨(c : F), c.2, ?_⟩
  have h := congrArg (KaehlerDifferential.map K K v.toValuationSubring F) hc
  rw [LinearMap.map_smul_of_tower, v.kaehlerMap_subring_D_uniformizer, KaehlerDifferential.map_D] at h
  calc KaehlerDifferential.D K F x
      = KaehlerDifferential.D K F (algebraMap v.toValuationSubring F ⟨x, hx⟩) := rfl
    _ = c • v.dCoord := h.symm
    _ = (c : F) • v.dCoord := (algebraMap_smul F c v.dCoord).symm

p2m_export "AlgebraicCurve.Place" "exists_mem_D_eq_smul_dCoord_s12"

private theorem _root_.AlgebraicCurve.Place.exists_unit_D_eq_smul_dCoord_s12 (hspan : ValSubringKaehlerSpanTop K F)
    [Nontrivial Ω[F⁄K]] [v.DCoordGenerates] {ϖ : F} (hϖ : v.ord ϖ = 1) :
    ∃ w : F, w ≠ 0 ∧ v.ord w = 0 ∧ KaehlerDifferential.D K F ϖ = w • v.dCoord := by
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, v.ord_zero] at hϖ; exact zero_ne_one hϖ
  have hϖmem : ϖ ∈ v.toValuationSubring := v.mem_of_ord_nonneg_s12 hϖ0 (by rw [hϖ]; exact zero_le_one)
  obtain ⟨c, hc, hDϖ⟩ := v.exists_mem_D_eq_smul_dCoord_s12 hspan hϖmem
  set π₀ : F := (uniformizerSubring' v : F) with hπ₀
  have hπ₀ord : v.ord π₀ = 1 := v.ord_uniformizerSubring'_s12
  have hπ₀0 : π₀ ≠ 0 := fun h => by rw [h, v.ord_zero] at hπ₀ord; exact zero_ne_one hπ₀ord
  set a : F := π₀ / ϖ with ha
  have ha0 : a ≠ 0 := div_ne_zero hπ₀0 hϖ0
  have haord : v.ord a = 0 := by
    rw [ha, div_eq_mul_inv, v.ord_mul hπ₀0 (inv_ne_zero hϖ0), v.ord_inv, hπ₀ord, hϖ]; ring
  have hamem : a ∈ v.toValuationSubring := v.mem_of_ord_nonneg_s12 ha0 haord.ge
  obtain ⟨d, hd, hDa⟩ := v.exists_mem_D_eq_smul_dCoord_s12 hspan hamem
  have hπ₀eq : π₀ = a * ϖ := by rw [ha, div_mul_cancel₀ _ hϖ0]
  have hD : v.dCoord = (a * c + ϖ * d) • v.dCoord := by
    conv_lhs => rw [v.dCoord_eq_D_uniformizerSubring'_s12, ← hπ₀, hπ₀eq, Derivation.leibniz, hDϖ, hDa]
    rw [smul_smul, smul_smul, ← add_smul, mul_comm ϖ d]
  have hone : a * c + ϖ * d = 1 := by
    have h1 : (1 - (a * c + ϖ * d)) • v.dCoord = 0 := by rw [sub_smul, one_smul, ← hD, sub_self]
    rcases smul_eq_zero.mp h1 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h v.dCoord_ne_zero

  have hacmem : a * c ∈ v.toValuationSubring := mul_mem hamem hc
  have hunit : IsUnit (⟨a * c, hacmem⟩ : v.toValuationSubring) := by
    by_contra hnu
    have hmax : (⟨a * c, hacmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hϖmax : (⟨ϖ, hϖmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (v.mem_maximalIdeal_iff_ord_pos hϖ0 hϖmem).mpr (by rw [hϖ]; exact one_pos)
    have h1 : (1 : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
      have : (1 : v.toValuationSubring)
          = ⟨a * c, hacmem⟩ + ⟨ϖ, hϖmem⟩ * ⟨d, hd⟩ := Subtype.ext (by
            show (1 : F) = a * c + ϖ * d
            exact hone.symm)
      rw [this]
      exact add_mem hmax (Ideal.mul_mem_right _ _ hϖmax)
    exact (IsLocalRing.maximalIdeal.isMaximal v.toValuationSubring).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1)
  have hacord : v.ord (a * c) = 0 := by
    have := v.ord_coe_unit hunit.unit
    rwa [IsUnit.unit_spec] at this
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : (⟨a * c, hacmem⟩ : v.toValuationSubring) = 0 := Subtype.ext (by simp [h0])
    rw [hz] at hunit
    exact not_isUnit_zero hunit
  have hcord : v.ord c = 0 := by
    rw [v.ord_mul ha0 hc0, haord, zero_add] at hacord
    exact hacord
  exact ⟨c, hc0, hcord, hDϖ⟩

p2m_export "AlgebraicCurve.Place" "exists_unit_D_eq_smul_dCoord_s12"

private theorem _root_.AlgebraicCurve.Place.exists_ord_eq_zero_D_eq_smul_D_s12 (hspan : ValSubringKaehlerSpanTop K F)
    [Nontrivial Ω[F⁄K]] [v.DCoordGenerates]
    (π π' : F) (hπ : v.ord π = 1) (hπ' : v.ord π' = 1) :
    ∃ u : F, v.ord u = 0 ∧ KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π := by
  obtain ⟨w, hw0, hw, hDπ⟩ := v.exists_unit_D_eq_smul_dCoord_s12 hspan hπ
  obtain ⟨w', hw0', hw', hDπ'⟩ := v.exists_unit_D_eq_smul_dCoord_s12 hspan hπ'
  refine ⟨w' / w, ?_, ?_⟩
  · rw [div_eq_mul_inv, v.ord_mul hw0' (inv_ne_zero hw0), v.ord_inv, hw', hw]; ring
  · rw [hDπ', hDπ, smul_smul, div_mul_cancel₀ _ hw0]

p2m_export "AlgebraicCurve.Place" "exists_ord_eq_zero_D_eq_smul_D_s12"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

theorem exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver_s12
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (v : Place K F) (π π' : F) (hπ : v.ord π = 1) (hπ' : v.ord π' = 1) :
    ∃ u : F, v.ord u = 0 ∧ KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π := by
  have hspan := valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField_s12 (K := K) (F := F)
  haveI : v.DCoordGenerates := Place.dCoordGenerates_of_valSubringKaehlerSpanTop hspan v
  exact v.exists_ord_eq_zero_D_eq_smul_D_s12 hspan π π' hπ hπ'

theorem exists_mem_D_eq_smul_D_of_isCurveOver_s12
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (v : Place K F) {π : F} (hπ : v.ord π = 1) {x : F} (hx : x ∈ v.toValuationSubring) :
    ∃ c : F, c ∈ v.toValuationSubring ∧ KaehlerDifferential.D K F x = c • KaehlerDifferential.D K F π := by
  have hspan := valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField_s12 (K := K) (F := F)
  haveI : v.DCoordGenerates := Place.dCoordGenerates_of_valSubringKaehlerSpanTop hspan v
  obtain ⟨c, hc, hDx⟩ := v.exists_mem_D_eq_smul_dCoord_s12 hspan hx
  obtain ⟨w, hw0, hw, hDπ⟩ := v.exists_unit_D_eq_smul_dCoord_s12 hspan hπ
  refine ⟨c / w, ?_, ?_⟩
  · rcases eq_or_ne c 0 with rfl | hc0
    · rw [zero_div]; exact zero_mem _
    · exact v.mem_of_ord_nonneg_s12 (div_ne_zero hc0 hw0) (by
        rw [div_eq_mul_inv, v.ord_mul hc0 (inv_ne_zero hw0), v.ord_inv, hw, neg_zero, add_zero]
        exact v.ord_nonneg_of_mem_s12 hc)
  · rw [hDx, hDπ, smul_smul, div_mul_cancel₀ _ hw0]

end S12WellDefined
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver.AlgebraicCurve"

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) (π π' : F) (hπ : v.ord π = 1) (hπ' : v.ord π' = 1) :
    ∃ u : F, v.ord u = 0 ∧ KaehlerDifferential.D K F π' = u • KaehlerDifferential.D K F π := by
  exact AlgebraicCurve.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver_s12 v π π' hπ hπ'

end
end S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
end P2MW
export P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver (solution)
