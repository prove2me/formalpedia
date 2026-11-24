-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_DetChrOf
-- name    : Formalism_LocalToGlobal_Columns_DetChrOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:47.117854+00:00
-- url     : https://prove2.me/theorems/01feb51a-14db-40bd-8f9f-c9ca6a551fe2
-- title:
--   Det Chr Of
-- statement:
--   Definitions and structural lemmas for Det Chr Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/DetChrOf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
namespace Formalism.L2.Col
namespace DetChrOf
section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
instance liesOver (P : HeightOneSpectrum (𝓞 E)) : P.asIdeal.LiesOver (P.under (𝓞 F)).asIdeal := ⟨rfl⟩
theorem ucont (P : HeightOneSpectrum (𝓞 E)) :
    UniformContinuous (algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E))) :=
  HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E (P.under (𝓞 F)) P
def compMap (P : HeightOneSpectrum (𝓞 E)) : (P.under (𝓞 F)).adicCompletion F →+* P.adicCompletion E :=
  (HeightOneSpectrum.adicCompletion.equiv E P).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom (algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E)))
      (ucont P).continuous).comp (HeightOneSpectrum.adicCompletion.equiv F (P.under (𝓞 F))).toRingHom)
theorem compMap_coe (P : HeightOneSpectrum (𝓞 E)) (x : F) :
    compMap P (x : (P.under (𝓞 F)).adicCompletion F) = ((algebraMap F E x : E) : P.adicCompletion E) := by
  apply HeightOneSpectrum.adicCompletion.ext
  have e : (compMap P (x : (P.under (𝓞 F)).adicCompletion F)).toCompletion =
      UniformSpace.Completion.mapRingHom (algebraMap (WithVal ((P.under (𝓞 F)).valuation F)) (WithVal (P.valuation E)))
        (ucont P).continuous ((x : F) : ((P.under (𝓞 F)).valuation F).Completion) := rfl
  rw [e, UniformSpace.Completion.mapRingHom_coe]
  rw [HeightOneSpectrum.adicCompletion.coe_toCompletion]
  congr 1
theorem continuous_compMap (P : HeightOneSpectrum (𝓞 E)) : Continuous (compMap (F := F) P) := by
  have h1 : Continuous (HeightOneSpectrum.adicCompletion.equiv F (P.under (𝓞 F))) :=
    (HeightOneSpectrum.adicCompletion.isUniformInducing_toCompletion F (P.under (𝓞 F))).uniformContinuous.continuous
  have h2 : Continuous (HeightOneSpectrum.adicCompletion.equiv E P).symm := by
    rw [(HeightOneSpectrum.adicCompletion.isUniformInducing_toCompletion E P).isInducing.continuous_iff]
    exact continuous_id
  exact h2.comp ((UniformSpace.Completion.continuous_map).comp h1)
theorem isOpen_integersAt {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  exact Valued.isOpen_integer _
theorem isClosed_integersAt {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  (v.adicCompletionIntegers K).toAddSubgroup.isClosed_of_isOpen (isOpen_integersAt v)
theorem valued_compMap_coe (P : HeightOneSpectrum (𝓞 E)) (x : F) :
    Valued.v (compMap P (x : (P.under (𝓞 F)).adicCompletion F)) =
      Valued.v (x : (P.under (𝓞 F)).adicCompletion F) ^ (P.under (𝓞 F)).asIdeal.ramificationIdx' P.asIdeal := by
  rw [compMap_coe, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_liesOver E (P.under (𝓞 F)) P x]
theorem compMap_mem (P : HeightOneSpectrum (𝓞 E)) {x : (P.under (𝓞 F)).adicCompletion F}
    (hx : x ∈ (P.under (𝓞 F)).adicCompletionIntegers F) : compMap P x ∈ P.adicCompletionIntegers E := by
  have hclosed : IsClosed {y : (P.under (𝓞 F)).adicCompletion F | compMap P y ∈ P.adicCompletionIntegers E} :=
    (isClosed_integersAt P).preimage (continuous_compMap P)
  have hdense := HeightOneSpectrum.denseRange_algebraMap (K := F) (P.under (𝓞 F))
  have hsub := hdense.open_subset_closure_inter (isOpen_integersAt (P.under (𝓞 F)))
  have hin : ((P.under (𝓞 F)).adicCompletionIntegers F : Set _) ∩ Set.range (algebraMap F ((P.under (𝓞 F)).adicCompletion F)) ⊆
      {y | compMap P y ∈ P.adicCompletionIntegers E} := by
    rintro y ⟨hyO, a, rfl⟩
    have e : algebraMap F ((P.under (𝓞 F)).adicCompletion F) a = (a : (P.under (𝓞 F)).adicCompletion F) := by
      rw [HeightOneSpectrum.algebraMap_adicCompletion]; rfl
    rw [e] at hyO ⊢
    show compMap P (a : (P.under (𝓞 F)).adicCompletion F) ∈ P.adicCompletionIntegers E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_compMap_coe]
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hyO
    exact pow_le_one₀ zero_le' hyO
  exact (closure_minimal hin hclosed) (hsub hx)
def finAdeleMap : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun P : HeightOneSpectrum (𝓞 E) => P.adicCompletion E) (fun P => P.under (𝓞 F))
    (Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => (Formalism.L2.Host.finite_aboveF (L := E) F v).to_subtype)
    (fun P => compMap P) (Filter.Eventually.of_forall fun P x hx => compMap_mem P hx)
end Loc
section Tens
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
abbrev algFAE : Algebra F (FiniteAdeleRing (𝓞 E) E) :=
  ((algebraMap E (FiniteAdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
attribute [local instance] algFAE
def diagEF : E →ₐ[F] FiniteAdeleRing (𝓞 E) E :=
  { algebraMap E (FiniteAdeleRing (𝓞 E) E) with commutes' := fun _ => rfl }
def finAdeleAlg : FiniteAdeleRing (𝓞 F) F →ₐ[F] FiniteAdeleRing (𝓞 E) E :=
  { finAdeleMap (F := F) (E := E) with
    commutes' := fun r => by
      apply RestrictedProduct.ext
      intro P
      show compMap P (r : (P.under (𝓞 F)).adicCompletion F) = ((algebraMap F E r : E) : P.adicCompletion E)
      exact compMap_coe P r }
def tensAdeleMap : Formalism.L2.DIV.AfE F E →+* FiniteAdeleRing (𝓞 E) E :=
  (Algebra.TensorProduct.lift (diagEF F E) (finAdeleAlg F E) fun _ _ => Commute.all _ _).toRingHom
def finToAdele : FiniteAdeleRing (𝓞 E) E →* AdeleRing (𝓞 E) E where
  toFun y := ((1 : InfiniteAdeleRing E), y)
  map_one' := rfl
  map_mul' _ _ := Prod.ext (mul_one 1).symm rfl
def toIdeles : (Formalism.L2.DIV.AfE F E)ˣ →* Ideles E :=
  (Units.map (finToAdele E)).comp (Units.map (tensAdeleMap F E).toMonoidHom)
end Tens
section Chr
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def infPart : AdeleRing (𝓞 E) E →* InfiniteAdeleRing E where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl
def finPart : AdeleRing (𝓞 E) E →* FiniteAdeleRing (𝓞 E) E where
  toFun a := a.2
  map_one' := rfl
  map_mul' _ _ := rfl
def chrOf {K : Type} [Field K] (σ₀ : K →+* ℂ) (χ : Formalism.L2.Host.HChar E)
    (hval : ∀ x, ∃ y : K, σ₀ y = ((χ.1 (toIdeles F E x) : ℂˣ) : ℂ)) : Formalism.L2.DIV.Chr F E K where
  toFun x := Units.mk0 (hval x).choose (fun h => by
    have := (hval x).choose_spec
    rw [h, map_zero] at this
    exact (Units.ne_zero _) this.symm)
  map_one' := by
    apply Units.ext
    apply σ₀.injective
    have h : σ₀ (hval 1).choose = 1 := (hval 1).choose_spec.trans (by rw [map_one, map_one, Units.val_one])
    rw [Units.val_mk0, h, Units.val_one, map_one]
  map_mul' x y := by
    apply Units.ext
    apply σ₀.injective
    have h1 := (hval (x * y)).choose_spec
    have h2 := (hval x).choose_spec
    have h3 := (hval y).choose_spec
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, h1, map_mul σ₀, h2, h3, map_mul (toIdeles F E),
      map_mul χ.1, Units.val_mul]
end Chr
end DetChrOf
end Formalism.L2.Col


