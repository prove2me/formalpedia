-- Prove2me | Definitions.Def_AlpoGeB004
-- name    : AlpoGeB004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T16:26:22.310821+00:00
-- url     : https://prove2.me/theorems/58fa489c-7ef9-4646-b574-47c94a853ad3
-- title:
--   Definitions bundle AlpoGeB004 of the alpo.ge GRH release, first cut (Row0b, IsRecT)
-- statement:
--   A definitions bundle of the first cut of L. Alpöge's Lean proof of GRH for Dirichlet $L$-functions (released 20 November 2026, written with Claude; announcement [alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)). The declarations and their proofs are the release's, carved mechanically for this platform: the carve reorders them, restates the namespaces and `open`s each needs, and writes a few declarations from their elaborated form. Two patches are recorded in the carve: an anonymous instance is given its original generated name, and an additive structure that a `to_additive` attribute names is restored beside the structure that names it. The release builds with `maxHeartbeats 4000000` and `maxSynthPendingDepth 3` as project options (and `synthInstance.maxHeartbeats 400000` for its local and global field libraries); since the verifier sets none of these, each carved module section states them as `set_option` lines. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   The first cut publishes the two inputs from which the release concludes its main theorem: `AlpoGe.galoisLocalGlobalStrong_recParameter` (the release's `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) and `AlpoGe.everyCharacter_of_row` (the release's `UpperTheory.FinalTheorems.everyCharacter_of_row`). These bundles hold the definitions their statements need, with the theorems those definitions use.
--
--   **Contents.** It holds 290 declarations of the release's Lean: 119 definitions, 5 inductive types or structures, 28 instances and 138 theorems. The definitions and types are `Formalism.BasicNotions.LocTied`, `Formalism.L2.GlobalTheoryTheory.HLatOps.withL`, `Formalism.Per.Acris`, `Formalism.Per.Acris0`, `Formalism.Per.AinfP`, `Formalism.Per.Bcris`, `Formalism.Per.BdR`, `Formalism.Per.BdRp`, `Formalism.Per.FilD`, `Formalism.Per.Fl`, `Formalism.Per.IsCrisDR`, `Formalism.Per.IsLog`, `Formalism.Per.a0B`, `Formalism.Per.aB`, `Formalism.Per.ev`, `Formalism.Per.kerP`, `Formalism.Per.pD`, `Formalism.Per.tm`, `Formalism.Per.zB`, `Formalism.Per.zD`, `Formalism.Per.θD`, `Formalism.Per.σB`, `Formalism.Per.σD`, `Formalism.Per.σO`, `Formalism.Per.φB`, `GlobalTheory.ContraPair.DualIsConjBy`, `GlobalTheory.ContraPair.PolarizedPair`, `GlobalTheory.CrisMaps.frob`, `GlobalTheory.CrisMaps.gal`, `GlobalTheory.CuspRep.CG`, `GlobalTheory.CuspRep.CG.HasInfChar`, `GlobalTheory.CuspRep.CG.IsRegAlg`, `GlobalTheory.CuspRep.CG.infChar`, `GlobalTheory.CuspRep.CG.mk`, `GlobalTheory.CuspRep.CuspSub.HasInfChar`, `GlobalTheory.CuspRep.CuspSub.IsLocComp`, `GlobalTheory.CuspRep.CuspSub.Iso`, `GlobalTheory.CuspRep.CuspSub.finPart`, `GlobalTheory.CuspRep.CuspSub.locRep`, `GlobalTheory.CuspRep.CuspSub.twist`, `GlobalTheory.CuspRep.locGL`, `GlobalTheory.CuspRep.opAdd`, `GlobalTheory.CuspRep.opMul`, `GlobalTheory.CuspRep.sLoc`, `GlobalTheory.GLq.IsCusp`, `GlobalTheory.GLq.br`, `GlobalTheory.GLq.res`, `GlobalTheory.GLq.tl`, `GlobalTheory.GalOfCusp.adeleNorm`, `GlobalTheory.GalOfCusp.algNorm`, `GlobalTheory.GalOfCusp.compNorm`, `GlobalTheory.GalOfCusp.ideleNorm`, `GlobalTheory.HeckeGal.Gab`, `GlobalTheory.HeckeGal.IsGlobalArtin`, `GlobalTheory.HeckeGal.infConn`, `GlobalTheory.HeckeGal.toAb`, `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap`, `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj`, `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap`, `GlobalTheory.LocGL.HasSupport`, and 64 more. It imports the bundles `Def_AlpoGeB000`, `Def_AlpoGeB001`, `Def_AlpoGeB002`.
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc)

import Mathlib
import Definitions.Def_AlpoGeB000
import Definitions.Def_AlpoGeB001
import Definitions.Def_AlpoGeB002

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.BasicNotions.Loc.maxUnramifiedAlgebra _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

section CM

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension.isCMField [h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] : IsCMField E := by
  haveI := h.totallyReal
  haveI := h.totallyComplex
  haveI := h.quadratic
  exact IsCMField.ofCMExtension F E

instance isCMExtension_maximalRealSubfield (E : Type) [Field E] [NumberField E] [IsCMField E] :
    IsCMExtension (maximalRealSubfield E) E where
  totallyReal := inferInstance
  totallyComplex := inferInstance
  quadratic := inferInstance

def conj [h : IsCMExtension F E] : E ≃ₐ[F] E :=
  haveI := h.totallyReal
  haveI := h.totallyComplex
  haveI := h.quadratic
  haveI := IsCMExtension.isCMField F E
  { (IsCMField.complexConj E).toRingEquiv with
    commutes' := fun x => by
      have := IsCMField.complexConj_apply_eq_self E (CMExtension.equivMaximalRealSubfield F E x)
      rw [CMExtension.equivMaximalRealSubfield_apply] at this
      exact this }

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension F E] (φ : E →+* ℂ) (x : E) :
    φ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F E x) = starRingEnd ℂ (φ (x)) := by
  haveI := _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.IsCMExtension.isCMField F E
  exact (IsCMField.isConj_complexConj E φ).eq x

end CM

section Extension

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo (w : HeightOneSpectrum (𝓞 L)) :
    Set.MapsTo (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w)
      ((w.under (𝓞 K)).adicCompletionIntegers K : Set _) (w.adicCompletionIntegers L : Set _) := by
  intro x hx
  have hS : IsClosed ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w) ⁻¹'
      (w.adicCompletionIntegers L : Set (w.adicCompletion L))) :=
    (Valued.isClopen_integer (w.adicCompletion L)).isClosed.preimage
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap K L w)
  have hopen : IsOpen (((w.under (𝓞 K)).adicCompletionIntegers K :
      Set ((w.under (𝓞 K)).adicCompletion K))) :=
    (Valued.isClopen_integer ((w.under (𝓞 K)).adicCompletion K)).isOpen
  have hd := Dense.open_subset_closure_inter (denseRange_algebraMap K (w.under (𝓞 K))) hopen hx
  refine closure_minimal ?_ hS hd
  rintro _ ⟨hy, k, rfl⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers] at hy ⊢
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
  have h1 : Valued.v (algebraMap K ((w.under (𝓞 K)).adicCompletion K) k) =
      (w.under (𝓞 K)).valuation K k := valuedAdicCompletion_eq_valuation' _ k
  have h2 : Valued.v (algebraMap L (w.adicCompletion L) (algebraMap K L k)) =
      w.valuation L (algebraMap K L k) := valuedAdicCompletion_eq_valuation' _ _
  rw [h1] at hy
  rw [h2, ← valuation_liesOver L (w.under (𝓞 K)) w]
  exact pow_le_one' hy _

def finiteAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (fun w => w.under (𝓞 K)) (tendsto_under K L) (finiteCompletionMap K L)
    (Eventually.of_forall (finiteCompletionMap_mapsTo K L))

def adeleMap : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (infiniteAdeleMap K L) (finiteAdeleMap K L)

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap (x : K) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L (algebraMap K _ x) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x) := by
  refine Prod.ext ?_ ?_
  · funext w
    exact LiesOver.completionMap_coe _
  · ext w : 1
    exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe K L w x

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter in
open scoped RestrictedProduct in
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap : Continuous (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L) :=
  (continuous_pi fun w => LiesOver.continuous_completionMap.comp (continuous_apply _)).prodMap
    (RestrictedProduct.mapAlong_continuous _ _ _
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K L) _
      (Eventually.of_forall (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo K L))
      fun w => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap K L w)

end Extension

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.SpanNatCastLeComap
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.Reformulated.AutPerF.Acris.eval_algebraMap _root_.Reformulated.AutPerF.Acris.extend_algebraMap _root_.Reformulated.AutPerF.Acris.frob_algebraMap _root_.Reformulated.AutPerF.Acris.frob_algebraMap_zero _root_.Reformulated.AutPerF.Acris.frob_logTeich _root_.Reformulated.AutPerF.Acris.logTeich_one _root_.Reformulated.AutPerF.Acris.log_one _root_.Reformulated.AutPerF.Acris.map_algebraMap _root_.Reformulated.AutPerF.Acris.map_algebraMap_zero _root_.Reformulated.AutPerF.Acris.map_logTeich _root_.Reformulated.AutPerF.AcrisZero.coe_frob _root_.Reformulated.AutPerF.AcrisZero.coe_gamma _root_.Reformulated.AutPerF.AcrisZero.coe_map _root_.Reformulated.AutPerF.AcrisZero.frob_algebraMap _root_.Reformulated.AutPerF.AcrisZero.map_algebraMap _root_.Reformulated.AutPerF.AcrisZero.map_id _root_.Reformulated.AutPerF.Ainf.theta_xi _root_.Reformulated.AutPerF.Bcris.lift_algebraMap _root_.Reformulated.AutPerF.Bcris.logTeich_one _root_.Reformulated.AutPerF.Bcris.map_logTeich _root_.Reformulated.AutPerF.BdRPlus.eval_algebraMap _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf _root_.Reformulated.AutPerF.BdRPlus.theta_algebraMap _root_.Reformulated.AutPerF.BdRPlus.theta_algebraMap_ainf _root_.Reformulated.AutPerF.PFlat.coe_map _root_.Reformulated.AutPerF.Tilt.untilt_zero _root_.Reformulated.AutPerF.tateModule.coe_map _root_.Reformulated.AutPerF.tateModule.map_id
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

section Adic

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]

theorem adicMap_eq_id (I : Ideal A) (f : A →+* A) (h : I ≤ I.comap f) (hf : ∀ a, f a = a)
    (x : AdicCompletion I A) : adicMap I I f h x = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_adicMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← ha, Ideal.quotientMap_mk, hf]

theorem adicMap_adicMap (I : Ideal A) (J : Ideal B) (K : Ideal C) (f : A →+* B) (g : B →+* C)
    (e : A →+* C) (h : I ≤ J.comap f) (h' : J ≤ K.comap g) (h'' : I ≤ K.comap e)
    (he : ∀ a, g (f a) = e a) (x : AdicCompletion I A) :
    adicMap J K g h' (adicMap I J f h x) = adicMap I K e h'' x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_adicMap, evalₐ_adicMap, evalₐ_adicMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← ha, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, he]

end Adic

variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)]
variable (S : Type v) [CommRing S] [Fact ¬IsUnit (p : S)]
variable (U : Type w) [CommRing U] [Fact ¬IsUnit (p : U)]

variable {R S U}

namespace Tilt

variable {p}

theorem map_map (f : R →+* S) (g : S →+* U) (x : Tilt p R) :
    map p g (map p f x) = map p (g.comp f) x := by
  refine ext fun n => ?_
  rw [coeff_map, coeff_map, coeff_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  rw [← ha]; rfl

end Tilt

namespace Ainf

variable {p}

theorem map_map (f : R →+* S) (g : S →+* U) (x : Ainf p R) :
    map p g (map p f x) = map p (g.comp f) x := by
  ext n; simp [map, Tilt.map_map]

end Ainf

namespace AinfInv

variable {p}

theorem map_map (f : R →+* S) (g : S →+* U) (x : AinfInv p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  RingHom.congr_fun (hom_ext (f := (map p g).comp (map p f)) (g := map p (g.comp f))
    (by simp [Ainf.map_map])) x

end AinfInv

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

section Adic

variable {A : Type u} [CommRing A]

def adicLog [Algebra ℚ A] (I : Ideal A) (u : AdicCompletion I A)
    (hu : AdicCompletion.evalOneₐ I u = 1) : AdicCompletion I A :=
  adicMk I (fun n => truncLog n (AdicCompletion.evalₐ I n (u - 1))) (fun m n hle => by
    rw [map_truncLog, factorPow_evalₐ]
    exact truncLog_eq_of_pow_eq_zero (evalₐ_pow_eq_zero I (by simp [hu]) m) hle)

end Adic

variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace BdRPlus

def fil (n : ℕ) : Ideal (BdRPlus p R) := RingHom.ker (theta p R) ^ n

variable {p R}

theorem ext_eval {x y : BdRPlus p R} (h : ∀ n, eval p R n x = eval p R n y) : x = y :=
  AdicCompletion.ext_evalₐ h

theorem theta_eq_zero_iff (x : BdRPlus p R) :
    theta p R x = 0 ↔ AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) x = 0 :=
  map_eq_zero_iff _ (RingHom.kerLift_injective _)

theorem theta_eq_one_iff (x : BdRPlus p R) :
    theta p R x = 1 ↔ AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) x = 1 :=
  map_eq_one_iff _ (RingHom.kerLift_injective _)

def log (u : BdRPlus p R) (hu : theta p R u = 1) : BdRPlus p R :=
  adicLog (AinfInv.kerTheta p R) u ((theta_eq_one_iff u).1 hu)

end BdRPlus

def BdR : Type u := FractionRing (BdRPlus p R)

namespace BdR

instance instCommRing : CommRing (BdR p R) := inferInstanceAs (CommRing (FractionRing (BdRPlus p R)))
instance instAlgebraBdRPlus : Algebra (BdRPlus p R) (BdR p R) :=
  inferInstanceAs (Algebra (BdRPlus p R) (FractionRing (BdRPlus p R)))
instance instIsFractionRingBdRPlus : IsFractionRing (BdRPlus p R) (BdR p R) :=
  inferInstanceAs (IsFractionRing (BdRPlus p R) (FractionRing (BdRPlus p R)))

def filNat (n : ℕ) : Submodule (BdRPlus p R) (BdR p R) :=
  Submodule.map (Algebra.linearMap (BdRPlus p R) (BdR p R)) (BdRPlus.fil p R n)

def fil (i : ℤ) : Submodule (BdRPlus p R) (BdR p R) :=
  filNat p R i.toNat / filNat p R (-i).toNat

end BdR

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamMap
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.Reformulated.AutPerF.Acris.extend_algebraMap _root_.Reformulated.AutPerF.Acris.frob_algebraMap _root_.Reformulated.AutPerF.Acris.frob_algebraMap_zero _root_.Reformulated.AutPerF.Acris.frob_logTeich _root_.Reformulated.AutPerF.Acris.logTeich_one _root_.Reformulated.AutPerF.Acris.log_one _root_.Reformulated.AutPerF.Acris.map_algebraMap _root_.Reformulated.AutPerF.Acris.map_algebraMap_zero _root_.Reformulated.AutPerF.Acris.map_logTeich _root_.Reformulated.AutPerF.AcrisZero.coe_frob _root_.Reformulated.AutPerF.AcrisZero.coe_gamma _root_.Reformulated.AutPerF.AcrisZero.coe_map _root_.Reformulated.AutPerF.AcrisZero.frob_algebraMap _root_.Reformulated.AutPerF.AcrisZero.map_algebraMap _root_.Reformulated.AutPerF.AcrisZero.map_id _root_.Reformulated.AutPerF.Ainf.theta_xi _root_.Reformulated.AutPerF.Bcris.lift_algebraMap _root_.Reformulated.AutPerF.Bcris.logTeich_one _root_.Reformulated.AutPerF.Bcris.map_logTeich _root_.Reformulated.AutPerF.BdRPlus.theta_algebraMap_ainf _root_.Reformulated.AutPerF.PFlat.coe_map _root_.Reformulated.AutPerF.Tilt.untilt_zero _root_.Reformulated.AutPerF.tateModule.coe_map _root_.Reformulated.AutPerF.tateModule.map_id
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]

namespace BdRPlus

variable {p}

@[simp] theorem map_id (x : BdRPlus p R) : map p (RingHom.id R) x = x :=
  adicMap_eq_id _ _ _ AinfInv.map_id x

theorem map_map (f : R →+* S) (g : S →+* U) (x : BdRPlus p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  adicMap_adicMap _ _ _ _ _ _ _ _ _ (AinfInv.map_map f g) x

variable (p) in

def mapEquiv (e : R ≃+* S) : BdRPlus p R ≃+* BdRPlus p S :=
  RingEquiv.ofRingHom (map p e.toRingHom) (map p e.symm.toRingHom)
    (by ext x; simp [map_map]) (by ext x; simp [map_map])

@[simp] theorem mapEquiv_apply (e : R ≃+* S) (x : BdRPlus p R) :
    mapEquiv p e x = map p (e : R →+* S) x := rfl

end BdRPlus

namespace BdR

def map (e : R ≃+* S) : BdR p R ≃+* BdR p S :=
  IsFractionRing.ringEquivOfRingEquiv (BdRPlus.mapEquiv p e)

variable {p}

theorem hom_ext {B : Type*} [CommRing B] {f g : BdR p R →+* B}
    (h : ∀ x : BdRPlus p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors (BdRPlus p R)) (RingHom.ext h)

@[simp] theorem map_algebraMap (e : R ≃+* S) (x : BdRPlus p R) :
    map p e (algebraMap _ _ x) = algebraMap _ _ (BdRPlus.map p (e : R →+* S) x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

@[simp] theorem map_refl (x : BdR p R) : map p (RingEquiv.refl R) x = x :=
  RingHom.congr_fun (hom_ext (f := (map p (RingEquiv.refl R) : _ →+* _)) (g := RingHom.id _)
    (by simp)) x

theorem map_map (e : R ≃+* S) (e' : S ≃+* U) (x : BdR p R) :
    map p e' (map p e x) = map p (e.trans e') x :=
  RingHom.congr_fun (hom_ext (f := (map p e').toRingHom.comp (map p e).toRingHom)
    (g := (map p (e.trans e')).toRingHom) (by simp [BdRPlus.map_map])) x

end BdR

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.Reformulated.AutPerF.Ainf.theta_xi _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf _root_.Reformulated.AutPerF.BdRPlus.theta_algebraMap_ainf _root_.Reformulated.AutPerF.Tilt.untilt_zero
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]

variable {p}

namespace Bcris

@[simp] theorem frob_logTeich (η : tateModule p R) : frob p R (logTeich η) = p * logTeich η := by
  simp [logTeich]

end Bcris

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

variable [Fact ¬IsUnit (p : R)]

variable [IsAdicComplete (span {(p : R)}) R]

instance BdR.mulSemiringAction : MulSemiringAction G (BdR p R) :=
  actionOf (fun g => (BdR.map p (MulSemiringAction.toRingEquiv G R g)).toRingHom)
    (fun x => by
      have : MulSemiringAction.toRingEquiv G R 1 = RingEquiv.refl R := by ext; simp
      simp [this])
    (fun g h x => by
      have : MulSemiringAction.toRingEquiv G R (g * h) =
          (MulSemiringAction.toRingEquiv G R h).trans (MulSemiringAction.toRingEquiv G R g) := by
        ext; simp [mul_smul]
      simp [this, BdR.map_map])

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.Reformulated.AutPerF.Acris.extend_algebraMap _root_.Reformulated.AutPerF.Acris.frob_algebraMap _root_.Reformulated.AutPerF.Acris.frob_algebraMap_zero _root_.Reformulated.AutPerF.Acris.frob_logTeich _root_.Reformulated.AutPerF.Acris.logTeich_one _root_.Reformulated.AutPerF.Acris.log_one _root_.Reformulated.AutPerF.Acris.map_algebraMap _root_.Reformulated.AutPerF.Acris.map_algebraMap_zero _root_.Reformulated.AutPerF.Acris.map_logTeich _root_.Reformulated.AutPerF.AcrisZero.coe_frob _root_.Reformulated.AutPerF.AcrisZero.coe_gamma _root_.Reformulated.AutPerF.AcrisZero.coe_map _root_.Reformulated.AutPerF.AcrisZero.frob_algebraMap _root_.Reformulated.AutPerF.AcrisZero.map_algebraMap _root_.Reformulated.AutPerF.AcrisZero.map_id _root_.Reformulated.AutPerF.Bcris.frob_logTeich _root_.Reformulated.AutPerF.Bcris.lift_algebraMap _root_.Reformulated.AutPerF.Bcris.logTeich_one _root_.Reformulated.AutPerF.Bcris.map_logTeich _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf _root_.Reformulated.AutPerF.BdRPlus.theta_algebraMap_ainf _root_.Reformulated.AutPerF.PFlat.coe_map _root_.Reformulated.AutPerF.tateModule.coe_map _root_.Reformulated.AutPerF.tateModule.map_id
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace Tilt

variable (p R) in

def sharpEquiv : Tilt p R ≃* Perfection R p :=
  (Perfection.quotientMulEquiv p (span {(p : R)})).symm

theorem coeff_zero_sharpEquiv (x : Tilt p R) :
    Perfection.coeffMonoidHom R p 0 (sharpEquiv p R x) = PreTilt.untilt x :=
  Perfection.coeff_zero_symm_quotientMulEquiv x

theorem untilt_sharpEquiv_symm (y : Perfection R p) :
    PreTilt.untilt ((sharpEquiv p R).symm y) = Perfection.coeffMonoidHom R p 0 y := by
  rw [← coeff_zero_sharpEquiv, MulEquiv.apply_symm_apply]

theorem coeff_sharpEquiv_pow (x : Tilt p R) (n : ℕ) :
    Perfection.coeffMonoidHom R p n (sharpEquiv p R x) ^ p ^ n = PreTilt.untilt x := by
  rw [Perfection.coeffMonoidHom_pow_p_pow_self, coeff_zero_sharpEquiv]

variable [IsDomain R]

theorem untilt_eq_zero_iff (x : Tilt p R) : PreTilt.untilt x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ untilt_zero⟩
  apply (sharpEquiv p R).injective
  refine Perfection.extMonoid fun n => ?_
  have h1 := coeff_sharpEquiv_pow x n
  have h2 := coeff_sharpEquiv_pow (0 : Tilt p R) n
  rw [h] at h1
  rw [untilt_zero] at h2
  rw [pow_eq_zero_iff (pow_pos (Fact.out : p.Prime).pos n).ne'] at h1 h2
  rw [h1, h2]

instance isDomain : IsDomain (Tilt p R) := by
  have : Nontrivial (Tilt p R) :=
    ⟨(CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one).1⟩
  have : NoZeroDivisors (Tilt p R) := ⟨fun {a b} h => by
    rw [← untilt_eq_zero_iff, map_mul, mul_eq_zero, untilt_eq_zero_iff, untilt_eq_zero_iff] at h
    exact h⟩
  exact NoZeroDivisors.to_isDomain _

theorem dvd_iff_untilt_dvd [IsIntegrallyClosed R] (x y : Tilt p R) :
    x ∣ y ↔ PreTilt.untilt x ∣ PreTilt.untilt y := by
  refine ⟨fun h => map_dvd _ h, fun h => ?_⟩
  by_cases hx : x = 0
  · subst hx
    rw [untilt_zero, zero_dvd_iff, untilt_eq_zero_iff] at h
    rw [h]
  have hp := (Fact.out : p.Prime).pos
  have hne : ∀ n, Perfection.coeffMonoidHom R p n (sharpEquiv p R x) ≠ 0 := by
    intro n hn
    have h1 := coeff_sharpEquiv_pow x n
    rw [hn, zero_pow (pow_pos hp n).ne', eq_comm, untilt_eq_zero_iff] at h1
    exact hx h1
  have hd : ∀ n, Perfection.coeffMonoidHom R p n (sharpEquiv p R x) ∣
      Perfection.coeffMonoidHom R p n (sharpEquiv p R y) := by
    intro n
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff (pow_pos hp n).ne', coeff_sharpEquiv_pow,
      coeff_sharpEquiv_pow]
    exact h
  choose c hc using hd
  have hcp : ∀ n, c (n + 1) ^ p = c n := by
    intro n
    apply mul_left_cancel₀ (hne n)
    rw [← hc, ← Perfection.coeffMonoidHom_pow_p' (sharpEquiv p R x) n, ← mul_pow, ← hc,
      Perfection.coeffMonoidHom_pow_p']
  obtain ⟨z, hz⟩ : ∃ z : Perfection R p, ∀ n, Perfection.coeffMonoidHom R p n z = c n :=
    ⟨⟨c, hcp⟩, fun _ => rfl⟩
  refine ⟨(sharpEquiv p R).symm z, (sharpEquiv p R).injective ?_⟩
  rw [map_mul, MulEquiv.apply_symm_apply]
  refine Perfection.extMonoid fun n => ?_
  rw [map_mul, hc, hz]

variable [ValuationRing R]

theorem untilt_surjective [IsAlgClosed (FractionRing R)] :
    Function.Surjective (PreTilt.untilt : Tilt p R → R) := by
  intro a
  choose r hr using fun b : R => exists_pow_eq_of_isAlgClosed b (Fact.out : p.Prime).pos
  refine ⟨(sharpEquiv p R).symm ⟨fun n => r^[n] a, fun n => ?_⟩, ?_⟩
  · beta_reduce
    rw [Function.iterate_succ_apply', hr]
  · exact (untilt_sharpEquiv_symm _).trans rfl

end Tilt

instance PFlat.nonempty_of_isAlgClosed [IsDomain R] [ValuationRing R]
    [IsAlgClosed (FractionRing R)] : Nonempty (PFlat p R) :=
  let ⟨x, hx⟩ := Tilt.untilt_surjective (p := p) (p : R)
  ⟨⟨x, hx⟩⟩

namespace Ainf

omit [IsAdicComplete (span {(p : R)}) R] in
theorem p_dvd_iff (x : Ainf p R) : (p : Ainf p R) ∣ x ↔ x.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker]
  rfl

omit [IsAdicComplete (span {(p : R)}) R] in
theorem p_dvd_sub_teich (x : Ainf p R) : (p : Ainf p R) ∣ x - teich p (x.coeff 0) := by
  rw [p_dvd_iff]
  change WittVector.constantCoeff (x - teich p (x.coeff 0)) = 0
  rw [map_sub]
  simp

theorem coeff_zero_xi (ϖ : PFlat p R) : (xi ϖ).coeff 0 = -ϖ.1 := by
  change WittVector.constantCoeff (xi ϖ) = _
  rw [xi, map_sub, map_natCast]
  simp

theorem mk_theta (x : Ainf p R) : Ideal.Quotient.mk (span {(p : R)}) (theta p R x) =
    Ideal.Quotient.mk _ (PreTilt.untilt (x.coeff 0)) := by
  rw [PreTilt.mk_untilt_eq_coeff_zero]; exact WittVector.mk_fontaineTheta x

variable [IsDomain R]

instance isDomain : IsDomain (Ainf p R) := inferInstanceAs (IsDomain (WittVector p (Tilt p R)))

theorem p_ne_zero : (p : Ainf p R) ≠ 0 := WittVector.p_nonzero p _

theorem xi_ne_zero [CharZero R] (ϖ : PFlat p R) : xi ϖ ≠ 0 := by
  intro h
  have h1 := coeff_zero_xi ϖ
  rw [h, WittVector.zero_coeff, eq_comm, neg_eq_zero] at h1
  have h2 := ϖ.2
  rw [h1, Tilt.untilt_zero, eq_comm, Nat.cast_eq_zero] at h2
  exact (Fact.out : p.Prime).ne_zero h2

variable [ValuationRing R]

theorem theta_surjective [IsAlgClosed (FractionRing R)] : Function.Surjective (theta p R) := by
  intro a
  obtain ⟨x, hx⟩ := Tilt.untilt_surjective (p := p) a
  exact ⟨teich p x, by rw [theta_teich, hx]⟩

theorem exists_eq_xi_mul_add (ϖ : PFlat p R) {x : Ainf p R} (hx : (p : R) ∣ theta p R x) :
    ∃ a y, x = xi ϖ * a + p * y := by
  rw [← mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, mk_theta,
    Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := (Tilt.dvd_iff_untilt_dvd ϖ.1 (x.coeff 0)).2 (by rw [ϖ.2]; exact hx)
  obtain ⟨d, hd⟩ := p_dvd_sub_teich x
  rw [hc, map_mul] at hd
  exact ⟨-teich p c, d + teich p c, by rw [xi]; linear_combination hd⟩

variable [CharZero R]

theorem ker_theta (ϖ : PFlat p R) : RingHom.ker (theta p R) = span {xi ϖ} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · refine mem_span_of_approx (p : Ainf p R) (xi ϖ) (RingHom.ker (theta p R)) ?_ hx
    intro x hx
    have hx' : theta p R x = 0 := hx
    obtain ⟨a, y, h⟩ := exists_eq_xi_mul_add ϖ (x := x) (by rw [hx']; exact dvd_zero _)
    refine ⟨a, y, ?_, h⟩
    rw [h] at hx'
    simpa [(Fact.out : p.Prime).ne_zero] using hx'
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact theta_xi ϖ

theorem theta_eq_zero_iff (ϖ : PFlat p R) (x : Ainf p R) : theta p R x = 0 ↔ xi ϖ ∣ x := by
  rw [← mem_span_singleton, ← ker_theta, RingHom.mem_ker]

end Ainf

namespace AinfInv

omit [IsAdicComplete (span {(p : R)}) R] in
theorem exists_p_pow_mul_eq (x : AinfInv p R) :
    ∃ (k : ℕ) (a : Ainf p R), (p : AinfInv p R) ^ k * x = algebraMap _ _ a := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (p : Ainf p R) x
  exact ⟨k, a, by rw [← h, map_natCast, mul_comm]⟩

variable [IsDomain R]

theorem algebraMap_injective : Function.Injective (algebraMap (Ainf p R) (AinfInv p R)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors Ainf.p_ne_zero)

instance isDomain : IsDomain (AinfInv p R) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Ainf.p_ne_zero (p := p) (R := R)))

variable [ValuationRing R]

theorem theta_surjective [IsAlgClosed (FractionRing R)] : Function.Surjective (theta p R) := by
  intro y
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (p : R) y
  obtain ⟨b, rfl⟩ := Ainf.theta_surjective (p := p) a
  obtain ⟨u, hu⟩ := isUnit_p (R := R) p
  refine ⟨algebraMap _ _ b * ↑(u⁻¹ ^ k), ?_⟩
  rw [map_mul, theta_algebraMap, ← h, map_natCast, mul_assoc, ← map_natCast (theta p R), ← map_pow,
    ← map_mul, ← hu]
  simp [← mul_pow]

variable [CharZero R]

theorem kerTheta_eq (ϖ : PFlat p R) :
    kerTheta p R = span {algebraMap (Ainf p R) (AinfInv p R) (Ainf.xi ϖ)} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨k, a, h⟩ := exists_p_pow_mul_eq x
    have h1 : theta p R (algebraMap _ _ a) = 0 := by
      rw [← h, map_mul, show theta p R x = 0 from hx, mul_zero]
    rw [theta_algebraMap, map_eq_zero_iff _ algebraMap_away_injective,
      Ainf.theta_eq_zero_iff ϖ] at h1
    rw [mem_span_singleton, ← ((isUnit_p (R := R) p).pow k).dvd_mul_left, h]
    exact map_dvd _ h1
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp [RingHom.mem_ker]

theorem kerTheta_fg [IsAlgClosed (FractionRing R)] : (kerTheta p R).FG := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  rw [kerTheta_eq ϖ]
  exact Submodule.fg_span_singleton _

end AinfInv

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.BdR.mulSemiringAction _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.Reformulated.AutPerF.BdR.map_algebraMap _root_.Reformulated.AutPerF.BdRPlus.mapEquiv_apply _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf _root_.Reformulated.AutPerF.BdRPlus.map_id _root_.Reformulated.AutPerF.PFlat.coe_map
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]

namespace BdRPlus

omit [IsDomain R] [ValuationRing R] [CharZero R] in

def xi (ϖ : PFlat p R) : BdRPlus p R := algebraMap (Ainf p R) _ (Ainf.xi ϖ)

theorem eval_eq_zero_iff (ϖ : PFlat p R) (n : ℕ) (x : BdRPlus p R) :
    eval p R n x = 0 ↔ xi ϖ ^ n ∣ x :=
  evalₐ_eq_zero_iff_dvd_of_eq_span (AinfInv.kerTheta_eq ϖ) n x

theorem theta_eq_zero_iff_dvd (ϖ : PFlat p R) (x : BdRPlus p R) :
    theta p R x = 0 ↔ xi ϖ ∣ x := by
  rw [← pow_one (xi ϖ), ← eval_eq_zero_iff, theta_eq_zero_iff]
  refine Iff.trans (Eq.congr_left (AdicCompletion.factorₐ_evalₐ_one _ _).symm)
    (map_eq_zero_iff _ ?_)
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact hy

theorem ker_theta (ϖ : PFlat p R) : RingHom.ker (theta p R) = span {xi ϖ} := by
  ext x
  rw [RingHom.mem_ker, theta_eq_zero_iff_dvd ϖ, mem_span_singleton]

theorem eq_zero_of_xi_mul_eq_zero (ϖ : PFlat p R) {x : BdRPlus p R} (h : xi ϖ * x = 0) : x = 0 :=
  eq_zero_of_algebraMap_mul_eq_zero (AinfInv.kerTheta_eq ϖ)
    ((map_ne_zero_iff _ AinfInv.algebraMap_injective).2 (Ainf.xi_ne_zero ϖ)) h

theorem eq_zero_of_forall_xi_pow_dvd (ϖ : PFlat p R) {x : BdRPlus p R}
    (h : ∀ n : ℕ, xi ϖ ^ n ∣ x) : x = 0 :=
  ext_eval fun n => by rw [map_zero, eval_eq_zero_iff ϖ]; exact h n

variable [IsAlgClosed (FractionRing R)]

theorem ker_theta_eq_map : RingHom.ker (theta p R) =
    (AinfInv.kerTheta p R).map (algebraMap (AinfInv p R) (BdRPlus p R)) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have h := congrArg (Ideal.map (algebraMap (AinfInv p R) (BdRPlus p R))) (AinfInv.kerTheta_eq ϖ)
  rw [ker_theta ϖ, h, Ideal.map_span, Set.image_singleton]
  rfl

instance isAdicComplete_ker_theta : IsAdicComplete (RingHom.ker (theta p R)) (BdRPlus p R) := by
  rw [ker_theta_eq_map]
  exact AdicCompletion.isAdicComplete_self _ AinfInv.kerTheta_fg

omit [CharZero R] in

theorem theta_surjective : Function.Surjective (theta p R) := fun y =>
  let ⟨x, hx⟩ := AinfInv.theta_surjective (p := p) y
  ⟨algebraMap _ _ x, hx⟩

theorem isUnit_iff_theta_ne_zero (x : BdRPlus p R) : IsUnit x ↔ theta p R x ≠ 0 := by
  have := (isField_away p R).nontrivial
  refine ⟨fun h => (h.map _).ne_zero, fun h => ?_⟩
  obtain ⟨z, hz⟩ := (isField_away p R).mul_inv_cancel h
  obtain ⟨y, rfl⟩ := theta_surjective (p := p) z
  have h1 : x * y - 1 ∈ RingHom.ker (theta p R) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hz, map_one, sub_self]
  have h2 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2

theorem exists_associated_xi_pow (ϖ : PFlat p R) {x : BdRPlus p R} (hx : x ≠ 0) :
    ∃ n : ℕ, Associated (xi ϖ ^ n) x := by
  classical
  have h : ∃ n : ℕ, ¬xi ϖ ^ (n + 1) ∣ x := by
    by_contra h
    push Not at h
    exact hx (eq_zero_of_forall_xi_pow_dvd ϖ fun n => (pow_dvd_pow _ n.le_succ).trans (h n))
  obtain ⟨u, hu⟩ : xi ϖ ^ Nat.find h ∣ x := by
    rcases e : Nat.find h with _ | m
    · simp
    · exact not_not.1 (Nat.find_min h (by omega))
  have hu' : IsUnit u := by
    rw [isUnit_iff_theta_ne_zero, Ne, theta_eq_zero_iff_dvd ϖ]
    intro hd
    apply Nat.find_spec h
    obtain ⟨v, rfl⟩ := hd
    exact ⟨v, hu.trans (by ring)⟩
  exact ⟨_, hu'.unit, hu.symm⟩

instance nontrivial : Nontrivial (BdRPlus p R) :=
  have := (isField_away p R).nontrivial
  (theta p R).domain_nontrivial

instance isDomain : IsDomain (BdRPlus p R) := by
  obtain ⟨ϖ⟩ : Nonempty (PFlat p R) := inferInstance
  have key : ∀ (n : ℕ) (y : BdRPlus p R), xi ϖ ^ n * y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro y hy
      exact ih y (eq_zero_of_xi_mul_eq_zero ϖ (by rw [← mul_assoc, ← pow_succ', hy]))
  have : NoZeroDivisors (BdRPlus p R) := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    obtain ⟨n, u, rfl⟩ := exists_associated_xi_pow ϖ ha
    exact Or.inr ((Units.mul_right_eq_zero u).1 (key n _ (by rw [← mul_assoc, h])))⟩
  exact NoZeroDivisors.to_isDomain _

end BdRPlus

namespace BdR

variable [IsAlgClosed (FractionRing R)]

instance field : Field (BdR p R) := IsFractionRing.toField (BdRPlus p R)

end BdR

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.BasicNotions.Loc.maxUnramifiedAlgebra _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.BdRPlus.isAdicComplete_ker_theta _root_.Reformulated.AutPerF.BdRPlus.isDomain _root_.Reformulated.AutPerF.BdRPlus.nontrivial _root_.Reformulated.AutPerF.isFractionRing_away
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]

namespace BdRPlus

def thetaC : BdRPlus p O →+* C :=
  (IsUnitBall.awayEquiv O p).toRingEquiv.toRingHom.comp (theta p O)

end BdRPlus

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.CrystallineRing.Acris0
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.BdR.field _root_.Reformulated.AutPerF.BdRPlus.isAdicComplete_ker_theta _root_.Reformulated.AutPerF.BdRPlus.isDomain _root_.Reformulated.AutPerF.BdRPlus.nontrivial _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.isFractionRing_away
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace UpperTheory.Ring.Comp

open Reformulated.AutPerF

abbrev Ainf (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.Ainf l (PadicComplexInt l)

abbrev AinfP (l : ℕ) [Fact (Nat.Prime l)] : Type := AinfInv l (PadicComplexInt l)

abbrev BdRp (l : ℕ) [Fact (Nat.Prime l)] : Type := BdRPlus l (PadicComplexInt l)

abbrev BdR (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.BdR l (PadicComplexInt l)

abbrev Acris0 (l : ℕ) [Fact (Nat.Prime l)] : Subalgebra (Ainf l) (AinfP l) := acrisZero l (PadicComplexInt l)

abbrev Acris (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.Acris l (PadicComplexInt l)

abbrev Bcris (l : ℕ) [Fact (Nat.Prime l)] : Type := Reformulated.AutPerF.Bcris l (PadicComplexInt l)

def zP (l : ℕ) [Fact (Nat.Prime l)] : ℤ_[l] →+* AinfP l := algebraMap ℤ_[l] (AinfP l)

def pD (l : ℕ) [Fact (Nat.Prime l)] : AinfP l →+* BdR l :=
  (algebraMap (BdRp l) (BdR l)).comp (algebraMap (AinfP l) (BdRp l))

def zD (l : ℕ) [Fact (Nat.Prime l)] : ℤ_[l] →+* BdR l := (pD l).comp (zP l)

def aB (l : ℕ) [Fact (Nat.Prime l)] : Ainf l →+* Bcris l :=
  (algebraMap (Acris l) (Bcris l)).comp (algebraMap (Ainf l) (Acris l))

def a0B (l : ℕ) [Fact (Nat.Prime l)] : Acris0 l →+* Bcris l :=
  (algebraMap (Acris l) (Bcris l)).comp (algebraMap (AcrisZero l (PadicComplexInt l)) (Acris l))

def zB (l : ℕ) [Fact (Nat.Prime l)] : ℤ_[l] →+* Bcris l :=
  (algebraMap (Acris l) (Bcris l)).comp (algebraMap ℤ_[l] (Acris l))

def σD {l : ℕ} [Fact (Nat.Prime l)] (g : Gq l) : BdR l →+* BdR l :=
  MulSemiringAction.toRingHom (Gq l) (BdR l) g

end UpperTheory.Ring.Comp
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.Per

open Reformulated.AutPerF

section Cp
variable {p : ℕ} [Fact p.Prime]
def σO (g : Gq p) : OC p →+* OC p := MulSemiringAction.toRingHom (Gq p) (OC p) g
end Cp

section Explicit
variable (l : ℕ) [Fact l.Prime]
abbrev Fl : Type := Tilt l (OC l)
def AinfP : Type := AinfInv l (OC l)
instance instCommRingAinfP : CommRing (AinfP l) := inferInstanceAs (CommRing (AinfInv l (OC l)))
instance instAlgebraAinfAinfP : Algebra (Ainf l) (AinfP l) := inferInstanceAs (Algebra (Ainf l) (AinfInv l (OC l)))
instance instAwayAinfCastAinfP : IsLocalization.Away ((l : ℕ) : Ainf l) (AinfP l) :=
  inferInstanceAs (IsLocalization.Away ((l : ℕ) : Ainf l) (AinfInv l (OC l)))
def kerP : Ideal (AinfP l) := AinfInv.kerTheta l (OC l)
def BdRp : Type := BdRPlus l (OC l)
instance instCommRingBdRp : CommRing (BdRp l) := inferInstanceAs (CommRing (BdRPlus l (OC l)))
instance instAlgebraAinfPBdRp : Algebra (AinfP l) (BdRp l) := inferInstanceAs (Algebra (AinfInv l (OC l)) (BdRPlus l (OC l)))
def ev (n : ℕ) : BdRp l →+* AinfP l ⧸ kerP l ^ n := BdRPlus.eval l (OC l) n
def θD : BdRp l →+* ℂ_[l] := BdRPlus.thetaC l (PadicComplexInt l)
def BdR : Type := Reformulated.AutPerF.BdR l (OC l)
instance instCommRingBdR : CommRing (BdR l) := inferInstanceAs (CommRing (Reformulated.AutPerF.BdR l (OC l)))
instance instAlgebraBdRpBdR : Algebra (BdRp l) (BdR l) := inferInstanceAs (Algebra (BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l)))
instance instIsFractionRingBdR : IsFractionRing (BdRp l) (BdR l) :=
  inferInstanceAs (IsFractionRing (BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l)))
def pD : AinfP l →+* BdR l := UpperTheory.Ring.Comp.pD l
def zD : ℤ_[l] →+* BdR l := UpperTheory.Ring.Comp.zD l
def FilD (a : ℤ) : Submodule (BdRp l) (BdR l) := BdR.fil l (OC l) a
def Acris0 : Subalgebra (Ainf l) (AinfP l) := acrisZero l (OC l)
def Acris : Type := Reformulated.AutPerF.Acris l (OC l)
instance instCommRingAcris : CommRing (Acris l) := inferInstanceAs (CommRing (Reformulated.AutPerF.Acris l (OC l)))
instance instAlgebraAcris0Acris : Algebra ↥(Acris0 l) (Acris l) :=
  inferInstanceAs (Algebra (AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l)))
instance instAlgebraAinfAcris : Algebra (Ainf l) (Acris l) := inferInstanceAs (Algebra (Ainf l) (Reformulated.AutPerF.Acris l (OC l)))
def Bcris : Type := Reformulated.AutPerF.Bcris l (OC l)
instance instCommRingBcris : CommRing (Bcris l) := inferInstanceAs (CommRing (Reformulated.AutPerF.Bcris l (OC l)))
instance instAlgebraAcrisBcris : Algebra (Acris l) (Bcris l) :=
  inferInstanceAs (Algebra (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)))
def aB : Ainf l →+* Bcris l := UpperTheory.Ring.Comp.aB l
def a0B : ↥(Acris0 l) →+* Bcris l := UpperTheory.Ring.Comp.a0B l
def zB : ℤ_[l] →+* Bcris l := UpperTheory.Ring.Comp.zB l
def φB : Bcris l →+* Bcris l := Bcris.frob l (OC l)
structure IsCrisDR (f : Bcris l →+* BdR l) : Prop where
  on0 : ∀ a : Acris0 l, f (a0B l a) = pD l (a : AinfP l)
  bdd : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Acris l, ∃ (y : BdRp l) (a : Ainf l),
    f (algebraMap (Acris l) (Bcris l) x) = algebraMap (BdRp l) (BdR l) y ∧
      ev l n (((l : ℕ) : BdRp l) ^ N * y) = Ideal.Quotient.mk _ (algebraMap (Ainf l) (AinfP l) a)
end Explicit

section Implicit
variable {l : ℕ} [Fact l.Prime]
abbrev tm (x : Fl l) : Ainf l := WittVector.teichmuller l x
def σD (g : Gq l) : BdR l →+* BdR l := UpperTheory.Ring.Comp.σD g
def σB (g : Gq l) : Bcris l →+* Bcris l := Bcris.map l (σO g) (MulAction.injective g)
def IsLog (l : ℕ) [Fact l.Prime] (e : Fl l) (y : BdRp l) : Prop :=
  ∃ h, y = BdRPlus.log (algebraMap (Ainf l) (BdRPlus l (OC l)) (tm e)) h
end Implicit

end Formalism.Per
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.OL_finite _root_.Formalism.BasicNotions.Examples₂.LB.OL_frac _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Examples₂.LB.instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace Formalism.BasicNotions

open Loc
open scoped Formalism.Per

structure LocTied (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) where

  eB : P.R.B ≃+* Per.Bcris l

  eD : P.R.BdR ≃+* Per.BdR l

  zB : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] P.R.B (z : ℚ_[l])) = Per.zB l z

  zD : ∀ z : ℤ_[l], eD (algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) = Per.zD l z

  om : ∀ x : Om l, ∃ y : Per.BdRp l, eD (algebraMap (Om l) P.R.BdR x) = algebraMap (Per.BdRp l) (Per.BdR l) y ∧
    Per.θD l y = ((x : Om l) : ℂ_[l])

  actB : ∀ (g : GQ l) (b : P.R.B), eB (P.actQ g b) = Per.σB g (eB b)

  actD : ∀ (g : GQ l) (b : P.R.BdR), eD (P.actQdR g b) = Per.σD g (eD b)

  frob : ∀ b : P.R.B, eB (P.φB b) = Per.φB l (eB b)

  incl : Per.IsCrisDR l ((eD.toRingHom.comp (P.ιB : P.R.B →+* P.R.BdR)).comp eB.symm.toRingHom)

  fil : ∀ (K : FinExt l) (a : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a ↔ eD x ∈ Per.FilD l a

  t : ∃ y : Per.BdRp l, Per.IsLog l AI.ε y ∧ eD (P.ιB P.tB) = algebraMap (Per.BdRp l) (Per.BdR l) y

  ιA : ∀ a : Ainf l, eB (AI.ιA a) = Per.aB l a

end Formalism.BasicNotions
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section
namespace GlobalTheory.CrisMaps
open Formalism
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

@[irreducible] def frob (l : ℕ) [Fact l.Prime] : Per.Acris l →+* Per.Acris l := Reformulated.AutPerF.Acris.frob l (Per.OC l)

@[irreducible] def gal (g : Per.Gq l) : Per.Acris l →+* Per.Acris l := Reformulated.AutPerF.Acris.map l (Per.σO g)

end GlobalTheory.CrisMaps
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Topology
open scoped ContDiff

namespace GlobalTheory.CuspRep

theorem isOpen_ker_finIdele (E : Type) [Field E] [NumberField E] (ψ : (FiniteAdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (hψ : Continuous ψ) : IsOpen {u | ψ u = 1} := by
  have hV : {u | ‖((ψ u : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : (FiniteAdeleRing (𝓞 E) E)ˣ) := by
    refine (isOpen_lt (((Units.continuous_val.comp hψ).sub continuous_const).norm) continuous_const).mem_nhds ?_
    simp
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  have hf : Continuous fun b : FiniteAdeleRing (𝓞 E) E => 1 + b := continuous_const.add continuous_id
  have h1 : (fun b : FiniteAdeleRing (𝓞 E) E => 1 + b) ⁻¹' T1 ∈ 𝓝 0 :=
    hf.continuousAt.preimage_mem_nhds (by rw [add_zero]; exact hT1)
  have h2 : (fun b : FiniteAdeleRing (𝓞 E) E => MulOpposite.op (1 + b)) ⁻¹' T2 ∈ 𝓝 0 :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, add_zero]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E _ (Filter.inter_mem h1 h2)
  let P : Set (FiniteAdeleRing (𝓞 E) E) :=
    {c | ∃ a : FiniteAdeleRing (𝓞 E) E, (∀ v, a v ∈ v.adicCompletionIntegers E) ∧ c = N • a}
  have hP : P ∈ 𝓝 0 := GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds E N hN
  have hmul : ∀ x y : FiniteAdeleRing (𝓞 E) E, x - 1 ∈ P → y - 1 ∈ P → x * y - 1 ∈ P := by
    rintro x y ⟨a, ha, e⟩ ⟨b, hb, e'⟩
    refine ⟨a + b + N • (a * b), fun v => add_mem (add_mem (ha v) (hb v)) (nsmul_mem (mul_mem (ha v) (hb v)) N), ?_⟩
    rw [eq_add_of_sub_eq e, eq_add_of_sub_eq e']
    simp only [nsmul_eq_mul]; ring
  let H : Submonoid (FiniteAdeleRing (𝓞 E) E)ˣ :=
    { carrier := {u | (u : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P ∧ ((u⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) - 1 ∈ P}
      one_mem' := ⟨by simpa using mem_of_mem_nhds hP, by simpa using mem_of_mem_nhds hP⟩
      mul_mem' := fun {x y} hx hy => ⟨hmul _ _ hx.1 hy.1, by rw [mul_inv, Units.val_mul]; exact hmul _ _ hx.2 hy.2⟩ }
  have hH : (H : Set (FiniteAdeleRing (𝓞 E) E)ˣ) ∈ 𝓝 1 := by
    refine Filter.inter_mem ?_ ?_
    · exact (Units.continuous_val.sub (continuous_const (y := 1))).continuousAt.preimage_mem_nhds (t := P) (by simpa using hP)
    · exact (Units.continuous_coe_inv.sub (continuous_const (y := 1))).continuousAt.preimage_mem_nhds (t := P) (by simpa using hP)
  have hk : ∀ u ∈ H, ψ u = 1 := by
    intro u hu
    apply Units.ext
    refine eq_one_of_pow_near fun n => ?_
    obtain ⟨⟨a, ha, e⟩, ⟨b, hb, e'⟩⟩ := pow_mem hu n
    have := hTV (a := u ^ n) (hTT ⟨?_, ?_⟩)
    · simpa using this
    · change ((u ^ n : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ T1
      rw [eq_add_of_sub_eq' e]; exact (hNW a ha).1
    · change MulOpposite.op (((u ^ n)⁻¹ : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) ∈ T2
      rw [eq_add_of_sub_eq' e']; exact (hNW b hb).2
  exact ψ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hH hk)

variable {ι : Type} [Fintype ι]

theorem exists_bound (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (u : (ι → ℂ)ˣ) (B : ℝ), 1 ≤ B → ‖(u : ι → ℂ)‖ ≤ B → ‖((u⁻¹ : (ι → ℂ)ˣ) : ι → ℂ)‖ ≤ B →
      ‖((ψ u : ℂˣ) : ℂ)‖ ≤ C * B ^ N := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  obtain ⟨N, hN⟩ := exists_nat_ge ‖L‖
  refine ⟨Real.exp (N * Real.pi), N, (Real.exp_pos _).le, fun u B hB h1 h2 => ?_⟩
  have hl : 0 ≤ Real.log B := Real.log_nonneg hB
  have hz : ‖fun i => Complex.log ((u : ι → ℂ) i)‖ ≤ Real.pi + Real.log B := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im, add_comm]
    refine add_le_add (Complex.abs_arg_le_pi _) (abs_le.2 ⟨?_, ?_⟩)
    · have e : ((u⁻¹ : (ι → ℂ)ˣ) : ι → ℂ) i = ((u : ι → ℂ) i)⁻¹ :=
        eq_inv_of_mul_eq_one_right (congrFun u.mul_inv i)
      have := Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u⁻¹ i)) ((norm_le_pi_norm _ i).trans h2)
      rw [e, norm_inv, Real.log_inv] at this
      linarith
    · exact Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u i)) ((norm_le_pi_norm _ i).trans h1)
  rw [← expU_log u, hL, Complex.norm_exp]
  have h3 : (L fun i => Complex.log ((u : ι → ℂ) i)).re ≤ N * (Real.pi + Real.log B) :=
    (Complex.re_le_norm _).trans ((L.le_opNorm _).trans (mul_le_mul hN hz (norm_nonneg _) (Nat.cast_nonneg _)))
  refine (Real.exp_le_exp.2 h3).trans_eq ?_
  rw [mul_add, Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity)]

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.PRep

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

variable {W : Type} [AddCommGroup W] [Module k W]

def ind (H : Subgroup G) (σ : Representation k H W) : Representation k G (indSpace H σ) :=
  sub (rightReg k G W) (indSpace H σ) (by
    intro g f hf h x
    have := hf h (x * g)
    simpa [rightReg, LinearMap.funLeft, mul_assoc] using this)

section Top2
variable [TopologicalSpace G] [IsTopologicalGroup G]

def smoothRep (ρ : Representation k G V) : Representation k G (smoothPart ρ) :=
  sub ρ (smoothPart ρ) (smoothPart_stable ρ)

def smInd (H : Subgroup G) (σ : Representation k H W) :
    Representation k G (smoothPart (ind H σ)) := smoothRep (ind H σ)

end Top2

end GlobalTheory.PRep
end
end

section
-- module Solutions.AlpoGe.ReciprocityTheory.GaloisValuations.Global
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

section Basic₃

theorem exists_isFrob [IsAlgClosure F Ω] {A : ValuationSubring (Ω)} {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) : ∃ σ : G F Ω, IsFrob A (normV v) σ := by
  exact exists_frob_over h

end Basic₃

end ReciprocityTheory.Gal
end
end

section
-- module Solutions.AlpoGe.Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

namespace Formalism.UG.P

open Formalism.UG

section Adic

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem glint_exists_approx (x : v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v ((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  first | exact Bl.NearbyExistence.goal1 .. | (apply Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply @Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> first | assumption | infer_instance)

theorem glint_finite_residueField :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hmem : ∀ y : v.adicCompletionIntegers F, Valued.v (y : v.adicCompletion F) < 1 →
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := fun y hy =>
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))).2 hy
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    apply hmem
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨r, ?_⟩
    simp only [φ, RingHom.comp_apply]
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    apply hmem
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r - x : v.adicCompletionIntegers F) :
        v.adicCompletion F) = -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, neg_sub, algebraMap_adicCompletionIntegers_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), algebraMap_adicCompletion]
      rfl
    rw [e, Valuation.map_neg]
    exact hr
  have := v.isMaximal
  have hs : Function.Surjective (Ideal.Quotient.lift v.asIdeal φ hker) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  exact Finite.of_surjective _ hs

end Adic

end Formalism.UG.P
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.CuspRep.CuspSub.op_val _root_.GlobalTheory.CuspRep.mulChi_apply _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped ContDiff

namespace GlobalTheory.CuspRep

variable (E : Type) [Field E] [NumberField E]

open Classical in

def sLoc (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* Af E where
  toFun x := ⟨Pi.single w x, by
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with v hv
    rw [Pi.single_eq_of_ne hv]
    exact zero_mem _⟩
  map_mul' x y := Subtype.ext (Pi.single_mul (α := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x y)
  map_zero' := Subtype.ext (Pi.single_zero (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w)
  map_add' x y := Subtype.ext (Pi.single_add (f := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x y)

def locGL (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : GL (Fin a) (w.adicCompletion E) →* GL (Fin a) (Af E) :=
  cornerGL a (sLoc E w)

theorem continuous_finId : Continuous (finId E) :=
  Continuous.units_map _ (continuous_const.add (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)))

variable [IsTotallyComplex E]

variable {E} {a : ℕ}

theorem det_finGL (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.det (finGL E a k) = finId E (GeneralLinearGroup.det k) := by
  refine Units.ext (ad_ext ?_ ?_)
  · rw [← det_map, pInf_finGL]
    change _ = pInf E (1 - sFin E 1 + sFin E _)
    have h : ∀ x, pInf E (sFin E x) = 0 := fun x => map_zero (infEq E).symm
    simp [h]
  · rw [← det_map, pFin_finGL]
    change _ = (1 : Af E) - 1 + (GeneralLinearGroup.det k : (Af E)ˣ)
    simp

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.CuspRep.CuspSub.op_val _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open scoped ContDiff

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (X : Fin a → Fin a → A)
    (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp [Formalism.REAL.Tm, apply_ite f]

theorem qdet_shift {A : Type} [Ring A] [Algebra ℂ A] (X : Fin a → Fin a → A) (s u : ℂ) :
    Formalism.REAL.qdet (fun i j => X i j + if i = j then algebraMap ℂ A s else 0) u = Formalism.REAL.qdet X (u + s) := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Formalism.REAL.Tm]
  split_ifs
  · simp only [map_sub, map_add]; abel
  · simp

theorem rt_mulChi (χ : HChar E) (h : GA E a) (φ : Sm E a) :
    rt E a h (mulChi a χ φ) = mulChi a χ (((chiDet a χ h : ℂˣ) : ℂ) • rt E a h φ) :=
  Subtype.ext <| funext fun g => by
    simp only [rt_apply, mulChi_apply, map_mul, Units.val_mul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

theorem lie_mulChi (χ : HChar E) (X : Lie E a) (φ : Sm E a) :
    lie E a X (mulChi a χ φ) = mulChi a χ (lie E a X φ + dchi χ (Matrix.of X).trace • φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have h1 : (Matrix.of (oneL E a)).det = 1 := Matrix.det_one
  have hd : HasFDerivAt (fun x : Lie E a => extZero (chiInf χ) (Matrix.of x).det)
      ((dchi χ).comp (fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a))) (oneL E a) := by
    refine HasFDerivAt.comp (g := extZero (chiInf χ)) _ ?_ (contDiff_det.differentiable (by simp) _).hasFDerivAt
    rw [h1]
    exact ((contDiffAt_extZero _ (continuous_chiInf χ) 1).differentiableAt (by simp)).hasFDerivAt
  have h2 := ((differentiableAt_chart φ.2 g).hasFDerivAt.mul (hd.const_mul ((chiDet a χ g : ℂˣ) : ℂ))).fderiv
  have h3 : extZero (chiInf χ) 1 = 1 := (extZero_unit _ 1).trans (by simp)
  have h4 : chart φ.1 g (oneL E a) = φ.1 g := (chart_val φ.1 g 1).trans (by simp)
  change fderiv ℝ (chart (fun x => φ.1 x * (chiDet a χ x : ℂˣ)) g) _ X = (lieD X φ.1 g + _ * φ.1 g) * _
  rw [chart_mul_chi]
  refine (congrArg (fun L : Lie E a →L[ℝ] ℂ => L X) h2).trans ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    fderiv_det_one, h1, h3, h4, smul_eq_mul, lieD]
  ring

theorem Eop_mulChi (χ : HChar E) (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (mulChi a χ φ) = mulChi a χ (Eop τ i j φ + (if i = j then expo χ τ else 0) • φ) := by
  have ht : ∀ x : Cinf E, (Matrix.of (toL (Matrix.single i j x))).trace = if i = j then x else 0 := fun x => by
    change (Matrix.single i j x).trace = _
    split_ifs with h
    · subst h; simp
    · exact Matrix.trace_single_eq_of_ne _ _ _ h
  simp only [Eop, lieS_apply, LinearMap.smul_apply, LinearMap.sub_apply, lie_mulChi, ht]
  rw [← map_smul (mulChi a χ), ← map_sub (mulChi a χ), ← map_smul (mulChi a χ)]
  congr 1
  split_ifs
  · simp only [expo]; match_scalars <;> ring
  · simp

theorem cap_mulChi (χ : HChar E) (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (mulChi a χ φ) = mulChi a χ (cap τ (u + expo χ τ) φ) := by
  have h := map_qdet ((mulChi a χ).conjAlgEquiv ℂ).toAlgHom
    (fun i j => Eop τ i j + if i = j then algebraMap ℂ _ (expo χ τ) else 0) (u + ((a : ℂ) - 1) / 2)
  have e : (fun i j => ((mulChi a χ).conjAlgEquiv ℂ).toAlgHom
      (Eop τ i j + if i = j then algebraMap ℂ _ (expo χ τ) else 0)) = Eop τ := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (mulChi a χ).surjective ψ
    rw [Eop_mulChi]
    change mulChi a χ ((Eop τ i j + if i = j then algebraMap ℂ _ (expo χ τ) else 0)
      ((mulChi a χ).symm (mulChi a χ ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
    split_ifs <;> simp
  rw [e, qdet_shift] at h
  rw [cap, ← h, cap, add_right_comm u (expo χ τ)]
  generalize Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2 + expo χ τ) = z
  change mulChi a χ (z ((mulChi a χ).symm (mulChi a χ φ))) = _
  rw [LinearEquiv.symm_apply_apply]

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

section Cong

variable {A : ValuationSubring Ω}

theorem val_apply_le_one {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (σ x) ≤ 1 := by
  rw [A.valuation_le_one_iff] at hx ⊢
  exact (apply_mem_iff_of_mem_Dec hσ x).mpr hx

end Cong

def ActsAs (A : ValuationSubring Ω) (q : ℕ) (σ : G E Ω) (a b : ℕ) : Prop :=
  σ ∈ Dec (F := E) A ∧
    ∀ x, A.valuation x ≤ 1 → A.valuation ((σ x) ^ (q ^ b) - x ^ (q ^ a)) < 1

section ActsAs

variable {A : ValuationSubring Ω} {q : ℕ}

theorem ActsAs.mul {σ τ : G E Ω} {a b c d : ℕ} (hσ : ActsAs A q σ a b) (hτ : ActsAs A q τ c d) :
    ActsAs A q (σ * τ) (a + c) (b + d) := by
  refine ⟨(Dec (F := E) A).mul_mem hσ.1 hτ.1, fun x hx => ?_⟩
  have hy := val_apply_le_one hτ.1 hx
  have h1 := cong_pow (val_pow_le_one (val_apply_le_one hσ.1 hy) _) (val_pow_le_one hy _)
    (hσ.2 _ hy) (q ^ d)
  have h2 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (hτ.2 _ hx) (q ^ a)
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add] at h1 h2
  rw [add_comm d a, add_comm c a] at h2
  exact cong_trans h1 h2

theorem ActsAs.inv {σ : G E Ω} {a b : ℕ} (hσ : ActsAs A q σ a b) : ActsAs A q σ⁻¹ b a := by
  refine ⟨(Dec (F := E) A).inv_mem hσ.1, fun x hx => ?_⟩
  have hy := val_apply_le_one ((Dec (F := E) A).inv_mem hσ.1) hx
  have h1 := hσ.2 _ hy
  rw [mul_inv_apply] at h1
  exact cong_symm h1

theorem actsAs_zero_iff {σ : G E Ω} : ActsAs A q σ 0 0 ↔ σ ∈ Ine (F := E) A := by
  simp only [ActsAs, pow_zero, pow_one]
  exact Iff.rfl

theorem actsAs_one_iff {σ : G E Ω} : ActsAs A q σ 1 0 ↔ IsFrob A q σ := by
  simp only [ActsAs, pow_zero, pow_one]
  exact Iff.rfl

theorem ActsAs.unique [IsAlgClosed Ω] (hq : 1 < q) {σ : G E Ω} {a b c d : ℕ}
    (h : ActsAs A q σ a b) (h' : ActsAs A q σ c d) : (a : ℤ) - b = (c : ℤ) - d := by
  have h1 := h.inv.mul h'
  rw [inv_mul_cancel] at h1
  have key : ∀ m n : ℕ, ActsAs A q (1 : G E Ω) m n → ¬ n < m := by
    intro m n hmn hlt
    obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A) (pow_pos (zero_lt_one.trans hq) n)
      (pow_lt_pow_right₀ hq hlt)
    exact hx' (cong_symm (hmn.2 x hx))
  have k1 := key _ _ h1
  have k2 := key _ _ (by simpa using h1.inv)
  omega

theorem ActsAs.cancel {φ : G E Ω} (hφ : IsFrob A q φ) {σ : G E Ω} {a b : ℕ} (n : ℕ)
    (h : ActsAs A q σ (a + n) (b + n)) : ActsAs A q σ a b := by
  induction n with
  | zero => exact h
  | succ n ih =>
    refine ih ⟨h.1, fun x hx => ?_⟩
    have h1 := h.2 x hx
    rw [← add_assoc, ← add_assoc, pow_succ, pow_succ, pow_mul, pow_mul] at h1
    have hu := val_pow_le_one (val_apply_le_one h.1 hx) (q ^ (b + n))
    have hv := val_pow_le_one hx (q ^ (a + n))
    rw [← valuation_apply_lt_one_iff hφ.1, map_sub]
    exact cong_trans (cong_trans (hφ.2 _ hu) h1) (cong_symm (hφ.2 _ hv))

end ActsAs

def weilSub (A : ValuationSubring Ω) (q : ℕ) : Subgroup (G E Ω) where
  carrier := {σ | ∃ a b, ActsAs A q σ a b}
  one_mem' := ⟨0, 0, actsAs_zero_iff.mpr (Ine (F := E) A).one_mem⟩
  mul_mem' := by
    rintro σ τ ⟨a, b, h⟩ ⟨c, d, h'⟩
    exact ⟨_, _, h.mul h'⟩
  inv_mem' := by
    rintro σ ⟨a, b, h⟩
    exact ⟨_, _, h.inv⟩

theorem one_lt_normV (w : HeightOneSpectrum (𝓞 E)) : 1 < normV w := by
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  exact Finite.one_lt_card

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

def Weil (_h : IsPlaceOver A w) : Subgroup (G E Ω) := weilSub A (normV w)

variable (h : IsPlaceOver A w)

theorem Ine_le_Weil : Ine (F := E) A ≤ Weil h := fun _ hσ => ⟨0, 0, actsAs_zero_iff.mpr hσ⟩

theorem mem_Weil_of_isFrob {σ : G E Ω} (hσ : IsFrob A (normV w) σ) : σ ∈ Weil h :=
  ⟨1, 0, actsAs_one_iff.mpr hσ⟩

def ineIncl : Ine (F := E) A →* Weil h := Subgroup.inclusion (Ine_le_Weil h)

@[simp] theorem coe_ineIncl (σ : Ine (F := E) A) : (ineIncl h σ : G E Ω) = σ := rfl

variable {h}

def deg (σ : Weil h) : ℤ :=
  (σ.2.choose : ℤ) - (σ.2.choose_spec.choose : ℤ)

variable [IsAlgClosure E Ω]

theorem deg_eq {σ : Weil h} {a b : ℕ} (hσ : ActsAs A (normV w) (σ : G E Ω) a b) :
    deg σ = (a : ℤ) - b :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  ActsAs.unique (one_lt_normV w) σ.2.choose_spec.choose_spec hσ

@[simp] theorem deg_mul (σ τ : Weil h) : deg (σ * τ) = deg σ + deg τ := by
  obtain ⟨a, b, hσ⟩ := σ.2
  obtain ⟨c, d, hτ⟩ := τ.2
  rw [deg_eq hσ, deg_eq hτ, deg_eq (σ := σ * τ) (hσ.mul hτ)]
  push_cast; ring

@[simp] theorem deg_one : deg (1 : Weil h) = 0 := by
  have := deg_mul (1 : Weil h) 1
  rw [mul_one] at this; omega

@[simp] theorem deg_inv (σ : Weil h) : deg σ⁻¹ = -deg σ := by
  have := deg_mul σ σ⁻¹
  rw [mul_inv_cancel, deg_one] at this; omega

variable (h) in

def degHom : Weil h →* Multiplicative ℤ where
  toFun σ := Multiplicative.ofAdd (deg σ)
  map_one' := by simp
  map_mul' σ τ := by simp [ofAdd_add]

@[simp] theorem degHom_apply (σ : Weil h) : degHom h σ = Multiplicative.ofAdd (deg σ) := rfl

@[simp] theorem deg_zpow (σ : Weil h) (n : ℤ) : deg (σ ^ n) = n * deg σ := by
  have := congrArg Multiplicative.toAdd (map_zpow (degHom h) σ n)
  simpa using this

@[simp] theorem deg_pow (σ : Weil h) (n : ℕ) : deg (σ ^ n) = n * deg σ := by
  rw [← zpow_natCast, deg_zpow]

theorem actsAs_of_deg {σ : Weil h} {a b : ℕ} (hσ : deg σ = (a : ℤ) - b) :
    ActsAs A (normV w) (σ : G E Ω) a b := by
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  obtain ⟨c, d, hcd⟩ := σ.2
  rw [deg_eq hcd] at hσ
  have h1 : ActsAs A (normV w) (1 : G E Ω) b b := ⟨(Dec (F := E) A).one_mem, fun x _ => by simp⟩
  have h2 := hcd.mul h1
  rw [mul_one, show c + b = a + d by omega, add_comm d b] at h2
  exact ActsAs.cancel hφ d h2

theorem deg_eq_zero_iff {σ : Weil h} : deg σ = 0 ↔ (σ : G E Ω) ∈ Ine (F := E) A :=
  ⟨fun hσ => actsAs_zero_iff.mp (actsAs_of_deg (a := 0) (b := 0) (by simpa using hσ)),
    fun hσ => by simpa using deg_eq (actsAs_zero_iff.mpr hσ)⟩

theorem deg_eq_one_iff {σ : Weil h} : deg σ = 1 ↔ IsFrob A (normV w) (σ : G E Ω) :=
  ⟨fun hσ => actsAs_one_iff.mp (actsAs_of_deg (a := 1) (b := 0) (by simpa using hσ)),
    fun hσ => by simpa using deg_eq (actsAs_one_iff.mpr hσ)⟩

@[simp] theorem deg_ineIncl (σ : Ine (F := E) A) : deg (ineIncl h σ) = 0 :=
  deg_eq_zero_iff.mpr σ.2

variable (h) in

def frob : Weil h := ⟨(exists_isFrob h).choose, mem_Weil_of_isFrob h (exists_isFrob h).choose_spec⟩

theorem isFrob_frob : IsFrob A (normV w) (frob h : G E Ω) := (exists_isFrob h).choose_spec

@[simp] theorem deg_frob : deg (frob h) = 1 := deg_eq_one_iff.mpr isFrob_frob

variable (h) in

def unrChar (c : ℂˣ) : Weil h →* ℂˣ := (zpowersHom ℂˣ c).comp (degHom h)

@[simp] theorem unrChar_apply (c : ℂˣ) (σ : Weil h) : unrChar h c σ = c ^ deg σ := rfl

variable (w) in

def qPow (s : ℝ) : ℂˣ :=
  Units.mk0 (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) (by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot))

omit [IsAlgClosure E Ω] in

@[simp] theorem coe_qPow (s : ℝ) : (qPow w s : ℂ) = ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) := rfl

omit [IsAlgClosure E Ω] in

@[simp] theorem qPow_zero : qPow w 0 = 1 := Units.ext (by simp)

omit [IsAlgClosure E Ω] in

theorem coe_qPow_one : (qPow w 1 : ℂ) = ((normV w : ℕ) : ℂ) := by simp

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open scoped ContDiff

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem det_unip {R : Type} [CommRing R] {r : ℕ} (x : BlockIx a r → R) : GeneralLinearGroup.det (unip x) = 1 := by
  apply Units.ext
  change (1 + nilM x).det = 1
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp only [nilM, Matrix.add_apply, Matrix.one_apply_eq, Matrix.of_apply]
    rw [dif_neg (fun h => by omega), add_zero]
  · intro i j hij
    have hij' : (j : ℕ) < i := hij
    simp only [nilM, Matrix.add_apply, Matrix.of_apply]
    rw [dif_neg (fun h => by omega), add_zero, Matrix.one_apply_ne (fun h => by rw [h] at hij'; omega)]

def opMul (χ : HChar E) : Op E a → ℂˣ
  | .fin k => chiDet a χ (finGL E a k)
  | .cpt k => chiDet a χ (infGL E a (Unitary.toUnits k))
  | .lie _ => 1

def opAdd (χ : HChar E) : Op E a → ℂ
  | .fin _ => 0
  | .cpt _ => 0
  | .lie X => dchi χ (Matrix.of X).trace

theorem act_mulChi (χ : HChar E) (o : Op E a) (φ : Sm E a) :
    act o (mulChi a χ φ) = mulChi a χ (((opMul χ o : ℂˣ) : ℂ) • act o φ + opAdd χ o • φ) := by
  cases o with
  | fin k => simp only [opAdd, zero_smul, add_zero]; exact rt_mulChi χ (finGL E a k) φ
  | cpt k => simp only [opAdd, zero_smul, add_zero]; exact rt_mulChi χ (infGL E a (Unitary.toUnits k)) φ
  | lie X => simp only [opMul, Units.val_one, one_smul]; exact lie_mulChi χ X φ

theorem isOpen_ker_chiDet (χ : HChar E) : IsOpen {k : GL (Fin a) (Af E) | chiDet a χ (finGL E a k) = 1} := by
  have h := (isOpen_ker_finIdele E (χ.1.comp (finId E)) (χ.2.1.comp (continuous_finId E))).preimage
    (GeneralLinearGroup.continuous_det (n := Fin a))
  convert h using 1
  ext k
  exact Iff.of_eq (congrArg (fun u => χ.1 u = 1) (det_finGL k))

omit [IsTotallyComplex E] in

theorem chiDet_ratGL (χ : HChar E) (γ : GL (Fin a) E) : chiDet a χ (ratGL E a γ) = 1 := by
  rw [← χ.2.2 (GeneralLinearGroup.det γ)]
  exact congrArg χ.1 (Units.ext (det_map _ γ))

omit [IsTotallyComplex E] in

theorem norm_det_le (x : Matrix (Fin a) (Fin a) (Cinf E)) {B : ℝ} (hx : ‖toL x‖ ≤ B) :
    ‖x.det‖ ≤ a.factorial * B ^ a := by
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (B ^ a) fun σ _ => ?_).trans_eq
    (by simp [Fintype.card_perm]))
  have h : ‖∏ i, x (σ i) i‖ ≤ B ^ a := by
    refine (Finset.norm_prod_le _ _).trans ((Finset.prod_le_prod (g := fun _ => B) (fun _ _ => norm_nonneg _)
      fun i _ => ?_).trans_eq (by simp))
    exact ((norm_le_pi_norm (toL x (σ i)) i).trans (norm_le_pi_norm (toL x) (σ i))).trans hx
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simpa [e] using h

theorem chiDet_growth (χ : HChar E) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖((chiDet a χ (infGL E a y) : ℂˣ) : ℂ)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, -, h⟩ := exists_bound _ (continuous_chiInf χ)
  refine ⟨C * a.factorial ^ N, a * N, fun y => ?_⟩
  have h1 := one_le_height y
  have h2 := h (GeneralLinearGroup.det y) (a.factorial * height y ^ a)
    (one_le_mul_of_one_le_of_one_le (by exact_mod_cast a.factorial_pos) (one_le_pow₀ h1))
    (norm_det_le _ (by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]))
    (by rw [← map_inv]; exact norm_det_le _ (by unfold height; linarith [norm_nonneg (toL y.val)]))
  rw [show chiDet a χ (infGL E a y) = chiInf χ (GeneralLinearGroup.det y) from congrArg χ.1 (det_infGL y)]
  exact h2.trans_eq (by rw [mul_pow, ← pow_mul, mul_assoc])

theorem Zalg_mulChi (χ : HChar E) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (mulChi a χ φ) = mulChi a χ (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Algebra.subset_adjoin ⟨τ, _, rfl⟩, cap_mulChi χ τ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

theorem IsAutForm.mulChi {φ : Sm E a} (h : IsAutForm φ) (χ : HChar E) : IsAutForm (mulChi a χ φ) where
  left γ g := by simp [h.left, chiDet_ratGL]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
      have h1 : rt E a (finGL E a k) φ = φ := hk.1
      have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
      change rt E a (finGL E a k) _ = _
      rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      (CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (CuspRep.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth g
    obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
    refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
    rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
    refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
      ((norm_nonneg _).trans (h1 y))).trans_eq ?_
    ring

theorem IsCuspForm.mulChi {φ : Sm E a} (h : IsCuspForm φ) (χ : HChar E) : IsCuspForm (mulChi a χ φ) := by
  refine ⟨h.1.mulChi χ, fun r h0 h1 _ _ μ 𝓕 hμ hF g => ?_⟩
  have e : ∀ x : BlockIx a r → Ad E, chiDet a χ (unip x * g) = chiDet a χ g := fun x => by
    rw [map_mul, show chiDet a χ (unip x) = 1 from (congrArg χ.1 (det_unip x)).trans (map_one _), one_mul]
  simp only [mulChi_apply, e]
  rw [integral_mul_const, h.2 r h0 h1 μ 𝓕 hμ hF g, zero_mul]

namespace CuspSub

variable (π π' : CuspSub E a)

def Iso : Prop := ∃ T : π.V ≃ₗ[ℂ] π'.V, ∀ o φ, T (π.op o φ) = π'.op o (T φ)

variable (E a) in

instance setoid : Setoid (CuspSub E a) where
  r := Iso
  iseqv := ⟨fun π => ⟨.refl _ _, fun _ _ => rfl⟩,
    fun ⟨T, h⟩ => ⟨T.symm, fun o φ => T.injective (by rw [h]; simp)⟩,
    fun ⟨T, h⟩ ⟨T', h'⟩ => ⟨T.trans T', fun o φ => by simp [h, h']⟩⟩

def twist (χ : HChar E) : CuspSub E a where
  V := π.V.map (mulChi a χ).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact (π.cusp φ hφ).mulChi χ
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (π.V.smul_mem _ (π.stable o φ hφ)) (π.V.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := mulChi a χ)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (mulChi a χ).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (mulChi a χ).injective h2]) fun o φ hφ => by
      have h1 : _ ∈ W.comap (mulChi a χ).toLinearMap := (act_mulChi χ o φ) ▸ hs o _ hφ
      exact (Submodule.smul_mem_iff _ (Units.ne_zero (opMul χ o))).1
        ((Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hφ)).1 h1)
    have e := Submodule.map_comap_eq_of_surjective (f := (mulChi a χ).toLinearMap) (mulChi a χ).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

def HasInfChar (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u, ∀ φ ∈ π.V, cap τ u φ = (m.map (u + ·)).prod • φ

variable {π π'}

theorem iso_cap (T : π.V ≃ₗ[ℂ] π'.V) (hT : ∀ o φ, T (π.op o φ) = π'.op o (T φ)) (τ : E →+* ℂ) (u : ℂ) (φ : π.V) :
    ∃ h : cap τ u φ.1 ∈ π.V, (T ⟨_, h⟩).1 = cap τ u (T φ).1 := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ φ : π.V, ∃ h : z φ.1 ∈ π.V, (T ⟨_, h⟩).1 = z (T φ).1}
      mul_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hy φ
        obtain ⟨h2, e2⟩ := hx ⟨_, h1⟩
        exact ⟨h2, e2.trans (congrArg x e1)⟩
      add_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hx φ
        obtain ⟨h2, e2⟩ := hy φ
        exact ⟨add_mem h1 h2, (congrArg Subtype.val (map_add T ⟨_, h1⟩ ⟨_, h2⟩)).trans (congrArg₂ (· + ·) e1 e2)⟩
      algebraMap_mem' := fun c φ => ⟨π.V.smul_mem c φ.2, congrArg Subtype.val (map_smul T c φ)⟩ }
  have hL : ∀ X, lie E a X ∈ S := fun X φ => ⟨π.stable (.lie X) _ φ.2, congrArg Subtype.val (hT (.lie X) φ)⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have : cap τ u ∈ S := by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact this φ

theorem Iso.hasInfChar (h : Iso π π') {τ : E →+* ℂ} {m : Multiset ℂ} (hm : π.HasInfChar τ m) : π'.HasInfChar τ m := by
  obtain ⟨T, hT⟩ := h
  refine ⟨hm.1, fun u φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := T.surjective ⟨φ, hφ⟩
  obtain ⟨h1, e⟩ := iso_cap T hT τ u ψ
  have e2 : (⟨_, h1⟩ : π.V) = (m.map (u + ·)).prod • ψ := Subtype.ext (hm.2 u _ ψ.2)
  rw [e2, map_smul, hψ] at e
  exact e.symm

variable (π) in

def finPart : Representation ℂ (GL (Fin a) (Af E)) π.V :=
  GlobalTheory.PRep.sub (finRep E a) π.V fun k => π.stable (.fin k)

variable (π) in

def locRep (w : HeightOneSpectrum (𝓞 E)) : Representation ℂ (GL (Fin a) (w.adicCompletion E)) π.V :=
  π.finPart.comp (locGL E a w)

variable (π) in

def IsLocComp (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)

end CuspSub

variable (E a) in

def CG : Type := Quotient (CuspSub.setoid E a)

namespace CG

def mk (π : CuspSub E a) : CG E a := Quotient.mk _ π

def HasInfChar (π : CG E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Quotient.liftOn π (·.HasInfChar τ m) fun _ _ h =>
    propext ⟨CuspSub.Iso.hasInfChar h, CuspSub.Iso.hasInfChar (Setoid.symm h)⟩

open Classical in

def infChar (π : CG E a) (τ : E →+* ℂ) : Multiset ℂ :=
  if h : ∃ m, π.HasInfChar τ m then h.choose else Multiset.replicate a 0

def IsRegAlg (π : CG E a) : Prop :=
  ∃ t : Reformulated.AlgebraicInfinityType.InfinityType E a, t.IsRegularAlgebraic ∧ ∀ τ, t.exponents τ = π.infChar τ

end CG

end GlobalTheory.CuspRep
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

def IsSmooth {h : IsPlaceOver A w} {M : Type*} [Monoid M] (f : Weil h →* M) : Prop :=
  IsOpen {σ : Ine (F := E) A | f (ineIncl h σ) = 1}

theorem IsSmooth.of_open {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    {U : Set (Ine (F := E) A)} (hU : IsOpen U) (h1 : 1 ∈ U)
    (hf : ∀ σ ∈ U, f (ineIncl h σ) = 1) : IsSmooth f :=
  Subgroup.isOpen_of_mem_nhds (f.comp (ineIncl h)).ker (g := 1)
    (Filter.mem_of_superset (hU.mem_nhds h1) hf)

theorem IsSmooth.of_le {h : IsPlaceOver A w} {M M' : Type*} [Monoid M] [Monoid M']
    {f : Weil h →* M} {g : Weil h →* M'} (hf : IsSmooth f) (hg : ∀ σ, f σ = 1 → g σ = 1) :
    IsSmooth g :=
  .of_open hf (by simp) fun _ hσ => hg _ hσ

theorem IsSmooth.of_le₂ {h : IsPlaceOver A w} {M M' M'' : Type*} [Monoid M] [Monoid M']
    [Monoid M''] {f : Weil h →* M} {f' : Weil h →* M'} {g : Weil h →* M''} (hf : IsSmooth f)
    (hf' : IsSmooth f') (hg : ∀ σ, f σ = 1 → f' σ = 1 → g σ = 1) : IsSmooth g :=
  .of_open (hf.inter hf') (by simp) fun _ hσ => hg _ hσ.1 hσ.2

structure WDRep [IsAlgClosure E Ω] (h : IsPlaceOver A w) (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] where

  ρ : Representation ℂ (Weil h) V

  N : End ℂ V
  smooth : IsSmooth ρ
  semisimple : ∀ σ, End.IsSemisimple (ρ σ)
  nilpotent : IsNilpotent N
  comm : ∀ σ, ρ σ * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)

variable [IsAlgClosure E Ω]

namespace WDRep

variable {h : IsPlaceOver A w}
variable {V V' V'' V''' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
  [AddCommGroup V'''] [Module ℂ V'''] [FiniteDimensional ℂ V''']

theorem comm_apply (a : WDRep h V) (σ : Weil h) (v : V) :
    a.ρ σ (a.N v) = ((normV w : ℕ) : ℂ) ^ deg σ • a.N (a.ρ σ v) :=
  LinearMap.congr_fun (a.comm σ) v

def sum (a : WDRep h V) (b : WDRep h V') : WDRep h (V × V') where
  ρ := a.ρ.prod b.ρ
  N := a.N.prodMap b.N
  smooth := a.smooth.of_le₂ b.smooth fun σ h1 h2 => by
    show (a.ρ σ).prodMap (b.ρ σ) = 1
    rw [h1, h2]; exact LinearMap.prodMap_one
  semisimple σ := isSemisimple_prodMap (a.semisimple σ) (b.semisimple σ)
  nilpotent := by
    have h1 : ∀ n : ℕ, (a.N.prodMap b.N : End ℂ (V × V')) ^ n = (a.N ^ n).prodMap (b.N ^ n) :=
      fun n => (map_pow (LinearMap.prodMapRingHom ℂ V V') (a.N, b.N) n).symm
    obtain ⟨m, hm⟩ := a.nilpotent
    obtain ⟨n, hn⟩ := b.nilpotent
    exact ⟨m + n, by
      rw [h1, pow_add, hm, zero_mul, pow_add, hn, mul_zero, LinearMap.prodMap_zero]⟩
  comm σ := LinearMap.ext fun v => Prod.ext (a.comm_apply σ v.1) (b.comm_apply σ v.2)

end WDRep

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.AdelicUnitaryTop

section Adeles

variable (F : Type) [Field F] [NumberField F]

theorem properSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.glint_finite_residueField v

theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  Valued.integer.properSpace_iff_compactSpace_integer.1 (properSpace_adicCompletion F v)

theorem locallyCompact_finiteAdele : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  haveI := properSpace_adicCompletion F
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (.of_forall fun v => isCompact_iff_compactSpace.2 (compactSpace_adicCompletionIntegers F v))

theorem secondCountable_finiteAdele : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI := properSpace_adicCompletion F
  haveI := countable_heightOneSpectrum F
  exact secondCountable_restrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun _ ↦ Valued.isOpen_valuationSubring _

theorem locallyCompact_adele : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  haveI := locallyCompact_finiteAdele F
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem secondCountable_adele : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  haveI := secondCountable_finiteAdele F
  haveI := secondCountable_infiniteAdele F
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Adeles

end GlobalTheory.AdelicUnitaryTop
end

section
-- module Solutions.AlpoGe.Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.OL_finite _root_.Formalism.BasicNotions.Examples₂.LB.OL_frac _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Examples₂.LB.instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations Module

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace Br

section Gen

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

variable [IsDomain O]

instance finKw : FiniteDimensional ℚ_[l] ↥Bw.Kw.1 := Bw.Kw.2

end Gen

end Br

end Formalism.MainNotions.N
end
end
end
end

section
-- module Solutions.AlpoGe.Formalism.LocalToGlobal.GlobalTheory.HLatOps
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Module NumberField ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.HLatOps

open Formalism.BasicNotions

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

@[reducible] def withL (A : HLat K) (L' : Submodule (𝓞 K) A.V) : HLat K := { A with L := L' }

end Defs

end Formalism.L2.GlobalTheoryTheory.HLatOps
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolEmb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infEmb_unique (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ)
    (h' : IsInfEmb τ θ') : θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

end GlobalTheory.Mem.VolEmb
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArchAdeleTensorEquivComplexCmType
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolInfIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bijective_fam (σ : E →ₐ[F] E) {I : Type} (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ))
    (h : IsCMExt F E σ) (hτ : IsCMFam τ) (hθ : ∀ i, IsInfEmb (τ i) (θ i)) :
    Function.Bijective (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ : E →+* ℂ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := by
    intro φ
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by
        show InfinitePlace.mk (τ j) = InfinitePlace.mk (τ i)
        rw [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · refine absurd ⟨i, ?_⟩ hn
        rw [← e]
        ext x
        simp
  have hb := GlobalTheory.InfAdeleCM.bijective c h2 hc hc' θ0
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)) (Set.range τ) hΨ
  have hinj : Function.Injective τ := fun i j hij => hτ.1 (by
    show InfinitePlace.mk (τ i) = InfinitePlace.mk (τ j)
    rw [hij])
  let u : I ≃ Set.range τ := Equiv.ofInjective τ hinj
  have he : (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) =
      (Equiv.arrowCongr u.symm (Equiv.refl ℂ)) ∘ (fun (z : Ainf F ⊗[F] E) (φ : Set.range τ) => θ0 φ.1 z) := by
    funext z i
    rw [GlobalTheory.Mem.VolEmb.infEmb_unique (τ i) (θ i) (θ0 (τ i)) (hθ i) ⟨h0 _, h0' _⟩]
    rfl
  rw [he]
  exact (Equiv.bijective _).comp hb

theorem infEmb_sigR (σ : E →ₐ[F] E) (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (h : IsCMExt F E σ) (hθ : IsInfEmb τ θ) (z : Ainf F ⊗[F] E) :
    θ (sigR (Ainf F) σ z) = star (θ z) := by
  obtain ⟨hF, -, -, hσ⟩ := h
  have hθ' := GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show θ (a ⊗ₜ[F] σ x) = starRingEnd ℂ _
    rw [hθ', hθ', map_mul, GlobalTheory.InfAdeleCM.conj_ext, hσ]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, star_add]

theorem exists_infAdele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → ∃ e : (Ainf F ⊗[F] E) ≃+* (I → ℂ), (∀ x i, e x i = θ i x) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x i, e (sigR (Ainf F) σ x) i = star (e x i) := by
  intro F E _ _ _ _ _ σ I _ τ θ h hτ hθ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e0.secondCountableTopology
  have hb : Function.Bijective (Pi.ringHom θ : Ainf F ⊗[F] E →+* (I → ℂ)) := bijective_fam σ τ θ h hτ hθ
  let e : (Ainf F ⊗[F] E) ≃+* (I → ℂ) := RingEquiv.ofBijective _ hb
  have hc : Continuous e := continuous_pi fun i =>
    IsModuleTopology.continuous_of_ringHom (R := Ainf F) (θ i) (hθ i).2
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective hc
  refine ⟨e, fun _ _ => rfl, hc, ?_, fun x i => infEmb_sigR σ (τ i) (θ i) h (hθ i) x⟩
  exact (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous

end GlobalTheory.Mem.VolInfIso
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.Host
open Filter Topology Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

namespace GlobalTheory.HeckeTensorRead

theorem exists_infinite_equiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ j : (Ainf F ⊗[F] E) ≃+* InfiniteAdeleRing E, Continuous j ∧ Continuous j.symm ∧
      ∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x := by
  haveI := h.1
  haveI := h.2.1
  choose θ h1 h2 using fun w : InfinitePlace E => GlobalTheory.InfAdeleCM.exists_hom (F := F) w.embedding
  obtain ⟨e, he, hc, hc', -⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ (InfinitePlace E) (fun w => w.embedding) θ h
    (by
      unfold GlobalTheory.Mem.Vol.IsCMFam
      simp only [InfinitePlace.mk_embedding]
      exact Function.bijective_id) (fun w => ⟨h1 w, h2 w⟩)
  let p : InfiniteAdeleRing E ≃+* (InfinitePlace E → ℂ) :=
    RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  have hp : Continuous p := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  have hp' : Continuous p.symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.continuous.comp
      (continuous_apply w)
  refine ⟨e.trans p.symm, hp'.comp hc, hc'.comp hp, fun x => ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
  funext w
  rw [he, h1]
  exact (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)).symm

end GlobalTheory.HeckeTensorRead
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
open scoped TensorProduct

namespace GlobalTheory.UnitaryHeckeBaseChange

section Iso

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toAdele : AE F E →+* AdeleRing (𝓞 E) E :=
  letI : Algebra F (AdeleRing (𝓞 E) E) :=
    ((algebraMap E (AdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  (Algebra.TensorProduct.productMap
    (⟨adeleMap F E, fun x => adeleMap_algebraMap F E x⟩ : AF F →ₐ[F] AdeleRing (𝓞 E) E)
    (⟨algebraMap E _, fun _ => rfl⟩ : E →ₐ[F] AdeleRing (𝓞 E) E)).toRingHom

variable {F E}

theorem toAdele_tmul (a : AF F) (x : E) :
    toAdele F E (a ⊗ₜ[F] x) = adeleMap F E a * algebraMap E _ x := rfl

theorem toAdele_incA (x : E) : toAdele F E (incA F E x) = algebraMap E _ x := by
  change toAdele F E ((1 : AF F) ⊗ₜ[F] x) = _
  rw [toAdele_tmul, map_one, one_mul]

theorem toAdele_algebraMap (a : AF F) : toAdele F E (algebraMap (AF F) (AE F E) a) = adeleMap F E a := by
  change toAdele F E (a ⊗ₜ[F] (1 : E)) = _
  rw [toAdele_tmul, map_one, mul_one]

variable (F E)

theorem continuous_toAdele : Continuous (toAdele F E) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (toAdele F E) ?_
  exact (continuous_adeleMap F E).congr fun a => (toAdele_algebraMap a).symm

theorem continuous_infiniteAdeleMap : Continuous (infiniteAdeleMap F E) :=
  continuous_fst.comp ((continuous_adeleMap F E).comp (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 F) F)))

theorem exists_finite : ∃ ι : Af F ⊗[F] E →+* FiniteAdeleRing (𝓞 E) E, Function.Bijective ι ∧
    (∀ z, (toAdele F E z).2 = ι (finPart F E z)) ∧
    ∀ y, y ∈ intAE F E ↔ ∀ Q, ι y Q ∈ Q.adicCompletionIntegers E := by
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd F E
  let c := Algebra.TensorProduct.comm F (Af F) E
  refine ⟨ι.comp c.toRingEquiv.toRingHom, Function.Bijective.comp (g := ι)
    ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩ c.bijective,
    fun z => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
    | tmul a x =>
      change _ = ι (x ⊗ₜ[F] a.2)
      rw [toAdele_tmul, hι, mul_comm]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = _ * GlobalTheory.AdeleBaseChange.locMap F Q _
      rw [GlobalTheory.CharTransport.locMap_eq]
      rfl
  · have : intAE F E ≤ (Formalism.L2.DIV.RInt F E).toAddSubgroup.comap c.toRingEquiv.toRingHom.toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, x, rfl⟩
      exact Formalism.UG.P.levelaf_tmul_mem x ha
    exact GlobalTheory.AdeleBaseChange.map_mem_int hι (this hy)
  · have hz := GlobalTheory.AdeleBaseChange.mem_int_of_map hι (y := c y) hy
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg hz
    have : y = ∑ j, r j ⊗ₜ[F] (g j : E) := by
      apply c.injective
      rw [map_sum]
      exact e
    rw [this]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨r j, hr j, g j, rfl⟩

variable {F E}

theorem bijective_toAdele {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Function.Bijective (toAdele F E) := by
  obtain ⟨ι, hb, h1, -⟩ := exists_finite F E
  obtain ⟨j, hjc, -, hj⟩ := GlobalTheory.HeckeTensorRead.exists_infinite_equiv F E σ h
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  have hj1 : ∀ a : Ainf F, j (a ⊗ₜ[F] (1 : E)) = infiniteAdeleMap F E a := by
    have hc : Continuous fun a : Ainf F => j (a • (1 : Ainf F ⊗[F] E)) :=
      hjc.comp (f := fun a : Ainf F => a • (1 : Ainf F ⊗[F] E)) (by fun_prop)
    have := (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hc (continuous_infiniteAdeleMap F E)
      (funext fun k => by
        change j (algebraMap F (Ainf F) k • (1 : Ainf F ⊗[F] E)) = infiniteAdeleMap F E (algebraMap F _ k)
        rw [algebraMap_smul, Algebra.TensorProduct.one_def, ← TensorProduct.tmul_smul, hj,
          ← Algebra.algebraMap_eq_smul_one]
        exact (congrArg Prod.fst (adeleMap_algebraMap F E k)).symm)
    intro a
    rw [← congrFun this a, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : ∀ z, (toAdele F E z).1 = j (s z).1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, s.map_zero]; exact j.map_zero.symm
    | add x y hx hy =>
      rw [RingHom.map_add, s.map_add]
      exact (congrArg₂ (· + ·) hx hy).trans (j.map_add _ _).symm
    | tmul a x =>
      rw [(hs _).1]
      change _ = j (a.1 ⊗ₜ[F] x)
      have : (a.1 ⊗ₜ[F] x : Ainf F ⊗[F] E) = (a.1 ⊗ₜ[F] 1) * (1 ⊗ₜ[F] x) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, hj, hj1]
      rfl
  have e : ⇑(toAdele F E) = Prod.map j ι ∘ s := funext fun z =>
    Prod.ext (h2 z) ((h1 z).trans (congrArg ι (hs z).2.symm))
  rw [e]
  exact (j.bijective.prodMap hb).comp s.bijective

def adeleEquiv {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : AE F E ≃+* AdeleRing (𝓞 E) E :=
  RingEquiv.ofBijective (toAdele F E) (bijective_toAdele h)

theorem continuous_adeleEquiv_symm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Continuous (adeleEquiv h).symm := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e0.secondCountableTopology
  have hc : Continuous (adeleEquiv h) := continuous_toAdele F E
  have ho : IsOpenMap (adeleEquiv h) :=
    AddMonoidHom.isOpenMap_of_sigmaCompact (adeleEquiv h).toAddEquiv.toAddMonoidHom (adeleEquiv h).surjective hc
  exact ((adeleEquiv h).toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous

end Iso

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCMExtension_of (h : IsCMExt F E σ) : IsCMExtension F E :=
  ⟨h.1, h.2.1, { finrank_eq_two' := h.2.2.1 }⟩

theorem isCMExt_iff (σ : E →ₐ[F] E) :
    IsCMExt F E σ ↔ ∃ _ : IsCMExtension F E, σ = (conj F E : E →ₐ[F] E) := by
  constructor
  · intro h
    haveI := isCMExtension_of h
    refine ⟨this, AlgHom.ext fun x => ?_⟩
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((h.2.2.2 τ x).trans (embedding_conj F E τ x).symm)
  · rintro ⟨h, rfl⟩
    exact ⟨h.totallyReal, h.totallyComplex, h.quadratic.finrank_eq_two, embedding_conj F E⟩

end CM

end GlobalTheory.UnitaryHeckeBaseChange
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ'
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryHeckeBaseChange
open scoped TensorProduct Topology HeckeCharacterZeroLocus.ThmBIn

namespace GlobalTheory.GalOfCusp

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem isCMExt_real : HeckeCharacterZeroLocus.ThmBIn.IsCMExt (maximalRealSubfield E) E
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E : E →ₐ[maximalRealSubfield E] E) :=
  (isCMExt_iff _).2 ⟨inferInstance, rfl⟩

def adeleNorm : AdeleRing (𝓞 E) E →* AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) :=
  (Algebra.norm (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))).comp
    (adeleEquiv (isCMExt_real E)).symm.toRingHom.toMonoidHom

theorem continuous_adeleNorm : Continuous (adeleNorm E) := by
  classical
  refine Continuous.comp (g := Algebra.norm (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))) ?_
    (continuous_adeleEquiv_symm (isCMExt_real E))
  haveI : IsModuleTopology (HeckeCharacterZeroLocus.ThmBIn.AF (maximalRealSubfield E)) (HeckeCharacterZeroLocus.ThmBIn.AE (maximalRealSubfield E) E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.ThmBIn.AF (maximalRealSubfield E))
    (Module.finBasis (maximalRealSubfield E) E)
  refine (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap).matrix_det.congr fun x => ?_
  exact (Algebra.norm_eq_matrix_det b x).symm

theorem adeleNorm_algebraMap (x : E) :
    adeleNorm E (algebraMap E _ x) = algebraMap _ _ (Algebra.norm (maximalRealSubfield E) x) := by
  have h : (adeleEquiv (isCMExt_real E)).symm (algebraMap E _ x) = 1 ⊗ₜ x :=
    (adeleEquiv (isCMExt_real E)).symm_apply_eq.2 (toAdele_incA x).symm
  change Algebra.norm _ ((adeleEquiv (isCMExt_real E)).symm (algebraMap E _ x)) = _
  rw [h, Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  ext y
  simp

def ideleNorm : Ideles E →* Ideles (maximalRealSubfield E) := Units.map (adeleNorm E)

def compNorm : HChar (maximalRealSubfield E) →* HChar E where
  toFun χ := ⟨χ.1.comp (ideleNorm E), χ.2.1.comp (Continuous.units_map _ (continuous_adeleNorm E)), fun k => by
    rw [← χ.2.2 (Units.map (Algebra.norm (maximalRealSubfield E)) k)]
    exact congrArg χ.1 (Units.ext (adeleNorm_algebraMap E k))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end GlobalTheory.GalOfCusp
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

def DualIsConjBy (π : CuspSub L a) (ψ : HChar L) : Prop := Paired (π.twist ψ⁻¹) π conjOp

structure PolarizedPair (π : CuspSub L a) (χ : HChar (maximalRealSubfield L)) : Prop where
  sign : ∀ v : InfinitePlace (maximalRealSubfield L), χ.locInf v (-1) = (-1) ^ a
  dual : DualIsConjBy π (GlobalTheory.GalOfCusp.compNorm L χ)

end GlobalTheory.ContraPair

end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

namespace GlobalTheory.GLq

open Polynomial Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def tl (a : ℕ) {n : ℕ} (M : Mt g n) : Mt g a := fun i j => entN M i j

def br (a b : ℕ) {n : ℕ} (M : Mt g n) : Mt g b := fun i j => entN M (a + i) (a + j)

def res (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) : Gn g a → Gn g b → ℂ := fun h₁ h₂ =>
  ((g : ℂ) ^ (a * b))⁻¹ * ∑ x : Gn g n,
    if InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b) then χ x else 0

def IsCusp {d : ℕ} (χ : Gn g d → ℂ) : Prop :=
  0 < d ∧ IsIrr χ ∧ ∀ a, 0 < a → a < d → res a (d - a) χ 1 1 = 0

end GlobalTheory.GLq
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL

section General

variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]

section Top

variable [TopologicalSpace G]

variable [IsTopologicalGroup G]

def contra (ρ : Representation F G V) : Representation F G (smoothPart ρ.dual) := smoothRep ρ.dual

@[simp] theorem contra_apply (ρ : Representation F G V) (g : G) (l : smoothPart ρ.dual) (v : V) :
    (contra ρ g l : Module.Dual F V) v = (l : Module.Dual F V) (ρ g⁻¹ v) := rfl

end Top

end General

end GlobalTheory.SmGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.SmGL

section Local

open Matrix

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable {k}

abbrev IndSp (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) : Type :=
  smoothPart (ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)))

def parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (GL n k) (IndSp e ρ) :=
  smInd (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e))

@[simp] theorem parInd_apply (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (g x : GL n k)
    (f : IndSp e ρ) :
    (parInd e ρ g f).1.1 x = f.1.1 (x * g) := rfl

abbrev IndSpLower (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) : Type :=
  smoothPart (ind (parabLower k e) ((twist ρ (deltaHalf k m)⁻¹).comp (leviProjLower k e)))

def parIndLower (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Representation ℂ (GL n k) (IndSpLower e ρ) :=
  smInd (parabLower k e) ((twist ρ (deltaHalf k m)⁻¹).comp (leviProjLower k e))

@[simp] theorem parIndLower_apply (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    (g x : GL n k) (f : IndSpLower e ρ) : (parIndLower e ρ g f).1.1 x = f.1.1 (x * g) := rfl

def multiProd (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) :=
  parInd e (piTensor π)

def IsCuspSupport (π : Representation ℂ (GL n k) V) {s : ℕ} (d : Fin s → ℕ) {X : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) : Prop :=
  π.IsIrreducible ∧ (∀ a, 0 < d a ∧ (σ a).IsIrreducible ∧ IsCuspidal (σ a)) ∧
    ∃ e : (Σ a, Fin (d a)) ≃ n, IsSubquotient π (multiProd e σ)

end Local

end GlobalTheory.SmGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Topology Filter
open scoped TensorProduct

namespace GlobalTheory.LocalData

section Completion

variable {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))

theorem isLocalField : letI := complRel p; IsNonarchimedeanLocalField (p.adicCompletion F) := by
  letI := complRel p
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F p
  haveI : IsValuativeTopology (p.adicCompletion F) :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))) Valued.mem_nhds_zero
  haveI : ValuativeRel.IsNontrivial (p.adicCompletion F) := by
    rw [ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))]
    infer_instance
  exact {}

end Completion

end GlobalTheory.LocalData

end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.LocGL

section General

variable {G H M V W X : Type} [Group G] [Group H] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

def subrepTwist (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    have := S.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
    simpa [smul_smul] using this⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_twist {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (χ : G →* ℂˣ) :
    (twist ρ χ).IsIrreducible := (subrepTwist ρ χ).isSimpleOrder_iff.2 h

end General

section Classes

variable {G : Type} [Group G] [TopologicalSpace G]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable [IsTopologicalGroup G]

def irrTwist (σ : IrrRep G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) : IrrRep G :=
  ⟨σ.V, twist σ.ρ χ, isSmooth_twist σ.smooth hχ, isIrreducible_twist σ.irr χ⟩

def clTwist (c : IrrCl G) (χ : G →* ℂˣ) (hχ : IsSmoothChar χ) : IrrCl G := (irrTwist c.rep χ hχ).cl

end Classes

end GlobalTheory.LocGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

namespace IrrGL

def tw (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : IrrGL k :=
  ⟨x.1, clTwist x.2 (detChar _ χ) hχ.detChar⟩

def nu (x : IrrGL k) (s : ℂ) : IrrGL k := x.tw (absPow k s) (isSmoothChar_absPow s)

@[simp] theorem tw_fst (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : (x.tw χ hχ).1 = x.1 := rfl

@[simp] theorem nu_fst (x : IrrGL k) (s : ℂ) : (x.nu s).1 = x.1 := rfl

end IrrGL

def prodIrr {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) :
    Representation ℂ (GL (Fin N) k) (IndSp (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) :=
  multiProd (stdBlocks (fun a => (x a).1) hd) fun a => (x a).rep

def HasSupport {n : Type} [Fintype n] [DecidableEq n] (π : Representation ℂ (GL n k) V) (s : Multiset (IrrGL k)) : Prop :=
  ∃ (h : ℕ) (x : Fin h → IrrGL k), Finset.univ.val.map x = s ∧ IsCuspSupport π (fun a => (x a).1) fun a => (x a).rep

end GlobalTheory.LocGL

namespace GlobalTheory.SmGL.Segment

open GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def first (Δ : Segment k) : IrrGL k := ⟨Δ.d, Δ.start⟩

def term (Δ : Segment k) (a : Fin Δ.len) : IrrGL k := Δ.first.nu (a : ℕ)

def carrier (Δ : Segment k) : Set (IrrGL k) := Set.range Δ.term

def Linked (Δ Δ' : Segment k) : Prop :=
  (∃ Γ : Segment k, Γ.carrier = Δ.carrier ∪ Δ'.carrier) ∧ ¬ Δ.carrier ⊆ Δ'.carrier ∧ ¬ Δ'.carrier ⊆ Δ.carrier

def Precedes (Δ Δ' : Segment k) : Prop := Linked Δ Δ' ∧ ∃ j : ℕ, 0 < j ∧ Δ'.first = Δ.first.nu j

end GlobalTheory.SmGL.Segment

namespace GlobalTheory.LocGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N h : ℕ}

def IsOrderedForm (Δ : Fin h → Segment k) (𝔪 : Multiset (Segment k)) : Prop :=
  Finset.univ.val.map Δ = 𝔪 ∧ ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)

def IsLSeg (Δ : Segment k) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ hd : ∑ a, (Δ.term a).1 = N, IsCosocle π (prodIrr Δ.term hd)

def LFactors (𝔪 : Multiset (Segment k)) (x : Fin h → IrrGL k) : Prop :=
  ∃ Δ : Fin h → Segment k, IsOrderedForm Δ 𝔪 ∧ ∀ i, IsLSeg (Δ i) (x i).rep

def IsL (𝔪 : Multiset (Segment k)) (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x ∧ IsCosocle π (prodIrr x hd)

end GlobalTheory.LocGL
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host

namespace GlobalTheory.HeckeGal

section Defs

variable (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

abbrev Gab : Type := TopologicalAbelianization (G E Ω)

def toAb : G E Ω →* Gab E Ω := QuotientGroup.mk' _

def infConn : Subgroup (Ideles E) :=
  (Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ).map
    (Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)))

variable {E Ω}

structure IsGlobalArtin (art : Ideles E →* Gab E Ω) : Prop where

  quot : IsOpenQuotientMap art

  ker : art.ker = ((diagUnits E).range ⊔ infConn E).topologicalClosure

  ine : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ g : Gab E Ω,
    (∃ x, IsUnitAt v x ∧ art (localIdele E v x) = g) ↔ ∃ σ ∈ Ine (F := E) A, toAb E Ω σ = g

  frob : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ g : Gab E Ω,
    (∃ x, IsUnifAt v x ∧ art (localIdele E v x) = g) ↔
      ∃ σ : G E Ω, IsFrob (F := E) A (normV v) σ ∧ toAb E Ω σ⁻¹ = g

  dec : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v →
    (art.comp (localIdele E v)).range.topologicalClosure = (Dec (F := E) A).map (toAb E Ω)

end Defs

end GlobalTheory.HeckeGal

end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalOfCusp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def algNorm {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    IrrGL (w.adicCompletion E) :=
  (IrrGL.of σ.ρ σ.smooth σ.irred).nu (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)

end GlobalTheory.GalOfCusp
end
end


