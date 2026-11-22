-- Prove2me | Definitions.Def_AlpoGeB008
-- name    : AlpoGeB008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T16:40:28.718126+00:00
-- url     : https://prove2.me/theorems/787cff41-f3c5-4624-926b-63b5450c5f1e
-- title:
--   Definitions bundle AlpoGeB008 of the alpo.ge GRH release, first cut (Row0b, IsRecT)
-- statement:
--   A definitions bundle of the first cut of L. Alpöge's Lean proof of GRH for Dirichlet $L$-functions (released 20 November 2026, written with Claude; announcement [alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)). The declarations and their proofs are the release's, carved mechanically for this platform: the carve reorders them, restates the namespaces and `open`s each needs, and writes a few declarations from their elaborated form. Two patches are recorded in the carve: an anonymous instance is given its original generated name, and an additive structure that a `to_additive` attribute names is restored beside the structure that names it. The release builds with `maxHeartbeats 4000000` and `maxSynthPendingDepth 3` as project options (and `synthInstance.maxHeartbeats 400000` for its local and global field libraries); since the verifier sets none of these, each carved module section states them as `set_option` lines. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   The first cut publishes the two inputs from which the release concludes its main theorem: `AlpoGe.galoisLocalGlobalStrong_recParameter` (the release's `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) and `AlpoGe.everyCharacter_of_row` (the release's `UpperTheory.FinalTheorems.everyCharacter_of_row`). These bundles hold the definitions their statements need, with the theorems those definitions use.
--
--   **Contents.** It holds 25 declarations of the release's Lean: 16 definitions, 4 inductive types or structures, 0 instances and 5 theorems. The definitions and types are `GlobalTheory.WeilDeligne.IsWDOf`, `GlobalTheory.WeilDeligne.IsWDOfWith`, `GlobalTheory.WeilDeligne.WD.inePol`, `GlobalTheory.WeilDeligne.WD.lpOfChar`, `GlobalTheory.WeilDeligne.inePart`, `GlobalTheory.WeilDeligne.toEndC`, `GlobalTheory.WeilDeligne.wdMat`, `GlobalTheory.WeilDeligne.wdOf`, `LocalGlobalAboveLAlt.Triv`, `UpperTheory.GalS.TmW`, `UpperTheory.GalStar.AboveB`, `UpperTheory.GalStar.AwayB`, `UpperTheory.GalStar.PropsB`, `UpperTheory.GalStar.RecNotion`, `UpperTheory.GalStar.Row0b`, `UpperTheory.GalStar.Sqf`, `UpperTheory.GalStar.Tor`, `UpperTheory.Zero.LLC.IsRecT`, `UpperTheory.Zero.LLC.LawsT`, `UpperTheory.Zero.LLC.TypeLaw`. It imports the bundles `Def_AlpoGeB003`, `Def_AlpoGeB006`, `Def_AlpoGeB007`.
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc)

import Mathlib
import Definitions.Def_AlpoGeB003
import Definitions.Def_AlpoGeB006
import Definitions.Def_AlpoGeB007

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.Pst.finiteDimensional_wdSpace _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.isEmpty_real _root_.ReciprocityTheory.ChartRestriction.G.Out.Inh.geomConn_id _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

variable [IsAlgClosure E Ω]

namespace WD

variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

variable (h) in

def lpOfChar (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : WD h :=
  mk (WDRep.ofChars h (ι := Fin 1) (fun _ => χ) fun _ => hχ)

open Classical in

def inePol (x : WD h) (σ : G E Ω) : ℂ[X] := if hσ : σ ∈ Weil h then charPol x ⟨σ, hσ⟩ else 1

end WD

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.Pst.finiteDimensional_wdSpace _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.isEmpty_real _root_.ReciprocityTheory.ChartRestriction.G.Out.Inh.geomConn_id
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.GlobalTheory.Pst.lpDim_trivWD _root_.GlobalTheory.Pst.wdRho_mk
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

def inePart {φ : Weil h} (hφ : deg φ = 1) (g : Weil h) : Ine (F := E) A :=
  ⟨((φ ^ deg g)⁻¹ * g : Weil h), deg_eq_zero_iff.mp (by simp [hφ])⟩

@[simp] theorem ineIncl_inePart {φ : Weil h} (hφ : deg φ = 1) (g : Weil h) :
    ineIncl h (inePart hφ g) = (φ ^ deg g)⁻¹ * g := rfl

@[simp] theorem inePart_zpow_mul {φ : Weil h} (hφ : deg φ = 1) (k : ℤ) (σ : Ine (F := E) A) :
    inePart hφ (φ ^ k * ineIncl h σ) = σ :=
  Subgroup.inclusion_injective (Ine_le_Weil h) (by
    show ineIncl h _ = ineIncl h _
    simp [hφ])

@[simp] theorem inePart_ineIncl {φ : Weil h} (hφ : deg φ = 1) (σ : Ine (F := E) A) :
    inePart hφ (ineIncl h σ) = σ := by
  simpa using inePart_zpow_mul hφ 0 σ

def wdMat (t : Ine (F := E) A →* Multiplicative ℤ_[l]) {φ : Weil h} (hφ : deg φ = 1)
    (r : G E Ω →* GL n (Qbar l)) (N : Matrix n n (Qbar l)) (g : Weil h) : Matrix n n (Qbar l) :=
  (r g : Matrix n n (Qbar l)) * exp ((-tval t (inePart hφ g)) • N)

def toEndC (ι : Qbar l ≃+* ℂ) : Matrix n n (Qbar l) →+* End ℂ (n → ℂ) :=
  ((Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] End ℂ (n → ℂ)) :
    Matrix n n ℂ →+* End ℂ (n → ℂ)).comp ι.toRingHom.mapMatrix

section Monodromy

variable {t t' : Ine (F := E) A →* Multiplicative ℤ_[l]} {r : G E Ω →* GL n (Qbar l)}
  {N N' : Matrix n n (Qbar l)} {φ φ' : Weil h}

@[simp] theorem wdMat_zero (hφ : deg φ = 1) (g : Weil h) :
    wdMat t hφ r 0 g = (r g : Matrix n n (Qbar l)) := by simp [wdMat]

end Monodromy

def IsWDOfWith (t : Ine (F := E) A →* Multiplicative ℤ_[l]) {φ : Weil h} (hφ : deg φ = 1)
    (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) (x : WD h) : Prop :=
  ∃ (N : Matrix n n (Qbar l)) (a : WDRep h (n → ℂ)), IsMonodromy t r N ∧
    IsFrobSS (fun g => toEndC ι (wdMat t hφ r N g)) (toEndC ι N) a ∧ WD.mk a = x

def IsWDOf (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) (x : WD h) : Prop :=
  ∃ t : Ine (F := E) A →* Multiplicative ℤ_[l], IsTameChar t ∧
    ∃ (φ : Weil h) (hφ : deg φ = 1), IsWDOfWith t hφ ι r x

variable (h) in
open Classical in

def wdOf (_hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) :
    WD h :=
  if H : ∃ x : WD h, IsWDOf ι r x then H.choose else WD.mk (WDRep.diag h fun _ : n => 1)

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.CrisTheta
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAcris0Acris _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.Per.instAwayAinfCastAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.isEmpty_real _root_.ReciprocityTheory.ChartRestriction.G.Out.Inh.geomConn_id _root_.ReciprocityTheory.Gal.continuousConstSMul_of_discrete _root_.ReciprocityTheory.Gal.continuousConstSMul_quotient _root_.Reformulated.AutPerF.Ainf.charZero_of_charZero _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.Tilt.valuationRing _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.tateModule.smul _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.Reformulated.AutPerF.Ainf.theta_xi _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap _root_.Reformulated.AutPerF.BdRPlus.map_algebraMap_ainf _root_.Reformulated.AutPerF.BdRPlus.theta_algebraMap_ainf _root_.Reformulated.AutPerF.Tilt.untilt_zero
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]

namespace AinfInv

@[simp] theorem gamma_one (x : AinfInv p R) : gamma 1 x = x := by simp [gamma]

end AinfInv

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.isEmpty_real _root_.ReciprocityTheory.ChartRestriction.G.Out.Inh.geomConn_id
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst

namespace LocalGlobalAboveLAlt

section Defs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def Triv (y : WD h) (g : ↥(Weil h)) : Prop := y.charPol g = (X - 1) ^ y.lpDim

end Defs

end LocalGlobalAboveLAlt
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConj
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def TmW (y : WD h) : Prop :=
  ∀ σ : G E Ω, (∀ z : Ω, z ≠ 0 → A.valuation (σ z / z - 1) < 1) → y.inePol σ = (X - 1) ^ y.lpDim

end Local

end UpperTheory.GalS
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjAlt
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalStar

open UpperTheory.GalS (TmW)

abbrev RecNotion : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), (IrrGL (w.adicCompletion E) → WD h) → Prop

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def Tor (y : WD h) : Prop := ∀ s t : ↥(Weil h), LocalGlobalAboveLAlt.Triv y ⁅s, t⁆

def Sqf (y : WD h) : Prop :=
  ∀ γ ∈ Ine (F := E) A, ((Ine (F := E) A : Subgroup (G E Ω)) : Set (G E Ω)) ⊆
      closure ((Subgroup.closure (insert γ {σ : G E Ω | ∀ z : Ω, z ≠ 0 → A.valuation (σ z / z - 1) < 1}) : Subgroup (G E Ω)) :
        Set (G E Ω)) →
    ∀ z : ℂ, 2 ≤ (y.inePol γ).rootMultiplicity z → z ^ (normV w - 1) = 1

end Local

end UpperTheory.GalStar
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalStar

open UpperTheory.GalS (TmW)

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure AwayB (x y : WD h) : Prop where
  dim : x.lpDim = y.lpDim

  tor : Tor y → y.mono0 → x = y

  tame0 : IsQpBig w y.lpDim → TmW y → Sqf y → y.mono0 → x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g

end Local

variable (Rc : RecNotion) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
  [IsAlgClosure E Ω] [IsCMField E]

structure AboveB (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  nice : ∀ σ, π.IsLocComp w σ → ∀ rc, Rc h rc → ((IsQpBig w a ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) → (rc (algNorm σ)).mono0 →
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    (∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)) ∧
    AwayB (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

structure PropsB (π : CuspSub E a) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), Rc h rc → ∀ σ, π.IsLocComp w σ → AwayB (wdOf h hl ι r) (rc (algNorm σ))
  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z
  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), AboveB Rc π ι r HT P h Bw hj

def Row0b : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), PropsB Rc π ι r wt HT

end UpperTheory.GalStar
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.ReciprocityTheory.ChartRestriction.G.FD.TraceIntegralBasis.isEmpty_real _root_.ReciprocityTheory.ChartRestriction.G.Out.Inh.geomConn_id
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

variable (h) in

def TypeLaw (rc : IrrGL (w.adicCompletion E) → WD h) : Prop :=
  ∀ (E' : Type) [Field E'] [NumberField E'] [Algebra E E'] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w'),
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      (rc (cls σ)).mono0 ∧
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))

structure LawsT (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (rc : IrrGL (w.adicCompletion E) → WD h) : Prop where
  dim : ∀ x, (rc x).lpDim = x.1
  one : ∀ χ hχ, rc (.ofChar χ hχ) = WD.lpOfChar h (χ.comp a) (ha.smooth hχ)
  langlands : ∀ (l : List (Segment (w.adicCompletion E))) (x : IrrGL (w.adicCompletion E)),
    IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep → rc x = segSum rc l
  cusp : ∀ x, x.IsCusp → IsIrrWD (rc x)
  nu : ∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s
  absCentral : ∀ (x : IrrGL (w.adicCompletion E)) ω, HasCentralChar x.rep ω →
    ∀ σ, ‖((rc x).eig σ).prod‖ = ‖(ω (a σ) : ℂ)‖
  twist : ∀ x χ hχ, Good x → rc (x.tw χ hχ) = (rc x).lpChar (rc (.ofChar χ hχ))
  central : ∀ (x : IrrGL (w.adicCompletion E)) ω, Good x → HasCentralChar x.rep ω →
    ∀ σ, ((rc x).eig σ).prod = (ω (a σ) : ℂ)
  dual : ∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w.adicCompletion E))), Good (cls π) →
    Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc (cls π') = (rc (cls π)).lpDual
  inj : ∀ x y, Good y → rc x = rc y → x = y
  depth : ∀ x, Good x → GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ → IsTameWD (rc x)
  type : TypeLaw h rc

variable (h) in

def IsRecT (rc : IrrGL (w.adicCompletion E) → WD h) : Prop := ∃ a ha, LawsT (h := h) a ha rc

end UpperTheory.Zero.LLC

end
end


