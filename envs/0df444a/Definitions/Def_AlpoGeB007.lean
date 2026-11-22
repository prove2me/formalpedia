-- Prove2me | Definitions.Def_AlpoGeB007
-- name    : AlpoGeB007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T16:30:21.22043+00:00
-- url     : https://prove2.me/theorems/6a4be842-f86f-4d3e-a30c-547124c140e8
-- title:
--   Definitions bundle AlpoGeB007 of the alpo.ge GRH release, first cut (Row0b, IsRecT)
-- statement:
--   A definitions bundle of the first cut of L. Alpöge's Lean proof of GRH for Dirichlet $L$-functions (released 20 November 2026, written with Claude; announcement [alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)). The declarations and their proofs are the release's, carved mechanically for this platform: the carve reorders them, restates the namespaces and `open`s each needs, and writes a few declarations from their elaborated form. Two patches are recorded in the carve: an anonymous instance is given its original generated name, and an additive structure that a `to_additive` attribute names is restored beside the structure that names it. The release builds with `maxHeartbeats 4000000` and `maxSynthPendingDepth 3` as project options (and `synthInstance.maxHeartbeats 400000` for its local and global field libraries); since the verifier sets none of these, each carved module section states them as `set_option` lines. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   The first cut publishes the two inputs from which the release concludes its main theorem: `AlpoGe.galoisLocalGlobalStrong_recParameter` (the release's `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) and `AlpoGe.everyCharacter_of_row` (the release's `UpperTheory.FinalTheorems.everyCharacter_of_row`). These bundles hold the definitions their statements need, with the theorems those definitions use.
--
--   **Contents.** It holds 7 declarations of the release's Lean: 2 definitions, 0 inductive types or structures, 5 instances and 0 theorems. The definitions and types are `UpperTheory.Zero.LLC.Good`, `UpperTheory.Zero.LLC.GoodCusp`. It imports the bundles `Def_AlpoGeB004`, `Def_AlpoGeB005`.
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc)

import Mathlib
import Definitions.Def_AlpoGeB004
import Definitions.Def_AlpoGeB005

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.BdR.field _root_.Reformulated.AutPerF.BdR.mulSemiringAction _root_.Reformulated.AutPerF.BdRPlus.isAdicComplete_ker_theta _root_.Reformulated.AutPerF.BdRPlus.isDomain _root_.Reformulated.AutPerF.BdRPlus.nontrivial _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace BdR

instance instAlgebraPadic : Algebra ℚ_[p] (BdR p R) :=
  ((algebraMap (BdRPlus p R) (BdR p R)).comp (algebraMap _ _)).toAlgebra
instance instIsScalarTowerPadicBdRPlus : IsScalarTower ℚ_[p] (BdRPlus p R) (BdR p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end BdR

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAcris0Acris _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.Per.instAwayAinfCastAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.charZero_of_charZero _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
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

instance tateModule.smul : SMul G (tateModule p R) :=
  ⟨fun g η => tateModule.map p (MulSemiringAction.toRingHom G R g) η⟩

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAcris0Acris _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.Per.instAwayAinfCastAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.tateModule.smul _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace Tilt

variable [IsDomain R]

variable [ValuationRing R]

instance valuationRing : ValuationRing (Tilt p R) :=
  { cond' := fun a b => by
      rcases ValuationRing.dvd_total (PreTilt.untilt a) (PreTilt.untilt b) with h | h
      · obtain ⟨c, hc⟩ := (dvd_iff_untilt_dvd a b).2 h
        exact ⟨c, Or.inl hc.symm⟩
      · obtain ⟨c, hc⟩ := (dvd_iff_untilt_dvd b a).2 h
        exact ⟨c, Or.inr hc.symm⟩ }

end Tilt

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.BdR.mulSemiringAction _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable [IsDomain R] [ValuationRing R] [CharZero R]

namespace BdR

variable [IsAlgClosed (FractionRing R)]

instance charZero : CharZero (BdR p R) :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] (BdR p R)).injective

end BdR

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.GLq
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

section Classes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def GoodCusp (y : IrrGL k) : Prop :=
  y.1 = 1 ∨ ((∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* k), Continuous i) ∧
    ∃ (y₀ : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), GlobalTheory.PRep.fixed y₀.rep (GlobalTheory.SplitWeil.KOne k (Fin y₀.1)) ≠ ⊥ ∧ y = y₀.tw χ hχ)

def Good (x : IrrGL k) : Prop := ∃ s, HasSupport x.rep s ∧ ∀ y ∈ s, GoodCusp y

end Classes

end UpperTheory.Zero.LLC

end
end


