-- Prove2me | Definitions.Def_AlpoGeB005
-- name    : AlpoGeB005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T16:26:30.338577+00:00
-- url     : https://prove2.me/theorems/b727710c-152e-438b-9df7-fdb4d8f61f44
-- title:
--   Definitions bundle AlpoGeB005 of the alpo.ge GRH release, first cut (Row0b, IsRecT)
-- statement:
--   A definitions bundle of the first cut of L. Alpöge's Lean proof of GRH for Dirichlet $L$-functions (released 20 November 2026, written with Claude; announcement [alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)). The declarations and their proofs are the release's, carved mechanically for this platform: the carve reorders them, restates the namespaces and `open`s each needs, and writes a few declarations from their elaborated form. Two patches are recorded in the carve: an anonymous instance is given its original generated name, and an additive structure that a `to_additive` attribute names is restored beside the structure that names it. The release builds with `maxHeartbeats 4000000` and `maxSynthPendingDepth 3` as project options (and `synthInstance.maxHeartbeats 400000` for its local and global field libraries); since the verifier sets none of these, each carved module section states them as `set_option` lines. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   The first cut publishes the two inputs from which the release concludes its main theorem: `AlpoGe.galoisLocalGlobalStrong_recParameter` (the release's `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) and `AlpoGe.everyCharacter_of_row` (the release's `UpperTheory.FinalTheorems.everyCharacter_of_row`). These bundles hold the definitions their statements need, with the theorems those definitions use.
--
--   **Contents.** It holds 163 declarations of the release's Lean: 40 definitions, 0 inductive types or structures, 14 instances and 109 theorems. The definitions and types are `GlobalTheory.Pst.Bst`, `GlobalTheory.Pst.Dpst`, `GlobalTheory.Pst.DpstUr`, `GlobalTheory.Pst.Dst`, `GlobalTheory.Pst.Induces`, `GlobalTheory.Pst.IsKummer`, `GlobalTheory.Pst.IsPst`, `GlobalTheory.Pst.WDSpace`, `GlobalTheory.Pst.actD`, `GlobalTheory.Pst.actSt`, `GlobalTheory.Pst.adjExt`, `GlobalTheory.Pst.algC`, `GlobalTheory.Pst.botExt`, `GlobalTheory.Pst.crisIncl`, `GlobalTheory.Pst.frobUr`, `GlobalTheory.Pst.kummer`, `GlobalTheory.Pst.lRoot`, `GlobalTheory.Pst.mapExt`, `GlobalTheory.Pst.monD`, `GlobalTheory.Pst.monSt`, `GlobalTheory.Pst.monV`, `GlobalTheory.Pst.mulD`, `GlobalTheory.Pst.mulV`, `GlobalTheory.Pst.onB`, `GlobalTheory.Pst.phiD`, `GlobalTheory.Pst.phiSt`, `GlobalTheory.Pst.phiU`, `GlobalTheory.Pst.phiV`, `GlobalTheory.Pst.resTo`, `GlobalTheory.Pst.stHom`, `GlobalTheory.Pst.stRep`, `GlobalTheory.Pst.supExt`, `GlobalTheory.Pst.toUr`, `GlobalTheory.Pst.urC`, `GlobalTheory.Pst.urEnd`, `GlobalTheory.Pst.wdMap`, `GlobalTheory.Pst.wdMk`, `GlobalTheory.Pst.wdN`, `ReciprocityTheory.Gal.cycZ`, `UpperTheory.Reformulated.B.CovariantDegrees.GQ`. It imports the bundles `Def_AlpoGeB000`, `Def_AlpoGeB001`, `Def_AlpoGeB002`.
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc)

import Mathlib
import Definitions.Def_AlpoGeB000
import Definitions.Def_AlpoGeB001
import Definitions.Def_AlpoGeB002

section
-- module Solutions.AlpoGe.ReciprocityTheory.GaloisValuations.Global
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem conj_mem_Ine {A : ValuationSubring (Ω)} {g σ : G F Ω} (hg : g ∈ Dec (F := F) A)
    (hσ : σ ∈ Ine (F := F) A) : g * σ * g⁻¹ ∈ Ine (F := F) A := by
  refine ⟨(Dec (F := F) A).mul_mem ((Dec (F := F) A).mul_mem hg hσ.1) ((Dec (F := F) A).inv_mem hg), fun x hx => ?_⟩
  have hy : A.valuation ((g⁻¹ : G F Ω) x) ≤ 1 := by
    rw [A.valuation_le_one_iff, ← apply_mem_iff_of_mem_Dec hg, mul_inv_apply]
    exact (A.valuation_le_one_iff x).mp hx
  have e : (g * σ * g⁻¹) x - x = g (σ ((g⁻¹ : G F Ω) x) - (g⁻¹ : G F Ω) x) := by
    rw [map_sub, mul_inv_apply]; rfl
  rw [e, valuation_apply_lt_one_iff hg]
  exact hσ.2 _ hy

instance normal_Ine_subgroupOf (A : ValuationSubring (Ω)) :
    ((Ine (F := F) A).subgroupOf (Dec (F := F) A)).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_Ine g.2 hn

variable (F Ω) in

def cycZ (l : ℕ) [Fact l.Prime] : G F Ω →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Ω) l).comp
    (MulSemiringAction.toRingAut (G F Ω) (Ω))

section Basic₃

theorem not_valuation_lt_one_of_isPlaceOver {l : ℕ} {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    (n : ℕ) : ¬ A.valuation (((l ^ n : ℕ) : Ω)) < 1 := by
  unfold Formalism.ConjugateSelfDual.IsPlaceOver at h
  intro hlt
  have hc : algebraMap F Ω (((l ^ n : ℕ) : 𝓞 F) : F) = ((l ^ n : ℕ) : Ω) := by
    simp
  rw [← hc, h] at hlt
  exact hl (v.isPrime.mem_of_pow_mem n (by simpa using hlt))

theorem cycZ_toZModPow_eq [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring (Ω)}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} {q : ℕ}
    (hσ : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) (n : ℕ) :
    PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = PadicInt.toZModPow n (q : ℤ_[l]) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hspec := cyclotomicCharacter.spec (L := Ω) l
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) ζ hζ.pow_eq_one
  set m := (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ)) : ℤ_[l]).toZModPow n |>.val with hm
  have hσζ : σ ζ = ζ ^ m := hspec
  have hζA : A.valuation ζ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hN0 hζ.pow_eq_one).le
  have hlt := hσ ζ hζA
  rw [hσζ] at hlt
  have heq : ζ ^ m = ζ ^ q := by
    refine eq_of_pow_eq_one A (not_valuation_lt_one_of_isPlaceOver hl h n) ?_ ?_ hlt
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ q := Units.ext (by simpa using heq)
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
  rw [map_natCast]
  show ((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n = _
  rw [← ZMod.natCast_zmod_val (((cyclotomicCharacter (Ω) l)
    (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) : ℤ_[l]).toZModPow n), ← hm]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq'

theorem isClosed_setOf_apply_lemma [IsAlgClosure F Ω] (x : Ω) (P : Ω → Prop) :
    IsClosed {τ : G F Ω | P (τ x)} := by
  have hal : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hfd : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hH : IsOpen ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ : G F Ω => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin F {x}).fixingSubgroup : Set (G F Ω)),
    ?_, hH.preimage (continuous_const.mul continuous_id), ?_⟩
  · intro τ hτ hPτ
    have h1 : (σ⁻¹ * τ) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x (IntermediateField.mem_adjoin_simple_self F x)
    have h2 : τ x = σ x := by
      have h3 := congrArg σ h1
      rwa [AlgEquiv.mul_apply, mul_inv_apply] at h3
    exact hσ (by simpa only [Set.mem_setOf_eq, h2] using hPτ)
  · show σ⁻¹ * σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _

theorem isClosed_Dec [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Dec (F := F) A : Set (G F Ω)) := by
  have e : (Dec (F := F) A : Set (G F Ω)) = ⋂ x : Ω, {τ : G F Ω | τ x ∈ A ↔ x ∈ A} := by
    ext τ
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun h x => apply_mem_iff_of_mem_Dec h x, fun h => mem_Dec.mpr ?_⟩
    ext y
    have k : τ • ((τ⁻¹ : G F Ω) y) ∈ τ • A ↔ (τ⁻¹ : G F Ω) y ∈ A :=
      ValuationSubring.smul_mem_pointwise_smul_iff
    rw [AlgEquiv.smul_def, mul_inv_apply] at k
    rw [k, ← h ((τ⁻¹ : G F Ω) y), mul_inv_apply]
  rw [e]
  exact isClosed_iInter fun x => isClosed_setOf_apply_lemma x (fun y => y ∈ A ↔ x ∈ A)

theorem isClosed_Ine [IsAlgClosure F Ω] (A : ValuationSubring (Ω)) : IsClosed (Ine (F := F) A : Set (G F Ω)) := by
  have e : (Ine (F := F) A : Set (G F Ω)) = (Dec (F := F) A : Set (G F Ω)) ∩
      ⋂ x : Ω, {τ : G F Ω | A.valuation x ≤ 1 → A.valuation (τ x - x) < 1} := by
    ext τ
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [e]
  exact (isClosed_Dec A).inter (isClosed_iInter fun x =>
    isClosed_setOf_apply_lemma x (fun y => A.valuation x ≤ 1 → A.valuation (y - x) < 1))

end Basic₃

end ReciprocityTheory.Gal
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.SpanNatCastLeComap
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)]
variable (S : Type v) [CommRing S] [Fact ¬IsUnit (p : S)]
variable (U : Type w) [CommRing U] [Fact ¬IsUnit (p : U)]

variable {R S U}

namespace AinfInv

instance instIsScalarTowerPadicIntPadic : IsScalarTower ℤ_[p] ℚ_[p] (AinfInv p R) :=
  IsScalarTower.of_algebraMap_eq fun a => (padicLift_algebraMap p _ _ a).symm

end AinfInv

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace BdRPlus

instance instAlgebraPadic : Algebra ℚ_[p] (BdRPlus p R) :=
  ((algebraMap (AinfInv p R) (BdRPlus p R)).comp (algebraMap _ _)).toAlgebra
instance instAlgebraRat : Algebra ℚ (BdRPlus p R) :=
  ((algebraMap (AinfInv p R) (BdRPlus p R)).comp (algebraMap _ _)).toAlgebra
instance instIsScalarTowerPadicAinfInv : IsScalarTower ℚ_[p] (AinfInv p R) (BdRPlus p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end BdRPlus

namespace BcrisPlus

instance instAlgebraPadic : Algebra ℚ_[p] (BcrisPlus p R) :=
  (padicLift p ((algebraMap (Acris p R) (BcrisPlus p R)).comp (algebraMap ℤ_[p] _))
    (isUnit_p p R)).toAlgebra

end BcrisPlus

namespace Bcris

instance instAlgebraPadic : Algebra ℚ_[p] (Bcris p R) :=
  ((algebraMap (BcrisPlus p R) (Bcris p R)).comp (algebraMap _ _)).toAlgebra
instance instIsScalarTowerPadicBcrisPlus : IsScalarTower ℚ_[p] (BcrisPlus p R) (Bcris p R) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end Bcris

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.EqZeroOfPMulEqZero
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace Acris

instance isAdicComplete : IsAdicComplete (span {(p : Acris p R)}) (Acris p R) := by
  have := AdicCompletion.isAdicComplete_self (span {(p : AcrisZero p R)})
    (Submodule.fg_span_singleton _)
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at this
  exact this

end Acris

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

@[simp] theorem PFlat.map_id (ϖ : PFlat p R) : PFlat.map p (RingHom.id R) ϖ = ϖ :=
  Subtype.ext (Tilt.map_id _)

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Action
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
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

instance PFlat.smul : SMul G (PFlat p R) :=
  ⟨fun g ϖ => PFlat.map p (MulSemiringAction.toRingHom G R g) ϖ⟩

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace Ainf

variable [IsDomain R]

instance charZero_of_charZero [CharZero R] : CharZero (Ainf p R) := (theta p R).charZero

end Ainf

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.OL_finite _root_.Formalism.BasicNotions.Examples₂.LB.OL_frac _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Examples₂.LB.instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

open IsLocalRing

theorem exists_frobenius_Kur (l : ℕ) [Fact l.Prime] :
    ∃ σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (Om l)
  rw [hcard] at hφ
  have hφ' : ∀ (x : Om l) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → φ x = x ^ l := by
    intro x m hm hx
    refine hφ x m (fun h => hm ?_) hx
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hle : (MaximalUnramifiedExtension l).map (φ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  refine ⟨((φ : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict (MaximalUnramifiedExtension l).toSubalgebra
    (fun x => hle ⟨x, x.2, rfl⟩), fun c m _ hlm hc => Subtype.ext ?_⟩
  exact hφ' c m hlm (congrArg Subtype.val hc)

end GlobalTheory.MemLoc
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.OL_finite _root_.Formalism.BasicNotions.Examples₂.LB.OL_frac _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Examples₂.LB.instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial

namespace GlobalTheory.Pst

section Kummer

variable (l : ℕ) [Fact l.Prime]

def lRoot (m : ℕ) : Om l :=
  Nat.rec (motive := fun _ => Om l) (l : Om l)
    (fun _ x => (IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos).choose) m

@[simp] theorem lRoot_zero : lRoot l 0 = (l : Om l) := rfl

theorem lRoot_succ (m : ℕ) : lRoot l (m + 1) ^ l = lRoot l m :=
  (IsAlgClosed.exists_pow_nat_eq (lRoot l m) (Fact.out : l.Prime).pos).choose_spec

theorem lRoot_pow (m : ℕ) : lRoot l m ^ (l ^ m) = (l : Om l) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, lRoot_succ, ih]

theorem lRoot_ne_zero (m : ℕ) : lRoot l m ≠ 0 := by
  intro h0
  have h := lRoot_pow l m
  rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at h
  exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h.symm

variable {l} (P : LocPrime l)

theorem isPrimitiveRoot_zeta (m : ℕ) : IsPrimitiveRoot (P.ζQ m) (l ^ m) := by
  have hp : ∀ k, P.ζQ k ^ l ^ k = 1 := by
    intro k
    induction k with
    | zero => simp [P.ζQ_zero]
    | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  cases m with
  | zero => simp [P.ζQ_zero]
  | succ m =>
    have h := orderOf_eq_prime_pow (x := P.ζQ (m + 1)) (p := l) (n := m)
      (by rw [h1]; exact P.ζQ_one) (hp _)
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

theorem zeta_pow_eq_iff (m a b : ℕ) :
    P.ζQ m ^ a = P.ζQ m ^ b ↔ (a : ZMod (l ^ m)) = (b : ZMod (l ^ m)) := by
  have hz := isPrimitiveRoot_zeta P m
  have hf : IsOfFinOrder (P.ζQ m) := hz.isOfFinOrder (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  rw [hf.pow_eq_pow_iff_modEq, ← hz.eq_orderOf, ZMod.natCast_eq_natCast_iff]

def IsKummer (g : GQ l) (c : ℤ_[l]) : Prop :=
  ∀ m, g (lRoot l m) = P.ζQ m ^ (PadicInt.toZModPow m c).val * lRoot l m

theorem exists_isKummer (g : GQ l) : ∃ c, IsKummer P g c := by
  have hne : ∀ m, NeZero (l ^ m) := fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : ∀ m, ∃ a : ℕ, g (lRoot l m) = P.ζQ m ^ a * lRoot l m := by
    intro m
    obtain ⟨a, -, ha⟩ := (isPrimitiveRoot_zeta P m).eq_pow_of_pow_eq_one
      (ξ := g (lRoot l m) / lRoot l m) (by
        rw [div_pow, ← map_pow, lRoot_pow, map_natCast,
          div_self (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)])
    exact ⟨a, by rw [ha, div_mul_cancel₀ _ (lRoot_ne_zero l m)]⟩
  choose a ha using h1
  have hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ) := by
    intro i
    have h2 := congrArg (· ^ l) (ha (i + 1))
    simp only [← map_pow, mul_pow, lRoot_succ] at h2
    rw [← pow_mul, mul_comm (a (i + 1)), pow_mul, P.ζQ_succ, ha i] at h2
    have h3 := (zeta_pow_eq_iff P i _ _).mp (mul_right_cancel₀ (lRoot_ne_zero l i) h2)
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact_mod_cast h3.dvd
  refine ⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd),
    fun m => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]
  congr 1
  rw [zeta_pow_eq_iff]
  simp

theorem IsKummer.unique {P : LocPrime l} {g : GQ l} {c c' : ℤ_[l]} (h : IsKummer P g c)
    (h' : IsKummer P g c') : c = c' := by
  refine PadicInt.ext_of_toZModPow.mp fun m => ?_
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h3 := (zeta_pow_eq_iff P m _ _).mp
    (mul_right_cancel₀ (lRoot_ne_zero l m) ((h m).symm.trans (h' m)))
  simpa using h3

def kummer (g : GQ l) : ℤ_[l] := (exists_isKummer P g).choose

theorem isKummer_kummer (g : GQ l) : IsKummer P g (kummer P g) := (exists_isKummer P g).choose_spec

theorem kummer_eq_zero_iff (g : GQ l) : kummer P g = 0 ↔ ∀ m, g (lRoot l m) = lRoot l m := by
  constructor
  · intro h m
    have := isKummer_kummer P g m
    rw [h] at this
    simpa using this
  · intro h
    exact (isKummer_kummer P g).unique fun m => by simpa using h m

@[simp] theorem kummer_one : kummer P 1 = 0 := (kummer_eq_zero_iff P 1).mpr fun _ => rfl

theorem kummer_mul (g h : GQ l) :
    (kummer P (g * h) : ℚ_[l]) = kummer P g + (P.χQ g : ℚ_[l]) * kummer P h := by
  have hx : ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
    obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (by simp)
    have e : (P.χQ g : ℚ_[l]) = ((P.χQ g : ℚ_[l]) - a) + a := by ring
    rw [e]
    refine (Padic.nonarchimedean _ _).trans (max_le (by simpa using ha) ?_)
    exact_mod_cast Padic.norm_int_le_one (p := l) (a : ℤ)
  let x : ℤ_[l] := ⟨P.χQ g, hx⟩
  have key : IsKummer P (g * h) (kummer P g + x * kummer P h) := by
    intro m
    have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    obtain ⟨a, ha, hg⟩ := P.χQ_cyc g m (P.ζQ m) (isPrimitiveRoot_zeta P m).pow_eq_one
    have hxa : PadicInt.toZModPow m x = a := by
      rw [← sub_eq_zero, ← map_natCast (PadicInt.toZModPow m), ← map_sub, ← RingHom.mem_ker,
        PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact ha
    rw [AlgEquiv.mul_apply, isKummer_kummer P h m, map_mul, map_pow, hg, isKummer_kummer P g m,
      ← mul_assoc, ← pow_mul, ← pow_add]
    congr 1
    rw [zeta_pow_eq_iff]
    simp [hxa, add_comm]
  rw [(isKummer_kummer P (g * h)).unique key]
  rfl

end Kummer

section Ring

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def botExt (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩

theorem mem_GK_botExt (g : GQ l) : g ∈ GK (botExt l) := by
  simp [GK, botExt]

theorem localPrime_galoisAction_periodT (g : GQ l) : P.actQ g P.tB = (P.χQ g : ℚ_[l]) • P.tB := by
  have h := (P.PD (botExt l)).t_act ⟨g, mem_GK_botExt g⟩
  rwa [P.PD_actB, P.period_datum_t_eq, P.PD_χ] at h

theorem localPrime_frobenius_periodT : P.φB P.tB = (l : ℚ_[l]) • P.tB := by
  have h := (P.PD (botExt l)).t_φ
  rwa [P.PD_φ, P.period_datum_t_eq, P.PD_p] at h

theorem phiB_actQ (g : GQ l) (b : P.R.B) : P.φB (P.actQ g b) = P.actQ g (P.φB b) := by
  have h := (P.PD (botExt l)).φ_comm ⟨g, mem_GK_botExt g⟩ b
  rwa [P.PD_actB, P.PD_actB, P.PD_φ, P.PD_φ] at h

theorem phiB_injective : Function.Injective P.φB := fun a b hab =>
  (P.PD (botExt l)).φ_inj (by rw [P.PD_φ, P.PD_φ, hab])

abbrev Bst : Type := Polynomial P.R.B

def stHom (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y : Bst P) : Bst P →ₐ[ℚ_[l]] Bst P :=
  eval₂AlgHom (CAlgHom.comp f) y fun _ => Commute.all _ _

@[simp] theorem stHom_C (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y : Bst P) (b : P.R.B) :
    stHom P f y (C b) = C (f b) := eval₂_C _ _

@[simp] theorem stHom_X (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y : Bst P) : stHom P f y X = y := eval₂_X _ _

theorem stHom_apply (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y p : Bst P) :
    stHom P f y p = (p.map (f : P.R.B →+* P.R.B)).comp y := by
  rw [comp, eval₂_map]; rfl

theorem derivative_stHom (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y p : Bst P) :
    derivative (stHom P f y p) = derivative y * stHom P f y (derivative p) := by
  rw [stHom_apply, stHom_apply, derivative_comp, derivative_map]

theorem stHom_ext {F G : Bst P →ₐ[ℚ_[l]] Bst P} (hC : ∀ b, F (C b) = G (C b)) (hX : F X = G X) :
    F = G := algHom_ext' (AlgHom.ext hC) hX

def actSt : GQ l →* (Bst P →ₐ[ℚ_[l]] Bst P) where
  toFun g := stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB))
  map_one' := stHom_ext P (fun b => by simp) (by simp)
  map_mul' g h := stHom_ext P (fun b => by simp [AlgHom.mul_apply]) (by
    have e : (P.actQ g : P.R.B →ₐ[ℚ_[l]] P.R.B) P.tB = (P.χQ g : ℚ_[l]) • P.tB := localPrime_galoisAction_periodT P g
    simp only [AlgHom.mul_apply, stHom_X, map_add, stHom_C, map_smul, e,
      kummer_mul, add_smul, smul_smul, add_assoc, mul_comm])

@[simp] theorem actSt_C (g : GQ l) (b : P.R.B) : actSt P g (C b) = C (P.actQ g b) := stHom_C _ _ _ _

@[simp] theorem actSt_X (g : GQ l) : actSt P g X = X + C ((kummer P g : ℚ_[l]) • P.tB) :=
  stHom_X _ _ _

def phiSt : Bst P →ₐ[ℚ_[l]] Bst P := stHom P P.φB ((l : Bst P) * X)

@[simp] theorem phiSt_C (b : P.R.B) : phiSt P (C b) = C (P.φB b) := stHom_C _ _ _ _

@[simp] theorem phiSt_X : phiSt P X = (l : Bst P) * X := stHom_X _ _ _

def monSt : Bst P →ₗ[ℚ_[l]] Bst P := -(derivative.restrictScalars ℚ_[l])

@[simp] theorem monSt_apply (p : Bst P) : monSt P p = -derivative p := rfl

theorem phiSt_actSt (g : GQ l) (p : Bst P) : phiSt P (actSt P g p) = actSt P g (phiSt P p) := by
  have : (phiSt P).comp (actSt P g) = (actSt P g).comp (phiSt P) :=
    stHom_ext P (fun b => by simp [phiB_actQ]) (by
      simp only [AlgHom.comp_apply, actSt_X, phiSt_X, map_add, phiSt_C, map_smul, localPrime_frobenius_periodT, map_mul,
        map_natCast, mul_add]
      rw [smul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, map_mul, map_natCast])
  exact AlgHom.congr_fun this p

theorem monSt_actSt (g : GQ l) (p : Bst P) : monSt P (actSt P g p) = actSt P g (monSt P p) := by
  have := derivative_stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB)) p
  simp only [derivative_add, derivative_X, derivative_C, add_zero, one_mul] at this
  rw [monSt_apply, monSt_apply, map_neg]
  exact congrArg Neg.neg this

theorem monSt_phiSt (p : Bst P) : monSt P (phiSt P p) = (l : ℚ_[l]) • phiSt P (monSt P p) := by
  have := derivative_stHom P P.φB ((l : Bst P) * X) p
  simp only [derivative_mul, derivative_natCast, zero_mul, derivative_X, mul_one, zero_add] at this
  rw [monSt_apply, monSt_apply, map_neg, smul_neg, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  exact congrArg Neg.neg this

theorem monSt_C_mul (b : P.R.B) (p : Bst P) : monSt P (C b * p) = C b * monSt P p := by
  simp

theorem exists_monSt_pow_eq_zero (p : Bst P) : ∃ n : ℕ, (monSt P ^ n) p = 0 := by
  have h : ∀ (n : ℕ) (q : Bst P), (monSt P ^ n) q = (-1) ^ n * derivative^[n] q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro q; rw [pow_succ, Module.End.mul_apply, ih]; simp [pow_succ]
  exact ⟨p.natDegree + 1, by rw [h, iterate_derivative_eq_zero (Nat.lt_succ_self _), mul_zero]⟩

theorem phiSt_injective : Function.Injective (phiSt P) := by
  intro p q hpq
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have e : ∀ r : Bst P, (phiSt P r).comp (C (algebraMap ℚ_[l] P.R.B (l : ℚ_[l])⁻¹) * X) =
      r.map (P.φB : P.R.B →+* P.R.B) := by
    intro r
    rw [phiSt, stHom_apply, comp_assoc, mul_comp, natCast_comp, X_comp, ← mul_assoc, ← map_natCast C,
      ← map_mul, ← map_natCast (algebraMap ℚ_[l] P.R.B), ← map_mul, mul_inv_cancel₀ hl, map_one,
      map_one, one_mul, comp_X]
  exact map_injective (P.φB : P.R.B →+* P.R.B) (phiB_injective P) (by rw [← e, ← e, hpq])

end Ring

end GlobalTheory.Pst
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.OL_finite _root_.Formalism.BasicNotions.Examples₂.LB.OL_frac _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Examples₂.LB.instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module

namespace GlobalTheory.Pst

section Unram

variable {l : ℕ} [Fact l.Prime]

theorem eq_of_pow_eq_one_of_norm_sub_lt {x y : Om l} {m : ℕ} (hm : ¬ l ∣ m) (hx : x ^ m = 1)
    (hy : y ^ m = 1) (h : ‖x - y‖ < 1) : x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hy1 : ‖y‖ = 1 := by
    have := congrArg norm hy
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp this
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  by_contra hne
  set z := x / y with hz
  have hz1 : z ≠ 1 := fun h1 => hne (by rwa [hz, div_eq_one_iff_eq hy0] at h1)
  have hzm : z ^ m = 1 := by rw [hz, div_pow, hx, hy, div_one]
  have hzn : ‖z - 1‖ < 1 := by
    rw [hz, div_sub_one hy0, norm_div, hy1, div_one]; exact h
  have hz0 : ‖z‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (z - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le hzn.le le_rfl)
  have hsum : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := geom_sum_mul z m
    rw [hzm, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hz1)
  have hpow : ∀ i : ℕ, ‖z ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : z ^ (i + 1) - 1 = z * (z ^ i - 1) + (z - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hzn)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz0).trans_lt ih
  have hall : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, z ^ i - (n : Om l)‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ∑ i ∈ Finset.range (n + 1), z ^ i - ((n + 1 : ℕ) : Om l) =
          (∑ i ∈ Finset.range n, z ^ i - (n : Om l)) + (z ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hpow n))
  have h1 := hall m
  rw [hsum, zero_sub, norm_neg, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends,
    Padic.norm_natCast_lt_one_iff] at h1
  exact hm h1

theorem norm_eq_one_of_pow_eq_one {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : ‖x‖ = 1 := by
  have := congrArg norm hx
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp this

theorem kur_algHom_ext {B : Type*} [Semiring B] [Algebra ℚ_[l] B] {f g : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] B}
    (h : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → f c = g c) : f = g :=
  IntermediateField.adjoin_algHom_ext ℚ_[l] fun _ ⟨m, h0, hm, hx⟩ => h _ m h0 hm (Subtype.ext hx)

variable (l) in

def frobUr : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := (GlobalTheory.MemLoc.exists_frobenius_Kur l).choose

theorem frobUr_root (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ) (h0 : 0 < m) (hm : ¬ l ∣ m) (hc : c ^ m = 1) :
    frobUr l c = c ^ l := (GlobalTheory.MemLoc.exists_frobenius_Kur l).choose_spec c m h0 hm hc

theorem frobUr_bijective : Function.Bijective (frobUr l) :=
  Algebra.IsAlgebraic.algHom_bijective _

def adjExt (x : Om l) : FinExt l :=
  ⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩

theorem mem_adjExt (x : Om l) : x ∈ (adjExt x).1 := IntermediateField.mem_adjoin_simple_self _ x

def supExt (K K' : FinExt l) : FinExt l :=
  ⟨K.1 ⊔ K'.1, haveI := K.2; haveI := K'.2; IntermediateField.finiteDimensional_sup _ _⟩

def mapExt (g : GQ l) (K : FinExt l) : FinExt l :=
  ⟨K.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
    haveI := K.2; (K.1.equivMap (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv.finiteDimensional⟩

theorem mem_GK {K : FinExt l} {g : GQ l} : g ∈ GK K ↔ ∀ x ∈ K.1, g x = x :=
  IntermediateField.mem_fixingSubgroup_iff _ _

theorem conj_mem_GK {K : FinExt l} {g h : GQ l} (hh : h ∈ GK (mapExt g K)) : g⁻¹ * h * g ∈ GK K := by
  rw [mem_GK] at hh ⊢
  intro x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh (g x) ⟨x, hx, rfl⟩, ← AlgEquiv.mul_apply,
    inv_mul_cancel, AlgEquiv.one_apply]

variable (P : LocPrime l)

theorem phiB_algebraMap (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (frobUr l c) := by
  have : P.φB.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) =
      (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B).comp (frobUr l) := by
    refine kur_algHom_ext fun c m h0 hm hc => ?_
    have hc' : (c : Om l) ^ m = 1 := congrArg Subtype.val hc
    let x : ↥(K0 (adjExt (c : Om l))) := ⟨c, mem_adjExt _, c.2⟩
    have hx : x ^ m = 1 := Subtype.ext hc'
    have h1 := (P.PD (adjExt (c : Om l))).φ_K₀ x
    rw [P.PD_φ] at h1
    have h2 : (((P.PD (adjExt (c : Om l))).σ x : ↥(K0 (adjExt (c : Om l)))) : Om l) = (c : Om l) ^ l := by
      refine eq_of_pow_eq_one_of_norm_sub_lt hm ?_ (by rw [← pow_mul, mul_comm, pow_mul, hc', one_pow])
        (P.PD_σ _ x (norm_eq_one_of_pow_eq_one h0 hc').le)
      have : (P.PD (adjExt (c : Om l))).σ x ^ m = 1 := by rw [← map_pow, hx, map_one]
      exact congrArg Subtype.val this
    rw [AlgHom.comp_apply, AlgHom.comp_apply, frobUr_root c m h0 hm hc]
    refine h1.trans ?_
    exact congrArg (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) (Subtype.ext h2)
  exact AlgHom.congr_fun this c

theorem phiSt_algebraMap (c : ↥(MaximalUnramifiedExtension l)) :
    phiSt P (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) (frobUr l c) := by
  rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, phiSt_C, phiB_algebraMap]

theorem actSt_algebraMap (g : GQ l) (c c' : ↥(MaximalUnramifiedExtension l)) (h : g (c : Om l) = (c' : Om l)) :
    actSt P g (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c' := by
  rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, actSt_C, P.actQ_Kur g c c' h]

end Unram

section Dst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)
  (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
  (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

def onB : End ℚ_[l] (Bst P) →+* End LL (V ⊗[ℚ_[l]] Bst P) where
  toFun f := AlgebraTensorModule.map LinearMap.id f
  map_one' := by ext; simp
  map_mul' f g := by ext; simp
  map_zero' := by ext; simp
  map_add' f g := by ext; simp [tmul_add]

def phiV : End LL (V ⊗[ℚ_[l]] Bst P) := onB P LL V (phiSt P).toLinearMap

def monV : End LL (V ⊗[ℚ_[l]] Bst P) := onB P LL V (monSt P)

def mulV : ↥(MaximalUnramifiedExtension l) →+* End LL (V ⊗[ℚ_[l]] Bst P) :=
  (onB P LL V).comp (((Algebra.lmul ℚ_[l] (Bst P) : Bst P →ₐ[ℚ_[l]] End ℚ_[l] (Bst P)) :
    Bst P →+* End ℚ_[l] (Bst P)).comp (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P)))

def crisIncl : V ⊗[ℚ_[l]] P.R.B →ₗ[LL] V ⊗[ℚ_[l]] Bst P :=
  AlgebraTensorModule.map LinearMap.id (CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap

variable {LL V}

@[simp] theorem onB_tmul (f : End ℚ_[l] (Bst P)) (v : V) (b : Bst P) :
    onB P LL V f (v ⊗ₜ b) = v ⊗ₜ f b := rfl

@[simp] theorem phiV_tmul (v : V) (b : Bst P) : phiV P LL V (v ⊗ₜ b) = v ⊗ₜ phiSt P b := rfl

@[simp] theorem monV_tmul (v : V) (b : Bst P) : monV P LL V (v ⊗ₜ b) = v ⊗ₜ monSt P b := rfl

@[simp] theorem mulV_tmul (c : ↥(MaximalUnramifiedExtension l)) (v : V) (b : Bst P) :
    mulV P LL V c (v ⊗ₜ b) = v ⊗ₜ (algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) := rfl

@[simp] theorem crisIncl_tmul (v : V) (b : P.R.B) : crisIncl P LL V (v ⊗ₜ b) = v ⊗ₜ C b := rfl

theorem end_ext {f g : End LL (V ⊗[ℚ_[l]] Bst P)} (h : ∀ v b, f (v ⊗ₜ b) = g (v ⊗ₜ b)) : f = g :=
  AlgebraTensorModule.ext h

theorem phiV_injective : Function.Injective (phiV P LL V) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V) (phiSt P).toLinearMap (phiSt_injective P)

theorem monV_phiV : monV P LL V * phiV P LL V = (l : LL) • (phiV P LL V * monV P LL V) :=
  end_ext P fun v b => by
    rw [End.mul_apply, phiV_tmul, monV_tmul, monSt_phiSt, LinearMap.smul_apply, End.mul_apply,
      monV_tmul, phiV_tmul, tmul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem phiV_mulV (c : ↥(MaximalUnramifiedExtension l)) :
    phiV P LL V * mulV P LL V c = mulV P LL V (frobUr l c) * phiV P LL V :=
  end_ext P fun v b => by simp only [End.mul_apply, phiV_tmul, mulV_tmul, map_mul, phiSt_algebraMap]

theorem monV_mulV (c : ↥(MaximalUnramifiedExtension l)) : monV P LL V * mulV P LL V c = mulV P LL V c * monV P LL V :=
  end_ext P fun v b => by
    simp only [End.mul_apply, monV_tmul, mulV_tmul, Polynomial.algebraMap_apply, monSt_C_mul]

theorem exists_monV_pow_eq_zero (x : V ⊗[ℚ_[l]] Bst P) : ∃ n : ℕ, (monV P LL V ^ n) x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v b =>
    obtain ⟨n, hn⟩ := exists_monSt_pow_eq_zero P b
    exact ⟨n, by rw [monV, ← map_pow, onB_tmul, hn, tmul_zero]⟩
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [map_add]
    nth_rewrite 1 [add_comm m n]
    rw [pow_add, pow_add, End.mul_apply, End.mul_apply, hm, hn, map_zero, map_zero, add_zero]

variable {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

def stRep : Representation LL ↥(GK K) (V ⊗[ℚ_[l]] Bst P) where
  toFun g := AlgebraTensorModule.map (ρ g) (actSt P (g : GQ l)).toLinearMap
  map_one' := by ext; simp
  map_mul' g h := end_ext P fun v b => by simp [AlgHom.mul_apply]

@[simp] theorem stRep_tmul (g : ↥(GK K)) (v : V) (b : Bst P) :
    stRep P ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ actSt P (g : GQ l) b := rfl

theorem phiV_stRep (g : ↥(GK K)) : phiV P LL V * stRep P ρ g = stRep P ρ g * phiV P LL V :=
  end_ext P fun v b => by simp only [End.mul_apply, phiV_tmul, stRep_tmul, phiSt_actSt]

theorem monV_stRep (g : ↥(GK K)) : monV P LL V * stRep P ρ g = stRep P ρ g * monV P LL V :=
  end_ext P fun v b => by simp only [End.mul_apply, monV_tmul, stRep_tmul, monSt_actSt]

theorem stRep_mulV (g : ↥(GK K)) (c c' : ↥(MaximalUnramifiedExtension l)) (h : (g : GQ l) (c : Om l) = (c' : Om l)) :
    stRep P ρ g * mulV P LL V c = mulV P LL V c' * stRep P ρ g :=
  end_ext P fun v b => by
    simp only [End.mul_apply, stRep_tmul, mulV_tmul, map_mul, actSt_algebraMap P _ c c' h]

def Dst : Submodule LL (V ⊗[ℚ_[l]] Bst P) := ⨅ g, LinearMap.ker (stRep P ρ g - LinearMap.id)

theorem mem_Dst {x : V ⊗[ℚ_[l]] Bst P} : x ∈ Dst P ρ ↔ ∀ g, stRep P ρ g x = x := by
  simp [Dst, sub_eq_zero]

abbrev resTo {K' : FinExt l} (h : K.1 ≤ K'.1) : Representation LL ↥(GK K') V :=
  ρ.comp (Subgroup.inclusion (GK_le h))

theorem mem_Dst_resTo {K' : FinExt l} (h : K.1 ≤ K'.1) {x : V ⊗[ℚ_[l]] Bst P} :
    x ∈ Dst P (resTo ρ h) ↔ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → stRep P ρ g x = x := by
  rw [mem_Dst]
  exact ⟨fun hx g hg => hx ⟨g, hg⟩, fun hx g => hx ⟨g, GK_le h g.2⟩ g.2⟩

def Dpst : Submodule LL (V ⊗[ℚ_[l]] Bst P) where
  carrier := {x | ∃ (K' : FinExt l) (h : K.1 ≤ K'.1), x ∈ Dst P (resTo ρ h)}
  zero_mem' := ⟨K, le_rfl, zero_mem _⟩
  add_mem' := by
    rintro x y ⟨K₁, h₁, hx⟩ ⟨K₂, h₂, hy⟩
    rw [mem_Dst_resTo] at hx hy
    refine ⟨supExt K₁ K₂, h₁.trans le_sup_left, (mem_Dst_resTo P ρ _).mpr fun g hg => ?_⟩
    rw [map_add, hx g (GK_le (K' := supExt K₁ K₂) le_sup_left hg),
      hy g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)]
  smul_mem' := by
    rintro c x ⟨K₁, h₁, hx⟩
    exact ⟨K₁, h₁, Submodule.smul_mem _ c hx⟩

theorem mem_Dpst {x : V ⊗[ℚ_[l]] Bst P} : x ∈ Dpst P ρ ↔
    ∃ K' : FinExt l, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → stRep P ρ g x = x := by
  constructor
  · rintro ⟨K', h, hx⟩
    exact ⟨K', (mem_Dst_resTo P ρ h).mp hx⟩
  · rintro ⟨K', hx⟩
    exact ⟨supExt K K', le_sup_left, (mem_Dst_resTo P ρ _).mpr fun g hg =>
      hx g (GK_le (K' := supExt K K') le_sup_right hg)⟩

theorem mem_Dpst_of_commute {T : End LL (V ⊗[ℚ_[l]] Bst P)}
    (hT : ∀ g, T * stRep P ρ g = stRep P ρ g * T) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    T x ∈ Dpst P ρ := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  refine (mem_Dpst P ρ).mpr ⟨K', fun g hg => ?_⟩
  rw [← End.mul_apply, ← hT, End.mul_apply, hx g hg]

theorem stRep_mem_Dpst (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    stRep P ρ g x ∈ Dpst P ρ := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  refine (mem_Dpst P ρ).mpr ⟨mapExt g K', fun h hh => ?_⟩
  have := congrArg (stRep P ρ g) (hx (g⁻¹ * h * g) (conj_mem_GK hh))
  rwa [← End.mul_apply, ← map_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, map_mul,
    End.mul_apply] at this

theorem mulV_mem_Dpst (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) (hx : x ∈ Dpst P ρ) :
    mulV P LL V c x ∈ Dpst P ρ := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  refine (mem_Dpst P ρ).mpr ⟨supExt K' (adjExt (c : Om l)), fun g hg => ?_⟩
  have h1 : (g : GQ l) (c : Om l) = c :=
    mem_GK.mp (GK_le (K := adjExt (c : Om l)) le_sup_right hg) _ (mem_adjExt _)
  rw [← End.mul_apply, stRep_mulV P ρ g c c h1, End.mul_apply, hx g (GK_le (K := K') le_sup_left hg)]

def phiD : End LL ↥(Dpst P ρ) := (phiV P LL V).restrict (mem_Dpst_of_commute P ρ (phiV_stRep P ρ))

def monD : End LL ↥(Dpst P ρ) := (monV P LL V).restrict (mem_Dpst_of_commute P ρ (monV_stRep P ρ))

def actD : Representation LL ↥(GK K) ↥(Dpst P ρ) where
  toFun g := (stRep P ρ g).restrict (stRep_mem_Dpst P ρ g)
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (by simp)

def mulD : ↥(MaximalUnramifiedExtension l) →+* End LL ↥(Dpst P ρ) where
  toFun c := (mulV P LL V c).restrict (mulV_mem_Dpst P ρ c)
  map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun x => Subtype.ext (by simp)
  map_zero' := LinearMap.ext fun x => Subtype.ext (by simp)
  map_add' g h := LinearMap.ext fun x => Subtype.ext (by simp)

@[simp] theorem coe_phiD (x : ↥(Dpst P ρ)) : (phiD P ρ x : V ⊗[ℚ_[l]] Bst P) = phiV P LL V x := rfl

@[simp] theorem coe_monD (x : ↥(Dpst P ρ)) : (monD P ρ x : V ⊗[ℚ_[l]] Bst P) = monV P LL V x := rfl

@[simp] theorem coe_actD (g : ↥(GK K)) (x : ↥(Dpst P ρ)) :
    (actD P ρ g x : V ⊗[ℚ_[l]] Bst P) = stRep P ρ g x := rfl

@[simp] theorem coe_mulD (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρ)) :
    (mulD P ρ c x : V ⊗[ℚ_[l]] Bst P) = mulV P LL V c x := rfl

theorem phiD_actD (g : ↥(GK K)) : phiD P ρ * actD P ρ g = actD P ρ g * phiD P ρ :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (phiV_stRep P ρ g) x)

theorem monD_actD (g : ↥(GK K)) : monD P ρ * actD P ρ g = actD P ρ g * monD P ρ :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (monV_stRep P ρ g) x)

theorem monD_phiD : monD P ρ * phiD P ρ = (l : LL) • (phiD P ρ * monD P ρ) :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (monV_phiV P) x.1)

theorem phiD_mulD (c : ↥(MaximalUnramifiedExtension l)) : phiD P ρ * mulD P ρ c = mulD P ρ (frobUr l c) * phiD P ρ :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (phiV_mulV P c) x.1)

theorem monD_mulD (c : ↥(MaximalUnramifiedExtension l)) : monD P ρ * mulD P ρ c = mulD P ρ c * monD P ρ :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (monV_mulV P c) x.1)

theorem actD_mulD (g : ↥(GK K)) (c c' : ↥(MaximalUnramifiedExtension l)) (h : (g : GQ l) (c : Om l) = (c' : Om l)) :
    actD P ρ g * mulD P ρ c = mulD P ρ c' * actD P ρ g :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (stRep_mulV P ρ g c c' h) x.1)

theorem phiD_injective : Function.Injective (phiD P ρ) :=
  fun _ _ h => Subtype.ext (phiV_injective P (congrArg Subtype.val h))

def DpstUr : Type := ↥(Dpst P ρ)

instance instAddCommGroupDpstUr : AddCommGroup (DpstUr P ρ) := inferInstanceAs (AddCommGroup ↥(Dpst P ρ))

instance instModuleSubtypeOmMemIntermediateFieldPadicMaximalUnramifiedExtensionDpstUr : Module ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := Module.compHom ↥(Dpst P ρ) (mulD P ρ)

def toUr : ↥(Dpst P ρ) ≃+ DpstUr P ρ := AddEquiv.refl _

def urEnd (T : End LL ↥(Dpst P ρ)) (hT : ∀ c, T * mulD P ρ c = mulD P ρ c * T) :
    End ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) where
  toFun x := toUr P ρ (T ((toUr P ρ).symm x))
  map_add' x y := by simp only [map_add]
  map_smul' c x := LinearMap.congr_fun (hT c) x

def IsPst : Prop := Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) = Module.rank ℚ_[l] V

variable [FiniteDimensional ℚ_[l] V]

theorem isPst_iff : IsPst P ρ ↔ FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ∧
    finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) = finrank ℚ_[l] V := by
  constructor
  · intro h
    refine ⟨Module.rank_lt_aleph0_iff.mp (by rw [h]; exact Module.rank_lt_aleph0 _ _), ?_⟩
    rw [finrank, finrank, h]
  · rintro ⟨h1, h2⟩
    rw [IsPst, ← finrank_eq_rank, ← finrank_eq_rank, h2]

variable {P ρ}

theorem IsPst.finiteDimensional (h : IsPst P ρ) : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
  ((isPst_iff P ρ).mp h).1

omit [FiniteDimensional ℚ_[l] V] in

theorem phiD_bijective [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] : Function.Bijective (phiD P ρ) := by
  refine ⟨phiD_injective P ρ, ?_⟩
  let j : DpstUr P ρ →+ DpstUr P ρ := (phiD P ρ).toAddMonoidHom
  have hj : ∀ (c : ↥(MaximalUnramifiedExtension l)) (x : DpstUr P ρ), j (c • x) = frobUr l c • j x :=
    fun c x => LinearMap.congr_fun (phiD_mulD P ρ c) x
  have hli := (finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)).linearIndependent.map_of_surjective_injective
    (frobUr l) j frobUr_bijective.2
    (fun x hx => phiD_injective P ρ (hx.trans (map_zero (phiD P ρ)).symm)) hj
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp)
  intro y
  have hy : toUr P ρ y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (Set.range (j ∘ finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ))) := by
    rw [hsp]; trivial
  have key : ∀ z ∈ Submodule.span ↥(MaximalUnramifiedExtension l) (Set.range (j ∘ finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ))),
      ∃ x, j x = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact ⟨_, rfl⟩
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a, rfl⟩ := ha; obtain ⟨b, rfl⟩ := hb; exact ⟨a + b, map_add _ _ _⟩
    | smul c a _ ha =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨c, rfl⟩ := frobUr_bijective.2 c
      exact ⟨c • a, hj c a⟩
  exact key _ hy

omit [FiniteDimensional ℚ_[l] V] in

theorem isNilpotent_monD [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] : IsNilpotent (monD P ρ) := by
  have hp : ∀ (n : ℕ) (x : ↥(Dpst P ρ)), (urEnd P ρ (monD P ρ) (monD_mulD P ρ) ^ n) (toUr P ρ x) =
      toUr P ρ ((monD P ρ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, ← ih]; rfl
  have hc : ∀ (n : ℕ) (x : ↥(Dpst P ρ)),
      (((monD P ρ ^ n) x : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) = (monV P LL V ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, ih]; rfl
  obtain ⟨n, hn⟩ : IsNilpotent (urEnd P ρ (monD P ρ) (monD_mulD P ρ)) := by
    rw [Module.End.isNilpotent_iff_of_finite]
    intro x
    obtain ⟨x, rfl⟩ := (toUr P ρ).surjective x
    obtain ⟨n, hn⟩ := exists_monV_pow_eq_zero P (LL := LL) x.1
    exact ⟨n, by rw [hp, show (monD P ρ ^ n) x = 0 from Subtype.ext ((hc n x).trans hn), map_zero]⟩
  exact ⟨n, LinearMap.ext fun x => (toUr P ρ).injective (by rw [← hp, hn]; rfl)⟩

omit [FiniteDimensional ℚ_[l] V] in

theorem exists_actD_eq_one [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] : ∃ K' : FinExt l,
    ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (∀ c, actD P ρ g * mulD P ρ c = mulD P ρ c * actD P ρ g) →
      actD P ρ g = 1 := by
  let b := finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)
  choose F hF using fun i => (mem_Dpst P ρ).mp ((toUr P ρ).symm (b i)).2
  have := fun i => (F i).2
  refine ⟨⟨⨆ i, (F i).1, inferInstance⟩, fun g hg hc => ?_⟩
  have h1 : urEnd P ρ (actD P ρ g) hc = 1 := b.ext fun i =>
    Subtype.ext (hF i g (GK_le (K := F i) (le_iSup (fun i => (F i).1) i) hg))
  exact LinearMap.ext fun x => LinearMap.congr_fun h1 (toUr P ρ x)

end Dst

end GlobalTheory.Pst
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.OL_finite _root_.Formalism.BasicNotions.Examples₂.LB.OL_frac _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Examples₂.LB.instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

variable (Bw : LocBridge l E Ω (Dec (F := E) A) O)

def Induces : Prop := ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1

variable {Bw}

omit [NumberField E] in

theorem Induces.valuation_lt_one_iff (hj : Induces Bw) (x : Ω) : A.valuation x < 1 ↔ ‖Bw.j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖Bw.j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

variable (Bw) (h : IsPlaceOver A w)

variable {Bw h} [IsAlgClosure E Ω]

theorem frobUr_pow_root (n : ℕ) (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ) (h0 : 0 < m) (hm : ¬ l ∣ m) (hc : c ^ m = 1) :
    (frobUr l ^ n) c = c ^ l ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, AlgHom.mul_apply, frobUr_root c m h0 hm hc, map_pow, ih, ← pow_mul, pow_succ]

variable (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

section Unit

variable {K : FinExt l} (ρ : Representation LL ↥(GK K) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

def phiU : (End LL ↥(Dpst P ρ))ˣ := ((End.isUnit_iff _).mpr (phiD_bijective (P := P) (ρ := ρ))).unit

@[simp] theorem coe_phiU : (phiU P ρ : End LL ↥(Dpst P ρ)) = phiD P ρ := rfl

theorem commute_actD_phiU (g : ↥(GK K)) (n : ℤ) :
    Commute (actD P ρ g) ((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) :=
  Commute.units_zpow_right (u := phiU P ρ) (phiD_actD P ρ g).symm n

omit [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] in

theorem phiD_pow_mulD (n : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    phiD P ρ ^ n * mulD P ρ c = mulD P ρ ((frobUr l ^ n) c) * phiD P ρ ^ n := by
  induction n generalizing c with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, phiD_mulD, ← mul_assoc, ih, mul_assoc, pow_succ, AlgHom.mul_apply]

theorem monD_phiU_zpow (n : ℤ) :
    monD P ρ * ((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) =
      (l : LL) ^ n • (((phiU P ρ ^ n : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) * monD P ρ) := by
  have : CharZero LL := charZero_of_injective_algebraMap (algebraMap ℚ_[l] LL).injective
  have hl : (l : LL) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have h1 : monD P ρ * ((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) =
      (l : LL)⁻¹ • (((phiU P ρ)⁻¹ : (End LL ↥(Dpst P ρ))ˣ) * monD P ρ) := by
    rw [eq_inv_smul_iff₀ hl, Units.eq_inv_mul_iff_mul_eq, mul_smul_comm, ← mul_assoc, ← smul_mul_assoc,
      coe_phiU, ← monD_phiD, ← coe_phiU, Units.mul_inv_cancel_right]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, coe_phiU, monD_phiD,
      mul_smul_comm, smul_smul, zpow_add_one₀ hl, mul_assoc]
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, ← mul_assoc, ih, smul_mul_assoc, mul_assoc, h1,
      mul_smul_comm, smul_smul, zpow_sub_one₀ hl, mul_assoc]

end Unit

end Bridge

end GlobalTheory.Pst
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.OL_finite _root_.Formalism.BasicNotions.Examples₂.LB.OL_frac _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Examples₂.LB.instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)

@[reducible] def algC (LL : FinExt l) : Algebra ↥LL.1 ℂ :=
  (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))).toAlgebra

def urC : ↥(MaximalUnramifiedExtension l) →+* ℂ := ι.toRingHom.comp (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))

section Space

variable {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

abbrev WDSpace : Type :=
  @Letter ↥LL.1 ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) _ _ _ _ (mulD P ρ) ℂ _ (algC ι LL) (urC ι)

def wdMk (x : ↥(Dpst P ρ)) : WDSpace P ι ρ :=
  @letterMk ↥LL.1 ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) _ _ _ _ (mulD P ρ) ℂ _ (algC ι LL) (urC ι) x

def wdMap (T : End ↥LL.1 ↥(Dpst P ρ)) (hT : ∀ c, T * mulD P ρ c = mulD P ρ c * T) :
    End ℂ (WDSpace P ι ρ) :=
  @letterMap ↥LL.1 ↥(MaximalUnramifiedExtension l) ↥(Dpst P ρ) _ _ _ _ (mulD P ρ) ℂ _ (algC ι LL) (urC ι) T hT

@[simp] theorem wdMap_mk (T : End ↥LL.1 ↥(Dpst P ρ)) (hT : ∀ c, T * mulD P ρ c = mulD P ρ c * T)
    (x : ↥(Dpst P ρ)) : wdMap P ι ρ T hT (wdMk P ι ρ x) = wdMk P ι ρ (T x) := rfl

@[simp] theorem wdMk_zero : wdMk P ι ρ 0 = 0 := letI := algC ι LL; letterMk_zero _ _ _

theorem wdMk_smul (a : ↥LL.1) (x : ↥(Dpst P ρ)) :
    wdMk P ι ρ (a • x) = ι (a : Om l) • wdMk P ι ρ x :=
  letI := algC ι LL; letterMk_smul _ _ _ a x

theorem span_wdMk : Submodule.span ℂ (Set.range (wdMk P ι ρ)) = ⊤ :=
  letI := algC ι LL; span_letterMk _ _ _

theorem wd_ext {f g : End ℂ (WDSpace P ι ρ)} (h : ∀ x, f (wdMk P ι ρ x) = g (wdMk P ι ρ x)) : f = g :=
  LinearMap.ext_on_range (span_wdMk P ι ρ) h

def wdN : End ℂ (WDSpace P ι ρ) := wdMap P ι ρ (monD P ρ) (monD_mulD P ρ)

@[simp] theorem wdN_mk (x : ↥(Dpst P ρ)) : wdN P ι ρ (wdMk P ι ρ x) = wdMk P ι ρ (monD P ρ x) := rfl

instance finiteDimensional_wdSpace [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] :
    FiniteDimensional ℂ (WDSpace P ι ρ) :=
  letI := algC ι LL
  finiteDimensional_letter _ _ _
    (fun i => (toUr P ρ).symm (finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) i)) fun x =>
      ⟨_, ((finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)).sum_repr (toUr P ρ x)).symm⟩

theorem isNilpotent_wdN [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] : IsNilpotent (wdN P ι ρ) := by
  obtain ⟨n, hn⟩ := isNilpotent_monD (P := P) (ρ := ρ)
  have hp : ∀ (k : ℕ) x, (wdN P ι ρ ^ k) (wdMk P ι ρ x) = wdMk P ι ρ ((monD P ρ ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, wdN_mk, ih]
  exact ⟨n, wd_ext P ι ρ fun x => by rw [hp, hn]; simp⟩

variable {P ρ} in

theorem IsPst.finite [FiniteDimensional ↥LL.1 V] (hV : IsPst P ρ) :
    FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  hV.finiteDimensional

end Space

end GlobalTheory.Pst
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory

section Multiplicity

variable {G X : Type*} [Group G] [MulAction G X]

variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}

@[to_additive setIntegral_le_mul_of_ae_covers_vadd
]
theorem setIntegral_le_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    (hu0 : ∀ x, 0 ≤ u x) (huB : AEStronglyMeasurable u (μ.restrict B))
    (huD : IntegrableOn u D μ) {m : ℕ}
    (hm : ∀ᵐ x ∂μ.restrict D, {g : G | g • x ∈ B}.encard ≤ m) :
    IntegrableOn u B μ ∧ ∫ x in B, u x ∂μ ≤ m * ∫ x in D, u x ∂μ := by
  have key : ∫⁻ x in B, ENNReal.ofReal (u x) ∂μ ≤ m * ∫⁻ x in D, ENNReal.ofReal (u x) ∂μ := by
    refine setLIntegral_le_mul_of_ae_covers hD hB (fun g x => by rw [hu]) ?_
    filter_upwards [hm] with x hx
    exact_mod_cast ENat.toENNReal_le.2 hx
  have hfin : ∫⁻ x in D, ENNReal.ofReal (u x) ∂μ ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (.of_forall hu0)).1 huD.2).ne
  have hfin' : (m : ℝ≥0∞) * ∫⁻ x in D, ENNReal.ofReal (u x) ∂μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hfin
  refine ⟨⟨huB, (hasFiniteIntegral_iff_ofReal (.of_forall hu0)).2 (key.trans_lt hfin'.lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall hu0) huB,
    integral_eq_lintegral_of_nonneg_ae (.of_forall hu0) huD.1]
  simpa [ENNReal.toReal_mul] using ENNReal.toReal_mono hfin' key

@[to_additive setLIntegral_le_mul_of_isAddFundamentalDomain
]
theorem setLIntegral_le_mul_of_isFundamentalDomain (hD : IsFundamentalDomain G D μ)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_ae_covers hD.ae_covers hB hu (.of_forall hm)

@[to_additive setLIntegral_le_encard_mul_of_ae_covers_vadd
]
theorem setLIntegral_le_encard_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in B, u x ∂μ
      ≤ ({g : G | (g • B ∩ B).Nonempty}.encard : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_ae_covers hD hB hu (.of_forall fun x =>
    ENat.toENNReal_le.2 (encard_smul_mem_le_encard_smul_inter_nonempty B x))

end Multiplicity

section Kernel

variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}

variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]

@[to_additive setLIntegral_le_mul_of_surjective_vadd
]
theorem setLIntegral_le_mul_of_surjective (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_ae_covers (ae_exists_smul_mem_of_surjective hφ hφs hD) hB hu
    (.of_forall hm)

variable {K : Subgroup G} {H' : Type*} [Group H'] [MulAction H' X] {φ' : K →* H'}

@[to_additive setLAverage_eq_of_surjective_vadd
]
theorem setLAverage_eq_of_surjective [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ := by
  have := finiteIndex_map_of_surjective (K := K) hφ
  rw [setLAverage_eq, setLAverage_eq, setLIntegral_eq_index_map_mul hφ hφs hD hφ' hφs' hD' hu,
    measure_eq_index_map_mul hφ hφs hD hφ' hφs' hD', ENNReal.mul_div_mul_left]
  · exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  · exact ENNReal.natCast_ne_top _

@[to_additive setAverage_eq_of_surjective_vadd
]
theorem setAverage_eq_of_surjective [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    (IntegrableOn f D' μ ↔ IntegrableOn f D μ) ∧
      ∫ x in D', f x ∂μ = ((K.map φ).index : ℝ) • ∫ x in D, f x ∂μ ∧
      ⨍ x in D', f x ∂μ = ⨍ x in D, f x ∂μ := by
  have := measurableConstSMul_of_surjective hφ hφs
  have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
  have : Countable H := hφ.countable
  have := finiteIndex_map_of_surjective (K := K) hφ
  have hD'' := isFundamentalDomain_map_of_surjective hφ hφs hD hφ' hφs' hD'
  have hf' : ∀ (h : H) (x : X), f (h • x) = f x := fun h x => by
    obtain ⟨g, rfl⟩ := hφ h
    rw [hφs, hf]
  exact ⟨integrableOn_subgroup_iff hD hD'' hf', setIntegral_subgroup_eq_index_smul hD hD'' hf',
    setAverage_subgroup_eq hD hD'' hf'⟩

end Kernel

end GlobalTheory
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

@[reducible] noncomputable def UpperTheory.Reformulated.B.CovariantDegrees.GQ :
    (l : Nat) → [Fact (Nat.Prime l)] → Type :=
    fun (l : Nat) [inst : Fact (Nat.Prime l)] ↦
      @AlgEquiv (@Padic l inst) (@UpperTheory.Reformulated.B.CovariantDegrees.Om l inst) (@UpperTheory.Reformulated.B.CovariantDegrees.Om l inst)
        (@Semifield.toCommSemiring (@Padic l inst) (@Field.toSemifield (@Padic l inst) (@instFieldPadic l inst)))
        (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.CovariantDegrees.Om l inst)
          (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.CovariantDegrees.Om l inst)
            (@Field.toSemifield (@UpperTheory.Reformulated.B.CovariantDegrees.Om l inst)
              (@AlgebraicClosure.instField (@Padic l inst) (@instFieldPadic l inst)))))
        (@DivisionSemiring.toSemiring (@UpperTheory.Reformulated.B.CovariantDegrees.Om l inst)
          (@Semifield.toDivisionSemiring (@UpperTheory.Reformulated.B.CovariantDegrees.Om l inst)
            (@Field.toSemifield (@UpperTheory.Reformulated.B.CovariantDegrees.Om l inst)
              (@AlgebraicClosure.instField (@Padic l inst) (@instFieldPadic l inst)))))
        (@AlgebraicClosure.instAlgebra (@Padic l inst) (@instFieldPadic l inst) (@Padic l inst)
          (@Semifield.toCommSemiring (@Padic l inst) (@Field.toSemifield (@Padic l inst) (@instFieldPadic l inst)))
          (@Algebra.id (@Padic l inst)
            (@Semifield.toCommSemiring (@Padic l inst) (@Field.toSemifield (@Padic l inst) (@instFieldPadic l inst)))))
        (@AlgebraicClosure.instAlgebra (@Padic l inst) (@instFieldPadic l inst) (@Padic l inst)
          (@Semifield.toCommSemiring (@Padic l inst) (@Field.toSemifield (@Padic l inst) (@instFieldPadic l inst)))
          (@Algebra.id (@Padic l inst)
            (@Semifield.toCommSemiring (@Padic l inst) (@Field.toSemifield (@Padic l inst) (@instFieldPadic l inst)))))
end


