-- Prove2me | Definitions.Def_AlpoGeB006
-- name    : AlpoGeB006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-21T16:32:22.334674+00:00
-- url     : https://prove2.me/theorems/ee307cba-d9c2-48a4-bc06-d9ca90945d98
-- title:
--   Definitions bundle AlpoGeB006 of the alpo.ge GRH release, first cut (Row0b, IsRecT)
-- statement:
--   A definitions bundle of the first cut of L. Alpöge's Lean proof of GRH for Dirichlet $L$-functions (released 20 November 2026, written with Claude; announcement [alpo.ge/remark.pdf](https://alpo.ge/remark.pdf)). The declarations and their proofs are the release's, carved mechanically for this platform: the carve reorders them, restates the namespaces and `open`s each needs, and writes a few declarations from their elaborated form. Two patches are recorded in the carve: an anonymous instance is given its original generated name, and an additive structure that a `to_additive` attribute names is restored beside the structure that names it. The release builds with `maxHeartbeats 4000000` and `maxSynthPendingDepth 3` as project options (and `synthInstance.maxHeartbeats 400000` for its local and global field libraries); since the verifier sets none of these, each carved module section states them as `set_option` lines. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   The first cut publishes the two inputs from which the release concludes its main theorem: `AlpoGe.galoisLocalGlobalStrong_recParameter` (the release's `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`) and `AlpoGe.everyCharacter_of_row` (the release's `UpperTheory.FinalTheorems.everyCharacter_of_row`). These bundles hold the definitions their statements need, with the theorems those definitions use.
--
--   **Contents.** It holds 138 declarations of the release's Lean: 55 definitions, 1 inductive types or structures, 1 instances and 81 theorems. The definitions and types are `GlobalTheory.LocLanglands.IsIrrWD`, `GlobalTheory.LocLanglands.IsLocalArtin`, `GlobalTheory.LocLanglands.IsTameWD`, `GlobalTheory.LocLanglands.cls`, `GlobalTheory.LocLanglands.segSum`, `GlobalTheory.LocLanglands.sumList`, `GlobalTheory.Pst.IsCrysAt`, `GlobalTheory.Pst.IsInduced`, `GlobalTheory.Pst.IsJumpsAt`, `GlobalTheory.Pst.IsModel`, `GlobalTheory.Pst.IsPstAt`, `GlobalTheory.Pst.IsdRAt`, `GlobalTheory.Pst.alpha`, `GlobalTheory.Pst.resDeg`, `GlobalTheory.Pst.trivWD`, `GlobalTheory.Pst.wdAt`, `GlobalTheory.Pst.wdPst`, `GlobalTheory.Pst.wdRep`, `GlobalTheory.Pst.wdRho`, `GlobalTheory.Pst.weilD`, `GlobalTheory.Pst.weilToGK`, `GlobalTheory.WeilDeligne.IsFrobSS`, `GlobalTheory.WeilDeligne.IsMonodromy`, `GlobalTheory.WeilDeligne.IsTameChar`, `GlobalTheory.WeilDeligne.WD`, `GlobalTheory.WeilDeligne.WD.charPol`, `GlobalTheory.WeilDeligne.WD.eig`, `GlobalTheory.WeilDeligne.WD.lpChar`, `GlobalTheory.WeilDeligne.WD.lpDim`, `GlobalTheory.WeilDeligne.WD.lpDual`, `GlobalTheory.WeilDeligne.WD.lpSp`, `GlobalTheory.WeilDeligne.WD.lpSum`, `GlobalTheory.WeilDeligne.WD.lpTw`, `GlobalTheory.WeilDeligne.WD.lpTwist`, `GlobalTheory.WeilDeligne.WD.lpZero`, `GlobalTheory.WeilDeligne.WD.mk`, `GlobalTheory.WeilDeligne.WD.mono0`, `GlobalTheory.WeilDeligne.WD.std`, `GlobalTheory.WeilDeligne.WDRep.Iso`, `GlobalTheory.WeilDeligne.WDRep.Mono0`, `GlobalTheory.WeilDeligne.WDRep.diag`, `GlobalTheory.WeilDeligne.WDRep.dual`, `GlobalTheory.WeilDeligne.WDRep.ofChars`, `GlobalTheory.WeilDeligne.WDRep.ofMatrix`, `GlobalTheory.WeilDeligne.WDRep.sp`, `GlobalTheory.WeilDeligne.WDRep.spEig`, `GlobalTheory.WeilDeligne.WDRep.tensor`, `GlobalTheory.WeilDeligne.WDRep.toGL`, `GlobalTheory.WeilDeligne.WDRep.transport`, `GlobalTheory.WeilDeligne.WDRep.tw`, `GlobalTheory.WeilDeligne.WDRep.twist`, `GlobalTheory.WeilDeligne.ineConj`, `GlobalTheory.WeilDeligne.isoSetoid`, `GlobalTheory.WeilDeligne.kummer`, `GlobalTheory.WeilDeligne.kummerChar`, `GlobalTheory.WeilDeligne.tval`. It imports the bundles `Def_AlpoGeB004`, `Def_AlpoGeB005`.
-- source:
--   L. Alpöge, working with Claude, Lean formalization of the Riemann hypothesis and of GRH for Dirichlet L-functions, released 20 November 2026 (announcement https://alpo.ge/remark.pdf; Lean archive https://alpo.ge/lean.tar.gz.part01 to part14, joined tarball sha256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc)

import Mathlib
import Definitions.Def_AlpoGeB004
import Definitions.Def_AlpoGeB005

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.charZero_of_charZero _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

variable (h : IsPlaceOver A w)

theorem Weil_le_Dec : Weil h ≤ Dec (F := E) A := fun _ ⟨_, _, hσ⟩ => hσ.1

variable {h}

variable [IsAlgClosure E Ω]

omit [IsAlgClosure E Ω] in

theorem qPow_add (s t : ℝ) : qPow w (s + t) = qPow w s * qPow w t := Units.ext (by
  simp only [coe_qPow, Units.val_mul, Complex.ofReal_add]
  exact Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot))

theorem compactSpace_Ine (A : ValuationSubring Ω) : CompactSpace (Ine (F := E) A) := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  exact isCompact_iff_compactSpace.mp (isClosed_Ine A).isCompact

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.Pst.finiteDimensional_wdSpace _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.charZero_of_charZero _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.AinfInv.instIsScalarTowerPadicIntPadic _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerPadicAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem IsSmooth.of_trivial {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    (hf : ∀ σ, f (ineIncl h σ) = 1) : IsSmooth f :=
  .of_open isOpen_univ trivial fun σ _ => hf σ

variable [IsAlgClosure E Ω]

theorem IsSmooth.finite_range {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    (hf : IsSmooth f) : (Set.range fun σ : Ine (F := E) A => f (ineIncl h σ)).Finite := by
  have := compactSpace_Ine (E := E) A
  have : Finite (Ine (F := E) A ⧸ (f.comp (ineIncl h)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hf
  refine (Set.finite_range (QuotientGroup.lift (f.comp (ineIncl h)).ker (f.comp (ineIncl h))
    le_rfl)).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨QuotientGroup.mk σ, rfl⟩

theorem isSmooth_unrChar (h : IsPlaceOver A w) (c : ℂˣ) : IsSmooth (unrChar h c) :=
  .of_trivial fun σ => by simp

namespace WDRep

variable {h : IsPlaceOver A w}
variable {V V' V'' V''' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
  [AddCommGroup V'''] [Module ℂ V'''] [FiniteDimensional ℂ V''']

def Iso (a : WDRep h V) (b : WDRep h V') : Prop :=
  ∃ e : V ≃ₗ[ℂ] V', (∀ σ v, e (a.ρ σ v) = b.ρ σ (e v)) ∧ ∀ v, e (a.N v) = b.N (e v)

theorem Iso.refl (a : WDRep h V) : a.Iso a := ⟨.refl _ _, fun _ _ => rfl, fun _ => rfl⟩

theorem Iso.symm {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : b.Iso a := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨e.symm, fun σ v => by simp [e.symm_apply_eq, h1], fun v => by simp [e.symm_apply_eq, h2]⟩

theorem Iso.trans {a : WDRep h V} {b : WDRep h V'} {c : WDRep h V''} (hab : a.Iso b) (hbc : b.Iso c) :
    a.Iso c := by
  obtain ⟨e, h1, h2⟩ := hab
  obtain ⟨e', h1', h2'⟩ := hbc
  exact ⟨e.trans e', fun σ v => by simp [h1, h1'], fun v => by simp [h2, h2']⟩

def transport (a : WDRep h V) (e : V ≃ₗ[ℂ] V') : WDRep h V' where
  ρ := (e.conjAlgEquiv ℂ : End ℂ V →* End ℂ V').comp a.ρ
  N := e.conjAlgEquiv ℂ a.N
  smooth := a.smooth.of_le fun σ hσ => by simp [hσ]
  semisimple σ := isSemisimple_map (e.conjAlgEquiv ℂ : End ℂ V →ₐ[ℂ] End ℂ V') (a.semisimple σ)
  nilpotent := a.nilpotent.map (e.conjAlgEquiv ℂ)
  comm σ := by
    show e.conjAlgEquiv ℂ (a.ρ σ) * _ = _ • (_ * e.conjAlgEquiv ℂ (a.ρ σ))
    rw [← map_mul, a.comm, map_smul, map_mul]

theorem iso_transport (a : WDRep h V) (e : V ≃ₗ[ℂ] V') : a.Iso (a.transport e) :=
  ⟨e, fun σ v => by
    show _ = e.conjAlgEquiv ℂ (a.ρ σ) (e v)
    simp, fun v => by simp [transport]⟩

@[simp] theorem sum_ρ (a : WDRep h V) (b : WDRep h V') (σ : Weil h) :
    (a.sum b).ρ σ = (a.ρ σ).prodMap (b.ρ σ) := rfl

@[simp] theorem sum_N (a : WDRep h V) (b : WDRep h V') : (a.sum b).N = a.N.prodMap b.N := rfl

theorem Iso.sum {a : WDRep h V} {a' : WDRep h V'} {b : WDRep h V''} {b' : WDRep h V'''} (ha : a.Iso a')
    (hb : b.Iso b') : (a.sum b).Iso (a'.sum b') := by
  obtain ⟨e, h1, h2⟩ := ha
  obtain ⟨e', h1', h2'⟩ := hb
  exact ⟨e.prodCongr e', fun σ v => Prod.ext (h1 σ v.1) (h1' σ v.2),
    fun v => Prod.ext (h2 v.1) (h2' v.2)⟩

def twist (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : WDRep h V where
  ρ := { toFun := fun σ => (χ σ : ℂ) • a.ρ σ
         map_one' := by simp
         map_mul' := fun σ τ => by simp [smul_smul, mul_comm] }
  N := a.N
  smooth := a.smooth.of_le₂ hχ fun σ h1 h2 => by simp [h1, h2]
  semisimple σ := End.IsSemisimple_smul _ (a.semisimple σ)
  nilpotent := a.nilpotent
  comm σ := by
    show ((χ σ : ℂ) • a.ρ σ) * a.N = _ • (a.N * ((χ σ : ℂ) • a.ρ σ))
    rw [smul_mul_assoc, a.comm, mul_smul_comm, smul_comm]

@[simp] theorem twist_ρ (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) (σ : Weil h) :
    (a.twist χ hχ).ρ σ = (χ σ : ℂ) • a.ρ σ := rfl

@[simp] theorem twist_N (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    (a.twist χ hχ).N = a.N := rfl

theorem Iso.twist {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (χ : Weil h →* ℂˣ)
    (hχ : IsSmooth χ) : (a.twist χ hχ).Iso (b.twist χ hχ) := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨e, fun σ v => by simp [h1], h2⟩

def tw (a : WDRep h V) (s : ℝ) : WDRep h V := a.twist (unrChar h (qPow w s)) (isSmooth_unrChar h _)

@[simp] theorem tw_ρ (a : WDRep h V) (s : ℝ) (σ : Weil h) :
    (a.tw s).ρ σ = (((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) ^ deg σ • a.ρ σ := by
  simp [tw]

@[simp] theorem tw_N (a : WDRep h V) (s : ℝ) : (a.tw s).N = a.N := rfl

def tensor (a : WDRep h V) (b : WDRep h V') : WDRep h (V ⊗[ℂ] V') where
  ρ := a.ρ.tprod b.ρ
  N := a.N.rTensor V' + b.N.lTensor V
  smooth := a.smooth.of_le₂ b.smooth fun σ h1 h2 => by
    rw [Representation.tprod_apply, h1, h2, TensorProduct.map_one]
  semisimple σ := isSemisimple_tensorMap (a.semisimple σ) (b.semisimple σ)
  nilpotent := by
    refine Commute.isNilpotent_add ?_ (a.nilpotent.map (End.rTensorAlgHom ℂ V V'))
      (b.nilpotent.map (End.lTensorAlgHom ℂ V' V))
    show _ = _
    ext; simp
  comm σ := by
    ext x y
    simp [a.comm_apply, b.comm_apply, smul_tmul']

@[simp] theorem tensor_ρ (a : WDRep h V) (b : WDRep h V') (σ : Weil h) :
    (a.tensor b).ρ σ = TensorProduct.map (a.ρ σ) (b.ρ σ) := rfl

@[simp] theorem tensor_N (a : WDRep h V) (b : WDRep h V') :
    (a.tensor b).N = a.N.rTensor V' + b.N.lTensor V := rfl

theorem Iso.tensor {a : WDRep h V} {a' : WDRep h V'} {b : WDRep h V''} {b' : WDRep h V'''} (ha : a.Iso a')
    (hb : b.Iso b') : (a.tensor b).Iso (a'.tensor b') := by
  obtain ⟨e, h1, h2⟩ := ha
  obtain ⟨e', h1', h2'⟩ := hb
  refine ⟨TensorProduct.congr e e', fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [h1, h1']
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [h2, h2']
    | add x y hx hy => simp only [map_add, hx, hy]

def dual (a : WDRep h V) : WDRep h (Dual ℂ V) where
  ρ := a.ρ.dual
  N := -a.N.dualMap
  smooth := a.smooth.of_le fun σ hσ => by
    have : a.ρ σ⁻¹ = 1 := by
      rw [← one_mul (a.ρ σ⁻¹), ← hσ, ← map_mul, mul_inv_cancel, map_one, hσ]
    ext; simp [Dual.transpose_apply, this]
  semisimple σ := isSemisimple_dualMap (a.semisimple σ⁻¹)
  nilpotent := by
    obtain ⟨n, hn⟩ := a.nilpotent
    refine IsNilpotent.neg ⟨n, ?_⟩
    rw [← aeval_X_pow (R := ℂ), aeval_dualMap, aeval_X_pow, hn]
    ext; simp
  comm σ := by
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
    ext f v
    simp [Dual.transpose_apply, a.comm_apply, zpow_ne_zero _ hq]

@[simp] theorem dual_ρ (a : WDRep h V) (σ : Weil h) : a.dual.ρ σ = (a.ρ σ⁻¹).dualMap := rfl

@[simp] theorem dual_N (a : WDRep h V) : a.dual.N = -a.N.dualMap := rfl

theorem Iso.dual {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : a.dual.Iso b.dual := by
  obtain ⟨e, h1, h2⟩ := hab.symm
  exact ⟨e.dualMap, fun σ f => by ext; simp [h1], fun f => by ext; simp [h2]⟩

variable (h) in

def ofChars {ι : Type*} [Finite ι] (χ : ι → Weil h →* ℂˣ) (hχ : ∀ i, IsSmooth (χ i)) :
    WDRep h (ι → ℂ) where
  ρ := { toFun := fun σ => diagEnd fun i => (χ i σ : ℂ)
         map_one' := by ext; simp
         map_mul' := fun σ τ => LinearMap.ext fun v => funext fun i => by simp [mul_assoc] }
  N := 0
  smooth := .of_open (isOpen_iInter_of_finite hχ) (by simp) fun σ hσ =>
    LinearMap.ext fun v => funext fun i => by
      have : χ i (ineIncl h σ) = 1 := Set.mem_iInter.mp hσ i
      simp [this]
  semisimple σ := isSemisimple_diagEnd _
  nilpotent := IsNilpotent.zero
  comm σ := by simp

@[simp] theorem ofChars_ρ {ι : Type*} [Finite ι] (χ : ι → Weil h →* ℂˣ)
    (hχ : ∀ i, IsSmooth (χ i)) (σ : Weil h) :
    (ofChars h χ hχ).ρ σ = diagEnd fun i => (χ i σ : ℂ) := rfl

@[simp] theorem ofChars_N {ι : Type*} [Finite ι] (χ : ι → Weil h →* ℂˣ)
    (hχ : ∀ i, IsSmooth (χ i)) : (ofChars h χ hχ).N = 0 := rfl

variable (h) in

def diag {ι : Type*} [Finite ι] (c : ι → ℂˣ) : WDRep h (ι → ℂ) :=
  ofChars h (fun i => unrChar h (c i)) fun _ => isSmooth_unrChar h _

@[simp] theorem diag_ρ {ι : Type*} [Finite ι] (c : ι → ℂˣ) (σ : Weil h) :
    (diag h c).ρ σ = diagEnd fun i => (c i : ℂ) ^ deg σ := by
  simp [diag]

@[simp] theorem diag_N {ι : Type*} [Finite ι] (c : ι → ℂˣ) : (diag h c).N = 0 := rfl

variable (w) in

def spEig (n : ℕ) (i : Fin n) : ℂˣ := qPow w (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2)

variable (h) in

def sp (n : ℕ) : WDRep h (Fin n → ℂ) where
  ρ := (diag h (spEig w n)).ρ
  N := shiftEnd n
  smooth := (diag h _).smooth
  semisimple := (diag h _).semisimple
  nilpotent := isNilpotent_shiftEnd n
  comm σ := LinearMap.ext fun v => funext fun i => by
    simp only [diag_ρ, End.mul_apply, diagEnd_apply, LinearMap.smul_apply, Pi.smul_apply,
      shiftEnd_apply, smul_eq_mul]
    split_ifs with hi
    · have : (spEig w n i : ℂ) = ((normV w : ℕ) : ℂ) * spEig w n ⟨i - 1, by omega⟩ := by
        rw [← coe_qPow_one, spEig, spEig, ← Units.val_mul, ← qPow_add]
        congr 2
        rw [Nat.cast_sub hi]; push_cast; ring
      rw [this, mul_zpow, mul_assoc]
    · simp

@[simp] theorem sp_ρ (n : ℕ) (σ : Weil h) :
    (sp h n).ρ σ = diagEnd fun i => (spEig w n i : ℂ) ^ deg σ := diag_ρ _ _

@[simp] theorem sp_N (n : ℕ) : (sp h n).N = shiftEnd n := rfl

def ofMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Weil h →* GL ι ℂ) (N : Matrix ι ι ℂ)
    (smooth : IsSmooth ρ)
    (semisimple : ∀ σ, End.IsSemisimple (Matrix.toLin' (ρ σ : Matrix ι ι ℂ)))
    (nilpotent : IsNilpotent N)
    (comm : ∀ σ, (ρ σ : Matrix ι ι ℂ) * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)) :
    WDRep h (ι → ℂ) where
  ρ := ((Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] End ℂ (ι → ℂ)) :
    Matrix ι ι ℂ →* End ℂ (ι → ℂ)).comp ((Units.coeHom _).comp ρ)
  N := Matrix.toLin' N
  smooth := smooth.of_le fun σ hσ => by simp [hσ]
  semisimple := semisimple
  nilpotent := nilpotent.map (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] End ℂ (ι → ℂ))
  comm σ := by
    have := congrArg (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] End ℂ (ι → ℂ)) (comm σ)
    rw [map_mul, map_smul, map_mul] at this
    exact this

@[simp] theorem ofMatrix_ρ {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Weil h →* GL ι ℂ)
    (N : Matrix ι ι ℂ) (h1 h2 h3 h4) (σ : Weil h) :
    (ofMatrix ρ N h1 h2 h3 h4).ρ σ = Matrix.toLin' (ρ σ : Matrix ι ι ℂ) := rfl

@[simp] theorem ofMatrix_N {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Weil h →* GL ι ℂ)
    (N : Matrix ι ι ℂ) (h1 h2 h3 h4) : (ofMatrix ρ N h1 h2 h3 h4).N = Matrix.toLin' N := rfl

def toGL {ι : Type*} [Fintype ι] [DecidableEq ι] (a : WDRep h (ι → ℂ)) : Weil h →* GL ι ℂ :=
  (((LinearMap.toMatrixAlgEquiv' : End ℂ (ι → ℂ) ≃ₐ[ℂ] Matrix ι ι ℂ) :
    End ℂ (ι → ℂ) →* Matrix ι ι ℂ).comp a.ρ).toHomUnits

@[simp] theorem coe_toGL {ι : Type*} [Fintype ι] [DecidableEq ι] (a : WDRep h (ι → ℂ))
    (σ : Weil h) : (a.toGL σ : Matrix ι ι ℂ) = LinearMap.toMatrix' (a.ρ σ) := rfl

def Mono0 (a : WDRep h V) : Prop := a.N = 0

theorem Iso.finrank_eq {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) :
    finrank ℂ V = finrank ℂ V' := hab.choose.finrank_eq

theorem Iso.charpoly_eq {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (σ : Weil h) :
    (a.ρ σ).charpoly = (b.ρ σ).charpoly := by
  obtain ⟨e, h1, -⟩ := hab
  rw [← LinearEquiv.charpoly_conj e]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply, h1]

theorem Iso.mono0 {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) (ha : a.Mono0) : b.Mono0 := by
  obtain ⟨e, -, h2⟩ := hab
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := e.surjective v
  rw [← h2, show a.N = 0 from ha]; simp

end WDRep

def isoSetoid (h : IsPlaceOver A w) : Setoid (Σ n : ℕ, WDRep h (Fin n → ℂ)) where
  r a b := a.2.Iso b.2
  iseqv := ⟨fun a => .refl a.2, WDRep.Iso.symm, WDRep.Iso.trans⟩

def WD (h : IsPlaceOver A w) : Type _ := Quotient (isoSetoid h)

namespace WD

variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def std (a : WDRep h V) : Σ n : ℕ, WDRep h (Fin n → ℂ) :=
  ⟨finrank ℂ V, a.transport (finBasis ℂ V).equivFun⟩

theorem iso_std (a : WDRep h V) : a.Iso (std a).2 := a.iso_transport _

def mk (a : WDRep h V) : WD h := Quotient.mk (isoSetoid h) (std a)

theorem mk_eq_mk {a : WDRep h V} {b : WDRep h V'} : mk a = mk b ↔ a.Iso b := by
  refine Quotient.eq.trans ⟨fun hab => ?_, fun hab => ?_⟩
  · exact ((iso_std a).trans hab).trans (iso_std b).symm
  · exact ((iso_std a).symm.trans hab).trans (iso_std b)

theorem sound {a : WDRep h V} {b : WDRep h V'} (hab : a.Iso b) : mk a = mk b := mk_eq_mk.mpr hab

def lpDim (x : WD h) : ℕ :=
  Quotient.lift (s := isoSetoid h) (fun a => finrank ℂ (Fin a.1 → ℂ))
    (fun _ _ hab => WDRep.Iso.finrank_eq hab) x

@[simp] theorem lpDim_mk (a : WDRep h V) : lpDim (mk a) = finrank ℂ V :=
  (iso_std a).finrank_eq.symm

def lpSum (x y : WD h) : WD h :=
  Quotient.lift₂ (s₁ := isoSetoid h) (s₂ := isoSetoid h) (fun a b => mk (a.2.sum b.2))
    (fun _ _ _ _ ha hb => sound (WDRep.Iso.sum ha hb)) x y

@[simp] theorem lpSum_mk (a : WDRep h V) (b : WDRep h V') :
    lpSum (mk a) (mk b) = mk (a.sum b) :=
  sound ((iso_std a).sum (iso_std b)).symm

def lpTwist (x : WD h) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) : WD h :=
  Quotient.lift (s := isoSetoid h) (fun a => mk (a.2.twist χ hχ))
    (fun _ _ hab => sound (WDRep.Iso.twist hab χ hχ)) x

@[simp] theorem lpTwist_mk (a : WDRep h V) (χ : Weil h →* ℂˣ) (hχ : IsSmooth χ) :
    lpTwist (mk a) χ hχ = mk (a.twist χ hχ) :=
  sound ((iso_std a).twist χ hχ).symm

def lpTw (x : WD h) (s : ℝ) : WD h := lpTwist x (unrChar h (qPow w s)) (isSmooth_unrChar h _)

@[simp] theorem lpTw_mk (a : WDRep h V) (s : ℝ) : lpTw (mk a) s = mk (a.tw s) := lpTwist_mk _ _ _

def lpChar (x y : WD h) : WD h :=
  Quotient.lift₂ (s₁ := isoSetoid h) (s₂ := isoSetoid h) (fun a b => mk (a.2.tensor b.2))
    (fun _ _ _ _ ha hb => sound (WDRep.Iso.tensor ha hb)) x y

@[simp] theorem lpChar_mk (a : WDRep h V) (b : WDRep h V') :
    lpChar (mk a) (mk b) = mk (a.tensor b) :=
  sound ((iso_std a).tensor (iso_std b)).symm

def lpDual (x : WD h) : WD h :=
  Quotient.lift (s := isoSetoid h) (fun a => mk a.2.dual)
    (fun _ _ hab => sound (WDRep.Iso.dual hab)) x

@[simp] theorem lpDual_mk (a : WDRep h V) : lpDual (mk a) = mk a.dual :=
  sound (iso_std a).dual.symm

variable (h) in

def lpZero : WD h := mk (WDRep.diag h (ι := Fin 0) fun i => i.elim0)

variable (h) in

def lpSp (n : ℕ) : WD h := mk (WDRep.sp h n)

def mono0 (x : WD h) : Prop :=
  Quotient.lift (s := isoSetoid h) (fun a => a.2.Mono0)
    (fun _ _ hab => propext ⟨WDRep.Iso.mono0 hab, (WDRep.Iso.symm hab).mono0⟩) x

@[simp] theorem monodromyZero_ofWeilDeligneRepClass_iff (a : WDRep h V) : mono0 (mk a) ↔ a.N = 0 :=
  ⟨(iso_std a).symm.mono0, (iso_std a).mono0⟩

def charPol (x : WD h) (σ : Weil h) : ℂ[X] :=
  Quotient.lift (s := isoSetoid h) (fun a => (a.2.ρ σ).charpoly)
    (fun _ _ hab => WDRep.Iso.charpoly_eq hab σ) x

@[simp] theorem charPol_mk (a : WDRep h V) (σ : Weil h) : charPol (mk a) σ = (a.ρ σ).charpoly :=
  ((iso_std a).charpoly_eq σ).symm

def eig (x : WD h) (σ : Weil h) : Multiset ℂ := (charPol x σ).roots

@[simp] theorem eig_mk (a : WDRep h V) (σ : Weil h) : eig (mk a) σ = (a.ρ σ).charpoly.roots := by
  rw [eig, charPol_mk]

@[simp] theorem lpDim_lpSp (n : ℕ) : lpDim (lpSp h n) = n := by simp [lpSp]

end WD

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.charZero_of_charZero _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

section Kummer

variable (l : ℕ) [Fact l.Prime]

theorem existsUnique_kummer (a : Eˣ) (σ : G E Ω) :
    ∃! c : ℤ_[l], ∀ n, σ (rootOf Ω l (a : E) n) = zetaPow E Ω l n c * rootOf Ω l (a : E) n := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have h := existsUnique_unityPow l (y := fun n => σ (rootOf Ω l (a : E) n) / rootOf Ω l (a : E) n)
    (fun n => by
      rw [div_pow, ← map_pow, rootOf_pow, AlgEquiv.commutes, div_self (by simp)])
    (fun n => by
      rw [div_pow, ← map_pow]
      exact congrArg (fun x => σ x / x) (rootSeq_succ_pow l _ n))
  have e : ∀ n y z : Ω, z ≠ 0 → (y / z = n ↔ y = n * z) := fun _ _ _ hz => div_eq_iff hz
  simp only [e _ _ _ (rootOf_ne_zero l a.ne_zero _)] at h
  exact h

def kummer (a : Eˣ) (σ : G E Ω) : ℤ_[l] := (existsUnique_kummer l a σ).exists.choose

theorem kummer_spec (a : Eˣ) (σ : G E Ω) (n : ℕ) :
    σ (rootOf Ω l (a : E) n) = zetaPow E Ω l n (kummer l a σ) * rootOf Ω l (a : E) n :=
  (existsUnique_kummer l a σ).exists.choose_spec n

theorem apply_zetaPow (σ : G E Ω) (n : ℕ) (c : ℤ_[l]) :
    σ (zetaPow E Ω l n c) = zetaPow E Ω l n ((cycZ E Ω l σ : ℤ_[l]ˣ) * c) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  exact (cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G E Ω) Ω σ) _
    (unityPow_pow Ω l n c)).trans (unityPow_mul Ω l n _ c).symm

theorem kummer_mul (a : Eˣ) (σ τ : G E Ω) :
    kummer l a (σ * τ) = kummer l a σ + (cycZ E Ω l σ : ℤ_[l]ˣ) * kummer l a τ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  refine (existsUnique_kummer l a (σ * τ)).unique (kummer_spec l a _) fun n => ?_
  rw [AlgEquiv.mul_apply, kummer_spec, map_mul, apply_zetaPow, kummer_spec, ← mul_assoc, add_comm]
  congr 1
  exact (unityPow_add Ω l n _ _).symm

@[simp] theorem kummer_one (a : Eˣ) : kummer l a (1 : G E Ω) = 0 := by
  simpa using kummer_mul l a (1 : G E Ω) 1

end Kummer

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]

theorem cycZ_of_mem_Ine (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {σ : G E Ω}
    (hσ : σ ∈ Ine (F := E) A) : cycZ E Ω l σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycZ_toZModPow_eq hl h (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
  simp

def ineConj {h : IsPlaceOver A w} (g : Weil h) (σ : Ine (F := E) A) : Ine (F := E) A :=
  ⟨(g : G E Ω) * σ * (g : G E Ω)⁻¹, conj_mem_Ine (Weil_le_Dec h g.2) σ.2⟩

omit [IsAlgClosure E Ω] in

@[simp] theorem ineIncl_ineConj {h : IsPlaceOver A w} (g : Weil h) (σ : Ine (F := E) A) :
    ineIncl h (ineConj g σ) = g * ineIncl h σ * g⁻¹ := rfl

omit [IsAlgClosure E Ω] in

@[simp] theorem coe_ineConj {h : IsPlaceOver A w} (g : Weil h) (σ : Ine (F := E) A) :
    (ineConj g σ : G E Ω) = (g : G E Ω) * σ * (g : G E Ω)⁻¹ := rfl

def kummerChar (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (a : Eˣ) :
    Ine (F := E) A →* Multiplicative ℤ_[l] :=
  MonoidHom.mk' (fun σ => Multiplicative.ofAdd (kummer l a (σ : G E Ω))) fun σ τ => by
    rw [Subgroup.coe_mul, kummer_mul, cycZ_of_mem_Ine h hl σ.2, Units.val_one, one_mul, ofAdd_add]

@[simp] theorem toAdd_kummerChar (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (a : Eˣ)
    (σ : Ine (F := E) A) : (kummerChar h hl a σ).toAdd = kummer l a (σ : G E Ω) := rfl

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmooth
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

open NumberField IsDedekindDomain Polynomial Module in

theorem _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
    _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ σ τ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg σ = _root_.GlobalTheory.WeilDeligne.deg τ →
      ∃ m : ℕ, 0 < m ∧ ρ σ ^ m = ρ τ ^ m := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ σ τ hdeg
  let x : ℕ → _root_.GlobalTheory.WeilDeligne.Weil h := fun k ↦ (τ ^ k)⁻¹ * σ ^ k
  have hmem : ∀ k, ρ (x k) ∈ Set.range fun ι ↦ ρ (_root_.GlobalTheory.WeilDeligne.ineIncl h ι) := by
    intro k
    have h0 : _root_.GlobalTheory.WeilDeligne.deg (x k) = 0 := by
      simp only [x, _root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_inv, _root_.GlobalTheory.WeilDeligne.deg_pow, hdeg]
      ring
    refine ⟨⟨_, _root_.GlobalTheory.WeilDeligne.deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only
    congr 1
  obtain ⟨k, l, hkl, hρkl⟩ :=
    Set.Finite.exists_lt_map_eq_of_forall_mem hmem hρ.finite_range
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hkl
  have hx : ρ (x k) = ρ (x (k + m + 1)) := hρkl
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  have key : σ ^ (m + 1) = τ ^ (k + m + 1) * x (k + m + 1) * (x k)⁻¹ * (τ ^ k)⁻¹ := by
    simp only [x]
    group
  have key' : τ ^ (m + 1) = τ ^ (k + m + 1) * (τ ^ k)⁻¹ := by
    group
  have hinv : ρ (x k) * ρ (x k)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [← map_pow, ← map_pow, key, key']
  simp only [map_mul]
  rw [← hx, mul_assoc (ρ _) (ρ (x k)), hinv, mul_one]

end GlobalTheory.WeilDeligne
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqPowOfWeilDegreeEqSmoothStatement
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V), IsSmooth ρ → ∀ σ τ : Weil h, deg σ = deg τ → ∃ m : ℕ, 0 < m ∧ ρ σ ^ m = ρ τ ^ m := by
  first | exact @GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq | exact GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq | (intros; apply GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq <;> assumption)
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.AinfInv.instIsScalarTowerPadicIntPadic _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerPadicAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

open NumberField IsDedekindDomain Polynomial Module in

theorem _root_.GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type)
      [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
      _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ φ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg φ = 1 →
      End.IsSemisimple (ρ φ) → ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, End.IsSemisimple (ρ σ) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ φ hφ hss σ
  have hunit : IsUnit (ρ σ) := (Group.isUnit σ).map ρ
  obtain ⟨τ, hτdeg, hτ⟩ : ∃ τ : _root_.GlobalTheory.WeilDeligne.Weil h,
      _root_.GlobalTheory.WeilDeligne.deg τ = _root_.GlobalTheory.WeilDeligne.deg σ ∧ End.IsSemisimple (ρ τ) := by
    rcases le_or_gt 0 (_root_.GlobalTheory.WeilDeligne.deg σ) with hd | hd
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hd
      refine ⟨φ ^ k, by rw [_root_.GlobalTheory.WeilDeligne.deg_pow, hφ, hk]; ring, ?_⟩
      rw [map_pow]
      exact hss.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
    · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hd.le
      have hinv : End.IsSemisimple (ρ φ⁻¹) :=
        isSemisimple_of_mul_eq_one' hss (by rw [← map_mul, inv_mul_cancel, map_one])
      refine ⟨φ⁻¹ ^ k, ?_, ?_⟩
      · rw [_root_.GlobalTheory.WeilDeligne.deg_pow, ← zpow_neg_one, _root_.GlobalTheory.WeilDeligne.deg_zpow, hφ, hk]
        ring
      · rw [map_pow]
        exact hinv.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
  obtain ⟨m, hm, hpow⟩ :=
    _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ σ τ hτdeg.symm
  apply isSemisimple_of_isUnit_of_pow_isSemisimple hunit hm
  rw [hpow]
  exact hτ.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) m)

end GlobalTheory.WeilDeligne
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrobStatement
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V), IsSmooth ρ → ∀ φ : Weil h, deg φ = 1 → End.IsSemisimple (ρ φ) → ∀ σ : Weil h, End.IsSemisimple (ρ σ) := by
  first | exact @GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob | exact GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob | (intros; apply GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob <;> assumption)
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrobeniusSemisimplification
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.domOCb _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Acris.instAlgebraAcrisZero _root_.Reformulated.AutPerF.Acris.instAlgebraAinf _root_.Reformulated.AutPerF.Acris.instIsScalarTowerAinfAcrisZero _root_.Reformulated.AutPerF.Acris.instIsScalarTowerPadicIntAinf _root_.Reformulated.AutPerF.Ainf.charZero_of_charZero _root_.Reformulated.AutPerF.Ainf.instAlgebraPadicInt _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.instAlgebraPadic _root_.Reformulated.AutPerF.AinfInv.instAlgebraRat _root_.Reformulated.AutPerF.AinfInv.instIsScalarTowerPadicIntPadic _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinf _root_.Reformulated.AutPerF.BdRPlus.instAlgebraAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerAinfAinfInv _root_.Reformulated.AutPerF.BdRPlus.instIsScalarTowerPadicAinfInv _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.GlobalTheory.WeilDeligne.coe_ineConj _root_.GlobalTheory.WeilDeligne.ineIncl_ineConj _root_.GlobalTheory.WeilDeligne.kummer_one _root_.GlobalTheory.WeilDeligne.toAdd_kummerChar
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_frobenius_semisimplification : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V) (N : End ℂ V), IsSmooth ρ → IsNilpotent N → (∀ σ, ρ σ * N = ((normV w : ℕ) : ℂ) ^ deg σ • (N * ρ σ)) → ∃ (a : WDRep h V) (u : (End ℂ V)ˣ), a.N = N ∧ IsNilpotent ((u : End ℂ V) - 1) ∧ Commute (u : End ℂ V) N ∧ (∀ σ, Commute (u : End ℂ V) (ρ σ)) ∧ ∀ σ, ρ σ = a.ρ σ * ((u ^ deg σ : (End ℂ V)ˣ) : End ℂ V) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ N hρ hN hc
  obtain ⟨n, hn, s, hs, hnil, hss, hf⟩ := End.exists_isNilpotent_isSemisimple (f := ρ (frob h))
  set f := ρ (frob h) with hfdef
  have hfn : Commute f n := Algebra.commute_of_mem_adjoin_self hn
  have hfs : Commute f s := Algebra.commute_of_mem_adjoin_self hs
  have hsub : f - s = n := by rw [hf]; simp
  have hns : Commute n s := by rw [← hsub]; exact hfs.sub_left (Commute.refl s)
  have hfu : IsUnit f := (Group.isUnit (frob h)).map ρ
  have hsu : IsUnit s := by
    have : s = f + -n := by rw [← hsub]; simp
    rw [this]
    exact hnil.neg.isUnit_add_left_of_commute hfu hfn.symm.neg_left
  obtain ⟨S, rfl⟩ := hsu
  obtain ⟨F, hF⟩ := hfu
  have hFS : Commute F S := by
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hF]; exact hfs.eq)
  set u : (End ℂ V)ˣ := S⁻¹ * F with hu
  have huS : Commute u S := (Commute.refl S).inv_left.mul_left hFS
  have hSu : S * u = F := by simp [hu]
  have hSu' : (S : End ℂ V) * u = f := by rw [← Units.val_mul, hSu, hF]
  have huS' : Commute (u : End ℂ V) (S : End ℂ V) := huS.units_val
  have hunil : IsNilpotent ((u : End ℂ V) - 1) := by
    have : (u : End ℂ V) - 1 = n * (S⁻¹ : (End ℂ V)ˣ) := by
      rw [hns.units_inv_right.eq, ← hsub, hu, Units.val_mul, hF, mul_sub]; simp
    rw [this]
    exact hns.units_inv_right.isNilpotent_mul_right hnil
  have huN : Commute (u : End ℂ V) N := by
    have h1 := hc (frob h)
    have h2 := semisimplePart_mul_eq hfs hss (hsub ▸ hnil) h1
    have hq : ((normV w : ℕ) : ℂ) ^ deg (frob h) ≠ 0 :=
      zpow_ne_zero _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot)
    have h3 : (S : End ℂ V) * ((u : End ℂ V) * N) = S * (N * u) := by
      rw [← mul_assoc, hSu', h1, ← mul_assoc, h2, smul_mul_assoc, mul_assoc, hSu']
    exact (Units.mul_right_inj S).mp h3
  have huρ : ∀ τ, Commute (u : End ℂ V) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, e⟩ := GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth E Ω A w h V ρ hρ (frob h) (τ * frob h * τ⁻¹) (by simp)
    have c1 : f ^ m * ρ τ = (1 : ℂ) • (ρ τ * f ^ m) := by
      rw [one_smul]
      conv_lhs => rw [hfdef, e]
      rw [hfdef, ← map_pow, ← map_pow, ← map_mul, ← map_mul, conj_pow]
      simp
    have epow : f ^ m = (S : End ℂ V) ^ m * (u : End ℂ V) ^ m := by
      rw [← huS'.symm.mul_pow, hSu']
    have c2 := semisimplePart_mul_eq (hfs.pow_pow m m) (hss.pow m) (by
      have : f ^ m - (S : End ℂ V) ^ m = ((u : End ℂ V) ^ m - 1) * (S : End ℂ V) ^ m := by
        rw [epow, sub_mul, (huS'.pow_pow m m).eq, one_mul]
      rw [this]
      exact ((huS'.pow_pow m m).sub_left (Commute.one_left _)).isNilpotent_mul_right
        (isNilpotent_pow_sub_one hunil m)) c1
    rw [one_smul] at c1 c2
    refine commute_of_commute_pow hm hunil ?_
    have h3 : ((S ^ m : (End ℂ V)ˣ) : End ℂ V) * ((u : End ℂ V) ^ m * ρ τ) =
        (S ^ m : (End ℂ V)ˣ) * (ρ τ * (u : End ℂ V) ^ m) := by
      rw [Units.val_pow_eq_pow_val, ← mul_assoc, ← epow, c1, ← mul_assoc, c2, mul_assoc, ← epow]
    exact (Units.mul_right_inj _).mp h3
  let ρ' : Representation ℂ (Weil h) V :=
    { toFun := fun σ => ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V)
      map_one' := by simp
      map_mul' := fun σ τ => by
        have := ((huρ τ).units_zpow_left (-deg σ)).eq
        rw [map_mul, deg_mul, neg_add, zpow_add, Units.val_mul]
        simp only [mul_assoc]
        rw [← mul_assoc _ (ρ τ) (Units.val (u ^ (-deg τ))), this, mul_assoc] }
  have hρ' : ∀ σ, ρ' σ = ρ σ * ((u ^ (-deg σ) : (End ℂ V)ˣ) : End ℂ V) := fun _ => rfl
  have hsm : IsSmooth ρ' := .of_open hρ (by simp) fun σ hσ => by
    have : ρ (ineIncl h σ) = 1 := hσ
    rw [hρ', this]; simp
  have hfr : ρ' (frob h) = S := by
    rw [hρ', deg_frob, ← hfdef, ← hSu', mul_assoc, ← Units.val_mul]; simp
  refine ⟨⟨ρ', N, hsm, GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob E Ω A w h V ρ' hsm (frob h) deg_frob (hfr ▸ hss), hN,
    fun σ => ?_⟩, u, rfl, hunil, huN, huρ, fun σ => ?_⟩
  · rw [hρ', mul_assoc, (huN.units_zpow_left (-deg σ)).eq, ← mul_assoc, hc, smul_mul_assoc,
      mul_assoc]
  · show _ = ρ' σ * _
    rw [hρ', mul_assoc, ← Units.val_mul, ← zpow_add]; simp

end GlobalTheory.WeilDeligne
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

def IsFrobSS (ρ : Weil h → End ℂ V) (N : End ℂ V) (a : WDRep h V) : Prop :=
  a.N = N ∧ ∀ g, Commute (a.ρ g) (ρ g) ∧ IsNilpotent (ρ g - a.ρ g)

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.CrisTheta
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAcris0Acris _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.Per.instAwayAinfCastAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.Ainf.charZero_of_charZero _root_.Reformulated.AutPerF.Ainf.isDomain _root_.Reformulated.AutPerF.AinfInv.isDomain _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.Tilt.isDomain _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.isFractionRing_away _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
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

@[simp] theorem gamma_zero (x : AinfInv p R) : gamma 0 x = 1 := by simp [gamma]

end AinfInv

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRham
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Loc.factOC _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.Per.instAlgebraAinfAcris _root_.Formalism.Per.instAlgebraAinfAinfP _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace _root_.Reformulated.AutPerF.IsUnitBall.instIsAlgClosedFractionRingSubtypeMemValuationSubring _root_.Reformulated.AutPerF.completionIsIsometricSMul _root_.Reformulated.AutPerF.completionMulSemiringAction _root_.Reformulated.AutPerF.instFactLtRealNormPadicComplexCastOfNat_solutions _root_.Reformulated.AutPerF.instIsIsometricSMulAlgEquivPadicAlgClOfIsScalarTowerPadic_solutions _root_.Reformulated.AutPerF.uniformContinuousConstSMul_of_isIsometricSMul
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

variable [IsAlgClosed (FractionRing R)]

instance isAdicComplete_fil_one : IsAdicComplete (fil p R 1) (BdRPlus p R) := by
  rw [fil, pow_one]
  infer_instance

end BdRPlus

end Reformulated.AutPerF
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.OL_finite _root_.Formalism.BasicNotions.Examples₂.LB.OL_frac _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Examples₂.LB.instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.MainNotions.N.Br.finKw _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.Pst.finiteDimensional_wdSpace _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.GlobalTheory.Pst.wdMap_mk _root_.GlobalTheory.Pst.wdMk_zero _root_.GlobalTheory.Pst.wdN_mk _root_.GlobalTheory.WeilDeligne.coe_ineConj _root_.GlobalTheory.WeilDeligne.ineIncl_ineConj _root_.GlobalTheory.WeilDeligne.kummer_one _root_.GlobalTheory.WeilDeligne.toAdd_kummerChar
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

def resDeg (l : ℕ) (w : HeightOneSpectrum (𝓞 E)) : ℕ := Nat.log l (normV w)

theorem normV_eq_pow (hw : w ∈ placesOver E l) : normV w = l ^ resDeg l w := by
  have : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  let := Ideal.Quotient.field w.asIdeal
  let := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal)
  have : CharP (𝓞 E ⧸ w.asIdeal) l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hw)
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 E ⧸ w.asIdeal) l
  rw [resDeg, normV, Nat.card_eq_fintype_card, hn, Nat.log_pow (Fact.out : l.Prime).one_lt]

variable (Bw : LocBridge l E Ω (Dec (F := E) A) O)

variable {Bw}

theorem Induces.mem_placesOver (hj : Induces Bw) (h : IsPlaceOver A w) : w ∈ placesOver E l := by
  refine (h (l : 𝓞 E)).mp ?_
  rw [hj.valuation_lt_one_iff]
  simp only [map_natCast]
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends, Padic.norm_natCast_lt_one_iff]

variable (Bw) (h : IsPlaceOver A w)

def weilToGK : ↥(Weil h) →* ↥(GK Bw.Kw) :=
  Bw.e.toMonoidHom.comp (Subgroup.inclusion (Weil_le_Dec h))

theorem weilToGK_j (σ : ↥(Weil h)) (x : Ω) :
    (weilToGK Bw h σ : GQ l) (Bw.j x) = Bw.j ((σ : G E Ω) x) := Bw.e_comm _ x

variable {Bw h} [IsAlgClosure E Ω]

variable (l) in

def alpha (σ : ↥(Weil h)) : ℤ := resDeg l w * deg σ

theorem weilToGK_frobUr (hj : Induces Bw) (σ : ↥(Weil h)) {a b : ℕ}
    (hσ : ActsAs A (normV w) (σ : G E Ω) a b) (c : ↥(MaximalUnramifiedExtension l)) :
    (weilToGK Bw h σ : GQ l) (((frobUr l ^ (resDeg l w * b)) c : ↥(MaximalUnramifiedExtension l)) : Om l) =
      (((frobUr l ^ (resDeg l w * a)) c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have : ((weilToGK Bw h σ : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp
      ((MaximalUnramifiedExtension l).val.comp (frobUr l ^ (resDeg l w * b))) =
      (MaximalUnramifiedExtension l).val.comp (frobUr l ^ (resDeg l w * a)) := by
    refine kur_algHom_ext fun c m h0 hm hc => ?_
    have hc' : (c : Om l) ^ m = 1 := congrArg Subtype.val hc
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    have : NeZero m := ⟨h0.ne'⟩
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
    obtain ⟨i, -, hi⟩ := (hz.map_of_injective Bw.j.injective).eq_pow_of_pow_eq_one hc'
    rw [← map_pow] at hi
    have hx : A.valuation (z ^ i) ≤ 1 := by
      rw [A.valuation_le_one_iff, hj, hi]; exact (norm_eq_one_of_pow_eq_one h0 hc').le
    have h1 := hσ.2 _ hx
    rw [hj.valuation_lt_one_iff, map_sub, map_pow Bw.j, map_pow Bw.j (z ^ i), ← weilToGK_j Bw h, hi,
      normV_eq_pow (hj.mem_placesOver h), ← pow_mul, ← pow_mul] at h1
    simp only [AlgHom.comp_apply, frobUr_pow_root _ c m h0 hm hc, map_pow]
    refine eq_of_pow_eq_one_of_norm_sub_lt hm ?_ ?_ h1
    · rw [← pow_mul, mul_comm, pow_mul, ← map_pow, IntermediateField.val_mk, hc', map_one, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, IntermediateField.val_mk, hc', one_pow]
  exact AlgHom.congr_fun this c

variable (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

variable (Bw h) (ρ : Representation LL ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

def weilD : Representation LL ↥(Weil h) ↥(Dpst P ρ) where
  toFun σ := actD P ρ (weilToGK Bw h σ) *
    ((phiU P ρ ^ (-alpha l σ) : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ))
  map_one' := by simp [alpha]
  map_mul' σ τ := by
    rw [map_mul, map_mul, alpha, deg_mul, mul_add, neg_add, zpow_add, Units.val_mul,
      (commute_actD_phiU P ρ _ _).mul_mul_mul_comm]
    rfl

theorem weilD_apply (σ : ↥(Weil h)) : weilD Bw h P ρ σ = actD P ρ (weilToGK Bw h σ) *
    ((phiU P ρ ^ (-alpha l σ) : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) := rfl

theorem weilD_ineIncl (σ : ↥(Ine (F := E) A)) :
    weilD Bw h P ρ (ineIncl h σ) = actD P ρ (weilToGK Bw h (ineIncl h σ)) := by
  simp [weilD_apply, alpha]

theorem weilD_monD (hj : Induces Bw) (σ : ↥(Weil h)) : weilD Bw h P ρ σ * monD P ρ =
    ((normV w : ℕ) : LL) ^ deg σ • (monD P ρ * weilD Bw h P ρ σ) := by
  have : CharZero LL := charZero_of_injective_algebraMap (algebraMap ℚ_[l] LL).injective
  have hl : (l : LL) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  rw [weilD_apply, ← mul_assoc, monD_actD, mul_assoc, mul_assoc, monD_phiU_zpow, mul_smul_comm, smul_smul,
    normV_eq_pow (hj.mem_placesOver h), Nat.cast_pow, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hl, alpha,
    add_neg_cancel, zpow_zero, one_smul]

theorem weilD_mulD (hj : Induces Bw) (σ : ↥(Weil h)) (c : ↥(MaximalUnramifiedExtension l)) :
    weilD Bw h P ρ σ * mulD P ρ c = mulD P ρ c * weilD Bw h P ρ σ := by
  obtain ⟨a, b, hσ⟩ := σ.2
  have e : -alpha l σ = ((resDeg l w * b : ℕ) : ℤ) + -((resDeg l w * a : ℕ) : ℤ) := by
    rw [alpha, deg_eq hσ]; push_cast; ring
  obtain ⟨c, rfl⟩ := (Algebra.IsAlgebraic.algHom_bijective (frobUr l ^ (resDeg l w * a))).2 c
  have h1 : (((phiU P ρ ^ (resDeg l w * a))⁻¹ : (End LL ↥(Dpst P ρ))ˣ) : End LL ↥(Dpst P ρ)) *
      mulD P ρ ((frobUr l ^ (resDeg l w * a)) c) =
      mulD P ρ c * ((phiU P ρ ^ (resDeg l w * a))⁻¹ : (End LL ↥(Dpst P ρ))ˣ) := by
    rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, Units.val_pow_eq_pow_val,
      coe_phiU, phiD_pow_mulD]
  rw [weilD_apply, e, zpow_add, zpow_neg, zpow_natCast, zpow_natCast, Units.val_mul, mul_assoc, mul_assoc, h1,
    Units.val_pow_eq_pow_val, coe_phiU, ← mul_assoc (phiD P ρ ^ _), phiD_pow_mulD, ← mul_assoc, ← mul_assoc,
    actD_mulD P ρ _ _ _ (weilToGK_frobUr hj σ hσ c)]
  simp only [mul_assoc]

theorem isSmooth_weilD (hj : Induces Bw) : IsSmooth (weilD Bw h P ρ) := by
  obtain ⟨K', hK'⟩ := exists_actD_eq_one (P := P) (ρ := ρ)
  have := K'.2
  have hc : Continuous fun σ : ↥(Ine (F := E) A) => (weilToGK Bw h (ineIncl h σ) : GQ l) :=
    continuous_subtype_val.comp (Bw.e_cont.comp (continuous_subtype_val.subtype_mk _))
  refine .of_open ((IntermediateField.fixingSubgroup_isOpen K'.1).preimage hc) (by simp) fun σ hσ => ?_
  rw [weilD_ineIncl]
  refine hK' _ hσ fun c => ?_
  rw [← weilD_ineIncl]
  exact weilD_mulD Bw h P ρ hj _ c

end Bridge

end GlobalTheory.Pst
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.OL_finite _root_.Formalism.BasicNotions.Examples₂.LB.OL_frac _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.BasicNotions.Examples₂.LB.instFiniteDimensionalPadicSubtypeOmMemIntermediateFieldVal _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.MainNotions.N.Br.finKw _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SmGL.instDecidableEqTwo _root_.GlobalTheory.SmGL.instFintypeTwo _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.GlobalTheory.WeilDeligne.coe_ineConj _root_.GlobalTheory.WeilDeligne.ineIncl_ineConj _root_.GlobalTheory.WeilDeligne.kummer_one _root_.GlobalTheory.WeilDeligne.toAdd_kummerChar
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

section Param

variable [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V)

def trivWD (a : ℕ) : WD h := WD.mk (WDRep.diag h fun _ : Fin a => 1)

@[simp] theorem lpDim_trivWD (a : ℕ) : (trivWD h a).lpDim = a := by simp [trivWD]

section Fin

variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]

def wdRho : Representation ℂ ↥(Weil h) (WDSpace P ι ρ) where
  toFun σ := wdMap P ι ρ (weilD Bw h P ρ σ) (weilD_mulD Bw h P ρ hj σ)
  map_one' := wd_ext P ι ρ fun x => by simp
  map_mul' σ τ := wd_ext P ι ρ fun x => by simp

@[simp] theorem wdRho_mk (σ : ↥(Weil h)) (x : ↥(Dpst P ρ)) :
    wdRho P ι Bw h hj ρ σ (wdMk P ι ρ x) = wdMk P ι ρ (weilD Bw h P ρ σ x) := rfl

theorem isSmooth_wdRho : IsSmooth (wdRho P ι Bw h hj ρ) :=
  (isSmooth_weilD Bw h P ρ hj).of_le fun σ hσ => wd_ext P ι ρ fun x => by simp [hσ]

theorem wdRho_wdN (σ : ↥(Weil h)) : wdRho P ι Bw h hj ρ σ * wdN P ι ρ =
    ((normV w : ℕ) : ℂ) ^ deg σ • (wdN P ι ρ * wdRho P ι Bw h hj ρ σ) :=
  wd_ext P ι ρ fun x => by
    have h1 := LinearMap.congr_fun (weilD_monD Bw h P ρ hj σ) x
    rw [End.mul_apply, LinearMap.smul_apply, End.mul_apply] at h1
    have e : ι (((((normV w : ℕ) : ↥LL.1) ^ deg σ : ↥LL.1)) : Om l) = ((normV w : ℕ) : ℂ) ^ deg σ :=
      (map_zpow₀ (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) ((normV w : ℕ) : ↥LL.1) (deg σ)).trans
        (by rw [map_natCast])
    have h2 := congrArg (wdMk P ι ρ) h1
    rw [wdMk_smul, e] at h2
    exact h2

def wdRep : WDRep h (WDSpace P ι ρ) :=
  (exists_frobenius_semisimplification E Ω A w h _ (wdRho P ι Bw h hj ρ) (wdN P ι ρ)
    (isSmooth_wdRho P ι Bw h hj ρ) (isNilpotent_wdN P ι ρ) (wdRho_wdN P ι Bw h hj ρ)).choose

end Fin

variable [FiniteDimensional ↥LL.1 V]

open Classical in

def wdPst : WD h :=
  if hV : IsPst P ρ then haveI := hV.finite; WD.mk (wdRep P ι Bw h hj ρ) else trivWD h (finrank ↥LL.1 V)

end Param

section Model

variable {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {a : ℕ}
  (r : ↥Gw →* GL (Fin a) (Om l))

def IsModel (LL' : FinExt l) (r' : ↥Gw →* GL (Fin a) ↥LL'.1) : Prop :=
  Bw.LL.1 ≤ LL'.1 ∧ Formalism.MainNotions.N.mapRep (algebraMap ↥LL'.1 (Om l)) r' = r

def IsCrysAt : Prop := ∃ LL' r', IsModel Bw r LL' r' ∧ Bw.IsCrysE P LL' r'

def IsdRAt : Prop := ∃ LL' r', IsModel Bw r LL' r' ∧ Bw.IsdRE P LL' r'

def IsPstAt : Prop := ∃ LL' r', IsModel Bw r LL' r' ∧ IsPst P (Bw.repE LL' r')

def IsInduced (τ : E →+* Om l) {LL' : FinExt l} (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) : Prop :=
  ∀ x : E, τ x = ((τ' ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ : ↥LL'.1) : Om l)

def IsJumpsAt (τ : E →+* Om l) (J : Multiset ℤ) : Prop :=
  ∃ LL' r', IsModel Bw r LL' r' ∧ Bw.IsdRE P LL' r' ∧ ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
    IsInduced Bw τ τ' ∧ ∀ n : ℤ, (J.count n : ℤ) = Bw.multE P LL' r' τ' n

end Model

section At

variable [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ}
  (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l))

open Classical in

def wdAt : WD h :=
  if hr : IsPstAt P Bw r then wdPst P ι Bw h hj (Bw.repE hr.choose hr.choose_spec.choose) else trivWD h a

end At

end GlobalTheory.Pst
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.FrobeniusOrbits.Eta.isGaloisGroup _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.Formalism.fact_prime_seven _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.Chr.negTwoFact _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.SplitWeil.matrixMeasurableSpace
attribute [-simp] _root_.Formalism.GaloisIrreducibility.BorderedIndexCases.zero_ne_succ' _root_.GlobalTheory.Idele.adele_add_apply _root_.GlobalTheory.Idele.adele_mul_apply _root_.GlobalTheory.Idele.adele_one_apply _root_.GlobalTheory.Idele.adele_sub_apply _root_.GlobalTheory.Idele.adele_zero_apply _root_.GlobalTheory.Pst.wdRho_mk
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

def IsTameChar (t : Ine (F := E) A →* Multiplicative ℤ_[l]) : Prop :=
  Continuous t ∧ Function.Surjective t

def tval (t : Ine (F := E) A →* Multiplicative ℤ_[l]) (σ : Ine (F := E) A) : Qbar l :=
  algebraMap ℚ_[l] (Qbar l) ((t σ).toAdd : ℚ_[l])

section Tame

variable {t t' : Ine (F := E) A →* Multiplicative ℤ_[l]}

omit [IsAlgClosure E Ω] in

@[simp] theorem tval_mul (σ τ : Ine (F := E) A) : tval t (σ * τ) = tval t σ + tval t τ := by
  simp [tval]

omit [IsAlgClosure E Ω] in

@[simp] theorem tval_one : tval t 1 = 0 := by simp [tval]

omit [IsAlgClosure E Ω] in

@[simp] theorem tval_pow (σ : Ine (F := E) A) (k : ℕ) : tval t (σ ^ k) = k * tval t σ := by
  simp [tval]

end Tame

def IsMonodromy (t : Ine (F := E) A →* Multiplicative ℤ_[l]) (r : G E Ω →* GL n (Qbar l))
    (N : Matrix n n (Qbar l)) : Prop :=
  IsNilpotent N ∧ ∃ U : Subgroup (Ine (F := E) A), IsOpen (U : Set (Ine (F := E) A)) ∧
    ∀ σ ∈ U, (r σ : Matrix n n (Qbar l)) = exp (tval t σ • N)

end GlobalTheory.WeilDeligne
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.LocLanglands

section Galois

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.HeckeGal ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}

structure IsLocalArtin {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) : Prop where
  surj : Function.Surjective a
  cont : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ)
  ord_eq : ∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ
  factor : ∀ ξ : Weil h →* ℂˣ, WeilDeligne.IsSmooth ξ → ∃ χ, IsSmoothChar χ ∧ ξ = χ.comp a
  glob : ∀ art : Ideles E →* Gab E Ω, IsGlobalArtin art →
    ∀ σ : Weil h, art (localIdele E w (a σ)) = toAb E Ω σ

theorem IsLocalArtin.smooth {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
    {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ}
    (ha : IsLocalArtin h a) {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    WeilDeligne.IsSmooth (χ.comp a) :=
  IsOpen.preimage ha.cont hχ

end Galois

end GlobalTheory.LocLanglands
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber _root_.GlobalTheory.Pst.finiteDimensional_wdSpace
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

abbrev cls {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (π : IrrRep (GL (Fin n) k)) : IrrGL k := ⟨n, π.cl⟩

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def sumList (l : List (WD h)) : WD h := l.foldr WD.lpSum (WD.lpZero h)

def IsIrrWD (x : WD h) : Prop := ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧ a.ρ.IsIrreducible

def IsTameWD (x : WD h) : Prop :=
  ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), WD.mk a = x ∧
    ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1

end GlobalTheory.LocLanglands
end
end

section
-- module Solutions.AlpoGe.Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
attribute [-instance] _root_.Formalism.BasicNotions.Examples₂.LB.compact_GK _root_.Formalism.DoubleCosetMeasures.instMeasGL _root_.Formalism.DoubleCosetMeasures.instMeasMat _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalQuotientSubmodule_solutions _root_.Formalism.IrreducibleCountingLemmas.Z.BN.instFiniteDimensionalSubtypeMemSubmodule_solutions _root_.Formalism.L2.Col.finite_quot _root_.Formalism.L2.Col.finite_res _root_.Formalism.L2.Col.instIsDomainQuotientRingOfIntegersIdealAsIdeal_solutions _root_.Formalism.L2.NG.isAlgClosure_rat _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_comap _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under _root_.GlobalTheory.LGrp.locallyCompact_GL _root_.GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField _root_.GlobalTheory.LocalLattice.instIsScalarTowerLocalRing _root_.GlobalTheory.Mem.finite_absNorm_fiber
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def segSum (rc : IrrGL (w.adicCompletion E) → WD h) (l : List (Segment (w.adicCompletion E))) : WD h :=
  sumList (l.map fun Δ => ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len))

end GlobalTheory.LocLanglands

end
end


