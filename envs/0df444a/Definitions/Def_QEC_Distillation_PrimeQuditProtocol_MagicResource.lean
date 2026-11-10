-- Prove2me | Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
-- name    : QEC_Distillation_PrimeQuditProtocol_MagicResource
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T10:48:09.023973+00:00
-- url     : https://prove2.me/theorems/c3aaa921-8e4f-4035-841d-aeefc6835c16
-- title:
--   Magic Resource
-- statement:
--   Definitions and structural lemmas for Magic Resource, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/PrimeQuditProtocol/MagicResource.lean

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_idealU13Resource_inner_self
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_physicalU13_apply_phase
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.KT19MagicResource
open Semantics
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
namespace KT19PrimeQuditCSS
universe u v w
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site]
local instance _p2m_local_instance_d135975d44_41 : DecidableEq Site := Classical.decEq Site
local instance primeQuditRegisterLabelFintypeLocal (p : Nat) [NeZero p]
    (Site : Type u) [Fintype Site] :
    Fintype (PrimeQuditRegisterLabel p Site) := Fintype.ofFinite _
theorem singleNorm_sq_mul_p :
    (Real.sqrt (p : Real) : Complex)⁻¹ * (Real.sqrt (p : Real) : Complex)⁻¹ * (p : ℂ) = 1 := by
  have hpos : (0 : Real) < (p : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hsqrt : (Real.sqrt (p : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  have hsquare :
      (Real.sqrt (p : Real) : Complex) * (Real.sqrt (p : Real) : Complex) = (p : Complex) := by
    exact_mod_cast Real.mul_self_sqrt hpos.le
  rw [← hsquare]
  field_simp [hsqrt]
def magicBasisAmplitude (a x : ZMod p) : Complex :=
  phase p (a * x + x ^ 3)
def magicBasisKet (a : ZMod p) : PrimeQudit p :=
  zPowerTransport p a (idealU13Resource p)
theorem sum_basisKet_apply (x : ZMod p) :
    (∑ y : ZMod p, quditBasisKet p y) x = ∑ y : ZMod p, (quditBasisKet p y) x := by
  rw [← PiLp.projₗ_apply (p := 2) (𝕜 := ℂ) (β := fun _ : ZMod p => ℂ) x]
  rw [map_sum]
  simp only [PiLp.projₗ_apply]
@[simp]
theorem magicBasisKet_apply (a x : ZMod p) :
    magicBasisKet p a x =
      (Real.sqrt (p : Real) : Complex)⁻¹ * magicBasisAmplitude p a x := by
  unfold magicBasisKet magicBasisAmplitude idealU13Resource
  rw [zPowerTransport_apply, u13Transport_apply]
  simp only [PiLp.smul_apply]
  rw [sum_basisKet_apply]
  change phase p (a * x) *
      (u13Amplitude p x * ((Real.sqrt (p : Real) : Complex)⁻¹ *
        (∑ y : ZMod p, (quditBasisKet p y) x))) = _
  simp only [u13Amplitude, quditBasisKet, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  simp only [Fintype.sum_ite_eq]
  rw [phase_add]
  ring
theorem magicBasisKet_inner_self (a : ZMod p) :
    inner ℂ (magicBasisKet p a) (magicBasisKet p a) = 1 := by
  rw [magicBasisKet, (zPowerTransport p a).map_inner, idealU13Resource_inner_self]
def magicBasisKrausFamily : FiniteKrausFamily (ZMod p) (PrimeQudit p) (PrimeQudit p) where
  operator a :=
    (InnerProductSpace.rankOne ℂ (magicBasisKet p a) (magicBasisKet p a)).toLinearMap
def magicBasisInstrument : FiniteInstrument (ZMod p) (ZMod p) (PrimeQudit p) (PrimeQudit p) where
  kraus := magicBasisKrausFamily p
  observe := id
def magicResource (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    DensityOperator (PrimeQudit p) :=
  DensityOperator.convexCombination Finset.univ mu
    (fun a => DensityOperator.pureDensity (magicBasisKet p a) (by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), magicBasisKet_inner_self]
      norm_num))
    (fun a _ => hmu_nonneg a) hmu_sum
def registerPairing (e x : PrimeQuditRegisterLabel p Site) : ZMod p :=
  ∑ site : Site, e site * x site
def registerPhase (e x : PrimeQuditRegisterLabel p Site) : Complex :=
  phase p (registerPairing p e x)
def zWordTransport (e : PrimeQuditRegisterLabel p Site) :
    UnitaryTransport (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) where
  toLinearEquiv := diagonalLinearEquiv (registerPhase p e)
    (fun x => phase p (-registerPairing p e x))
    (by
      intro x
      change phase p (-registerPairing p e x) * phase p (registerPairing p e x) = 1
      rw [← phase_add, neg_add_cancel, phase_zero])
    (by
      intro x
      change phase p (registerPairing p e x) * phase p (-registerPairing p e x) = 1
      rw [← phase_add, add_neg_cancel, phase_zero])
  map_inner := diagonalOperator_map_inner (registerPhase p e)
    (fun x => phase_mul_conj p (registerPairing p e x))
@[simp]
theorem zWordTransport_apply (e : PrimeQuditRegisterLabel p Site)
    (psi : PrimeQuditRegister p Site) (x : PrimeQuditRegisterLabel p Site) :
    zWordTransport p e psi x = registerPhase p e x * psi x :=
  rfl
@[simp]
theorem zWordTransport_symm_apply (e : PrimeQuditRegisterLabel p Site)
    (psi : PrimeQuditRegister p Site) (x : PrimeQuditRegisterLabel p Site) :
    (zWordTransport p e).symm psi x = phase p (-registerPairing p e x) * psi x := by
  unfold zWordTransport UnitaryTransport.symm diagonalLinearEquiv
  rfl
def idealRegisterState : PrimeQuditRegister p Site :=
  ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) •
    ∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x
@[simp]
theorem idealRegisterState_apply (x : PrimeQuditRegisterLabel p Site) :
    idealRegisterState p x = (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site := by
  simp [idealRegisterState, registerBasisKet, EuclideanSpace.basisFun_apply,
    Finset.sum_apply]
theorem registerNorm_sq_mul_pow :
    ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
      ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
        (p : ℂ) ^ Fintype.card Site = 1 := by
  rw [← mul_pow, ← mul_pow, singleNorm_sq_mul_p]
  norm_num
theorem idealRegisterState_inner_self :
    inner ℂ (idealRegisterState p : PrimeQuditRegister p Site)
      (idealRegisterState p : PrimeQuditRegister p Site) = 1 := by
  rw [idealRegisterState]
  change inner ℂ (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) •
      ∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x)
    (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) •
      ∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x) = 1
  rw [inner_smul_left, inner_smul_right]
  change starRingEnd ℂ ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
      (((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site) *
        inner ℂ (∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x)
          (∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x)) = 1
  rw [inner_sum (s := Finset.univ) (f := registerBasisKet p)
    (x := ∑ x : PrimeQuditRegisterLabel p Site, registerBasisKet p x)]
  simp_rw [sum_inner (s := Finset.univ) (f := registerBasisKet p)]
  simp only [registerBasisKet, EuclideanSpace.basisFun_apply]
  simp_rw [EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply]
  change ((Real.sqrt (p : Real) : Complex) ^ Fintype.card Site)⁻¹ *
      (((Real.sqrt (p : Real) : Complex) ^ Fintype.card Site)⁻¹ *
        ↑(Fintype.card (PrimeQuditRegisterLabel p Site))) = 1
  rw [← mul_assoc]
  have hcard : (Fintype.card (PrimeQuditRegisterLabel p Site) : ℂ) =
      (p : ℂ) ^ Fintype.card Site := by
    rw [show (Fintype.card (PrimeQuditRegisterLabel p Site) : ℂ) =
        (@Fintype.card (Site → ZMod p) Pi.instFintype : ℂ) by
      congr 1
      exact @Fintype.card_congr (PrimeQuditRegisterLabel p Site) (Site → ZMod p)
        (primeQuditRegisterLabelFintypeLocal p Site) Pi.instFintype
        (Equiv.refl (Site → ZMod p))]
    rw [Fintype.card_fun]
    norm_num [ZMod.card]
  rw [hcard]
  rw [← inv_pow]
  exact registerNorm_sq_mul_pow p
def characterKet (e : PrimeQuditRegisterLabel p Site) : PrimeQuditRegister p Site :=
  zWordTransport p e (idealRegisterState p)
@[simp]
theorem characterKet_apply (e x : PrimeQuditRegisterLabel p Site) :
    characterKet p e x =
      (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site *
        phase p (registerPairing p e x) := by
  unfold characterKet
  rw [zWordTransport_apply]
  simp [idealRegisterState, registerPhase]
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]
  ring
def finSuccArrowEquiv (n : ℕ) (α : Type w) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun f := (f (Fin.last n), fun i => f i.castSucc)
  invFun p := Fin.snoc p.2 p.1
  left_inv f := by
    funext i
    by_cases hi : i = Fin.last n
    · subst hi
      simp
    · rw [show i = (i.castPred hi).castSucc by
        exact (Fin.castSucc_castPred i hi).symm]
      dsimp
      exact Fin.snoc_castSucc _ _ _
  right_inv p := by
    ext <;> simp
theorem Fintype_sum_fn_prod_fin {R : Type u} {α : Type w} [CommSemiring R] [Fintype α]
    (n : ℕ) (g : Fin n → α → R) :
    ∑ f : Fin n → α, ∏ i : Fin n, g i (f i) = ∏ i : Fin n, ∑ a : α, g i a := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ∑ f : Fin (n + 1) → α, ∏ i : Fin (n + 1), g i (f i) =
          ∑ f : Fin (n + 1) → α, g (Fin.last n) (f (Fin.last n)) *
            (∏ i : Fin n, g i.castSucc (f i.castSucc)) := by
        apply Finset.sum_congr rfl
        intro f _
        rw [Fin.prod_univ_castSucc, mul_comm]
      _ = ∑ pair : α × (Fin n → α), g (Fin.last n) pair.1 *
            (∏ i : Fin n, g i.castSucc (pair.2 i)) := by
        rw [Fintype.sum_equiv (finSuccArrowEquiv n α)
          (fun f : Fin (n + 1) → α => g (Fin.last n) (f (Fin.last n)) *
            (∏ i : Fin n, g i.castSucc (f i.castSucc)))
          (fun pair : α × (Fin n → α) => g (Fin.last n) pair.1 *
            (∏ i : Fin n, g i.castSucc (pair.2 i)))]
        intro f
        rfl
      _ = (∑ a : α, g (Fin.last n) a) * (∏ i : Fin n, ∑ a : α, g i.castSucc a) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_congr rfl (fun a _ => by
          change (∑ y : Fin n → α, g (Fin.last n) a * (∏ i : Fin n, g i.castSucc (y i))) = _
          rw [← Finset.mul_sum])]
        rw [ih (fun i => g i.castSucc)]
        rw [← Finset.sum_mul]
      _ = ∏ i : Fin (n + 1), ∑ a : α, g i a := by
        rw [Fin.prod_univ_castSucc, mul_comm]
theorem Fintype_sum_fn_prod {R : Type u} {ι : Type v} {α : Type w} [CommSemiring R] [Fintype ι] [Fintype α]
    (g : ι → α → R) :
    ∑ f : ι → α, ∏ i : ι, g i (f i) = ∏ i : ι, ∑ a : α, g i a := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  rw [Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl α)) (fun f => ∏ i : ι, g i (f i))
    (fun f => ∏ j : Fin (Fintype.card ι), g (e.symm j) (f j)) (by
      intro f
      rw [Fintype.prod_equiv e (fun i => g i (f i)) (fun j => g (e.symm j) (f (e.symm j)))]
      · rfl
      · intro i
        rw [Equiv.symm_apply_apply])]
  rw [Fintype_sum_fn_prod_fin (Fintype.card ι) (fun j => g (e.symm j))]
  rw [Fintype.prod_equiv e (fun i => ∑ a : α, g i a) (fun j => ∑ a : α, g (e.symm j) a)]
  intro i
  rw [Equiv.symm_apply_apply]
theorem labelUniv_eq_piUniv :
    (@Finset.univ (PrimeQuditRegisterLabel p Site) (primeQuditRegisterLabelFintypeLocal p Site)) =
      (@Finset.univ (Site → ZMod p) Pi.instFintype) := by
  apply Finset.ext
  intro x
  simp
def magicRegisterKet (e : PrimeQuditRegisterLabel p Site) : PrimeQuditRegister p Site :=
  zWordTransport p e (physicalU13 p (idealRegisterState p))
@[simp]
theorem magicRegisterKet_apply (e x : PrimeQuditRegisterLabel p Site) :
    magicRegisterKet p e x =
      (Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site *
        phase p (registerPairing p e x + cubicExponent p x) := by
  unfold magicRegisterKet
  rw [zWordTransport_apply, physicalU13_apply_phase]
  simp [idealRegisterState, registerPhase]
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]
  rw [phase_add]
  ring
@[simp]
theorem physicalU13_symm_apply_phase (psi : PrimeQuditRegister p Site)
    (x : PrimeQuditRegisterLabel p Site) :
    (physicalU13 p).symm psi x = phase p (-cubicExponent p x) * psi x := by
  have hleft : ∀ x : PrimeQuditRegisterLabel p Site,
      phase p (cubicExponent p x) * phase p (-cubicExponent p x) = 1 := by
    intro x
    rw [← phase_add, add_neg_cancel, phase_zero]
  have hright : ∀ x : PrimeQuditRegisterLabel p Site,
      phase p (-cubicExponent p x) * phase p (cubicExponent p x) = 1 := by
    intro x
    rw [← phase_add, neg_add_cancel, phase_zero]
  have htrans (psi : PrimeQuditRegister p Site) :
      (physicalU13 p) (diagonalLinearEquiv (fun y => phase p (-cubicExponent p y))
        (fun y => phase p (cubicExponent p y)) hleft hright psi) = psi := by
    ext y
    rw [physicalU13_apply_phase]
    unfold diagonalLinearEquiv
    change phase p (cubicExponent p y) *
      ((diagonalOperator (fun z : PrimeQuditRegisterLabel p Site =>
        phase p (-cubicExponent p z))) psi) y = psi y
    rw [diagonalOperator_apply]
    rw [← mul_assoc, ← phase_add, add_neg_cancel, phase_zero]
    simp
  have hvec : (physicalU13 p).symm psi = diagonalLinearEquiv
      (fun y => phase p (-cubicExponent p y)) (fun y => phase p (cubicExponent p y))
      hleft hright psi := by
    apply (physicalU13 p).toLinearEquiv.injective
    rw [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
    exact (htrans psi).symm
  rw [hvec]
  unfold diagonalLinearEquiv
  change ((diagonalOperator (fun z : PrimeQuditRegisterLabel p Site =>
    phase p (-cubicExponent p z))) psi) x = phase p (-cubicExponent p x) * psi x
  rw [diagonalOperator_apply]
theorem magicRegisterKet_inner_self (e : PrimeQuditRegisterLabel p Site) :
    inner ℂ (magicRegisterKet p e) (magicRegisterKet p e) = 1 := by
  rw [magicRegisterKet, (zWordTransport p e).map_inner, (physicalU13 p).map_inner,
    idealRegisterState_inner_self]
def magicRegisterKrausFamily :
    FiniteKrausFamily (PrimeQuditRegisterLabel p Site)
      (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) where
  operator e :=
    (InnerProductSpace.rankOne ℂ (magicRegisterKet p e)
      (magicRegisterKet p e)).toLinearMap
def magicRegisterInstrument :
    FiniteInstrument (PrimeQuditRegisterLabel p Site)
      (PrimeQuditRegisterLabel p Site)
      (PrimeQuditRegister p Site) (PrimeQuditRegister p Site) where
  kraus := magicRegisterKrausFamily p
  observe := id
def wordProbability (mu : ZMod p → ℝ) (e : PrimeQuditRegisterLabel p Site) : ℝ :=
  ∏ site : Site, mu (e site)
theorem wordProbability_nonneg (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (e : PrimeQuditRegisterLabel p Site) :
    0 ≤ wordProbability p mu e := by
  unfold wordProbability
  exact Finset.prod_nonneg (fun site _ => hmu_nonneg (e site))
theorem sum_wordProbability_eq_one (mu : ZMod p → ℝ)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    ∑ e : PrimeQuditRegisterLabel p Site, wordProbability p mu e = 1 := by
  change (∑ e : Site → ZMod p, ∏ site : Site, mu (e site)) = 1
  rw [labelUniv_eq_piUniv]
  rw [Fintype_sum_fn_prod (R := ℝ) (ι := Site) (α := ZMod p)
    (fun (site : Site) (a : ZMod p) => mu a)]
  rw [hmu_sum]
  simp
def magicRegisterResource (mu : ZMod p → ℝ) (hmu_nonneg : ∀ a : ZMod p, 0 ≤ mu a)
    (hmu_sum : ∑ a : ZMod p, mu a = 1) :
    DensityOperator (PrimeQuditRegister p Site) :=
  DensityOperator.convexCombination Finset.univ (wordProbability p mu)
    (fun e => DensityOperator.pureDensity (magicRegisterKet p e) (by
      rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), magicRegisterKet_inner_self]
      norm_num))
    (fun e _ => wordProbability_nonneg p mu hmu_nonneg e)
    (sum_wordProbability_eq_one p mu hmu_sum)
def nonzeroMass (mu : ZMod p → ℝ) : ℝ :=
  ∑ a : ZMod p, if a = 0 then 0 else mu a
end KT19PrimeQuditCSS
end QEC.Distillation.KT19MagicResource


