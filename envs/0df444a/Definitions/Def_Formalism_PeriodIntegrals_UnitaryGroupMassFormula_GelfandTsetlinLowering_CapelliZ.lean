-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliZ
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:41.722439+00:00
-- url     : https://prove2.me/theorems/b912c161-cd78-4525-871a-5b7c846d69c6
-- title:
--   Capelli Z
-- statement:
--   Definitions and structural lemmas for Capelli Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliZ.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Lemmata_GeneralBFactRight_Imports
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
def CapScalar : Prop :=
  ∀ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
    ∀ s ∈ nablaSq ℂ n mu, ∀ u : ℂ,
      Formalism.REAL.qdet (capE h lam) u (φ s) = (∏ k : Fin n, (u - (k : ℂ) + (mu.w k : ℂ))) • φ s
def capF {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (i : Fin n) (v : ℤ) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ((-1 : ℂ) ^ n) • Formalism.REAL.qdet (capE h lam) (-((v : ℂ) - ((i.1 : ℤ) : ℂ)))
def capZ {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  ((List.finRange n).map fun i =>
    ((((Rset h lam sg i).erase (sg.w i)).toList.map fun v => capF h lam i v).prod)).prod
def presRing {N : ℕ} (lam : DomWeight N) : Subring (Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ)) where
  carrier := {Q | ∀ f ∈ nablaSq ℤ N lam, ∃ f' ∈ nablaSq ℤ N lam,
    Q (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.map (Int.castRingHom ℂ) f'}
  mul_mem' := by
    intro Q1 Q2 h1 h2 f hf
    obtain ⟨f2, hf2, e2⟩ := h2 f hf
    obtain ⟨f3, hf3, e3⟩ := h1 f2 hf2
    exact ⟨f3, hf3, by rw [Module.End.mul_apply, e2, e3]⟩
  one_mem' := fun f hf => ⟨f, hf, rfl⟩
  add_mem' := by
    intro Q1 Q2 h1 h2 f hf
    obtain ⟨f1, hf1, e1⟩ := h1 f hf
    obtain ⟨f2, hf2, e2⟩ := h2 f hf
    exact ⟨f1 + f2, add_mem hf1 hf2, by rw [LinearMap.add_apply, e1, e2, map_add]⟩
  zero_mem' := fun f hf => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro Q h1 f hf
    obtain ⟨f1, hf1, e1⟩ := h1 f hf
    exact ⟨-f1, neg_mem hf1, by rw [LinearMap.neg_apply, e1, map_neg]⟩
end PI.WGL


