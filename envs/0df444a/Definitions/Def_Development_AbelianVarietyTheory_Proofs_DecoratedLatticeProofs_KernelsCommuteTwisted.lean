-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KernelsCommuteTwisted
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T20:13:26.660872+00:00
-- url     : https://prove2.me/theorems/55359906-295a-4b37-a143-1f256667c9d5
-- title:
--   Kernels Commute Twisted
-- statement:
--   Definitions and structural lemmas for Kernels Commute Twisted, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/KernelsCommuteTwisted.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndicatorIdentity
import Theorems.Thm_GlobalTheory_LatPair_phiOne_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp
noncomputable section
namespace GlobalTheory.KernelCommTw
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
def IsTwEquiv (l' l : kˣ →* ℂˣ) (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V)
    (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)),
    (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) *
      Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)
variable {l' l : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
theorem theta_mem (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (v : V') :
    θ v (phiOneSB P₀ Q₀) ∈ levelVec π Q₀ := fun h hh => by
  have hv := valuation_det_of_fix Q₀.lat (h := h) (by rw [← Pair.smul_lat, hh])
  have := hθ 1 h v (phiOneSB P₀ Q₀) (phiOneSB P₀ Q₀) fun x => by
    have e := phiOne_smul (x := x) (P := P₀) (Q := Q₀) 1 h
    rw [one_smul, hh] at e
    simp only [phiOneSB, map_one, hl _ hv, Units.val_one, one_mul]
    simpa using e
  simpa using this.symm
variable (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)
def KK : Form k n' V' →ₗ[ℂ] Form k n V :=
  (EqForm π).subtype ∘ₗ (evalEquiv π Q₀).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (θ.flip (phiOneSB P₀ Q₀) ∘ₗ LinearMap.proj P₀) fun φ => theta_mem hl hθ P₀ Q₀ (φ P₀)
end GlobalTheory.KernelCommTw
namespace GlobalTheory.KernelCommTw
end GlobalTheory.KernelCommTw


