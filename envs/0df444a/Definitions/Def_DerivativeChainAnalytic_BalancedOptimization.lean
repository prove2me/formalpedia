-- Prove2me | Definitions.Def_DerivativeChainAnalytic_BalancedOptimization
-- name    : DerivativeChainAnalytic_BalancedOptimization
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:57:43.064992+00:00
-- url     : https://prove2.me/theorems/52b98438-9c38-41a5-9835-e1c2307abe70
-- title:
--   Linear maps for mass, barycenter and weighted cost
-- statement:
--   The balance map sends real weights to their total mass and complex weighted sum. The cost map sends weights to the real weighted sum of a supplied cost vector. Both retain their real-linear structures and exact source formulas.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/BalancedOptimization.lean, lines 10-24, SHA-256 bcfbd51f6b73a747efafcbdd431499ffdffd395e1daab9836edc63d5b585da35. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/prefix_laws/BalancedOptimization.lean, lines 26-30, SHA-256 bcfbd51f6b73a747efafcbdd431499ffdffd395e1daab9836edc63d5b585da35. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

import Mathlib
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainFiniteHistory
end DerivativeChainFiniteHistory
namespace DerivativeChainPhaseLock
end DerivativeChainPhaseLock
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace DerivativeChainPrefixLaws
noncomputable section

noncomputable def balanceMap {ι : Type*} [Fintype ι] (a : ι → ℂ) :
    (ι → ℝ) →ₗ[ℝ] ℝ × ℂ where
  toFun w := (∑ i,w i,∑ i,(w i:ℂ)*a i)
  map_add' := by
    intro w v
    apply Prod.ext
    · simp only [Pi.add_apply,Finset.sum_add_distrib,Prod.fst_add]
    · simp only [Pi.add_apply,Complex.ofReal_add,add_mul,Finset.sum_add_distrib,Prod.snd_add]
  map_smul' := by
    intro c w
    apply Prod.ext
    · change (∑ i,c*w i)=c*(∑ i,w i)
      rw [Finset.mul_sum]
    · change (∑ i,((c*w i:ℝ):ℂ)*a i)=c • (∑ i,(w i:ℂ)*a i)
      simp only [Complex.ofReal_mul,Complex.real_smul,Finset.mul_sum,mul_assoc]

noncomputable def costLinearMap {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ i,w i*c i
  map_add' := by intro w v; simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' := by intro r w; simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc,RingHom.id_apply]







end
end DerivativeChainPrefixLaws


