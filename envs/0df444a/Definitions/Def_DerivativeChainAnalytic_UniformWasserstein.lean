-- Prove2me | Definitions.Def_DerivativeChainAnalytic_UniformWasserstein
-- name    : DerivativeChainAnalytic_UniformWasserstein
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:56:57.480524+00:00
-- url     : https://prove2.me/theorems/70fdf44d-a5fe-4b63-876b-596d822a1723
-- title:
--   Uniform finite transition kernels and transport infimum
-- statement:
--   A uniform kernel has nonnegative entries, each row sums to one, and uniform input weights produce uniform output weights. Define its average distance cost, the linear map taking a joint array to its two marginal sums, and uniformW1 as the real infimum of kernel costs.
-- source:
--   New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/UniformWasserstein.lean, lines 10-12, SHA-256 d2b3a395a27d92bbd7b053e89aa3da51910edc46c26e0351e65151d2b5b8fe4b. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/UniformWasserstein.lean, lines 14-16, SHA-256 d2b3a395a27d92bbd7b053e89aa3da51910edc46c26e0351e65151d2b5b8fe4b. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/UniformWasserstein.lean, lines 18-22, SHA-256 d2b3a395a27d92bbd7b053e89aa3da51910edc46c26e0351e65151d2b5b8fe4b. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.; New frozen formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/phase_lock/UniformWasserstein.lean, lines 75-76, SHA-256 d2b3a395a27d92bbd7b053e89aa3da51910edc46c26e0351e65151d2b5b8fe4b. The source manifest pins the author receipts and analytic provenance. This new code is not attributed to the older public checkpoint. Shared canonical history and prefix interfaces. The phase26 and prefix-core19 frozen author manifests supply exact proof receipts and source provenance; no extension or new global U is included.

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
open DerivativeChainPrefixLaws
namespace DerivativeChainPhaseLock
noncomputable section

def UniformKernel (m n : ℕ) (K : Fin (m+1) → Fin (n+1) → ℝ) : Prop :=
  (∀ i j,0 ≤ K i j) ∧ (∀ i,∑ j,K i j=1) ∧
    ∀ j,(∑ i,(m+1:ℝ)⁻¹*K i j)=(n+1:ℝ)⁻¹

def uniformKernelCost {m n : ℕ} (x : Fin (m+1) → ℂ) (y : Fin (n+1) → ℂ)
    (K : Fin (m+1) → Fin (n+1) → ℝ) : ℝ :=
  ∑ i,(m+1:ℝ)⁻¹*(∑ j,K i j*‖y j-x i‖)

def jointMarginals (m n : ℕ) :
    ((Fin (m+1) × Fin (n+1)) → ℝ) →ₗ[ℝ] ((Fin (m+1) → ℝ) × (Fin (n+1) → ℝ)) where
  toFun p := (fun i => ∑ j,p (i,j),fun j => ∑ i,p (i,j))
  map_add' p q := by ext i <;> simp [Finset.sum_add_distrib]
  map_smul' c p := by ext i <;> simp [Finset.mul_sum]



def uniformW1 {m n : ℕ} (x : Fin (m+1) → ℂ) (y : Fin (n+1) → ℂ) : ℝ :=
  sInf {q | ∃ K,UniformKernel m n K ∧ q=uniformKernelCost x y K}





end
end DerivativeChainPhaseLock


