-- Prove2me | Definitions.Def_CubicTurning_finite_balanced
-- name    : CubicTurning_finite_balanced
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:20:16.890366+00:00
-- url     : https://prove2.me/theorems/00144a41-3ef5-4625-8c18-2524d55482ed
-- title:
--   Sharp cubic roots and arbitrary finite balanced forward laws
-- statement:
--   For every real $t$, define $a_t=\mathrm it$, $b_t=\sqrt{3+3t^2/4}-\mathrm it/2$, and $c_t=-\sqrt{3+3t^2/4}-\mathrm it/2$, with the nonnegative real square root.
--
--   For any complex triple $a,b,c$ and natural number $n$, a finite balanced forward law has real weights $w_i\ge0$ with $\sum_{i<n}w_i=1$, actual complete cubic derivative chains $z^{(i)}$, and unit axes forward for both consecutive displacements. It satisfies the complex balance identity $\sum_{i<n}(w_i:\mathbb C)z^{(i)}_2=0$. Every slot must satisfy the chain and forward conditions, even when its weight is zero. No fixed slot-to-endpoint assignment or separate common-start field is required. There is no law for $n=0$, because the empty weight sum cannot equal one.
--
--   Its mean selected energy is
--
--   $$\mathcal E(L)=\sum_{i<n}w_iE(e_i,z^{(i)}_1-z^{(i)}_0,z^{(i)}_2-z^{(i)}_1).$$
--
--   The domain consists of arbitrary finite slot counts and real normalized weights, matching the source finite linear program. No general measure or integration operation is introduced.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSharpness.lean, lines 113-113, SHA-256 387285b9af69f97f92225f56b89ed0b82ae043d24968cf05a356099163011707. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSharpness.lean, lines 114-114, SHA-256 387285b9af69f97f92225f56b89ed0b82ae043d24968cf05a356099163011707. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSharpness.lean, lines 115-115, SHA-256 387285b9af69f97f92225f56b89ed0b82ae043d24968cf05a356099163011707. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSharpness.lean, lines 213-221, SHA-256 387285b9af69f97f92225f56b89ed0b82ae043d24968cf05a356099163011707. The new Lean file is not present in the analytic source commit.; Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/continuation/CUBIC_TURNING.md (SHA-256 700f272e9074fa24f04f5fbdc8402cabc1521b4f114ad4cf29f05fc31e11b5b8), with signed-energy definitions in research-results/unified-20261025/proofs/SIGNED_TURNING.md (SHA-256 f092149c0133465022966bc4ecfc5f8227dd5219b0929ed5ac7bbef6d7a5c4c9). New formal source /Users/amal/.codex/worktrees/prove2me-sync-20261026/derivative-chain-prize/submission_sync/new_formal/cubic_turning/CubicSharpness.lean, lines 223-225, SHA-256 387285b9af69f97f92225f56b89ed0b82ae043d24968cf05a356099163011707. The new Lean file is not present in the analytic source commit.

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning








noncomputable def sharpCentral (t : ℝ) : ℂ := Complex.I*(t:ℂ)
noncomputable def sharpOuterPlus (t : ℝ) : ℂ := ⟨Real.sqrt (3+3*t^2/4),-t/2⟩
noncomputable def sharpOuterMinus (t : ℝ) : ℂ := ⟨-Real.sqrt (3+3*t^2/4),-t/2⟩

















structure FiniteBalancedForwardLaw (n : ℕ) (a b c : ℂ) where
  weights : Fin n → ℝ
  nonneg : ∀ i, 0≤weights i
  total : ∑ i, weights i=1
  paths : Fin n → Fin 3 → ℂ
  axes : Fin n → ℂ
  actual : ∀ i, DerivativeChainPrivate.IsChain ![a,b,c] (paths i)
  balanced : ∑ i, (weights i : ℂ)*paths i 2=0
  forward : ∀ i, IsForward (axes i) (paths i 1-paths i 0) (paths i 2-paths i 1)

noncomputable def FiniteBalancedForwardLaw.meanEnergy {n : ℕ} {a b c : ℂ}
    (L : FiniteBalancedForwardLaw n a b c) : ℝ :=
  ∑ i, L.weights i * energy (L.axes i) (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1)


































end CubicTurning


