-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
-- name    : Development_AutomorphicArithmetic_ThickFrames_MarkedLow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:11.35212+00:00
-- url     : https://prove2.me/theorems/33eae614-00ce-4850-b74b-52c875780a8c
-- title:
--   Marked Low
-- statement:
--   Definitions and structural lemmas for Marked Low, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThickFrames/MarkedLow.lean

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
def pw {α : Type} [Fintype α] [DecidableEq α] (p : α → ℝ) (T : Finset α) : ℝ :=
  (∏ a ∈ T, p a) * ∏ a ∈ univ \ T, (1 - p a)
def exP (p : ℕ → ℝ) (S : Finset ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (∏ a ∈ T, p a) * (∏ a ∈ S \ T, (1 - p a)) * f T
open Classical in

def ind (q : Prop) : ℝ := if q then 1 else 0
def markedLow (δ : ℝ) (r u : ℕ) : ℝ :=
  ((1 - δ) ^ u) ^ (3 * r + 1) * (((u / 2 : ℕ) : ℝ) * (3 / 4 * δ) * (1 - δ) ^ (u - 1)) ^ (3 * r)
def hE (eps : ℝ) : ℝ := 2 + 8 * eps
def KE (eps : ℝ) : ℕ := ⌈8 * (hE eps + 2) / eps⌉₊
def rE (eps : ℝ) : ℕ := KE eps + 1
def dE (eps x : ℝ) : ℝ := x ^ (-(eps / 8))
end UpperTheory.BernoulliSumsFrobeniusOrbits
end


