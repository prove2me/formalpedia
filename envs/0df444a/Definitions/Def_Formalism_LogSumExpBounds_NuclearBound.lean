-- Prove2me | Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
-- name    : Formalism_LogSumExpBounds_NuclearBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:53.973599+00:00
-- url     : https://prove2.me/theorems/1bcdae8b-6e78-4a64-8e0e-fa8cf24c6b32
-- title:
--   Nuclear Bound
-- statement:
--   Definitions and structural lemmas for Nuclear Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/NuclearBound.lean

import Definitions.Def_Formalism_LogSumExpBounds_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.NuclearRankWeightBounds.D
open Finset
def CBWeights : Prop :=
  ∀ (N : ℕ) (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Y.IsHermitian) (i : ℕ), i ≤ N →
    ∃ w : Finset (Fin N) → ℝ, (∀ J, 0 ≤ w J) ∧
      (∑ J ∈ powersetCard i (univ : Finset (Fin N)), w J) = 1 ∧
      lead (NormedSpace.exp Y) i
        = ((∑ J ∈ powersetCard i (univ : Finset (Fin N)),
            w J * Real.exp (∑ j ∈ J, hY.eigenvalues j) : ℝ) : ℂ) ∧
      (∑ J ∈ powersetCard i (univ : Finset (Fin N)), w J * (∑ j ∈ J, hY.eigenvalues j))
        = ∑ a ∈ univ.filter (fun a : Fin N => a.val < i), (Y a a).re ∧
      (∑ J ∈ powersetCard i (univ : Finset (Fin N)), w J * (∑ j ∈ J, hY.eigenvalues j) ^ 2)
        = (∑ a ∈ univ.filter (fun a : Fin N => a.val < i), (Y a a).re) ^ 2
          + ∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
              ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2
def NuclearBound : Prop :=
  ∀ (N : ℕ) (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Y.IsHermitian),
    ∑ j, |hY.eigenvalues j| ≤ Real.sqrt (Y.rank : ℝ) * hs Y
def RankBlock : Prop :=
  ∀ (N : ℕ) (ep : Fin N → Bool) (Y : Matrix (Fin N) (Fin N) ℂ),
    (∀ a b, ep a = ep b → Y a b = 0) → Y.rank ≤ 2 * q0 ep
def LogSumExp : Prop :=
  ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (M : ℝ),
    (∀ j, 0 ≤ w j) → ∑ j, w j = 1 → ∑ j, w j * y j = 0 → (∀ j, |y j| ≤ M) →
    min 1 M⁻¹ * (∑ j, w j * y j ^ 2) / 4 ≤ Real.log (∑ j, w j * Real.exp (y j))
def WeightedOff : Prop :=
  ∀ (N : ℕ) (s : ℕ → ℝ) (ep : Fin N → Bool) (h : ℝ) (Y : Matrix (Fin N) (Fin N) ℂ),
    Y.IsHermitian → (∀ a b, ep a = ep b → Y a b = 0) →
    (∀ a b : Fin N, b < a → ep a ≠ ep b → h ≤ ∑ i ∈ Ico (b.val + 1) (a.val + 1), s i) →
    h * hs Y ^ 2 / 2 ≤ ∑ i ∈ Ico 1 N, s i *
      ∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2
end Formalism.NuclearRankWeightBounds.D


