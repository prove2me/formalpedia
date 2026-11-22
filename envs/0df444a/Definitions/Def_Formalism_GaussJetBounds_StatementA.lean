-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_StatementA
-- name    : Formalism_GaussJetBounds_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:30.737622+00:00
-- url     : https://prove2.me/theorems/e1c843b6-415e-4ad9-afd5-0508205c8dac
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/StatementA.lean

import Definitions.Def_Formalism_GaussJetBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
def rowRad {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d) (isTop : ι → Bool)
    (spec : ι → Option (ZMod d × ℤ)) (i : ι) : ℝ :=
  if isTop i then eps (lt i) else
    match spec i with
    | some (s, j) =>
        if 0 < j then max (sig (lt i)) (1 - (l : ℝ) ^ j.toNat * eps s)
        else max (sig (lt i)) ((l : ℝ) ^ (-j).toNat)⁻¹
    | none => sig (lt i)
def ThmAAssembly : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d →
  ∀ (TT : Finset (ZMod d)) (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu2 s ≤ nu1 s) →
    (∀ s, nu1 s ≤ size s) →
  ∀ sig : ZMod d → ℝ, IsOptDual l d (fun s => (Dl d TT nu1 size s : ℝ)) sig →
  ∀ (ι : Type) [Fintype ι] (lt : ι → ZMod d) (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ))
    (κ : ι → ℕ),
    (∀ i, isTop i = true → lt i ∈ TT ∧ spec i = none) →
    (∀ s ∈ TT, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = true), (κ i : ℝ)) =
      (nu1 s : ℝ)) →
    (∀ s, (∑ i ∈ Finset.univ.filter (fun i => lt i = s ∧ isTop i = false), (κ i : ℝ)) =
      (Dl d TT nu1 size s : ℝ)) →
    (∀ i s j, spec i = some (s, j) → s ∈ TT ∧ Odd j ∧ lt i = s + (j : ZMod d) ∧
      (0 < j → l ^ j.toNat ≤ nu1 s) ∧ (j < 0 → l ^ (-j).toNat ≤ size (lt i))) →
    (∀ (s : ZMod d) (j : ℤ), (∑ i ∈ Finset.univ.filter (fun i => spec i = some (s, j)), (κ i : ℝ)) ≤
      (capL d TT nu1 nu2 (s + (j : ZMod d)) : ℝ)) →
    ∃ eps : ZMod d → ℝ, (∀ s, 0 ≤ eps s) ∧
      (∀ s ∈ TT, ∀ e : ℕ, dTop d TT s = (e : ℕ∞) → ((l : ℝ) ^ e)⁻¹ ≤ eps s) ∧
      (∑ s ∈ TT, (topTerm l d TT nu1 nu2 s - gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) ≤
        ∑ i, (κ i : ℝ) * (gam l - rowRad l sig eps lt isTop spec i)
end Formalism.DworkPowerSeriesWeights


