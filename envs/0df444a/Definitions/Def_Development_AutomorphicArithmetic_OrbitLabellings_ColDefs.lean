-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_ColDefs
-- name    : Development_AutomorphicArithmetic_OrbitLabellings_ColDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:21.893402+00:00
-- url     : https://prove2.me/theorems/f296537a-3431-4ecd-a1b7-9e43cb4b42ec
-- title:
--   Col Defs
-- statement:
--   Definitions and structural lemmas for Col Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/OrbitLabellings/ColDefs.lean

import Mathlib
import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
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
open Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds
namespace UpperTheory.G2
structure IsPos {Lt : Type} (i : ℕ) (pos : Lt → ℕ → Lt) : Prop where
  zero : ∀ z, pos z 0 = z
  add : ∀ z a b, pos (pos z a) b = pos z (a + b)
  period : ∀ z, pos z i = z
section Series
variable {K : Type} {Lt β : Type}
def logS [Field K] [DecidableEq Lt] [DecidableEq β] (l i : ℕ) (pos : Lt → ℕ → Lt) (v : Lt × β) : MvPowerSeries (Lt × β) K :=
  genLog l (fun y : Lt × β => (pos y.1 (2 * (i - 1)), y.2)) v
def beS [Field K] [Fintype β] (i : ℕ) (pos : Lt → ℕ → Lt) (R : Finset Lt) (sg : Lt → K)
    (be : Lt → MvPowerSeries (ZMod (2 * i)) K) : MvPowerSeries (Lt × β) K :=
  ∑ r ∈ R, (sg r / 2) • ∑ b : β,
    MvPowerSeries.subst (fun s : ZMod (2 * i) => (MvPowerSeries.X (pos r s.val, b) : MvPowerSeries (Lt × β) K)) (be r)
def ShapeS [NormedField K] [CharZero K] [DecidableEq Lt] [DecidableEq β] [Fintype β] (l i : ℕ) (pos : Lt → ℕ → Lt)
    (R : Finset Lt) (ep : K) (sg : Lt → K) (be : Lt → MvPowerSeries (ZMod (2 * i)) K) (Th : MvPowerSeries (Lt × β) K) : Prop :=
  ∃ U : MvPowerSeries (Lt × β) K, Integral U ∧
    MvPowerSeries.subst (fun v : Lt × β => MvPowerSeries.C ep * logS (K := K) l i pos v) Th =
      U * MvPowerSeries.subst (logS (K := K) (β := β) l i pos) (mvExp (beS i pos R sg be))
def HasThetaProductForm [NormedField K] [CharZero K] [DecidableEq Lt] [DecidableEq β] [Fintype β] (l i : ℕ) [NeZero i] (pos : Lt → ℕ → Lt)
    (Th : MvPowerSeries (Lt × β) K) : Prop :=
  ∃ (K0 : Subfield K) (ζ : K) (R : Finset Lt) (ep : K) (sg : Lt → K) (be : Lt → MvPowerSeries (ZMod (2 * i)) K),
    Unram l K0 ∧ IsPrimitiveRoot ζ (l ^ (2 * i) - 1) ∧ ‖ep‖ = 1 ∧ (∀ r ∈ R, sg r = 1 ∨ sg r = -1) ∧
      (∀ r ∈ R, BHyp l (2 * i) K0 ζ (be r)) ∧ ShapeS l i pos R ep sg be Th
def linS [Field K] {K0 : Type} [Field K0] (j : K0 →+* K) (σ : K0 →+* K0) (i : ℕ) [NeZero i] (pos : Lt → ℕ → Lt) (c : K0) (r : Lt)
    (b : β) : MvPowerSeries (Lt × β) K :=
  ∑ s : ZMod (2 * i), if s.val % 2 = 0 then MvPowerSeries.C (j (σ^[s.val] c)) * MvPowerSeries.X (pos r s.val, b) else 0
end Series
def IsRadii {Lt : Type} (l : ℕ) (pos : Lt → ℕ → Lt) (sig : Lt → ℝ) : Prop :=
  (∀ z, 0 ≤ sig z) ∧ ∀ z, ∀ e : ℕ, Odd e → 1 ≤ (l : ℝ) ^ e * sig z + sig (pos z e)
end UpperTheory.G2
end


