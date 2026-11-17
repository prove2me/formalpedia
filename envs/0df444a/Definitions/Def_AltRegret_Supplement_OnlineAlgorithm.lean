-- Prove2me | Definitions.Def_AltRegret_Supplement_OnlineAlgorithm
-- name    : AltRegret_Supplement_OnlineAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:08:46.817191+00:00
-- url     : https://prove2.me/theorems/9aa9c355-dd38-4e18-9cab-26ad51e2179f
-- title:
--   Randomized causal online algorithms and expected alternating regret
-- statement:
--   A randomized causal online algorithm chooses its action on round $t+1$ from exactly the first $t$ loss functions and a private random seed. For a fixed deterministic loss sequence, this induces a random play sequence. Its expected worst-comparator alternating regret is
--   $$
--   \mathbb E_A\left[\sup_{u\in X}\operatorname{Reg}_{\mathrm{Alt}}^T(u)\right],
--   $$
--   where the expectation is only over the private seed.
--
--   This interface makes the obliviousness convention in Theorems 9 and 10 explicit: the adversarial loss sequence is chosen outside the seed.
--
--   **Formalization Note** Actions are required to be measurable functions of the seed for every finite loss history and to lie in $X$ for every seed.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Theorems 9 and 10, pp.12, 15

import Mathlib
import Definitions.Def_AltRegret_Supplement_ContinuousAAHedgeRun

open MeasureTheory

namespace AltRegret.Supplement

/-- A randomized causal online algorithm: before round `t+1`, it sees exactly `t` past losses
and uses a private random seed `ω`. -/
abbrev OnlineAlgorithm (Ω : Type*) (d : ℕ) :=
  (t : ℕ) → (Fin t → Point d → ℝ) → Ω → Point d

/-- The play sequence induced by an online algorithm and an oblivious loss sequence. -/
def onlinePlay {Ω : Type*} {d : ℕ} (A : OnlineAlgorithm Ω d)
    (f : ℕ → Point d → ℝ) (t : ℕ) (ω : Ω) : Point d :=
  if _ht : 1 ≤ t then A (t - 1) (fun j => f (j.1 + 1)) ω else 0

/-- The algorithm always plays in `X`, and its random play is measurable for every history. -/
def IsOnlineAlgorithmOn {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (X : Set (Point d)) (A : OnlineAlgorithm Ω d) : Prop :=
  ∀ (t : ℕ) (hist : Fin t → Point d → ℝ),
    Measurable (A t hist) ∧ ∀ ω, A t hist ω ∈ X

/-- Worst-comparator alternating regret over `X`. Compactness, nonemptiness and bounded losses
in the milestone theorems ensure that this real supremum is finite and attained. -/
noncomputable def worstAltRegret {d : ℕ} (X : Set (Point d))
    (f : ℕ → Point d → ℝ) (x : ℕ → Point d) (T : ℕ) : ℝ :=
  sSup (continuousAltRegret f x T '' X)

/-- Expected worst-comparator alternating regret; expectation is only over the private seed. -/
noncomputable def expectedWorstAltRegret {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (X : Set (Point d)) (A : OnlineAlgorithm Ω d)
    (f : ℕ → Point d → ℝ) (T : ℕ) : ℝ :=
  ∫ ω, worstAltRegret X f (fun t => onlinePlay A f t ω) T ∂P

end AltRegret.Supplement


