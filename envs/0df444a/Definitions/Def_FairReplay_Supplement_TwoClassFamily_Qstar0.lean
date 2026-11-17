-- Prove2me | Definitions.Def_FairReplay_Supplement_TwoClassFamily_Qstar0
-- name    : FairReplay_Supplement_TwoClassFamily_Qstar0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:49:40.182204+00:00
-- url     : https://prove2.me/theorems/26d7cebd-a9ed-4321-bb3e-ae618a38cb64
-- title:
--   Declared cost, $\delta$-correctness and $Q^\star_0(d)$ in the P19 family
-- statement:
--   In the P19 family, the **declared cost** of a run is $\sum_i c_iN_i$, where $N_i$ is the number of queries of group $S_i$ before stopping; the **boundary-block cost** is the part spent on groups meeting the unmatched set $U$. A partial-replay tester is **$\delta$-correct** if its type-I error under the simple null and its type-II error under every alternative $x\in A$ are at most $\delta$. A tester is **fixed-design** if it queries a schedule fixed in advance for a fixed number of rounds. Finally
--   $$Q^\star_0(d)=\inf\{\mathbb E_0[\mathrm{cost}]:\ \text{tester }\delta\text{-correct}\}$$
--   is the optimal expected null declared cost.
--
--   **Formalization Note** Expectations are lower integrals and the infimum is in $[0,\infty]$; non-stopping counts as an error under an alternative.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9, p.19 and (vi), p.20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_armCount
import Definitions.Def_FairReplay_Supplement_TwoClassFamily
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_coverLP

open MeasureTheory

namespace FairReplay.Supplement

/-- A tester is **fixed-design** if its policy plays a deterministic schedule fixed in advance
(round `t` plays `sched t` whatever the history) and it stops after a fixed number `N` of rounds. -/
def IsFixedDesign {k : ℕ} (π : BanditAlgorithm.BanditPolicy k) (T : (ℕ → Fin k × ℝ) → ℕ∞) :
    Prop :=
  (∃ sched : ℕ → Fin k, ∀ t (h : BanditAlgorithm.BanditHistory k t),
      π.select t h = Measure.dirac (sched t)) ∧
    ∃ N : ℕ, ∀ ω, T ω = (N : ℕ∞)

namespace TwoClassFamily

/-- The **declared cost** of a run: `Σ_i c_i N_i`, with `N_i` the number of queries of group `i`
before stopping (Theorem 10.9, p.19: "declared cost"). The final idle action of `groupModel` has
zero declared cost. -/
noncomputable def declaredCost (F : TwoClassFamily) (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
    (ω : ℕ → Fin (F.k + 1) × ℝ) : ENNReal :=
  ∑ i, ENNReal.ofReal (F.c i) * armCount (Fin.castSucc i) T ω

/-- The **boundary-block cost** of a run: the declared cost spent on groups that contain an
unmatched candidate (Theorem 10.9(vi), eq. (77), p.20). Such groups contain no other high vertex. -/
noncomputable def boundaryCost (F : TwoClassFamily) (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
    (ω : ℕ → Fin (F.k + 1) × ℝ) : ENNReal := by
  classical exact
    ∑ i ∈ Finset.univ.filter (fun i => (F.S i ∩ F.unmatched).Nonempty),
      ENNReal.ofReal (F.c i) * armCount (Fin.castSucc i) T ω

/-- **δ-correctness in the P19 family** (Theorem 10.9, p.19; "pointwise type-II error"): type-I
error at most `δ` under the simple null and type-II error at most `δ` under every singleton
alternative `x ∈ A`. A run that never stops counts as an error under an alternative. -/
def IsGroupDeltaCorrect (F : TwoClassFamily) (p s τ d δ : ℝ)
    (π : BanditAlgorithm.BanditPolicy (F.k + 1)) (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool) : Prop :=
  BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π {ω | T ω < ⊤ ∧ ψ ω = true} ≤
      ENNReal.ofReal δ ∧
    ∀ x ∈ F.A, BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d (some x)) π
      {ω | ¬ (T ω < ⊤ ∧ ψ ω = true)} ≤ ENNReal.ofReal δ

/-- **The optimal expected null declared cost** `Q⋆₀(d)` (Sah, Zhang, Lian, *Testing Fairness of
Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, Theorem 10.9(vi), p.20 (PDF p.22): "Q⋆0(d) denotes the optimal expected null
declared cost in this P19 family").

The infimum, over all adaptive (possibly randomized) partial-replay testers that are δ-correct in the
P19 family, of the expected declared cost under the simple null.

**Formalization Note** Expectations are lower integrals and the infimum is in `[0, ∞]`. The stopping
time is named `T` (the paper's `τ` is the high-class shift). The model has one deterministic
zero-cost idle action in addition to the legal groups, so a zero-query tester is representable even
when the legal-group family is empty; this action carries no information. -/
noncomputable def Qstar0 (F : TwoClassFamily) (p s τ d δ : ℝ) : ENNReal :=
  ⨅ (π : BanditAlgorithm.BanditPolicy (F.k + 1)) (T : (ℕ → Fin (F.k + 1) × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin (F.k + 1) × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T)
    (_ : Measurable[hT.measurableSpace] ψ) (_ : F.IsGroupDeltaCorrect p s τ d δ π T ψ),
    ∫⁻ ω, F.declaredCost T ω ∂BanditAlgorithm.banditTrajMeasure (F.groupModel p s τ d none) π

end TwoClassFamily

end FairReplay.Supplement


