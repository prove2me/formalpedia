-- Prove2me | Definitions.Def_CausalFailureRank_J
-- name    : CausalFailureRank_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:10.450134+00:00
-- url     : https://prove2.me/theorems/4e13bd8e-ab31-46f1-8b48-29242d3d99df
-- title:
--   Local penalty value $J_i(t)$ and the posterior-error SPRT
-- statement:
--   For the fresh experiment of stage $i$, the **local penalty value** is
--   $$J_i(t)=\inf_{T,\hat X}\mathbb E\big[c_iT+t\,\mathbf 1\{\hat X\ne X_i\}\big],\qquad t\ge0,$$
--   over randomized sequential tests with no observation cap and arbitrary (not only MAP) decisions. The **posterior-error SPRT with target $p$** stops as soon as the posterior probability of error is at most $p$, and writes the MAP value.
--
--   This is the Bayes sequential-testing problem of one stage.
--
--   **Formalization Note** $J$ takes values in $[0,\infty]$. A test that never decides counts as an error, and has infinite cost anyway. A MAP tie is resolved in favour of $1$.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.1, p.15

import Mathlib
import Definitions.Def_CausalFailureRank_tapeLaw

open MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- The first `n` entries of a tape. -/
def tapePrefix {α : Type} (tape : ℕ → α) (n : ℕ) : List α :=
  (List.range n).map tape

open scoped Classical in
/-- The stopping time of a sequential rule on a tape, `⊤` if it never decides. The rule reads the
observed prefix and answers `some b` to stop and decide `b`, `none` to buy the next observation. -/
noncomputable def stopTime {α : Type} (rule : List α → Option Bool) (tape : ℕ → α) : ℕ∞ :=
  if h : ∃ n, (rule (tapePrefix tape n)).isSome then (Nat.find h : ℕ) else ⊤

open scoped Classical in
/-- The decision of a sequential rule on a tape, `none` if it never decides. -/
noncomputable def decisionOf {α : Type} (rule : List α → Option Bool) (tape : ℕ → α) : Option Bool :=
  if h : ∃ n, (rule (tapePrefix tape n)).isSome then rule (tapePrefix tape (Nat.find h)) else none

/-- A randomized sequential test of the fact of stage `i`: a private seed and a sequential rule. -/
structure LocalTest (I : Instance N q) (i : Fin N) where
  /-- The seed space. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The law of the seed. -/
  ν : Measure Ω
  [probν : IsProbabilityMeasure ν]
  /-- The sequential rule, given the seed. -/
  rule : Ω → List (I.α i) → Option Bool
  measurable_rule : ∀ h a, MeasurableSet {s | rule s h = a}

attribute [instance] LocalTest.mΩ LocalTest.probν

open scoped Classical in
/-- **The local penalty value** `J_i(t) = inf_{T, X̂} E[c_i T + t 1{X̂ ≠ X_i}]`, `t ≥ 0`. Zang, Li, Jin,
Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of
2026-11-03, sha256 721c8b0d…), App. B.1, p.15. "The infimum allows randomized tests and non-MAP
decisions", with no observation cap.

**Formalization Note.** Valued in `ℝ≥0∞`, with `T` possibly infinite; a run that never decides is
counted as an error and has infinite cost anyway, since `c_i > 0`. -/
noncomputable def J (I : Instance N q) (i : Fin N) (t : ℝ) : ENNReal :=
  ⨅ τ : LocalTest I i,
    ∫⁻ x, ENNReal.ofReal (I.c i) * ((stopTime (τ.rule x.1) x.2.2 : ℕ∞) : ENNReal) +
        ENNReal.ofReal t * (if decisionOf (τ.rule x.1) x.2.2 = some x.2.1 then 0 else 1)
      ∂(τ.ν.prod (stageLaw I i))

/-- The posterior probability of `X_i = true` after observing `ys`. -/
noncomputable def posterior (I : Instance N q) (i : Fin N) (ys : List (I.α i)) : ℝ :=
  let L := fun x => (ys.map fun y => (I.P i x y).toReal).prod
  I.prior i * L true / (I.prior i * L true + (1 - I.prior i) * L false)

open scoped Classical in
/-- **The posterior-error SPRT with target `p`**, App. B.1, p.15, writing MAP at the stop.
It stops as soon as the posterior error is at most `p`.

**Formalization Note.** A MAP tie goes to `true`; the bound is on the posterior error, so any fixed
tie rule does. -/
noncomputable def sprtRule (I : Instance N q) (i : Fin N) (p : ℝ) (ys : List (I.α i)) : Option Bool :=
  if min (posterior I i ys) (1 - posterior I i ys) ≤ p then some (decide (1 / 2 ≤ posterior I i ys))
  else none

end CausalFailureRank


