-- Prove2me | Definitions.Def_SpiderDiameter_ValueFunction
-- name    : SpiderDiameter_ValueFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:39.088123+00:00
-- url     : https://prove2.me/theorems/5aba421e-38ee-4933-aa91-84fadec76c8b
-- title:
--   Gain $G$, the two-stage strategy $\tau^*$, its value, and the value function (3.3)
-- statement:
--   Let $G(x,y,z)=y-z-x^2$. For a start $(x,y,z)\in\mathcal D$ define:
--
--   1. the **strategy** of Step 7: "Stage 1. Wait until $f(Z)\le g(Y)$ is observed for the first time. Stage 2. Wait until $f(Z)\le X\le g(Y)$", with $g(y)=y-\tfrac12$; since the Stage 2 condition implies the Stage 1 condition, this is the hitting time $\tau^*=\inf\{t\ge0: f(Z_t)\le X_t\le Y_t-\tfrac12\}$;
--   2. the **strategy value** $\mathbb E_{x,y,z}G(X_{\tau^*},Y_{\tau^*},Z_{\tau^*})$, which the paper calls $U$ from Step 7 on;
--   3. the **value function** (3.3)
--   $$\mathbb U(x,y,z)=\sup_\tau \mathbb E_{x,y,z}G(X_\tau,Y_\tau,Z_\tau),$$
--   the supremum over all integrable stopping times $\tau$ of $X$.
--
--   **Formalization Note** Expectations are Bochner integrals; every theorem about the strategy value also asserts that $\tau^*<\infty$ almost surely and that the gain is integrable. The value function is a supremum of real numbers; stopping times with non-integrable gain are left out (their gain has integrable positive part, so their expectation is $-\infty$), and statements about it assert that the set of values is bounded above.
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, §3: G and (3.3), p.13; g(y) = y − 1/2, Step 5, p.14; strategy and U = E G(X_τ, Y_τ, Z_τ), Step 7, p.14

import Mathlib
import Definitions.Def_SpiderDiameter_Noise
import Definitions.Def_SpiderDiameter_Candidate
import Definitions.Def_SpiderDiameter_GeneralProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpiderDiameter

/-! A family of tightly coupled definitions: the gain `G`, the guessed two-stage strategy of
§3 Step 7 and its value, and the value function `𝕌` of (3.3). -/

/-- **The gain** `G(x, y, z) = y − z − x²`.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, §3 Step 3, p.13. -/
def payoffG (x y z : ℝ) : ℝ := y - z - x ^ 2

/-- **The guessed optimal stopping time** of §3 Step 7, p.14: "Stage 1. Wait until the equality
f(Z) ≤ g(Y) is observed for the first time. Stage 2. Wait until f(Z) ≤ X ≤ g(Y)", with
`g(y) = y − 1/2` (Step 5, p.14) and `f = finv n`.

**Formalization Note.** The Stage 2 condition `f(Z_t) ≤ X_t ≤ Y_t − 1/2` implies the Stage 1
condition `f(Z_t) ≤ Y_t − 1/2`, so the combined rule is the first time `t ≥ 0` at which the Stage 2
condition holds: `τ* = inf {t ≥ 0 : f(Z_t) ≤ X_t ≤ Y_t − 1/2}` in `[0, ∞]` (`inf ∅ = ∞`). -/
noncomputable def stratTime {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (ω : Ω) : ℝ≥0∞ :=
  sInf {u : ℝ≥0∞ | ∃ t : ℝ≥0, u = t ∧
    finv n (Zg N x y z t ω) ≤ Xg N x y z t ω ∧ Xg N x y z t ω ≤ Yg N x y z t ω - 1 / 2}

/-- The gain `G(X_{τ*}, Y_{τ*}, Z_{τ*})` collected by the strategy `τ*` started from `(x, y, z)`. -/
noncomputable def stratPayoff {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) (ω : Ω) : ℝ :=
  payoffG (atTime (Xg N x y z) (stratTime N x y z) ω) (atTime (Yg N x y z) (stratTime N x y z) ω)
    (atTime (Zg N x y z) (stratTime N x y z) ω)

/-- **The value of the strategy** `E_{x,y,z} G(X_{τ*}, Y_{τ*}, Z_{τ*})`, the function called `U`
from §3 Step 7, p.14, on ("we shall henceforth set U(x, y, z) = E_{x,y,z}G(X_τ, Y_τ, Z_τ)").

**Formalization Note.** A Bochner integral: every statement about it also asserts that the gain is
integrable and that `τ* < ∞` almost surely, so the junk values are never used. -/
noncomputable def stratValue {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (N : SpiderNoise n P) (x y z : ℝ) : ℝ :=
  ∫ ω, stratPayoff N x y z ω ∂P

/-- The set of expected gains `E_{x,y,z} G(X_τ, Y_τ, Z_τ)` over integrable stopping times `τ` of
`X` whose gain is integrable (the set whose supremum is (3.3)). -/
def valueSet {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : SpiderNoise n P) (x y z : ℝ) : Set ℝ :=
  {r | ∃ τ : Ω → ℝ≥0∞, IsXStoppingTime N x y z τ ∧ ∫⁻ ω, τ ω ∂P < ⊤ ∧
    Integrable (fun ω => payoffG (atTime (Xg N x y z) τ ω) (atTime (Yg N x y z) τ ω)
      (atTime (Zg N x y z) τ ω)) P ∧
    r = ∫ ω, payoffG (atTime (Xg N x y z) τ ω) (atTime (Yg N x y z) τ ω)
      (atTime (Zg N x y z) τ ω) ∂P}

/-- **The value function** `𝕌(x, y, z) = sup E_{x,y,z} G(X_τ, Y_τ, Z_τ)`, the supremum over all
integrable stopping times `τ` of `X`.
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, eq. (3.3), p.13.

**Formalization Note.** A supremum of real numbers (`sSup`); statements about it assert that the
set is bounded above. Stopping times whose gain is not integrable are left out: the positive part
of the gain is at most `Y_τ − Z_τ`, which is integrable for every integrable `τ`, so a
non-integrable gain has expectation `−∞` and does not affect the supremum. -/
noncomputable def valueFn {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : SpiderNoise n P) (x y z : ℝ) : ℝ :=
  sSup (valueSet P N x y z)

end SpiderDiameter


