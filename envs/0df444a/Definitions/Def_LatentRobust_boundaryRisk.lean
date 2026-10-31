-- Prove2me | Definitions.Def_LatentRobust_boundaryRisk
-- name    : LatentRobust_boundaryRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:20.303008+00:00
-- url     : https://prove2.me/theorems/384f1d0c-52bf-473b-84d1-f8c3153a66f0
-- title:
--   Standard, adversarial and boundary risk (1), (3), (4)
-- statement:
--   Let $P$ be the joint law of a feature–label pair $(x,y)$ with $x\in\mathbb R^d$ and $y\in\{+1,-1\}$, and let $h:\mathbb R^d\to\{+1,-1\}$ be a classifier. For an $\ell_p$ adversary of power $\varepsilon$:
--
--   1. the **standard risk** (1) is $\mathrm{SR}(h)=P\big(h(x)y\le 0\big)$;
--   2. the **adversarial risk** (3) is
--   $$
--   \mathrm{AR}(h)=P\Big(\inf_{\|x'-x\|_{\ell_p}\le\varepsilon} h(x')y\le 0\Big);
--   $$
--   3. the **boundary risk** (4) is $\mathrm{BR}(h)=\mathrm{AR}(h)-\mathrm{SR}(h)$.
--
--   The boundary risk is the probability that a correctly classified point has a misclassified point within distance $\varepsilon$; the paper studies when it vanishes for the Bayes-optimal classifier.
--
--   **Formalization Note** $P$ is a measure on $\mathbb R^d\times\mathbb R$ (feature, label). For a $\{\pm1\}$-valued classifier the infimum is $\le 0$ exactly when some $x'$ in the closed ball has $h(x')y\le0$, and the adversarial event is written in that form.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, §2.1, p.5 eq. (1), (3) and p.6 eq. (4)

import Mathlib
import Definitions.Def_LatentRobust_lpNorm

namespace LatentRobust

open MeasureTheory

/-- The standard risk (1) (Javanmard, Mehrabi, arXiv:2110.11950v2, §2.1, p.5):
`SR(h) := P(h(x)y ≤ 0)` for a classifier `h` and a joint law `P` of `(x, y)`.

**Formalization Note** `P` is a measure on `ℝ^d × ℝ` (feature, label); the theorems assume it is
a probability measure whose labels lie in `{+1, −1}`. -/
noncomputable def standardRisk {d : ℕ} (P : Measure ((Fin d → ℝ) × ℝ))
    (h : (Fin d → ℝ) → ℝ) : ℝ :=
  (P {xy | h xy.1 * xy.2 ≤ 0}).toReal

/-- The adversarial risk (3) (Javanmard, Mehrabi, arXiv:2110.11950v2, §2.1, p.5) against an
`ℓp`-norm bounded adversary of power `ε`:
`AR(h) = P( inf_{‖x′−x‖_{ℓp} ≤ ε} h(x′)y ≤ 0 )`.

**Formalization Note** For a `{±1}`-valued classifier the infimum of `h(x′)y` over the ball is
`≤ 0` exactly when some `x′` in the ball has `h(x′)y ≤ 0`, so the event is written in this
`∃`-form instead of with a real infimum. The ball is the closed `ℓp` ball `‖x′ − x‖_{ℓp} ≤ ε`. -/
noncomputable def adversarialRisk {d : ℕ} (p ε : ℝ) (P : Measure ((Fin d → ℝ) × ℝ))
    (h : (Fin d → ℝ) → ℝ) : ℝ :=
  (P {xy | ∃ x' : Fin d → ℝ, lpNorm p (x' - xy.1) ≤ ε ∧ h x' * xy.2 ≤ 0}).toReal

/-- The boundary risk (4) (Javanmard, Mehrabi, arXiv:2110.11950v2, §2.1, p.6):
`BR(h) := AR(h) − SR(h)`, the adversarial risk against an `ℓp` adversary of power `ε` minus the
standard risk, under the joint law `P`. -/
noncomputable def boundaryRisk {d : ℕ} (p ε : ℝ) (P : Measure ((Fin d → ℝ) × ℝ))
    (h : (Fin d → ℝ) → ℝ) : ℝ :=
  adversarialRisk p ε P h - standardRisk P h

end LatentRobust


