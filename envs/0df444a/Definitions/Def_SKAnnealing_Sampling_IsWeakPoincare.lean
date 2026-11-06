-- Prove2me | Definitions.Def_SKAnnealing_Sampling_IsWeakPoincare
-- name    : SKAnnealing_Sampling_IsWeakPoincare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:30.964353+00:00
-- url     : https://prove2.me/theorems/fda2aaaa-dc4d-456f-b079-6f05fc18e9e3
-- title:
--   Poincaré and $(\rho,\varepsilon)$-weak Poincaré inequalities
-- statement:
--   Let $p$ be a law on $\{\pm1\}^N$ with Glauber Dirichlet form $\mathcal E_p$. The law $p$ satisfies a **Poincaré inequality with constant $\rho$** if
--   $$\mathbf{Var}_p[f]\le\rho\,\mathcal E_p(f,f)\qquad\text{for all }f:\{\pm1\}^N\to\mathbb R,$$
--   and a **$(\rho,\varepsilon)$-weak Poincaré inequality** if
--   $$\mathcal E_p(f,f)\ \ge\ \frac1\rho\Big(\mathbf{Var}_p[f]-\varepsilon\,\|f\|_\infty^2\Big)\qquad\text{for all }f,$$
--   where $\|f\|_\infty$ is the largest value of $|f|$ on the support of $p$.
--
--   With $\varepsilon=0$ the weak inequality is the Poincaré inequality, equivalent to a spectral gap $1/\rho$ for Glauber dynamics. For $\varepsilon>0$ it still gives rapid mixing from a warm start down to total variation about $\sqrt\varepsilon$, which is what simulated annealing needs.
--
--   **Formalization Note** For the full-support Gibbs measures of the paper, the support is the whole cube and $\|f\|_\infty$ is the usual supremum norm.
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), display (2), p. 2; Lemma 1.5, p. 4; Lemma 2.4, p. 11

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_glauberKernel

open OAI.CriticalSK
open scoped NNReal

namespace SKAnnealing.Sampling

/-- `‖f‖_∞` on the support of `p`: the largest `|f x|` over `x` with `p x > 0` (`0` if there is none). -/
noncomputable def lawSupNorm {N : ℕ} (p : Spin N → ℝ) (f : Spin N → ℝ) : ℝ :=
  (((Finset.univ.filter fun x : Spin N => 0 < p x).sup fun x => ‖f x‖₊ : ℝ≥0) : ℝ)

/-- `p` satisfies a **Poincaré inequality with constant `ρ`**: `Var_p[f] ≤ ρ · E(f, f)` for every `f`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), p. 2 (display (2) with `ε = 0`), Lemma 1.5 (p. 4), Lemma 2.4 (p. 11). -/
def IsPoincare {N : ℕ} (p : Spin N → ℝ) (ρ : ℝ) : Prop :=
  ∀ f : Spin N → ℝ, lawVar p f ≤ ρ * glauberDirichlet p f

/-- `p` satisfies a **`(ρ, ε)`-weak Poincaré inequality**, display (2):
`E(f, f) ≥ ρ⁻¹ (Var_p[f] − ε ‖f‖_∞^2)` for every `f : {±1}^N → ℝ`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), display (2), p. 2.

**Formalization Note** Reading R7: `E` is `glauberDirichlet` (the discrete Glauber chain, factor `N⁻¹`)
and `‖f‖_∞` is the supremum over the support of `p` (`lawSupNorm`); for the full-support laws of the
paper this is the supremum over `{±1}^N`. Positivity of `ρ` is a hypothesis of the theorems that use it. -/
def IsWeakPoincare {N : ℕ} (p : Spin N → ℝ) (ρ ε : ℝ) : Prop :=
  ∀ f : Spin N → ℝ, (1 / ρ) * (lawVar p f - ε * lawSupNorm p f ^ 2) ≤ glauberDirichlet p f

end SKAnnealing.Sampling


