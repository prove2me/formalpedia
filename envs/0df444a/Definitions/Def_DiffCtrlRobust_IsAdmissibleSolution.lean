-- Prove2me | Definitions.Def_DiffCtrlRobust_IsAdmissibleSolution
-- name    : DiffCtrlRobust_IsAdmissibleSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:10.800208+00:00
-- url     : https://prove2.me/theorems/949212ab-6506-4b09-b861-e343f26a9d45
-- title:
--   Admissible control $U$ with solution $X$ of (2.1)
-- statement:
--   A pair $(U,X)$ on the given probability space is admissible from $x$ if $U$ is a $\mathrm V$-valued process, $W_t-W_s$ is independent of $\mathfrak F_s$ for $s<t$ (non-anticipativity), and $X$ is a continuous $\mathfrak F$-adapted process with, almost surely for all $t\ge0$,
--
--   $$
--   X_t=x+\int_0^t b(X_s,U_s)\,\mathrm ds+\int_0^t\sigma(X_s)\,\mathrm dW_s .
--   $$
--
--   The set of admissible controls is denoted $\mathfrak U$. Non-anticipativity also makes $W$ a Brownian motion for $\mathfrak F$, so the Itô integral is well defined.
--
--   **Formalization Note** $U$ is jointly measurable in $(t,\omega)$, which is what "$\mathrm V$-valued process" means here. The Itô integral is the published `EthierKurtz.HasBrownianItoIntegral`, taken against $\mathfrak F$.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2, p.5, (2.1) and the non-anticipativity condition

import Definitions.Def_DiffCtrlRobust_relaxed
import Definitions.Def_DiffCtrlRobust_admissiblePast
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- The pair `(u, X)` is an admissible control together with the solution of (2.1) from `x`
(arXiv:2205.05894v2, §2, p.5): `u` is a `V`-valued process, the increments `W_t - W_s` are
independent of `𝔉_s` (non-anticipativity), and `X` is the strong solution of
`dX_t = b(X_t, u_t) dt + σ(X_t) dW_t`, `X_0 = x`.

**Formalization Note.** Joint measurability of `u` makes "a `V`-valued process" precise. The clauses
on `X` are those of `EthierKurtz.SolvesBrownianSDE`, against the filtration `𝔉` of the paper and
with the drift `b(X_t, u_t)`, which depends on `ω` through `u`. The independence clause is also
what makes `W` a Brownian motion for `𝔉`, so that the Itô integrals are meaningful. It is stated
for `s ≤ t`; at `s = t` it says nothing. -/
def IsAdmissibleSolution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {U : Type*} [MeasurableSpace U]
    (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d) (b : SDEState d → U → SDEState d)
    (σ : SDEState d → SDEDiffusion d) (x : SDEState d)
    (u : ℝ≥0 → Ω → ProbabilityMeasure U) (X : ℝ≥0 → Ω → SDEState d) : Prop :=
  Measurable (fun p : ℝ≥0 × Ω => u p.1 p.2) ∧
  (∀ s t : ℝ≥0, s ≤ t → Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance)
    (admissiblePast P W u (fun _ => x) s) P) ∧
  (∀ t, Measurable (X t)) ∧
  (∀ ω, Continuous (fun t => X t ω)) ∧
  (∀ t, Measurable[admissiblePast P W u (fun _ => x) t] (X t)) ∧
  (X 0 =ᵐ[P] fun _ => x) ∧
  ∃ J : ℝ≥0 → Ω → SDEDiffusion d,
    (∀ ω, Continuous (fun t => J t ω)) ∧
    (∀ t, Measurable[admissiblePast P W u (fun _ => x) t] (J t)) ∧
    (∀ i j, HasBrownianItoIntegral P (admissiblePast P W u (fun _ => x))
      (fun t ω => W t ω j) (fun t ω => σ (X t ω) (i, j)) (fun t ω => J t ω (i, j))) ∧
    (∀ (t : ℝ≥0) ω i, IntervalIntegrable
      (fun r : ℝ => relaxed b (X r.toNNReal ω) (u r.toNNReal ω) i) volume 0 t.val) ∧
    ∀ᵐ ω ∂P, ∀ t i, X t ω i = X 0 ω i + (∑ j, J t ω (i, j)) +
      ∫ r in (0 : ℝ)..t.val, relaxed b (X r.toNNReal ω) (u r.toNNReal ω) i

end DiffCtrlRobust


