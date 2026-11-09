-- Prove2me | Definitions.Def_HighConfRobust_renyiDivergence
-- name    : HighConfRobust_renyiDivergence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:05:28.325217+00:00
-- url     : https://prove2.me/theorems/eaec5bc5-935d-46d7-985f-fdedc00cc73d
-- title:
--   Rényi divergence $D_q(P\,\|\,Q)$, $q \ge 1$
-- statement:
--   Let $P$ and $Q$ be probability measures on the same measurable space and let $q\ge 1$. If $P$ is absolutely continuous with respect to $Q$, the **Rényi divergence of order $q$** is
--
--   $$
--   D_q(P\,\|\,Q)=\begin{cases}\dfrac{1}{q-1}\log\displaystyle\int\Big(\frac{dP}{dQ}\Big)^{q}\,dQ, & q>1,\\[2ex] \displaystyle\int\log\Big(\frac{dP}{dQ}\Big)\,dP, & q=1,\end{cases}
--   $$
--
--   and otherwise $D_q(P\,\|\,Q)=+\infty$. Thus $D_1$ is the Kullback–Leibler divergence.
--
--   Rényi divergences control how much the probability of an event can change between two laws; the mission uses them for orders $q\in(1,2]$ to transfer the failure probability of an algorithm from a reference law to a contaminated one.
--
--   **Formalization Note** The value lies in the extended reals. For $q\ne 1$ it is the public definition `PADMPriv.renyiDiv` (Radon–Nikodym derivative with respect to $Q$, nonnegative extended integral). For $q=1$ it is Mathlib's `klDiv`, which for probability measures equals $\int\log(dP/dQ)\,dP$ when this integral is finite and $+\infty$ otherwise. A separate branch is needed because the factor $1/(q-1)$ of `PADMPriv.renyiDiv` is $0$ in Lean at $q=1$.
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Definition 3.2, p.16

import Mathlib
import Definitions.Def_PADMPriv_renyiDiv

namespace HighConfRobust

open MeasureTheory

/-- The **Rényi divergence** `D_q(P ‖ Q)` of order `q ≥ 1` (Definition 3.2, p.16):
for `q > 1` and `P ≪ Q` it is `(q − 1)⁻¹ log ∫ (dP/dQ)^q dQ`; for `q = 1` and `P ≪ Q` it is
`∫ log (dP/dQ) dP`, the Kullback–Leibler divergence; otherwise it is `+∞`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153),
Definition 3.2, p.16.

**Formalization Note** Values in `EReal`. For `q ≠ 1` this is the public `PADMPriv.renyiDiv q P Q`
(Radon–Nikodym derivative with respect to `Q`, `ℝ≥0∞` lower integral, `+∞` when `P` is not
absolutely continuous with respect to `Q`). For `q = 1` it is Mathlib's `InformationTheory.klDiv`,
which for probability measures is `∫ log (dP/dQ) dP` when `P ≪ Q` and the log-likelihood ratio is
`P`-integrable, and `+∞` otherwise (the negative part is always integrable, so `+∞` is the value
of the integral in the remaining case). The separate branch is needed because
`PADMPriv.renyiDiv 1 P Q` carries the factor `(1 − 1)⁻¹ = 0` in Lean. Only `q ≥ 1` is used. -/
noncomputable def renyiDivergence {X : Type*} [MeasurableSpace X] (q : ℝ) (P Q : Measure X) :
    EReal :=
  if q = 1 then ((InformationTheory.klDiv P Q : ENNReal) : EReal) else PADMPriv.renyiDiv q P Q

end HighConfRobust


