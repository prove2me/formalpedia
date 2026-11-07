-- Prove2me | Definitions.Def_ReplicableOL_advantage
-- name    : ReplicableOL_advantage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:13.126278+00:00
-- url     : https://prove2.me/theorems/88252319-0975-4e4e-ab03-a102e3df9cbd
-- title:
--   The comparator's advantage $A=\mathbb E|X|$
-- statement:
--   The **comparator's advantage** is
--   $$
--   A=\mathbb E|X|,
--   $$
--   over $\theta\sim U[-\Delta,\Delta]^k$ and $S\sim P_\theta$. It is the advantage of the best fixed expert over the baseline $kL/2$, and it is the scale of the main theorem.
--
--   **Formalization Note** The joint law of `(θ, S)` is written as an iterated integral: first `S` under `lawP`, then `θ` under the prior. The integrand is bounded on the prior's support, so both integrals are genuine; the verification file proves integrability.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.2, p.8

import Mathlib
import Definitions.Def_ReplicableOL_comparatorEdge
import Definitions.Def_ReplicableOL_lawP
import Definitions.Def_ReplicableOL_epochPrior
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **The comparator's advantage $A=\mathbb E|X|$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.2, p.8. `A := E|X|`.

**Formalization Note.** The joint law of `(θ, S)` is written as an iterated integral: first `S` under `lawP`, then `θ` under the prior. The integrand is bounded on the prior's support, so both integrals are genuine; the verification file proves integrability. -/
noncomputable def advantage (T L : ℕ) (Δ : ℝ) : ℝ :=
  ∫ θ, ∫ S, |comparatorEdge (T / L) L θ S| ∂(lawP T L θ) ∂(epochPrior (T / L) Δ)

end ReplicableOL


