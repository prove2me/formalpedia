-- Prove2me | Definitions.Def_CoffmanMitrani_Achieves
-- name    : CoffmanMitrani_Achieves
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:16:17.821629+00:00
-- url     : https://prove2.me/theorems/4d92b38e-a140-418c-a6ec-7a9b668a903f
-- title:
--   A strategy achieves a performance vector
-- statement:
--   A schedule $S$ achieves the vector $W = (W_1,\dots,W_M)$ if, for every class $i$, each response time $w_i^{(n)}$ of the $n$-th class-$i$ job is integrable and
--   $$W_i = \lim_{n\to\infty} \mathbb E\big(w_i^{(n)}\big).$$
--   $W_i$ is the paper's *response time* of class $i$, and $W$ is the performance vector of $S$.
--
--   **Formalization Note** The integrability requirement excludes the convention that the integral of a non-integrable function is $0$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_P
import Definitions.Def_CoffmanMitrani_responseTime
open MeasureTheory ProbabilityTheory

namespace CoffmanMitrani

/-- **A strategy achieves a performance vector.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811: "We shall consistently assume the existence of the limiting, equilibrium mean
value Wi = lim_{n→∞} E(wi(n)), to be called the response time of the ith job class. For our purposes
system performance will be measured by the vector of response times W = (W1, W2, ···, WM)."

`Achieves D S W` holds when, for every class `i`, every response time `wi(n)` is integrable under
`D.P` and `E(wi(n)) → W i` as `n → ∞`.

**Formalization Note.** The integrability conjunct excludes the junk value `∫ = 0` of a
non-integrable function; under `ρ < 1` every response time of a strategy is integrable (it is at
most the length of its busy period). The limit is along the class-`i` job index, as in the paper. -/
def Achieves (D : Data) (S : Schedule D.M) (W : Fin D.M → ℝ) : Prop :=
  ∀ i : Fin D.M,
    (∀ n : ℕ, Integrable (fun ω => responseTime S (i, n) ω) D.P) ∧
    Filter.Tendsto (fun n : ℕ => ∫ ω, responseTime S (i, n) ω ∂D.P) Filter.atTop
      (nhds (W i))

end CoffmanMitrani


