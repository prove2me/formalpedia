-- Prove2me | Definitions.Def_MemQueryFeas_IsValidAdaptive
-- name    : MemQueryFeas_IsValidAdaptive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:34.935147+00:00
-- url     : https://prove2.me/theorems/696f9735-ce73-4629-ae64-08bda7609dce
-- title:
--   Valid adaptive separation oracle
-- statement:
--   An **adaptive oracle** maps the history of past queries $(x_0,\dots,x_{t-1})$ and the current query $x_t$ to a response in $\mathbb R^d\cup\{\mathrm{Success}\}$. It is **valid** for $Q$ if every response, after every history and at every query point, is a valid response for $Q$.
--
--   The response may depend on the round (the length of the history) and on all past queries, as allowed in the problem setup.
--
--   **Formalization Note** The oracle is a deterministic function of the history; validity is required at every point of $\mathbb R^d$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_MemQueryFeas_IsValidResp

namespace MemQueryFeas

/-- **Valid adaptive separation oracle.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4): "The oracle may be
time-dependent, randomized and adaptive: its response `g_t` may depend on the current query and the
previous history, as long as it remains a valid separating hyperplane for the feasible set `Q`."

An adaptive oracle is a map `O : List (Vec d) → Vec d → Option (Vec d)` sending (the list of past
queries `[x_0, …, x_{t-1}]`, the current query `x_t`) to a response. `IsValidAdaptive Q O` requires the
response to be valid (`IsValidResp`) for every history and every query point.

**Formalization Note.** The oracle is deterministic given the history; the round index is the length
of the history, so time-dependence is included. Validity is required at every history and every
point of `ℝ^d` (not only at points of the unit ball). -/
def IsValidAdaptive {d : ℕ} (Q : Set (Vec d)) (O : List (Vec d) → Vec d → Option (Vec d)) : Prop :=
  ∀ (h : List (Vec d)) (x : Vec d), IsValidResp Q x (O h x)

end MemQueryFeas


