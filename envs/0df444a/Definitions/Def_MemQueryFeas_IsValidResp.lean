-- Prove2me | Definitions.Def_MemQueryFeas_IsValidResp
-- name    : MemQueryFeas_IsValidResp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:27.503037+00:00
-- url     : https://prove2.me/theorems/1184594a-6d16-4e22-a232-d63bcf3ed1f2
-- title:
--   Valid separation-oracle response
-- statement:
--   Let $Q\subseteq\mathbb R^d$ and let $x$ be a query. A response $r\in\mathbb R^d\cup\{\mathrm{Success}\}$ is **valid** for $Q$ at $x$ if it is Success exactly when $x\in Q$, and a returned normal $g$ separates $x$ from $Q$:
--   $$
--   g^\top(y-x)<0\qquad\text{for all }y\in Q.
--   $$
--
--   **Formalization Note** Responses are `Option (Vec d)`, with `none` standing for Success.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_MemQueryFeas_Vec

namespace MemQueryFeas

/-- **Valid separation-oracle response.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4): "given a query
`x_t ∈ B_d(0,1)`, the oracle returns Success if `x_t ∈ Q`, and otherwise returns a separating
hyperplane with its normal `g_t ∈ ℝ^d` … satisfying `g_t^⊤(y − x_t) < 0` for all `y ∈ Q`".

`IsValidResp Q x r`: the response `r` is Success (`none`) exactly when `x ∈ Q`, and a response
`some g` satisfies `⟪g, y − x⟫ < 0` for every `y ∈ Q`.

**Formalization Note.** The response set `ℝ^d ∪ {Success}` is `Option (Vec d)`, with `none` for
Success. -/
def IsValidResp {d : ℕ} (Q : Set (Vec d)) (x : Vec d) (r : Option (Vec d)) : Prop :=
  (r = none ↔ x ∈ Q) ∧ ∀ g : Vec d, r = some g → ∀ y ∈ Q, inner ℝ g (y - x) < 0

end MemQueryFeas


