-- Prove2me | Definitions.Def_GeoSemialgCSP_multilin
-- name    : GeoSemialgCSP_multilin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:52.136601+00:00
-- url     : https://prove2.me/theorems/6ebbe0c0-081e-4c5c-89d8-cc62a5f6b5f9
-- title:
--   Multilinear extension of a payoff
-- statement:
--   For a payoff $f:[q]^k\to\mathbb R$ and vectors $u_1,\dots,u_k\in\mathbb R^q$, the **multilinear extension** is
--   $$f(u_1,\dots,u_k)=\sum_{a_1,\dots,a_k\in[q]}f(a_1,\dots,a_k)\prod_{j=1}^k u_j(a_j).$$
--   For probability vectors it is the expected payoff when the labels $a_j$ are drawn independently from $u_j$. For a relation $\Delta\subseteq[q]^k$, $\Delta[u_1,\dots,u_k]$ denotes the extension of its indicator.
--
--   **Formalization Note** $[q]=\{0,\dots,q-1\}$ is `Fin q`.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, p.12 (PDF p.13); §9, p.27 (PDF p.28)

import Mathlib

namespace GeoSemialgCSP

/-- **Multilinear extension.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, printed p.12 (PDF p.13), and §9, printed
p.27 (PDF p.28): for `f : [q]^k → ℝ` and vectors `u₁, …, u_k ∈ ℝ^q`,
`f(u₁, …, u_k) = ∑_{a ∈ [q]^k} f(a) ∏_j u_j(a_j)`. For a relation `Δ ⊆ [q]^k`, `Δ[u₁, …, u_k]` is
the extension of its indicator.

**Formalization Note.** `[q] = Fin q` (the paper's `[q] = {0, …, q−1}`); positions are `Fin k`. -/
def multilin {k q : ℕ} (f : (Fin k → Fin q) → ℝ) (u : Fin k → Fin q → ℝ) : ℝ :=
  ∑ a : Fin k → Fin q, f a * ∏ j, u j (a j)

end GeoSemialgCSP


