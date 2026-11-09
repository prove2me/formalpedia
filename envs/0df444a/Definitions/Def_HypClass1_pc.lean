-- Prove2me | Definitions.Def_HypClass1_pc
-- name    : HypClass1_pc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:30:53.136056+00:00
-- url     : https://prove2.me/theorems/b6c141a7-b679-4fd4-9842-2bafdc8d932e
-- title:
--   Critical probability $p_c(\mathcal B)$
-- statement:
--   For a non-empty increasing family $\mathcal B \subseteq 2^X$, $p \mapsto \mu_p(\mathcal B)$ is strictly increasing, and the **critical probability** $p_c(\mathcal B)$ is the unique $p$ with $\mu_p(\mathcal B) = 1/2$.
--
--   **Formalization Note** $p_c(\mathcal B) := \inf\{p \in [0,1] : \mu_p(\mathcal B) \ge 1/2\}$, which is the unique solution when $\emptyset \notin \mathcal B$ (continuity and strict monotonicity of the polynomial $\mu_p(\mathcal B)$, from $0$ at $p=0$ to $1$ at $p=1$). If $\emptyset \in \mathcal B$ the paper's $p_c$ is undefined and the value is $0$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.42

import Mathlib
import Definitions.Def_HypClass1_muP

namespace HypClass1

/-- **Critical probability** `p_c(B)`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.42: "Since B is increasing, it follows that µ_p(B)
is strictly increasing in p. Let p_c(B) denote the unique value of p such that µ_p(B) = 1/2."

**Formalization Note.** `p_c(B) := inf {p ∈ [0, 1] : µ_p(B) ≥ 1/2}`. For a non-empty increasing family
with `∅ ∉ B`, `p ↦ µ_p(B)` is a continuous strictly increasing polynomial from `0` to `1` on `[0, 1]`,
so this infimum is the unique `p` with `µ_p(B) = 1/2`. If `∅ ∈ B` (then `B = 2^X` and `µ_p(B) = 1`), the
paper's `p_c` is undefined and this definition gives `0`. -/
noncomputable def pc {α : Type*} [Fintype α] [DecidableEq α] (B : Finset (Finset α)) : ℝ :=
  sInf {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ 1 / 2 ≤ muP p B}

end HypClass1


