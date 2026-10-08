-- Prove2me | Definitions.Def_OracleRO_ApproxFPL_IsApproxLinOracle
-- name    : OracleRO_ApproxFPL_IsApproxLinOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:10:47.893806+00:00
-- url     : https://prove2.me/theorems/a7f740e4-fa23-4638-9c4c-d4827b3ba49c
-- title:
--   The ε-approximate linear optimization procedure $M_\epsilon$ over a domain $\mathcal K$ (§3.3)
-- statement:
--   Let $\mathcal K \subseteq \mathbb R^n$ be a set (not necessarily convex, closed or bounded) and let $\epsilon$ be a real number. A map $M : \mathbb R^n \to \mathbb R^n$ is an **$\epsilon$-approximate linear optimization procedure** over $\mathcal K$ if, for every vector $g \in \mathbb R^n$, the output $M(g)$ lies in $\mathcal K$ and is $\epsilon$-optimal for the linear objective $x \mapsto g\cdot x$ over $\mathcal K$:
--   $$
--   M(g) \in \mathcal K \qquad\text{and}\qquad g \cdot M(g) \;\ge\; g \cdot x - \epsilon \quad \text{for every } x \in \mathcal K .
--   $$
--   Here $g \cdot x = \sum_{i=1}^n g_i x_i$ is the standard inner product.
--
--   This is the only access the Follow the Approximate Perturbed Leader algorithm has to the decision domain: it never needs exact linear optimization over $\mathcal K$, only an additive $\epsilon$-approximation. Every theorem of the mission holds for every procedure meeting this specification.
--
--   **Formalization Note** The paper writes $f\cdot M_\epsilon(f) \ge \max_{x\in\mathcal K} f\cdot x - \epsilon$; requiring the inequality against every $x\in\mathcal K$ is the same condition and does not presuppose that the maximum is attained. Membership $M(g)\in\mathcal K$ is implicit on the page (the outputs are decisions, and the proof of Lemma 8 bounds $\|M_\epsilon(f_{1:T})-M_\epsilon(f_0)\|_1$ by the diameter of $\mathcal K$); it is stated explicitly. A procedure meeting the specification forces $\mathcal K \neq \emptyset$.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 11, §3.3 (definition of the procedure M_ε)

import Mathlib

namespace OracleRO.ApproxFPL

/-- The approximate linear optimization procedure `M_ε` of §3.3 (Ben-Tal, Hazan, Koren, Mannor,
arXiv:1402.6361v1, p. 11): a map `M : ℝⁿ → ℝⁿ` that, for every reward vector `g`, returns a point
`M g` of the (not necessarily convex) domain `K` that is `ε`-optimal for the linear objective
`x ↦ g · x` over `K`, i.e. `g · M(g) ≥ g · x - ε` for every `x ∈ K`.

Formalization Note: the page writes `f · M_ε(f) ≥ max_{x ∈ K} f · x - ε`; the maximum is replaced
by a bound against every `x ∈ K`, which is the same condition and needs no attainment or `sSup`.
Membership `M g ∈ K` is implicit on the page (the output is a decision in `K`; the proof of
Lemma 8 bounds `‖M_ε(·) - M_ε(·)‖₁` by the diameter of `K`). -/
def IsApproxLinOracle {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ g : Fin n → ℝ, M g ∈ K ∧ ∀ x ∈ K, g ⬝ᵥ x - ε ≤ g ⬝ᵥ M g

end OracleRO.ApproxFPL


