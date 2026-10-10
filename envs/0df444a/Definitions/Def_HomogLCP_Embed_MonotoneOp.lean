-- Prove2me | Definitions.Def_HomogLCP_Embed_MonotoneOp
-- name    : HomogLCP_Embed_MonotoneOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:40:41.799045+00:00
-- url     : https://prove2.me/theorems/2d89145a-40bc-41a3-9b53-af9daaf82d46
-- title:
--   §2, p. 3 — operators on ℝ^d × ℝ as graphs; monotone and maximal monotone operators
-- statement:
--   Throughout, $\mathbb R^{d+1}$ is identified with $\mathbb R^d\times\mathbb R$, with points written $u=(z,\tau)$ and the Euclidean inner product
--   $$\langle (z,\tau),(w,\kappa)\rangle = z^\top w+\tau\kappa .$$
--
--   1. **Operators.** An operator (relation, point-to-set mapping, multi-valued function) $F$ on $\mathbb R^d\times\mathbb R$ is identified with its graph, a subset of $(\mathbb R^d\times\mathbb R)\times(\mathbb R^d\times\mathbb R)$; $F(x)=\{y \mid (x,y)\in F\}$.
--   2. **Monotone.** $F$ is monotone if
--   $$(u-v)^\top(x-y)\ \ge\ 0\qquad\text{for all } (x,u),(y,v)\in F .$$
--   3. **Maximal monotone.** A monotone operator $F$ is maximal if it is not strictly contained in another monotone operator: whenever $F\subseteq F'$ and $F'$ is monotone, $F'=F$.
--
--   These are the notions of monotone operator theory in which the paper's embedding operators $\mathcal F$, $\mathcal I$ and $\mathcal Q=\mathcal F\cup\mathcal I$ are studied; maximal monotonicity is what Douglas–Rachford splitting requires for guaranteed convergence.
--
--   **Formalization Note** Points of $\mathbb R^{d+1}$ are pairs in `(Fin d → ℝ) × ℝ` and the inner product is `pair u v = u.1 ⬝ᵥ v.1 + u.2 * v.2`. An operator is a `Set` of (point, value) pairs. The paper defines these notions for operators on $\mathbb R^d$; they are stated here on $\mathbb R^d\times\mathbb R$, the only space on which the mission uses them. Maximality is the containment form of the page's definition; the page's "i.e." form (adding any pair not already in $F$ breaks monotonicity) is equivalent.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, p. 3, §2 (operators, monotone, maximal monotone)

import Mathlib

namespace HomogLCP.Embed

open Matrix

/-- The Euclidean inner product of `ℝ^{d+1} = ℝ^d × ℝ`: `(z, τ)ᵀ(w, κ) = zᵀw + τκ`. -/
def pair {d : ℕ} (u v : (Fin d → ℝ) × ℝ) : ℝ := u.1 ⬝ᵥ v.1 + u.2 * v.2

/-- An operator (relation, set-valued map) on `ℝ^d × ℝ`, given by its graph: an element
`a` of the graph is a pair `(a.1, a.2)` = (point, value), so `F(x) = {y | (x, y) ∈ F}`. -/
abbrev Op (d : ℕ) := Set (((Fin d → ℝ) × ℝ) × ((Fin d → ℝ) × ℝ))

/-- Monotone operator (§2, p. 3): `(u - v)ᵀ(x - y) ≥ 0` for all `(x, u), (y, v) ∈ F`. -/
def IsMonotoneOp {d : ℕ} (T : Op d) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, 0 ≤ pair (a.2 - b.2) (a.1 - b.1)

/-- Maximal monotone operator (§2, p. 3): a monotone operator that is not strictly contained
in another monotone operator on `ℝ^d × ℝ`. -/
def IsMaximalMonotoneOp {d : ℕ} (T : Op d) : Prop :=
  IsMonotoneOp T ∧ ∀ T' : Op d, IsMonotoneOp T' → T ⊆ T' → T' = T

end HomogLCP.Embed


