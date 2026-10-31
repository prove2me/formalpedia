-- Prove2me | Definitions.Def_SampleMechDesign_IsDelineable
-- name    : SampleMechDesign_IsDelineable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:32.718602+00:00
-- url     : https://prove2.me/theorems/d5cfa073-657a-41e6-8fb3-95f228a69a50
-- title:
--   Definition 3.5, p.10 — $(d,t)$-delineable class (corrected: affine on arrangement cells)
-- statement:
--   Let $X$ be a set of valuations, and let a class of mechanisms be given by parameter vectors $p\in P\subseteq\mathbb R^d$, with $\mathrm{profit}_p(v)$ the profit of mechanism $p$ on $v$. The class is **$(d,t)$-delineable** if for every $v\in X$ there is a set $H$ of at most $t$ hyperplanes $\{p: a\cdot p=b\}$, $a\neq0$, such that on each cell of the arrangement the map $p\mapsto\mathrm{profit}_p(v)$ agrees on $P$ with one affine function:
--
--   $$
--   \exists\, a_\sigma\in\mathbb R^d,\ b_\sigma\in\mathbb R:\qquad \mathrm{profit}_p(v)=a_\sigma\cdot p+b_\sigma\quad\text{for all } p\in P \text{ with } \operatorname{sign}(a\cdot p-b)=\sigma(a,b)\ \ \forall (a,b)\in H.
--   $$
--
--   A cell is the set of points with one sign vector $\sigma\in\{-,0,+\}^H$, so the cells cover $\mathbb R^d$, lower-dimensional faces included. The definition says that for a fixed buyer profile, profit is piecewise affine in the parameters with few pieces; this is the structure that drives the main theorem.
--
--   **Formalization Note** The source asks for linearity on the connected components of $P\setminus H$, and that version makes Lemma 3.10 and Theorem 3.9 false: for $P=\mathbb N\subseteq\mathbb R$ the components are single points, and for $P=\mathbb R^2$ the points on $H$ are unconstrained. The cells above close both holes. For convex $P$ the two definitions agree off the hyperplanes. "Linear" means affine, as in the proof of Lemma 3.10, and "$t$ hyperplanes" means at most $t$, because adding hyperplanes refines the cells.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Definition 3.5, p.10 (PDF p.10), corrected; parameterized classes §3.1, p.8

import Mathlib

namespace SampleMechDesign

/-- **`(d, t)`-delineable class, corrected.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6,
Definition 3.5, p.10.

The class is the family of profit functions `profit p : X → ℝ` indexed by the parameter vectors
`p ∈ P ⊆ ℝ^d`. It is delineable when, for every valuation `v`, there are at most `t` hyperplanes
`{p | a ⬝ᵥ p = b}` with `a ≠ 0` such that `p ↦ profit p v` agrees with one affine function
`a ⬝ᵥ p + b` on `P ∩ C`, for each cell `C` of the arrangement. A cell is a class of points with
one sign vector `σ` in `{-, 0, +}^H`, so the cells cover `ℝ^d`, lower-dimensional faces included.

**Formalization Note.**
* Parameters are `Fin d → ℝ` and a hyperplane is a pair `(a, b)` with `a ≠ 0`, a point of the
  `Finset` `H`.
* Correction: the paper asks for linearity on the connected components of `P \ H`. For
  `P = ℕ ⊆ ℝ` those are single points, and for `P = ℝ²` the points on `H` are unconstrained;
  either way Lemma 3.10 and Theorem 3.9 fail. Sign-vector cells of `ℝ^d` close both holes and
  agree with the paper off `H` when `P` is convex.
* "Linear" is affine, as in the proof of Lemma 3.10 (`profit = a ⬝ᵥ p + b`).
* "A set of `t` hyperplanes" is `H.card ≤ t`: adding hyperplanes refines the cells.
* `σ` is a function on all pairs, but only its values on `H` matter, and an empty cell imposes
  nothing. -/
def IsDelineable {X : Type*} (d t : ℕ) (P : Set (Fin d → ℝ))
    (profit : (Fin d → ℝ) → X → ℝ) : Prop :=
  ∀ v : X, ∃ H : Finset ((Fin d → ℝ) × ℝ), H.card ≤ t ∧ (∀ h ∈ H, h.1 ≠ 0) ∧
    ∀ σ : (Fin d → ℝ) × ℝ → SignType, ∃ (a : Fin d → ℝ) (b : ℝ), ∀ p ∈ P,
      (∀ h ∈ H, SignType.sign (h.1 ⬝ᵥ p - h.2) = σ h) → profit p v = a ⬝ᵥ p + b

end SampleMechDesign


