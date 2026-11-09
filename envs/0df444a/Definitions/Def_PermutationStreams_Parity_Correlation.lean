-- Prove2me | Definitions.Def_PermutationStreams_Parity_Correlation
-- name    : PermutationStreams_Parity_Correlation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:30.124453+00:00
-- url     : https://prove2.me/theorems/5c9ac4c2-b162-486d-8396-27890d0cb12a
-- title:
--   Pairwise connected laws, nonembeddable targets and product expectations
-- statement:
--   Let $\Sigma,\Gamma,\Phi$ be finite sets and $\mu$ a probability distribution on $\Sigma\times\Gamma\times\Phi$, with support $\operatorname{supp}(\mu)=\{t:\mu(t)>0\}$. Let $D=\{z\in\mathbb C:|z|\le1\}$ be the closed unit disk.
--
--   1. **Product expectation.** For $m\ge1$ the law $\mu^{\otimes m}$ on $(\Sigma\times\Gamma\times\Phi)^m$ makes the $m$ coordinate triples independent with law $\mu$, and $\mathbb E_{\mu^{\otimes m}}[g]=\sum_{w}\prod_{i=1}^m\mu(w_i)\,g(w)$. A vector $w=((x_i,y_i,z_i))_{i}$ is identified with the triple $(x,y,z)\in\Sigma^m\times\Gamma^m\times\Phi^m$.
--   2. **Support graphs.** The support graph on $\Sigma$ and $\Gamma$ is the bipartite graph with an edge $\{x,y\}$ whenever $\mu(x,y,z)>0$ for some $z$; the graphs on $\Sigma,\Phi$ and on $\Gamma,\Phi$ are defined in the same way. The law $\mu$ is **pairwise connected** when all three graphs are connected after removing the symbols of zero marginal probability.
--   3. **Nonembeddability.** A function $T:\operatorname{supp}(\mu)\to D$ is **nonembeddable over $D$** when there are no functions $a:\Sigma\to D$, $b:\Gamma\to D$, $c:\Phi\to D$ with
--
--   $$
--   a(x)\,b(y)\,c(z)\,T(x,y,z)=1\qquad\text{for every }(x,y,z)\in\operatorname{supp}(\mu).
--   $$
--
--   These are the hypotheses of the correlation bound of Bhangale, Braverman, Khot, Liu and Minzer quoted as Theorem 4.2.
--
--   **Formalization Note** The law is a function of point masses with the predicate "nonnegative and summing to one". A symbol has positive marginal probability exactly when it occurs in a positive-probability triple, which is how the vertex set is described. $T$ is a total function on $\Sigma\times\Gamma\times\Phi$ whose values off the support are never used: the nonembeddability condition and the disk condition only concern support points, and in an expectation off-support points have weight zero.
--
--   Differences from the source:
--   - encoding: T : supp(µ) → D → T : Σ × Γ × Φ → ℂ whose disk bound and embedding condition are required on supp(µ) only; reason: values off the support never enter any statement
--   - encoding: remove symbols of zero marginal probability → keep the symbols occurring in a positive-probability triple; reason: for a nonnegative law these are the same symbols
--   - encoding: Σ^m, coordinates i = 1,…,m → Fin m → Σ; reason: 0-based coordinates
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §4.2, pp. 5–6 (D, support graphs, pairwise connected, nonembeddable, µ^⊗m)

import Mathlib

namespace PermutationStreams.Parity

/-- A probability law on a finite set, given by its point masses. -/
def IsProbLaw {α : Type} [Fintype α] (μ : α → ℝ) : Prop :=
  (∀ a, 0 ≤ μ a) ∧ ∑ a, μ a = 1

/-- Expectation of `g` under the `m`-fold product law `μ^{⊗m}` on `α^m`, coordinates
independent with law `μ` each. -/
noncomputable def prodExpect {α : Type} [Fintype α] (μ : α → ℝ) (m : ℕ)
    (g : (Fin m → α) → ℂ) : ℂ :=
  ∑ w : Fin m → α, ((∏ i, μ (w i) : ℝ) : ℂ) * g w

/-- The bipartite support graph on `α ⊕ β` of a law `μ` on `Ω` read through the two coordinate
maps `f : Ω → α`, `g : Ω → β` (§4.2 p.5): `a` and `b` are adjacent when some `t` with
`μ t > 0` has `f t = a` and `g t = b`. -/
def supportGraph {Ω α β : Type} (μ : Ω → ℝ) (f : Ω → α) (g : Ω → β) : SimpleGraph (α ⊕ β) :=
  SimpleGraph.fromRel fun u v => ∃ t, 0 < μ t ∧ u = Sum.inl (f t) ∧ v = Sum.inr (g t)

/-- The symbols of positive marginal probability (equivalently, for a nonnegative `μ`, the
symbols occurring in some positive-probability point). -/
def supportVertices {Ω α β : Type} (μ : Ω → ℝ) (f : Ω → α) (g : Ω → β) : Set (α ⊕ β) :=
  {u | ∃ t, 0 < μ t ∧ (u = Sum.inl (f t) ∨ u = Sum.inr (g t))}

/-- The support graph after removing symbols of zero marginal probability is connected. -/
def SupportGraphConnected {Ω α β : Type} (μ : Ω → ℝ) (f : Ω → α) (g : Ω → β) : Prop :=
  ((supportGraph μ f g).induce (supportVertices μ f g)).Connected

/-- §4.2 p.5: a law `μ` on `Σ × Γ × Φ` is pairwise connected when its three support graphs
(on `Σ, Γ`, on `Σ, Φ`, on `Γ, Φ`) are connected after removing zero-marginal symbols. -/
def PairwiseConnected {Sig Gam Phi : Type} (μ : Sig × Gam × Phi → ℝ) : Prop :=
  SupportGraphConnected μ (fun t => t.1) (fun t => t.2.1) ∧
  SupportGraphConnected μ (fun t => t.1) (fun t => t.2.2) ∧
  SupportGraphConnected μ (fun t => t.2.1) (fun t => t.2.2)

/-- §4.2 p.6: `T : supp(μ) → D` is nonembeddable over the closed unit disk `D ⊆ ℂ` when no
`a : Σ → D`, `b : Γ → D`, `c : Φ → D` satisfy `a(x) b(y) c(z) T(x,y,z) = 1` at every
`(x,y,z) ∈ supp(μ)`. `T` is given as a total function; its values off the support are never
used. -/
def Nonembeddable {Sig Gam Phi : Type} (μ : Sig × Gam × Phi → ℝ)
    (T : Sig × Gam × Phi → ℂ) : Prop :=
  ¬ ∃ (a : Sig → ℂ) (b : Gam → ℂ) (c : Phi → ℂ),
    (∀ x, ‖a x‖ ≤ 1) ∧ (∀ y, ‖b y‖ ≤ 1) ∧ (∀ z, ‖c z‖ ≤ 1) ∧
    ∀ t, 0 < μ t → a t.1 * b t.2.1 * c t.2.2 * T t = 1

end PermutationStreams.Parity


