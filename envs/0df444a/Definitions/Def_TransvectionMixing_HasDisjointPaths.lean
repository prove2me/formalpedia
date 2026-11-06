-- Prove2me | Definitions.Def_TransvectionMixing_HasDisjointPaths
-- name    : TransvectionMixing_HasDisjointPaths
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:07.9291+00:00
-- url     : https://prove2.me/theorems/2ee1a707-1eaa-4b7e-96b8-bb18662998c5
-- title:
--   Time-expanded graph: routed paths, vertex-disjoint path families, and source collection
-- statement:
--   The **time-expanded graph** of a skeleton $\sigma=((I_1\mapsto J_1),\dots,(I_T\mapsto J_T))$ has vertices $[n]\times\{0,\dots,T\}$, persistence edges $(r,t-1)\to(r,t)$ for every row $r$, and transmission edges $(I_t,t-1)\to(J_t,t)$. Every edge advances one layer, so a directed path from layer $0$ to layer $T$ is a sequence of rows $p(0),\dots,p(T)$ with $p(t)=p(t-1)$ or $(p(t-1),p(t))=(I_t,J_t)$ at every step.
--
--   For $\mathcal B,\mathcal T\subseteq[n]$, the graph **contains $|\mathcal B|$ vertex-disjoint directed paths from $\{(b,0):b\in\mathcal B\}$ to $\mathcal T\times\{T\}$** if there is such a path for each $b\in\mathcal B$, starting at row $b$ and ending in $\mathcal T$, with no two paths at the same row in any layer.
--
--   A skeleton **contains updates from at least $s$ distinct rows of $S$ into $R$** if at least $s$ distinct rows of $S$ occur as the source of some update whose target lies in $R$ (the receiving rows need not be distinct). The module also defines the constants of Corollary 5.2:
--   $$
--   \mu=\frac{n(n-1)}{|R|}\log\frac{|S|+1/2}{|S|-s+1/2},\qquad v=\frac{n(n-1)}{|R|(|S|-s+1)}.
--   $$
--
--   **Formalization Note** Layers are `Fin (T + 1)`; step $s$ of `Fin T` is the paper's step $s+1$.
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), §4, p.13 (time-expanded graph, Lemma 4.1); Corollary 5.2, pp.17–18 (collection, μ, v)

import Mathlib
import Definitions.Def_TransvectionMixing_walkMat

namespace TransvectionMixing

/-- A directed path from layer `0` to layer `T` of the time-expanded graph of a skeleton `σ`
(Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §4, p.13). The graph has vertices
`[n] × {0, …, T}`, persistence edges `(r, t−1) → (r, t)` and transmission edges
`(I_t, t−1) → (J_t, t)`. Every edge advances one layer, so such a path is a row
`p(0), …, p(T)` with, at each step `t`, either `p(t) = p(t−1)` or
`(p(t−1), p(t)) = (I_t, J_t)`.

**Formalization Note** Layers are `Fin (T + 1)`; step `s : Fin T` (the paper's `t = s + 1`)
goes from layer `s` to layer `s + 1` and uses the pair `σ s`. -/
def IsRoutedPath {n T : ℕ} (σ : Skel n T) (p : Fin (T + 1) → Fin n) : Prop :=
  ∀ s : Fin T, p s.succ = p s.castSucc ∨ (p s.castSucc = (σ s).1.1 ∧ p s.succ = (σ s).1.2)

/-- The time-expanded graph of `σ` contains `|ℬ|` vertex-disjoint directed paths from
`{(b, 0) : b ∈ ℬ}` to `𝒯 × {T}` (manuscript sha256 217f833f…, Lemma 4.1, p.13). Paths through
the layered graph meet a layer exactly once, so vertex-disjointness is injectivity in every
layer. -/
def HasDisjointPaths {n T : ℕ} (σ : Skel n T) (B Tg : Finset (Fin n)) : Prop :=
  ∃ P : ↥B → Fin (T + 1) → Fin n,
    (∀ b, IsRoutedPath σ (P b)) ∧ (∀ b, P b 0 = b.1) ∧ (∀ b, P b (Fin.last T) ∈ Tg) ∧
      ∀ s : Fin (T + 1), Function.Injective (fun b => P b s)

/-- The skeleton contains updates from at least `s` distinct rows of `S` into `R` (the receiving
rows need not be distinct) (manuscript sha256 217f833f…, Corollary 5.2, pp.17–18). -/
def Collects {n T : ℕ} (σ : Skel n T) (S R : Finset (Fin n)) (s : ℕ) : Prop :=
  s ≤ ((Finset.univ.filter (fun u => (σ u).1.1 ∈ S ∧ (σ u).1.2 ∈ R)).image
    (fun u => (σ u).1.1)).card

/-- `µ = (n(n−1)/|R|) log((|S| + 1/2)/(|S| − s + 1/2))` of Corollary 5.2 (manuscript sha256
217f833f…, p.18). -/
noncomputable def collectMu (n : ℕ) (S R : Finset (Fin n)) (s : ℕ) : ℝ :=
  (n : ℝ) * (n - 1) / R.card * Real.log ((S.card + 1 / 2) / ((S.card : ℝ) - s + 1 / 2))

/-- `v = n(n−1)/(|R|(|S| − s + 1))` of Corollary 5.2 (manuscript sha256 217f833f…, p.18). -/
noncomputable def collectV (n : ℕ) (S R : Finset (Fin n)) (s : ℕ) : ℝ :=
  (n : ℝ) * (n - 1) / (R.card * ((S.card : ℝ) - s + 1))

end TransvectionMixing


