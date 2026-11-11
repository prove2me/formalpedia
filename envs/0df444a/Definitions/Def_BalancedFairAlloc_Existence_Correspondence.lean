-- Prove2me | Definitions.Def_BalancedFairAlloc_Existence_Correspondence
-- name    : BalancedFairAlloc_Existence_Correspondence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:10.754854+00:00
-- url     : https://prove2.me/theorems/b21e1cef-5f54-4b10-a9d9-cf001099928c
-- title:
--   Closed graph and lower hemicontinuity of a correspondence, sequential form (Appendix C)
-- statement:
--   Let $P\subseteq\mathbb R^k$ be a parameter set and $K$ a correspondence assigning to each $w$ a set $K(w)\subseteq\mathbb R^d$ (in Lean, `K : (Fin k → ℝ) → Set (Fin d → ℝ)`). Following Appendix C:
--
--   - $K$ has a **closed graph on $P$** (`HasClosedGraphOn P K`) if whenever $w_t\to w$ with all $w_t,w\in P$, $z_t\in K(w_t)$ for every $t$, and $z_t\to z$, then $z\in K(w)$;
--   - $K$ is **lower hemicontinuous on $P$** (`IsLowerHemicontinuousOn P K`) if whenever $w_t\to w$ with all $w_t,w\in P$ and $z\in K(w)$, there are $z_t\in K(w_t)$ with $z_t\to z$.
--
--   $$w_t\to w,\ z_t\in K(w_t),\ z_t\to z\ \Longrightarrow\ z\in K(w).$$
--
--   A correspondence is **continuous** in the sense of Lemma 3 when both hold.
--
--   **Formalization Note.** Both properties are stated with sequences, exactly as in Appendix C; $\mathbb R^k$ and $\mathbb R^d$ are `Fin k → ℝ` and `Fin d → ℝ` with the product topology.
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 56 (PDF 58), Appendix C, properties (i) and (ii)

import Mathlib

namespace BalancedFairAlloc.Existence

open Filter Topology

/-! ### Sequential continuity notions for correspondences

Cookson, Shah, Verma, *Fair and Efficient Balanced Allocations for Additive Valuations*,
arXiv:2608.06325, Appendix C (p. 56): the parameter `w` ranges over a set `P ⊆ ℝᵏ` and the
values `K(w)` are subsets of `ℝᵈ`; both spaces are `Fin _ → ℝ`. -/

/-- (i) Closed graph (Appendix C): if `w_t → w` in `P`, `z_t ∈ K(w_t)` for every `t` and
`z_t → z`, then `z ∈ K(w)`. -/
def HasClosedGraphOn {k d : ℕ} (P : Set (Fin k → ℝ)) (K : (Fin k → ℝ) → Set (Fin d → ℝ)) :
    Prop :=
  ∀ (wt : ℕ → Fin k → ℝ) (w : Fin k → ℝ) (zt : ℕ → Fin d → ℝ) (z : Fin d → ℝ),
    (∀ t, wt t ∈ P) → w ∈ P → Tendsto wt atTop (𝓝 w) →
    (∀ t, zt t ∈ K (wt t)) → Tendsto zt atTop (𝓝 z) → z ∈ K w

/-- (ii) Lower hemicontinuity (Appendix C): if `w_t → w` in `P` and `z ∈ K(w)`, then there are
`z_t ∈ K(w_t)` with `z_t → z`. -/
def IsLowerHemicontinuousOn {k d : ℕ} (P : Set (Fin k → ℝ))
    (K : (Fin k → ℝ) → Set (Fin d → ℝ)) : Prop :=
  ∀ (wt : ℕ → Fin k → ℝ) (w : Fin k → ℝ),
    (∀ t, wt t ∈ P) → w ∈ P → Tendsto wt atTop (𝓝 w) →
    ∀ z ∈ K w, ∃ zt : ℕ → Fin d → ℝ, (∀ t, zt t ∈ K (wt t)) ∧ Tendsto zt atTop (𝓝 z)

end BalancedFairAlloc.Existence


