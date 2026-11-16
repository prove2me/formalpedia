-- Prove2me | Definitions.Def_HarmonicRanking_Main_Supplement_Proposals
-- name    : HarmonicRanking_Main_Supplement_Proposals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:44:52.069757+00:00
-- url     : https://prove2.me/theorems/4ea01560-4676-491c-a2ca-cadf0c083baa
-- title:
--   Mutual proposals, long proposal cycles and long-cycle-freeness
-- statement:
--   This file sets up the objects of Section 2.3 needed for Theorem 2.1.
--
--   A **gain-sharing rule** is a function $g$ of two ranks in $[0,1)$. A **finite weighted bipartite residual instance** consists of finite vertex sets $L$ and $R$ (either may be empty), a set $A\subseteq L\times R$ of available pairs, and nonnegative weights $w_{uv}\ge 0$ on the potential pairs. Every vertex $z\in L\sqcup R$ carries a rank $x_z\in[0,1)$; distinct vertices may share a rank. On a pair $uv$ with $u\in L$, $v\in R$, the two **prospective gains** of equation (3) are
--
--   $$G_u(uv)=g(x_u,x_v)\,w_{uv},\qquad G_v(uv)=g(x_v,x_u)\,w_{uv}.$$
--
--   A **common total tie order** on $L\times R$ is given by an injective key $\mathrm{ord}:L\times R\to\mathbb N$ (a smaller key is earlier). A vertex $z$ **proposes along** an available pair $e\ni z$ when $e$ maximizes $z$'s own prospective gain among the available pairs at $z$, ties being resolved in favour of the earliest pair in the common order.
--
--   A **long proposal cycle** is a cyclic sequence of $n\ge 3$ pairwise distinct vertices $z_0,\dots,z_{n-1}$ such that each $z_i$ proposes along the pair joining $z_i$ and $z_{i+1 \bmod n}$ (by bipartiteness such a cycle has length at least four; mutual two-cycles are excluded). The rule $g$ is **long-cycle-free on the sampled domain** if no finite weighted bipartite residual instance, no rank assignment in $[0,1)$ and no common total tie order produce a long proposal cycle.
--
--   These notions are the hypotheses of the characterization of score-balanced gain sharing (Theorem 2.1).
--
--   **Formalization Note** The two sides are arbitrary finite types `L`, `R : Type` and ranks use the published `Ranks L R` (maps from `L ⊕ R` into `[0,1)`). A gain-sharing rule is a total function `ℝ → ℝ → ℝ`; only its values on `[0,1)²` are ever evaluated. Every total order on a finite set is induced by an injective key into `ℕ`, and conversely.
-- source:
--   Bo Peng, Zhihao Gavin Tang, Harmonic Ranking for Edge-Weighted Oblivious Matching, STOC 2027 submission #176 (October 2026), printed/PDF p. 6, Section 2.3 (Mutual Proposals, equation (3), long proposal cycle, long-cycle-free on the sampled domain)

import Definitions.Def_HarmonicRanking_Main_Instance

set_option autoImplicit false
noncomputable section

namespace HarmonicRanking.Main.Supplement

/-- Vertex `z` of `L ⊕ R` is an endpoint of the potential pair `e`. -/
def IsEndpoint {L R : Type*} (z : L ⊕ R) (e : L × R) : Prop :=
  z = Sum.inl e.1 ∨ z = Sum.inr e.2

/-- The pair `e` joins the two vertices `z` and `z'` (in either orientation). -/
def Joins {L R : Type*} (z z' : L ⊕ R) (e : L × R) : Prop :=
  (z = Sum.inl e.1 ∧ z' = Sum.inr e.2) ∨ (z = Sum.inr e.2 ∧ z' = Sum.inl e.1)

/-- Prospective gain (3) of an endpoint `z` on the pair `e = uv`:
`G_u(uv) = g(x_u, x_v) w_uv` for the left endpoint, `G_v(uv) = g(x_v, x_u) w_uv` for the
right endpoint. Only used when `z` is an endpoint of `e`. -/
def prospectiveGain {L R : Type*} (g : ℝ → ℝ → ℝ) (w : L × R → ℝ) (x : Ranks L R)
    (z : L ⊕ R) (e : L × R) : ℝ :=
  match z with
  | Sum.inl _ => g (x (Sum.inl e.1)) (x (Sum.inr e.2)) * w e
  | Sum.inr _ => g (x (Sum.inr e.2)) (x (Sum.inl e.1)) * w e

/-- In the residual instance with available pairs `A`, vertex `z` proposes along `e`:
`e` is an available pair at `z` maximizing `z`'s own prospective gain, ties resolved in favour
of the earliest pair of the common total order given by the injective key `ord`
(smaller key = earlier). -/
def Proposes {L R : Type*} (g : ℝ → ℝ → ℝ) (A : Finset (L × R)) (w : L × R → ℝ)
    (x : Ranks L R) (ord : L × R → ℕ) (z : L ⊕ R) (e : L × R) : Prop :=
  e ∈ A ∧ IsEndpoint z e ∧
    ∀ e' ∈ A, IsEndpoint z e' →
      prospectiveGain g w x z e' < prospectiveGain g w x z e ∨
        (prospectiveGain g w x z e' = prospectiveGain g w x z e ∧ ord e ≤ ord e')

/-- A long proposal cycle: `n ≥ 3` pairwise distinct vertices `z₀, …, z_{n-1}` such that each
`z_i` proposes along the pair joining `z_i` and `z_{i+1 mod n}`. -/
def HasLongProposalCycle {L R : Type*} (g : ℝ → ℝ → ℝ) (A : Finset (L × R))
    (w : L × R → ℝ) (x : Ranks L R) (ord : L × R → ℕ) : Prop :=
  ∃ (n : ℕ) (z : Fin n → L ⊕ R), 3 ≤ n ∧ Function.Injective z ∧
    ∀ i : Fin n, ∃ e : L × R, Joins (z i) (z (finRotate n i)) e ∧ Proposes g A w x ord (z i) e

/-- `g` is long-cycle-free on the sampled domain: no finite weighted bipartite residual
instance (finite sides, any set `A` of available pairs, nonnegative weights), no assignment of
ranks in `[0,1)` and no common total tie order produce a long proposal cycle. -/
def LongCycleFree (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ (L R : Type) [Fintype L] [Fintype R] (A : Finset (L × R)) (w : L × R → ℝ),
    (∀ e, 0 ≤ w e) → ∀ (x : Ranks L R) (ord : L × R → ℕ), Function.Injective ord →
      ¬ HasLongProposalCycle g A w x ord

end HarmonicRanking.Main.Supplement


