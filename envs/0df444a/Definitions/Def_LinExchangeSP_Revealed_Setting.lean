-- Prove2me | Definitions.Def_LinExchangeSP_Revealed_Setting
-- name    : LinExchangeSP_Revealed_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:29.21559+00:00
-- url     : https://prove2.me/theorems/143a1a9d-9900-46be-8841-b9cdf364a203
-- title:
--   §3.1, §3.3, Definition 3.2, display (1), pp. 5–6, 9 — revealed edges F*, F-allocations, F-equilibria, components of F, φ, Ψ(F)
-- statement:
--   This file builds the objects of §3 of Garg and Végh on top of the linear exchange market (agents $A$, goods $G$, edge set $E$, MBB edges $\mathrm{MBB}(p)$, money allocations and market equilibria).
--
--   1. **Revealed edges** (§3.1, p. 5). $F^*\subseteq E$ is the set of edges $(i,g_j)\in E$ that are MBB edges for *every* market equilibrium $(p,f)$.
--   2. **$F$-allocation** (Definition 3.2). For an edge set $F$, the pair $(p,f)$ is an $F$-allocation if (i) $p>0$ and $f_{ij}\ge0$ for $(i,g_j)\in E\setminus F$; (ii) $\operatorname{supp}(f)\cup F\subseteq\mathrm{MBB}(p)$; (iii) $\sum_{g_j}f_{ij}\le p_i$ for every agent $i$; (iv) $\sum_i f_{ij}\le p_j$ for every good $g_j$. Money on the edges of $F$ may be negative. An $F$-allocation is an **$F$-equilibrium** if $\lVert s(p,f)\rVert_1=0$.
--   3. **Components of $F$** (pp. 7, 9). The undirected bipartite graph $(A\cup G,F)$ has the agents and the goods as vertices (an agent and the good it owns are different vertices) and an edge between $i$ and $g_j$ whenever $(i,g_j)\in F$.
--   4. **Potential** (§3.3, p. 6).
--   $$\varphi(p,f)=\frac{\lVert s(p,f)\rVert_\infty}{\left(\prod_{j=1}^n p_j\right)^{1/n}},\qquad \Psi(F)=\min\{\varphi(p,f): (p,f)\text{ is an }F\text{-allocation},\ \operatorname{supp}(f)\subseteq F\}.$$
--   5. **The block of maximal price ratio** (proof of Lemma 3.4, p. 9). For two price vectors $p,p'$, let $\alpha=\max_{g_j\in G}p'_j/p_j$, $T=\{g_j: p'_j/p_j=\alpha\}$, and $S=\{i\in A:\exists g_j\in T,\ (i,g_j)\in\mathrm{MBB}(p')\}$. A vertex of $(A\cup G,\cdot)$ is in the block $S\cup T$ if it is an agent of $S$ or a good of $T$.
--
--   $F^*$ is the set the algorithm of the paper grows edge by edge; $F$-equilibria are what it computes; $\varphi$ and $\Psi$ measure its progress.
--
--   **Formalization Note** If the market has no equilibrium, $F^*=E$. The graph lives on `Fin n ⊕ Fin n` (agents on the left, goods on the right). $\Psi(F)$ is taken as an infimum (`sInf`): it is the paper's minimum whenever the minimum exists, and $0$ when there is no $F$-allocation with $\operatorname{supp}(f)\subseteq F$. The paper defines $\Psi(F)$ for $F\subseteq F^*$; here it is defined for every $F$. $\alpha$ is a supremum over `Fin n` (equal to $0$ when $n=0$); $S$ and $T$ are finite sets of indices in `Fin n`.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 5 (§3.1, F*; Definition 3.2), p. 6 (φ and display (1)), p. 7 (Lemma 3.9, components of F), p. 9 (proof of Lemma 3.4: α, T, S, the graph (A ∪ G, Ē))

import Mathlib
import Definitions.Def_LinExchangeSP_Revealed_Market

namespace LinExchangeSP.Revealed

variable {n : ℕ}

/-- `F*` (§3.1, p. 5): the edges of `E` that are MBB edges for every market equilibrium `(p, f)`.
If the market has no equilibrium, `F* = E`. -/
def Market.Fstar (M : Market n) : Set (Fin n × Fin n) :=
  {e | e ∈ M.E ∧ ∀ p f, M.IsMarketEquilibrium p f → e ∈ M.MBB p}

/-- Definition 3.2 (p. 5): `(p, f)` is an `F`-allocation if (i) `p > 0` and `f_ij ≥ 0` on `E \ F`;
(ii) `supp(f) ∪ F ⊆ MBB(p)`; (iii) every agent spends at most `p_i`; (iv) every good is sold for at
most `p_j`. Money on edges of `F` may be negative. -/
def Market.IsFAllocation (M : Market n) (F : Set (Fin n × Fin n)) (p : Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) : Prop :=
  (∀ j, 0 < p j) ∧ (∀ e ∈ M.E \ F, 0 ≤ f e.1 e.2) ∧ supp f ∪ F ⊆ M.MBB p ∧
    (∀ i, ∑ j, f i j ≤ p i) ∧ (∀ j, ∑ i, f i j ≤ p j)

/-- Definition 3.2 (p. 5): an `F`-allocation with `‖s(p, f)‖₁ = 0` is an `F`-equilibrium. -/
def Market.IsFEquilibrium (M : Market n) (F : Set (Fin n × Fin n)) (p : Fin n → ℝ)
    (f : Fin n → Fin n → ℝ) : Prop :=
  M.IsFAllocation F p f ∧ surplusL1 p f = 0

/-- The undirected bipartite graph `(A ∪ G, F)` on `Fin n ⊕ Fin n`: agent `i` is `Sum.inl i`, good
`g_j` is `Sum.inr j`, and `{inl i, inr j}` is an edge iff `(i, j) ∈ F`. Its connected components are
the "undirected connected components of `F`" (pp. 7, 9). -/
def bipGraph (F : Set (Fin n × Fin n)) : SimpleGraph (Fin n ⊕ Fin n) :=
  SimpleGraph.fromRel (fun a b => ∃ i j, a = Sum.inl i ∧ b = Sum.inr j ∧ (i, j) ∈ F)

/-- The potential `φ(p, f) = ‖s(p, f)‖∞ / (Π_j p_j)^{1/n}` (§3.3, p. 6). -/
noncomputable def phi (p : Fin n → ℝ) (f : Fin n → Fin n → ℝ) : ℝ :=
  surplusLinf p f / (∏ j, p j) ^ ((1 : ℝ) / n)

/-- `Ψ(F)`, display (1) (p. 6): the minimum of `φ(p, f)` over the `F`-allocations `(p, f)` with
`supp(f) ⊆ F`, taken as `sInf` (which is the minimum when it is attained, and `0` if there is no
such `F`-allocation). -/
noncomputable def Market.Psi (M : Market n) (F : Set (Fin n × Fin n)) : ℝ :=
  sInf {x | ∃ p f, M.IsFAllocation F p f ∧ supp f ⊆ F ∧ x = phi p f}

/-- `α := max_j p'_j / p_j` (proof of Lemma 3.4, p. 9); `0` when `n = 0`. -/
noncomputable def maxRatio (p p' : Fin n → ℝ) : ℝ := ⨆ j, p' j / p j

/-- `T := {g_j ∈ G | p'_j / p_j = α}` (proof of Lemma 3.4, p. 9). -/
noncomputable def topGoods (p p' : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => p' j / p j = maxRatio p p')

/-- `S := {i ∈ A | ∃ g_j ∈ T, (i, g_j) ∈ MBB(p')}` (proof of Lemma 3.4, p. 9). -/
noncomputable def Market.topAgents (M : Market n) (p p' : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ j ∈ topGoods p p', (i, j) ∈ M.MBB p')

/-- Membership in `S ∪ T` as a vertex set of `(A ∪ G, ·)`: agent `inl i` is in it iff `i ∈ S`,
good `inr j` iff `j ∈ T`. -/
def Market.inBlock (M : Market n) (p p' : Fin n → ℝ) : Fin n ⊕ Fin n → Prop :=
  Sum.elim (fun i => i ∈ M.topAgents p p') (fun j => j ∈ topGoods p p')

end LinExchangeSP.Revealed


