-- Prove2me | Definitions.Def_LoadBalMatch_Main_FracMatching
-- name    : LoadBalMatch_Main_FracMatching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:32:28.687746+00:00
-- url     : https://prove2.me/theorems/46fd73f5-a0fa-46cc-9486-6a3e3b581c43
-- title:
--   The matching polytope $P(H)$, loads, levels, $\eta$ and balanced fractional matchings (§6.1, Definition 6.2)
-- statement:
--   Let $H$ be a graph on the finite set $V$ with edge set $E$. An edge vector $x\in\mathbb R^E$ has **load** $x_v=\sum_{e\ni v}x_e$ at the vertex $v$, **size** $|x|=\sum_e x_e$ and **support** $\operatorname{supp}(x)=\{e: x_e\neq 0\}$; for vertex sets $S,T$ write $x_S=\sum_{e\in E[S]}x_e$ (edges with both ends in $S$) and $x_{S,T}=\sum_{e\in E[S,T]}x_e$ (edges with one end in $S$ and one in $T$). The **matching polytope** of the (not necessarily bipartite) graph $H$ is
--   $$P(H)=\Big\{x\in[0,1]^E:\ \sum_{e\ni v}x_e\le 1\ \ \forall v\in V,\quad \sum_{e\in E[S]}x_e\le\frac{|S|-1}{2}\ \ \forall S\subseteq V,\ |S|\ge 3 \text{ odd}\Big\},$$
--   and $x$ is a **fractional matching** of $H$ if $x\in P(H)$. Each fractional matching has a **level vector**: $\ell_v=\min_{u\in N_H(v)}x_u$, the least load of a neighbour of $v$ in $H$, with $\ell_v=1$ when $v$ is isolated in $H$ (footnote 3). The objective of Definition 6.2 is
--   $$\eta(x)=\sum_{v\in V}(1-x_v)^2,\qquad \eta(H)=\min_{x\in P(H)}\eta(x),$$
--   and $x$ is a **balanced fractional matching** on $H$ if $x\in P(H)$ attains this minimum.
--
--   Balanced fractional matchings are the paper's central object: the algorithm stores one in each iteration, and the potential $\eta(x)-\eta(G)$ measures its distance from optimal.
--
--   **Formalization Note.** An edge vector is `x : Sym2 V → ℝ`; `IsFracMatching H x` requires `0 ≤ x ≤ 1`, `x e = 0` for every pair `e` that is not an edge of `H` (so $x\in[0,1]^E$), the degree constraints, and the odd-set constraints for every `S : Finset V` of odd cardinality at least 3. One vector space serves all graphs on $V$, so $P(H)\subseteq P(H')$ for $H\subseteq H'$. `load x v` sums `x` over the pairs `{v, w}`, `w ≠ v`. `etaOpt H` is the infimum of `eta` over $P(H)$, a nonempty (it contains $0$) set of values bounded below by $0$; $P(H)$ is compact, so this is the attained minimum $\eta(H)$. `IsBalanced H x` is stated as a minimiser directly. `level H x v` is the minimum of `load x` over the neighbours of `v` in `H`, and `1` if there are none. `supportGraph x` is the graph $(V,\operatorname{supp}(x))$ and `suppCard x` $=|\operatorname{supp}(x)|$.
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), pp. 26-27, §6.1 and Definition 6.2; p. 4, §2.1 (levels, footnote 3)

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching

/-!
# The matching polytope P(H), loads, levels, η and balanced fractional matchings

Assadi, Bernstein, Wrzos-Kaminska, STOC 2027 submission (sha256 7cd28a8b…), §6.1 pp. 26–27,
Definition 6.2; levels §2.1 p. 4 with footnote 3 ("We set ℓ_v = 1 for isolated vertices").

* `P(H) = { x ∈ [0,1]^E : Σ_{e∋v} x_e ≤ 1 ∀ v ∈ V, Σ_{e∈E[S]} x_e ≤ (|S| − 1)/2 ∀ S ⊆ V, |S| ≥ 3
  odd }` (the general matching polytope, with the odd-set constraints).
* load `x_v = Σ_{e∋v} x_e`; size `|x| = Σ_e x_e`; `x_S = Σ_{e∈E[S]} x_e`;
  `x_{S,T} = Σ_{e∈E[S,T]} x_e`; `supp(x) = {e : x_e ≠ 0}`.
* level `ℓ_v = min_{u∈N(v)} x_u`, neighbourhood in the graph `H` carrying `x`, and `ℓ_v = 1` when
  `v` is isolated in `H`.
* `η(x) = Σ_v (1 − x_v)²`, `η(H) = min_{x∈P(H)} η(x)`; `x` is balanced on `H` iff
  `x ∈ argmin_{x'∈P(H)} η(x')`.

Formalization Note. An edge vector is a function `x : Sym2 V → ℝ`; membership in `P(H)` forces it
to vanish off the edges of `H` (in particular on loops), so one vector space serves every graph on
`V` and `P(H) ⊆ P(H')` for `H ≤ H'`. `etaOpt H` is the infimum of `η` over `P(H)`; that set is
nonempty (`0 ∈ P(H)`) and bounded below by `0`, and `P(H)` is compact, so it is the attained
minimum `η(H)`. `IsBalanced` is stated as a minimiser directly and does not use `etaOpt`.
-/

namespace LoadBalMatch.Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The load `x_v = Σ_{e ∋ v} x_e` (the sum over the pairs `{v, w}`, `w ≠ v`). -/
noncomputable def load (x : Sym2 V → ℝ) (v : V) : ℝ :=
  ∑ w ∈ Finset.univ.erase v, x s(v, w)

/-- `x_S = Σ_{e ∈ E[S]} x_e`: the sum of `x` over the pairs with both ends in `S`. -/
noncomputable def inside (x : Sym2 V → ℝ) (S : Set V) : ℝ := by
  classical
  exact ∑ e ∈ (Finset.univ : Finset (Sym2 V)).filter (fun e => ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ S), x e

/-- `x_{S,T} = Σ_{e ∈ E[S,T]} x_e`: the sum of `x` over the pairs with one end in `S` and the
other in `T` (used for disjoint `S`, `T`). -/
noncomputable def cut (x : Sym2 V → ℝ) (S T : Set V) : ℝ := by
  classical
  exact ∑ e ∈ (Finset.univ : Finset (Sym2 V)).filter
    (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∈ T), x e

/-- The size `|x| = Σ_e x_e`. -/
noncomputable def size (x : Sym2 V → ℝ) : ℝ :=
  ∑ e, x e

/-- The graph `(V, supp(x))` with edge set `supp(x) = {e : x_e ≠ 0}`. -/
def supportGraph (x : Sym2 V → ℝ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | x e ≠ 0}

/-- `|supp(x)|`, the number of pairs `e` with `x_e ≠ 0`. -/
noncomputable def suppCard (x : Sym2 V → ℝ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Sym2 V)).filter (fun e => x e ≠ 0)).card

/-- `x ∈ P(H)`: `x` is a fractional matching of `H` (§6.1). -/
def IsFracMatching (H : SimpleGraph V) (x : Sym2 V → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ (∀ e, x e ≤ 1) ∧ (∀ e, e ∉ H.edgeSet → x e = 0) ∧
  (∀ v, load x v ≤ 1) ∧
  ∀ S : Finset V, 3 ≤ S.card → Odd S.card → inside x ↑S ≤ ((S.card : ℝ) - 1) / 2

/-- `η(x) = Σ_v (1 − x_v)²` (Definition 6.2). -/
noncomputable def eta (x : Sym2 V → ℝ) : ℝ :=
  ∑ v, (1 - load x v) ^ 2

/-- `η(H) = min_{x ∈ P(H)} η(x)` (Definition 6.2), as the infimum over `P(H)`. -/
noncomputable def etaOpt (H : SimpleGraph V) : ℝ :=
  sInf (eta '' {x | IsFracMatching H x})

/-- `x` is a balanced fractional matching on `H` (Definition 6.2): `x ∈ P(H)` minimises `η`
over `P(H)`. -/
def IsBalanced (H : SimpleGraph V) (x : Sym2 V → ℝ) : Prop :=
  IsFracMatching H x ∧ ∀ y, IsFracMatching H y → eta x ≤ eta y

/-- The level `ℓ_v = min_{u ∈ N_H(v)} x_u`, and `ℓ_v = 1` for a vertex isolated in `H`. -/
noncomputable def level (H : SimpleGraph V) (x : Sym2 V → ℝ) (v : V) : ℝ := by
  classical
  exact if h : (Finset.univ.filter (H.Adj v)).Nonempty then
    (Finset.univ.filter (H.Adj v)).inf' h (load x) else 1

end LoadBalMatch.Main


