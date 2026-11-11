-- Prove2me | Definitions.Def_MinKCutII_Main_KCut
-- name    : MinKCutII_Main_KCut
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:37:52.094571+00:00
-- url     : https://prove2.me/theorems/1e14c76f-31eb-4fd3-9b34-e58a7c6090b6
-- title:
--   k-cuts of a capacitated multigraph, their value c_G(P), and λ_k(G) (with λ_j = +∞ for |V| < j)
-- statement:
--   Let $G=(V,E,c)$ be a finite capacitated multigraph: a finite vertex set $V$, a finite set $E$ of edge records, each with an unordered pair of ends and a capacity $c(e)\in\mathbb R$ (parallel records and loops allowed; a loop crosses no cut). For $S\subseteq V$ the **boundary** is $\delta_G(S)$, the records with exactly one end in $S$, and $c_G(S)=c(\delta_G(S))=\sum_{e\in\delta_G(S)}c(e)$.
--
--   A partition of $V$ into labelled parts is a labelling $f:V\to\{0,\dots,k-1\}$; its cut set $\delta_G(P)$ consists of the records whose ends get different labels, and its value is $c_G(P)=c(\delta_G(P))$. A **$k$-cut** is a partition into exactly $k$ nonempty parts, i.e. a surjective labelling. The minimum $k$-cut value is
--   $$\lambda_k(G)=\min\{c_G(P) : P \text{ a } k\text{-cut of } G\}\in\mathbb R\cup\{+\infty\},$$
--   with $\lambda_k(G)=+\infty$ when $|V|<k$ (no $k$-cut exists) and $\lambda_1(G)=0$ for nonempty $V$. A **minimum $k$-cut** is a $k$-cut of value $\lambda_k(G)$. The module also names positivity and integrality of capacities and connectivity (the simple graph with an edge $ab$, $a\ne b$, whenever some record has ends $\{a,b\}$ is connected; this includes $V\ne\emptyset$).
--
--   **Formalization Note.** The graph is the published `CombOpt.MinCut.CapGraph V E` with `delta` and `uSum`, which bundle no condition; positivity (`PosCap`) and integrality (`IntCap`) are hypotheses of the statements. `lam G k : WithTop ℝ` is a `Finset.inf` over the finitely many surjective labellings, so it is `⊤` exactly when $|V|<k$ and never a junk value. Labels are `Fin k` (0-based).
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), pp. 5–6, §2 (Conventions; Graph and cut notation; Minimum k-cut)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_delta
import Definitions.Def_CombOpt_MinCut_CapGraph_uSum

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-!
# k-cuts of a capacitated multigraph, their value, and `λ_k`

Vaughn, *Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted
Graphs*, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), §2, pp. 5–6.

The graph is the published `CombOpt.MinCut.CapGraph V E`: vertex type `V`, edge-record type `E`,
`ends e : Sym2 V`, capacity `u e : ℝ`. Parallel edges are distinct records with the same ends; a
loop has diagonal ends and lies in no cut set (the paper discards loops: "they cross no cut").

* `cutVal G S = c_G(S) = c(δ_G(S))` (p. 6).
* A partition of `V` into `k` labelled parts is a labelling `f : V → Fin k`; it is a **k-cut**
  ("a partition of V into exactly k nonempty parts", p. 6) when `f` is surjective. The parts are
  the fibres of `f`; a k-cut and its relabellings are the same partition and have the same value.
* `partDelta G f = δ_G(P)`: the edges whose two ends get different labels; `partVal G f = c_G(P)`.
* `lam G k = λ_k(G)`: the minimum of `partVal G f` over surjective `f : V → Fin k`, in
  `WithTop ℝ`. It is `⊤` exactly when `|V| < k` (no surjection exists), the paper's convention
  `λ_j(G) := +∞` for `|V(G)| < j`; for `k = 1` and `V` nonempty it is `0`, the paper's `λ_1 := 0`.
  It is a `Finset.inf` over a finite set, so no junk value arises.
* Positivity and integrality of capacities are separate predicates (`PosCap`, `IntCap`), used as
  hypotheses: the published `CapGraph` bundles no condition.
* `IsConnected G`: the underlying simple graph (an edge between `a ≠ b` when some record has ends
  `{a, b}`) is connected; Mathlib's `Connected` includes nonemptiness of `V`.
-/

/-- The boundary value `c_G(S) = c(δ_G(S))` of a vertex set `S` (p. 6). -/
noncomputable def cutVal {V E : Type*} [Fintype E] (G : CapGraph V E) (S : Finset V) : ℝ :=
  G.uSum (G.delta S)

open Classical in
/-- The cut set `δ_G(P)` of the partition given by the labelling `f`: the edge records whose
ends receive different labels (a loop never does). -/
noncomputable def partDelta {V E : Type*} [Fintype E] {k : ℕ} (G : CapGraph V E)
    (f : V → Fin k) : Finset E :=
  Finset.univ.filter (fun e => ∃ a ∈ G.ends e, ∃ b ∈ G.ends e, f a ≠ f b)

/-- The value `c_G(P) = c(δ_G(P))` of the partition given by `f`. -/
noncomputable def partVal {V E : Type*} [Fintype E] {k : ℕ} (G : CapGraph V E)
    (f : V → Fin k) : ℝ :=
  G.uSum (partDelta G f)

/-- `f` is a k-cut: a partition of `V` into exactly `k` nonempty parts (the fibres of `f`). -/
def IsKCut {V : Type*} {k : ℕ} (f : V → Fin k) : Prop :=
  Function.Surjective f

open Classical in
/-- `λ_k(G)`: the minimum value of a k-cut, `⊤` (`+∞`) when `|V| < k`. -/
noncomputable def lam {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : CapGraph V E)
    (k : ℕ) : WithTop ℝ :=
  (Finset.univ.filter (fun f : V → Fin k => Function.Surjective f)).inf
    (fun f => ((partVal G f : ℝ) : WithTop ℝ))

/-- `f` is a minimum k-cut: a k-cut of value `λ_k(G)`. -/
def IsMinKCut {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : CapGraph V E) (k : ℕ)
    (f : V → Fin k) : Prop :=
  Function.Surjective f ∧ ((partVal G f : ℝ) : WithTop ℝ) = lam G k

/-- All capacities are positive. -/
def PosCap {V E : Type*} (G : CapGraph V E) : Prop :=
  ∀ e, 0 < G.u e

/-- All capacities are (nonnegative) integers. -/
def IntCap {V E : Type*} (G : CapGraph V E) : Prop :=
  ∀ e, ∃ z : ℕ, G.u e = z

/-- `G` is connected: its underlying simple graph is connected (in particular `V` is nonempty). -/
def IsConnected {V E : Type*} (G : CapGraph V E) : Prop :=
  (SimpleGraph.fromRel (fun a b : V => ∃ e, G.ends e = s(a, b))).Connected

end MinKCutII.Main


