-- Prove2me | Definitions.Def_DecrNbhdCover_ShelledCover
-- name    : DecrNbhdCover_ShelledCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:59.097693+00:00
-- url     : https://prove2.me/theorems/523bec91-01f5-4113-a0e1-3eb3aa08ad24
-- title:
--   Shelled neighborhood covers (Definition 3.3) and the derived graph $H_{G,\mathcal N}$
-- statement:
--   Let $G$ be a graph, $0<\epsilon<1/2$, $0<d<D$ integers with $D\ge d\cdot2^{32/\epsilon^c}$. An **$(\epsilon,d,D)$-shelled neighborhood cover** $\mathcal N=(\mathcal S,\{D_S,T(S),\mathrm{Shell}(S)\}_{S\in\mathcal S})$ consists of clusters $S\subseteq V(G)$ with values $d\cdot2^{16/\epsilon^c}\le D_S\le D/2^{16/\epsilon^c}$ and subsets $T(S)\subseteq S$, such that $B_G(v,D_S)\subseteq S$ for $v\in T(S)$, $\mathrm{dist}_G(v,v')\le D_S2^{1/\epsilon^c}$ for $v,v'\in S$, and every vertex lies in some $T(S)$. With $D'_S=D_S2^{2/\epsilon^c}$, each $S$ also has $\mathrm{Shell}(S)\subseteq V(G)$ and values $0\le\tilde d_S(v)\le32D'_S/\epsilon^2$ with $\tilde d_S(v)\ge\mathrm{dist}_G(S,v)$; and if $T(S)\ne\emptyset$, then $B_G(S,10D'_S/\epsilon^2)\subseteq\mathrm{Shell}(S)$ and on that ball $\tilde d_S(v)\le(1+\epsilon)\mathrm{dist}_G(S,v)+\epsilon D'_S$.
--
--   Let $i_S(v)=\max\{1,\lceil\tilde d_S(v)/(\epsilon D'_S)\rceil\}$ and $L_S(v)=\{j\epsilon D'_S: i_S(v)\le j\le\lceil32/\epsilon^3\rceil\}$. The graph $H_{G,\mathcal N}$ has regular vertices $V(G)$ and a supernode $u(S)$ per cluster. For $v\in\mathrm{Shell}(S)$ and $\gamma\in L_S(v)$ it has a **primary** edge $(v,u(S))$ of length $D_S2^{1/\epsilon^c}+\gamma$. For every edge $e\in E(G)$ with $\ell_G(e)\ge d$, every endpoint $x$ of $e$, with $y$ the other endpoint, and each primary edge $(x,u(S))$, it has a **secondary** edge $(y,u(S))$ of length $\ell(x,u(S))+\ell_G(e)$. Finally all lengths are rounded up to the next integral multiple of $d$.
--
--   This graph is the emulator that the paper builds at each distance scale.
--
--   **Formalization Note** $c$ is a parameter. Edges of $H_{G,\mathcal N}$ are named by what creates them, so an edge keeps its name while it exists.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Definition 3.3, p.17 (PDF 21); "Graph Derived from Shelled Neighborhood Cover", pp.17–18 (PDF 21–22); §7.4, p.61 (PDF 65)

import Mathlib
import Definitions.Def_DecrNbhdCover_Emulator

set_option autoImplicit false

namespace DecrNbhdCover

open scoped ENNReal

/-! # Shelled neighborhood covers and the derived graph `H_{G,N}`

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Definition 3.3, p.17, and "Graph Derived from Shelled
Neighborhood Cover", pp.17–18.

**Formalization Note.** `c` is the "large enough universal integral constant", a parameter here: every statement
that uses it is of the form "∃ c₀, ∀ c ≥ c₀". `Dprime` is `D′_S = D_S·2^{2/ε^c}`. All exponents are real powers.
Edges of `H_{G,N}` are named by what creates them: `primary S v j` is the edge `(v, u(S))` corresponding to
`γ = j·ε·D′_S ∈ L_S(v)`, and `secondary e b S j` is the edge owned by `e` obtained from the endpoint `x` of `e` (the first
endpoint if `b`, the second otherwise), joining the other endpoint `y` to `u(S)`. Lengths are rounded up to an integral
multiple of `d` at the end: `d·⌈X/d⌉`, the smallest multiple at least `X` (§7.4, p.61). The supernode `u(S)` is `S` itself. -/

variable {α σ ε : Type}

/-- The data `N = (S, {D_S, T(S), Shell(S)}_{S∈S})`, with `S` indexed by `σ`. -/
structure ShelledCover (α σ : Type) where
  clusters : Set σ
  S : σ → Set α
  DS : σ → ℝ
  T : σ → Set α
  Shell : σ → Set α
  dt : σ → α → ℝ

namespace ShelledCover

/-- `D′_S = D_S · 2^{2/ε^c}`. -/
noncomputable def Dprime (N : ShelledCover α σ) (eps : ℝ) (c : ℕ) (s : σ) : ℝ :=
  N.DS s * (2 : ℝ) ^ (2 / eps ^ c)

/-- `i_S(v) = max{1, ⌈d̃_S(v)/(ε D′_S)⌉}`. -/
noncomputable def iS (N : ShelledCover α σ) (eps : ℝ) (c : ℕ) (s : σ) (v : α) : ℕ :=
  max 1 ⌈N.dt s v / (eps * N.Dprime eps c s)⌉₊

/-- The top index `⌈32/ε³⌉` of `L_S(v)`. -/
noncomputable def jTop (eps : ℝ) : ℕ :=
  ⌈32 / eps ^ 3⌉₊

/-- `j·ε·D′_S ∈ L_S(v)`. -/
def InL (N : ShelledCover α σ) (eps : ℝ) (c : ℕ) (s : σ) (v : α) (j : ℕ) : Prop :=
  N.iS eps c s v ≤ j ∧ j ≤ jTop eps

end ShelledCover

/-- Definition 3.3: `N` is an `(ε, d, D)`-shelled neighborhood cover for the graph `G`. -/
structure IsShelledCover (G : Graph α ε) (N : ShelledCover α σ) (eps : ℝ) (d D c : ℕ) : Prop where
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 2
  d_pos : 0 < d
  d_lt : d < D
  D_ge : (d : ℝ) * (2 : ℝ) ^ (32 / eps ^ c) ≤ (D : ℝ)
  fin : N.clusters.Finite
  S_sub : ∀ s ∈ N.clusters, N.S s ⊆ G.V
  DS_ge : ∀ s ∈ N.clusters, (d : ℝ) * (2 : ℝ) ^ (16 / eps ^ c) ≤ N.DS s
  DS_le : ∀ s ∈ N.clusters, N.DS s ≤ (D : ℝ) / (2 : ℝ) ^ (16 / eps ^ c)
  T_sub : ∀ s ∈ N.clusters, N.T s ⊆ N.S s
  ball_sub : ∀ s ∈ N.clusters, ∀ v ∈ N.T s, G.ball v (N.DS s) ⊆ N.S s
  diam : ∀ s ∈ N.clusters, ∀ v ∈ N.S s, ∀ v' ∈ N.S s,
    ((G.dist v v' : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.DS s * (2 : ℝ) ^ (1 / eps ^ c))
  cover : ∀ v ∈ G.V, ∃ s ∈ N.clusters, v ∈ N.T s
  Shell_sub : ∀ s ∈ N.clusters, N.Shell s ⊆ G.V
  dt_nonneg : ∀ s ∈ N.clusters, ∀ v ∈ N.Shell s, 0 ≤ N.dt s v
  dt_le : ∀ s ∈ N.clusters, ∀ v ∈ N.Shell s, N.dt s v ≤ 32 * N.Dprime eps c s / eps ^ 2
  dt_ge : ∀ s ∈ N.clusters, ∀ v ∈ N.Shell s,
    ((G.distSet (N.S s) v : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.dt s v)
  ball_shell : ∀ s ∈ N.clusters, (N.T s).Nonempty →
    G.ballSet (N.S s) (10 * N.Dprime eps c s / eps ^ 2) ⊆ N.Shell s
  dt_upper : ∀ s ∈ N.clusters, (N.T s).Nonempty →
    ∀ v ∈ G.ballSet (N.S s) (10 * N.Dprime eps c s / eps ^ 2),
      ENNReal.ofReal (N.dt s v) ≤
        ENNReal.ofReal (1 + eps) * ((G.distSet (N.S s) v : ℕ∞) : ℝ≥0∞) +
          ENNReal.ofReal (eps * N.Dprime eps c s)

/-- Names of the edges of `H_{G,N}`. -/
inductive HEdge (α σ ε : Type) where
  | primary (s : σ) (v : α) (j : ℕ)
  | secondary (e : ε) (b : Bool) (s : σ) (j : ℕ)

/-- The endpoint `x` of `e` selected by `b`. -/
def endX (G : Graph α ε) (e : ε) (b : Bool) : α :=
  if b then (G.ends e).1 else (G.ends e).2

/-- The other endpoint `y` of `e`. -/
def endY (G : Graph α ε) (e : ε) (b : Bool) : α :=
  if b then (G.ends e).2 else (G.ends e).1

/-- The graph `H_{G,N}` derived from `G` and `N`, pp.17–18. -/
noncomputable def hGN (G : Graph α ε) (N : ShelledCover α σ) (eps : ℝ) (d c : ℕ) :
    WSGraph α σ (HEdge α σ ε) where
  V := G.V
  U := N.clusters
  E := {f | match f with
    | .primary s v j => s ∈ N.clusters ∧ v ∈ N.Shell s ∧ N.InL eps c s v j
    | .secondary e b s j => e ∈ G.E ∧ d ≤ G.len e ∧ s ∈ N.clusters ∧ endX G e b ∈ N.Shell s ∧
        N.InL eps c s (endX G e b) j}
  reg := fun f => match f with
    | .primary _ v _ => v
    | .secondary e b _ _ => endY G e b
  sup := fun f => match f with
    | .primary s _ _ => s
    | .secondary _ _ s _ => s
  len := fun f => match f with
    | .primary s _ j =>
        d * ⌈(N.DS s * (2 : ℝ) ^ (1 / eps ^ c) + (j : ℝ) * (eps * N.Dprime eps c s)) / (d : ℝ)⌉₊
    | .secondary e _ s j =>
        d * ⌈(N.DS s * (2 : ℝ) ^ (1 / eps ^ c) + (j : ℝ) * (eps * N.Dprime eps c s) +
          (G.len e : ℝ)) / (d : ℝ)⌉₊

end DecrNbhdCover


