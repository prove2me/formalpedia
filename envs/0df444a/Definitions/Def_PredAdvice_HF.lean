-- Prove2me | Definitions.Def_PredAdvice_HF
-- name    : PredAdvice_HF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:52.080455+00:00
-- url     : https://prove2.me/theorems/d9f18544-e000-41c5-bde6-33a4ffefb5b0
-- title:
--   Bipartite graphs $B^{h,j}_{d,c}$, maximal matchings, $F^{out}_u$, $F^{in}_v$ and the hop set $\hat H_F$
-- statement:
--   Let $V_L,V_R$ be two disjoint copies of $V$. For $1\le d<D$, $c\in[3D]$, $h\in V$ and $j\in[L]$, the bipartite graph $B^{h,j}_{d,c}=(V_L,V_R,E^{h,j}_{d,c})$ has the edge $(u_L,v_R)$ iff
--
--   1. $(u,v)$ is separated, 2. $h\in H^\circ_{u,v}$, 3. $\mathrm{dist}(u,v)=d$, 4. $j(u,v,h)=j$, 5. $c_{j,u}(h)=c$.
--
--   For a choice of maximal matchings $M^{h,j}_{d,c}$ of these graphs, with endpoint sets $C^{h,j}_{d,c}$,
--   $$
--   F^{out}_u=\{h : \exists d,c,j,\ u_L\in C^{h,j}_{d,c}\},\qquad F^{in}_v=\{h : \exists d,c,j,\ v_R\in C^{h,j}_{d,c}\},
--   $$
--   $$
--   \hat H_F=\{(u,h) : h\in F^{out}_u\}\cup\{(h,v) : h\in F^{in}_v\}. \tag{6}
--   $$
--   These hops realize the separated small pairs (Lemma 3.4), and their number is controlled by $RS(n)$ (Lemma 3.5).
--
--   **Formalization Note** An edge $(u_L,v_R)$ is the ordered pair $(u,v)$. A maximal matching is a set of pairwise disjoint edges of the bipartite graph such that every edge has a covered endpoint. Hops carry weight $\mathrm{dist}$, which statements use directly.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3.3, pp.12–13, eq. (6)

import Mathlib
import Definitions.Def_PredAdvice_IsSeparated

set_option autoImplicit false

namespace PredAdvice

/-- The edge relation of the bipartite graph `B^{h,j}_{d,c} = (V_L, V_R, E^{h,j}_{d,c})`
(Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027
submission (manuscript sha256 0ae8a68d…), §3.3, p.12): `(u_L, v_R) ∈ E^{h,j}_{d,c}` iff
(1) `(u, v)` is separated, (2) `h ∈ H°_{u,v}`, (3) `dist(u, v) = d`, (4) `j(u, v, h) = j`,
(5) `c_{j,u}(h) = c`.

**Formalization Note** `V_L` and `V_R` are two disjoint copies of `V`; an edge `(u_L, v_R)` is the
ordered pair `(u, v)`, its first coordinate the left endpoint and its second the right one. -/
def BEdge {V : Type*} [Fintype V] [DecidableEq V] {D L : ℕ} (G : Digraph V)
    (χ : Colorings V D L) (d c : ℕ) (j : Fin L) (h : V) (u v : V) : Prop :=
  IsSeparated G χ u v ∧ h ∈ Hcirc G u v ∧ dist G u v = d ∧ IsFirstIsolating G χ j u v h ∧
    shiftedColor G χ j u h = c

/-- `M` is a **maximal matching** of the bipartite graph `(V_L, V_R)` with edge relation `r`:
its edges are edges of `r`, two distinct edges of `M` share neither the left nor the right
endpoint, and every edge of `r` has its left or its right endpoint covered by `M` (no edge can be
added). -/
def IsMaximalMatching {V : Type*} (r : V → V → Prop) (M : Finset (V × V)) : Prop :=
  (∀ p ∈ M, r p.1 p.2) ∧ (∀ p ∈ M, ∀ q ∈ M, p ≠ q → p.1 ≠ q.1 ∧ p.2 ≠ q.2) ∧
    ∀ a b, r a b → ∃ p ∈ M, p.1 = a ∨ p.2 = b

/-- A choice of maximal matchings `M^{h,j}_{d,c}` of `B^{h,j}_{d,c}` for every `1 ≤ d < D`,
`c ∈ [3D]`, `j ∈ [L]`, `h ∈ V` (§3.3, p.12). `M d c j h` is `M^{h,j}_{d,c}`; its values outside the
index ranges are never used. -/
def IsMatchingFamily {V : Type*} [Fintype V] [DecidableEq V] {D L : ℕ} (G : Digraph V)
    (χ : Colorings V D L) (M : ℕ → ℕ → Fin L → V → Finset (V × V)) : Prop :=
  ∀ d c : ℕ, ∀ j : Fin L, ∀ h : V, 1 ≤ d → d < D → 1 ≤ c → c ≤ 3 * D →
    IsMaximalMatching (BEdge G χ d c j h) (M d c j h)

open Classical in
/-- `F^out_u := {h ∈ V | ∃ d, c, j, u_L ∈ C^{h,j}_{d,c}}` (§3.3, p.13), where `C^{h,j}_{d,c}` is
the set of endpoints of the edges of `M^{h,j}_{d,c}`; `u_L ∈ C^{h,j}_{d,c}` means that some edge
`(u, b)` lies in `M^{h,j}_{d,c}`. -/
noncomputable def FOut {V : Type*} [Fintype V] {L : ℕ} (D : ℕ)
    (M : ℕ → ℕ → Fin L → V → Finset (V × V)) (u : V) : Finset V :=
  Finset.univ.filter fun h => ∃ d c : ℕ, ∃ j : Fin L, 1 ≤ d ∧ d < D ∧ 1 ≤ c ∧ c ≤ 3 * D ∧
    ∃ b : V, (u, b) ∈ M d c j h

open Classical in
/-- `F^in_v := {h ∈ V | ∃ d, c, j, v_R ∈ C^{h,j}_{d,c}}` (§3.3, p.13): some edge `(a, v)` lies in
`M^{h,j}_{d,c}`. -/
noncomputable def FIn {V : Type*} [Fintype V] {L : ℕ} (D : ℕ)
    (M : ℕ → ℕ → Fin L → V → Finset (V × V)) (v : V) : Finset V :=
  Finset.univ.filter fun h => ∃ d c : ℕ, ∃ j : Fin L, 1 ≤ d ∧ d < D ∧ 1 ≤ c ∧ c ≤ 3 * D ∧
    ∃ a : V, (a, v) ∈ M d c j h

open Classical in
/-- The hop set `Ĥ_F := {(u, h) ∈ V² | h ∈ F^out_u} ∪ {(h, v) ∈ V² | h ∈ F^in_v}`
(Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027
submission (manuscript sha256 0ae8a68d…), §3.3, eq. (6), p.13), built from a family of maximal
matchings `M^{h,j}_{d,c}` (`IsMatchingFamily`).

**Formalization Note** A pair `(a, b)` is a hop of `Ĥ_F` iff `b ∈ F^out_a` or `a ∈ F^in_b`. Each hop
carries the weight `dist(a, b)`; the weight is not stored, statements use `dist` directly. -/
noncomputable def HF {V : Type*} [Fintype V] {L : ℕ} (D : ℕ)
    (M : ℕ → ℕ → Fin L → V → Finset (V × V)) : Finset (V × V) :=
  Finset.univ.filter fun p => p.2 ∈ FOut D M p.1 ∨ p.1 ∈ FIn D M p.2

end PredAdvice


