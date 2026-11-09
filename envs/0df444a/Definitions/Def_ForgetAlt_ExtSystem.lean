-- Prove2me | Definitions.Def_ForgetAlt_ExtSystem
-- name    : ForgetAlt_ExtSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:45.401816+00:00
-- url     : https://prove2.me/theorems/b7d4b73b-5829-43d2-9329-01cf46e1e608
-- title:
--   The super free vertex $f$, parity distances $\mathrm{dist}^\theta$, orthodox parity $\alpha$, volume, height and level
-- statement:
--   Given $(G,M)$, add a **super free vertex** $f$ and, for each free vertex $u$, a new vertex $a_u$ with edges $\{f,a_u\}$, $\{a_u,u\}$; the edge $\{a_u,u\}$ is added to the matching. In the resulting system $f$ is the only free vertex.
--
--   For a parity $\theta\in\{\mathrm{odd},\mathrm{even}\}$, $\mathrm{dist}^\theta(x)$ is the length of a shortest alternating path of parity $\theta$ from $f$ to $x$ in the extended system ($\infty$ if none; the trivial path at $f$ counts, so $\mathrm{dist}^{\mathrm{even}}(f)=0$). Further
--
--   $$\mathrm{dist}^\alpha(x)=\min_\theta \mathrm{dist}^\theta(x),\qquad \mathrm{dist}^\beta(x)=\max_\theta \mathrm{dist}^\theta(x),$$
--
--   $\alpha(x)$ is the parity attaining the minimum (the **orthodox** parity) and $\beta(x)=\bar\alpha(x)$. For an edge $e$, $\rho(e)=\mathrm{odd}$ if $e$ is a matching edge and $\mathrm{even}$ otherwise. For $e=\{y,z\}$,
--
--   $$\mathrm{vlevel}(e)=\mathrm{dist}^{\rho(e)}(y)+\mathrm{dist}^{\rho(e)}(z)+1,\qquad \mathrm{hlevel}(e)=\max\{\mathrm{dist}^{\rho(e)}(y),\mathrm{dist}^{\rho(e)}(z)\},$$
--
--   $\mathrm{vlevel}(v)=\mathrm{dist}^\alpha(v)+\mathrm{dist}^\beta(v)$, and the **level** of $e$ orders edges by volume and then by height.
--
--   **Formalization Note** The vertex type has $f$, a copy of each vertex, and an $a_u$ for every $u$; $a_u$ is joined to $f$ and $u$ only when $u$ is free, so the other $a_u$ are isolated and unreachable. Distances are in $\mathbb N\cup\{\infty\}$. $\alpha$ is `even` (junk) on unreachable vertices, where the paper leaves it undefined. The level takes values in $\mathrm{WithTop}(\mathbb N\times_{\mathrm{lex}}\mathbb N)$: $\top$ for infinite volume, else (volume, height); this is the order of $n'\cdot\mathrm{vlevel}+\mathrm{hlevel}$ for every $n'>|V(G)|$, as footnote 5 intends.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Section 3.1.1, printed pp.15–16 (PDF pp.16–17); Definition 3.5 and footnote 5, printed p.18 (PDF p.19)

import Mathlib
import Definitions.Def_ForgetAlt_Matching

namespace ForgetAlt

open BergeMatching.Core

/-!
# The system with the super free vertex, parity-wise distances, volume, height and level

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…), Section 3.1.1, printed pp.15–16 (PDF pp.16–17), and
Definition 3.5 with footnote 5, printed p.18 (PDF p.19).

**Formalization Notes.**
* The extended vertex type `ExtV V` has the super free vertex `f`, a copy `orig v` of every
  vertex of `G`, and a vertex `aux u` for **every** `u : V`. The extended graph joins `f — aux u`
  and `aux u — orig u` only for free `u`, so `aux u` of a matched `u` is an isolated vertex: it
  is unreachable from `f`, has infinite distances and lies outside the ABD, which is all the
  paper's construction sees. The extended matching is `M` together with every `{aux u, orig u}`
  for free `u`.
* Distances are in `ℕ∞` with `⊤ = ∞` (infimum over an empty set of paths). The trivial path at
  `f` is an alternating path of length `0` (p.15), so `dist even f = 0`.
* `alpha v` is the parity attaining the smaller distance. On a vertex unreachable from `f` both
  distances are `⊤` and `alpha v = even` is a junk value; the paper leaves `α` undefined there
  and every statement that uses `alpha`, `beta`, `candParents` restricts to reachable vertices.
* `level e` lives in `WithTop (ℕ ×ₗ ℕ)`: an edge of infinite volume has level `⊤`, and a
  finite-volume edge has level `(vlevel e, hlevel e)` ordered lexicographically. This is the
  order of `n′·vlevel(e) + hlevel(e)` for every `n′ > |V(G)|` (finite heights are below `n′`),
  which is exactly the ordering footnote 5 says is intended.
-/

/-- The vertices of the system with the super free vertex: `f`, the original vertices, and the
auxiliary vertices `a_u`. -/
inductive ExtV (V : Type) where
  | f : ExtV V
  | orig : V → ExtV V
  | aux : V → ExtV V
  deriving DecidableEq

variable {V : Type}

/-- Adjacency of the extended system (p.15): the edges of `G` between original vertices, and
`{f, a_u}`, `{a_u, u}` for every free vertex `u`. -/
def extAdj (G : SimpleGraph V) (M : G.Subgraph) : ExtV V → ExtV V → Prop
  | .orig a, .orig b => G.Adj a b
  | .f, .aux u => IsNeutral M u
  | .aux u, .f => IsNeutral M u
  | .aux u, .orig v => u = v ∧ IsNeutral M u
  | .orig v, .aux u => u = v ∧ IsNeutral M u
  | _, _ => False

/-- The extended graph. -/
def extGraph (G : SimpleGraph V) (M : G.Subgraph) : SimpleGraph (ExtV V) where
  Adj := extAdj G M
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp only [extAdj] at h ⊢
    all_goals first
      | exact h
      | exact G.adj_symm h⟩
  loopless := ⟨fun x h => by
    cases x <;> simp_all [extAdj]⟩

/-- The extended matching (p.15): the edges of `M` together with `{a_u, u}` for free `u`. -/
def extMatching (G : SimpleGraph V) (M : G.Subgraph) : Set (Sym2 (ExtV V)) :=
  {e | (∃ a b, M.Adj a b ∧ e = s(.orig a, .orig b)) ∨
       (∃ u, IsNeutral M u ∧ e = s(.aux u, .orig u))}

/-- The two parities. -/
inductive Parity where
  | odd : Parity
  | even : Parity
  deriving DecidableEq

/-- `θ̄`, the other parity. -/
def Parity.flip : Parity → Parity
  | .odd => .even
  | .even => .odd

/-- The parity of a natural number. -/
def parityOf (k : ℕ) : Parity := if k % 2 = 1 then .odd else .even

/-- `dist^θ(x)` (p.15): the length of a shortest alternating path of parity `θ` from `f` to `x`
in the extended system, `⊤` if there is none. -/
noncomputable def dist (G : SimpleGraph V) (M : G.Subgraph) (θ : Parity) (x : ExtV V) : ℕ∞ :=
  ⨅ (p : (extGraph G M).Walk .f x) (_ : IsAltPath (extMatching G M) p ∧ parityOf p.length = θ),
    (p.length : ℕ∞)

/-- `dist^α(x) = min_θ dist^θ(x)` (p.16). -/
noncomputable def distA (G : SimpleGraph V) (M : G.Subgraph) (x : ExtV V) : ℕ∞ :=
  min (dist G M .odd x) (dist G M .even x)

/-- `dist^β(x) = max_θ dist^θ(x)` (p.16). -/
noncomputable def distB (G : SimpleGraph V) (M : G.Subgraph) (x : ExtV V) : ℕ∞ :=
  max (dist G M .odd x) (dist G M .even x)

/-- `x` is reachable from `f` by an alternating path, i.e. `x ∈ V(H_I)` (Definition 3.2). -/
def Reach (G : SimpleGraph V) (M : G.Subgraph) (x : ExtV V) : Prop :=
  distA G M x < ⊤

/-- The orthodox parity `α(x)` (p.16): the parity with `dist^{α(x)}(x) < dist^{ᾱ(x)}(x)`. Junk
(`even`) on unreachable `x`. -/
noncomputable def alpha (G : SimpleGraph V) (M : G.Subgraph) (x : ExtV V) : Parity :=
  open Classical in if dist G M .odd x < dist G M .even x then .odd else .even

/-- The unorthodox parity `β(x) = ᾱ(x)` (p.16). -/
noncomputable def beta (G : SimpleGraph V) (M : G.Subgraph) (x : ExtV V) : Parity :=
  (alpha G M x).flip

/-- `ρ(e)` (p.16): `odd` if `e` is a matching edge of the extended system, `even` otherwise. -/
noncomputable def rho (G : SimpleGraph V) (M : G.Subgraph) (e : Sym2 (ExtV V)) : Parity :=
  open Classical in if e ∈ extMatching G M then .odd else .even

/-- The volume `vlevel(e) = dist^{ρ(e)}(y) + dist^{ρ(e)}(z) + 1` of `e = {y, z}`
(Definition 3.5). -/
noncomputable def vlevelE (G : SimpleGraph V) (M : G.Subgraph) (e : Sym2 (ExtV V)) : ℕ∞ :=
  Sym2.lift ⟨fun y z => dist G M (rho G M e) y + dist G M (rho G M e) z + 1,
    fun y z => by simp only [add_comm (dist G M (rho G M e) y)]⟩ e

/-- The height `hlevel(e) = max{dist^{ρ(e)}(y), dist^{ρ(e)}(z)}` of `e = {y, z}`
(Definition 3.5). -/
noncomputable def hlevelE (G : SimpleGraph V) (M : G.Subgraph) (e : Sym2 (ExtV V)) : ℕ∞ :=
  Sym2.lift ⟨fun y z => max (dist G M (rho G M e) y) (dist G M (rho G M e) z),
    fun _ _ => max_comm _ _⟩ e

/-- The volume `vlevel(v) = dist^α(v) + dist^β(v)` of a vertex (Definition 3.5). -/
noncomputable def vlevelV (G : SimpleGraph V) (M : G.Subgraph) (v : ExtV V) : ℕ∞ :=
  distA G M v + distB G M v

/-- The level of `e` (Definition 3.5 with footnote 5): volume first, then height,
lexicographically; `⊤` for an edge of infinite volume. -/
noncomputable def level (G : SimpleGraph V) (M : G.Subgraph) (e : Sym2 (ExtV V)) :
    WithTop (ℕ ×ₗ ℕ) :=
  open Classical in
  if vlevelE G M e = ⊤ then ⊤
  else ((toLex ((vlevelE G M e).toNat, (hlevelE G M e).toNat) : ℕ ×ₗ ℕ) : WithTop (ℕ ×ₗ ℕ))

end ForgetAlt


