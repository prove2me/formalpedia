-- Prove2me | Definitions.Def_TreeEquivalenceHORS_Equivalence_Semantics
-- name    : TreeEquivalenceHORS_Equivalence_Semantics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:09.118137+00:00
-- url     : https://prove2.me/theorems/c43d7ee3-26c8-4ac2-96a1-2e9e5baba7a9
-- title:
--   Head rewriting, positive observations, value trees with ⊥, and productivity
-- statement:
--   Fix a scheme $G$. For closed ground terms the only rewriting is **head unfolding**
--   $$F\,u_1\cdots u_r\to_h t_F[u_1/x_1,\dots,u_r/x_r],$$
--   with simultaneous substitution, applicable when the head of the term is a nonterminal applied to exactly its $r$ parameters. Write $t\Downarrow_G a(t_0,\dots,t_{r-1})$ when finitely many head steps produce that terminal application.
--
--   1. **Observations.** Addresses are words over $\mathbb N$ with zero-based child indices.
--   $$\mathrm{Obs}_G(t,\varepsilon,a)\iff\exists\vec u\ t\Downarrow_G a(\vec u),\qquad \mathrm{Obs}_G(t,iw,a)\iff\exists c,\vec u\,[t\Downarrow_G c(\vec u)\wedge i<|\vec u|\wedge\mathrm{Obs}_G(u_i,w,a)].$$
--   2. **Value tree.** $\mathrm{BT}_G(t)$ has root $a$ and children $\mathrm{BT}_G(u_i)$ when $t\Downarrow_G a(\vec u)$, and otherwise is a present nullary node $\bot$. It is represented by its label at every finite address: a terminal, $\bot$, or absence $\dagger$ (below a leaf, below $\bot$, or at a child index beyond the arity). $\mathrm{BT}(G)=\mathrm{BT}_G(S)$.
--   3. **Productivity.** Every term is productive to depth $0$; $t$ is productive to depth $d+1$ if it exposes a terminal and every actual child is productive to depth $d$. $G$ is productive if $S$ is productive to every depth. Finite terminal leaves are allowed.
--
--   These are the semantic objects compared by tree equivalence.
--
--   **Formalization Note** The head of a term is computed by iterating the deterministic head step; `head` takes the first budget at which a terminal is exposed (a classical choice that does not depend on the budget, since a terminal head admits no further step). `BTat G t` is the tree $\mathrm{BT}_G(t)$ as a function from addresses to `Lab`.
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Section 3, printed p. 10 / PDF p. 12 (head rewriting, Obs, BT, productivity)

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Syntax

namespace TreeEquivalenceHORS.Equivalence

/-! # Head rewriting, observations, value trees and productivity (Section 3, PDF p. 12 / printed p. 10)

Head rewriting unfolds a fully applied nonterminal at the head of a term by simultaneous
substitution. Observations, the value tree `BT` (with present `⊥` nodes and absent addresses) and
productivity are defined from it. -/

namespace Tm

/-- Simultaneous substitution of `args[i]` for the parameter `var i`. -/
def subst (args : List Tm) : Tm → Tm
  | var i => args.getD i (var i)
  | app t u => app (t.subst args) (u.subst args)
  | nt F => nt F
  | tm c => tm c

end Tm

namespace HORS

/-- One head step `F u₁ ⋯ uᵣ →ₕ t_F[u₁/x₁, …, uᵣ/xᵣ]`: defined exactly when the head of the term is
a nonterminal `F` applied to exactly as many arguments as `F` has parameters. -/
def headStep (G : HORS) (t : Tm) : Option Tm :=
  match t.spine with
  | (.nt F, as) =>
      match G.nts[F]?, G.rules[F]? with
      | some τ, some body => if as.length = τ.args.length then some (body.subst as) else none
      | _, _ => none
  | _ => none

/-- The head-step relation `t →ₕ t'`. -/
def HeadStep (G : HORS) (t t' : Tm) : Prop := G.headStep t = some t'

/-- Head convergence `t ⇓_G c(u₀, …, u_{r-1})`: finitely many head steps produce the terminal
application `c u₀ ⋯ u_{r-1}`. -/
def HeadConv (G : HORS) (t : Tm) (c : ℕ) (us : List Tm) : Prop :=
  ∃ t', Relation.ReflTransGen G.HeadStep t t' ∧ t'.spine = (Tm.tm c, us)

/-- Positive observations (Section 3): `Obs_G(t, ε, c)` iff `t` head-converges to `c(u⃗)`, and
`Obs_G(t, i w, c)` iff `t` head-converges to some `c'(u⃗)` with `i < |u⃗|` and `Obs_G(uᵢ, w, c)`.
Addresses are lists of natural numbers with zero-based child indices. -/
def Obs (G : HORS) : Tm → List ℕ → ℕ → Prop
  | t, [], c => ∃ us, G.HeadConv t c us
  | t, i :: w, c => ∃ c' us, G.HeadConv t c' us ∧ ∃ h : i < us.length, G.Obs us[i] w c

/-- `n` deterministic head steps (stopping early when no head step applies). -/
def run (G : HORS) : ℕ → Tm → Tm
  | 0, t => t
  | n + 1, t =>
      match G.headStep t with
      | some t' => G.run n t'
      | none => t

end HORS

/-- The terminal application exposed by a term, if its head is a terminal. -/
def exposed (t : Tm) : Option (ℕ × List Tm) :=
  match t.spine with
  | (.tm c, us) => some (c, us)
  | _ => none

namespace HORS

open Classical in
/-- The head of `t`: the terminal and children exposed by head unfolding, or `none` (`⊥`) when no
finite number of head steps exposes a terminal. Head steps are deterministic, so this is the
unique head exposure of `t`. -/
noncomputable def head (G : HORS) (t : Tm) : Option (ℕ × List Tm) :=
  if h : ∃ n, (exposed (G.run n t)).isSome then exposed (G.run (Nat.find h) t) else none

end HORS

/-- What a tree has at an address: a terminal label `term c`, a present nullary bottom node
`bot` (`⊥`), or nothing (`absent`, written `†`). -/
inductive Lab : Type where
  | term (c : ℕ) : Lab
  | bot : Lab
  | absent : Lab
  deriving DecidableEq, Encodable, Repr

namespace HORS

/-- The value tree `BT_G(t)`, as its label at every finite address: the root is the exposed
terminal `a` with children `u⃗` when `t ⇓_G a(u⃗)`, and `⊥` otherwise; children of a `⊥` node and
child indices at least the arity of a terminal are absent. The tree may be infinite. -/
noncomputable def BTat (G : HORS) : Tm → List ℕ → Lab
  | t, [] =>
      match G.head t with
      | some (c, _) => .term c
      | none => .bot
  | t, i :: w =>
      match G.head t with
      | some (_, us) => if h : i < us.length then G.BTat us[i] w else .absent
      | none => .absent

/-- The tree of the scheme, `BT(G) = BT_G(S_G)`. -/
noncomputable def BT (G : HORS) : List ℕ → Lab := G.BTat (.nt G.start)

/-- Productivity to depth `d` (Section 3): always at depth `0`; at depth `d + 1` the term exposes a
terminal and every actual child is productive to depth `d`. -/
def ProdDepth (G : HORS) : Tm → ℕ → Prop
  | _, 0 => True
  | t, d + 1 => ∃ c us, G.HeadConv t c us ∧ ∀ u ∈ us, G.ProdDepth u d

/-- A scheme is productive if its start term is productive to every depth. -/
def Prod (G : HORS) : Prop := ∀ d, G.ProdDepth (.nt G.start) d

end HORS

end TreeEquivalenceHORS.Equivalence


