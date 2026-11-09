-- Prove2me | Definitions.Def_GirthBethe_Sharp_FlowNetwork
-- name    : GirthBethe_Sharp_FlowNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:14:20.939624+00:00
-- url     : https://prove2.me/theorems/bd4ccd89-4612-420e-aa41-efc343397ed0
-- title:
--   (4.2), Definition 4.4 — $s$–$t$ flows, the auxiliary network $N$ and its flow $\varphi$
-- statement:
--   A directed network has a finite node set, an arc relation, a source $s$ and a sink $t$. A function $\varphi$ on ordered pairs of nodes is an $s$–$t$ flow if it vanishes off the arcs, is nonnegative on arcs, and satisfies conservation (inflow $=$ outflow) at every node other than $s,t$; its value is the net flow out of $s$.
--
--   For a finite bipartite graph $G=(L\sqcup R,E)$, weights $J^\pm_e$ and a vertex $v$, coefficients $\alpha^v_{ef}$ indexed by distinct edges $e,f\ni v$ satisfy (4.2) if they are nonnegative and
--   $$\sum_{f\ni v,\,f\ne e}\alpha^v_{ef}=J^-_e,\qquad \sum_{e\ni v,\,e\ne f}\alpha^v_{ef}\le J^+_f .$$
--   The slack is $\delta_{v,e}=J^+_e-\sum_{f\ni v,f\ne e}\alpha^v_{fe}$.
--
--   (Definition 4.4) The auxiliary network $N$ has a source $s$, a sink $t$ and a node $(v,e,\sigma)$ for every incidence $v\in e$ and sign $\sigma\in\{+,-\}$. Writing $e_L\in L$, $e_R\in R$ for the endpoints of $e$, its arcs are: the traversal arcs $(e_L,e,+)\to(e_R,e,+)$ and $(e_R,e,-)\to(e_L,e,-)$; for distinct $e,f\ni v$ the transfer arcs $(v,e,-)\to(v,f,+)$ if $v\in L$ and $(v,f,+)\to(v,e,-)$ if $v\in R$; the source arcs $s\to(v,e,+)$, $v\in L$, and the sink arcs $(v,e,+)\to t$, $v\in R$.
--
--   The assignment $\varphi$ puts $J^+_e$ on the plus traversal arc of $e$, $J^-_e$ on its minus traversal arc, $\alpha^v_{ef}$ on the transfer arc indexed by $(v,e,f)$, and $\delta_{v,e}$ on the source or sink arc at $(v,e,+)$.
--
--   This network converts the information revealed by $X_\star$ into a flow whose decomposition is controlled by the girth.
--
--   **Formalization Note** A node $(v,e,\sigma)$ is recorded by the edge $e$, the side of $v$ ($e_L$ or $e_R$) and the sign. Coefficients are a function of all pairs of edges; only pairs of distinct edges at $v$ are constrained or used.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 13, equation (4.2) (p. 12), the definition of δ and (4.3), Definition 4.4 and the following paragraph (p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_BipartiteGraph

open Finset

namespace GirthBethe.Sharp

/-! Directed networks and `s–t` flows, the local coefficient condition (4.2), the slacks
`δ_{v,e}`, and the auxiliary network `N` with its flow `φ` (Definition 4.4 and the paragraph
after it, §4.1 of Jain–Dong, STOC 2027 submission #705). -/

/-- A directed network on a finite node type: an arc relation, a source and a sink. -/
structure Network (N : Type*) where
  arc : N → N → Prop
  source : N
  sink : N

/-- `φ` is an `s–t` flow: it vanishes off the arcs, is nonnegative on arcs, and is conserved
(inflow = outflow) at every node other than the source and the sink. -/
def IsSTFlow {N : Type*} [Fintype N] (G : Network N) (φ : N → N → ℝ) : Prop :=
  (∀ x y, ¬ G.arc x y → φ x y = 0) ∧ (∀ x y, G.arc x y → 0 ≤ φ x y) ∧
    ∀ x, x ≠ G.source → x ≠ G.sink → ∑ y, φ y x = ∑ y, φ x y

/-- The value of a flow: net flow out of the source. -/
def flowValue {N : Type*} [Fintype N] (G : Network N) (φ : N → N → ℝ) : ℝ :=
  ∑ y, φ G.source y - ∑ y, φ y G.source

variable {L R : Type*} [Fintype L] [Fintype R]

open scoped Classical in
/-- Condition (4.2) at a vertex `v` for coefficients `α e f` (`e, f` distinct edges at `v`):
`α ≥ 0`, `∑_{f ∋ v, f ≠ e} α_{ef} = J_e^-` and `∑_{e ∋ v, e ≠ f} α_{ef} ≤ J_f^+`. -/
def SatisfiesCoeffCond {E : Finset (L × R)} (Jp Jm : Edge E → ℝ) (v : L ⊕ R)
    (α : Edge E → Edge E → ℝ) : Prop :=
  (∀ e f, Inc v e.1 → Inc v f.1 → e ≠ f → 0 ≤ α e f) ∧
  (∀ e, Inc v e.1 → ∑ f with Inc v f.1 ∧ f ≠ e, α e f = Jm e) ∧
  (∀ f, Inc v f.1 → ∑ e with Inc v e.1 ∧ e ≠ f, α e f ≤ Jp f)

open scoped Classical in
/-- `δ_{v,e} = J_e^+ - ∑_{f ∋ v, f ≠ e} α^v_{fe}`. -/
noncomputable def slack {E : Finset (L × R)} (Jp : Edge E → ℝ)
    (α : L ⊕ R → Edge E → Edge E → ℝ) (v : L ⊕ R) (e : Edge E) : ℝ :=
  Jp e - ∑ f with Inc v f.1 ∧ f ≠ e, α v f e

/-- Which endpoint of an edge an incidence node sits over: `eL ∈ L` or `eR ∈ R`. -/
inductive Side | left | right
  deriving DecidableEq

instance : Fintype Side :=
  Fintype.ofEquiv Bool
    { toFun := fun b => if b then .left else .right
      invFun := fun s => match s with | .left => true | .right => false
      left_inv := fun b => by cases b <;> rfl
      right_inv := fun s => by cases s <;> rfl }

/-- The sign `σ ∈ {+, -}` of an incidence node. -/
inductive Sgn | plus | minus
  deriving DecidableEq

instance : Fintype Sgn :=
  Fintype.ofEquiv Bool
    { toFun := fun b => if b then .plus else .minus
      invFun := fun s => match s with | .plus => true | .minus => false
      left_inv := fun b => by cases b <;> rfl
      right_inv := fun s => by cases s <;> rfl }

/-- Nodes of the auxiliary network `N`: source `s`, sink `t`, and a node `(v, e, σ)` for every
incidence `v ∈ e` and sign `σ`; the incidence `v ∈ e` is recorded by the edge `e` and the side of
`v` (`v = e_L` or `v = e_R`). -/
inductive AuxNode (E : Finset (L × R)) where
  | src : AuxNode E
  | snk : AuxNode E
  | inc : Edge E → Side → Sgn → AuxNode E
  deriving DecidableEq

instance (E : Finset (L × R)) : Fintype (AuxNode E) :=
  Fintype.ofEquiv (Option (Option (Edge E × Side × Sgn)))
    { toFun := fun x => match x with
        | none => .src
        | some none => .snk
        | some (some (e, s, σ)) => .inc e s σ
      invFun := fun n => match n with
        | .src => none
        | .snk => some none
        | .inc e s σ => some (some (e, s, σ))
      left_inv := fun x => by rcases x with _ | _ | ⟨e, s, σ⟩ <;> rfl
      right_inv := fun n => by cases n <;> rfl }

/-- The arcs of `N` (Definition 4.4): traversal arcs `(e_L,e,+) → (e_R,e,+)` and
`(e_R,e,-) → (e_L,e,-)`; for distinct `e, f ∋ v` the transfer arcs `(v,e,-) → (v,f,+)` for
`v ∈ L` and `(v,f,+) → (v,e,-)` for `v ∈ R`; source arcs `s → (v,e,+)`, `v ∈ L`; sink arcs
`(v,e,+) → t`, `v ∈ R`. -/
def auxArc {E : Finset (L × R)} : AuxNode E → AuxNode E → Prop
  | .inc e .left .plus, .inc e' .right .plus => e = e'
  | .inc e .right .minus, .inc e' .left .minus => e = e'
  | .inc e .left .minus, .inc f .left .plus => e ≠ f ∧ e.1.1 = f.1.1
  | .inc f .right .plus, .inc e .right .minus => e ≠ f ∧ e.1.2 = f.1.2
  | .src, .inc _ .left .plus => True
  | .inc _ .right .plus, .snk => True
  | _, _ => False

/-- The auxiliary network `N`. -/
def auxNetwork (E : Finset (L × R)) : Network (AuxNode E) where
  arc := auxArc
  source := .src
  sink := .snk

open scoped Classical in
/-- The specific assignment `φ` on `N` built from weights `J^±` and coefficients `α^v`: `J_e^+` on
the plus traversal arc of `e`, `J_e^-` on its minus traversal arc, `α^v_{ef}` on the transfer arc
indexed by `(v, e, f)`, and `δ_{v,e}` on the source or sink arc at `(v, e, +)`; `0` elsewhere. -/
noncomputable def auxFlow {E : Finset (L × R)} (Jp Jm : Edge E → ℝ)
    (α : L ⊕ R → Edge E → Edge E → ℝ) : AuxNode E → AuxNode E → ℝ
  | .inc e .left .plus, .inc e' .right .plus => if e = e' then Jp e else 0
  | .inc e .right .minus, .inc e' .left .minus => if e = e' then Jm e else 0
  | .inc e .left .minus, .inc f .left .plus =>
      if e ≠ f ∧ e.1.1 = f.1.1 then α (Sum.inl e.1.1) e f else 0
  | .inc f .right .plus, .inc e .right .minus =>
      if e ≠ f ∧ e.1.2 = f.1.2 then α (Sum.inr e.1.2) e f else 0
  | .src, .inc e .left .plus => slack Jp α (Sum.inl e.1.1) e
  | .inc e .right .plus, .snk => slack Jp α (Sum.inr e.1.2) e
  | _, _ => 0

end GirthBethe.Sharp


