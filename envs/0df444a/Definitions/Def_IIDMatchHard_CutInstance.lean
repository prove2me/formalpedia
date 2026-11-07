-- Prove2me | Definitions.Def_IIDMatchHard_CutInstance
-- name    : IIDMatchHard_CutInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:05:13.605392+00:00
-- url     : https://prove2.me/theorems/0016401b-1048-4eb0-aac3-222412a1fa2f
-- title:
--   The online matching instance $I(G,\lambda)$ and the cut policy $\pi_\sigma$ (Algorithm 1)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with $n=|V|$ and $m=|E|$, and let $\lambda>0$. The instance **$I(G,\lambda)$** has:
--
--   1. **offline vertices** $u^+,u^-$ for each $u\in V$;
--   2. **vertex types** $u\in V$ with neighbors $\{u^+,u^-\}$ and rate $\lambda_u=1$;
--   3. **edge types** $e^+,e^-$ for each $e=(u,v)\in E$, with neighbors $\{u^+,v^+\}$ and $\{u^-,v^-\}$ and rate $\lambda$;
--   4. type probabilities proportional to the rates, $1/R$ for a vertex type and $\lambda/R$ for an edge type, where $R=n+2m\lambda$;
--   5. $T=\lceil R\rceil$ online vertices.
--
--   The **cut policy** $\pi_\sigma$ of a cut $\sigma$ (Algorithm 1) proceeds as follows.
--
--   1. On a vertex arrival $u$: if $u^+$ and $u^-$ are both free, it matches to $u^{-\sigma(u)}$. If exactly one is free, it matches to that one. Otherwise it rejects.
--   2. On an edge arrival $e^s$ with $e=(u,v)$: if $w^s$ and $w^{-s}$ are both free for some $w\in\{u,v\}$, it matches to $w^s$ for the first such $w$ in a fixed order of $V$. Else, if $w^s$ is free for some $w\in\{u,v\}$, it matches to $w^s$ for the first such $w$. Otherwise it rejects.
--
--   $I(G,\lambda)$ is the instance built from a Max Cut instance. The cut policy links cuts of $G$ to matching policies.
--
--   **Formalization Note** Offline vertices are `V × Bool`, with `(u, true)` $=u^+$. Edges are elements of Mathlib's `G.edgeSet` (unordered pairs), so $\{u^s,v^s\}$ needs no orientation. The fixed order of $V$ is an explicit `LinearOrder` argument of $\pi_\sigma$. $T$ is `Nat.ceil R`.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), §3.1, p.5 (PDF p.6); Algorithm 1, p.6 (PDF p.7)

import Definitions.Def_IIDMatchHard_Model
import Definitions.Def_IIDMatchHard_Cut

set_option autoImplicit false

namespace IIDMatchHard

variable {V : Type*}

/-- The online arrival types of `I(G, λ)` (§3.1, p.5 (PDF p.6)): a **vertex type** `u` for each
`u ∈ V`, and two **edge types** `e⁺`, `e⁻` for each edge `e ∈ E` (`edge e true` is `e⁺`,
`edge e false` is `e⁻`). -/
inductive IType (G : SimpleGraph V) where
  /-- The vertex type `u`. -/
  | vtx (u : V)
  /-- The edge type `e^s` (`s = true` is `+`). -/
  | edge (e : G.edgeSet) (s : Bool)
  deriving DecidableEq

namespace IType

variable {G : SimpleGraph V}

/-- The arrival types as a sum type. -/
def equivSum : IType G ≃ V ⊕ (G.edgeSet × Bool) where
  toFun
    | vtx u => Sum.inl u
    | edge e s => Sum.inr (e, s)
  invFun
    | Sum.inl u => vtx u
    | Sum.inr x => edge x.1 x.2
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with u | ⟨e, s⟩ <;> rfl

open Classical in
noncomputable instance [Fintype V] : Fintype (IType G) :=
  Fintype.ofEquiv _ equivSum.symm

/-- Types carry the discrete σ-algebra. -/
instance : MeasurableSpace (IType G) := ⊤

instance : DiscreteMeasurableSpace (IType G) := ⟨fun _ => trivial⟩

end IType

variable [Fintype V] [DecidableEq V]

/-- The neighbors of the arrival types of `I(G, λ)` among the offline vertices `V × Bool`
(`(u, true)` is `u⁺`, `(u, false)` is `u⁻`): the vertex type `u` has neighbors `{u⁺, u⁻}`, and the
edge type `e^s` of `e = (u, v)` has neighbors `{u^s, v^s}`. -/
def cutNbr (G : SimpleGraph V) : IType G → Finset (V × Bool)
  | .vtx u => {(u, true), (u, false)}
  | .edge e s => Finset.univ.filter fun x : V × Bool => x.1 ∈ (e : Sym2 V) ∧ x.2 = s

/-- The arrival rates of `I(G, λ)`: `λ_u = 1` for a vertex type and `λ_{e^±} = λ` for an edge
type. -/
def cutRate (G : SimpleGraph V) (lam : ℝ) : IType G → ℝ
  | .vtx _ => 1
  | .edge _ _ => lam

/-- `R = n + 2mλ`, the total arrival rate of `I(G, λ)` (§3.1, p.5). -/
noncomputable def totalRate (G : SimpleGraph V) (lam : ℝ) : ℝ :=
  (Fintype.card V : ℝ) + 2 * (numEdges G : ℝ) * lam

/-- The online stochastic matching instance **`I(G, λ)`** of §3.1 (p.5 (PDF p.6)), Teng, Yang,
*Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026, sha256
f0193d92…): offline vertices `u⁺, u⁻` for `u ∈ V`, the vertex types and edge types of `IType G`
with the neighbors `cutNbr G`, type probabilities proportional to the rates (`1/R` for a vertex
type, `λ/R` for an edge type) and `T = ⌈R⌉` online vertices, where `R = n + 2mλ`.

**Formalization Note.** The edges of `G` are the elements of `G.edgeSet` (unordered pairs, `G`
simple), so `e = (u, v)` needs no orientation: `{u^s, v^s}` is symmetric. `⌈R⌉` is `Nat.ceil`. -/
noncomputable def cutInst (G : SimpleGraph V) (lam : ℝ) : IIDModel (V × Bool) (IType G) where
  nbr := cutNbr G
  p y := cutRate G lam y / totalRate G lam
  T := ⌈totalRate G lam⌉₊

/-- The first element of `W` in the order `o`, if `W` is nonempty. -/
def firstIn (o : LinearOrder V) (W : Finset V) : Option V :=
  letI := o
  if h : W.Nonempty then some (W.min' h) else none

/-- The policy **`π_σ` induced by a cut `σ`** (Algorithm 1, p.6 (PDF p.7)), with tie-breaking by
the fixed order `o` of `V`. On a vertex type `u`: if `u⁺` and `u⁻` are both free, match to
`u^{−σ(u)}`; else if exactly one is free, match to it; else reject. On an edge type `e^s`,
`e = (u, v)`: if `w^s` and `w^{−s}` are both free for some `w ∈ {u, v}`, match to `w^s` for the
first such `w`; else if `w^s` is free for some `w ∈ {u, v}`, match to `w^s` for the first such
`w`; else reject.

**Formalization Note.** `σ u = true` means `σ(u) = +`, so `u^{−σ(u)}` is `(u, !σ u)`. The policy
reads only the matched set and the current type; "free" means not in the matched set `S`. In the
adjusted Poisson model it is run with the adjusted neighbor sets, so it rejects every blocked
arrival and follows Algorithm 1 on the others with the free vertices of the adjusted model
(App. B.5, p.18). -/
def cutPolicy (G : SimpleGraph V) (o : LinearOrder V) (σ : V → Bool) :
    Policy (V × Bool) (IType G) :=
  fun _ S y =>
    match y with
    | .vtx u =>
        if (u, true) ∉ S ∧ (u, false) ∉ S then some (u, !σ u)
        else if (u, true) ∉ S then some (u, true)
        else if (u, false) ∉ S then some (u, false)
        else none
    | .edge e s =>
        let W := Finset.univ.filter fun w : V => w ∈ (e : Sym2 V)
        match firstIn o (W.filter fun w => (w, s) ∉ S ∧ (w, !s) ∉ S) with
        | some w => some (w, s)
        | none => (firstIn o (W.filter fun w => (w, s) ∉ S)).map fun w => (w, s)

end IIDMatchHard


