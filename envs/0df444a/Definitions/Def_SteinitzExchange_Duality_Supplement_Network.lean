-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_Network
-- name    : SteinitzExchange_Duality_Supplement_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:25:03.891948+00:00
-- url     : https://prove2.me/theorems/b13bffa4-f3f7-4369-8e93-e865e6babb18
-- title:
--   Network induction: flow boundary, feasible flows, induced base set $\tilde B$ and induced function $\tilde\omega$ (7.1)–(7.6)
-- statement:
--   Let $G=(V,A;V^+,V^-)$ be a directed graph with finite vertex set $V$, finite arc set $A$ (each arc $a$ has a tail and a head; parallel arcs and loops are allowed), a set $V^+\subseteq V$ of **entrances** and a set $V^-\subseteq V$ of **exits**. Let $\underline c,\bar c:A\to\mathbb Z$ be lower and upper capacities, $w:A\to\mathbb R$ arc weights, $B^+\subseteq\mathbb Z^{V^+}$ a finite set and $\omega^+:B^+\to\mathbb R$.
--
--   A **flow** is $\varphi:A\to\mathbb Z$; its **boundary** is
--   $$\partial\varphi(v)=\sum\{\varphi(a)\mid a\in\delta^+v\}-\sum\{\varphi(a)\mid a\in\delta^-v\}\qquad(v\in V),$$
--   where $\delta^+v$ ($\delta^-v$) is the set of arcs leaving (entering) $v$. Write $(\partial\varphi)^+$ and $(\partial\varphi)^-$ for the restrictions of $\partial\varphi$ to $V^+$ and $V^-$. A flow is **feasible** if
--   1. $\underline c(a)\le\varphi(a)\le\bar c(a)$ for all $a\in A$ (7.2);
--   2. $\partial\varphi(v)=0$ for all $v\in V\setminus(V^+\cup V^-)$ (7.3);
--   3. $(\partial\varphi)^+\in B^+$ (7.4).
--
--   The **induced set** and **induced function** are
--   $$\tilde B=\{(\partial\varphi)^-\mid\varphi\ \text{feasible}\}\subseteq\mathbb Z^{V^-},\qquad \tilde\omega(x)=\max\{\langle w,\varphi\rangle_A+\omega^+((\partial\varphi)^+)\mid \varphi\ \text{feasible},\ (\partial\varphi)^-=x\}\quad(x\in\tilde B),$$
--   with $\langle w,\varphi\rangle_A=\sum_{a\in A}w(a)\varphi(a)$.
--
--   Lemma 7.1 and Theorem 7.2 of the paper show that this construction preserves (B1) and (EXC).
--
--   **Formalization Note.** Vertices form a finite type `N`, arcs a finite type `A` with maps `tail, head : A → N`; entrances and exits are finsets `Vp, Vm` and vectors on them are functions on the subtypes. Because the capacities are finite integers, all feasible flows lie in a finite box, so `feasibleFlows` is a `Finset` and `inducedBase` is its image under $\varphi\mapsto(\partial\varphi)^-$. `inducedValue` is a real `⨆` over the finite set of feasible flows with exit boundary $x$: the paper's maximum for $x\in\tilde B$, and the junk value $0$ (empty family) off $\tilde B$, where it is never used. The exit boundary is $(\partial\varphi)^-$ itself, not its negative.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), pp. 304–305, Section 7.1, Eqs. (7.1)–(7.6)

import Mathlib

namespace SteinitzExchange.Duality.Supplement

/-! Network induction (Murota 1996, pp. 304–305, §7.1, Eqs. (7.1)–(7.6)).
The network `G = (N, A; V⁺, V⁻)` has a finite vertex type `N` and a finite arc type `A` with
tail and head maps, so parallel arcs and loops are allowed. The entrance set `V⁺` and the exit
set `V⁻` are finsets of vertices; vectors on them are functions on the subtypes `↥Vp`, `↥Vm`. -/

/-- The boundary `∂φ(v) = Σ{φ(a) | a ∈ δ⁺v} − Σ{φ(a) | a ∈ δ⁻v}` of a flow `φ : A → ℤ`
(Eq. (7.1)): out-flow minus in-flow, `δ⁺v` the arcs leaving `v`, `δ⁻v` the arcs entering `v`. -/
def boundary {N A : Type*} [Fintype A] [DecidableEq N] (tail head : A → N) (φ : A → ℤ)
    (v : N) : ℤ :=
  (∑ a ∈ Finset.univ.filter (fun a => tail a = v), φ a) -
    (∑ a ∈ Finset.univ.filter (fun a => head a = v), φ a)

/-- `(∂φ)⁺`: the restriction of `∂φ` to the entrances `V⁺`. -/
def entranceBd {N A : Type*} [Fintype A] [DecidableEq N] (tail head : A → N) (Vp : Finset N)
    (φ : A → ℤ) : Vp → ℤ :=
  fun v => boundary tail head φ v

/-- `(∂φ)⁻`: the restriction of `∂φ` to the exits `V⁻` (not negated). -/
def exitBd {N A : Type*} [Fintype A] [DecidableEq N] (tail head : A → N) (Vm : Finset N)
    (φ : A → ℤ) : Vm → ℤ :=
  fun v => boundary tail head φ v

/-- A feasible flow (Eqs. (7.2)–(7.4)): `c̲(a) ≤ φ(a) ≤ c̄(a)` for every arc,
`∂φ(v) = 0` for every vertex outside `V⁺ ∪ V⁻`, and `(∂φ)⁺ ∈ B⁺`. -/
def IsFeasibleFlow {N A : Type*} [Fintype A] [DecidableEq N] (tail head : A → N)
    (Vp Vm : Finset N) (lo up : A → ℤ) (Bp : Finset (Vp → ℤ)) (φ : A → ℤ) : Prop :=
  (∀ a, lo a ≤ φ a ∧ φ a ≤ up a) ∧
    (∀ v, v ∉ Vp → v ∉ Vm → boundary tail head φ v = 0) ∧
    entranceBd tail head Vp φ ∈ Bp

/-- The finite set of feasible flows: every feasible flow lies in the box
`∏_a [c̲(a), c̄(a)] ∩ ℤ^A`. -/
noncomputable def feasibleFlows {N A : Type*} [Fintype A] [DecidableEq N] (tail head : A → N)
    (Vp Vm : Finset N) (lo up : A → ℤ) (Bp : Finset (Vp → ℤ)) : Finset (A → ℤ) := by
  classical
  exact (Fintype.piFinset fun a => Finset.Icc (lo a) (up a)).filter
    (IsFeasibleFlow tail head Vp Vm lo up Bp)

/-- `⟨w, φ⟩_A = Σ_{a ∈ A} w(a) φ(a)`. -/
def arcWeight {A : Type*} [Fintype A] (w : A → ℝ) (φ : A → ℤ) : ℝ :=
  ∑ a, w a * (φ a : ℝ)

/-- `B̃ = {(∂φ)⁻ | φ feasible flow} ⊆ ℤ^{V⁻}` (Eq. (7.5)). -/
noncomputable def inducedBase {N A : Type*} [Fintype A] [DecidableEq N] (tail head : A → N)
    (Vp Vm : Finset N) (lo up : A → ℤ) (Bp : Finset (Vp → ℤ)) : Finset (Vm → ℤ) := by
  classical
  exact (feasibleFlows tail head Vp Vm lo up Bp).image (exitBd tail head Vm)

/-- `ω̃(x) = max{⟨w, φ⟩_A + ω⁺((∂φ)⁺) | φ feasible flow with (∂φ)⁻ = x}` for `x ∈ B̃`
(Eq. (7.6)). For `x ∈ B̃` the index family is finite and nonempty, so the real supremum is the
maximum; for `x ∉ B̃` it is empty and the value is the junk value `0`, never used. -/
noncomputable def inducedValue {N A : Type*} [Fintype A] [DecidableEq N] (tail head : A → N)
    (Vp Vm : Finset N) (lo up : A → ℤ) (w : A → ℝ) (Bp : Finset (Vp → ℤ))
    (ωp : (Vp → ℤ) → ℝ) (x : Vm → ℤ) : ℝ :=
  ⨆ φ : {φ : A → ℤ // φ ∈ feasibleFlows tail head Vp Vm lo up Bp ∧ exitBd tail head Vm φ = x},
    arcWeight w φ.1 + ωp (entranceBd tail head Vp φ.1)

end SteinitzExchange.Duality.Supplement


