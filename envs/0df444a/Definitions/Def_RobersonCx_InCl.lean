-- Prove2me | Definitions.Def_RobersonCx_InCl
-- name    : RobersonCx_InCl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:31.915328+00:00
-- url     : https://prove2.me/theorems/96c39d98-8717-424b-bb06-2a905078ad88
-- title:
--   Homomorphism counts $\hom(F,X)$, graph classes, $X\equiv_{\mathcal F}Y$ and the homomorphism distinguishing closure $\mathrm{Cl}(\mathcal F)$
-- statement:
--   All graphs are finite, simple and loopless. For graphs $F$ and $X$, a **homomorphism** from $F$ to $X$ is a map $\varphi:V(F)\to V(X)$ such that $\varphi(u)\varphi(v)\in E(X)$ whenever $uv\in E(F)$; $\hom(F,X)$ is the number of homomorphisms.
--
--   A **graph class** $\mathcal F$ is a collection of finite graphs. Two graphs $X,Y$ are **homomorphism indistinguishable over $\mathcal F$**, written $X\equiv_{\mathcal F}Y$, if
--   $$\hom(F,X)=\hom(F,Y)\quad\text{for every }F\in\mathcal F.$$
--
--   The **homomorphism distinguishing closure** $\mathrm{Cl}(\mathcal F)$ (Roberson; Definition 1) consists of all graphs $H$ such that
--   $$X\equiv_{\mathcal F}Y\ \Longrightarrow\ \hom(H,X)=\hom(H,Y)\qquad\text{for all graphs }X,Y.$$
--   $\mathcal F$ is **homomorphism distinguishing closed** (h.d.-closed) if $\mathrm{Cl}(\mathcal F)=\mathcal F$.
--
--   $\mathrm{Cl}(\mathcal F)$ is the largest class with the same indistinguishability relation as $\mathcal F$; the Strong Roberson Conjecture asserted that every class closed under minors and disjoint unions is h.d.-closed.
--
--   **Formalization Note** $\hom(F,X)$ is `Nat.card (F →g X)`. A graph class is a predicate on simple graphs on finite types in `Type` (`GraphClass`); the paper's classes are isomorphism-closed, which is not built in. In `InCl` the target graphs $X,Y$ and in `HomIndist` the source graphs $F$ range over all simple graphs on finite types in `Type`, the graph on the empty type included. `IsHDClosed` compares $\mathrm{Cl}(\mathcal F)$ and $\mathcal F$ on all finite graphs.
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §1 p.1 (PDF p.3), Definition 1; §2.1 p.5 (PDF p.7)

import Mathlib

set_option autoImplicit false

namespace RobersonCx

/-- `homCount F X = hom(F, X)`, the number of homomorphisms from `F` to `X`: maps
`φ : V(F) → V(X)` with `φ(u)φ(v) ∈ E(X)` whenever `uv ∈ E(F)` (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §2.1, p.5 (PDF p.7)).

**Formalization Note** `hom(F, X)` is `Nat.card (F →g X)` (Mathlib's graph homomorphisms are exactly the
adjacency-preserving vertex maps). Every statement of the mission applies it to graphs on finite types only;
on an infinite type `Nat.card` would return the junk value `0`. -/
noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (X : SimpleGraph W) : ℕ :=
  Nat.card (F →g X)

/-- A graph class: a predicate on finite simple graphs (p.5: "All graphs considered are finite and
undirected. Unless otherwise stated, they are simple and loopless.").

**Formalization Note** A class is a predicate on simple graphs on finite types in `Type`. The paper's classes
are closed under isomorphism; this is not built in, so a statement proved for every `GraphClass` applies in
particular to every isomorphism-closed class. -/
abbrev GraphClass : Type 1 := ∀ (V : Type) [Finite V], SimpleGraph V → Prop

/-- `HomIndist 𝓕 X Y`, the homomorphism indistinguishability relation `X ≡_𝓕 Y`:
`hom(F, X) = hom(F, Y)` for every `F ∈ 𝓕` (§1, p.1 (PDF p.3)). -/
def HomIndist (𝓕 : GraphClass) {X Y : Type} (GX : SimpleGraph X) (GY : SimpleGraph Y) : Prop :=
  ∀ (V : Type) [Finite V] (F : SimpleGraph V), 𝓕 V F → homCount F GX = homCount F GY

/-- `InCl 𝓕 H`: the graph `H` lies in the homomorphism distinguishing closure `Cl(𝓕)`
(Definition 1, p.1 (PDF p.3)): for all graphs `X, Y`, `X ≡_𝓕 Y` implies `hom(H, X) = hom(H, Y)`.

**Formalization Note** The targets `X, Y` range over every simple graph on a finite type in `Type`, the graph
on the empty type included; every finite graph is isomorphic to one of these, and hom counts are invariant under
isomorphism, so this is the paper's "for all graphs X, Y". -/
def InCl (𝓕 : GraphClass) {W : Type} (H : SimpleGraph W) : Prop :=
  ∀ (X Y : Type) [Finite X] [Finite Y] (GX : SimpleGraph X) (GY : SimpleGraph Y),
    HomIndist 𝓕 GX GY → homCount H GX = homCount H GY

/-- `𝓕` is homomorphism distinguishing closed (h.d.-closed), `Cl(𝓕) = 𝓕` (Definition 1, p.1 (PDF p.3)):
a finite graph lies in `Cl(𝓕)` exactly when it lies in `𝓕`. -/
def IsHDClosed (𝓕 : GraphClass) : Prop :=
  ∀ (W : Type) [Finite W] (H : SimpleGraph W), InCl 𝓕 H ↔ 𝓕 W H

end RobersonCx


