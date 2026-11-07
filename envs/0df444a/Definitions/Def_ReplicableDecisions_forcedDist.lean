-- Prove2me | Definitions.Def_ReplicableDecisions_forcedDist
-- name    : ReplicableDecisions_forcedDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:16.531048+00:00
-- url     : https://prove2.me/theorems/94e2a201-7d28-468d-93c2-5be47d60a4e4
-- title:
--   Forced classes $A_i$, $\mathrm{dist}_G(A_0,A_1)$ and breadth-first layers
-- statement:
--   For outputs $\{0,1\}$ the **forced classes** are $A_i=\{P:\Gamma(P)=\{i\}\}$; the remaining models are indifference models. For a graph $G$ on the models, $\mathrm{dist}_G(A_0,A_1)$ is the number of edges in a shortest path between the classes, with value $+\infty$ if a class is empty or no such path exists. The breadth-first layer of a model is $d(P)=\mathrm{dist}_G(A_0,P)$, which is $\infty$ on components not meeting $A_0$.
--
--   These integers are what the exact selector values of Theorem 3.2 depend on, and $d$ is the statistic of the rule in Theorem 3.1.
--
--   **Formalization Note** Distances are `SimpleGraph.edist`, with values in $\mathbb N\cup\{\infty\}$, and an empty infimum is $\infty$. `forcedClass` and `forcedDist` take any output type, so Proposition 3.4 can name two outputs of an abstract two-element type.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), §2 "Binary decisions", p.9 (PDF p.11); proof of Theorem 3.2, p.11 (PDF p.13)

import Mathlib

namespace ReplicableDecisions

/-- **Forced classes.** Chen, *Replicable Decisions in Finite Experiments*, STOC 2027 submission
(sha256 52d181db…), §2 "Binary decisions", p.9 (PDF p.11): `A_i = {P : Γ(P) = {i}}`.

**Formalization Note.** With `Y = Bool`, the page's `0` is `false` and `1` is `true`; the definition
is stated for any output type. -/
def forcedClass {ι : Type*} {Y : Type*} (Γ : ι → Set Y) (y : Y) : Set ι :=
  {i | Γ i = {y}}

/-- **Graph distance between forced classes,** `dist_G(A_{y₀}, A_{y₁})`. Chen, STOC 2027 submission
(sha256 52d181db…), §2, p.9 (PDF p.11): "the number of edges in a shortest path between the classes,
with value +∞ if a class is empty or no such path exists."

**Formalization Note.** `SimpleGraph.edist` is `ℕ∞`-valued and `⊤` on disconnected pairs; an empty
infimum is `⊤`. -/
noncomputable def forcedDist {ι : Type*} {Y : Type*} (G : SimpleGraph ι) (Γ : ι → Set Y)
    (y₀ y₁ : Y) : ℕ∞ :=
  ⨅ a ∈ forcedClass Γ y₀, ⨅ b ∈ forcedClass Γ y₁, G.edist a b

/-- **Breadth-first layer** `d(P) = dist_G(A₀, P)`. Chen, STOC 2027 submission (sha256 52d181db…),
proof of Theorem 3.2, p.11 (PDF p.13): "using d(P) = ∞ in components not meeting A0". -/
noncomputable def layerDist {ι : Type*} (G : SimpleGraph ι) (Γ : ι → Set Bool) (i : ι) : ℕ∞ :=
  ⨅ a ∈ forcedClass Γ false, G.edist a i

end ReplicableDecisions


