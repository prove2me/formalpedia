-- Prove2me | Definitions.Def_LocalLLL_Main_VariableInstance
-- name    : LocalLLL_Main_VariableInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:31.024748+00:00
-- url     : https://prove2.me/theorems/02934db9-4392-4878-8c51-32c1553fd28b
-- title:
--   Variable LLL instances and consistent distributed solutions
-- statement:
--   Let $\iota$ index arbitrary measurable variable spaces $\alpha_z$ with probability laws $\mu_z$, and let $V$ be the finite event set. An instance consists of a graph $G$, coordinate sets $V_v\subseteq\iota$, and measurable bad events $A_v\subseteq\prod_z\alpha_z$ determined by $V_v$. Shared variables imply adjacency for distinct events; extra edges are permitted. The maximum degree is at most $d$, and each product-law event probability is at most $p$:
--
--   $$\Pr_{\bigotimes_z\mu_z}[A_v]\le p.$$
--
--   A distributed output solves the instance if there is a common full assignment $x$ such that every local output agrees with $x$ on its own coordinates and $x$ avoids every bad event. The uniform success predicate quantifies over every graph, identifier map, coordinate set and event family after fixing the program and its round budget, and bounds the outer measure of failure by $n^{-a}$. It includes empty event sets and makes no finiteness or regularity assumption on the variable spaces.
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §1 LLL problem, p. 1 (PDF 2); §2 LLL notations, p. 2 (PDF 3); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_LocalLLL_Main_LocalAlgorithm

noncomputable section

namespace LocalLLL.Main

open MeasureTheory

abbrev Assignment {ι : Type} (α : ι → Type) := (z : ι) → α z
abbrev LLLInput (ι : Type) (α : ι → Type) := Set ι × Set (Assignment α)

/-- Product law, with probability hypotheses supplied by the statements using it. -/
def probability {ι : Type} {α : ι → Type} [∀ z, MeasurableSpace (α z)]
    (μ : ∀ z, Measure (α z)) (E : Set (Assignment α)) : ℝ :=
  (Measure.infinitePi μ E).toReal

/-- Edges need only contain all shared-variable pairs; extra edges are allowed. -/
def variableInstance {ι V : Type} [Fintype V] {α : ι → Type}
    [∀ z, MeasurableSpace (α z)] (μ : ∀ z, Measure (α z))
    (G : SimpleGraph V) (vars : V → Set ι) (events : V → Set (Assignment α))
    (d : ℕ) (p : ℝ) : Prop :=
  (∀ v, MeasurableSet (events v)) ∧
  (∀ v, DependsOn (fun x => x ∈ events v) (vars v)) ∧
  (∀ u v, u ≠ v → (vars u ∩ vars v).Nonempty → G.Adj u v) ∧
  (∀ v, degree G v ≤ d) ∧ (∀ v, probability μ (events v) ≤ p)

/-- Local outputs agree on every relevant coordinate with one common, satisfying assignment. -/
def Solved {ι V : Type} {α : ι → Type} (vars : V → Set ι)
    (events : V → Set (Assignment α)) (out : V → Assignment α) : Prop :=
  ∃ x : Assignment α, (∀ v z, z ∈ vars v → out v z = x z) ∧ ∀ v, x ∉ events v

def labels {ι V : Type} {α : ι → Type} (vars : V → Set ι)
    (events : V → Set (Assignment α)) : V → LLLInput ι α := fun v => (vars v, events v)

/-- The guarantee is an outer-measure upper bound on failure, without a measurability
assumption on local computation. The algorithm is universally fixed before this predicate is used. -/
def solvesWithin {ι : Type} {α : ι → Type} [∀ z, MeasurableSpace (α z)]
    (μ : ∀ z, Measure (α z)) (n d : ℕ) (p a : ℝ)
    (alg : LocalAlg (LLLInput ι α) (Assignment α)) (T : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ)
    (vars : V → Set ι) (events : V → Set (Assignment α)),
    Function.Injective id → Fintype.card V ≤ n → variableInstance μ G vars events d p →
    tapes V {ω | ¬ Solved vars events (run alg T G id (labels vars events) ω)} ≤
      ENNReal.ofReal ((n : ℝ) ^ (-a))
end LocalLLL.Main


