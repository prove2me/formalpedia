-- Prove2me | Definitions.Def_AvgCostLP_Assumption21
-- name    : AvgCostLP_Assumption21
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:30:18.603125+00:00
-- url     : https://prove2.me/theorems/6085334b-61dd-4545-80f0-65643e4850f9
-- title:
--   Assumption 2.1 — (G), strictly unbounded costs (SU) and majorization (M)
-- statement:
--   **Assumption 2.1.**
--
--   1. **(G)** For some $\pi\in\Pi$ and $\zeta\in\mathcal P(\mathbb X)$, $J(\pi,\zeta)<\infty$.
--   2. **(SU)** There is a nondecreasing sequence of compact sets $\Gamma_j\uparrow\Gamma$ such that
--   $$\lim_{j\to\infty}\ \inf_{(x,a)\in\Gamma_j^c}c(x,a)=+\infty .$$
--   3. **(M)** For each compact set $K\in\{\mathrm{proj}_{\mathbb X}(\Gamma_j)\}$ there are an open set $O\supset K$, a closed set $D\subset\mathbb X$ (possibly empty) and a finite measure $\nu$ on $\mathcal B(\mathbb X)$ such that
--   $$q\big((O\setminus D)\cap B\mid x,a\big)\le\nu(B)\qquad\forall B\in\mathcal B(\mathbb X),\ (x,a)\in\Gamma, \tag{2.1}$$
--   and, for each action $a$, $q(dy\mid\cdot,a)$ is continuous and $c(\cdot,a)$ is lower semicontinuous on $D$.
--
--   The sequence $\Gamma_j$ in (M) is the one of (SU). The auxiliary predicates `IsSUSeq` (for (SU)) and `IsMajorizing` (for (M) at one compact set) are reused by the proof milestones.
--
--   **Formalization Note** The infimum in (SU) is taken in $[0,+\infty]$ over the complement in $\mathbb X\times\mathbb A$ (equal to the one over $\Gamma\setminus\Gamma_j$ since $c=+\infty$ off $\Gamma$); $j$ ranges over $\mathbb N$. Continuity of $x\mapsto q(\cdot\mid x,a)$ into $\mathcal P(\mathbb X)$ with the weak topology is written as continuity of $x\mapsto\int f(y)\,q(dy\mid x,a)$ on $D$ for every bounded continuous $f$.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, Assumption 2.1 and footnote 2, p.6

import Mathlib
import Definitions.Def_AvgCostLP_avgCost

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace AvgCostLP

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [TopologicalSpace X] [TopologicalSpace A]

/-- Yu, arXiv:1905.12095v3, Assumption 2.1(SU), p.6: `Γs = (Γ_j)` is a nondecreasing sequence of
compact sets with `Γ_j ↑ Γ` (so `Γ_j ⊂ Γ` and `⋃_j Γ_j = Γ`) such that
`lim_{j→∞} inf_{(x,a) ∈ Γ_jᶜ} c(x, a) = +∞`.

**Formalization Note** The sequence is indexed by `ℕ` (the paper's `j ∈ ℤ₊`, shifted). The
infimum is taken in `[0, +∞]` over the complement of `Γ_j` in `X × A` (the infimum of the empty
set is `+∞`); since `c = +∞` off `Γ`, the complement in `Γ` gives the same value. -/
def IsSUSeq (M : Model X A) (Γs : ℕ → Set (X × A)) : Prop :=
  Monotone Γs ∧ (∀ j, IsCompact (Γs j)) ∧ (⋃ j, Γs j) = M.graph ∧
    Tendsto (fun j => ⨅ p ∈ (Γs j)ᶜ, M.c p) atTop (𝓝 ⊤)

/-- Yu, arXiv:1905.12095v3, Assumption 2.1(M), p.6, for one compact set `K`: `O ⊃ K` is open,
`D ⊂ X` is closed (possibly empty), `ν` is a finite measure on `B(X)`, and

* (2.1) `q((O \ D) ∩ B | x, a) ≤ ν(B)` for all `B ∈ B(X)` and `(x, a) ∈ Γ`;
* restricted to `D × A`, `q(dy | x, a)` is continuous and `c(x, a)` is lower semicontinuous; by
  footnote 2 (`A` discrete) this means that for each action `a`, `q(dy | ·, a)` is continuous and
  `c(·, a)` is lower semicontinuous on `D`.

**Formalization Note** Continuity of `x ↦ q(· | x, a)` on `D` into `P(X)` with the topology of
weak convergence is written as continuity on `D` of `x ↦ ∫ f(y) q(dy | x, a)` for every bounded
continuous `f : X → ℝ` (the weak topology is the coarsest making these maps continuous). -/
def IsMajorizing (M : Model X A) (K O D : Set X) (ν : Measure X) : Prop :=
  IsOpen O ∧ K ⊆ O ∧ IsClosed D ∧ IsFiniteMeasure ν ∧
    (∀ B : Set X, MeasurableSet B → ∀ p ∈ M.graph, M.q p ((O \ D) ∩ B) ≤ ν B) ∧
    (∀ (a : A) (f : X →ᵇ ℝ), ContinuousOn (fun x => ∫ y, f y ∂(M.q (x, a))) D) ∧
    (∀ a : A, LowerSemicontinuousOn (fun x => M.c (x, a)) D)

/-- Yu, arXiv:1905.12095v3, Assumption 2.1, p.6:

* (G) for some `π ∈ Π` and `ζ ∈ P(X)`, the average cost `J(π, ζ) < ∞`;
* (SU) there is a nondecreasing sequence of compact sets `Γ_j ↑ Γ` with
  `lim_j inf_{Γ_jᶜ} c = +∞`;
* (M) for each compact set `K ∈ {proj_X(Γ_j)}` (for the same sequence `Γ_j`) there are an open
  `O ⊃ K`, a closed `D ⊂ X` and a finite measure `ν` with the majorization (2.1) and the
  continuity / lower semicontinuity of the model on `D`. -/
def Assumption21 (M : Model X A) : Prop :=
  (∃ (π : Policy M) (ζ : ProbabilityMeasure X), avgCost M π ζ < ⊤) ∧
    ∃ Γs : ℕ → Set (X × A), IsSUSeq M Γs ∧
      ∀ j, ∃ (O D : Set X) (ν : Measure X), IsMajorizing M (Prod.fst '' Γs j) O D ν

end AvgCostLP


