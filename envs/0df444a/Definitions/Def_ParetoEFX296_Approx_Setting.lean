-- Prove2me | Definitions.Def_ParetoEFX296_Approx_Setting
-- name    : ParetoEFX296_Approx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:30.314172+00:00
-- url     : https://prove2.me/theorems/c89f23e2-671a-4fa9-8a02-0e678194e3d8
-- title:
--   Complete allocations, additive utility, approximate EFX, and integral Pareto optimality
-- statement:
--   Let $N$ be a finite set of agents and $M$ a finite set of indivisible goods. A complete allocation is an owner map $A:M\to N$; its bundle $A_i$ contains precisely the goods owned by $i$. Empty bundles are allowed. For a real table $v_i(g)$ define
--   $$v_i(S)=\sum_{g\in S}v_i(g).$$
--   For distinct agents $i,j$, the approximate EFX condition requires
--   $$v_i(A_i)\ge\alpha v_i(A_j\setminus\{g\})\quad\text{for every }g\in A_j.$$
--   An allocation $B$ Pareto dominates $A$ if every agent weakly improves and some agent strictly improves. Pareto optimality means no complete integral allocation dominates $A$.
--
--   This general vocabulary is independent of the four-agent counterexample. Nonnegativity and the range of $\alpha$ are not bundled into a predicate: the concrete theorem supplies positive values. The EFX inequality agrees with Definition 1 for $0<\alpha\le1$ and is defined for every real $\alpha$. The owner map encodes exactly a partition, with no free disposal or fractional goods.
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, pp.4–5, §2, Definitions 1–2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib

namespace ParetoEFX296.Approx

/-- A complete integral allocation: every good has exactly one owner. -/
abbrev Allocation (N M : Type) := M → N

/-- The (possibly empty) bundle of an agent. -/
def bundle {N M : Type} [Fintype M] [DecidableEq N]
    (A : Allocation N M) (i : N) : Finset M :=
  Finset.univ.filter (fun g => A g = i)

/-- Additive extension of a real table to bundles; the empty bundle has value zero. -/
noncomputable def value {N M : Type} (v : N → M → ℝ) (i : N) (S : Finset M) : ℝ :=
  ∑ g ∈ S, v i g

/-- Definition 1 (p.5), with its inequality extended to all real α.
The comparison is only between DISTINCT agents, and removes EVERY good. -/
def IsAlphaEFX {N M : Type} [Fintype M] [DecidableEq N] [DecidableEq M]
    (v : N → M → ℝ) (α : ℝ) (A : Allocation N M) : Prop :=
  ∀ i j, i ≠ j → ∀ g ∈ bundle A j,
    α * value v i ((bundle A j).erase g) ≤ value v i (bundle A i)

/-- Definition 2 (p.5): B weakly improves everyone and strictly improves someone. -/
def ParetoDominates {N M : Type} [Fintype M] [DecidableEq N]
    (v : N → M → ℝ) (B A : Allocation N M) : Prop :=
  (∀ i, value v i (bundle A i) ≤ value v i (bundle B i)) ∧
    ∃ i, value v i (bundle A i) < value v i (bundle B i)

/-- Definition 2 (p.5): all competitors are complete integral allocations. -/
def IsParetoOptimal {N M : Type} [Fintype M] [DecidableEq N]
    (v : N → M → ℝ) (A : Allocation N M) : Prop :=
  ¬ ∃ B : Allocation N M, ParetoDominates v B A

end ParetoEFX296.Approx


