-- Prove2me | Definitions.Def_ProjSchedTW_Complexity_DelayingAlternatives
-- name    : ProjSchedTW_Complexity_DelayingAlternatives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T01:53:02.011364+00:00
-- url     : https://prove2.me/theorems/9467f84d-5d90-4765-9d69-3ace5060c2a9
-- title:
--   Forbidden sets, minimal delaying alternatives, and the decision problem of Proposition 2.5.4
-- statement:
--   This file defines minimal delaying alternatives (Definition 2.5.1 of Neumann, Schwindt and Zimmermann) and the decision problem of Proposition 2.5.4.
--
--   **Resources.** Activities are $V=\{0,1,\dots,n+1\}$, renewable resources $\mathcal R=\{1,\dots,m\}$; activity $i$ uses $r_{ik}\in\mathbb N$ units of resource $k$, whose capacity is $R_k\in\mathbb N$.
--
--   **Forbidden and feasible sets** (Definition 2.3.9). $F\subseteq V$ is forbidden if $\sum_{i\in F}r_{ik}>R_k$ for some $k$, and feasible otherwise.
--
--   **Delaying alternatives** (Definition 2.5.1). For a set $F$, a set $B\subseteq F$ is a delaying alternative for $F$ if $F\setminus B$ is a feasible set; it is a minimal delaying alternative if moreover no proper subset $B'\subsetneq B$ is a delaying alternative for $F$.
--
--   **The decision problem.** An instance consists of resource data $(n,m,r,R)$, a set $F$ and an activity $j^*$. It is well formed if $n\ge1$, $r_{0k}=r_{n+1,k}=0$, $r_{ik}\le R_k$ for all $i,k$ (§2.1), $F$ is forbidden and $j^*\in F$. It is a yes-instance if
--   $$\exists B:\ B\text{ is a minimal delaying alternative for }F\ \text{and}\ j^*\in B.$$
--   Instances are coded in binary as $n,m$, the $r_{ik}$, the $R_k$, the indicator of $F$ over $V$, and $j^*$; the language consists of the codes of well-formed yes-instances.
--
--   Proposition 2.5.4 says this language is NP-complete.
--
--   **Formalization Note** Activities are `Fin (n + 2)`, resources `Fin m`. The durations and the project network are not part of the instance, because the question does not depend on them. Proper subsets are `⊂` on `Finset`.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 24 (§2.1, resource data), p. 34 (Definition 2.3.9, Eq. (2.3.1)), p. 46 (Definition 2.5.1), p. 48 (Proposition 2.5.4)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace ProjSchedTW.Complexity

open CookPvsNP

/-! # Forbidden sets and minimal delaying alternatives (Definitions 2.3.9 and 2.5.1)

Activities are `V = Fin (n + 2)`, renewable resources `ℛ = Fin m`; `r i k ∈ ℕ` is the amount
of resource `k` used by activity `i`, and `R k ∈ ℕ` the capacity of resource `k` (§2.1). -/

section

variable {n m : ℕ}

/-- A forbidden set (Definition 2.3.9, Eq. (2.3.1), p. 34): `∑_{i ∈ F} r_ik > R_k` for some
resource `k`. -/
def IsForbiddenSet (r : Fin (n + 2) → Fin m → ℕ) (R : Fin m → ℕ) (F : Finset (Fin (n + 2))) :
    Prop :=
  ∃ k, R k < ∑ i ∈ F, r i k

/-- A feasible set (Definition 2.3.9, p. 34): a set of activities that is not forbidden,
`∑_{i ∈ A} r_ik ≤ R_k` for every resource `k`. -/
def IsFeasibleSet (r : Fin (n + 2) → Fin m → ℕ) (R : Fin m → ℕ) (A : Finset (Fin (n + 2))) :
    Prop :=
  ¬ IsForbiddenSet r R A

/-- A delaying alternative for `F` (Definition 2.5.1, p. 46): `B ⊆ F` such that `F \ B` is a
feasible set. -/
def IsDelayingAlternative (r : Fin (n + 2) → Fin m → ℕ) (R : Fin m → ℕ)
    (F B : Finset (Fin (n + 2))) : Prop :=
  B ⊆ F ∧ IsFeasibleSet r R (F \ B)

/-- A minimal delaying alternative for `F` (Definition 2.5.1, p. 46): a delaying alternative no
proper subset of which is a delaying alternative for `F`. -/
def IsMinimalDelayingAlternative (r : Fin (n + 2) → Fin m → ℕ) (R : Fin m → ℕ)
    (F B : Finset (Fin (n + 2))) : Prop :=
  IsDelayingAlternative r R F B ∧ ∀ B' ⊂ B, ¬ IsDelayingAlternative r R F B'

end

/-- An instance of the decision problem of Proposition 2.5.4: the resource data of a project
(`n` real activities, `m` renewable resources, requirements `r`, capacities `R`), a set `F` of
activities and an activity `jstar`. The question is whether some minimal delaying alternative
for `F` contains `jstar`. -/
structure DAInstance where
  n : ℕ
  m : ℕ
  r : Fin (n + 2) → Fin m → ℕ
  R : Fin m → ℕ
  F : Finset (Fin (n + 2))
  jstar : Fin (n + 2)

namespace DAInstance

/-- The standing assumptions and the hypotheses of the question: `n ≥ 1` (§1.1);
`r_0k = r_{n+1,k} = 0` and `r_ik ≤ R_k` (§2.1, p. 24); `F` is a forbidden set and `j* ∈ F`. -/
def WellFormed (x : DAInstance) : Prop :=
  1 ≤ x.n ∧ (∀ k, x.r 0 k = 0 ∧ x.r (Fin.last (x.n + 1)) k = 0) ∧ (∀ i k, x.r i k ≤ x.R k) ∧
    IsForbiddenSet x.r x.R x.F ∧ x.jstar ∈ x.F

/-- The yes-instances: some minimal delaying alternative `B` for `F` contains `j*`. -/
def Yes (x : DAInstance) : Prop :=
  ∃ B, IsMinimalDelayingAlternative x.r x.R x.F B ∧ x.jstar ∈ B

/-- The numbers describing an instance, in order: `n`, `m`; the requirements `r_ik` (row by
row); the capacities `R_k`; the indicator of `F` (`1` if `i ∈ F`, else `0`, for `i ∈ V`); `j*`. -/
def code (x : DAInstance) : List ℕ :=
  [x.n, x.m] ++ (List.ofFn fun i => List.ofFn fun k => x.r i k).flatten ++ List.ofFn x.R ++
    List.ofFn (fun i => if i ∈ x.F then 1 else 0) ++ [x.jstar.val]

end DAInstance

/-- The language of Proposition 2.5.4: binary codes of the well-formed yes-instances. -/
def minDelayAltLang : Lang BSym :=
  { w | ∃ x : DAInstance, x.WellFormed ∧ x.Yes ∧ w = encNats x.code }

end ProjSchedTW.Complexity


