-- Prove2me | Definitions.Def_ParallelMatroidBasis_Main_Deletion
-- name    : ParallelMatroidBasis_Main_Deletion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:00.429643+00:00
-- url     : https://prove2.me/theorems/462b39a3-ec21-444f-a4f8-52c1ebdd7033
-- title:
--   §6 — spanning witnesses, good elements and Algorithm 3 (RecoverRedundantElements)
-- statement:
--   Let $M$ be a matroid, $S$ a finite subset of its ground set and $n$ the ambient size parameter. Put
--   $$m=\big\lceil(1-1/\log_2 n)\,|S|\big\rceil .$$
--   For $x\in S$ and an integer $g$, the **spanning witnesses** of $x$ of size $g$ are
--   $$W_g(x)=\Big\{T\in\tbinom{S-\{x\}}{g}\ :\ \mathrm{Ind}(T)=1,\ x\in\mathrm{span}(T)\Big\}.$$
--   Given values $g_x$ ($x\in S$) and a set $S'\subseteq S$, an element $x\in S$ is **good with respect to $S'$** if $x\notin S'$ and
--   $$\frac{|W_{g_x}(x)\cap\binom{S'}{g_x}|}{\binom{m}{g_x}}\ \ge\ \frac{1}{2n^{10}}$$
--   (PDF p.27).
--
--   **Algorithm 3**, $\mathrm{RecoverRedundantElements}(S,n)$ (PDF p.25): draw a uniformly random $m$-element subset $S'\subseteq S$; then, in each of $n^{21}$ independent experiments, draw a uniformly random ordering $\pi$ of $S'$, let $P_\pi$ be its longest independent prefix (possibly $\emptyset$ or $S'$), and put into $R$ every $x\in S-S'$ with $\mathrm{Ind}(P_\pi+\{x\})=0$. The output is $R$.
--
--   These objects carry the analysis of the one-round deletion procedure (Claims 6.4, 6.6, Lemmas 6.5, 6.7, Theorem 6.3).
--
--   **Formalization Note.** The span is Mathlib's matroid closure, which equals Definition 3.4's span for subsets of the ground set. The randomness of one run of Algorithm 3 is the finite type `Alg3Seed S m N` of pairs ($m$-subset $S'$ of $S$, $N$ orderings of $S'$); since every $S'$ has the same number $(m!)^N$ of order tuples, the uniform distribution on it is exactly "$S'$ uniform, then $N$ independent uniform orderings". `alg3Run M S n` is the output for $N=n^{21}$. When $\log_2 n\le 0$ the Lean value of $m$ is $|S|$ (division by $0$ is $0$); every statement assumes $n$ large.
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, §6.1–6.2, Algorithm 3 and Observation 6.1, pp.22–25 (PDF pp.24–27); definition of good elements, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_CircuitStats

noncomputable section
open Classical

namespace ParallelMatroidBasis.Main

/-! # Spanning witnesses, good elements and Algorithm 3 (RecoverRedundantElements)
(Putterman–Khanna–Song, STOC 2027 submission #589, §6, PDF pp.24–27) -/

variable {α : Type*}

/-- The subsample size `m = ⌈(1 − 1/log₂ n)|S|⌉` of Algorithm 3 (PDF p.25). -/
def mVal (n : ℕ) (S : Finset α) : ℕ :=
  ⌈(1 - 1 / Real.logb 2 n) * (S.card : ℝ)⌉₊

/-- `{T ∈ (S−{x} choose g) : Ind(T) = 1, x ∈ span(T)}` (Claim 6.4, PDF p.25). The span is
Mathlib's matroid closure, which equals Definition 3.4's span on subsets of the ground set. -/
def witnesses (M : Matroid α) (S : Finset α) (x : α) (g : ℕ) : Finset (Finset α) :=
  ((S.erase x).powersetCard g).filter
    (fun T => M.Indep (↑T : Set α) ∧ x ∈ M.closure (↑T : Set α))

/-- PDF p.27: `x ∈ S` is good with respect to `S'` (for the choice of values `g`) if `x ∉ S'` and
`|witnesses(x, g_x) ∩ (S' choose g_x)| / (m choose g_x) ≥ 1/(2n^{10})`, `m = ⌈(1 − 1/log n)|S|⌉`. -/
def IsGood (M : Matroid α) (S : Finset α) (n : ℕ) (g : α → ℕ) (S' : Finset α) (x : α) : Prop :=
  x ∈ S ∧ x ∉ S' ∧
    (1 : ℝ) / (2 * (n : ℝ) ^ 10) ≤
      ((witnesses M S x (g x) ∩ S'.powersetCard (g x)).card : ℝ) / ((mVal n S).choose (g x) : ℝ)

/-- Algorithm 3, line 8: the longest independent prefix `P_π` of an ordering `π` of `S'`
(possibly `∅` or `S'`). -/
def longestIndepPrefix (M : Matroid α) (S' : Finset α) (π : Ordering S') : Finset α :=
  prefixSet S' π (Nat.findGreatest (fun j => M.Indep (↑(prefixSet S' π j) : Set α)) S'.card)

/-- Algorithm 3, lines 9–13, for one ordering `π`: the elements `x ∈ S − S'` with
`Ind(P_π + {x}) = 0`. -/
def caught (M : Matroid α) (S S' : Finset α) (π : Ordering S') : Finset α :=
  (S \ S').filter (fun x => ¬ M.Indep (↑(insert x (longestIndepPrefix M S' π)) : Set α))

/-- The output `R` of Algorithm 3 once `S'` and the `N` orderings `π_1, …, π_N` of `S'` are drawn:
the union over the experiments of the caught elements. -/
def alg3Output (M : Matroid α) (S S' : Finset α) (N : ℕ) (πs : Fin N → Ordering S') :
    Finset α :=
  Finset.univ.biUnion (fun l => caught M S S' (πs l))

/-- The random seed of one run of Algorithm 3 on `S` with subsample size `m` and `N`
experiments: an `m`-element subset `S' ⊆ S` and `N` orderings of `S'`. Every `S'` has the same
number `(m!)^N` of order tuples, so the uniform distribution on this finite type is exactly
"`S'` uniform among the `m`-subsets of `S`, then `N` independent uniform orderings of `S'`". -/
abbrev Alg3Seed (S : Finset α) (m N : ℕ) :=
  Σ S' : {S' : Finset α // S' ∈ S.powersetCard m}, (Fin N → Ordering S'.1)

/-- Algorithm 3, `RecoverRedundantElements(S, n)` (PDF p.25): `m = ⌈(1 − 1/log₂ n)|S|⌉` and
`N = n^{21}` experiments; the output `R` for a given seed. -/
def alg3Run (M : Matroid α) (S : Finset α) (n : ℕ) (ω : Alg3Seed S (mVal n S) (n ^ 21)) :
    Finset α :=
  alg3Output M S ω.1.1 (n ^ 21) ω.2

end ParallelMatroidBasis.Main


