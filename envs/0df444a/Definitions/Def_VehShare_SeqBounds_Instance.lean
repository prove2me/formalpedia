-- Prove2me | Definitions.Def_VehShare_SeqBounds_Instance
-- name    : VehShare_SeqBounds_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:31:12.458729+00:00
-- url     : https://prove2.me/theorems/a8b0d996-2472-436f-bc8c-3388c52d5e5f
-- title:
--   Vehicle-sharing network instance with phase-type travel times
-- statement:
--   A **vehicle-sharing network instance** consists of the following data (§2, pp. 4–5).
--
--   1. A finite set $\mathcal N$ of locations.
--   2. Demand rates $\Lambda_{ij}\ge 0$ for $i,j\in\mathcal N$ ($i=j$ allowed): customers requesting a trip from $i$ to $j$ arrive as a Poisson process of rate $\Lambda_{ij}$.
--   3. For every pair $(i,j)$, a **phase-type** travel-time law: a finite set of exponential stages $s$, entry probabilities $\beta_{ij}(s)\ge0$ with $\sum_s\beta_{ij}(s)\le 1$ (the defect $1-\sum_s\beta_{ij}(s)$ is the probability of a trip of length zero), rates $r_{ij}(s,s')\ge0$ of moving from stage $s$ to stage $s'\neq s$, and exit rates $e_{ij}(s)\ge 0$; from every stage, a stage with positive exit rate is reachable.
--   4. For every pair, the reward per trip $I_{ij}(q)$ as a function of the accepted fraction $q\in[0,1]$, with $q\mapsto q\,I_{ij}(q)$ concave on $[0,1]$.
--
--   The paper requires trip durations "with rational Laplace transform", represented "in terms of a network of stages (or phases) each exponentially distributed" (p. 4), and its state counts vehicles at each stage of the transit queues (footnote 1). Phase-type laws are exactly the laws with such a stage network.
--
--   **Formalization Note** Prices are encoded by the accepted fractions (quantiles) $q_{ij}=1-F_{ij}(p_{ij})$, as the paper does on p. 5; the valuation laws $F_{ij}$ are not modeled. No monotonicity or sign of $I_{ij}$ is assumed (the paper requires only concavity of $q I_{ij}(q)$). Data are given on all pairs; pairs with $\Lambda_{ij}=0$ enter every formula with factor $0$.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, §2, pp. 4–5, footnote 1 p. 4

import Mathlib

namespace VehShare.SeqBounds

/-- **A vehicle-sharing network instance.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), §2, pp. 4–5 (unnumbered), footnote 1 p. 4.

A finite set `L` of locations; Poisson demand rates `Λ i j ≥ 0` for trips `i → j` (`i = j`
allowed); for every pair a phase-type travel-time law given by finitely many exponential stages
`Ph i j`: entry probabilities `β i j s ≥ 0` with `∑ s, β i j s ≤ 1` (the defect `1 − ∑ s, β i j s`
is the probability of a trip of length zero), transition rates `r i j s s' ≥ 0` between distinct
stages, exit rates `e i j s ≥ 0`, and from every stage an exiting stage is reachable; and the
reward per trip `I i j : ℝ → ℝ`, a function of the accepted fraction (quantile) `q`, with
`q ↦ q · I i j q` concave on `[0, 1]` (p. 5: "we only require that `q_ij I_ij(q_ij)` be concave").

**Formalization Note.**
* Reading 1 (travel times): the paper asks for a law "with rational Laplace transform" that "can be
  represented in terms of a network of stages (or phases) each exponentially distributed" (p. 4), and
  its state counts vehicles "at each stage of the transit queue" (footnote 1). The model therefore
  exists exactly for phase-type laws; here a phase-type law is any finite absorbing continuous-time
  Markov chain (general phase type, not only Coxian), with the usual initial defect for an atom at 0.
* Data are given on all pairs, also those with `Λ i j = 0` (they enter every formula with factor 0).
* Prices are encoded by quantiles `q` (p. 5, following Banerjee et al.); the valuation laws `F_ij`
  are not modeled. No monotonicity or sign of `I` is assumed. -/
structure Instance where
  /-- the locations -/
  L : Type
  [instFintypeL : Fintype L]
  [instDecEqL : DecidableEq L]
  /-- demand rate of trips `i → j` -/
  Λ : L → L → ℝ
  Λ_nonneg : ∀ i j, 0 ≤ Λ i j
  /-- stages of the travel-time law of `i → j` -/
  Ph : L → L → Type
  [instFintypePh : ∀ i j, Fintype (Ph i j)]
  [instDecEqPh : ∀ i j, DecidableEq (Ph i j)]
  /-- entry probabilities of the stages -/
  β : ∀ i j, Ph i j → ℝ
  β_nonneg : ∀ i j s, 0 ≤ β i j s
  β_sum_le : ∀ i j, ∑ s, β i j s ≤ 1
  /-- rates between distinct stages (`r i j s s` is never used) -/
  r : ∀ i j, Ph i j → Ph i j → ℝ
  r_nonneg : ∀ i j s s', 0 ≤ r i j s s'
  /-- exit (trip completion) rates -/
  e : ∀ i j, Ph i j → ℝ
  e_nonneg : ∀ i j s, 0 ≤ e i j s
  /-- from every stage, a stage with positive exit rate is reachable -/
  absorbing : ∀ i j (s : Ph i j), ∃ s', Relation.ReflTransGen (fun a b => a ≠ b ∧ 0 < r i j a b) s s' ∧
    0 < e i j s'
  /-- reward per trip as a function of the accepted fraction -/
  I : L → L → ℝ → ℝ
  concave : ∀ i j, ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => x * I i j x)

attribute [instance] Instance.instFintypeL Instance.instDecEqL Instance.instFintypePh
  Instance.instDecEqPh

end VehShare.SeqBounds


