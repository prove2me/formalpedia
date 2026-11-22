-- Prove2me | Definitions.Def_SelfSelReg_Supplement_RecoveredList
-- name    : SelfSelReg_Supplement_RecoveredList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:13:45.264982+00:00
-- url     : https://prove2.me/theorems/12cfc7fb-2995-46d9-bc19-fecdf51895e3
-- title:
--   Recovered list $\widehat{\mathcal R}$ matched to $R\subsetneq[k]$, and the remaining set $Q=[k]\setminus R$
-- statement:
--   The algorithms of Sections 6–8 work with a list $\widehat{\mathcal R}$ of regressor estimates obtained so far, together with a bijection $\mathrm{match}:\widehat{\mathcal R}\to R$ onto a proper subset $R\subsetneq[k]$ of the regressor indices. The indices still to be recovered are $Q=[k]\setminus R$.
--
--   A recovered list for $k$ regressors in $\mathbb R^n$ consists of a number $m<k$ of estimates $\widehat w_1,\dots,\widehat w_m\in\mathbb R^n$ and an injective map $j\mapsto \mathrm{match}(\widehat w_j)\in[k]$. Its image is $R$, and $Q=[k]\setminus R$ has $k-m\ge1$ elements. The list is $\eta$-accurate for regressors $w_1,\dots,w_k$ when
--
--   $$
--   \|\widehat w-w_{\mathrm{match}(\widehat w)}\|_2\le\eta\qquad(\widehat w\in\widehat{\mathcal R}).
--   $$
--
--   Every theorem of the supplement that takes a recovered list assumes this with $\eta=e^{-K^6s}$.
--
--   **Formalization Note** The estimates are indexed by position, so an algorithm receives them in an order that says nothing about the matching; the matching occurs only in hypotheses. The bundle also fixes how the list is written into a program's input (estimate after estimate, coordinate by coordinate, without the matched indices).
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Section 6, p.28 (PDF p.31); Theorems 6.1, 6.3, 8.1, pp.28–30, 55 (PDF pp.31–33, 58)

import Mathlib

namespace SelfSelReg

namespace Supplement

/-- **A recovered list matched to a proper subset of `[k]`** (§6 and §8).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), §6, p.28 (PDF p.31): "given a set R̂ ⊆ ℝⁿ of recovered regressors, with
a bijection match : R̂ → R ⊊ [k], we will recover unit vectors parallel to some subset of the remaining
regressors w_i, i ∈ Q := [k] ∖ R."

`size` is `|R̂|`, `est j` is the `j`-th estimate and `idx j = match(est j)` is the index of the regressor
it is matched to. `idx` is injective (the matching is a bijection onto its image `R`) and `size < k`
(`R ⊊ [k]`).

**Formalization Note.** The list is indexed by `Fin size`, so an algorithm receives the estimates in an
order that carries no information about `idx`; the matching is part of the hypothesis, never of the
input (`data`). Two positions may hold equal vectors; under the accuracy hypothesis used by every
theorem the estimates of distinct regressors are distinct, so this adds no instance. -/
structure RecoveredList (n k : ℕ) where
  size : ℕ
  est : Fin size → EuclideanSpace ℝ (Fin n)
  idx : Fin size → Fin k
  idx_injective : Function.Injective idx
  proper : size < k

/-- The recovered index set `R = match(R̂)`. -/
def RecoveredList.recovered {n k : ℕ} (Rhat : RecoveredList n k) : Finset (Fin k) :=
  Finset.univ.image Rhat.idx

/-- The remaining index set `Q = [k] ∖ R`. It has `k − |R̂| ≥ 1` elements. -/
def RecoveredList.remaining {n k : ℕ} (Rhat : RecoveredList n k) : Finset (Fin k) :=
  Finset.univ \ Rhat.recovered

/-- `‖ŵ − w_match(ŵ)‖₂ ≤ η` for every `ŵ ∈ R̂` (Theorems 6.1, 6.3, 8.1). -/
def RecoveredList.Accurate {n k : ℕ} (Rhat : RecoveredList n k)
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (η : ℝ) : Prop :=
  ∀ j, ‖Rhat.est j - w (Rhat.idx j)‖ ≤ η

/-- The estimates written as one list of reals, estimate after estimate, each as its `n` coordinates.
The matched indices are not part of it. -/
noncomputable def RecoveredList.data {n k : ℕ} (Rhat : RecoveredList n k) : List ℝ :=
  (List.ofFn fun j => List.ofFn fun c => Rhat.est j c).flatten

end Supplement

end SelfSelReg


