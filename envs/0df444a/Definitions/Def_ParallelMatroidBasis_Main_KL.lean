-- Prove2me | Definitions.Def_ParallelMatroidBasis_Main_KL
-- name    : ParallelMatroidBasis_Main_KL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:44.859505+00:00
-- url     : https://prove2.me/theorems/a8f78666-4e42-491b-97f8-17e91427c3cb
-- title:
--   Definitions 3.9–3.13 — KL divergence in bits, Bernoulli laws, uniform $U_i$, up and down operators
-- statement:
--   All logarithms are to base $2$ (PDF p.12). For two distributions $\mu,\nu$ on a set $\mathcal X$ the **KL divergence** is
--   $$d_{KL}(\mu\|\nu)=\sum_{x\in\mathcal X}\mu(x)\log_2\frac{\mu(x)}{\nu(x)},$$
--   with the value $+\infty$ when $\mu$ charges a point that $\nu$ does not. For $a\in[0,1]$ the Bernoulli law with success probability $a$ is the law on $\{\mathrm{true},\mathrm{false}\}$ giving mass $a$ to $\mathrm{true}$.
--
--   Fix $n$ and write $[n]=\{0,\dots,n-1\}$. For $0\le i\le n$, $U_i$ is the uniform distribution on $\binom{[n]}{i}$, the $i$-element subsets of $[n]$. A distribution $\mu$ is a distribution over $\binom{[n]}{k}$ when it gives mass only to $k$-element sets.
--
--   For $k<n$ the **up operator** maps a distribution $\mu$ over $\binom{[n]}{k}$ to the distribution over $\binom{[n]}{k+1}$
--   $$U_{k\to k+1}(\mu)(S)=\sum_{T\subseteq S,\ |T|=k}\frac{\mu(T)}{n-k},$$
--   obtained by replacing each $T$ with a uniformly random $(k+1)$-element superset of $T$. For $0<k\le n$ the **down operator** is
--   $$D_{k\to k-1}(\mu)(S)=\sum_{T\supseteq S,\ |T|=k}\frac{\mu(T)}{k},$$
--   obtained by replacing each $T$ with a uniformly random $(k-1)$-element subset of $T$. $U_{k\to k+j}$ and $D_{k\to k-j}$ denote $j$ consecutive applications.
--
--   These are the objects of the KL-contraction estimates (Lemma 3.14, Corollaries 3.15, 3.16), the change-of-measure inequality (Fact 3.17) and the Bernoulli bound (Fact 3.18), which together give the density-preservation theorem (Theorem 4.1).
--
--   **Formalization Note.** `klBits μ ν` is Mathlib's `InformationTheory.klDiv` (natural logarithm, value `∞` without absolute continuity or integrability) divided by $\ln 2$, for measures on any measurable space; on a finite type with the discrete σ-algebra (such as `Finset (Fin n)`) it is the displayed sum. Distributions over sets are `PMF (Finset (Fin n))`, and "over $\binom{[n]}{k}$" is the support condition `IsDistOn n k μ`. The up and down steps are defined on every distribution of `Finset (Fin n)`: a set with no $(|T|+1)$-superset ($T=[n]$) is kept by the up step and the empty set is kept by the down step; neither case occurs within the stated ranges. `uniformK n i` is the point mass at $\emptyset$ when $i>n$, a case no statement uses.
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Definitions 3.9, 3.10, 3.11, Remark 3.12, Definition 3.13, pp.11–12 (PDF pp.13–14); Fact 3.18, p.13 (PDF p.15)

import Mathlib

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main

/-! # KL divergence in bits, Bernoulli laws, and the up/down operators on `k`-subsets
(Putterman–Khanna–Song, STOC 2027 submission #589, §3.2–3.3, Definitions 3.9–3.13, PDF pp.13–15) -/

/-- Definition 3.9 (PDF p.13), with the paper's base-2 logarithm ("All logarithms are to base 2",
PDF p.12): `d_KL(μ‖ν) = Σ_x μ(x) log₂ (μ(x)/ν(x))`. It is Mathlib's Kullback–Leibler divergence
(natural logarithm, value `∞` when `μ` is not absolutely continuous with respect to `ν` or the
log-likelihood ratio is not integrable) divided by `ln 2`. On a finite type with the discrete
σ-algebra it is exactly the displayed finite sum. -/
def klBits {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : ENNReal :=
  InformationTheory.klDiv μ ν / ENNReal.ofReal (Real.log 2)

/-- The Bernoulli law with success probability `a` on `Bool` (`true` = success); used only for
`a ∈ [0, 1]`. -/
def bernoulliLaw (a : ℝ) : Measure Bool :=
  ENNReal.ofReal a • Measure.dirac true + ENNReal.ofReal (1 - a) • Measure.dirac false

/-- Definition 3.13 (PDF p.14): `U_i`, the uniform distribution on the `i`-element subsets of
`[n] = Fin n`. Used only for `i ≤ n`, where that family is nonempty. -/
def uniformK (n i : ℕ) : PMF (Finset (Fin n)) :=
  if h : ((Finset.univ : Finset (Fin n)).powersetCard i).Nonempty then
    PMF.uniformOfFinset _ h
  else PMF.pure ∅

/-- `μ` is a distribution over `([n] choose k)`: it gives mass only to `k`-element sets. -/
def IsDistOn (n k : ℕ) (μ : PMF (Finset (Fin n))) : Prop :=
  ∀ T ∈ μ.support, T.card = k

/-- Definition 3.10 (PDF p.13), the up operator `U_{k→k+1}`: every set `T` is replaced by a
uniformly random `(|T|+1)`-element superset of `T`, so that
`U_{k→k+1}(μ)(S) = Σ_{T ⊆ S, |T| = k} μ(T) / (n − k)`. (A set with no superset, `T = [n]`, is
kept; this case does not arise for `k < n`.) -/
def upStep (n : ℕ) (μ : PMF (Finset (Fin n))) : PMF (Finset (Fin n)) :=
  μ.bind fun T =>
    if h : (((Finset.univ : Finset (Fin n)).powersetCard (T.card + 1)).filter
        (fun S => T ⊆ S)).Nonempty then
      PMF.uniformOfFinset _ h
    else PMF.pure T

/-- Definition 3.11 (PDF p.14), the down operator `D_{k→k−1}`: every set `T` is replaced by a
uniformly random `(|T|−1)`-element subset of `T`, so that
`D_{k→k−1}(μ)(S) = Σ_{T ⊇ S, |T| = k} μ(T) / k`. (The empty set is kept; it does not arise for
`k > 0`.) -/
def downStep (n : ℕ) (μ : PMF (Finset (Fin n))) : PMF (Finset (Fin n)) :=
  μ.bind fun T =>
    PMF.uniformOfFinset (T.powersetCard (T.card - 1))
      (Finset.powersetCard_nonempty.mpr (Nat.sub_le _ _))

/-- Remark 3.12 (PDF p.14): `U_{k→k+j}` is `j` consecutive up steps. -/
def upOp (n j : ℕ) : PMF (Finset (Fin n)) → PMF (Finset (Fin n)) := (upStep n)^[j]

/-- Remark 3.12 (PDF p.14): `D_{k→k−j}` is `j` consecutive down steps. -/
def downOp (n j : ℕ) : PMF (Finset (Fin n)) → PMF (Finset (Fin n)) := (downStep n)^[j]

end ParallelMatroidBasis.Main


