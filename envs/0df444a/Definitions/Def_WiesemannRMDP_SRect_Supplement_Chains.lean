-- Prove2me | Definitions.Def_WiesemannRMDP_SRect_Supplement_Chains
-- name    : WiesemannRMDP_SRect_Supplement_Chains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:49:22.7398+00:00
-- url     : https://prove2.me/theorems/d8bd6eac-b8da-49e9-9043-68886e5d138a
-- title:
--   Irreducibility, expected return time µ_s and the χ²_κ distribution (§5.2 p. 32, Appendix B p. 46, Appendix C p. 49)
-- statement:
--   General objects for finite Markov chains and for the limit law of Theorem 5.3.
--
--   1. **Irreducibility.** A finite Markov chain with transition matrix $P$ is irreducible if every state $j$ can be reached from every state $i$: there is $m\ge 0$ with $(P^m)_{ij}>0$.
--   2. **Expected return time.** For a state $s$, let $\tau_s^+ := \min\{m\ge1 : X_m = s\}$ be the first return time of the chain started in $s$. The expected return time is
--   $$\mu_s := \mathbb E_s[\tau_s^+] = \sum_{m\ge 0}\mathbb P_s(\tau_s^+>m) = \sum_{m\ge0}\sum_{y}\big(T_s^m\big)_{sy}\in[0,\infty],$$
--   where $T_s$ is $P$ with its column $s$ replaced by zeros, so that $(T_s^m)_{sy}$ is the probability of an $m$-step path from $s$ to $y$ that avoids $s$ at times $1,\dots,m$.
--   3. **The $\chi^2_\kappa$ distribution.** $\chi^2_\kappa$ is the law of $Z_1^2+\dots+Z_\kappa^2$ for independent standard normal random variables $Z_1,\dots,Z_\kappa$.
--
--   Irreducibility enters assumption (A2) and condition (C4), the return times enter Lemma C.1 and the matrix $\Sigma$ of (48d), and $\chi^2_\kappa$ is the limit law in Theorem 5.3.
--
--   **Formalization Note** $\mu_s$ is valued in $[0,\infty]$, so that its finiteness, claimed in Lemma C.1, is a statement rather than a convention; it is computed by the tail-sum formula for the expectation of a $\{1,2,\dots,\infty\}$-valued random variable. $\chi^2_\kappa$ is the image of the product of $\kappa$ standard Gaussian measures under $x\mapsto\sum_i x_i^2$; an instance records that it is a probability measure.
-- source:
--   Wiesemann, Kuhn & Rustem, Robust Markov Decision Processes, Optimization Online 2610 (revision of February 9, 2012; sha256 8cbadb80…a79b), (A2) p. 32, Theorem 5.3 p. 32, (C4) of Theorem B.1 p. 46, expected return time p. 49

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace WiesemannRMDP.SRect.Supplement

/-- Irreducibility of a finite Markov chain with transition matrix `P` (used in (A2), p. 32, and in
condition (C4) of Theorem B.1, p. 46, of Wiesemann, Kuhn & Rustem, *Robust Markov Decision
Processes*, Optimization Online 2610, revision of February 9, 2012): every state `j` can be
reached from every state `i`, i.e. some power of `P` has a positive `(i, j)` entry.

**Formalization Note.** The power `m = 0` is allowed, so `i` always reaches itself; this is the
usual convention ("every state communicates with every state"). -/
def IsIrreducible {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℝ) : Prop :=
  ∀ i j : ι, ∃ m : ℕ, 0 < (P ^ m) i j

/-- The taboo matrix of `P` for the state `s`: `P` with its column `s` set to zero. Its `m`-th
power gives the probabilities of `m`-step paths that avoid `s` at times `1, …, m`. -/
def tabooMatrix {ι : Type*} [DecidableEq ι] (P : Matrix ι ι ℝ) (s : ι) : Matrix ι ι ℝ :=
  Matrix.of fun x y => if y = s then 0 else P x y

/-- The expected return time `µ_s` of the state `s` in the finite Markov chain with transition
matrix `P` (Appendix C, p. 49): the expected number of transitions between two successive visits
of `s`, i.e. `E_s[τ_s⁺]` with `τ_s⁺ := min {m ≥ 1 : X_m = s}` the first return time.

It is computed by the tail-sum formula `E_s[τ_s⁺] = ∑_{m ≥ 0} P_s(τ_s⁺ > m)`, where
`P_s(τ_s⁺ > m) = ∑_y [(P with column s set to 0)^m]_{s y}` is the probability that the chain
started in `s` avoids `s` at times `1, …, m`. The value lies in `[0, ∞]`; it is `∞` when the
return time has infinite mean or is infinite with positive probability.

**Formalization Note.** The value is taken in `ℝ≥0∞`, so that `µ_s < ∞` (claimed in Lemma C.1) is
a statement and not a convention. `ENNReal.ofReal` is applied to the (nonnegative, for a
stochastic `P`) tail probabilities. -/
noncomputable def expectedReturnTime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (s : ι) : ℝ≥0∞ :=
  ∑' m : ℕ, ENNReal.ofReal (∑ y : ι, ((tabooMatrix P s) ^ m) s y)

/-- The `χ²`-distribution with `κ` degrees of freedom (Theorem 5.3, p. 32): the law of
`Z₁² + ⋯ + Z_κ²` for independent standard normal random variables `Z₁, …, Z_κ`. -/
noncomputable def chiSquared (κ : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin κ => gaussianReal 0 1).map (fun x => ∑ i, x i ^ 2)

instance (κ : ℕ) : IsProbabilityMeasure (chiSquared κ) := by
  unfold chiSquared
  exact Measure.isProbabilityMeasure_map
    (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2).aemeasurable

end WiesemannRMDP.SRect.Supplement


