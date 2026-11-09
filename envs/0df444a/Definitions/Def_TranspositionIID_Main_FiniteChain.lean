-- Prove2me | Definitions.Def_TranspositionIID_Main_FiniteChain
-- name    : TranspositionIID_Main_FiniteChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:18.82962+00:00
-- url     : https://prove2.me/theorems/d1d6d3f1-404e-4712-a2db-543de732dc9d
-- title:
--   Finite-chain laws, reversible probabilities and smoothed densities
-- statement:
--   Let $P$ be a real matrix on a finite state space $S$. The row-law after $t$ transitions and the expected observable from $s$ are
--   $$\nu_t(z)=\sum_a\nu_0(a)P^t(a,z),\qquad (P^tv)(s)=\sum_zP^t(s,z)v(z).$$
--   A reversible probability is a strictly positive, normalized probability vector $\mu$ satisfying stationarity and detailed balance. Define
--   $$H=\log(1/\min_z\mu(z)),\quad f_t(z)=\nu_t(z)/\mu(z),\quad g_t(z)=(1+f_t(z)+f_{t+1}(z))/3.$$
--   The minimum is only formed on a nonempty finite space. These objects apply to general finite reversible chains, including reducible and periodic chains. Probability and stochasticity use the published minimal predicates.
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). §2.1, printed p.3 = PDF p.3; §4.2, Lemma 4.2, printed p.9 = PDF p.9

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_isFiniteStateDistribution

noncomputable section

namespace TranspositionIID.Main

/-- Finite row-law evolution, with exactly t transitions (source §4.2, p.9). -/
def lawAfter {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (ν : S → ℝ) (t : ℕ) (z : S) : ℝ :=
  ∑ a, ν a * (P ^ t) a z

/-- Expected observable after exactly t transitions from a fixed start. -/
def expectedAfter {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (s : S) (t : ℕ) (v : S → ℝ) : ℝ :=
  ∑ z, (P ^ t) s z * v z

/-- Positive stationary probability with detailed balance; no mixing assumptions. -/
def ReversibleProbability {S : Type*} [Fintype S]
    (P : Matrix S S ℝ) (μ : S → ℝ) : Prop :=
  ActuarialValuation.isFiniteStateDistribution μ ∧
  (∀ z, 0 < μ z) ∧
  (∀ z, ∑ a, μ a * P a z = μ z) ∧
  (∀ a z, μ a * P a z = μ z * P z a)

/-- On a nonempty finite type this is the attained minimum mass. -/
def entropyCeiling {S : Type*} [Fintype S] [Nonempty S] (μ : S → ℝ) : ℝ :=
  Real.log (1 / sInf (Set.range μ))

/-- Density of the t-step law and the paper's three-term smoothing. -/
def densityAfter {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (μ ν : S → ℝ) (t : ℕ) (z : S) : ℝ :=
  lawAfter P ν t z / μ z

def smoothedDensity {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (μ ν : S → ℝ) (t : ℕ) (z : S) : ℝ :=
  (1 + densityAfter P μ ν t z + densityAfter P μ ν (t + 1) z) / 3

end TranspositionIID.Main


