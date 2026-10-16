-- Prove2me | Definitions.Def_InfFisher_EG_Setting
-- name    : InfFisher_EG_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:38.166907+00:00
-- url     : https://prove2.me/theorems/9e65c3bc-4943-4942-8ad5-a0ef07482c20
-- title:
--   §2–§3 and Lemma A.1, pp. 6, 9, 11, a1 — pure utility set U′, reduced dual objective (2), Pareto optimality, envy-freeness, proportionality, atomless measures, the sets of Lemma A.1
-- statement:
--   These definitions give the utility sets, the reduced dual objective and the fairness notions of Sections 2–3 of Gao and Kroer, together with the objects of the Dvoretzky–Wald–Wolfowitz lemma (Lemma A.1). Throughout, $\mu$ is a measure on a measurable item space, $\Theta$ is a measurable region of it, there are $n$ buyers with valuations $v_i$ and budgets $B_i$, and $\langle f,g\rangle=\int fg\,d\mu$.
--
--   1. **Pure utility set.** $U'(v,\Theta)$ is the set of vectors $(v_1(\Theta_1),\dots,v_n(\Theta_n))$, where $v_i(\Theta_i)=\int_{\Theta_i}v_i\,d\mu$ and $\Theta_1,\dots,\Theta_n\subseteq\Theta$ are measurable and pairwise a.e.-disjoint, that is, $\mu(\Theta_i\cap\Theta_j)=0$ for $i\ne j$.
--   2. **Reduced dual objective (2).** For $\beta\in\mathbb R^n$,
--   $$\psi(\beta)=\Big\langle \max_i\beta_i v_i,\mathbf 1\Big\rangle-\sum_i B_i\log\beta_i .$$
--   3. **Pareto optimality.** An allocation $x$ is (strongly) Pareto optimal if there is no allocation $\tilde x$ with $\langle v_i,\tilde x_i\rangle\ge\langle v_i,x_i\rangle$ for all $i$ and strict inequality for at least one $i$.
--   4. **Envy-freeness (budget weighted).** $\frac{1}{B_i}\langle v_i,x_i\rangle\ge\frac{1}{B_j}\langle v_i,x_j\rangle$ for all $j\ne i$.
--   5. **Proportionality.** $\langle v_i,x_i\rangle\ge\frac{B_i}{\|B\|_1}v_i(\Theta)$ for all $i$, where $v_i(\Theta)=\int v_i\,d\mu$.
--   6. **Atomless measure.** A measure $m$ is atomless if for every measurable set $A$ and every $0<c<m(A)$ there is a measurable $B\subseteq A$ with $m(B)=c$.
--   7. **The sets of Lemma A.1.** For measures $\mu_1,\dots,\mu_m$ on a measurable space $\Omega$ and a number $p$ of parts: $\mathcal X$ is the set of $p$-tuples of nonnegative measurable functions with $\sum_j x_j=\mathbf 1$; $\mathcal S$ is the set of measurable partitions $(\Theta_1,\dots,\Theta_p)$ of $\Omega$ (pairwise disjoint, union $\Omega$); and
--   $$\mathcal U=\Big\{u\in\mathbb R^{m\times p}:u_{ij}=\int x_j\,d\mu_i,\ x\in\mathcal X\Big\},\qquad \mathcal U'=\big\{u\in\mathbb R^{m\times p}:u_{ij}=\mu_i(\Theta_j),\ (\Theta_j)\in\mathcal S\big\}.$$
--
--   $U'$ and $\psi$ are the objects of Lemmas 1 and 2, the three fairness notions are the conclusions of Theorem 3, and atomlessness together with $\mathcal U$ and $\mathcal U'$ is the setting of Lemma A.1, from which Lemma 1 follows.
--
--   **Formalization Note** Buyers are indexed by `Fin n` (0-based). $\|B\|_1$ is written $\sum_j B_j$, which agrees with the paper because budgets are positive. Lean's real logarithm has $\log 0=0$, so $\psi$ is meaningful only at $\beta>0$; the theorems restrict to that domain. The weights in $\mathcal X$ sum to one at every point rather than almost everywhere: the paper names no reference measure for its “a.e.”, and changing a tuple on a set that is null for every $\mu_i$ does not change $\mathcal U$. In $\mathcal U'$, $\mu_i(\Theta_j)$ is converted to a real number, which is exact for the finite measures of Lemma A.1 (finiteness is a hypothesis of that lemma). Atomlessness is the paper's divisibility property, not Mathlib's weaker `NoAtoms`. Envy-freeness and proportionality do not themselves require $x$ to be an allocation; the theorems that use them supply it.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, §2 p. 6, (2) p. 9, fairness definitions p. 11, Lemma A.1 p. a1

import Mathlib
import Definitions.Def_InfFisher_EG_Market

namespace InfFisher.EG

open MeasureTheory
variable {α : Type*} [MeasurableSpace α]

def pureUtil (μ : Measure α) (Θ : Set α) {n : ℕ}
    (v : Fin n → α → ℝ) : Set (Fin n → ℝ) :=
  {u | ∃ S : Fin n → Set α,
    (∀ i, MeasurableSet (S i) ∧ S i ⊆ Θ) ∧
    (∀ i j, i ≠ j → μ (S i ∩ S j) = 0) ∧
    ∀ i, u i = ∫ θ in S i, v i θ ∂μ}

noncomputable def dualRed (μ : Measure α) {n : ℕ}
    (v : Fin n → α → ℝ) (B β : Fin n → ℝ) : ℝ :=
  (∫ θ, maxScaled v β θ ∂μ) - ∑ i, B i * Real.log (β i)

def IsParetoOptimal (μ : Measure α) {n : ℕ}
    (v : Fin n → α → ℝ) (x : Fin n → α → ℝ) : Prop :=
  IsAllocation μ x ∧
  ¬ ∃ x', IsAllocation μ x' ∧
    (∀ i, pair μ (v i) (x i) ≤ pair μ (v i) (x' i)) ∧
    ∃ i, pair μ (v i) (x i) < pair μ (v i) (x' i)

def IsEnvyFree (μ : Measure α) {n : ℕ}
    (v : Fin n → α → ℝ) (B : Fin n → ℝ)
    (x : Fin n → α → ℝ) : Prop :=
  ∀ i j, j ≠ i →
    (1 / B j) * pair μ (v i) (x j) ≤
    (1 / B i) * pair μ (v i) (x i)

def IsProportional (μ : Measure α) {n : ℕ}
    (v : Fin n → α → ℝ) (B : Fin n → ℝ)
    (x : Fin n → α → ℝ) : Prop :=
  ∀ i, B i / (∑ j, B j) * (∫ θ, v i θ ∂μ) ≤ pair μ (v i) (x i)

def IsAtomless {Ω : Type*} [MeasurableSpace Ω] (m : Measure Ω) : Prop :=
  ∀ (A : Set Ω) (c : ENNReal), MeasurableSet A →
    0 < c → c < m A → ∃ B, B ⊆ A ∧ MeasurableSet B ∧ m B = c

def dwwX {Ω : Type*} [MeasurableSpace Ω] (p : ℕ) : Set (Fin p → Ω → ℝ) :=
  {x | (∀ j, Measurable (x j) ∧ ∀ θ, 0 ≤ x j θ) ∧
    ∀ θ, ∑ j, x j θ = 1}

def dwwS {Ω : Type*} [MeasurableSpace Ω] (p : ℕ) : Set (Fin p → Set Ω) :=
  {S | (∀ j, MeasurableSet (S j)) ∧
    (∀ j k, j ≠ k → S j ∩ S k = ∅) ∧
    (⋃ j, S j) = Set.univ}

def dwwU {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μs : Fin m → Measure Ω) (p : ℕ) : Set (Fin m → Fin p → ℝ) :=
  {u | ∃ x ∈ dwwX p, ∀ i j, u i j = ∫ θ, x j θ ∂(μs i)}

def dwwU' {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μs : Fin m → Measure Ω) (p : ℕ) : Set (Fin m → Fin p → ℝ) :=
  {u | ∃ S ∈ dwwS p, ∀ i j, u i j = (μs i (S j)).toReal}

end InfFisher.EG


