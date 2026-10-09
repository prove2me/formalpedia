-- Prove2me | Definitions.Def_StochKolmogorov_Persist_Persistence
-- name    : StochKolmogorov_Persist_Persistence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:11.508036+00:00
-- url     : https://prove2.me/theorems/a22b7e5d-edad-473b-873b-6a3661bcca21
-- title:
--   §1.1, §3, §4, pp. 5, 14–16 — faces ℝ^{I,◦}₊, Assumption 1.2, Φ of (4.3), and irreducible / aperiodic / petite for the skeleton chain X(kT)
-- statement:
--   This module adds the objects specific to the persistence theorem.
--
--   1. **Faces** (Lemma 3.1, p. 14). For $I\subseteq\{1,\dots,n\}$, $\mathbb R^{I,\circ}_+=\{x\in\mathbb R^n_+: x_i=0\text{ if }i\notin I,\ x_i>0\text{ if }i\in I\}$.
--   2. **Assumption 1.2** (p. 5). For every $\mu\in\mathrm{Conv}(\mathcal M)$,
--   $$\max_{i=1,\dots,n}\lambda_i(\mu)>0.$$
--   3. **The function $\Phi$ of (4.3)** (p. 16), for a weight vector $p$:
--   $$\Phi(x)=\frac{\sum_ic_ix_if_i(x)}{1+c^\top x}-\frac12\frac{\sum_{i,j}\sigma_{ij}c_ic_jx_ix_jg_i(x)g_j(x)}{(1+c^\top x)^2}-\sum_ip_i\Big(f_i(x)-\frac{\sigma_{ii}g_i^2(x)}{2}\Big).$$
--   4. **The skeleton chain** $(X(kT))_{k\in\mathbb N}$ on $\mathbb R^{n,\circ}_+$, $T>0$, whose $k$-step kernel is $P^k(x,\cdot)=P_X(kT,x,\cdot)$ (p. 15):
--      - *irreducible*: there is a nonzero $\sigma$-finite measure $\varphi$ on $\mathbb R^{n,\circ}_+$ such that every measurable $A\subseteq\mathbb R^{n,\circ}_+$ with $\varphi(A)>0$ satisfies $\sum_{k\ge1}P^k(x,A)>0$ for all $x\in\mathbb R^{n,\circ}_+$;
--      - *aperiodic*: there is no $d\ge2$ and no family of nonempty, pairwise disjoint measurable sets $E_0,\dots,E_{d-1}\subseteq\mathbb R^{n,\circ}_+$ with $P(x,E_{i+1\bmod d})=1$ for all $x\in E_i$;
--      - a set $K$ is *petite* if there are weights $a_k\ge0$, $k\ge1$, $\sum_{k\ge1}a_k=1$, and a nonzero finite measure $\nu$ on $\mathbb R^{n,\circ}_+$ with $\sum_{k\ge1}a_kP^k(x,A)\ge\nu(A)$ for all $x\in K$ and measurable $A\subseteq\mathbb R^{n,\circ}_+$.
--
--   Assumption 1.2 says every boundary ergodic measure (and every finite mixture of them) is a "repeller"; $\Phi$ is the drift of $\ln V$ along the process; the skeleton-chain notions are the hypotheses of the Meyn–Tweedie criterion that turns the Lyapunov bound (4.18) into geometric ergodicity.
--
--   **Formalization Note** On p. 15 the period is defined as "the smallest positive integer $d$" admitting a cyclic decomposition $E_0,\dots,E_{d-1}$; read literally, $d=1$ (with $E_0$ the whole space) always qualifies and every chain would be aperiodic. The definition here is the intended Meyn–Tweedie notion: no $d$-cycle with $d\ge2$, the cycle sets nonempty (otherwise empty sets would form a trivial cycle). The irreducibility measure $\varphi$ and the petite measure $\nu$ are required to live on $\mathbb R^{n,\circ}_+$ (they are measures on the chain's state space $E=\mathbb R^{n,\circ}_+$); the petite weights are indexed from $k=1$ by setting $a_0=0$.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 3.1, p. 14 (faces); Assumption 1.2, p. 5; (4.3), p. 16; §3, p. 15 (irreducible, period/aperiodic, petite: "If there is a non-trivial σ-finite positive measure φ on (E, 𝓔) such that for any A ∈ 𝓔 satisfying φ(A) > 0 we have Σ_{n=1}^∞ 𝒫ⁿ(x, A) > 0, x ∈ E […] then the Markov chain Φ is called irreducible. […] there exists a positive integer d and disjoint subsets E_0, …, E_{d−1} such that for all i = 0, …, d − 1 and all x ∈ E_i, we have 𝒫(x, E_j) = 1 where j = i + 1 (mod d). The smallest positive integer d satisfying the above is called the period of Φ. An aperiodic Markov chain is a chain with period d = 1. A set C ∈ 𝓔 is called petite, if there exists a non-negative sequence (a_n)_{n∈ℕ} with Σ_{n=1}^∞ a_n = 1 and a nontrivial positive measure ν on (E, 𝓔) such that Σ_{n=1}^∞ a_n𝒫ⁿ(x, A) ≥ ν(A), x ∈ C, A ∈ 𝓔.")

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

/-- The face `ℝ^{I,◦}₊ = {x ∈ ℝⁿ₊ : xᵢ = 0 if i ∉ I, xᵢ > 0 if i ∈ I}` of Lemma 3.1
(arXiv:1704.06984v1, p. 14). -/
def faceOpen {n : ℕ} (I : Finset (Fin n)) : Set (SDEState n) :=
  {x | x ∈ orthant n ∧ (∀ i, i ∉ I → x i = 0) ∧ ∀ i, i ∈ I → 0 < x i}

/-- Assumption 1.2 (p. 5): `max_i λᵢ(π) > 0` for every `π ∈ Conv(M)`. -/
def Assumption12 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ π ∈ conv (bdryErgodic P X), ∃ i, 0 < lyap C i π

/-- The minimum in (4.1): `2ρ*` is the least weighted invasion rate on `M` and is attained
by a boundary ergodic measure. -/
def IsWeightedInvasionMin {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (p : SDEState n) (ρ : ℝ) : Prop :=
  (∀ μ ∈ bdryErgodic P X, 2 * ρ ≤ ∑ i, p i * lyap C i μ) ∧
    ∃ μ ∈ bdryErgodic P X, ∑ i, p i * lyap C i μ = 2 * ρ

/-- `Φ` of (4.3) (p. 16):
`Φ(x) = ∑ᵢ cᵢxᵢfᵢ(x)/(1 + cᵀx) − ½ ∑ᵢⱼ σᵢⱼcᵢcⱼxᵢxⱼgᵢ(x)gⱼ(x)/(1 + cᵀx)² − ∑ᵢ pᵢ(fᵢ(x) − σᵢᵢgᵢ²(x)/2)`. -/
noncomputable def Phi {n : ℕ} (C : Coeffs n) (c p x : SDEState n) : ℝ :=
  cBracket C c x - ∑ i, p i * (C.f i x - C.sig i i * C.g i x ^ 2 / 2)

/-- Irreducibility (p. 15) of the skeleton chain `(X(kT))_{k ∈ ℕ}` on `ℝⁿ,◦₊`: there is a
nontrivial σ-finite measure `φ` on `ℝⁿ,◦₊` such that every `A ⊆ ℝⁿ,◦₊` with `φ(A) > 0` is reached
from every `x ∈ ℝⁿ,◦₊`, i.e. `∑_{k ≥ 1} P^k(x, A) > 0`. The `k`-step kernel of the skeleton chain is
the transition probability at time `kT`. -/
def SkelIrreducible {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (T : ℝ≥0) : Prop :=
  ∃ φ : Measure (SDEState n), φ ≠ 0 ∧ SigmaFinite φ ∧ φ (openOrthant n)ᶜ = 0 ∧
    ∀ A : Set (SDEState n), MeasurableSet A → A ⊆ openOrthant n → 0 < φ A →
      ∀ x ∈ openOrthant n, ∃ k : ℕ, 1 ≤ k ∧ 0 < trans P X (k * T) x A

/-- Aperiodicity (p. 15) of the skeleton chain on `ℝⁿ,◦₊`, in Meyn–Tweedie's sense: there is no
cycle `E₀, …, E_{d−1}` with `d ≥ 2` of nonempty, pairwise disjoint measurable subsets of `ℝⁿ,◦₊`
with `P(x, E_{i+1 mod d}) = 1` for all `x ∈ Eᵢ`. -/
def SkelAperiodic {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (T : ℝ≥0) : Prop :=
  ¬ ∃ d : ℕ, 2 ≤ d ∧ ∃ E : Fin d → Set (SDEState n),
    (∀ i, MeasurableSet (E i) ∧ (E i).Nonempty ∧ E i ⊆ openOrthant n) ∧
    Pairwise (Function.onFun Disjoint E) ∧
    ∀ i, ∀ x ∈ E i, trans P X T x (E (finRotate d i)) = 1

/-- `K` is petite (p. 15) for the skeleton chain on `ℝⁿ,◦₊`: there are weights `aₖ ≥ 0`,
`k ≥ 1`, with `∑_{k ≥ 1} aₖ = 1` and a nontrivial measure `ν` on `ℝⁿ,◦₊` such that
`∑_{k ≥ 1} aₖ P^k(x, A) ≥ ν(A)` for all `x ∈ K` and measurable `A ⊆ ℝⁿ,◦₊`. -/
def SkelPetite {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (T : ℝ≥0) (K : Set (SDEState n)) : Prop :=
  ∃ a : ℕ → ℝ≥0∞, a 0 = 0 ∧ ∑' k, a k = 1 ∧
    ∃ ν : Measure (SDEState n), ν ≠ 0 ∧ IsFiniteMeasure ν ∧ ν (openOrthant n)ᶜ = 0 ∧
      ∀ x ∈ K, ∀ A : Set (SDEState n), MeasurableSet A → A ⊆ openOrthant n →
        ν A ≤ ∑' k, a k * trans P X (k * T) x A

end StochKolmogorov.Persist


