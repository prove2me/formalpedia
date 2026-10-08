-- Prove2me | Definitions.Def_PoissonDepTrials_MixInv_Setting
-- name    : PoissonDepTrials_MixInv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:23:58.808067+00:00
-- url     : https://prove2.me/theorems/fc16c12b-c428-4418-8942-afc62ac753e7
-- title:
--   §2–§4, pp. 535–541 — Bernoulli trials, W, λ, V^{(i)}, V^{(i,j)}, Y_{ij}, Y'_{ij}, 𝒫_λ (2.4), the Stein solution S_λh (2.5), Δ, ℳ_{a,b}, Ibragimov's mixing (4.1), m-dependence
-- statement:
--   This file fixes the objects of Chen's Poisson approximation for dependent Bernoulli trials.
--
--   1. **Trials.** $X_1,\dots,X_n$ are Bernoulli random variables on a probability space $(\Omega,\mathcal F,P)$, with the paper's convention $X_i\equiv0$ for $i\le0$ and $i\ge n+1$. $p_i=P(X_i=1)$, $\lambda=\sum_{i=1}^n p_i$ and $W=\sum_{i=1}^n X_i$.
--   2. **Partial sums.** For a nonnegative integer $m$,
--   $$V^{(i)}=\sum_{|k-i|>m}X_k,\qquad V^{(i,j)}=\sum_{|k-i|>m,\ |k-j|>m}X_k,$$
--   $$Y_{it}=V^{(i)}+\sum_{k=i-m}^{t}X_k,\qquad Y'_{it}=V^{(i)}+\sum_{k=i-m,\,k\ne i}^{t}X_k,$$
--   where a sum $\sum_a^b$ with $b<a$ is empty.
--   3. **Poisson expectation** (2.4): for a bounded $h$ on the nonnegative integers, $\mathcal P_\lambda h=e^{-\lambda}\sum_{k\ge0}h(k)\lambda^k/k!$.
--   4. **Stein solution** (2.5): for $w\ge1$,
--   $$S_\lambda h(w)=-(w-1)!\,\lambda^{-w}\sum_{k=0}^{w-1}\bigl[h(k)-\mathcal P_\lambda h\bigr]\frac{\lambda^k}{k!},$$
--   and the forward difference $\Delta f(w)=f(w+1)-f(w)$.
--   5. **Mixing.** $\mathcal M_{a,b}=\sigma(X_i:a\le i\le b)$ and $\mathcal M_{a,\infty}=\sigma(X_i:i\ge a)$. Ibragimov's condition (4.1) asks for a non-increasing $\varphi(k)\downarrow0$ with $|P(B\mid\mathcal M_{1j})-P(B)|\le\varphi(k)$ almost surely for every $B\in\mathcal M_{j+k,\infty}$, $j,k\ge1$. The sequence is $m$-dependent if $\mathcal M_{1r}$ and $\mathcal M_{r+k,\infty}$ are independent whenever $k>m$.
--
--   These are the objects every statement of the mission is written in.
--
--   **Formalization Note** The trials are a map $X:\mathbb N\to\Omega\to\mathbb N$; `IsBernoulliTrials` says each $X_i$ is measurable, vanishes for $i=0$ and $i>n$, and is at most $1$ almost surely. Sums over $k$ run over $[1,n]$ with integer bounds, which equals the paper's sums because $X_k=0$ outside $[1,n]$. `stein` is defined for every $w$ by the first equation of (2.5); its value at $w=0$ is a junk $0$ that no statement uses. In (4.1) the conditional probability is the conditional expectation of the indicator, and the lag $k$ ranges over $k\ge1$. $m$-dependence is stated as independence of $\sigma(X_1,\dots,X_r)$ and $\sigma(X_{r+k},X_{r+k+1},\dots)$ for $k>m$, which is equivalent to the paper's independence of every pair of finite blocks $(X_i,\dots,X_r)$, $(X_{r+k},\dots,X_j)$.
-- source:
--   Chen, Poisson approximation for dependent trials, Ann. Probab. 3 (1975), pp. 535–541, §1, §2, (2.4), (2.5), §4, (4.1), m-dependence (p. 538), V^{(i,j)} (p. 541)

import Mathlib

namespace PoissonDepTrials.MixInv

open MeasureTheory ProbabilityTheory Filter Topology

/-- §2, p. 535: `X₁, …, Xₙ` are Bernoulli trials, padded by `X_i = 0` for `i = 0` and `i > n`
(the paper's convention "Take X_i to be identically zero when i ≦ 0 or ≧ n + 1"). Each `X_i` is
measurable and takes the values `0, 1` almost surely. -/
def IsBernoulliTrials {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) : Prop :=
  (∀ i, Measurable (X i)) ∧ (∀ i, (i = 0 ∨ n < i) → X i = 0) ∧ ∀ i, ∀ᵐ ω ∂P, X i ω ≤ 1

/-- `p_i = P(X_i = 1)`. -/
noncomputable def prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℕ)
    (i : ℕ) : ℝ :=
  P.real {ω | X i ω = 1}

/-- `λ = Σ_{i=1}^n p_i`. -/
noncomputable def lam {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ)
    (X : ℕ → Ω → ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, prob P X i

/-- `W = Σ_{i=1}^n X_i`. -/
def W {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℕ) : Ω → ℕ :=
  fun ω => ∑ i ∈ Finset.Icc 1 n, X i ω

/-- `V^{(i)} = Σ_{|k−i|>m} X_k`. -/
def V {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) : Ω → ℕ :=
  fun ω => ∑ k ∈ Finset.Icc 1 n with m < Int.natAbs (((k : ℕ) : ℤ) - i), X k ω

/-- `V^{(i,j)} = Σ_{|k−i|>m, |k−j|>m} X_k` (p. 541). -/
def Vij {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i j : ℕ) : Ω → ℕ :=
  fun ω => ∑ k ∈ Finset.Icc 1 n with
    m < Int.natAbs (((k : ℕ) : ℤ) - i) ∧ m < Int.natAbs (((k : ℕ) : ℤ) - j), X k ω

/-- `Y_{it} = V^{(i)} + Σ_{k=i−m}^{t} X_k` (empty when `t < i − m`). -/
def Y {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (t : ℤ) : Ω → ℕ :=
  fun ω => V n m X i ω +
    ∑ k ∈ Finset.Icc 1 n with (i : ℤ) - m ≤ ((k : ℕ) : ℤ) ∧ ((k : ℕ) : ℤ) ≤ t, X k ω

/-- `Y'_{it} = V^{(i)} + Σ_{k=i−m, k≠i}^{t} X_k`. -/
def Y' {Ω : Type*} (n m : ℕ) (X : ℕ → Ω → ℕ) (i : ℕ) (t : ℤ) : Ω → ℕ :=
  fun ω => V n m X i ω +
    ∑ k ∈ Finset.Icc 1 n with k ≠ i ∧ (i : ℤ) - m ≤ ((k : ℕ) : ℤ) ∧ ((k : ℕ) : ℤ) ≤ t, X k ω

/-- (2.4): `𝒫_λh = e^{−λ} Σ_{k≥0} h(k) λ^k / k!`. -/
noncomputable def poissonExp (lam : ℝ) (h : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) * h k

/-- (2.5), first equation: the Stein solution `S_λh(w)` for `w ≥ 1`
(its value at `w = 0` is a junk `0` and is never used). -/
noncomputable def stein (lam : ℝ) (h : ℕ → ℝ) (w : ℕ) : ℝ :=
  -(((w - 1).factorial : ℝ) * (lam ^ w)⁻¹ *
    ∑ k ∈ Finset.range w, (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ))

/-- `Δf(w) = f(w + 1) − f(w)`. -/
def delta (f : ℕ → ℝ) (w : ℕ) : ℝ := f (w + 1) - f w

/-- `ℳ_{a,b} = ℬ(X_i : a ≤ i ≤ b)`. -/
def sigmaIcc {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a b : ℕ) :
    MeasurableSpace Ω :=
  ⨆ i ∈ Finset.Icc a b, MeasurableSpace.comap (X i) inferInstance

/-- `ℳ_{a,∞} = ℬ(X_i : i ≥ a)`. -/
def sigmaIci {Ω β : Type*} [MeasurableSpace β] (X : ℕ → Ω → β) (a : ℕ) :
    MeasurableSpace Ω :=
  ⨆ i ∈ Set.Ici a, MeasurableSpace.comap (X i) inferInstance

/-- Ibragimov's mixing condition (4.1), p. 538: `φ(k) ↓ 0` and for all `j, k ≥ 1` and every
`B ∈ ℳ_{j+k,∞}`, `|P(B | ℳ_{1j}) − P(B)| ≤ φ(k)` almost surely. -/
def IbragimovMixing {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    (X : ℕ → Ω → β) (φ : ℕ → ℝ) : Prop :=
  Antitone φ ∧ Tendsto φ atTop (𝓝 0) ∧
    ∀ j k : ℕ, 1 ≤ j → 1 ≤ k → ∀ B : Set Ω, MeasurableSet[sigmaIci X (j + k)] B →
      ∀ᵐ ω ∂P, |(P[B.indicator (fun _ => (1 : ℝ)) | sigmaIcc X 1 j]) ω - P.real B| ≤ φ k

/-- m-dependence, p. 538: `(X_1, …, X_r)` and `(X_{r+k}, X_{r+k+1}, …)` are independent whenever
`k > m`. -/
def IsMDependent {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    (X : ℕ → Ω → β) (m : ℕ) : Prop :=
  ∀ r k : ℕ, m < k → Indep (sigmaIcc X 1 r) (sigmaIci X (r + k)) P

end PoissonDepTrials.MixInv


