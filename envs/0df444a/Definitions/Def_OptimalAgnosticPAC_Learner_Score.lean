-- Prove2me | Definitions.Def_OptimalAgnosticPAC_Learner_Score
-- name    : OptimalAgnosticPAC_Learner_Score
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:19.591845+00:00
-- url     : https://prove2.me/theorems/ee7d44b8-2b0a-439e-b4ae-8ef623624ec6
-- title:
--   §3 — symmetrized scores, excess losses, suffix averaging and the threshold class
-- statement:
--   For a sample $S=(Z_1,\dots,Z_N)$, $S_{\le t}=(Z_1,\dots,Z_t)$, and $S^{-i}$ is $S$ with observation $i$ removed.
--
--   A score family assigns to every sample $S$ of every length a function $q(\cdot;S)$. The properties §3 uses are:
--
--   1. $q(x;S)\in[-1,1]$;
--   2. $q$ is symmetric in the observations of $S$;
--   3. $q$ is jointly measurable in $(S,x)$;
--   4. for every sample $S$ of size $m\ge1$,
--   $$\frac1{2m}\sum_{i=1}^m|q(x_i;S^{-i})-y_i|\le\widehat L^*_S+120\sqrt{\frac{d\widehat L^*_S}{m}}+7202\frac dm.\tag{13}$$
--
--   With $q_t=q(\cdot;S_{\le t})$, the excess loss against $h$ is
--   $$\Delta_{t+1,h}=\ell(q_t(X_{t+1}),Y_{t+1})-\mathbf 1\{h(X_{t+1})\ne Y_{t+1}\}.$$
--   The suffix average, built from $Z_1,\dots,Z_{2k-1}$, is
--   $$\widehat p(x)=\frac1k\sum_{t=k}^{2k-1}q_t(x).\tag{14}$$
--   For $p:\mathcal X\to[-1,1]$, the threshold class is
--   $$\mathcal T_p=\{x\mapsto2\cdot\mathbf 1\{p(x)\ge u\}-1:-1\le u\le1\}\cup\{x\mapsto-1\}.$$
--   An empirical risk minimizer over a class picks, for each sample, a member of the class with the fewest errors on that sample.
--
--   These objects carry the passage from the leave-one-out bound to the high probability bound.
--
--   **Formalization Note** Indices are 0-based: `S t` is the paper's $Z_{t+1}$, so $\sum_{m=k+1}^{2k}\Delta_{m,h}$ is the sum over $k\le t<2k$. Inequality (13) is stated for samples of length $m+1$ with $m\ge0$, which is every length at least one.
-- source:
--   Dahl, Qian and Zhivotovskiy, An Optimal Agnostic PAC Algorithm, August 6, 2026 preprint, STOC 2027 submission #67, SHA-256 b61bab4e8b832787499a381cc9efadcf919f9384a3bcfae6c3412fb3e557e2fc, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/67.pdf, §3.1–3.3, PDF pp. 8–9 and 14 (printed pp. 7–8 and 13), equations (13), (14)

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Risk
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Learner

variable {X : Type}

/-- `S_{≤t} = (Z_1, …, Z_t)`, the first `t` observations of a sample of size `N ≥ t` (PDF p. 9). -/
def prefixSample {α : Type} {N : ℕ} (S : Fin N → α) (t : ℕ) (ht : t ≤ N) : Fin t → α :=
  fun i => S (Fin.castLE ht i)

/-- `S^{-i}`: the sample with observation `i` removed, the others keeping their order (PDF p. 9). -/
def deleteObs {α : Type} {m : ℕ} (S : Fin (m + 1) → α) (i : Fin (m + 1)) : Fin m → α :=
  fun j => S (i.succAbove j)

/-- The properties of the symmetrized leave-one-out score that §3 uses (PDF p. 9), for a family
`q m S x = q(x; S)` over samples `S` of every length `m ≥ 0`: values in `[-1,1]`; symmetry in the
observations of `S`; joint measurability in `(S, x)`; and inequality (13) for every sample of every
length `m + 1 ≥ 1`. -/
structure IsLOOScore [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) : Prop where
  mem_Icc : ∀ (m : ℕ) (S : Fin m → X × Bool) (x : X), q m S x ∈ Set.Icc (-1 : ℝ) 1
  symm : ∀ (m : ℕ) (S : Fin m → X × Bool) (π : Equiv.Perm (Fin m)) (x : X),
    q m (S ∘ π) x = q m S x
  measurable : ∀ m : ℕ, Measurable (fun z : (Fin m → X × Bool) × X => q m z.1 z.2)
  loo_bound : ∀ (m : ℕ) (S : Fin (m + 1) → X × Bool),
    (1 / (2 * ((m : ℝ) + 1))) * ∑ i, |q m (deleteObs S i) (S i).1 - sgn (S i).2| ≤
      empMinRisk H S + 120 * Real.sqrt ((d : ℝ) * empMinRisk H S / ((m : ℝ) + 1)) +
        7202 * ((d : ℝ) / ((m : ℝ) + 1))

/-- `Δ_{t+1,h} = ℓ(q_t(X_{t+1}), Y_{t+1}) - 1{h(X_{t+1}) ≠ Y_{t+1}}` (PDF p. 8). The index `t` is
0-based: `S t` is the paper's observation `Z_{t+1}`, and `q_t` is trained on the `t` observations
before it. -/
noncomputable def excessLoss {N : ℕ} (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (h : X → Bool)
    (S : Fin N → X × Bool) (t : Fin N) : ℝ :=
  loss (q t (prefixSample S t t.isLt.le) (S t).1) (S t).2 - (if h (S t).1 ≠ (S t).2 then 1 else 0)

/-- `∑_{m=k+1}^{2k} Δ_{m,h}`: the 1-based index `m` is the 0-based index `t = m - 1`, which ranges
over `k ≤ t ≤ 2k - 1`. -/
noncomputable def excessLossSum (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (h : X → Bool) (k : ℕ)
    (S : Fin (2 * k) → X × Bool) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val), excessLoss q h S t

/-- The suffix average (14) (PDF p. 9): `p̂(x) = (1/k) ∑_{t=k}^{2k-1} q_t(x)` with
`q_t = q(·; S_{≤t})`, built from a sample of `2k - 1` observations. The index `j` stands for
`t = k + j`. It takes neither `L*` nor `δ` as input. -/
noncomputable def suffixAvg (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (k : ℕ)
    (S : Fin (2 * k - 1) → X × Bool) (x : X) : ℝ :=
  (1 / (k : ℝ)) * ∑ j : Fin k,
    q (k + j) (prefixSample S (k + j) (by have := j.isLt; omega)) x

/-- The threshold class (PDF p. 14):
`T_p = {x ↦ 2·1{p(x) ≥ u} - 1 : -1 ≤ u ≤ 1} ∪ {x ↦ -1}`, with `true` standing for `+1`. -/
def thresholdClass (p : X → ℝ) : Set (X → Bool) :=
  {h | ∃ u ∈ Set.Icc (-1 : ℝ) 1, h = fun x => decide (u ≤ p x)} ∪ {fun _ => false}

/-- `hhat` selects, for every sample, an empirical risk minimizer over the class `T`. -/
def IsERM {k : ℕ} (T : Set (X → Bool)) (hhat : (Fin k → X × Bool) → X → Bool) : Prop :=
  ∀ S, hhat S ∈ T ∧ ∀ h ∈ T, errCount (hhat S) S ≤ errCount h S

end OptimalAgnosticPAC.Learner


