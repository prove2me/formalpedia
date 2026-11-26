-- Prove2me | Definitions.Def_SecSampling_Supplement_ROSp
-- name    : SecSampling_Supplement_ROSp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:58:48.004465+00:00
-- url     : https://prove2.me/theorems/a48f9f29-c5c8-4f4f-a20e-e95125789be9
-- title:
--   ROSp, $ALG_t$, sequential-$\ell$-max, Eq. (1), and Samuels' constant
-- statement:
--   This module defines the **random-order secretary problem with independent $p$-sampling (ROSp)** in both equivalent forms used by the paper.
--
--   In the original form, each element is independently sampled with probability $p$, and the remaining elements arrive in a uniformly random order. An ordinal behavioral algorithm sees the sample count and the relative-rank history. Its success probability is the finite average over sampled sets and permutations; its success guarantee is the worst case over distinct value vectors and instance sizes.
--
--   In the arrival-time form, every element receives an independent uniform time $\tau_i\in[0,1]$, is sampled when $\tau_i<p$, and otherwise arrives online in increasing time order. For a strictly increasing sequence $0\le t_1<t_2<\cdots<1$, $ALG_t$ rejects before $t_1$ and, on $[t_k,t_{k+1})$, accepts the first running online maximum above the $k$-th largest sample. The module also defines sequential-$\ell$-max algorithms (with $\ell$ non-decreasing and valued in $\{0,\dots,n\}$, the value $0$ meaning no acceptance at that index; the paper's printed codomain $[n]$ omits $0$, which Lemma 5 needs), Eq. (1), the equations for $t^*$, the approximation $t'_i=1-c/i$, and
--   $$
--   \gamma=e^{-c}+(e^c-1-c)\int_1^\infty x^{-1}e^{-cx}\,dx,
--   \qquad \int_0^1\frac{e^{cx}-1}{x}\,dx=1.
--   $$
--
--   These definitions are the common interface for Theorem 2 and Lemmas 2–6 and 22.
--
--   **Formalization Note** Elements are `Fin n`; threshold sequences are zero-indexed (`t 0=t₁`). Uniform random order is an exact finite permutation average. Arrival-time probabilities use product Lebesgue measure restricted to $[0,1]^n$; equal arrival times, a null event, are broken by index. Guarantees use lower-bound plus epsilon-attainment predicates instead of real `sInf`. Win is by vacuity when every element is sampled, as in the published AOSp definition.
-- source:
--   Correa, Cristi, Feuilloley, Oosterwijk & Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, §1 p.2 (PDF p.3), §3 pp.11–13 (PDF pp.12–14), Eq. (1), Eq. (2), and Lemma 22 pp.34–35 (PDF pp.35–36)

import Mathlib
import Definitions.Def_SecSampling_AOSp

open Classical Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace SecSampling.Supplement

/-- The online order obtained by deleting the sampled elements from a permutation of all elements.
For a uniform permutation this induces the uniform order on the online set. -/
def randomOnlineOrder {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : List (Fin n) :=
  (List.ofFn σ).filter (fun i => decide (i ∉ S))

/-- The ROSp success probability in the paper's original, ordinal formulation: first perform
independent `p`-sampling, then average the online win probability over a uniform random order.

The average is taken over permutations of all `n` elements and then restricted to the online
elements. Every order of a fixed online set has the same number of extensions, so this is exactly
the uniform random order of that set. -/
noncomputable def rospWinProb (p : ℝ) (A : SecSampling.Algorithm) {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), SecSampling.sampleWeight p S *
    ((∑ σ : Equiv.Perm (Fin n),
        SecSampling.winOnSample A v S (randomOnlineOrder σ S)) /
      (n.factorial : ℝ))

/-- A real number `g` is the worst-case ROSp success probability at the fixed size `n`.
The epsilon-attainment clause records the infimum without relying on the default value of `sInf`.
-/
def IsROSpSizeValue (p : ℝ) (A : SecSampling.Algorithm) (n : ℕ) (g : ℝ) : Prop :=
  (∀ (v : Fin n → ℝ), Function.Injective v → g ≤ rospWinProb p A v) ∧
    ∀ ε : ℝ, 0 < ε → ∃ v : Fin n → ℝ,
      Function.Injective v ∧ rospWinProb p A v < g + ε

/-- A real number `g` is the ROSp success guarantee of `A`: the worst case over both the size and
the distinct values, expressed by a lower bound plus epsilon-attainment. -/
def IsROSpGuarantee (p : ℝ) (A : SecSampling.Algorithm) (g : ℝ) : Prop :=
  (∀ (n : ℕ) (v : Fin n → ℝ), Function.Injective v → g ≤ rospWinProb p A v) ∧
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (v : Fin n → ℝ),
      Function.Injective v ∧ rospWinProb p A v < g + ε

/-- An admissible threshold sequence `t₁,t₂,…`, represented with `t 0 = t₁`: it is strictly
increasing and lies in `[0,1)`. The algorithm below simply never stops after the supremum of a
sequence that does not tend to `1`; this totalizes the paper's rule without changing its intended
sequences, in particular `t*`. -/
def IsAdmissible (t : ℕ → ℝ) : Prop :=
  StrictMono t ∧ ∀ i, t i ∈ Ico (0 : ℝ) 1

/-- The product uniform probability law on the arrival-time cube `[0,1]^n`. -/
noncomputable def arrivalLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1))

/-- The sampled set in the arrival-time formulation: element `i` is sampled exactly when
`τᵢ < p`. -/
noncomputable def arrivalSample {n : ℕ} (p : ℝ) (τ : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => τ i < p)

/-- A deterministic tie-breaking order on arrivals. Equal arrival times have probability zero;
breaking their ties by index makes every definition total on the whole cube. -/
def arrivesBefore {n : ℕ} (τ : Fin n → ℝ) (i j : Fin n) : Prop :=
  τ i < τ j ∨ (τ i = τ j ∧ i < j)

/-- At its arrival, `i` passes the rule of `ALG_t`: it is online, is a running online maximum,
and lies in an interval `[t_k,t_{k+1})` whose `(k+1)`-st largest sampled value it exceeds.
Indices of `t` are zero-based, so `k=0` is the paper's first threshold. Before `t₁` no element
passes. -/
noncomputable def ALGTAcceptable {n : ℕ} (p : ℝ) (t : ℕ → ℝ) (v : Fin n → ℝ)
    (τ : Fin n → ℝ) (i : Fin n) : Prop :=
  p ≤ τ i ∧
    (∀ j : Fin n, p ≤ τ j → arrivesBefore τ j i → v j ≤ v i) ∧
    ∃ k : ℕ, t k ≤ τ i ∧ τ i < t (k + 1) ∧
      ((arrivalSample p τ).filter (fun j => v i < v j)).card < k + 1

/-- The success event of `ALG_t` in the uniform-arrival formulation. It holds by vacuity when
every element is sampled; otherwise the first acceptable online value must be the maximum of the
online set. -/
noncomputable def ALGTWins {n : ℕ} (p : ℝ) (t : ℕ → ℝ) (v : Fin n → ℝ)
    (τ : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, τ i < p) ∨
    ∃ i : Fin n,
      p ≤ τ i ∧
      (∀ j : Fin n, p ≤ τ j → v j ≤ v i) ∧
      ALGTAcceptable p t v τ i ∧
      ∀ j : Fin n, arrivesBefore τ j i → ¬ ALGTAcceptable p t v τ j

/-- Success probability of `ALG_t` on a fixed injective value vector in the arrival-time model.
-/
noncomputable def algTSuccessProb {n : ℕ} (p : ℝ) (t : ℕ → ℝ) (v : Fin n → ℝ) : ℝ :=
  (arrivalLaw n).real {τ | ALGTWins p t v τ}

/-- A canonical injective value vector. Since `ALG_t` is ordinal and arrival order is uniform, its
success probability is independent of the chosen injective values; this representative defines
the size-`n` probability used in Lemmas 2 and 3. -/
def canonicalValues (n : ℕ) : Fin n → ℝ := fun i => (i : ℝ)

/-- The size-`n` success probability of `ALG_t`. -/
noncomputable def algTSizeProb (p : ℝ) (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  algTSuccessProb p t (canonicalValues n)

/-- `g` is the success guarantee of `ALG_t`, expressed without a potentially junk real infimum.
-/
def IsALGTGuarantee (p : ℝ) (t : ℕ → ℝ) (g : ℝ) : Prop :=
  (∀ n : ℕ, g ≤ algTSizeProb p t n) ∧
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, algTSizeProb p t n < g + ε

/-- Equation (1), with `t 0 = t₁`: the limiting ROSp success probability of `ALG_t`. -/
noncomputable def eqOne (p : ℝ) (t : ℕ → ℝ) : ℝ :=
  ∑' i : ℕ, p ^ i *
    (1 - max p (t i) -
      ∫ x in max p (t i)..1,
        ∑ j ∈ Finset.range (i + 1), (x - max p (t i)) / x ^ (j + 1))

/-- A non-decreasing sequential threshold function `ℓ` on the observation indices `1,…,n`
(§3, p.12), with values in `{0,…,n}`. Values away from the indices `1,…,n` are irrelevant.

**Formalization Note.** The paper writes `ℓ : [n] → [n]`, but the value `0` ("reject even a
running maximum that beats every sample", i.e. never accept at that index) is needed: the proof of
Lemma 5 (p.31) defines `ℓ(j) = max{r : ∏_{s<r} (j-s)/(n-s) ≥ W(n,j,r)}`, where `r = 0` always
qualifies (empty product), and the limit in Lemma 6 (p.33) uses `ℓ̃ = 0` on `[p,t₁)`. With values
`≥ 1` the rule accepts the first online element whenever no element is sampled, and no such rule is
optimal (at `p = 0`, `n = 3` it wins with probability `1/3`, the classical rule `1/2`). -/
structure SequentialThreshold (n : ℕ) where
  level : ℕ → ℕ
  bounds : ∀ i, 1 ≤ i → i ≤ n → level i ≤ n
  monotone : Monotone level

/-- The sequential-`ℓ`-max algorithm in the original ordinal formulation. At the current online
arrival, `s + h.length` is its position among the sample followed by online observations; the rule
accepts precisely when it is the running online maximum (`b=0`) and fewer than `ℓ(i)` samples are
larger (`a<ℓ(i)`). -/
noncomputable def sequentialMax {n : ℕ} (ℓ : SequentialThreshold n) : SecSampling.Algorithm :=
  fun n' s h =>
    if n' = n then
      match h.getLast? with
      | some (a, b) => if b = 0 ∧ a < ℓ.level (s + h.length) then 1 else 0
      | none => 0
    else 0

/-- `ℓ` is optimal for the fixed ROSp parameters `p,n` among every ordinal, possibly randomized
algorithm. -/
def IsOptimalSequential (p : ℝ) (n : ℕ) (ℓ : SequentialThreshold n) : Prop :=
  ∀ A : SecSampling.Algorithm, SecSampling.IsAlgorithm A →
    rospWinProb p A (canonicalValues n) ≤
      rospWinProb p (sequentialMax ℓ) (canonicalValues n)

/-- The coordinate equation (2) for `t*_i`, with zero-based coordinate `i` representing the
paper's `i+1`. -/
noncomputable def thresholdEquation (i : ℕ) (x : ℝ) : Prop :=
  Real.log (1 / x) +
      ∑ j ∈ Finset.range i, ((1 / x) ^ (j + 1) - 1) / (j + 1 : ℝ) = 1

/-- The first-order approximation `t'_i = 1-c/i`, zero-indexed. -/
noncomputable def tPrime (c : ℝ) (i : ℕ) : ℝ :=
  1 - c / (i + 1 : ℝ)

/-- The defining equation for the positive constant `c` in Lemma 22. -/
noncomputable def IsSamuelsC (c : ℝ) : Prop :=
  0 < c ∧ (∫ x in (0 : ℝ)..1, (Real.exp (c * x) - 1) / x) = 1

/-- Samuels' constant. The coefficient is `e^c - 1 - c`, as derived on printed p.35; the
displayed `e^{-c}` coefficient in Eq. (10) is a typographical error. -/
noncomputable def samuelsGamma (c : ℝ) : ℝ :=
  Real.exp (-c) + (Real.exp c - 1 - c) *
    ∫ x in Ioi (1 : ℝ), x⁻¹ * Real.exp (-c * x)

end SecSampling.Supplement


