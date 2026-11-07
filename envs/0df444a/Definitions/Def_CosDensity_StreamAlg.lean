-- Prove2me | Definitions.Def_CosDensity_StreamAlg
-- name    : CosDensity_StreamAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:44.646873+00:00
-- url     : https://prove2.me/theorems/cd149aa2-5d46-4a40-aa8d-744685adc1dc
-- title:
--   Randomized one-pass streaming algorithms with a public seed
-- statement:
--   A **randomized one-pass streaming algorithm** over vectors of $E$ has a finite set $S$ of memory configurations and a random seed $\omega$ drawn once from a probability space $(\Omega,\mu)$. On a stream $(x_0,\dots,x_{n-1})$ of length $n$ it starts in the configuration $\mathrm{init}(\omega,n)$, updates it to $\mathrm{step}(\omega,n,t,x_t,\cdot)$ at each position $t=0,\dots,n-1$, and outputs the real number $\mathrm{out}(\omega,n,s_n)$ computed from its final configuration $s_n$. Its **memory** is $\log_2|S|$ bits.
--
--   An event about the seed holds **with probability at least $c$** if some measurable event of $\mu$-measure at least $c$ is contained in the set of seeds where it holds. A "1/3-error" algorithm succeeds with probability at least $2/3$ in this sense.
--
--   This is the model in which the paper's space lower bounds are stated: the algorithm reads the stream once and computes its answer from its final memory configuration.
--
--   **Formalization Note** The seed is persistent and is not charged as memory (it plays the role of the paper's fully random hash functions); fresh randomness at every step is a special case. The transitions may depend on the stream length and on the position, which only enlarges the class of algorithms.
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §3, p.12 ("The algorithm is allowed to make a sequential pass over the stream while using limited memory. At the end of the stream, it computes the target function on P using its final memory configuration."), pp.12–13 (fully random hash functions; memory measured in bits)

import Mathlib

open MeasureTheory

namespace CosDensity

/-!
# Randomized one-pass streaming algorithms with a public seed

Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density Moments*, arXiv:2609.06925
(held version, sha256 f4d4df22…), §3, p.12 (pdf_page 13): "The algorithm is allowed to make a
sequential pass over the stream while using limited memory. At the end of the stream, it computes
the target function on P using its final memory configuration."

**Formalization Note.**
* The memory configurations form a finite type `S`; the memory is `log₂ |S|` bits
  (`memoryBits`, a real number, computed with `Real.logb 2`).
* Randomness is a seed `ω` drawn once from a probability space `(Ω, μ)` and read throughout the
  pass (a persistent public seed, the paper's "fully random hash functions", pp.12–13). The seed
  is not charged as memory. Fresh per-step randomness is a special case.
* The initial state may depend on the stream length `n`, each transition on `n` and on the
  position `t` (`0`-based), and the output map on `n`. This only enlarges the class of algorithms.
* `SucceedsWP μ good c` means: some measurable event of `μ`-measure at least `c` is contained in
  the set of seeds where `good` holds (an inner-measure lower bound; the set itself need not be
  measurable). "1/3-error" is `SucceedsWP μ good (2/3)`.
-/

/-- Some measurable event of measure at least `c` lies inside `{ω | good ω}`. -/
def SucceedsWP {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (good : Ω → Prop)
    (c : ENNReal) : Prop :=
  ∃ A : Set Ω, MeasurableSet A ∧ A ⊆ {ω | good ω} ∧ c ≤ μ A

/-- A randomized one-pass streaming algorithm over vectors of `E`, with seed space `Ω` and
memory configurations `S`. -/
structure StreamAlg (E Ω S : Type*) where
  /-- Initial memory configuration, from the seed and the stream length. -/
  init : Ω → ℕ → S
  /-- Transition: seed, stream length, position, arriving vector, current configuration. -/
  step : Ω → ℕ → ℕ → E → S → S
  /-- Output: seed, stream length, final configuration. -/
  out : Ω → ℕ → S → ℝ

namespace StreamAlg

variable {E Ω S : Type*}

/-- Process the vectors `xs`, the first of which sits at position `t`, from configuration `s`,
on a stream of total length `n`. -/
def runFrom (A : StreamAlg E Ω S) (ω : Ω) (n : ℕ) : ℕ → List E → S → S
  | _, [], s => s
  | t, x :: xs, s => runFrom A ω n (t + 1) xs (A.step ω n t x s)

/-- The final memory configuration after one pass over `P` with seed `ω`. -/
def run (A : StreamAlg E Ω S) (ω : Ω) (P : List E) : S :=
  runFrom A ω P.length 0 P (A.init ω P.length)

/-- The algorithm's estimate on `P` with seed `ω`. -/
def estimate (A : StreamAlg E Ω S) (ω : Ω) (P : List E) : ℝ :=
  A.out ω P.length (run A ω P)

end StreamAlg

/-- The memory, in bits, of an algorithm with configuration set `S`: `log₂ |S|`. -/
noncomputable def memoryBits (S : Type*) [Fintype S] : ℝ :=
  Real.logb 2 (Fintype.card S)

end CosDensity


