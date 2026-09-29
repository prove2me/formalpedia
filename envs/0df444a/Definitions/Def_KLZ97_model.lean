-- Prove2me | Definitions.Def_KLZ97_model
-- name    : KLZ97_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T12:27:33.157182+00:00
-- url     : https://prove2.me/theorems/676cff5b-a989-4893-a624-1bc5d263cb22
-- title:
--   Concatenated error parameter and quasi-independent error models
-- statement:
--   The definition layer for the threshold analysis of Knill, Laflamme and Zurek.
--
--   **Concatenated failure parameter.** One level of the fault tolerant construction turns a physical failure parameter $p$ into $f p^2$, where $f$ counts the minimal pairs of error locations that can make an encoded gate fail. `levelError` iterates this reduction: $E_0 = p$ and $E_{h+1} = f E_h^2$, so $E_h$ is the failure parameter of an encoded gate after $h$ levels of concatenation.
--
--   **Error models.** For a network whose error locations are indexed by a finite set $\mathrm{locs}$, with $F_i$ the event that location $i$ fails, the quasi-independent stochastic model with error probability $p$ asks that
--   $$\mu\Big(\bigcap_{i \in S} F_i\Big) \le p^{|S|}$$
--   for every set $S \subseteq \mathrm{locs}$ of error locations, and the quasi-independent monotonic model with constant $C$ relaxes this to $C p^{|S|}$. Probabilities (or strengths) take values in $[0, \infty]$.
-- source:
--   Knill, Laflamme, Zurek, Resilient Quantum Computation: Error Models and Thresholds, arXiv:quant-ph/9702058v1, https://arxiv.org/abs/quant-ph/9702058, Sections I.B (error models) and I.F (concatenation)

import Mathlib

namespace KLZ97

/-- `levelError f p h` is the failure parameter of an encoded gate at concatenation
level `h`, obtained from the physical failure parameter `p` by iterating the
one-level reduction `p ↦ f * p ^ 2`, where `f` is the number of minimal pairs of
error locations that can make an encoded gate fail. -/
noncomputable def levelError (f p : ℝ) : ℕ → ℝ
  | 0 => p
  | h + 1 => f * levelError f p h ^ 2

@[simp] theorem levelError_zero (f p : ℝ) : levelError f p 0 = p := rfl

@[simp] theorem levelError_succ (f p : ℝ) (h : ℕ) :
    levelError f p (h + 1) = f * levelError f p h ^ 2 := rfl

/-- The quasi-independent **stochastic** error model with error probability `p`,
for a network whose error locations are indexed by the finite set `locs` and whose
failure event at location `i` is `fail i`: for every set `S` of error locations,
the probability that all locations of `S` fail is at most `p ^ |S|`. -/
def QuasiIndepStochastic {Ω ι : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (locs : Finset ι) (fail : ι → Set Ω) (p : ENNReal) : Prop :=
  ∀ S : Finset ι, S ⊆ locs → μ (⋂ i ∈ S, fail i) ≤ p ^ S.card

/-- The quasi-independent **monotonic** error model with error parameter `p` and
constant `C`: for every set `S` of error locations, the strength of the summands in
which all locations of `S` have failed is at most `C * p ^ |S|`. -/
def QuasiIndepMonotone {Ω ι : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (locs : Finset ι) (fail : ι → Set Ω) (C p : ENNReal) : Prop :=
  ∀ S : Finset ι, S ⊆ locs → μ (⋂ i ∈ S, fail i) ≤ C * p ^ S.card

end KLZ97


