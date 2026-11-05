-- Prove2me | Definitions.Def_MayersQKD_Attack
-- name    : MayersQKD_Attack
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:26.931857+00:00
-- url     : https://prove2.me/theorems/7fb7bd50-c620-4dbc-8661-c6a4d560c7d5
-- title:
--   Attacks by Bob on STRING-QOT
-- statement:
--   An attack on the protocol with $n$ photons, $r$ redundant bits and a string of length $m$ consists of
--
--   1. a finite set of seeds with any distribution, Bob's private randomness;
--   2. the committed bases $\hat\theta$, as a function of the seed;
--   3. for each seed, a measurement $\{M_{\hat w}\}$ of the photons into a finite-dimensional memory, with $\sum_{\hat w}M_{\hat w}^\dagger M_{\hat w}=\mathbf I$;
--   4. a rule giving $(E_0,E_1)$ or "stop" from the seed, $\hat w$, $R$ and $\theta$, which answers a valid pair and stops only when no valid pair exists;
--   5. a finite set of outcomes and, for each transcript $t$, a measurement $\{K_y(t)\}$ of the memory.
--
--   The transcript is what Bob has seen before the final measurement: the seed, $\hat w$, $R$, and, on acceptance of the test, $\theta$ and, unless the protocol stopped, $(E_0,E_1)$, $c$, $f$, $s$, $a$ and $w[\bar E_c]$.
--
--   This is the class of attacks over which the goal quantifies; an honest Bob is an instance.
--
--   **Formalization Note** The commitments are ideal, as the abstract and §1 assume: the committed values are the classical $\hat\theta$ and $\hat w$. Finite dimension and finite outcomes lose nothing, because the range of $M_{\hat w}$ has dimension at most $2^n$ and a countable final measurement is a limit of finite coarse-grainings. By §6, Bob does not measure at step 6, so the rule sees no quantum outcome.
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §5, p.7; §6, pp.8–9

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_MayersQKD_Bits
import Definitions.Def_MayersQKD_T0
import Definitions.Def_MayersQKD_IsMeasurement

namespace MayersQKD

open WildeQIT

/-- Mayers, arXiv:quant-ph/9606003v1, §5 p.7, steps 6–7 and §6 p.8: what Bob receives after a pair
is chosen: the pair `(E₀, E₁)`, the bit `c`, the matrix `f` (that is, `g` and `h`), the strings
`s` and `a`, and the bits `w[Ē_c]` (announced "generously" at the end, p.8, as `offBlock`). -/
abbrev Step7 (n r m : ℕ) : Type :=
  (Finset (Fin n) × Finset (Fin n)) × Bool × HashMatrix r m (blockLen n) × Bits r × Bits m × Bits n

/-- Mayers, arXiv:quant-ph/9606003v1, §6, pp.8–9: the classical record Bob holds before his final
measurement: his seed, `ŵ`, `R`, and, if the test result is accepted, `θ` and, unless the
protocol stops at step 6, the step-7 announcements. The test result is the outer `Option`.

**Formalization Note.** After a rejected test nothing further is announced, so the outer value is
`none`; after "stop" at step 6 the inner value is `none`. -/
abbrev Transcript (Seed : Type) (n r m : ℕ) : Type :=
  Seed × Bits n × Finset (Fin n) × Option (Bases n × Option (Step7 n r m))

/-- Mayers, arXiv:quant-ph/9606003v1, §5 p.7 and §6 pp.8–9: an attack by Bob on STRING-QOT with `n`
photons, `r` redundant bits and a string of length `m`.

* `Seed`, `seedLaw`: Bob's private randomness, with any distribution.
* `commit`: the committed bases `θ̂` of step 2, as a function of the seed.
* `Mem`, `M`: the measurement `{M_ŵ}` of step 4 on the photons, with the residual state kept in a
  finite-dimensional memory.
* `sel`: the rule of step 6 giving `(E₀, E₁)` or "stop".
* `Y`, `K`: the final measurement of step 8, which may depend on everything Bob has seen.

**Formalization Note.** The commitments are ideal (abstract; §1): Bob's committed values are the
classical `θ̂` and `ŵ`. Finite dimension and finite outcome sets lose nothing: the range of `M_ŵ`
has dimension at most `2ⁿ`, and a countable final measurement is a limit of finite
coarse-grainings. `θ̂` need not be uniform for a dishonest Bob, and `sel` is any function of the
seed and the public data. An honest rule (including a uniformly random one, through the seed) is
an instance. By §6, p.8, Bob does not measure at step 6, so `sel` sees no quantum outcome. -/
structure Attack (n r m : ℕ) where
  /-- Bob's private randomness. -/
  Seed : Type
  [seedFintype : Fintype Seed]
  /-- The distribution of the seed. -/
  seedLaw : FinDist Seed
  /-- The committed bases `θ̂`. -/
  commit : Seed → Bases n
  /-- A basis of Bob's memory. -/
  Mem : Type
  [memFintype : Fintype Mem]
  /-- The operation `M_ŵ` on the photons at step 4. -/
  M : Seed → Bits n → (Photons n →ₗ[ℂ] EuclideanSpace ℂ Mem)
  /-- `∑_ŵ M_ŵ† M_ŵ = I`. -/
  M_complete : ∀ s, IsMeasurement (M s)
  /-- The rule choosing `(E₀, E₁)` at step 6 from the seed, `ŵ`, `R`, `θ`. -/
  sel : Seed → Bits n → Finset (Fin n) → Bases n → Option (Finset (Fin n) × Finset (Fin n))
  /-- A pair is valid, and "stop" occurs only when no valid pair exists. -/
  sel_valid : ∀ s what R θ, SelValid θ (commit s) R (sel s what R θ)
  /-- The outcomes of the final measurement. -/
  Y : Type
  [yFintype : Fintype Y]
  /-- The final measurement on the memory, given the transcript. -/
  K : Transcript Seed n r m → Y → (EuclideanSpace ℂ Mem →ₗ[ℂ] EuclideanSpace ℂ Mem)
  /-- `∑_y K_y† K_y = I` for every transcript. -/
  K_complete : ∀ t, IsMeasurement (K t)

attribute [instance] Attack.seedFintype Attack.memFintype Attack.yFintype

end MayersQKD


