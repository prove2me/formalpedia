-- Prove2me | Definitions.Def_StochasticProg_Bounds_Partition
-- name    : StochasticProg_Bounds_Partition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:54:07.409933+00:00
-- url     : https://prove2.me/theorems/5f2caa6e-d8ed-4c47-b285-8611656b58a8
-- title:
--   Finite measurable partition of a probability space, with block weight and conditional mean
-- statement:
--   This bundle formalizes a **finite measurable partition of a probability space**, together with
--   each block's probability weight and conditional-mean accessor, as used throughout Birge &
--   Louveaux §8.2 (p. 346) to state the chapter's discrete bounding approximations.
--
--   A `Partition` (parameters: a measure $\mu$ on $\Omega$, a block count $\nu\in\mathbb N$)
--   consists of:
--   - a family of sets $S_1,\dots,S_\nu \subseteq \Omega$ (indexed by $l < \nu$),
--   - a proof each $S_l$ is $\mu$-measurable,
--   - a proof the $S_l$ are pairwise disjoint,
--   - a proof they cover $\Omega$: $\bigcup_l S_l = \Omega$,
--   - a proof each has positive measure: $\mu(S_l) \ne 0$ for every $l$.
--
--   Two derived quantities are defined on top of a partition: the **block weight**
--   $$
--   p_l = P.\mathrm{weight}(l) = \mu(S_l)_{\mathbb R} ,
--   $$
--   the real number underlying the extended-real measure $\mu(S_l)$ (via `ENNReal.toReal`),
--   matching the book's $p_l = P[\xi\in S_l]$; and, for a random vector $\xi:\Omega\to E$ valued in
--   a complete normed real vector space $E$, the **block conditional mean**
--   $$
--   \xi^l = P.\mathrm{condMean}(\xi,l) = p_l^{-1}\int_{S_l}\xi\,d\mu ,
--   $$
--   the Bochner-integral average of $\xi$ over $S_l$, matching the book's
--   $\xi^l=\mathbb E[\xi\mid S_l]$ (p. 346).
--
--   **Formalization Note** The partition is defined directly on the sample space $\Omega$ — blocks
--   $S_l\subseteq\Omega$ — rather than on the support $\Xi$ of $\xi$; this is the pulled-back-sets
--   convention noted in the mission description and is mathematically equivalent to partitioning
--   $\Xi$ itself. `condMean` is *forced* to equal the conditional mean by its own definition (a
--   quotient of an integral by the block's probability); it cannot be weakened to return an
--   arbitrary point of $S_l$.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, p. 346, Chapter 8, Section 8.2 (before Theorem 1)

import Mathlib

open MeasureTheory

namespace StochasticProg.Bounds

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite measurable partition of a probability space `(Ω, μ)` into `ν` blocks of positive
probability, following Birge & Louveaux §8.2 (p. 346). The book partitions the support `Ξ` of
the random vector `ξ` into regions `S_l`; here the blocks `S l` are the pulled-back sets
`ξ⁻¹(region_l) ⊆ Ω` directly, which is equivalent and keeps every integral over `Ω`. -/
structure Partition (μ : Measure Ω) (ν : ℕ) where
  S : Fin ν → Set Ω
  measurable : ∀ l, MeasurableSet (S l)
  disjoint : Pairwise (Function.onFun Disjoint S)
  cover : ⋃ l, S l = Set.univ
  pos : ∀ l, μ (S l) ≠ 0

variable {μ : Measure Ω} {ν : ℕ}

/-- The block probability `p_l = P[ξ ∈ S_l]` (Birge & Louveaux, p. 346, before Theorem 1). -/
noncomputable def Partition.weight (P : Partition μ ν) (l : Fin ν) : ℝ :=
  (μ (P.S l)).toReal

/-- The block conditional mean `ξ^l = E[ξ | S_l]` (Birge & Louveaux, p. 346, before Theorem 1),
for a random vector `ξ : Ω → E` valued in a complete normed real vector space `E`. -/
noncomputable def Partition.condMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Partition μ ν) (ξ : Ω → E) (l : Fin ν) : E :=
  (P.weight l)⁻¹ • ∫ ω in P.S l, ξ ω ∂μ

end StochasticProg.Bounds


