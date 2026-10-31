-- Prove2me | Definitions.Def_RiskBargaining_Instance_split
-- name    : RiskBargaining_Instance_split
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:25:56.333995+00:00
-- url     : https://prove2.me/theorems/00ea6b5a-d03b-4250-a438-6cf81ef82398
-- title:
--   The game obtained by splitting a player into $\ell$ players
-- statement:
--   Given an instance $(R,M,\mathcal A)$, a player $i$ and $\ell\ge 1$, the **associated game** $(R',M,\mathcal A')$ has player set $N'=N\setminus\{i\}\cup\{(i,k)\mid k=1,\dots,\ell\}$ and
--   $$
--   R'_j=R_j\ \ (j\ne i),\qquad R'_{ik}=R_i/\ell,\qquad \mathcal A'_j=\mathcal A_j\ \ (j\ne i),\qquad \mathcal A'_{ik}=\mathcal A_i\qquad (k=1,\dots,\ell).
--   $$
--   This is the game that Axiom 3 compares with the original one.
--
--   **Formalization Note** $N'$ is the type `{j // j ≠ i} ⊕ Fin ℓ`, and $\ell$ is a positive natural number (`ℕ+`), which excludes the empty split.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Axiom 3, p.9

import Mathlib
import Definitions.Def_RiskBargaining_Instance

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}

/-- **The game associated with `(R, M, 𝒜)` by splitting player `i` into `ℓ` players.**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Axiom 3, p.9: `N′ = N \ {i} ∪ {(i, k) | k = 1, …, ℓ}`, `R′_j = R_j`, `R′_ik = R_i / ℓ`,
`𝒜′_j = 𝒜_j`, `𝒜′_ik = 𝒜_i`, with `M` unchanged.

**Formalization Note.** `N′` is `{j // j ≠ i} ⊕ Fin ℓ`, and `ℓ : ℕ+` enforces `ℓ ≥ 1`. `R_i / ℓ` is
`(ℓ : ℝ)⁻¹ • R i`. -/
noncomputable def Instance.split (I : Instance μ p X ι) (i : ι) (ℓ : ℕ+) :
    Instance μ p X ({j // j ≠ i} ⊕ Fin ℓ) where
  R := Sum.elim (fun j => I.R j) (fun _ => ((ℓ : ℕ) : ℝ)⁻¹ • I.R i)
  M := I.M
  A := Sum.elim (fun j => I.A j) (fun _ => I.A i)
  coherent := by
    rintro (j | k)
    · exact I.coherent j
    · exact I.coherent i
  cont_M := I.cont_M

end RiskBargaining


