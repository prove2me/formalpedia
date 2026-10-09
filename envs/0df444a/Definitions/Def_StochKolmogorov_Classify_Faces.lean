-- Prove2me | Definitions.Def_StochKolmogorov_Classify_Faces
-- name    : StochKolmogorov_Classify_Faces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:59.996992+00:00
-- url     : https://prove2.me/theorems/b22ccad9-0ae5-4995-b570-5c4661b2ef9d
-- title:
--   §1.1, pp. 5–6 — the index set I_µ, the faces ℝ^µ₊, ℝ^{µ,◦}₊, ∂ℝ^µ₊, M_µ, Assumption 1.3, M¹ and M²
-- statement:
--   For a probability measure $\mu$ on $\mathbb R^n_+$ this module defines the coordinates it charges and the face of the orthant it lives on, and then the sink condition of the paper.
--
--   1. $I_\mu = \{i : \mu(x_i > 0) > 0\}$ and $I^c_\mu$ its complement;
--   2. $\mathbb R^\mu_+ = \{x \in \mathbb R^n_+ : x_i = 0 \text{ for } i \in I^c_\mu\}$, its relative interior $\mathbb R^{\mu,\circ}_+$ (where moreover $x_i > 0$ for $i \in I_\mu$), and $\partial\mathbb R^\mu_+ = \mathbb R^\mu_+ \setminus \mathbb R^{\mu,\circ}_+$;
--   3. $\mathcal M_\mu = \{\nu' \in \mathcal M : \operatorname{supp}(\nu') \subset \partial\mathbb R^\mu_+\}$;
--   4. **Assumption 1.3** for $\mu \in \mathcal M$:
--   $$
--   \max_{i \in I^c_\mu}\lambda_i(\mu) < 0 \quad (1.6),\qquad\text{and, if } \mathbb R^\mu_+ \ne \{0\},\quad \max_{i\in I_\mu}\lambda_i(\nu) > 0 \text{ for every } \nu \in \mathrm{Conv}(\mathcal M_\mu) \quad (1.7);
--   $$
--   5. $\mathcal M^1 = \{\mu \in \mathcal M : \mu \text{ satisfies Assumption 1.3}\}$ (1.8) and $\mathcal M^2 = \mathcal M \setminus \mathcal M^1$ (1.9).
--
--   The measures of $\mathcal M^1$ are the "sinks": boundary ergodic measures near whose support the absent species decay. They index the possible long-run behaviours in Theorem 1.3.
--
--   **Formalization Note** The paper defines $I_\mu$ through $\operatorname{supp}(\mu) = \mathbb R^\mu_+$, a property of ergodic $\mu$; here $I_\mu$ is defined directly as the set of coordinates that are not $\mu$-a.s. zero, which agrees with the paper's on $\mathcal M$. $\mathbb R^\mu_+ \ne \{0\}$ is written as $I_\mu \ne \emptyset$, and $\operatorname{supp}(\nu') \subset \partial\mathbb R^\mu_+$ as $\nu'((\partial\mathbb R^\mu_+)^c) = 0$ ($\partial\mathbb R^\mu_+$ is closed).
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §1.1, p. 5 (faces), p. 6, Assumption 1.3, (1.6)–(1.9)

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify

open EthierKurtz

open Classical in
/-- `I_μ` (p. 5): the coordinates that are not `μ`-a.s. zero. The paper's `supp(μ) = ℝ^μ₊` is then a
property of ergodic `μ`, not part of the definition. -/
noncomputable def supp {n : ℕ} (μ : Measure (SDEState n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => μ {x | 0 < x i} ≠ 0)

/-- `ℝ^μ₊ = {x ∈ ℝⁿ₊ : xᵢ = 0 if i ∈ I^c_μ}` (p. 5). -/
def face {n : ℕ} (μ : Measure (SDEState n)) : Set (SDEState n) :=
  {x | x ∈ orthant n ∧ ∀ i, i ∉ supp μ → x i = 0}

/-- `ℝ^{μ,◦}₊ = {x ∈ ℝⁿ₊ : xᵢ = 0 if i ∈ I^c_μ, xᵢ > 0 if i ∈ I_μ}` (p. 5). -/
def faceInt {n : ℕ} (μ : Measure (SDEState n)) : Set (SDEState n) :=
  {x | x ∈ face μ ∧ ∀ i, i ∈ supp μ → 0 < x i}

/-- `∂ℝ^μ₊ = ℝ^μ₊ \ ℝ^{μ,◦}₊` (p. 5). -/
def faceBdry {n : ℕ} (μ : Measure (SDEState n)) : Set (SDEState n) := face μ \ faceInt μ

/-- `M_μ = {ν′ ∈ M : supp(ν′) ⊂ ∂ℝ^μ₊}` (p. 6); `∂ℝ^μ₊` is closed, so this is `ν′((∂ℝ^μ₊)ᶜ) = 0`. -/
def subErgodic {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (μ : Measure (SDEState n)) :
    Set (Measure (SDEState n)) :=
  {ν | ν ∈ bdryErgodic P X ∧ ν (faceBdry μ)ᶜ = 0}

/-- Assumption 1.3 for a given `μ ∈ M` (p. 6): (1.6) `max_{i ∈ I^c_μ} λᵢ(μ) < 0`, and, if
`ℝ^μ₊ ≠ {0}` (i.e. `I_μ ≠ ∅`), (1.7) `max_{i ∈ I_μ} λᵢ(ν) > 0` for every `ν ∈ Conv(M_μ)`. -/
def Assumption13 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (μ : Measure (SDEState n)) : Prop :=
  μ ∈ bdryErgodic P X ∧ (∀ i, i ∉ supp μ → lyap C i μ < 0) ∧
    ((supp μ).Nonempty → ∀ ν ∈ conv (subErgodic P X μ), ∃ i ∈ supp μ, 0 < lyap C i ν)

/-- `M¹` of (1.8). -/
def M1 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Set (Measure (SDEState n)) :=
  {μ | Assumption13 P C X μ}

/-- `M² = M \ M¹` of (1.9). -/
def M2 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Set (Measure (SDEState n)) :=
  bdryErgodic P X \ M1 P C X

end StochKolmogorov.Classify


