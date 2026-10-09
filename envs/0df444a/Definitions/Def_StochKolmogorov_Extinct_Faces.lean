-- Prove2me | Definitions.Def_StochKolmogorov_Extinct_Faces
-- name    : StochKolmogorov_Extinct_Faces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:31.547685+00:00
-- url     : https://prove2.me/theorems/91d77fbb-9f2d-48fc-b4b1-83acb854667e
-- title:
--   pp. 5–6 — boundary faces and Assumption 1.3
-- statement:
--   For a boundary ergodic invariant measure $\mu$, let $I_\mu$ be the coordinates with positive abundance on a set of positive $\mu$-measure. The associated face is
--
--   $$\mathbb R^\mu_+=\{x\in\mathbb R^n_+:x_i=0\text{ for }i\notin I_\mu\}.$$
--
--   The module defines its relative interior and boundary, the boundary ergodic measures $M_\mu$ supported on the latter, and the classes $M^1$ and $M^2$. A measure $\mu$ satisfies Assumption 1.3 when every missing species has negative invasion rate at $\mu$ and, if $I_\mu$ is nonempty, every finite convex combination of measures in $M_\mu$ has a positive invasion rate for some species in $I_\mu$.
--
--   This separates the attracting boundary face from faces of smaller dimension.
--
--   **Formalization Note** The paper describes $I_\mu$ through the support of an ergodic measure. Here $I_\mu=\{i:\mu(x_i>0)>0\}$, an equivalent reading for those measures. A maximum over a finite set is rendered by the equivalent existential or universal inequality. The paper's printed “$x_i\in I_\mu$” is read as “$i\in I_\mu$.”
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, §1.1, pp. 5–6, Assumption 1.3, (1.6)–(1.9)

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Model

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

open Classical in
/-- `I_mu` (p. 5): the coordinates that are not `mu`-a.s. zero. The paper's `supp(mu) = ℝ^mu₊` is then a
property of ergodic `mu`, not part of the definition. -/
noncomputable def supp {n : ℕ} (mu : Measure (SDEState n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => mu {x | 0 < x i} ≠ 0)

/-- `ℝ^mu₊ = {x ∈ ℝⁿ₊ : xᵢ = 0 if i ∈ I^c_mu}` (p. 5). -/
def face {n : ℕ} (mu : Measure (SDEState n)) : Set (SDEState n) :=
  {x | x ∈ orthant n ∧ ∀ i, i ∉ supp mu → x i = 0}

/-- `ℝ^{mu,◦}₊ = {x ∈ ℝⁿ₊ : xᵢ = 0 if i ∈ I^c_mu, xᵢ > 0 if i ∈ I_mu}` (p. 5). -/
def faceInt {n : ℕ} (mu : Measure (SDEState n)) : Set (SDEState n) :=
  {x | x ∈ face mu ∧ ∀ i, i ∈ supp mu → 0 < x i}

/-- `∂ℝ^mu₊ = ℝ^mu₊ \ ℝ^{mu,◦}₊` (p. 5). -/
def faceBdry {n : ℕ} (mu : Measure (SDEState n)) : Set (SDEState n) := face mu \ faceInt mu

/-- `M_mu = {ν′ ∈ M : supp(ν′) ⊂ ∂ℝ^mu₊}` (p. 6); `∂ℝ^mu₊` is closed, so this is `ν′((∂ℝ^mu₊)ᶜ) = 0`. -/
def subErgodic {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (mu : Measure (SDEState n)) :
    Set (Measure (SDEState n)) :=
  {ν | ν ∈ bdryErgodic P X ∧ ν ((faceBdry mu)ᶜ) = 0}

/-- Assumption 1.3 for a given `mu ∈ M` (p. 6): (1.6) `max_{i ∈ I^c_mu} λᵢ(mu) < 0`, and, if
`ℝ^mu₊ ≠ {0}` (i.e. `I_mu ≠ ∅`), (1.7) `max_{i ∈ I_mu} λᵢ(ν) > 0` for every `ν ∈ Conv(M_mu)`. -/
def Assumption13 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (mu : Measure (SDEState n)) : Prop :=
  mu ∈ bdryErgodic P X ∧ (∀ i, i ∉ supp mu → lyap C i mu < 0) ∧
    ((supp mu).Nonempty → ∀ ν ∈ conv (subErgodic P X mu), ∃ i ∈ supp mu, 0 < lyap C i ν)

/-- `M¹` of (1.8). -/
def M1 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Set (Measure (SDEState n)) :=
  {mu | Assumption13 P C X mu}

/-- `M² = M \ M¹` of (1.9). -/
def M2 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Set (Measure (SDEState n)) :=
  bdryErgodic P X \ M1 P C X

end StochKolmogorov.Extinct


