-- Prove2me | Definitions.Def_UncrowdedColoring_IsLipschitzTrials
-- name    : UncrowdedColoring_IsLipschitzTrials
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:10:31.462483+00:00
-- url     : https://prove2.me/theorems/1dc12289-3237-4621-b060-adcfdb2ae53b
-- title:
--   $\mu$-Lipschitz and $r$-certifiable functions of independent trials
-- statement:
--   Let $X$ be a function of independent trials. $X$ is **$\mu$-Lipschitz** if changing the outcome of one trial changes $X$ by at most $\mu$. $X$ is **$r$-certifiable** if for every integer $s\ge 1$, whenever $X\ge s$ there is a set of at most $rs$ trials whose outcomes certify $X\ge s$: changing the other trials cannot bring $X$ below $s$.
--
--   These are the hypotheses of Talagrand's inequality in the form used for the concentration steps of the nibble.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Definition 3.6, p.15

import Mathlib

namespace UncrowdedColoring

/-- **`µ`-Lipschitz function of independent trials** (Definition 3.6, p.15): "if (t_1, …, t_n) and
(t′_1, …, t′_n) differ in exactly one coordinate, then |X(t_1, …, t_n) − X(t′_1, …, t′_n)| ≤ µ."
(Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.15.) -/
def IsLipschitzTrials {ι : Type*} {Ω : ι → Type*} (X : (∀ i, Ω i) → ℕ) (μ : ℝ) : Prop :=
  ∀ x y : ∀ i, Ω i, (∃ i, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j) →
    |(X x : ℝ) - (X y : ℝ)| ≤ μ

/-- **`r`-certifiable function of independent trials** (Definition 3.6, p.15): "for every integer
s ≥ 1, whenever X ≥ s, there exists a set of t ≤ rs trials T_{i_1}, …, T_{i_t} whose outcomes certify
X ≥ s, i.e., changing the outcomes of any of the other trials cannot cause X to be less than s."
(Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.15.) -/
def IsCertifiableTrials {ι : Type*} {Ω : ι → Type*} (X : (∀ i, Ω i) → ℕ) (r : ℝ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∀ x : ∀ i, Ω i, s ≤ X x →
    ∃ I : Finset ι, (I.card : ℝ) ≤ r * s ∧ ∀ y : ∀ i, Ω i, (∀ i ∈ I, y i = x i) → s ≤ X y

end UncrowdedColoring


