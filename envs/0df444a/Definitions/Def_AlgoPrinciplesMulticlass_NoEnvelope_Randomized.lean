-- Prove2me | Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Randomized
-- name    : AlgoPrinciplesMulticlass_NoEnvelope_Randomized
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:28:07.427699+00:00
-- url     : https://prove2.me/theorems/25c7e44a-3b40-4c6d-a985-099cd23e3d5f
-- title:
--   Randomized learners, their PAC guarantee and their image im(A) (§3.1)
-- statement:
--   A **randomized learner** consists of a probability space $(\Omega,\mu)$ of internal randomness and, for every $\omega\in\Omega$, a learner $A_\omega:(X\times Y)^{<\omega}\to Y^X$ in the sense of §2, such that every prediction $\omega\mapsto A_\omega(S)(x)$ (for every finite sample $S$ and point $x$) is a measurable function of $\omega$, with every subset of $Y$ measurable. Its failure probability at a target $h^\star$, distribution $D$, size $m$ and accuracy $\varepsilon$ is
--   $$\Pr_{S\sim D^m,\ \omega\sim\mu}\big[L_D(A_\omega(S),h^\star)>\varepsilon\big],$$
--   taken under the product of $D^m$ (the sample, labeled by $h^\star$) and $\mu$. It **PAC learns** $\mathcal H$ if for every $\varepsilon,\delta\in(0,1)$ there is $n(\varepsilon,\delta)$ such that this probability is at most $\delta$ for all $m\ge n(\varepsilon,\delta)$, all $h^\star\in\mathcal H$ and all distributions $D$ on $X$. Its **image** is
--   $$\operatorname{im}(A)=\{A_\omega(S):\ \omega\in\Omega,\ S\in(X\times Y)^{<\omega}\},$$
--   every hypothesis it outputs for some sample and some value of its randomness.
--
--   The proof of Theorem 3.1 shows that every *possibly randomized* PAC learner for the constructed class has an image of infinite DS dimension; §2 defines only deterministic learners, and this is the model of randomization used. A deterministic learner is the case of a one-point $\Omega$ (`RandLearner.ofLearner`).
--
--   **Formalization Note.** `RandLearner.{u} X Y` bundles `Ω : Type u`, its σ-algebra, the probability measure `μ`, the family `A : Ω → Learner X Y` and the measurability of `ω ↦ A ω m S x` (σ-algebra `⊤` on `Y`). `failProb` applies `(Measure.pi (fun _ => D)).prod μ` to the set of pairs `(xs, ω)` with `ENNReal.ofReal ε < popLoss D (A ω m (labelSample h⋆ xs)) h⋆`. On a countable domain this set is measurable, so the probability is an honest one.
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 18 (every (possibly randomized) PAC learner A, im(A)); p. 19 (A's internal randomness); p. 13, §2 (PAC learning)

import Mathlib
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_PAC

open MeasureTheory

namespace AlgoPrinciplesMulticlass.NoEnvelope

/-!
# Randomized learners and their image (§3.1, p. 18)

Asilis, Dughmi, Sharan, Sun, Teng, Wang, *Algorithmic Principles For Multiclass Learning Are
Hard To Come By*, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 18 ("every (possibly
randomized) PAC learner") and p. 6 / p. 18 (the image `im(A)`).

A randomized learner is a probability space `(Ω, μ)` of internal randomness together with a
deterministic learner `A ω` for each `ω`. The only regularity asked is that every prediction
`A ω m S x` is a measurable function of `ω` (with every set of labels measurable); a
deterministic learner is the case of a one-point `Ω`. Its failure probability is computed under
the product of the sample law `D^m` and `μ`, and its image is the union of the images of the
`A ω`.
-/

/-- A randomized learner: internal randomness `ω` drawn from a probability measure `μ` on `Ω`,
and a learner `A ω` for every `ω`, each prediction measurable in `ω`. -/
structure RandLearner.{u, v, w} (X : Type v) (Y : Type w) : Type (max (u + 1) v w) where
  /-- The space of internal randomness. -/
  Ω : Type u
  /-- Its σ-algebra. -/
  msΩ : MeasurableSpace Ω
  /-- The law of the internal randomness. -/
  μ : @Measure Ω msΩ
  /-- `μ` is a probability measure. -/
  isProb : @IsProbabilityMeasure Ω msΩ μ
  /-- The learner run with internal randomness `ω`. -/
  A : Ω → Learner X Y
  /-- Every prediction is a measurable function of the internal randomness. -/
  meas : ∀ (m : ℕ) (S : Fin m → X × Y) (x : X), @Measurable Ω Y msΩ ⊤ (fun ω => A ω m S x)

/-- The failure probability `P_{S∼D^m, ω∼μ}[L_D(A_ω(S), h⋆) > ε]` of a randomized learner,
under the product of `D^m` (the sample, labeled by `h⋆`) and the law `μ` of the randomness. -/
noncomputable def RandLearner.failProb {X Y : Type*} (R : RandLearner X Y) (hstar : X → Y)
    (D : @Measure X ⊤) (m : ℕ) (ε : ℝ) : ENNReal :=
  letI : MeasurableSpace X := ⊤
  letI : MeasurableSpace R.Ω := R.msΩ
  (Measure.pi (fun _ : Fin m => D)).prod R.μ
    {p : (Fin m → X) × R.Ω |
      ENNReal.ofReal ε < popLoss D (R.A p.2 m (labelSample hstar p.1)) hstar}

/-- A randomized learner PAC learns `H`: the §2 definition (p. 13) with the probability taken
over the sample and the internal randomness. -/
def RandLearner.PACLearns {X Y : Type*} (R : RandLearner X Y) (H : Set (X → Y)) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → ∀ hstar ∈ H, ∀ D : @Measure X ⊤, @IsProbabilityMeasure X ⊤ D →
      R.failProb hstar D m ε ≤ ENNReal.ofReal δ

/-- The image `im(A)` of a randomized learner: every hypothesis it outputs on some finite sample
for some value of its internal randomness. -/
def RandLearner.image {X Y : Type*} (R : RandLearner X Y) : Set (X → Y) :=
  {f | ∃ (ω : R.Ω) (m : ℕ) (S : Fin m → X × Y), R.A ω m S = f}

/-- A deterministic learner as a randomized one (one-point randomness). -/
noncomputable def RandLearner.ofLearner {X Y : Type*} (A : Learner X Y) : RandLearner.{0} X Y where
  Ω := Unit
  msΩ := ⊤
  μ := @Measure.dirac Unit ⊤ ()
  isProb := @Measure.dirac.isProbabilityMeasure Unit ⊤ ()
  A := fun _ => A
  meas := fun _ _ _ => @measurable_const Y Unit ⊤ ⊤ _

end AlgoPrinciplesMulticlass.NoEnvelope


