-- Prove2me | Definitions.Def_MulticalibrationERM_Oracle_BlackBox
-- name    : MulticalibrationERM_Oracle_BlackBox
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:50:14.751201+00:00
-- url     : https://prove2.me/theorems/b3737b2a-fb11-4d3b-a44b-44f97924fbbc
-- title:
--   Definition 3.10, §3.4 — q-query black-box ERM learners, their failure probability, instances, and the lower-bound parameters
-- statement:
--   A **$q$-query black-box ERM learner** using $n$ labeled samples on the input set $X$ (`BBLearner X n q Ωl`), for a fixed accuracy $\varepsilon$: it receives $n$ samples and a private seed $\rho\in\Omega_l$ (unlimited randomness, unlimited computation); its $k$-th oracle query ($k<q$) is any finite list of weighted inputs chosen from the samples, the seed and the $k$ auditors returned so far; after the $q$-th answer it outputs a finitely supported randomized predictor (values in $[0,1]$). It has no other access to the class. A learner wanting fewer calls submits dummy queries. The oracle may break ties by any rule; the learner does not know it.
--
--   `bbFailProb A μl O νo D ε` is the probability that the output has $\mathrm{MC}>\varepsilon$, when the samples are i.i.d. $D$, the learner seed has law $\mu_l$ and the oracle seeds are i.i.d. $\nu_o$ (the outer measure of the failure event if it is not measurable). A `BBInstance` bundles a class $H$, a weighted ERM oracle for it (with seed law $\nu_o$) and a distribution $D$. `HiddenSigns J D` is the set of hidden signs $\tau\in\{\pm1\}^{[J]\times[D]}$ and 16 planted block-sign vectors $\theta^{(\ell)}\in\{\pm1\}^J$.
--
--   Parameters of §3.4 for $\varepsilon>0$, query budget $q$ and block size $D$ (`Dblk`), with $|X|=JD$:
--   $$\beta=8\varepsilon,\quad\kappa_{\mathrm{anc}}=2\lceil\log_2(1/\beta)\rceil+4,\quad\Delta_c=128\kappa_{\mathrm{anc}}\beta,\quad J=\lfloor1/(4\Delta_c)\rfloor,$$
--   $$d_0=\lceil16D\log(8|X|)\rceil,\qquad t=\log(1000|X|),\qquad A=\kappa_{\mathrm{anc}}^2+\log(1000q).$$
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), pp. 21–22, Definition 3.10, §3.4

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM

namespace MulticalibrationERM.Oracle

open MeasureTheory

/-! # Black-box ERM learners and the parameters of the lower bound

Okoroafor, *The Sample Complexity of Multicalibration with an ERM Oracle* (supplied preprint,
SHA256 654c7a81…), Definition 3.10 (p. 21) and the parameters of Section 3.4 (p. 22). -/

variable {X : Type*} [MeasurableSpace X]

/-- A `q`-query black-box ERM learner on the input set `X` that uses `n` labeled samples
(Definition 3.10), for a fixed accuracy `ε` (which it may use freely). Its private randomness is a
seed `ρ ∈ Ωl` (unlimited randomness); its computation is unrestricted. It has no access to
the class except through the oracle: the `k`-th query (`k < q`) is a finite weighted list of inputs
chosen from the samples, the seed, and the `k` auditors returned so far (adaptivity); after the
`q`-th answer it outputs a finitely supported randomized predictor. A learner that wants fewer
calls submits dummy queries and ignores their answers. -/
structure BBLearner (X : Type*) [MeasurableSpace X] (n q : ℕ) (Ωl : Type*) where
  query : (k : ℕ) → (Fin n → X × ℝ) → Ωl → (Fin k → (X → Bool)) → List (X × ℝ)
  output : (Fin n → X × ℝ) → Ωl → (Fin q → (X → Bool)) → RandPred X

variable {H : Set (X → Bool)} {Ωo : Type*} [MeasurableSpace Ωo] {n q : ℕ} {Ωl : Type*}

/-- The first `k` oracle answers in a run of the learner `A` against the oracle `O`, on samples
`s`, learner seed `ρ`, and oracle seeds `ω` (call `k` uses `ω k`). -/
def bbAnswers (A : BBLearner X n q Ωl) (O : ERMOracle X H 0 Ωo) (s : Fin n → X × ℝ) (ρ : Ωl)
    (ω : ℕ → Ωo) : (k : ℕ) → Fin k → (X → Bool)
  | 0 => Fin.elim0
  | k + 1 => Fin.snoc (α := fun _ => X → Bool) (bbAnswers A O s ρ ω k)
      (O.call (A.query k s ρ (bbAnswers A O s ρ ω k)) (ω k))

/-- The output predictor of a run. -/
def bbOutput (A : BBLearner X n q Ωl) (O : ERMOracle X H 0 Ωo) (s : Fin n → X × ℝ) (ρ : Ωl)
    (ω : ℕ → Ωo) : RandPred X :=
  A.output s ρ (bbAnswers A O s ρ ω q)

/-- The probability that the learner's output has multicalibration error greater than `ε`
(`n` i.i.d. samples from `D`, learner seed of law `μl`, i.i.d. oracle seeds of law `νo`). It is
the measure of the failure event; if the event is not measurable it is its outer measure, which
is never smaller than the probability of any measurable failure event it contains. -/
noncomputable def bbFailProb [MeasurableSpace Ωl] (A : BBLearner X n q Ωl) (μl : Measure Ωl)
    (O : ERMOracle X H 0 Ωo) (νo : Measure Ωo) (D : LabeledDist X) (ε : ℝ) : ENNReal :=
  ((Measure.pi fun _ : Fin n => D.μ).prod (μl.prod (Measure.infinitePi fun _ : ℕ => νo)))
    {p | ε < (bbOutput A O p.1 p.2.1 p.2.2).MC D H}

/-- An instance for a black-box ERM learner on the input set `X`: a class `H ⊆ {−1, +1}^X`, a
weighted ERM oracle for `H` (Definition 2.3; its randomness has law `νo` on `Ωo`), and a
distribution `D` over `X × [0, 1]`. -/
structure BBInstance (X : Type*) [MeasurableSpace X] (Ωo : Type*) [MeasurableSpace Ωo] where
  H : Set (X → Bool)
  O : ERMOracle X H 0 Ωo
  νo : Measure Ωo
  νo_prob : IsProbabilityMeasure νo
  D : LabeledDist X

/-- The hidden part of the hard instance of Section 3.4: the hidden signs `τ ∈ {−1, +1}^X`, one per
input of `X = [J] × [D]`, and the 16 planted block-sign vectors `θ⁽ℓ⁾ ∈ {−1, +1}^J` (`true` is
`+1`). -/
abbrev HiddenSigns (J Dblk : ℕ) := (Fin J × Fin Dblk → Bool) × (Fin 16 → Fin J → Bool)

/-! ### Parameters of Section 3.4 (p. 22) -/

/-- The gap `β = 8ε`. -/
def lbBeta (ε : ℝ) : ℝ := 8 * ε

/-- `κ_anc = 2⌈log₂(1/β)⌉ + 4`. -/
noncomputable def lbKappa (ε : ℝ) : ℝ := 2 * (⌈Real.logb 2 (1 / lbBeta ε)⌉ : ℝ) + 4

/-- The center spacing `Δ_c = 128 κ_anc β`. -/
noncomputable def lbDelta (ε : ℝ) : ℝ := 128 * lbKappa ε * lbBeta ε

/-- The number of blocks `J = ⌊1/(4Δ_c)⌋`. -/
noncomputable def lbJ (ε : ℝ) : ℕ := ⌊1 / (4 * lbDelta ε)⌋₊

/-- `d₀ = ⌈16 D log(8|X|)⌉` for `|X| = J·D`. -/
noncomputable def lbD0 (ε : ℝ) (Dblk : ℕ) : ℕ :=
  ⌈16 * (Dblk : ℝ) * Real.log (8 * ((lbJ ε * Dblk : ℕ) : ℝ))⌉₊

/-- `t = log(1000|X|)`. -/
noncomputable def lbT (ε : ℝ) (Dblk : ℕ) : ℝ := Real.log (1000 * ((lbJ ε * Dblk : ℕ) : ℝ))

/-- `A = κ_anc² + log(1000 q)`. -/
noncomputable def lbA (ε : ℝ) (q : ℕ) : ℝ := lbKappa ε ^ 2 + Real.log (1000 * q)

end MulticalibrationERM.Oracle


