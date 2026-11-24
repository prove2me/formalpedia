-- Prove2me | Definitions.Def_FBMStrongSim_RecordBreak_Supplement_SamplingModel
-- name    : FBMStrongSim_RecordBreak_Supplement_SamplingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:26:07.258068+00:00
-- url     : https://prove2.me/theorems/b5c28062-076e-48c6-9b4b-63eda5c34243
-- title:
--   Conditional fBM law and the change-of-measure algorithms 3–4
-- statement:
--   Let $B$ have the published fBM model. The regular conditional law $\kappa_n(x)$ is the law of all dyadic coordinates given the level-$n$ vector $x$, computed by `condDistrib`. For a dyadic path $v$, write $b_{l,k}(v)=(v_{l,2k-2}+v_{l,2k})/2-v_{l,2k-1}$. With $\ell_l=2^{-(H-\delta)l}$, Section 4 uses strict records $|b_{l,k}|>\rho\ell_l$. The event $\operatorname{FirstRecord}(n,m)$ asserts a record at $n+m$ and none at earlier levels strictly after $n$.
--
--   The proposal probabilities and threshold are computed from the data:
--   $$Z_n=\sum_{m\ge1}2^{n+m}e^{-(\rho^2/8)2^{2(n+m)\delta}},\quad g_n(m)=Z_n^{-1}2^{n+m}e^{-(\rho^2/8)2^{2(n+m)\delta}},\quad N^*=1+\sup\{n\ge1:Z_n>1\}.$$
--   BCE requires every conditional mean $|\int b_{n+m,k}\,d\kappa_n(x)|\le\rho\ell_{n+m}/2$. The signed tilt has $\theta^+_n(m)=\rho2^{(n+m)(H+\delta)}/2$ and $\theta^-=-\theta^+$. Its normalizer is $\Xi(\theta)=\int e^{\theta b}\,d\kappa_n(x)$, and
--   $$\Theta^\pm_n(m,k)=g_n(m)^{-1}2^{n+m}\exp(-\theta^\pm b_{n+m,k}+\log\Xi(\theta^\pm)).$$
--   The algorithm law samples $M\sim g_n$, $K$ uniform over $1,\ldots,2^{n+M-1}$, an independent fair sign, the exponentially tilted path, and an independent uniform $U\in[0,1]$. It accepts when $U<\Theta^\pm/R_{n+M}$ and the selected signed crossing occurs with no earlier record; $R$ counts strict crossings and division by zero returns zero. The output is restricted to $D_{n+M}\setminus D_n$.
--
--   **Formalization Note** A countable redundant array encodes dyadic coordinates, with invalid indices clamped to the endpoint. The conditional law therefore enforces consistency of repeated times. Sampling a latent completion of the dyadic path under the same tilt has precisely the finite marginal that Algorithm 4 samples; no additional values are output. Measure tilting accommodates singular Gaussian laws, unlike the density notation on p. 17. Natural suprema and the series are used only with positive $\rho,\delta$ in the theorems, where the set is finite and the series converges. The two-sided sign slip in the displayed definition of $\Theta^-$ is read with the negative tilt, as its second line specifies.
--
--   Differences from the source:
--   - encoding: finite dyadic values and P(·|B_n) → a coherent redundant countable dyadic array and condDistrib of that array given the level-n values; reason: the kernel is computed from the original process; only valid finite coordinates are queried and conditional statements hold almost surely at realized inputs
--   - encoding: Algorithm 4 samples its finite output values → a latent full dyadic completion, restricted to AugmentedIndex for the observable output; reason: the exponential density factor depends only on the selected triple, so restriction gives the same finite tilted marginal
--   - reading: a Gaussian density and the first-line plus superscript in the definition of Θ− → exponential tilting of measures and the negative tilt in Θ−; reason: conditional triples can be singular; the second line of the printed Θ− definition fixes the sign
--   - encoding: Z_n, sup{n≥1:Z_n>1}, and the footnote convention 0/0=0 → a real series, a natural supremum with sup∅=0, and total real division; reason: consumers require ρ,δ>0, where the series is positive and convergent and the supremum set is bounded; zero record count gives zero acceptance
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, pp. 15–20, (4.2), Definition 4.2, (4.5)–(4.7), Algorithms 3–4

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

namespace FBMStrongSim.RecordBreak.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Redundant coordinates for all dyadic values. Only i ≤ 2^l is queried. -/
abbrev DyadicPath := ℕ → ℕ → ℝ
abbrev LevelValues (n : ℕ) := Fin (2 ^ n + 1) → ℝ
abbrev Trial := ℕ × ℕ × Bool × DyadicPath × ℝ

noncomputable def dyadicValues {Ω : Type*} (B : ℝ → Ω → ℝ) (ω : Ω) : DyadicPath :=
  fun l i => B (dyadic l (min i (2 ^ l))) ω

noncomputable def levelValues {Ω : Type*} (B : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : LevelValues n :=
  fun i => B (dyadic n i) ω

/-- The actual regular conditional law P_n, not an arbitrary kernel. -/
noncomputable def conditionalLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ → Ω → ℝ) (P : Measure Ω) [IsFiniteMeasure P] (n : ℕ) :
    Kernel (LevelValues n) DyadicPath :=
  condDistrib (dyadicValues B) (levelValues B n) P

/-- βᵀα, with the source's sign, k = 1,...,2^(l-1). -/
noncomputable def betaValue (v : DyadicPath) (l k : ℕ) : ℝ :=
  (v l (2 * k - 2) + v l (2 * k)) / 2 - v l (2 * k - 1)

noncomputable def proposalTerm (rho delta : ℝ) (n m : ℕ) : ℝ :=
  (2 : ℝ) ^ (n + m) * Real.exp (-(rho ^ 2 / 8) * (2 : ℝ) ^ (2 * (n + m : ℕ) * delta))

noncomputable def normalizer (rho delta : ℝ) (n : ℕ) : ℝ :=
  ∑' q : ℕ, proposalTerm rho delta n (q + 1)

noncomputable def proposalMass (rho delta : ℝ) (n m : ℕ) : ℝ :=
  if m = 0 then 0 else proposalTerm rho delta n m / normalizer rho delta n

/-- For rho,delta>0 the defining set is finite; empty supremum is zero. -/
noncomputable def startLevel (rho delta : ℝ) : ℕ :=
  1 + sSup {n : ℕ | 1 ≤ n ∧ 1 < normalizer rho delta n}

noncomputable def conditionalMean (mu : Measure DyadicPath) (l k : ℕ) : ℝ :=
  ∫ v, betaValue v l k ∂mu

noncomputable def mgf (mu : Measure DyadicPath) (l k : ℕ) (theta : ℝ) : ℝ :=
  ∫ v, Real.exp (theta * betaValue v l k) ∂mu

/-- Definition 4.2, including every future level and position. -/
def BCE (mu : Measure DyadicPath) (rho H delta : ℝ) (n : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, 1 ≤ k → k ≤ 2 ^ (n + m - 1) →
    |conditionalMean mu (n + m) k| ≤ rho / 2 * ell H delta (n + m)

noncomputable def tiltParameter (rho H delta : ℝ) (n m : ℕ) (plus : Bool) : ℝ :=
  (if plus then 1 else -1) * (rho / 2 * (2 : ℝ) ^ ((n + m : ℕ) * (H + delta)))

noncomputable def weightedRatio (mu : Measure DyadicPath) (rho H delta : ℝ)
    (n m k : ℕ) (plus : Bool) (v : DyadicPath) : ℝ :=
  (proposalMass rho delta n m)⁻¹ * (2 : ℝ) ^ (n + m) *
    Real.exp (-tiltParameter rho H delta n m plus * betaValue v (n + m) k +
      Real.log (mgf mu (n + m) k (tiltParameter rho H delta n m plus)))

def Crossing (rho H delta : ℝ) (l k : ℕ) (plus : Bool) (v : DyadicPath) : Prop :=
  if plus then rho * ell H delta l < betaValue v l k
  else betaValue v l k < -(rho * ell H delta l)

def RecordAt (rho H delta : ℝ) (l : ℕ) (v : DyadicPath) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ (l - 1) ∧ rho * ell H delta l < |betaValue v l k|

/-- τ=n+m, for m≥1; no earlier strict record. -/
def FirstRecord (rho H delta : ℝ) (n m : ℕ) (v : DyadicPath) : Prop :=
  1 ≤ m ∧ RecordAt rho H delta (n + m) v ∧
    ∀ j : ℕ, 1 ≤ j → j < m → ¬RecordAt rho H delta (n + j) v

noncomputable def recordCount (rho H delta : ℝ) (l : ℕ) (v : DyadicPath) : ℕ := by
  classical
  exact ((Finset.Icc 1 (2 ^ (l - 1))).filter
    (fun k => rho * ell H delta l < |betaValue v l k|)).card

noncomputable def acceptanceWeight (mu : Measure DyadicPath) (rho H delta : ℝ)
    (n m k : ℕ) (plus : Bool) (v : DyadicPath) : ℝ := by
  classical
  exact if Crossing rho H delta (n + m) k plus v ∧
      (∀ j : ℕ, 1 ≤ j → j < m → ¬RecordAt rho H delta (n + j) v)
    then weightedRatio mu rho H delta n m k plus v / recordCount rho H delta (n + m) v
    else 0

/-- The independent uniform used by Algorithm 4. -/
noncomputable def uniformUnit : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- Algorithm 3 in its BCE branch, including Algorithm 4. The full dyadic path is a
latent completion: output uses only coordinates through n+M. The tilt depends only on α. -/
noncomputable def algorithmLaw (mu : Measure DyadicPath) (rho H delta : ℝ) (n : ℕ) :
    Measure Trial :=
  Measure.sum fun q : ℕ =>
    ∑ i ∈ Finset.range (2 ^ (n + (q + 1) - 1)), ∑ plus : Bool,
      ENNReal.ofReal (proposalMass rho delta n (q + 1) / (2 : ℝ) ^ (n + (q + 1))) •
        Measure.map (fun z : DyadicPath × ℝ => (q + 1, i + 1, plus, z.1, z.2))
          ((mu.tilted (fun v => tiltParameter rho H delta n (q + 1) plus *
            betaValue v (n + (q + 1)) (i + 1))).prod uniformUnit)

def Accepted (mu : Measure DyadicPath) (rho H delta : ℝ) (n : ℕ) (z : Trial) : Prop :=
  z.2.2.2.2 < acceptanceWeight mu rho H delta n z.1 z.2.1 z.2.2.1 z.2.2.2.1

/-- Finite carrier of D_(n+m) \ D_n, retaining the source's time coordinates. -/
def AugmentedIndex (n m : ℕ) :=
  {i : Fin (2 ^ (n + m) + 1) // ¬∃ j : Fin (2 ^ n + 1),
    dyadic (n + m) i = dyadic n j}

noncomputable def augmentedValues (n m : ℕ) (v : DyadicPath) : AugmentedIndex n m → ℝ :=
  fun i => v (n + m) i.val

end FBMStrongSim.RecordBreak.Supplement


