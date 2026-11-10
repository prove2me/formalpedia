-- Prove2me | Definitions.Def_TightReleaseSchedules_Stationary_multiscale_prior
-- name    : TightReleaseSchedules_Stationary_multiscale_prior
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:45:37.566788+00:00
-- url     : https://prove2.me/theorems/111e10f7-87c8-4de9-ad18-4d336e52f8e8
-- title:
--   Independent cube levels and the observed filtration under the hidden prior
-- statement:
--   Let $S\subseteq\{1,\ldots,d\}$ be a coordinate block of size $d_h$, let $0<\Delta\le1$, and choose an integer $L\ge\ell_0$, where
--
--   $$
--   \ell_0=\left\lceil\log_2\frac{16d_h}{\Delta^2}\right\rceil,\quad
--   \kappa=2^{-10},\quad a_\ell=\sqrt{\kappa2^{-\ell}},\quad
--   H=\sum_{\ell=\ell_0}^{L}a_\ell U_\ell.
--   $$
--   The vectors $U_\ell$ are independent uniform points in $[-1,1]^S$. Their coordinates are independent uniform interval points. The shift $H\in\mathbb R^S$ is embedded by zero outside $S$. Given an arbitrary deterministic nuisance path $g_{1:T}$, the regression target is $g_t+H$. The seed, uniform levels, Gaussian designs and Gaussian noises have their independent product law. Only the seed and labeled observations enter the date-$n$ information; the levels and $H$ remain hidden.
--
--   The block projection restricts a vector to $S$, with its Euclidean norm. This construction supplies the actual prior and information model for every clause of Lemma 4.2. It assumes no small-ball or estimation conclusion.
--
--   **Formalization Note** Levels are signed integers. Cube coordinates are elements of the closed interval subtype, so every sample is in the cube, including null boundary points. A coordinate law is one half of Lebesgue measure pulled back to that interval. There is no boundedness assumption on the nuisance path outside $S$.
-- source:
--   Jing Wang, When to Update a Pretrained Model: Tight Release Schedules under Distribution Shift, STOC 2027 submission #1096 (October 2026), Lemma 4.2 and its construction, printed pp.10–11, PDF pp.11–12

import Definitions.Def_TightReleaseSchedules_Stationary_geometric_algorithm

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section

namespace TightReleaseSchedules.Stationary

abbrev BlockVector {d : ℕ} (S : Finset (Fin d)) := EuclideanSpace ℝ S

def blockProjection {d : ℕ} (S : Finset (Fin d)) (v : Vector d) : BlockVector S :=
  WithLp.toLp 2 (fun i : S => v i.val)

def embedBlock {d : ℕ} (S : Finset (Fin d)) (v : BlockVector S) : Vector d :=
  WithLp.toLp 2 (fun i => if h : i ∈ S then v ⟨i, h⟩ else 0)

def firstLevel (dₕ : ℕ) (Δ : ℝ) : ℤ := ⌈logTwo (16 * dₕ / Δ ^ 2)⌉

def levelAmplitude (ℓ : ℤ) : ℝ := Real.sqrt ((2 : ℝ) ^ (-10 : ℤ) * (2 : ℝ) ^ (-ℓ))

abbrev CubeCoordinate := Set.Icc (-1 : ℝ) 1

/-- Lebesgue uniform probability on the closed interval, with its endpoints retained. -/
def uniformCoordinate : Measure CubeCoordinate :=
  (2 : ℝ≥0∞)⁻¹ • (volume : Measure ℝ).comap (Subtype.val : CubeCoordinate → ℝ)

abbrev PriorDraws {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :=
  (ℓ : ↥(Finset.Icc (firstLevel S.card Δ) L)) → S → CubeCoordinate

def uniformLevels {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :
    Measure (PriorDraws S Δ L) :=
  Measure.pi (fun _ => Measure.pi (fun _ : S => uniformCoordinate))

/-- Actual sum of the independent cube levels, not a random vector with assumed bounds. -/
def hiddenShift {d : ℕ} (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ)
    (u : PriorDraws S Δ L) : BlockVector S :=
  ∑ ℓ, levelAmplitude ℓ.val • WithLp.toLp 2 (fun i : S => (u ℓ i : ℝ))

abbrev PriorSample (s : RandomSeed) (T d : ℕ) (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :=
  s.space × (PriorDraws S Δ L × GaussianRows T d)

def priorLaw (s : RandomSeed) (T d : ℕ) (S : Finset (Fin d)) (Δ : ℝ) (L : ℤ) :
    Measure (PriorSample s T d S Δ L) :=
  s.law.prod ((uniformLevels S Δ L).prod (gaussianRows T d))

def priorTranscript {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) (ω : PriorSample s T d S Δ L) : Transcript s T d :=
  (ω.1, observations (fun i => g i + embedBlock S (hiddenShift S Δ L ω.2.1)) ω.2.2)

/-- Only the seed and observed rows are available: hidden uniform levels are absent. -/
@[instance_reducible] def priorInformation {s : RandomSeed} {T d : ℕ} {S : Finset (Fin d)} {Δ : ℝ} {L : ℤ}
    (g : Fin T → Vector d) (n : ℕ) : MeasurableSpace (PriorSample s T d S Δ L) :=
  MeasurableSpace.comap (priorTranscript g) (information s T d n)

end TightReleaseSchedules.Stationary


