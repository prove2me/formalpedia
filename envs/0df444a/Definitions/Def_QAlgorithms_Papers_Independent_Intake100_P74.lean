-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P74
-- name    : QAlgorithms_Papers_Independent_Intake100_P74
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T14:57:26.71099+00:00
-- url     : https://prove2.me/theorems/fd07926d-2972-447f-8bda-7fa3ed5e9b17
-- title:
--   Definitions for Coherent-state constellations and polar codes for thermal Gaussian channels
-- statement:
--   The objects the formalized statements of *Coherent-state constellations and polar codes for thermal Gaussian channels* (arXiv:1603.05970) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `coherentEntry`: PDF p.2: normalized coherent projector on the complete number basis.
--   - `positivePState`: PDF pp.5,8: positive coherent mixture. On probability measures every coefficient is bounded and integrable. Density means relative to d²z, not d²z/pi. Unlike Support50.P06.coherentMixture, the prior is any probability measure, including atomic constellations; it is not restricted to complexNormal N 0.
--   - `HasThermalMoments`: PDF p.5: all first/second ladder moments, both conjugates and both mixed-product orderings. HasSum excludes divergent-tsum default values.
--   - `constellationPoint`: PDF p.5, (7): amplitude z=sqrt(N/2)(x+iy).
--   - `finiteConstellationState`: PDF p.5, (7)--(8): independent finite probability masses, not densities. The two coordinate laws need only be separately centered and standardized.
--   - `realGaussian`: PDF p.7, (14): centered real Gaussian density for v>0.
--   - `awgnDensity`: PDF pp.5,7, (18): actual output density of sqrt(s)X+G, where G is an independent standard normal. No input moment premise.
--   - `classicalCollision`: PDF p.8, (19): positive collision integral against N(0,1+s). The denominator has positive variance on the stated s>=0 domain.
--   - `classicalChiSquare`: PDF pp.5,7: collision minus one; collision>=1 on probability inputs.
--   - `realKernel`: PDF p.7, (16): finite nonnegative Gaussian kernel for every s>=0.
--   - `quantumCollision`: PDF p.8: Tr[rho tau^(-1/2) rho tau^(-1/2)] as a positive Fock-entry sum. At vacuum a nonzero entry outside the reference support gives infinity. This is not the generally different Tr[rho² tau^(-1)].
--   - `quantumChiSquare`: PDF pp.5,8: extended quantum chi-square in the paper's convention.
--   - `coherentCollisionKernel`: PDF p.8, (22): t_N corrects printed t_n; the cross term is 2 t_N Re(z conjugate(w)). Only N>0 is used. This scalar positive kernel is distinct from Dependency50.P10.complexKernel, a matrix nullspace.
--   - `outputAmplitudeLaw`: PDF pp.2,5,7: the channel output's actual positive-P law, with independent coordinates and independent planar Gaussian noise. Nc=0 uses a Dirac mass; k=1 with independent Nc>=0 includes additive noise.
--   - `constellationOutput`: PDF p.7, Lemma 1: complete Fock output of the specified input mixture. No complementary channel or operational capacity is assigned by this definition.
--   - `comparisonSnr`: PDF pp.5,7: comparison SNR, used only at positive output energy.
--   - `finiteRealLaw`: PDF p.5: explicit finite real law, with masses rather than a density.
--   - `singleModeEntropy`: PDF pp.2,5: actual spectral von Neumann entropy, in nats, with a bijection between the one-mode occupation string and its number label.
--   - `classicalInformationGap`: PDF p.5, (9a): Holevo-information gap after cancellation of the common conditional displaced-thermal entropy g(Nc). The quantity is computed from the actual output, not a freely chosen rate scalar. On standardized laws the output entropy is finite and at most g(k²N+Nc). Infinite entropy is explicit.
--   - `randomWalkPoint`: PDF p.3: standardized symmetric walk with m-1 steps, m>=2.
--   - `randomWalkLaw`: PDF p.3: the m possible walk positions have their binomial probabilities.
--   - `normalHermite`: PDF pp.3--4: probabilists' Hermite polynomial, for standard normal weight.
--   - `gaussHermiteWeight`: PDF pp.3--4: standard Gaussian quadrature weight at a root x of H_m. This is m!/(m² H_(m-1)(x)²); it is only used for m>=2.
--   - `gaussHermiteLaw`: PDF pp.3--4: m real roots of H_m with the standard-normal quadrature weights. Roots are simple for m>=1, so the finset loses no multiplicities. There is no arbitrary choice of a grid or normalization.
--   - `gapExponent`: PDF p.6: exact fixed-channel exponential rate, only used for k,N>0.
-- source:
--   Coherent-state constellations and polar codes for thermal Gaussian channels, arXiv:1603.05970v3, https://arxiv.org/abs/1603.05970v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

/-! Lacerda--Renes--Scholz, arXiv:1603.05970v3. Complete countable Fock
basis, without photon cutoff. Divergent positive sums/integrals stay infinite.
All new definitions are paper-local. Deferred nodes are in HARD.md/GAPS.json.
Compilation and independent moderation are pending batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P74

open MeasureTheory
open scoped BigOperators ENNReal
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient thermalMatrix)
open QAlgorithms.Papers.Independent.Support50.P14 (photonEnergy)
open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal spectralEntropyNats)
open QAlgorithms.Papers.Independent.Claimed50.P39 (thermalProbability g)

attribute [local instance] Classical.propDecidable Classical.decEq

/-! Frozen reuse: thermalMatrix uses covariance parameter a=2N+1, so vacuum
is thermalMatrix 1. photonEnergy is reused on occupation strings of Fin 1,
relabeling rho via (a,b) ↦ rho (a 0) (b 0). No frozen body is copied.
The general positive-P mixture and scalar coherent collision kernel have
distinct descriptive names because the same short frozen names have
incompatible domains and meanings, as recorded in ASSESSMENT.json. -/

/-- PDF p.2: normalized coherent projector on the complete number basis. -/
def coherentEntry (z : ℂ) (i j : ℕ) : ℂ :=
  coherentCoefficient z i * star (coherentCoefficient z j)

/-- PDF pp.5,8: positive coherent mixture. On probability measures every
coefficient is bounded and integrable. Density means relative to d²z, not d²z/pi.
Unlike Support50.P06.coherentMixture, the prior is any probability measure,
including atomic constellations; it is not restricted to complexNormal N 0. -/
def positivePState (mu : Measure ℂ) : Matrix ℕ ℕ ℂ :=
  fun i j => ∫ z, coherentEntry z i j ∂mu

/-- PDF p.5: all first/second ladder moments, both conjugates and both
mixed-product orderings. HasSum excludes divergent-tsum default values. -/
def HasThermalMoments (rho : Matrix ℕ ℕ ℂ) (N : ℝ) : Prop :=
  HasSum (fun n : ℕ => (Real.sqrt (n + 1 : ℝ) : ℂ) * rho (n + 1) n) 0 ∧
  HasSum (fun n : ℕ => (Real.sqrt (n + 1 : ℝ) : ℂ) * rho n (n + 1)) 0 ∧
  HasSum (fun n : ℕ =>
    (Real.sqrt ((n + 1 : ℝ) * (n + 2 : ℝ)) : ℂ) * rho (n + 2) n) 0 ∧
  HasSum (fun n : ℕ =>
    (Real.sqrt ((n + 1 : ℝ) * (n + 2 : ℝ)) : ℂ) * rho n (n + 2)) 0 ∧
  HasSum (fun n : ℕ => (n : ℂ) * rho n n) (N : ℂ) ∧
  HasSum (fun n : ℕ => (n + 1 : ℂ) * rho n n) ((N + 1 : ℝ) : ℂ)

/-- PDF p.5, (7): amplitude z=sqrt(N/2)(x+iy). -/
def constellationPoint (N : ℝ) (x y : ℝ) : ℂ :=
  (Real.sqrt (N / 2) : ℂ) * ((x : ℂ) + Complex.I * (y : ℂ))

/-- PDF p.5, (7)--(8): independent finite probability masses, not densities.
The two coordinate laws need only be separately centered and standardized. -/
def finiteConstellationState {m l : ℕ} (N : ℝ)
    (p : Fin m → ℝ) (q : Fin l → ℝ) (x : Fin m → ℝ) (y : Fin l → ℝ) :
    Matrix ℕ ℕ ℂ :=
  fun a b => ∑ i : Fin m, ∑ j : Fin l,
    ((p i * q j : ℝ) : ℂ) * coherentEntry (constellationPoint N (x i) (y j)) a b

/-- PDF p.7, (14): centered real Gaussian density for v>0. -/
def realGaussian (v t : ℝ) : ℝ :=
  Real.exp (-t ^ 2 / (2 * v)) / Real.sqrt (2 * Real.pi * v)

/-- PDF pp.5,7, (18): actual output density of sqrt(s)X+G, where
G is an independent standard normal. No input moment premise. -/
def awgnDensity (s : ℝ) (mu : Measure ℝ) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (realGaussian 1 (y - Real.sqrt s * x)) ∂mu

/-- PDF p.8, (19): positive collision integral against N(0,1+s).
The denominator has positive variance on the stated s>=0 domain. -/
def classicalCollision (s : ℝ) (mu : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ y : ℝ, (awgnDensity s mu y) ^ 2 /
    ENNReal.ofReal (realGaussian (1 + s) y)

/-- PDF pp.5,7: collision minus one; collision>=1 on probability inputs. -/
def classicalChiSquare (s : ℝ) (mu : Measure ℝ) : ℝ≥0∞ :=
  classicalCollision s mu - 1

/-- PDF p.7, (16): finite nonnegative Gaussian kernel for every s>=0. -/
def realKernel (s x y : ℝ) : ℝ :=
  (1 + s) / Real.sqrt (1 + 2 * s) *
    Real.exp (-s / (2 * (1 + 2 * s)) * (s * (x - y) ^ 2 - 2 * x * y))

/-- PDF p.8: Tr[rho tau^(-1/2) rho tau^(-1/2)] as a positive Fock-entry
sum. At vacuum a nonzero entry outside the reference support gives infinity.
This is not the generally different Tr[rho² tau^(-1)]. -/
def quantumCollision (rho : Matrix ℕ ℕ ℂ) (N : ℝ) : ℝ≥0∞ :=
  if N = 0 then
    if ∀ i j : ℕ, i ≠ 0 ∨ j ≠ 0 → rho i j = 0 then
      ENNReal.ofReal (Complex.normSq (rho 0 0)) else ⊤
  else
    ∑' ij : ℕ × ℕ, ENNReal.ofReal
      (Complex.normSq (rho ij.1 ij.2) /
        Real.sqrt (thermalProbability N ij.1 * thermalProbability N ij.2))

/-- PDF pp.5,8: extended quantum chi-square in the paper's convention. -/
def quantumChiSquare (rho : Matrix ℕ ℕ ℂ) (N : ℝ) : ℝ≥0∞ :=
  quantumCollision rho N - 1

/-- PDF p.8, (22): t_N corrects printed t_n; the cross term is
2 t_N Re(z conjugate(w)). Only N>0 is used. This scalar positive
kernel is distinct from Dependency50.P10.complexKernel, a matrix nullspace. -/
def coherentCollisionKernel (N : ℝ) (z w : ℂ) : ℝ :=
  (N + 1) * Real.exp (-Complex.normSq z - Complex.normSq w +
    2 * Real.sqrt ((N + 1) / N) * (z * star w).re)

/-- PDF pp.2,5,7: the channel output's actual positive-P law, with
independent coordinates and independent planar Gaussian noise. Nc=0 uses
a Dirac mass; k=1 with independent Nc>=0 includes additive noise. -/
def outputAmplitudeLaw (k Nc N : ℝ) (mu nu : Measure ℝ) : Measure ℂ :=
  Measure.map (fun t : (ℝ × ℝ) × ℂ =>
    (k : ℂ) * constellationPoint N t.1.1 t.1.2 + t.2)
    ((mu.prod nu).prod (complexNormal Nc 0))

/-- PDF p.7, Lemma 1: complete Fock output of the specified input mixture.
No complementary channel or operational capacity is assigned by this definition. -/
def constellationOutput (k Nc N : ℝ) (mu nu : Measure ℝ) : Matrix ℕ ℕ ℂ :=
  positivePState (outputAmplitudeLaw k Nc N mu nu)

/-- PDF pp.5,7: comparison SNR, used only at positive output energy. -/
def comparisonSnr (k Nc N : ℝ) : ℝ :=
  k ^ 2 * N /
    (Real.sqrt ((k ^ 2 * N + Nc) * (k ^ 2 * N + Nc + 1)) - k ^ 2 * N)

example : coherentEntry 0 0 0 = 1 := by
  simp [coherentEntry, coherentCoefficient]

example : thermalMatrix 1 0 0 = 1 := by
  norm_num [thermalMatrix]

example (x y : ℝ) : realKernel 0 x y = 1 := by
  simp [realKernel]

example (N : ℝ) : coherentCollisionKernel N 0 0 = N + 1 := by
  simp [coherentCollisionKernel]

example (x y : ℝ) : constellationPoint 0 x y = 0 := by
  simp [constellationPoint]

/-- PDF p.5: explicit finite real law, with masses rather than a density. -/
def finiteRealLaw {m : ℕ} (p x : Fin m → ℝ) : Measure ℝ :=
  ∑ i : Fin m, ENNReal.ofReal (p i) • Measure.dirac (x i)

/-- PDF pp.2,5: actual spectral von Neumann entropy, in nats, with a
bijection between the one-mode occupation string and its number label. -/
def singleModeEntropy (rho : Matrix ℕ ℕ ℂ) : ℝ≥0∞ :=
  spectralEntropyNats (fun a b : Fin 1 → ℕ => rho (a 0) (b 0))

/-- PDF p.5, (9a): Holevo-information gap after cancellation of the common
conditional displaced-thermal entropy g(Nc). The quantity is computed from
the actual output, not a freely chosen rate scalar. On standardized laws the
output entropy is finite and at most g(k²N+Nc). Infinite entropy is explicit. -/
def classicalInformationGap (k Nc N : ℝ) (mu : Measure ℝ) : ℝ≥0∞ :=
  let H := singleModeEntropy (constellationOutput k Nc N mu mu)
  if H = ⊤ then ⊤ else ENNReal.ofReal (g (k ^ 2 * N + Nc)) - H

/-- PDF p.3: standardized symmetric walk with m-1 steps, m>=2. -/
def randomWalkPoint (m : ℕ) (j : Fin m) : ℝ :=
  (2 * (j.val : ℝ) - ((m - 1 : ℕ) : ℝ)) / Real.sqrt ((m - 1 : ℕ) : ℝ)

/-- PDF p.3: the m possible walk positions have their binomial probabilities. -/
def randomWalkLaw (m : ℕ) : Measure ℝ :=
  finiteRealLaw
    (fun j : Fin m => (Nat.choose (m - 1) j.val : ℝ) / (2 : ℝ) ^ (m - 1))
    (randomWalkPoint m)

/-- PDF pp.3--4: probabilists' Hermite polynomial, for standard normal weight. -/
def normalHermite (m : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite m).map (Int.castRingHom ℝ)

/-- PDF pp.3--4: standard Gaussian quadrature weight at a root x of H_m.
This is m!/(m² H_(m-1)(x)²); it is only used for m>=2. -/
def gaussHermiteWeight (m : ℕ) (x : ℝ) : ℝ :=
  (Nat.factorial m : ℝ) /
    ((m : ℝ) ^ 2 * ((normalHermite (m - 1)).eval x) ^ 2)

/-- PDF pp.3--4: m real roots of H_m with the standard-normal quadrature
weights. Roots are simple for m>=1, so the finset loses no multiplicities.
There is no arbitrary choice of a grid or normalization. -/
def gaussHermiteLaw (m : ℕ) : Measure ℝ :=
  ∑ x ∈ (normalHermite m).roots.toFinset,
    ENNReal.ofReal (gaussHermiteWeight m x) • Measure.dirac x

/-- PDF p.6: exact fixed-channel exponential rate, only used for k,N>0. -/
def gapExponent (k Nc N : ℝ) : ℝ :=
  2 * Real.log ((1 + comparisonSnr k Nc N) / comparisonSnr k Nc N)

example : randomWalkPoint 2 (0 : Fin 2) = -1 := by
  norm_num [randomWalkPoint]

example : gaussHermiteWeight 2 1 = 1 / 2 := by
  norm_num [gaussHermiteWeight, normalHermite, Polynomial.hermite]

end QAlgorithms.Papers.Independent.Intake100.P74


