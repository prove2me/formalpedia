-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P02
-- name    : QAlgorithms_Papers_Independent_Intake100_P02
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:48:28.383411+00:00
-- url     : https://prove2.me/theorems/94f82aba-4204-4d84-8f8f-b670e6a36d11
-- title:
--   Definitions for Theory of channel simulation and bounds for private communication
-- statement:
--   The objects the formalized statements of *Theory of channel simulation and bounds for private communication* (arXiv:1711.09909) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `varianceEntropy`: PDF p.14, (111): entropy in bits, vacuum variance 1/2; 0 log 0 = 0.
--   - `conditionalSymplecticEigenvalue`: PDF p.14, (115): limiting conditional symplectic eigenvalue.
--   - `siftedRateExpression`: PDF p.14, (116): signed calculated expression including basis sifting. This does not define an achieved rate. Domain: 0<eta<1, omega>=1/2, xi>=0.
--   - `reverseRateExpression`: PDF p.13, (110): signed reverse-coherent-information comparison expression.
--   - `leadingRateExpression`: PDF p.15, (118): leading expression, with the continuous convention at nbar=0.
--   - `KeyRegister`: PDF pp.2-3: two key registers followed by two shield registers.
--   - `privateTarget`: PDF pp.2-3: private target from a shield and diagonal twisting blocks. Register-order adapter to the accepted Information100.P67.privateState. Every family U_i extends to a controlled twisting.
--   - `finiteKeyRate`: PDF pp.2-3: log2(k) key bits divided by actual channel-use count n.
--   - `FiniteTargetFunctional`: PDF p.15, (122)-(123): only the functional properties needed in (129), simultaneously over every finite key/shield dimension. No simulation or capacity bound is a field. Radius records the available continuity interval.
--   - `schmidtAmplitude`: PDF p.28, (A1)-(A2): TMSV Schmidt amplitudes at variance t=N+1/2.
--   - `tmsvKernel`: PDF p.28, (A1)-(A2): actual full pure TMSV density kernel, reusing the accepted thermal purification after converting variance to mean occupation.
--   - `bkNoise`: PDF p.28: BK added quadrature variance at resource variance mu.
--   - `displacedTmsvKernel`: PDF p.28, (A3): displace only the transmitted mode; retain the reference. Its photon index fixes the input Schmidt index.
--   - `bkOutput`: PDF p.28, text before (A3): actual additive-noise realization of BK on one TMSV half. Complex displacement variance xi equals added quadrature variance under [q,p]=i. Neither state nor channel is defined by (A4).
--   - `bkOverlapTerm`: PDF p.28, (A4): terms of the pure-input overlap with the constructed output.
--   - `bkRootFidelity`: PDF pp.5,28, (28),(A4): unsquared fidelity with pure TMSV input, sqrt(<TMSV|output|TMSV>). Normalization, integrability and summability are conclusions below, rather than assumed closed fidelity formulas.
-- source:
--   Theory of channel simulation and bounds for private communication, arXiv:1711.09909v3, https://arxiv.org/abs/1711.09909v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

/-!
arXiv:1711.09909v3. All citations are PDF pages. Missing operational
interfaces are deferred in HARD.md. Signed scalar expressions are not capacities.
Full Fock kernels have no photon cutoff. Accepted-paper imports provide normal
densities, Weyl matrix elements, the complex Gaussian law and private targets. Compilation and
independent moderation are pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P02

open Filter MeasureTheory QAlgorithms
open scoped ENNReal Topology
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal)

/-- PDF p.14, (111): entropy in bits, vacuum variance 1/2; 0 log 0 = 0. -/
def varianceEntropy (x : ℝ) : ℝ :=
  (x + 1 / 2) * Real.logb 2 (x + 1 / 2) -
    (x - 1 / 2) * Real.logb 2 (x - 1 / 2)

/-- PDF p.14, (115): limiting conditional symplectic eigenvalue. -/
def conditionalSymplecticEigenvalue (eta omega xi : ℝ) : ℝ :=
  Real.sqrt (omega * (1 + 4 * omega * xi * (1 - eta)) /
    (4 * (omega + xi * (1 - eta))))

/-- PDF p.14, (116): signed calculated expression including basis sifting.
This does not define an achieved rate. Domain: 0<eta<1, omega>=1/2, xi>=0. -/
def siftedRateExpression (eta omega xi : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.logb 2
    ((omega + xi * (1 - eta)) / ((1 - eta) * ((1 - eta) * omega + xi))) +
    (varianceEntropy (conditionalSymplecticEigenvalue eta omega xi) - varianceEntropy omega) / 2

/-- PDF p.13, (110): signed reverse-coherent-information comparison expression. -/
def reverseRateExpression (eta omega : ℝ) : ℝ :=
  -Real.logb 2 (1 - eta) - varianceEntropy omega

/-- PDF p.15, (118): leading expression, with the continuous convention at nbar=0. -/
def leadingRateExpression (eta nbar : ℝ) : ℝ :=
  (eta - nbar) * Real.logb 2 (Real.exp 1) + nbar * Real.logb 2 nbar

/-- PDF pp.2-3: two key registers followed by two shield registers. -/
abbrev KeyRegister (k a b : ℕ) := (Fin k × Fin k) × (Fin a × Fin b)

/-- PDF pp.2-3: private target from a shield and diagonal twisting blocks.
Register-order adapter to the accepted Information100.P67.privateState.
Every family U_i extends to a controlled twisting. -/
def privateTarget {k a b : ℕ}
    (shield : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (U : Fin k → Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    Matrix (KeyRegister k a b) (KeyRegister k a b) ℂ :=
  fun x y => QAlgorithms.Papers.Independent.Information100.P67.privateState
    (fun i => (U i : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)) shield
    (x.1.1, (x.2.1, (x.1.2, x.2.2)))
    (y.1.1, (y.2.1, (y.1.2, y.2.2)))

/-- PDF pp.2-3: log2(k) key bits divided by actual channel-use count n. -/
def finiteKeyRate (k n : ℕ) : ℝ := Real.logb 2 (k : ℝ) / (n : ℝ)

/-- PDF p.15, (122)-(123): only the functional properties needed in (129),
simultaneously over every finite key/shield dimension. No simulation or
capacity bound is a field. Radius records the available continuity interval. -/
structure FiniteTargetFunctional where
  value : (k a b : ℕ) → Matrix (KeyRegister k a b) (KeyRegister k a b) ℂ → ℝ
  g : ℝ → ℝ
  h : ℝ → ℝ
  radius : ℝ
  radius_positive : 0 < radius
  radius_le_one : radius ≤ 1
  nonnegative : ∀ k a b rho, IsDensityMatrix rho → 0 ≤ value k a b rho
  normalization : ∀ k a b, 0 < k → 0 < a → 0 < b →
    ∀ (shield : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ),
      IsDensityMatrix shield →
      ∀ U : Fin k → Matrix.unitaryGroup (Fin a × Fin b) ℂ,
        Real.logb 2 (k : ℝ) ≤ value k a b (privateTarget shield U)
  continuity : ∀ k a b rho sigma, IsDensityMatrix rho → IsDensityMatrix sigma →
    ∀ eps : ℝ, 0 ≤ eps → eps < radius → traceNorm (rho - sigma) ≤ eps →
      |value k a b rho - value k a b sigma| ≤
        g eps * Real.logb 2 ((k : ℝ) ^ 2 * (a : ℝ) * (b : ℝ)) + h eps

/-- PDF p.28, (A1)-(A2): TMSV Schmidt amplitudes at variance t=N+1/2. -/
def schmidtAmplitude (t : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((QAlgorithms.Papers.Independent.Claimed50.P35.thermalInput (t - 1 / 2)) n n).re

/-- PDF p.28, (A1)-(A2): actual full pure TMSV density kernel, reusing the
accepted thermal purification after converting variance to mean occupation. -/
def tmsvKernel (t : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  QAlgorithms.Papers.Independent.Claimed50.P35.thermalPurificationDensity (t - 1 / 2)

/-- PDF p.28: BK added quadrature variance at resource variance mu. -/
def bkNoise (mu : ℝ) : ℝ := 2 * mu - Real.sqrt (4 * mu ^ 2 - 1)

/-- PDF p.28, (A3): displace only the transmitted mode; retain the reference.
Its photon index fixes the input Schmidt index. -/
def displacedTmsvKernel (t : ℝ) (z : ℂ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun x y =>
    ((schmidtAmplitude t x.1 : ℂ) * displacementMatrix z x.2 x.1) *
      star ((schmidtAmplitude t y.1 : ℂ) * displacementMatrix z y.2 y.1)

/-- PDF p.28, text before (A3): actual additive-noise realization of BK on
one TMSV half. Complex displacement variance xi equals added quadrature
variance under [q,p]=i. Neither state nor channel is defined by (A4). -/
def bkOutput (mu t : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun x y => ∫ z : ℂ, displacedTmsvKernel t z x y ∂complexNormal (bkNoise mu) 0

/-- PDF p.28, (A4): terms of the pure-input overlap with the constructed output. -/
def bkOverlapTerm (mu t : ℝ) (p : ℕ × ℕ) : ℂ :=
  (schmidtAmplitude t p.1 : ℂ) *
    bkOutput mu t (p.1, p.1) (p.2, p.2) * (schmidtAmplitude t p.2 : ℂ)

/-- PDF pp.5,28, (28),(A4): unsquared fidelity with pure TMSV input,
sqrt(<TMSV|output|TMSV>). Normalization, integrability and summability are
conclusions below, rather than assumed closed fidelity formulas. -/
def bkRootFidelity (mu t : ℝ) : ℝ :=
  Real.sqrt ((∑' p : ℕ × ℕ, bkOverlapTerm mu t p).re)

/-- Vacuum entropy, including the zero-log convention; PDF p.14. -/
example : varianceEntropy (1 / 2) = 0 := by
  norm_num [varianceEntropy, Real.logb]

/-- A one-dimensional key carries zero bits; PDF pp.2-3. -/
example (n : ℕ) : finiteKeyRate 1 n = 0 := by
  simp [finiteKeyRate]

/-- With a one-dimensional key and identity twisting, the private target is
exactly the original shield density, entry by entry; PDF pp.2-3. -/
example {a b : ℕ} (shield : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (i j : Fin a × Fin b) :
    privateTarget shield (fun _ : Fin 1 => 1) ((0, 0), i) ((0, 0), j) = shield i j := by
  simp [privateTarget, QAlgorithms.Papers.Independent.Information100.P67.privateState]

/-- Vacuum-resource BK adds quadrature variance one; PDF p.28. -/
example : bkNoise (1 / 2) = 1 := by
  norm_num [bkNoise]

/-- Vacuum TMSV has zero-photon amplitude one; PDF p.28. -/
example : schmidtAmplitude (1 / 2) 0 = 1 := by
  norm_num [schmidtAmplitude,
    QAlgorithms.Papers.Independent.Claimed50.P35.thermalInput,
    QAlgorithms.Papers.Independent.Dependency50.P39.thermalMatrix]

/-- The matching reference index is retained; PDF p.28. -/
example (t : ℝ) (z : ℂ) (m n : ℕ) :
    displacedTmsvKernel t z (0, m) (0, n) =
      ((schmidtAmplitude t 0 : ℂ) * displacementMatrix z m 0) *
        star ((schmidtAmplitude t 0 : ℂ) * displacementMatrix z n 0) := rfl

end QAlgorithms.Papers.Independent.Intake100.P02


