-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P15
-- name    : QAlgorithms_Papers_Independent_Bridge50_P15
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T14:23:31.773035+00:00
-- url     : https://prove2.me/theorems/9ca5aa27-79fb-4773-8a2f-dd20a8d0581e
-- title:
--   Definitions for Narrow Bounds for the Quantum Capacity of Thermal Attenuators
-- statement:
--   The objects the formalized statements of *Narrow Bounds for the Quantum Capacity of Thermal Attenuators* (arXiv:1801.04731) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `referenceDensity`: PDF pp.3-4, (15): canonical reference purification, with coefficients of sqrt(rho) vectorized as |sqrt(rho)>. Physical uses are normalized densities.
--   - `referenceCoherent`: PDF pp.3-4, (15): reference coherent information I(R:B)-S(R) in bits. For finite input entropy the mutual information is finite, even if both output entropies are infinite. When output entropies are finite it equals S(B)-S(F). Values outside this domain are unused by singleLetter and all statements.
--   - `singleLetter`: PDF p.3, (16): extended supremum over all finite-input-entropy states. No output-entropy finiteness or energy bound restricts this optimization. The nonnegative supremum retains unbounded capacity; pure inputs supply zero.
--   - `purifiedJoint`: PDF p.4, (22): one joint output, with U acting on A,E and leaving R alone. Index order is ((B,F),R); input order is (A,(E,R)).
--   - `mixedReceiver`: PDF pp.2,4, (1),(2): receiver of the fixed mixed-environment dilation.
--   - `mixedWeak`: PDF p.4, (20): weak complement from exactly the same K and sigma.
--   - `purifiedExtension`: PDF p.4, (23): retain B,R and trace F from the computed joint output.
--   - `extensionComplement`: PDF p.4, (24): true complement of the extension, retaining only F.
--   - `originalComplement`: PDF p.4, (21): true complement of the original receiver, retaining F,R.
--   - `qubitCoupling`: PDF p.3, (7): ordered |00>,|01>,|10>,|11> coupling, including its minus sign.
--   - `qubitBath`: PDF p.3, (6): bath population N, in the ordered energy basis.
--   - `qubitPurification`: PDF p.5, (27): normalized thermal Schmidt purification for 0<=N<=1/2.
--   - `qubitExtension`: PDF pp.4-5, (23),(27): physical qubit extension, output B,Eprime.
--   - `qubitExtendedCoherent`: PDF pp.5,9, (41),(44): actual finite output-entropy difference of the extension.
--   - `qubitLower`: PDF pp.3-4, (17): achievable diagonal-input objective; no noisy-channel claim equating it to unrestricted Q1 is built into this definition.
--   - `qubitUpper`: PDF p.5, (28): diagonal extension objective; finite compact optimization.
--   - `fockCoupling`: PDF p.3, (12)-(13): complete Fock beam splitter in number coordinates. The finite binomial expansion implements U|m,n>, with minus on transmission from the first input to the second output. The qubit convention (7) instead places its minus on the reverse transfer; each follows its own source formula.
--   - `bosonicChannel`: PDF pp.3,6, (10)-(13): thermal attenuator from the complete mixed dilation.
--   - `bosonicExtension`: PDF pp.4-5, (22),(29): actual thermal two-mode Schmidt density, not just its covariance. Accepted thermalPurificationDensity uses mean photon number N.
--   - `twistedBound`: PDF p.7, (40): scalar twisted upper bound, used only for eta<1 and etaPrime>0.
--   - `extendedBound`: PDF p.6, (33): scalar extension bound in the finite-log domain eta<1.
--   - `gaussianLower`: PDF p.4, (18): clipped Gaussian achievable lower endpoint.
--   - `swatBound`: PDF p.4, (19): SWAT comparison endpoint, with the source's clipping.
--   - `plobBound`: PDF p.4, (19): PLOB endpoint. For eta>0, log((1-eta)eta^N) =log(1-eta)+N log(eta), avoiding an unnecessary real-power convention.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, https://arxiv.org/abs/1801.04731v5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

/-!
arXiv:1801.04731v5. Full trace-class channels on completed Hilbert spaces.
Accepted paper definitions are imported under the independent-paper override.
No photon cutoff or covariance-only channel model is used. Compilation and
independent moderation are pending. The false residual branch of (46) is deferred.
-/

noncomputable section

open Filter
open scoped BigOperators ENNReal Topology Matrix

namespace QAlgorithms.Papers.Independent.Bridge50.P15

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass IsTraceClassChannel productCoeff tensorApply rankOne)
open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel partialLeft partialRight isometryCoeff WeaklyDegradable GaussianDensity)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedRelativeEntropyNats)
open QAlgorithms.Papers.Independent.Gap48.P26
  (entropyBits PhaseInsensitive weightedPhotonExpectation thermalKernel)
open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassQuantumCapacity vacuumChannel)
open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)
open QAlgorithms.Papers.Independent.Support50.P07 (qubitPhaseFlipChannel)
open QAlgorithms.Papers.Independent.Information100.P08 (qubitInput thermalChannel)

/- Source (3)-(5): qubitInput is reused exactly; thermalChannel takes damping
probability 1-eta rather than transmissivity eta. Source (34)-(37),(49):
vacuumChannel takes amplitude sqrt(kappa) rather than intensity gain kappa. -/

/-- PDF pp.3-4, (15): canonical reference purification, with coefficients of
sqrt(rho) vectorized as |sqrt(rho)>. Physical uses are normalized densities. -/
def referenceDensity {A : Type} (X : Matrix A A ℂ) : Matrix (A × A) (A × A) ℂ :=
  let S := operatorCoeff (cfc (fun z : ℂ => (Real.sqrt z.re : ℂ)) (boundedOperator X))
  fun i j => S i.1 i.2 * star (S j.1 j.2)

/-- PDF pp.3-4, (15): reference coherent information I(R:B)-S(R) in bits.
For finite input entropy the mutual information is finite, even if both output
entropies are infinite. When output entropies are finite it equals S(B)-S(F).
Values outside this domain are unused by singleLetter and all statements. -/
def referenceCoherent {A B : Type} (Phi : Operation A B) (X : Matrix A A ℂ) : ℝ :=
  let Y := tensorApply Phi (referenceDensity X)
  (extendedRelativeEntropyNats Y (productCoeff (partialRight Y) (partialLeft Y)) /
    ENNReal.ofReal (Real.log 2)).toReal - (entropyBits X).toReal

/-- PDF p.3, (16): extended supremum over all finite-input-entropy states.
No output-entropy finiteness or energy bound restricts this optimization.
The nonnegative supremum retains unbounded capacity; pure inputs supply zero. -/
def singleLetter {A B : Type} (Phi : Operation A B) : ℝ≥0∞ :=
  ⨆ rho : {rho : State A // entropyBits rho.coefficients < ⊤},
    ENNReal.ofReal (referenceCoherent Phi rho.val.coefficients)

/-- PDF p.4, (22): one joint output, with U acting on A,E and leaving R alone.
Index order is ((B,F),R); input order is (A,(E,R)). -/
def purifiedJoint {A B E F R : Type} (K : Matrix (B × F) (A × E) ℂ)
    (tau : Matrix (E × R) (E × R) ℂ) (X : Matrix A A ℂ) :
    Matrix ((B × F) × R) ((B × F) × R) ℂ :=
  conjugateKernel
    (fun o i => K o.1 (i.1, i.2.1) * (if o.2 = i.2.2 then 1 else 0))
    (productCoeff X tau)

/-- PDF pp.2,4, (1),(2): receiver of the fixed mixed-environment dilation. -/
def mixedReceiver {A B E F : Type} (K : Matrix (B × F) (A × E) ℂ)
    (sigma : Matrix E E ℂ) : Operation A B :=
  fun X => partialRight (conjugateKernel K (productCoeff X sigma))

/-- PDF p.4, (20): weak complement from exactly the same K and sigma. -/
def mixedWeak {A B E F : Type} (K : Matrix (B × F) (A × E) ℂ)
    (sigma : Matrix E E ℂ) : Operation A F :=
  fun X => partialLeft (conjugateKernel K (productCoeff X sigma))

/-- PDF p.4, (23): retain B,R and trace F from the computed joint output. -/
def purifiedExtension {A B E F R : Type} (K : Matrix (B × F) (A × E) ℂ)
    (tau : Matrix (E × R) (E × R) ℂ) : Operation A (B × R) :=
  fun X i j => ∑' f, purifiedJoint K tau X ((i.1, f), i.2) ((j.1, f), j.2)

/-- PDF p.4, (24): true complement of the extension, retaining only F. -/
def extensionComplement {A B E F R : Type} (K : Matrix (B × F) (A × E) ℂ)
    (tau : Matrix (E × R) (E × R) ℂ) : Operation A F :=
  fun X f g => ∑' b, ∑' r, purifiedJoint K tau X ((b, f), r) ((b, g), r)

/-- PDF p.4, (21): true complement of the original receiver, retaining F,R. -/
def originalComplement {A B E F R : Type} (K : Matrix (B × F) (A × E) ℂ)
    (tau : Matrix (E × R) (E × R) ℂ) : Operation A (F × R) :=
  fun X i j => ∑' b, purifiedJoint K tau X ((b, i.1), i.2) ((b, j.1), j.2)

/-- PDF p.3, (7): ordered |00>,|01>,|10>,|11> coupling, including its minus sign. -/
def qubitCoupling (eta : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun o i => if i.1 = i.2 then (if o = i then 1 else 0)
    else if o = i then (Real.sqrt eta : ℂ)
    else if o = (i.2, i.1) then
      (if i.1 = 0 then -(Real.sqrt (1 - eta) : ℂ) else (Real.sqrt (1 - eta) : ℂ))
    else 0

/-- PDF p.3, (6): bath population N, in the ordered energy basis. -/
def qubitBath (N : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then (if i = 0 then ((1 - N : ℝ) : ℂ) else (N : ℂ)) else 0

/-- PDF p.5, (27): normalized thermal Schmidt purification for 0<=N<=1/2. -/
def qubitPurification (N : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  let v : Fin 2 × Fin 2 → ℂ := fun i =>
    if i.1 = i.2 then (if i.1 = 0 then (Real.sqrt (1 - N) : ℂ) else (Real.sqrt N : ℂ)) else 0
  fun i j => v i * star (v j)

/-- PDF pp.4-5, (23),(27): physical qubit extension, output B,Eprime. -/
def qubitExtension (eta N : ℝ) : Operation (Fin 2) (Fin 2 × Fin 2) :=
  purifiedExtension (qubitCoupling eta) (qubitPurification N)

/-- PDF pp.5,9, (41),(44): actual finite output-entropy difference of the extension. -/
def qubitExtendedCoherent (eta N : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (entropyBits (qubitExtension eta N X)).toReal -
    (entropyBits (extensionComplement (qubitCoupling eta) (qubitPurification N) X)).toReal

/-- PDF pp.3-4, (17): achievable diagonal-input objective; no noisy-channel
claim equating it to unrestricted Q1 is built into this definition. -/
def qubitLower (eta N : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ p ∈ Set.Icc (0 : ℝ) 1,
    z = (entropyBits (thermalChannel (1 - eta) N (qubitInput p 0))).toReal -
      (entropyBits (originalComplement (qubitCoupling eta) (qubitPurification N)
        (qubitInput p 0))).toReal}

/-- PDF p.5, (28): diagonal extension objective; finite compact optimization. -/
def qubitUpper (eta N : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ p ∈ Set.Icc (0 : ℝ) 1,
    z = qubitExtendedCoherent eta N (qubitInput p 0)}

/-- PDF p.3, (12)-(13): complete Fock beam splitter in number coordinates.
The finite binomial expansion implements U|m,n>, with minus on transmission
from the first input to the second output. The qubit convention (7) instead
places its minus on the reverse transfer; each follows its own source formula. -/
def fockCoupling (eta : ℝ) : Matrix (ℕ × ℕ) (ℕ × ℕ) ℂ :=
  fun o i => ∑ j ∈ Finset.range (i.1 + 1), ∑ h ∈ Finset.range (i.2 + 1),
    if o.1 = j + h ∧ o.2 = (i.1 - j) + (i.2 - h) then
      ((Real.sqrt (((Nat.factorial o.1 : ℝ) * (Nat.factorial o.2 : ℝ)) /
          ((Nat.factorial i.1 : ℝ) * (Nat.factorial i.2 : ℝ))) *
        (Nat.choose i.1 j : ℝ) * (Nat.choose i.2 h : ℝ) *
        Real.sqrt eta ^ j * (-Real.sqrt (1 - eta)) ^ (i.1 - j) *
        Real.sqrt (1 - eta) ^ h * Real.sqrt eta ^ (i.2 - h) : ℝ) : ℂ)
    else 0

/-- PDF pp.3,6, (10)-(13): thermal attenuator from the complete mixed dilation. -/
def bosonicChannel (eta N : ℝ) : Operation ℕ ℕ :=
  mixedReceiver (fockCoupling eta) (thermalKernel N)

/-- PDF pp.4-5, (22),(29): actual thermal two-mode Schmidt density, not just
its covariance. Accepted thermalPurificationDensity uses mean photon number N. -/
def bosonicExtension (eta N : ℝ) : Operation ℕ (ℕ × ℕ) :=
  purifiedExtension (fockCoupling eta)
    (QAlgorithms.Papers.Independent.Claimed50.P35.thermalPurificationDensity N)

/-- PDF p.7, (40): scalar twisted upper bound, used only for eta<1 and etaPrime>0. -/
def twistedBound (eta N : ℝ) : ℝ :=
  max 0 (Real.logb 2 ((eta - N * (1 - eta)) / ((1 + N) * (1 - eta))))

/-- PDF p.6, (33): scalar extension bound in the finite-log domain eta<1. -/
def extendedBound (eta N : ℝ) : ℝ :=
  max 0 (Real.logb 2 (eta / (1 - eta)) + thermalEntropyBits N)

/-- PDF p.4, (18): clipped Gaussian achievable lower endpoint. -/
def gaussianLower (eta N : ℝ) : ℝ :=
  max 0 (Real.logb 2 (eta / (1 - eta)) - thermalEntropyBits N)

/-- PDF p.4, (19): SWAT comparison endpoint, with the source's clipping. -/
def swatBound (eta N : ℝ) : ℝ :=
  max 0 (Real.logb 2 (eta / (1 - eta)) - Real.logb 2 (N + 1))

/-- PDF p.4, (19): PLOB endpoint. For eta>0, log((1-eta)eta^N)
=log(1-eta)+N log(eta), avoiding an unnecessary real-power convention. -/
def plobBound (eta N : ℝ) : ℝ :=
  max 0 (-Real.logb 2 (1 - eta) - N * Real.logb 2 eta - thermalEntropyBits N)

example {A : Type} (X : Matrix A A ℂ) (i j : A × A) :
    referenceDensity X i j = star (referenceDensity X j i) := by
  simp [referenceDensity, mul_comm]

example (z : ℂ) :
    purifiedExtension (fun _ _ : Unit × Unit => (1 : ℂ))
      (fun _ _ : Unit × Unit => (1 : ℂ)) (fun _ _ : Unit => z) ((), ()) ((), ()) = z := by
  simp [purifiedExtension, purifiedJoint, conjugateKernel, productCoeff]

example : qubitCoupling (1 / 2) (1, 0) (0, 1) = -(Real.sqrt (1 - (1 / 2 : ℝ)) : ℂ) := by
  norm_num [qubitCoupling]

example : qubitPurification 0 (0, 0) (0, 0) = 1 := by
  norm_num [qubitPurification]

example : qubitBath 0 1 1 = 0 := by
  norm_num [qubitBath]

example (p : ℝ) : qubitInput p 0 1 1 = (p : ℂ) := by rfl

example : fockCoupling (1 / 2) (0, 0) (0, 0) = 1 := by
  norm_num [fockCoupling, Finset.sum_range_succ]

example : twistedBound (1 / 2) 0 = 0 := by
  norm_num [twistedBound]

example : extendedBound (1 / 2) 0 = 0 := by
  norm_num [extendedBound, thermalEntropyBits]

end QAlgorithms.Papers.Independent.Bridge50.P15


