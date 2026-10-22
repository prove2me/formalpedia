-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44
-- name    : QAlgorithms_Papers_Independent_Gap48_P44
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T05:37:52.920513+00:00
-- url     : https://prove2.me/theorems/5ed84482-fb54-4ecb-89a9-9809af491629
-- title:
--   Definitions for Quantum trade-off coding for bosonic communication
-- statement:
--   The objects the formalized statements of *Quantum trade-off coding for bosonic communication* (arXiv:1105.0119) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `cqFamily`: PDF pp.6,14, (40)-(41), (81)-(82): nonnegative CQ coding family. The three arguments are the unconditional receiver entropy and the conditional receiver/complement entropies in bits, as functions of photon sharing lambda. This is a scalar inner family, with no assertion of operational achievability in its definition.
--   - `ceFamily`: PDF pp.7,14, (42)-(43) and the CE display: positive entanglement consumption. The coordinates are classical bits and consumed ebits per use.
--   - `cqTimeSharing`: PDF pp.6-8, Figure 2(a): same-budget endpoint time sharing, with rate disposal. Coordinates are (classical, quantum); t is the quantum-code time fraction.
--   - `ceTimeSharing`: PDF pp.7-8, Figure 2(b): same-budget CE endpoint mixtures. Extra consumption is allowed, while generated classical bits can be discarded.
--   - `lossCQ`: PDF pp.6-8: the displayed pure-loss CQ family at the stated photon budget.
--   - `lossCE`: PDF pp.7-8: the displayed pure-loss CE family, with consumption positive.
--   - `thermalD`: PDF p.14, (80): D is the nonnegative square root, rather than an arbitrary root.
--   - `thermalEnvironment`: PDF p.14, (80): entropy in bits of the TRUE complementary output. Both symplectic modes, including the environment purifier, contribute.
--   - `amplifierCQ`: PDF pp.16-17, Figure 6(a): vacuum-amplifier CQ family, at N_S=200.
--   - `amplifierCE`: PDF pp.16-17, Figure 6(b): vacuum-amplifier CE family, at N_S=200.
--   - `fockParity`: PDF p.5, (27): parity implements the environmental output phase in the source beam splitter relative to the accepted opposite-sign output convention.
--   - `lossComplement`: PDF p.5, (26)-(27): the fixed pure-loss complement on arbitrary block inputs. The imported receiver has precisely (26). Its unused port has the opposite sign to (27); parity on both matrix indices fixes that sign without changing entropy.
--   - `BlockEnsemble`: PDF pp.2,11, (60)-(63): a discrete block ensemble, allowing countably many nonzero weights and arbitrary intra-block entanglement. PMF labels may have zero mass.
--   - `BlockEnsemble.average`: PDF pp.4,11: the ensemble's actual unconditional density coefficients. Absolute convergence follows from trace-one states and normalized probabilities.
--   - `BlockEnsemble.energy`: PDF pp.2,11-12: averaged TOTAL input photon number. Sum the imported modeEnergy over modes, then average over the ensemble. By positivity this is the energy of the unconditional density.
--   - `blockEntropy`: PDF pp.2,11, (60)-(63): bit entropy, keeping infinity until after weighting.
--   - `BlockEnsemble.entropyAverage`: PDF p.11: weighted entropy is formed in the extended nonnegative reals. In particular a zero-probability label with infinite entropy contributes zero.
--   - `lossQuantumFamily`: PDF p.5, (28)-(30): all three faces of the signed pure-loss inner family. This scalar set is not used as the definition of any operational capacity.
--   - `BlockEnsemble.dynamicEntropyRegion`: PDF pp.3-4,11: the computed block-ensemble entropy region, scaled per use. Only finite-energy ensembles at positive blocklength enter the optimization below. Each entropy average is weighted BEFORE conversion to real; zero times infinity is zero. Input energy bounds imply finiteness of every converted average and the unconditional output entropy. Signed net rates are allowed in all coordinates.
--   - `gaussianDynamicOptimization`: PDF pp.11-13: regularized dynamic ENTROPY optimization restricted to Gaussian conditional input states, not to Gaussian gates or operational codes. All finite label sets and all positive blocklengths are included, followed by closure. Conditional states may have arbitrary Gaussian correlations among the n modes; their unconditional mixture is not required to be Gaussian. Finite alphabets with closure retain the continuous displaced-thermal ensemble through discretization.
-- source:
--   Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4, https://arxiv.org/abs/1105.0119v4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

/-!
Quantum trade-off coding for bosonic communication, arXiv:1105.0119v4.
Scalar coding-family comparisons and the common-parameter block entropy bounds.
Operational results lacking a full Fock-space code interface are recorded separately
in HARD.md and GAPS.json; no scalar family is defined to be an operational capacity.
Compilation and independent moderation are pending the separate batch stages.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P44

open Filter
open scoped ENNReal Topology
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

namespace Fock
export QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel pureLoss jointMix charlieMarginal vacuum
   modeEnergy spectralEntropyNats StrongConjecture2 Gaussian)
export QAlgorithms.Papers.Independent.Dependency50.P33 (State)
end Fock

/-- PDF pp.6,14, (40)-(41), (81)-(82): nonnegative CQ coding family.
The three arguments are the unconditional receiver entropy and the conditional
receiver/complement entropies in bits, as functions of photon sharing lambda.
This is a scalar inner family, with no assertion of operational achievability in its definition. -/
def cqFamily (output : ℝ) (conditional environment : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ share ∈ Set.Icc (0 : ℝ) 1,
    r.2 ≤ conditional share - environment share ∧
    r.1 + r.2 ≤ output - environment share}

/-- PDF pp.7,14, (42)-(43) and the CE display: positive entanglement consumption.
The coordinates are classical bits and consumed ebits per use. -/
def ceFamily (budget output : ℝ) (environment : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ share ∈ Set.Icc (0 : ℝ) 1,
    r.1 ≤ thermalEntropy (share * budget) + output - environment share ∧
    r.1 ≤ output - environment share + r.2}

/-- PDF pp.6-8, Figure 2(a): same-budget endpoint time sharing, with rate disposal.
Coordinates are (classical, quantum); t is the quantum-code time fraction. -/
def cqTimeSharing (classical quantum : ℝ) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ t ∈ Set.Icc (0 : ℝ) 1,
    r.1 ≤ (1 - t) * classical ∧ r.2 ≤ t * quantum}

/-- PDF pp.7-8, Figure 2(b): same-budget CE endpoint mixtures.
Extra consumption is allowed, while generated classical bits can be discarded. -/
def ceTimeSharing (unassisted assisted consumption : ℝ) : Set (ℝ × ℝ) :=
  {r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ ∃ t ∈ Set.Icc (0 : ℝ) 1,
    r.1 ≤ (1 - t) * unassisted + t * assisted ∧ t * consumption ≤ r.2}

/-- PDF pp.6-8: the displayed pure-loss CQ family at the stated photon budget. -/
def lossCQ (eta budget : ℝ) : Set (ℝ × ℝ) :=
  cqFamily (thermalEntropy (eta * budget))
    (fun share => thermalEntropy (eta * share * budget))
    (fun share => thermalEntropy ((1 - eta) * share * budget))

/-- PDF pp.7-8: the displayed pure-loss CE family, with consumption positive. -/
def lossCE (eta budget : ℝ) : Set (ℝ × ℝ) :=
  ceFamily budget (thermalEntropy (eta * budget))
    (fun share => thermalEntropy ((1 - eta) * share * budget))

/-- PDF p.14, (80): D is the nonnegative square root, rather than an arbitrary root. -/
def thermalD (eta share budget noise : ℝ) : ℝ :=
  Real.sqrt ((share * (1 + eta) * budget + (1 - eta) * noise + 1) ^ 2 -
    4 * eta * share * budget * (share * budget + 1))

/-- PDF p.14, (80): entropy in bits of the TRUE complementary output.
Both symplectic modes, including the environment purifier, contribute. -/
def thermalEnvironment (eta share budget noise : ℝ) : ℝ :=
  thermalEntropy ((thermalD eta share budget noise +
    share * (1 - eta) * budget - (1 - eta) * noise - 1) / 2) +
  thermalEntropy ((thermalD eta share budget noise -
    share * (1 - eta) * budget + (1 - eta) * noise - 1) / 2)

/-- PDF pp.16-17, Figure 6(a): vacuum-amplifier CQ family, at N_S=200. -/
def amplifierCQ (gain : ℝ) : Set (ℝ × ℝ) :=
  cqFamily (thermalEntropy (gain * 200 + gain - 1))
    (fun share => thermalEntropy (gain * share * 200 + gain - 1))
    (fun share => thermalEntropy ((gain - 1) * (share * 200 + 1)))

/-- PDF pp.16-17, Figure 6(b): vacuum-amplifier CE family, at N_S=200. -/
def amplifierCE (gain : ℝ) : Set (ℝ × ℝ) :=
  ceFamily 200 (thermalEntropy (gain * 200 + gain - 1))
    (fun share => thermalEntropy ((gain - 1) * (share * 200 + 1)))

/-- PDF p.5, (27): parity implements the environmental output phase in the
source beam splitter relative to the accepted opposite-sign output convention. -/
def fockParity {n : ℕ} (a : Fock.NumberString n) : ℂ :=
  (-1 : ℂ) ^ (∑ i, a i)

/-- PDF p.5, (26)-(27): the fixed pure-loss complement on arbitrary block inputs.
The imported receiver has precisely (26). Its unused port has the opposite sign
to (27); parity on both matrix indices fixes that sign without changing entropy. -/
def lossComplement (n : ℕ) (eta : ℝ) (rho : Fock.FockKernel n) :
    Fock.FockKernel n :=
  fun a b => fockParity a *
    Fock.charlieMarginal (Fock.jointMix n eta rho (Fock.vacuum n)) a b * star (fockParity b)

/-- PDF pp.2,11, (60)-(63): a discrete block ensemble, allowing countably many
nonzero weights and arbitrary intra-block entanglement. PMF labels may have zero mass. -/
structure BlockEnsemble (X : Type*) (n : ℕ) where
  probability : PMF X
  state : X → Fock.State (Fock.NumberString n)

/-- PDF pp.4,11: the ensemble's actual unconditional density coefficients.
Absolute convergence follows from trace-one states and normalized probabilities. -/
def BlockEnsemble.average {X : Type*} {n : ℕ} (e : BlockEnsemble X n) :
    Fock.FockKernel n :=
  fun a b => ∑' x, ((e.probability x).toReal : ℂ) * (e.state x).coefficients a b

/-- PDF pp.2,11-12: averaged TOTAL input photon number.
Sum the imported modeEnergy over modes, then average over the ensemble.
By positivity this is the energy of the unconditional density. -/
def BlockEnsemble.energy {X : Type*} {n : ℕ} (e : BlockEnsemble X n) : ℝ≥0∞ :=
  ∑' x, e.probability x * (∑ i : Fin n, Fock.modeEnergy (e.state x).coefficients i)

/-- PDF pp.2,11, (60)-(63): bit entropy, keeping infinity until after weighting. -/
def blockEntropy {n : ℕ} (rho : Fock.FockKernel n) : ℝ≥0∞ :=
  Fock.spectralEntropyNats rho / ENNReal.ofReal (Real.log 2)

/-- PDF p.11: weighted entropy is formed in the extended nonnegative reals.
In particular a zero-probability label with infinite entropy contributes zero. -/
def BlockEnsemble.entropyAverage {X : Type*} {n : ℕ} (e : BlockEnsemble X n)
    (channel : Fock.FockKernel n → Fock.FockKernel n) : ℝ≥0∞ :=
  ∑' x, e.probability x * blockEntropy (channel (e.state x).coefficients)

/-- PDF p.5, (28)-(30): all three faces of the signed pure-loss inner family.
This scalar set is not used as the definition of any operational capacity. -/
def lossQuantumFamily (eta budget : ℝ) : Set (Fin 3 → ℝ) :=
  {r | ∃ share ∈ Set.Icc (0 : ℝ) 1,
    r 0 + 2 * r 1 ≤ thermalEntropy (share * budget) + thermalEntropy (eta * budget) -
      thermalEntropy ((1 - eta) * share * budget) ∧
    r 1 + r 2 ≤ thermalEntropy (eta * share * budget) -
      thermalEntropy ((1 - eta) * share * budget) ∧
    r 0 + r 1 + r 2 ≤ thermalEntropy (eta * budget) -
      thermalEntropy ((1 - eta) * share * budget)}

/-- PDF pp.3-4,11: the computed block-ensemble entropy region, scaled per use.
Only finite-energy ensembles at positive blocklength enter the optimization below.
Each entropy average is weighted BEFORE conversion to real; zero times infinity
is zero. Input energy bounds imply finiteness of every converted average and the
unconditional output entropy. Signed net rates are allowed in all coordinates. -/
def BlockEnsemble.dynamicEntropyRegion {X : Type*} {n : ℕ}
    (e : BlockEnsemble X n) (eta : ℝ) : Set (Fin 3 → ℝ) :=
  let input := (e.entropyAverage id).toReal
  let output := (blockEntropy (Fock.pureLoss n eta e.average)).toReal
  let conditional := (e.entropyAverage (Fock.pureLoss n eta)).toReal
  let environment := (e.entropyAverage (lossComplement n eta)).toReal
  {r | (n : ℝ) * (r 0 + 2 * r 1) ≤ input + output - environment ∧
    (n : ℝ) * (r 1 + r 2) ≤ conditional - environment ∧
    (n : ℝ) * (r 0 + r 1 + r 2) ≤ output - environment}

/-- PDF pp.11-13: regularized dynamic ENTROPY optimization restricted to
Gaussian conditional input states, not to Gaussian gates or operational codes.
All finite label sets and all positive blocklengths are included, followed by closure.
Conditional states may have arbitrary Gaussian correlations among the n modes;
their unconditional mixture is not required to be Gaussian. Finite alphabets with
closure retain the continuous displaced-thermal ensemble through discretization. -/
def gaussianDynamicOptimization (eta budget : ℝ) : Set (Fin 3 → ℝ) :=
  closure {r | ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ, 0 < k ∧
    ∃ e : BlockEnsemble (Fin k) n,
      (∀ x, Fock.Gaussian (e.state x).coefficients) ∧
      e.energy ≤ ENNReal.ofReal ((n : ℝ) * budget) ∧
      r ∈ e.dynamicEntropyRegion eta}

example : g 0 = 0 := by simp [g]

example : thermalEntropy 0 = 0 := by simp [thermalEntropy]

example (N : ℝ) :
    (-1 : ℝ) ^ (0 + 2) / (((0 + 1 : ℕ) : ℝ) * ((0 + 2 : ℕ) : ℝ) * N ^ (0 + 1)) =
      1 / (2 * N) := by simp

example : (0, 0) ∈ cqFamily 0 (fun _ => 0) (fun _ => 0) := by
  refine ⟨le_rfl, le_rfl, 0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩ <;> simp

example : (0, 0) ∈ ceFamily 0 0 (fun _ => 0) := by
  refine ⟨le_rfl, le_rfl, 0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩ <;>
    simp [thermalEntropy]

example : (0, 0) ∈ cqTimeSharing 0 0 := by
  exact ⟨le_rfl, le_rfl, 0, ⟨le_rfl, zero_le_one⟩, by simp, by simp⟩

example : (0, 3) ∈ ceTimeSharing 0 0 0 := by
  refine ⟨le_rfl, by norm_num, 0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩ <;> norm_num

example (eta share : ℝ) : thermalD eta share 0 0 = 1 := by simp [thermalD]

example (eta share : ℝ) : thermalEnvironment eta share 0 0 = 0 := by
  simp [thermalEnvironment, thermalD, thermalEntropy]

example : fockParity (fun _ : Fin 1 => 1) = -1 := by simp [fockParity]

example (rho : Fock.FockKernel 0) : (∑ i : Fin 0, Fock.modeEnergy rho i) = 0 := by simp

example : (0 : ℝ≥0∞) * (⊤ : ℝ≥0∞) = 0 := by simp

example (eta : ℝ) : (0, 0) ∈ lossCQ eta 0 := by
  refine ⟨le_rfl, le_rfl, 0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩ <;>
    simp [thermalEntropy]

example (eta : ℝ) : (0, 0) ∈ lossCE eta 0 := by
  refine ⟨le_rfl, le_rfl, 0, ⟨le_rfl, zero_le_one⟩, ?_, ?_⟩ <;>
    simp [thermalEntropy]

example : amplifierCQ 1 = lossCQ 1 200 := by
  simp [amplifierCQ, lossCQ, thermalEntropy]

example : amplifierCE 1 = lossCE 1 200 := by
  simp [amplifierCE, lossCE, thermalEntropy]

example (n : ℕ) (rho : Fock.State (Fock.NumberString n)) :
    (BlockEnsemble.average
      (⟨PMF.pure (), fun _ : Unit => rho⟩ : BlockEnsemble Unit n)) = rho.coefficients := by
  classical
  ext a b
  simp [BlockEnsemble.average, PMF.pure_apply]

example (n : ℕ) (rho : Fock.State (Fock.NumberString n)) :
    (BlockEnsemble.energy
      (⟨PMF.pure (), fun _ : Unit => rho⟩ : BlockEnsemble Unit n)) =
      (∑ i : Fin n, Fock.modeEnergy rho.coefficients i) := by
  simp [BlockEnsemble.energy, PMF.pure_apply]

example (n : ℕ) (rho : Fock.State (Fock.NumberString n)) :
    (BlockEnsemble.entropyAverage
      (⟨PMF.pure (), fun _ : Unit => rho⟩ : BlockEnsemble Unit n) id) =
      blockEntropy rho.coefficients := by
  simp [BlockEnsemble.entropyAverage, PMF.pure_apply]

example (eta : ℝ) : (fun _ : Fin 3 => (0 : ℝ)) ∈ lossQuantumFamily eta 0 := by
  refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_, ?_, ?_⟩ <;> simp [thermalEntropy]

end QAlgorithms.Papers.Independent.Gap48.P44


