-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P36
-- name    : QAlgorithms_Papers_Independent_Bridge50_P36
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T16:14:42.070738+00:00
-- url     : https://prove2.me/theorems/0b529bb1-d6d2-4c2d-8d34-741ce537a6c8
-- title:
--   Definitions for Superadditivity of private information for any number of uses of the channel
-- statement:
--   The objects the formalized statements of *Superadditivity of private information for any number of uses of the channel* (arXiv:1502.05326) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `lockingInformation`: PDF p.2, (8): locking information over all normalized finite mixed-state ensembles. The accepted accessible-information interface optimizes all finite POVMs with no outcome bound on the entire complementary output. The same ensemble occurs in both terms; no finite-ensemble attainment is assumed.
--   - `erasureReceiver`: PDF p.3, (16): specialize the accepted pure orthogonal-flag erasure isometry to input dimension d and take its receiver marginal.
--   - `gammaValue`: PDF p.3, (17): the printed finite-d sequence. Its limit is 1-EulerGamma; the false printed limiting claim is separately deferred.
--   - `harmonicValue`: PDF p.5, (A1)–(A2): printed harmonic number, including t=1.
--   - `basisProbability`: PDF p.5: basis probabilities after a unitary. Used only for density inputs and exact unitaries in the subentropy statement.
--   - `subentropy`: PDF p.5, (A1): standard subentropy in bits, using the corrected offset sum_{t=2}^d 1/t. Printed (A1) subtracts H_d and is off by log_2(e). The corrected Haar-average formula is verified in arXiv:1310.1312 p.2 (2). For density inputs the integrand is continuous and bounded on compact U(d), so the Bochner integral has no nonintegrable junk-zero case.
-- source:
--   Superadditivity of private information for any number of uses of the channel, arXiv:1502.05326v1, https://arxiv.org/abs/1502.05326v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

/-!
Statements from Elkouss and Strelchuk, arXiv:1502.05326v1.
Page references are PDF pages. New definitions belong only to this paper.
Information is in bits. Compilation is pending the batch handoff.
The full Lemma 1, the false gamma-limit claim, (26), (28), and Conjecture 1
are deferred in HARD.md; no weakened replacements are asserted.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P36

open scoped BigOperators Matrix ComplexConjugate
open MeasureTheory

-- These imports are pinned accepted libraries, permitted by the repair task.
-- P08.Ensemble allows an impossible zero-sized normalized ensemble; its total=1
-- field excludes that case without a separate positive-size field.
open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo channelHolevo)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel maximumCoherentInformation dilationPower erasureDilation)
open QAlgorithms.Papers.Independent.Dependency50.P07 (accessibleInformation)
open QAlgorithms.Papers.Independent.Dependency50.P48 (privateMaximum)

variable {A B E C D : Type}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]
variable [Fintype D] [DecidableEq D]

/-- PDF p.2, (8): locking information over all normalized finite mixed-state
ensembles. The accepted accessible-information interface optimizes all finite
POVMs with no outcome bound on the entire complementary output. The same
ensemble occurs in both terms; no finite-ensemble attainment is assumed. -/
def lockingInformation (V : Matrix (B × E) A ℂ) : ℝ :=
  sSup {r | ∃ ens : Ensemble A,
    r = outputHolevo (receiverChannel V) ens -
      accessibleInformation
        (QAlgorithms.Papers.Independent.Dependency50.P07.CQData.mk ens.prob
          (fun x => complementaryChannel V (ens.state x)))}

/-- PDF p.3, (16): specialize the accepted pure orthogonal-flag erasure
isometry to input dimension d and take its receiver marginal. -/
def erasureReceiver (p : ℝ) (d : ℕ) : Superop (Fin d) (Option (Fin d)) :=
  receiverChannel (erasureDilation (A := Fin d) p)

/-- PDF p.3, (17): the printed finite-d sequence. Its limit is
1-EulerGamma; the false printed limiting claim is separately deferred. -/
def gammaValue (d : ℕ) : ℝ :=
  Real.log (d : ℝ) - ∑ t ∈ Finset.Icc 2 d, (t : ℝ)⁻¹

/-- PDF p.5, (A1)–(A2): printed harmonic number, including t=1. -/
def harmonicValue (d : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 d, (t : ℝ)⁻¹

/-- PDF p.5: basis probabilities after a unitary. Used only for density
inputs and exact unitaries in the subentropy statement. -/
def basisProbability {d : ℕ} (U rho : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) : ℝ :=
  ((U * rho * Uᴴ) i i).re

/-- PDF p.5, (A1): standard subentropy in bits, using the corrected offset
sum_{t=2}^d 1/t. Printed (A1) subtracts H_d and is off by log_2(e).
The corrected Haar-average formula is verified in arXiv:1310.1312 p.2 (2).
For density inputs the integrand is continuous and bounded on compact U(d),
so the Bochner integral has no nonintegrable junk-zero case. -/
def subentropy {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    shannon (basisProbability (U : Matrix (Fin d) (Fin d) ℂ) rho)
      ∂QAlgorithms.Schur.unitaryHaar d) -
    (∑ t ∈ Finset.Icc 2 d, (t : ℝ)⁻¹) / Real.log 2

/-! Definition sanity examples; no source theorem is proved here. -/

example (V : Matrix (B × E) A ℂ) (be : (Fin 0 → B) × (Fin 0 → E))
    (a : Fin 0 → A) : dilationPower V 0 be a = 1 := by
  simp [dilationPower]

example (p : ℝ) (d : ℕ) (a : Fin d) : erasureDilation (A := Fin d) p (none, none) a = 0 := by
  simp [erasureDilation]

example (d : ℕ) (a : Fin d) : erasureDilation (A := Fin d) 0 (some a, none) a = 1 := by
  simp [erasureDilation]

example (d : ℕ) (a : Fin d) : erasureDilation (A := Fin d) 1 (none, some a) a = 1 := by
  simp [erasureDilation]

example : gammaValue 1 = 0 := by
  norm_num [gammaValue]

example : harmonicValue 1 = 1 := by
  norm_num [harmonicValue]

example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    basisProbability 1 rho i = (rho i i).re := by
  simp [basisProbability]

-- The explicit Fin 1 change prevents a residual arbitrary-cardinality sum.
example (rho : Matrix A A ℂ) (hRho : IsDensityMatrix rho) (N : Superop A B) :
    let ens : Ensemble A :=
      { size := 1, prob := fun _ => 1, state := fun _ => rho,
        nonneg := fun _ => by norm_num, total := by simp,
        density := fun _ => hRho }
    outputHolevo N ens = 0 := by
  change vnEntropy (N (∑ _ : Fin 1, (1 : ℝ) • rho)) -
    (∑ _ : Fin 1, (1 : ℝ) * vnEntropy (N rho)) = 0
  simp

example : subentropy (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  have hu (U : Matrix.unitaryGroup (Fin 1) ℂ) (i : Fin 1) :
      basisProbability (U : Matrix (Fin 1) (Fin 1) ℂ) 1 i = 1 := by
    have hU : (U : Matrix (Fin 1) (Fin 1) ℂ) *
        (U : Matrix (Fin 1) (Fin 1) ℂ)ᴴ = 1 :=
      Unitary.mul_star_self_of_mem U.property
    simp only [basisProbability, mul_one, hU]
    simp
  have hz (U : Matrix.unitaryGroup (Fin 1) ℂ) :
      shannon (basisProbability (U : Matrix (Fin 1) (Fin 1) ℂ) 1) = 0 := by
    simp [shannon, hu]
  norm_num [subentropy, hz]

end QAlgorithms.Papers.Independent.Bridge50.P36


