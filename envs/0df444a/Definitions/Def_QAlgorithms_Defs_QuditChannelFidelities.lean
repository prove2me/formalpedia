-- Prove2me | Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
-- name    : QAlgorithms_Defs_QuditChannelFidelities
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:36.200004+00:00
-- url     : https://prove2.me/theorems/51a67cde-c891-4623-a009-549dfb164ad3
-- title:
--   QuditChannelFidelities
-- statement:
--   QuditChannelFidelities
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\QuditChannelFidelities.lean

import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.QuditFidelity

open MeasureTheory

/-- arxiv-quant-ph-0205035v2 PDF p.1. -/
def haarPureStateLaw (d : ℕ) (hd : 0 < d) : Measure (EuclideanSpace ℂ (Fin d)) :=
  (Schur.unitaryHaar d).map (fun U : Matrix.unitaryGroup (Fin d) ℂ => act (U : Matrix (Fin d) (Fin d) ℂ) (ket ⟨0,hd⟩))

/-- arxiv-quant-ph-0205035v2 PDF p.1. -/
def averageFidelity (d : ℕ) (hd : 0 < d) (E : Superop (Fin d) (Fin d)) : ℝ :=
  ∫ psi, effectProb (pureDensity psi) (E (pureDensity psi)) ∂haarPureStateLaw d hd

/-- arxiv-quant-ph-0205035v2 PDF p.1; arxiv-quant-ph-0205035v2 PDF p.2. -/
def entanglementFidelity (d : ℕ) (hd : 0 < d) (E : Superop (Fin d) (Fin d)) : ℝ :=
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let phi := finiteMaxEntangled (Fin d)
  effectProb (pureDensity phi) (idTensorSuperop E (pureDensity phi))

/-- arxiv-quant-ph-0205035v2 PDF p.1; arxiv-quant-ph-0205035v2 PDF p.2. -/
def haarTwirl (d : ℕ) (_hd : 0 < d) (E : Superop (Fin d) (Fin d)) : Superop (Fin d) (Fin d) :=
  fun X => ∫ U, conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ))
    (E (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) X)) ∂Schur.unitaryHaar d

/-- arxiv-quant-ph-0205035v2 PDF p.2. -/
def depolarizingMap (d : ℕ) (_hd : 0 < d) (p : ℝ) : Superop (Fin d) (Fin d) :=
  fun X => (((p/d : ℝ) : ℂ)*X.trace) • 1 + ((1-p : ℝ) : ℂ) • X

/-- CPT maps are continuous by their finite Kraus form (0205035 p.1). -/
theorem channel_continuous {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) : Continuous E := by
  obtain ⟨m,K,_,hK⟩ := hE
  have he : E = krausApply K := funext hK
  rw [he]
  unfold krausApply
  fun_prop

/-- The actual Haar state-preparation map is continuous (0205035 p.1). -/
theorem haarState_continuous (d : ℕ) (hd : 0 < d) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => act (U : Matrix (Fin d) (Fin d) ℂ) (ket ⟨0,hd⟩)) := by
  unfold act
  fun_prop

/-- Haar pure-state mass is one, proved rather than a free probability assumption
(0205035 p.1). -/
theorem haarPureStateLaw_univ (d : ℕ) (hd : 0 < d) : haarPureStateLaw d hd Set.univ = 1 := by
  rw [haarPureStateLaw,Measure.map_apply (haarState_continuous d hd).measurable MeasurableSet.univ]
  exact Measure.haarMeasure_self

/-- Every vector in the specified Haar preparation image is normalized (0205035 p.1). -/
example (d : ℕ) (hd : 0 < d) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsState (act (U : Matrix (Fin d) (Fin d) ℂ) (ket ⟨0,hd⟩)) := by
  rw [IsState,act_norm_of_mem_unitaryGroup U.property]
  simp [ket]

/-- The average-fidelity integrand is integrable for every lawful channel, using the
actual compact Haar image; the Bochner integral cannot default to zero because of
nonintegrability (0205035 p.1). -/
theorem averageFidelity_integrable (d : ℕ) (hd : 0 < d) (E : Superop (Fin d) (Fin d))
    (hE : IsChannel E) :
    Integrable (fun psi => effectProb (pureDensity psi) (E (pureDensity psi))) (haarPureStateLaw d hd) := by
  have hp : Continuous (fun psi : EuclideanSpace ℂ (Fin d) => pureDensity psi) := by
    unfold pureDensity; fun_prop
  have hcE := channel_continuous E hE
  have hf : Continuous (fun psi : EuclideanSpace ℂ (Fin d) =>
      effectProb (pureDensity psi) (E (pureDensity psi))) := by
    obtain ⟨m,K,_,hK⟩ := hE
    simp_rw [hK]
    unfold effectProb krausApply pureDensity
    fun_prop
  have hc := hf.comp (haarState_continuous d hd)
  have hm : (Schur.unitaryHaar d) Set.univ ≠ ⊤ := by
    have he : (Schur.unitaryHaar d) Set.univ = 1 := Measure.haarMeasure_self
    rw [he]; simp
  have hi := hc.continuousOn.integrableOn_of_subset_isCompact isCompact_univ
    MeasurableSet.univ (Set.Subset.rfl) hm
  rw [haarPureStateLaw]
  apply (integrable_map_measure hf.aestronglyMeasurable
    (haarState_continuous d hd).measurable.aemeasurable).mpr
  simpa [IntegrableOn,Function.comp_def] using hi

/-- Twirling is a genuine integral of every lawful finite-dimensional channel
(0205035 p.2). -/
theorem haarTwirl_integrable (d : ℕ) (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    Integrable (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) (E (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) X)))
      (Schur.unitaryHaar d) := by
  have hcE := channel_continuous E hE
  have hc : Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      conjSuperop (star (U : Matrix (Fin d) (Fin d) ℂ)) (E (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) X))) := by
    obtain ⟨m,K,_,hK⟩ := hE
    simp_rw [hK]
    unfold conjSuperop krausApply
    fun_prop
  have hm : (Schur.unitaryHaar d) Set.univ ≠ ⊤ := by
    have he : (Schur.unitaryHaar d) Set.univ = 1 := Measure.haarMeasure_self
    rw [he]; simp
  simpa [IntegrableOn] using hc.continuousOn.integrableOn_of_subset_isCompact
    isCompact_univ MeasurableSet.univ Set.Subset.rfl hm

/-- Sanity check for the source model (arxiv-quant-ph-0205035v2 PDF p.1). -/
example (d : ℕ) (hd : 0 < d) (X : Matrix (Fin d) (Fin d) ℂ) :
    depolarizingMap d hd 0 X = X := by simp [depolarizingMap]

/-- Sanity check for the source model (arxiv-quant-ph-0205035v2 PDF p.1). -/
example (d : ℕ) (hd : 0 < d) : averageFidelity d hd (fun _ => 0) = 0 := by
  simp [averageFidelity,effectProb]

end QAlgorithms.QuditFidelity


