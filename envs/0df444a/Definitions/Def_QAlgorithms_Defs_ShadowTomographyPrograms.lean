-- Prove2me | Definitions.Def_QAlgorithms_Defs_ShadowTomographyPrograms
-- name    : QAlgorithms_Defs_ShadowTomographyPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:25.529778+00:00
-- url     : https://prove2.me/theorems/38b4605a-bdbf-4c3f-bdd0-dece76799842
-- title:
--   ShadowTomographyPrograms
-- statement:
--   ShadowTomographyPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ShadowTomographyPrograms.lean

import Definitions.Def_QAlgorithms_Defs_AdaptiveMixedMeasurements
noncomputable section

namespace QAlgorithms.ShadowTomography

variable {n m d k b w M K N c out : ℕ}

/-- Explicit physical procedure data on k copies with known ancillas,
1711.01053 pp.2,13–16. All estimates lie in [0,1]; unknown rho is absent
from the procedure, decoder and initial ancilla data. -/
structure TomographyProcedure (D M : ℕ) where
  copies : ℕ
  ancillas : ℕ
  outcomes : ℕ
  initialAncilla : Matrix (Fin ancillas) (Fin ancillas) ℂ
  initial_density : IsDensityMatrix initialAncilla
  procedure : CopyMeasurements.AdaptiveMeasurementProcedure
    ((Fin copies → Fin D) × Fin ancillas) (Fin outcomes)
  decode : Fin outcomes → Fin M → Set.Icc (0 : ℝ) 1

/-- A known-input constructor of explicit adaptive physical tomography
procedures, 1711.01053 p.3 Theorem 2 and p.19's online-learning replacement.
No accuracy/copy bound is assumed as a field. This is the operational
interface; the concrete p.19 online-learning/Gentle-Search constructor
is an outstanding prerequisite documented in the unit status. -/
structure ProcedureFamily where
  construct : (D M : ℕ) → (Fin M → Matrix (Fin D) (Fin D) ℂ) →
    ℝ → ℝ → TomographyProcedure D M

/-- Simultaneous accuracy contract on the same operational law,
1711.01053 p.2 Problem 1. Neither average error nor state reconstruction
replaces the displayed all-measurements event. -/
def IsAccurate {D M : ℕ} (P : TomographyProcedure D M)
    (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (eps delta : ℝ) : Prop :=
  ∀ rho : Matrix (Fin D) (Fin D) ℂ, IsDensityMatrix rho →
    (open Classical in
      ∑ o : Fin P.outcomes, if (∀ i, |(P.decode o i).val - effectProb (E i) rho| ≤ eps)
        then CopyMeasurements.procedureLaw P.procedure
          (Matrix.kronecker (piKron P.copies rho) P.initialAncilla) o else 0) ≥ 1-delta

/-- Uniform precise expansion of the selected soft copy bound,
1711.01053 pp.3,19. Only the named iterated-log and accuracy polylogs are
suppressed; floored logs preserve D=1/M=1 boundary cases. -/
def SoftSampleBound (F : ProcedureFamily) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ,
    ∀ D M, 1 ≤ D → 1 ≤ M → ∀ E : Fin M → Matrix (Fin D) (Fin D) ℂ,
    (∀ i, IsEffect (E i)) → ∀ eps delta : ℝ,
    0 < eps → eps < 1 → 0 < delta → delta < 1 →
      (F.construct D M E eps delta).copies ≤
        ⌈C * eps⁻¹ ^ 4 * max 1 (Real.log delta⁻¹) * max 1 (Real.log M) ^ 4 *
          max 1 (Real.log D) *
          (1 + max 1 (Real.log (max 1 (Real.log M))) +
            max 1 (Real.log (max 1 (Real.log D))) + max 1 (Real.log eps⁻¹)) ^ p⌉₊

/-- Sanity check for the modeled source objects (arxiv-1711.01053v2, PDF pp.2,3,14,19). -/
example {D M : ℕ} (P : TomographyProcedure D M)
    (E : Fin M → Matrix (Fin D) (Fin D) ℂ) (eps : ℝ)
    (h : IsAccurate P E eps 0) (rho : Matrix (Fin D) (Fin D) ℂ) (hrho : IsDensityMatrix rho) :
    (open Classical in
      ∑ o : Fin P.outcomes, if (∀ i, |(P.decode o i).val - effectProb (E i) rho| ≤ eps)
        then CopyMeasurements.procedureLaw P.procedure
          (Matrix.kronecker (piKron P.copies rho) P.initialAncilla) o else 0) ≥ 1 := by
  simpa using h rho hrho

end QAlgorithms.ShadowTomography


