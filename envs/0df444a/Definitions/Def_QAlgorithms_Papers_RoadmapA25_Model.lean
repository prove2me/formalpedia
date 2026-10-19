-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapA25_Model
-- name    : QAlgorithms_Papers_RoadmapA25_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:21.307926+00:00
-- url     : https://prove2.me/theorems/e694478e-4cbe-4f2b-910a-c0f56a777bbd
-- title:
--   Amplitude Estimation from Quantum Signal Processing: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Amplitude Estimation from Quantum Signal Processing, arXiv:2207.08628v3, https://arxiv.org/abs/2207.08628v3. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_GroverSampling
/-!
Theorem 6 of Rall and Fuller, *Amplitude Estimation from Quantum Signal Processing*,
arXiv:2207.08628v3, PDF p.14 (printed p.14), equation (39).

We use the completed two-dimensional Grover space of equations (3)--(6), including
amplitudes 0 and 1. The oracle-assisted basis measurement in the proof of Proposition 3
uses controlled rotations; these are counted in the instrument. Semi-Pellian sampling
uses the distinct opposite-angle oracle of equation (30). Ancillas alone are measured;
the signal is retained. Equality of branch density matrices ignores global phase.
-/

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.RoadmapA25

/-- The exact sampling and retained-state contract in Theorem 6, PDF p.14, equation (39).
The four labels are the known classical input/output labels. The branch trace is its
probability, and a zero-probability branch has the zero density matrix. -/
def SamplesWithRetainedSignal {n : ℕ} (I : GroverSamplingInstrument n)
    (value : ℝ → ℂ) : Prop :=
  ∀ (F : GroverFrame) (input : GroverLabel),
    (∑ label ∈ ({GroverLabel.psi, GroverLabel.psiPerp, GroverLabel.pi,
        GroverLabel.piPerp} : Finset GroverLabel),
      (groverInstrumentBranch I F input (pureDensity (F.state input)) true label).trace.re) =
        ‖value F.amplitude.val‖ ^ 2 ∧
    ∀ (b : Bool) (label : GroverLabel),
      groverInstrumentBranch I F input (pureDensity (F.state input)) b label =
        (((groverInstrumentBranch I F input (pureDensity (F.state input)) b label).trace.re :
          ℝ) : ℂ) • pureDensity (F.state label)


end QAlgorithms.Papers.RoadmapA25


