-- Prove2me | Definitions.Def_QAlgorithms_Defs_MitigationTomography
-- name    : QAlgorithms_Defs_MitigationTomography
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:18:16.705985+00:00
-- url     : https://prove2.me/theorems/7105d48a-3dbd-4fe7-89a7-c587290ccd5a
-- title:
--   MitigationTomography
-- statement:
--   MitigationTomography
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MitigationTomography.lean

import Definitions.Def_QAlgorithms_Defs_MitigationMeasurements
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.ErrorMitigation

/-- arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.7; arxiv-1712.09271v2 PDF p.14; arxiv-1712.09271v2 PDF p.18. -/
structure TomographicFrame (n : ℕ) where
  preparation : PauliIndex n → Matrix (Qubits n) (Qubits n) ℂ
  density : ∀ k, IsDensityMatrix (preparation k)
  measurement : PauliIndex n → ObservableMeasurement (Qubits n)

/-- Columns of physical preparations, A2 (1712.09271 pp.12,14).
arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.7; arxiv-1712.09271v2 PDF p.14; arxiv-1712.09271v2 PDF p.18. -/
def TomographicFrame.inputMatrix {n : ℕ} (F : TomographicFrame n) :
    Matrix (PauliIndex n) (PauliIndex n) ℝ :=
  Matrix.of fun sigma k => pauliStateVector (F.preparation k) sigma

/-- Rows of physical valued observables, A4 (1712.09271 pp.13--14).
arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.7; arxiv-1712.09271v2 PDF p.14; arxiv-1712.09271v2 PDF p.18. -/
def TomographicFrame.outputMatrix {n : ℕ} (F : TomographicFrame n) :
    Matrix (PauliIndex n) (PauliIndex n) ℝ :=
  Matrix.of fun j sigma => pauliObservableRow (F.measurement j).observable sigma

/-- Exactly measured calibration data; targets chosen independently (1712.09271 p.14, E3).
arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.7; arxiv-1712.09271v2 PDF p.14; arxiv-1712.09271v2 PDF p.18. -/
def TomographicFrame.gram {n : ℕ} (F : TomographicFrame n) := F.outputMatrix*F.inputMatrix

/-- Public invertible matrices g,T from exact GST (1712.09271 pp.14,18). -/
structure GSTData (J : Type*) [Fintype J] [DecidableEq J] where
  g : Matrix J J ℝ
  T : Matrix J J ℝ
  g_unit : IsUnit g
  T_unit : IsUnit T

/-- Estimated input/output frames and operation, in that order (1712.09271 p.14, E4--E6).
arxiv-1712.09271v2 PDF p.6; arxiv-1712.09271v2 PDF p.7; arxiv-1712.09271v2 PDF p.14; arxiv-1712.09271v2 PDF p.18. -/
def gstEstimates {J : Type*} [Fintype J] [DecidableEq J] (G : GSTData J)
    (Otilde : Matrix J J ℝ) : Matrix J J ℝ × (Matrix J J ℝ × Matrix J J ℝ) :=
  (G.T,(G.g*G.T⁻¹,G.T*G.g⁻¹*Otilde*G.T⁻¹))

/-- Sanity check for the source model (arxiv-1712.09271v2 PDF p.6). -/
example {J : Type*} [Fintype J] [DecidableEq J] (G : GSTData J) (O : Matrix J J ℝ) :
    (gstEstimates G O).1 = G.T := rfl

end QAlgorithms.ErrorMitigation


