-- Prove2me | Definitions.Def_LowRankIncoherent_Adaptive_Experiment
-- name    : LowRankIncoherent_Adaptive_Experiment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:17:11.51856+00:00
-- url     : https://prove2.me/theorems/e2c379bd-6adf-48e5-86b3-8f1e74d2b3d9
-- title:
--   Haar/Born experiments and the TwoBatch decoder
-- statement:
--   A basis is obtained from exact Haar probability on the finite-dimensional unitary group, transported by a fixed coordinate equivalence to the register in use. Conditional on a basis matrix $U$ and state $X$, the outcome index has Born probability $⟨Ue_i|X|Ue_i⟩$. Both basis and index are classical outcomes. The observed vector gives
--   $$Y=(D+1)|ψ⟩⟨ψ|-I_D,\qquad \widehat X=n^{-1}\sum_{t=1}^nY_t.$$
--   The two batches have independent product laws at the same queried input. From the first estimate retain the $r$ largest positive eigenvalues in $S$ and form $R=(S+sI)^{-1}P_S$. The decoder returns
--   $$\widehat Z=\widehat X_1R\widehat X_1,\qquad \widehat H=(I_a-Φ_σ(\widehat Z)^†(I_b))/s.$$
--   The truncation function is only a deterministic argument to this decoder; its measurable structural admissibility is separately required or concluded. The distribution is computed from the Haar/Born experiment, without assuming snapshot moments or concentration. This supplies an operational interpretation for fresh batches conditional on an earlier transcript.
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), §2.4, Definitions 2.7–2.8 and equations (22)–(26), Definition 3.3 / Algorithm 2 / (41), printed pp. 11–13, 19 = PDF pp. 11–13, 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_MatrixModel
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

instance matrixMeasurable (ι κ : Type) [Fintype ι] [Fintype κ] : MeasurableSpace (Matrix ι κ ℂ) := borel _
instance matrixBorel (ι κ : Type) [Fintype ι] [Fintype κ] : BorelSpace (Matrix ι κ ℂ) := ⟨rfl⟩

/-- Exact Haar basis matrices on an arbitrary finite register, transported only by a fixed
coordinate equivalence. This is not a finite design or a state-dependent Haar law. -/
def basisLaw (ι : Type) [Fintype ι] [DecidableEq ι] : Measure (Mat ι) :=
  (QAlgorithms.Schur.unitaryHaar (Fintype.card ι)).map
    (fun (U : Matrix.unitaryGroup (Fin (Fintype.card ι)) ℂ) => Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm (U : Mat (Fin (Fintype.card ι))))

def column {ι : Type} (U : Mat ι) (i : ι) : ι → ℂ := fun j => U j i

def projector {ι : Type} (v : ι → ℂ) : Mat ι := fun i j => v i * star (v j)

def born {ι : Type} [Fintype ι] (X U : Mat ι) (i : ι) : ℝ :=
  (∑ j, ∑ k, star (U j i) * X j k * U k i).re

/-- U is sampled first from Haar, then i is sampled by the Born rule. Both remain in
classical memory, while no quantum register is carried into the next experiment. -/
def experimentLaw {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) : Measure (Mat ι × Fin (Fintype.card ι)) :=
  (basisLaw ι).bind (fun U => ∑ i : Fin (Fintype.card ι), (ENNReal.ofReal (born X U ((Fintype.equivFin ι).symm i))) • Measure.dirac (U,i))

def observed {ι : Type} [Fintype ι] (z : Mat ι × Fin (Fintype.card ι)) : ι → ℂ := column z.1 ((Fintype.equivFin ι).symm z.2)

def snapshot {ι : Type} [Fintype ι] [DecidableEq ι] (z : Mat ι × Fin (Fintype.card ι)) : Mat ι :=
  ((Fintype.card ι + 1 : ℕ) : ℂ) • projector (observed z) - 1

abbrev Batch (ι : Type) [Fintype ι] (n : ℕ) := Fin n → Mat ι × Fin (Fintype.card ι)
abbrev BatchPair (ι : Type) [Fintype ι] (n : ℕ) := Batch ι n × Batch ι n

def batchLaw {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) (n : ℕ) : Measure (Batch ι n) :=
  Measure.pi (fun _ : Fin n => experimentLaw X)

def pairLaw {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) (n : ℕ) : Measure (BatchPair ι n) :=
  (batchLaw X n).prod (batchLaw X n)

def estimate {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (z : Batch ι n) : Mat ι :=
  (1 / (n : ℂ)) • ∑ i, snapshot (z i)

/-- Deterministic TwoBatch decoder. The only user choice is how a tied eigenspace is
split; admissibility is separately stated, and contains no error guarantee. -/
def twoBatch {a b n : ℕ} (truncate : Joint a b → Joint a b)
    (σ : Input a) (s : ℝ) (z : BatchPair (Fin b × Fin a) n) : Joint a b × Input a :=
  let S := truncate (estimate z.1)
  let R := resolvent s S
  let Z := estimate z.2 * R * estimate z.2
  (Z, (1/s : ℂ) • (1 - adjointI σ Z))

end LowRankIncoherent.Adaptive


