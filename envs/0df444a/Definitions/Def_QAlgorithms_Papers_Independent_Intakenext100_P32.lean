-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P32
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P32
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:59:56.623903+00:00
-- url     : https://prove2.me/theorems/46478e89-a8eb-4c70-b9d3-7cc6845939c4
-- title:
--   Definitions for Degrees of concealment and bindingness in quantum bit commitment protocols
-- statement:
--   The objects the formalized statements of *Degrees of concealment and bindingness in quantum bit commitment protocols* (arXiv:quant-ph/0106019) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CommonQubitSupport`: PDF p.4, Lemma 1: both supports are contained in the SAME subspace of complex dimension at most two. Finite dimensionality guards `finrank` against its zero value on infinite-dimensional spaces. Range containment is equivalent to support containment here because a finite-dimensional subspace is closed.
--   - `qutritToken`: PDF p.8, Section VI.B: the two explicit diagonal token states. The parameter is restricted to [0,1] in the statement, where positivity and trace one hold.
-- source:
--   Degrees of concealment and bindingness in quantum bit commitment protocols, arXiv:quant-ph/0106019v2, https://arxiv.org/abs/quant-ph/0106019v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P44

/-!
Spekkens and Rudolph, arXiv:quant-ph/0106019v2, PDF pp.4,7--8,10--11.
The independent-paper workflow permits the inspected pinned accepted-library import.
General density operators, root fidelity and trace norm are reused from Support50.P44.
They act on genuine Hilbert spaces, without a finite-dimensional cutoff. The finite
matrices below describe only the explicitly three-dimensional example on PDF p.8.
Protocol-dependent nodes are deferred in HARD.md: neither a scalar security budget
nor a holding-phase attack is substituted for the missing full strategy semantics.
Compilation is pending the mechanical batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P32

open QAlgorithms.Papers.Independent.Support50.P44
  (IsHilbertDensity hilbertFidelity hilbertTraceNorm)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.4, Lemma 1: both supports are contained in the SAME subspace of
complex dimension at most two. Finite dimensionality guards `finrank` against
its zero value on infinite-dimensional spaces. Range containment is equivalent
to support containment here because a finite-dimensional subspace is closed. -/
def CommonQubitSupport (rho sigma : H →L[ℂ] H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ 2 ∧
    (∀ x : H, rho x ∈ S) ∧ (∀ x : H, sigma x ∈ S)

/-- PDF p.8, Section VI.B: the two explicit diagonal token states. The parameter
is restricted to [0,1] in the statement, where positivity and trace one hold. -/
def qutritToken (b : Bool) (lam : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (if b then ![0, ((1 - lam : ℝ) : ℂ), (lam : ℂ)]
    else ![(lam : ℂ), ((1 - lam : ℝ) : ℂ), 0])

example : CommonQubitSupport (0 : H →L[ℂ] H) 0 := by
  refine ⟨⊥, inferInstance, ?_, ?_, ?_⟩
  · simp
  · intro x
    simp
  · intro x
    simp

example : qutritToken false 0 = qutritToken true 0 := by
  simp [qutritToken]

end QAlgorithms.Papers.Independent.Intakenext100.P32


