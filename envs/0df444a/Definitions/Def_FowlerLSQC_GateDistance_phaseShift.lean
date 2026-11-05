-- Prove2me | Definitions.Def_FowlerLSQC_GateDistance_phaseShift
-- name    : FowlerLSQC_GateDistance_phaseShift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:28.973402+00:00
-- url     : https://prove2.me/theorems/cac6e129-6a09-4075-a3db-d635c3646b13
-- title:
--   Global phase: the gate $e^{i\alpha}U\in U(m)$
-- statement:
--   For a real number $\alpha$ and a gate $U\in U(m)$, this is the gate $e^{i\alpha}U\in U(m)$, namely $U$ multiplied by the **global phase** $e^{i\alpha}$.
--
--   Two gates that differ only by a global phase act identically on quantum states up to an unobservable phase. The definition lets the mission state what it means for a distance to "ignore global phase".
--
--   **Formalization Note** The underlying matrix is the scalar multiple `Complex.exp (α * I) • U`. The module also records this as the simp lemma `coe_phaseShift`.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.1, p.110 (PDF 128) ("does not ignore global phase")

import Mathlib

namespace FowlerLSQC.GateDistance

/-- The gate `e^{iα} U ∈ U(m)`: the gate `U` multiplied by the global phase `e^{iα}`, the operation
that Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.1, p.110
(PDF 128), refers to when saying that a distance does or does not "ignore global phase".

**Formalization Note** The underlying matrix is the scalar multiple `Complex.exp (α * I) • U`, and
`α` is any real number. -/
noncomputable def phaseShift {m : ℕ} (α : ℝ) (U : Matrix.unitaryGroup (Fin m) ℂ) :
    Matrix.unitaryGroup (Fin m) ℂ :=
  ⟨Complex.exp ((α : ℂ) * Complex.I) • (U : Matrix (Fin m) (Fin m) ℂ), by
    have hc : star (Complex.exp ((α : ℂ) * Complex.I)) * Complex.exp ((α : ℂ) * Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp
    rw [Matrix.mem_unitaryGroup_iff', star_smul, smul_mul_smul_comm, hc, one_smul]
    exact Matrix.UnitaryGroup.star_mul_self U⟩

/-- The matrix of `phaseShift α U` is `e^{iα} U`. -/
@[simp]
theorem coe_phaseShift {m : ℕ} (α : ℝ) (U : Matrix.unitaryGroup (Fin m) ℂ) :
    ((phaseShift α U : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) =
      Complex.exp ((α : ℂ) * Complex.I) • (U : Matrix (Fin m) (Fin m) ℂ) := rfl

end FowlerLSQC.GateDistance


