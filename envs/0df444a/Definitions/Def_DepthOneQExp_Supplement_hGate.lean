-- Prove2me | Definitions.Def_DepthOneQExp_Supplement_hGate
-- name    : DepthOneQExp_Supplement_hGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:33:16.004062+00:00
-- url     : https://prove2.me/theorems/2e4818a9-853e-4638-94e6-4d87cb25da91
-- title:
--   The Hadamard gate $H$
-- statement:
--   The Hadamard gate
--   $$
--   H = \frac{1}{\sqrt 2}\begin{pmatrix} 1 & 1 \\ 1 & -1\end{pmatrix},
--   $$
--   as a gate of arity 1. Its entry in row $x$ and column $y$ ($x, y\in\{0,1\}$) is $(-1)^{xy}/\sqrt2$. Together with the phase gate $S$ and CNOT it generates the Clifford group $\mathrm{Cl}(n) = \langle H_j, S_j, \mathrm{CNOT}_{j,k}\rangle$ of Eq. (2.55).
--
--   **Formalization Note** A `MITMSynthesis.Gate` of arity 1; unitarity is proved in the module.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), §2.4, Eq. (2.55), p.15

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp.Supplement

/-- The Hadamard gate `H = (1/√2)[[1, 1], [1, −1]]` as a gate of arity 1
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, §2.4, Eq. (2.55), p.15: `H_j` is the Hadamard gate on qubit `j`).

**Formalization Note** The entry in row `x` and column `y` is `(−1)^{x·y}/√2`, i.e. `−1/√2` exactly
when both bits are `1`. -/
noncomputable def hGate : MITMSynthesis.Gate :=
  ⟨1, one_pos,
    ⟨Matrix.of fun x y : MITMSynthesis.Q 1 =>
        (if x 0 = 1 ∧ y 0 = 1 then -1 else 1) / (Real.sqrt 2 : ℂ), by
      rw [Matrix.mem_unitaryGroup_iff]
      have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
      have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; positivity
      ext x y
      rw [Matrix.mul_apply, ← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp, Fin.sum_univ_two]
      have key : ∀ b : Fin 2, b = 0 ∨ b = 1 := fun b => by fin_cases b <;> simp
      have ext1 : ∀ u v : MITMSynthesis.Q 1, u = v ↔ u 0 = v 0 := fun u v =>
        ⟨fun h => h ▸ rfl, fun h => funext fun i => by rw [Subsingleton.elim i 0]; exact h⟩
      simp only [Matrix.one_apply, Matrix.star_apply, ext1, Equiv.funUnique_symm_apply]
      simp only [Complex.star_def]
      rcases key (x 0) with h | h <;> rcases key (y 0) with h' | h' <;>
        simp [h, h'] <;> field_simp <;> (try simp [h2]) <;> (try norm_num)⟩⟩

end DepthOneQExp.Supplement


