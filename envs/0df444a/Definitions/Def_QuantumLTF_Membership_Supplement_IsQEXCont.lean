-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_IsQEXCont
-- name    : QuantumLTF_Membership_Supplement_IsQEXCont
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:35:58.848902+00:00
-- url     : https://prove2.me/theorems/7223d4b9-2f47-4725-8c0b-6055199efe11
-- title:
--   Valid continuous example oracle $\mathsf{QEX}(f_w,\gamma_n)$
-- statement:
--   Let $H_X=L^2(\mathbb R^n\times\{0,1\})$ (Lebesgue measure times counting measure). Given a designated unit vector $\psi_0\in H_X$ (the input "$|0\rangle$"), a unitary $U$ on $H_X$ is a **valid** $\mathsf{QEX}(f_w,\gamma_n)$ oracle if $U\psi_0=\psi_w$.
--
--   The paper's oracle is a state-preparation oracle: "only its action on the designated all-zero input state is specified, and its behavior on other states doesn't matter" (p. 10).
--
--   **Formalization Note** The identity $U\psi_0=\psi_w$ holds in $L^2$, that is, almost everywhere.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, §1.5, Eq. (6), p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Supplement_gaussExampleState

namespace QuantumLTF.Membership.Supplement

open MeasureTheory QuantumLTF.Membership

/-- The oracle space `H_X := L²(ℝⁿ × {0,1}, dx ⊗ counting)` of the continuous quantum example
oracle. Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §1.5, p. 11 (PDF p. 12). -/
abbrev ExSpace (n : ℕ) : Type :=
  Lp ℂ 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (Measure.count : Measure Bool))

/-- **A valid continuous quantum example oracle.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, §1.5, Eq. (6), p. 10 (PDF p. 11):
"QEX(f, D) is a state-preparation oracle: only its action on the designated all-zero input state is
specified, and its behavior on other states doesn't matter". `U` is any unitary on `H_X` mapping the
designated unit vector `ψ0` ("`|0⟩`") to the example state `ψ_w` (`gaussExampleState`), almost
everywhere. -/
def IsQEXCont {n : ℕ} (ψ0 : ExSpace n) (w : EuclideanSpace ℝ (Fin n))
    (U : ExSpace n ≃ₗᵢ[ℂ] ExSpace n) : Prop :=
  ((U ψ0 : ExSpace n) : EuclideanSpace ℝ (Fin n) × Bool → ℂ)
    =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n))).prod (Measure.count : Measure Bool)]
    gaussExampleState w

end QuantumLTF.Membership.Supplement


