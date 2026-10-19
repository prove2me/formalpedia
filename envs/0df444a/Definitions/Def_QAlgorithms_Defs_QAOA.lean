-- Prove2me | Definitions.Def_QAlgorithms_Defs_QAOA
-- name    : QAlgorithms_Defs_QAOA
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:41:09.223983+00:00
-- url     : https://prove2.me/theorems/117f3bd6-4eda-498d-b9a7-16c6166acb47
-- title:
--   The QAOA expectation, MaxCut, Max E3LIN2 (shared definition layer)
-- statement:
--   # The QAOA expectation, MaxCut, Max E3LIN2 (shared definition layer)
--
--   * E. Farhi, J. Goldstone, S. Gutmann, *A quantum approximate optimization algorithm*
--     (arXiv:1411.4028v1), cited "FGG p.N" (PDF pages).
--   * E. Farhi, J. Goldstone, S. Gutmann, *A quantum approximate optimization algorithm applied to a
--     bounded occurrence constraint problem* (arXiv:1412.6062v2), cited "FGG-E3LIN2 p.N".
--
--   The QAOA unitary is the frozen `qaoaUnitary` (`e^{−iγC}` applied before `e^{−iβB}` in each
--   round, `B = Σ_j X_j`), the start state `|s⟩ = H^{⊗n}|0⟩`.
--   -/
--
--   namespace QAlgorithms
--
--   /-- FGG eq. (7) (p.3; FGG-E3LIN2 eqs. (1)–(4), p.2): `F_p(γ, β) = ⟨γ, β| C |γ, β⟩` with
--   `|γ, β⟩ = U(B, β_p) U(C, γ_p) ⋯ U(B, β_1) U(C, γ_1) |s⟩`, `|s⟩ = 2^{−n/2} Σ_z |z⟩`, for the
--   diagonal objective `C = Σ_z f(z) |z⟩⟨z|`; `θ` is the source's `γ`. Written as the mean of `f` over
--   the computational-basis measurement of `|γ, β⟩`, which equals `⟨γ, β| C |γ, β⟩` for diagonal `C`.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\QAOA.lean

import Definitions.Def_QAlgorithms_Defs_ConvexOpt
/-!
# The QAOA expectation, MaxCut, Max E3LIN2 (shared definition layer)

* E. Farhi, J. Goldstone, S. Gutmann, *A quantum approximate optimization algorithm*
  (arXiv:1411.4028v1), cited "FGG p.N" (PDF pages).
* E. Farhi, J. Goldstone, S. Gutmann, *A quantum approximate optimization algorithm applied to a
  bounded occurrence constraint problem* (arXiv:1412.6062v2), cited "FGG-E3LIN2 p.N".

The QAOA unitary is the frozen `qaoaUnitary` (`e^{−iγC}` applied before `e^{−iβB}` in each
round, `B = Σ_j X_j`), the start state `|s⟩ = H^{⊗n}|0⟩`.
-/

namespace QAlgorithms

/-- FGG eq. (7) (p.3; FGG-E3LIN2 eqs. (1)–(4), p.2): `F_p(γ, β) = ⟨γ, β| C |γ, β⟩` with
`|γ, β⟩ = U(B, β_p) U(C, γ_p) ⋯ U(B, β_1) U(C, γ_1) |s⟩`, `|s⟩ = 2^{−n/2} Σ_z |z⟩`, for the
diagonal objective `C = Σ_z f(z) |z⟩⟨z|`; `θ` is the source's `γ`. Written as the mean of `f` over
the computational-basis measurement of `|γ, β⟩`, which equals `⟨γ, β| C |γ, β⟩` for diagonal `C`. -/
noncomputable def qaoaExpectation {n : ℕ} (f : Qubits n → ℝ) (p : ℕ) (β θ : Fin p → ℝ) : ℝ :=
  ∑ z, prob (act (qaoaUnitary f p β θ) (act (hadamardN n) (zeroKet n))) z * f z

/-- FGG eqs. (11)–(12) (p.4): the MaxCut objective `C(z) = Σ_{⟨jk⟩} ½(1 − σ^z_j σ^z_k)`, the number
of edges of `G` whose endpoints receive different bits (each edge counted once, `j < k`). -/
def cutValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Qubits n) : ℕ :=
  (Finset.univ.filter fun e : Fin n × Fin n => e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ z e.1 ≠ z e.2).card

/-- A Max E3LIN2 instance on `n` bits (FGG-E3LIN2 §I, p.3, and eq. (6), p.4): a set of equations
`x_a + x_b + x_c = rhs (mod 2)`, each on exactly three distinct variables, at most one equation per
triple of variables. The number of equations is `eqs.card`. -/
structure E3LIN2Instance (n : ℕ) where
  /-- The equations: the variable triple and the right-hand side (`true` = 1). -/
  eqs : Finset (Finset (Fin n) × Bool)
  /-- Every equation has exactly three variables. -/
  card_three : ∀ e ∈ eqs, e.1.card = 3
  /-- At most one equation per variable triple. -/
  vars_inj : ∀ e ∈ eqs, ∀ e' ∈ eqs, e.1 = e'.1 → e = e'

/-- FGG-E3LIN2 eq. (1) (p.2) and §I (p.3): the objective `C(z)`, the number of satisfied equations
(the three bits of the triple xor to the right-hand side). -/
def E3LIN2Instance.numSatisfied {n : ℕ} (I : E3LIN2Instance n) (z : Qubits n) : ℕ :=
  (I.eqs.filter fun e => decide (((e.1.filter fun a => z a = true).card % 2 = 1) = e.2)).card

/-- FGG-E3LIN2 §I (p.3) and eq. (31) (p.7): every bit occurs in at most `B` equations (the source's
bounded occurrence "each bit is in at most `D + 1` equations" is `OccurrenceAtMost (D + 1)`). -/
def E3LIN2Instance.OccurrenceAtMost {n : ℕ} (I : E3LIN2Instance n) (B : ℕ) : Prop :=
  ∀ a : Fin n, (I.eqs.filter fun e => a ∈ e.1).card ≤ B

/-! ### Sanity tests -/

example {n : ℕ} (f : Qubits n → ℝ) (β θ : Fin 0 → ℝ) :
    qaoaExpectation f 0 β θ = ∑ z, prob (act (hadamardN n) (zeroKet n)) z * f z := by
  simp [qaoaExpectation, qaoaUnitary, orderedProd, act]

example : cutValue (⊤ : SimpleGraph (Fin 2)) ![false, true] = 1 := by
  decide

example : cutValue (⊤ : SimpleGraph (Fin 2)) ![true, true] = 0 := by
  decide

example : (⟨{({0, 1, 2}, true)}, by decide, by decide⟩ : E3LIN2Instance 3).numSatisfied
    ![true, false, false] = 1 := by
  decide

example : (⟨{({0, 1, 2}, true)}, by decide, by decide⟩ : E3LIN2Instance 3).numSatisfied
    ![true, true, false] = 0 := by
  decide

end QAlgorithms


