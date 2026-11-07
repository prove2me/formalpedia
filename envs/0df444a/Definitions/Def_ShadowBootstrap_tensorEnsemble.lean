-- Prove2me | Definitions.Def_ShadowBootstrap_tensorEnsemble
-- name    : ShadowBootstrap_tensorEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:19.192622+00:00
-- url     : https://prove2.me/theorems/c8292998-c10d-4fb1-b98d-670c4844c912
-- title:
--   Product $E_A \otimes E_B$ of independent unitary ensembles
-- statement:
--   Let $E_A$ be a finite ensemble of unitaries on $n_A$ qubits (unitary $U_i$ drawn with probability $w_A(i)$) and $E_B$ one on $n_B$ qubits. Their product $E_A \otimes E_B$ is the ensemble on $n_A + n_B$ qubits that draws $i \sim E_A$ and $j \sim E_B$ independently and applies
--   $$U_i \otimes V_j,$$
--   with $E_A$ acting on the first $n_A$ qubits and $E_B$ on the last $n_B$ qubits.
--
--   It is the ensemble of Lemma A.1 and the construction $E_\ell = E_{2L}(km) \otimes \mathrm{Cl}(r)$ of Lemma A.2.
--
--   **Formalization Note** Ensembles are the published `ClassicalShadow.Linear.Primitive` (finite label set, weights, unitaries). The module also provides `castQubits`, which reads an ensemble on $a$ qubits as one on $b = a$ qubits.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Lemma A.1, p.33; Lemma A.2, p.34

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear
open scoped Kronecker

namespace ShadowBootstrap

/-- The splitting `{0,1}^{a+b} ≃ {0,1}^a × {0,1}^b` of a bit string into its first `a` and its last
`b` bits. -/
def splitBits (a b : ℕ) : Bits (a + b) ≃ Bits a × Bits b :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl (Fin 2))).trans
    (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) (Fin 2))

/-- Reindexing a unitary along a bijection of the basis keeps it unitary. -/
theorem submatrix_mem_unitaryGroup {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (f : α ≃ β) (A : Matrix β β ℂ) (hA : A ∈ Matrix.unitaryGroup β ℂ) :
    A.submatrix f f ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    ← Matrix.star_eq_conjTranspose, hA, Matrix.submatrix_one_equiv]

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Lemma A.1, p.33, and Lemma A.2, p.34: the product `E_A ⊗ E_B` of independent unitary ensembles on
`a` and `b` qubits. A label is a pair `(i, j)`, drawn with probability `w_A(i) w_B(j)`, and its
unitary is `U_i ⊗ V_j`.

**Formalization Note** The register of `E_A ⊗ E_B` is `{0,1}^{a+b}`, its first `a` qubits carry
`E_A` and its last `b` qubits carry `E_B` (`splitBits`). -/
noncomputable def tensorEnsemble {a b : ℕ} {ιA ιB : Type} [Fintype ιA] [Fintype ιB]
    (EA : Primitive a ιA) (EB : Primitive b ιB) : Primitive (a + b) (ιA × ιB) where
  w := EA.w.prod EB.w
  U p := ⟨((EA.U p.1 : Op a) ⊗ₖ (EB.U p.2 : Op b)).submatrix (splitBits a b) (splitBits a b),
    submatrix_mem_unitaryGroup _ _ (Matrix.kronecker_mem_unitary (EA.U p.1).2 (EB.U p.2).2)⟩

/-- An ensemble on `a` qubits read as an ensemble on `b = a` qubits (transport along `a = b`). -/
def castQubits {a b : ℕ} {ι : Type} [Fintype ι] (h : a = b) (E : Primitive a ι) : Primitive b ι :=
  h ▸ E

end ShadowBootstrap


