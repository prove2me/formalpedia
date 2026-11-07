-- Prove2me | Definitions.Def_PRUPermLayer_layerUnitary
-- name    : PRUPermLayer_layerUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:53.228056+00:00
-- url     : https://prove2.me/theorems/b0d3b0ce-c488-4f88-977b-1db04556fe6e
-- title:
--   Single-qubit layer $L = C_1 \otimes \cdots \otimes C_n$ as an element of $U(N)$
-- statement:
--   For single-qubit unitaries $C_1, \dots, C_n \in U(2)$, the **layer** $L = C_1 \otimes \cdots \otimes C_n$ is the tensor product of the $C_k$, an $n$-qubit unitary in $U(N)$, $N = 2^n$, of depth one.
--
--   **Formalization Note** The same matrix as the tensor product of single-qubit operators, packaged together with the proof that it is unitary.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_PRUPermLayer_productLayer

namespace PRUPermLayer

/-- The layer `L = C₁ ⊗ ⋯ ⊗ Cₙ` of `n` single-qubit unitaries, as an element of `U(N)`,
`N = 2ⁿ` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, p.1 (PDF p.3)). It is `productLayer` of the factors; the unitarity proof is
part of the definition.

**Formalization Note** Factor `k` acts on wire `k` of the bit string of the label (see
`productLayer`). -/
noncomputable def layerUnitary {n : ℕ} (C : Fin n → Matrix.unitaryGroup Bool ℂ) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  ⟨productLayer fun k => (C k : Matrix Bool Bool ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    ext x z
    simp only [Matrix.mul_apply, Matrix.star_apply, productLayer, Matrix.of_apply]
    rw [← (QAlgorithms.bitsEquivFin n).sum_comp]
    simp only [Equiv.symm_apply_apply, star_prod, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun k b => (C k : Matrix Bool Bool ℂ) ((QAlgorithms.bitsEquivFin n).symm x k) b *
      star ((C k : Matrix Bool Bool ℂ) ((QAlgorithms.bitsEquivFin n).symm z k) b))]
    have hk : ∀ k, ∑ b, (C k : Matrix Bool Bool ℂ) ((QAlgorithms.bitsEquivFin n).symm x k) b *
        star ((C k : Matrix Bool Bool ℂ) ((QAlgorithms.bitsEquivFin n).symm z k) b) =
        (1 : Matrix Bool Bool ℂ) ((QAlgorithms.bitsEquivFin n).symm x k)
          ((QAlgorithms.bitsEquivFin n).symm z k) := by
      intro k
      have h := Matrix.mem_unitaryGroup_iff.mp (C k).2
      rw [← h]; simp [Matrix.mul_apply]
    simp only [hk, Matrix.one_apply]
    by_cases h : x = z
    · subst h; simp
    · have : (QAlgorithms.bitsEquivFin n).symm x ≠ (QAlgorithms.bitsEquivFin n).symm z := by
        simpa using h
      obtain ⟨k, hk⟩ := Function.ne_iff.mp this
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)⟩

end PRUPermLayer


