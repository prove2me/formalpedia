-- Prove2me | Definitions.Def_LIPAlgorithm_Supplement_autGroup
-- name    : LIPAlgorithm_Supplement_autGroup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:54:32.087048+00:00
-- url     : https://prove2.me/theorems/eee9f8e7-8d68-4795-8528-481b45e202b1
-- title:
--   The automorphism group $\mathrm{Aut}(G)=\mathrm{Iso}(G,G)$ as a subgroup of $GL_n(\mathbb Z)$
-- statement:
--   For an integral Gram matrix $G\in\mathbb Z^{n\times n}$, the **automorphism group**
--   $$\mathrm{Aut}(G)=\{U\in GL_n(\mathbb Z) : G=U^{\top}GU\}=\mathrm{Iso}(G,G)$$
--   is a subgroup of $GL_n(\mathbb Z)$. It is the group whose generators Theorem 8.15 outputs; for an isomorphism $O_0\in\mathrm{Iso}(G_1,G_2)$ one has $\mathrm{Iso}(G_1,G_2)=O_0\,\mathrm{Aut}(G_1)$.
--
--   **Formalization Note** $GL_n(\mathbb Z)$ is the unit group of the ring of $n\times n$ integer matrices; a unit lies in $\mathrm{Aut}(G)$ exactly when its matrix lies in the published $\mathrm{Iso}(G,G)$ (`isoSet G G`).
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), §2.2, p.11 (PDF p.14); Theorem 8.15, p.49 (PDF p.52)

import Mathlib
import Definitions.Def_LIPAlgorithm_Gram

namespace LIPAlgorithm

namespace Supplement

/-- `Aut(L) = Iso(L, L)` as a subgroup of `GLn(Z)`: the units `U` with `G = UᵀGU`.
Aggarwal, Jiang, Li, Liu, *An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem*, STOC 2027
submission (manuscript sha256 61ee52aa…), §2.2, p.11 (PDF p.14) (`Iso(G₁, G₂)`, `Aut(L) = Iso(L, L)`);
Theorem 8.15, p.49 (PDF p.52) ("generators of Aut(L1)").

**Formalization Note.** `GLn(Z)` is the unit group `(Matrix (Fin n) (Fin n) ℤ)ˣ`; a unit's matrix lies
in the published `isoSet G G` exactly when it is in this subgroup (`IsUnit U.det` holds for units). -/
def autGroup {n : ℕ} (G : Gram n) : Subgroup (Matrix (Fin n) (Fin n) ℤ)ˣ where
  carrier := {U | G = (U : Matrix (Fin n) (Fin n) ℤ).transpose * G * (U : Matrix (Fin n) (Fin n) ℤ)}
  one_mem' := by simp
  mul_mem' := by
    intro U V hU hV
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul] at *
    calc G = (V : Matrix (Fin n) (Fin n) ℤ).transpose * G * V := hV
      _ = (V : Matrix (Fin n) (Fin n) ℤ).transpose *
            ((U : Matrix (Fin n) (Fin n) ℤ).transpose * G * U) * V := by rw [← hU]
      _ = _ := by simp only [Matrix.mul_assoc]
  inv_mem' := by
    intro U hU
    simp only [Set.mem_ofPred_eq] at *
    have hr : (U : Matrix (Fin n) (Fin n) ℤ) *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ) = 1 := Units.mul_inv U
    have hl : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ).transpose *
        (U : Matrix (Fin n) (Fin n) ℤ).transpose = 1 := by
      rw [← Matrix.transpose_mul, hr, Matrix.transpose_one]
    have key : ((U⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ).transpose * G *
        ((U⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ) = G := by
      conv_lhs => rw [hU]
      calc _ = (((U⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ).transpose *
              (U : Matrix (Fin n) (Fin n) ℤ).transpose) * G *
              ((U : Matrix (Fin n) (Fin n) ℤ) *
                ((U⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ)) := by
            simp only [Matrix.mul_assoc]
        _ = G := by rw [hl, hr, Matrix.one_mul, Matrix.mul_one]
    exact key.symm

end Supplement

end LIPAlgorithm


