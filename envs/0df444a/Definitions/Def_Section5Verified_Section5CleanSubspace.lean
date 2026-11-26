-- Prove2me | Definitions.Def_Section5Verified_Section5CleanSubspace
-- name    : Section5Verified_Section5CleanSubspace
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T12:17:57.78824+00:00
-- url     : https://prove2.me/theorems/2fd46c91-f7b8-5b6d-92a0-4696330423c8
-- title:
--   Section5CleanSubspace — verified interface
-- statement:
--   An explicit basis isometry for degree encodings with zero ancillas; its adjoint extracts encoded amplitudes. Exact equality with the mission's projDist and synthesis-to-inverse error transfer.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5CleanSubspace; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Mathlib
section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-! Basis encodings and clean ancillary workspace in Theorem 5.2. -/

noncomputable def section5_basis_embedding {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) : EuclideanSpace ℂ α →ₗᵢ[ℂ] EuclideanSpace ℂ β := by
  classical
  let b := EuclideanSpace.basisFun α ℂ
  let b' := EuclideanSpace.basisFun β ℂ
  let L : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ β :=
    b.toBasis.constr ℂ (fun i => b' (e i))
  have heq : L ∘ b = b' ∘ e := by
    funext i
    change (b.toBasis.constr ℂ (fun j => b' (e j))) (b.toBasis i) = b' (e i)
    exact Module.Basis.constr_basis b.toBasis ℂ (fun j => b' (e j)) i
  have hL : Orthonormal ℂ (L ∘ b) := by
    rw [heq]
    exact b'.orthonormal.comp e e.injective
  exact L.isometryOfOrthonormal (v := b.toBasis) b.orthonormal hL











def section5_clean_degree_encoding (n q a D : ℕ) (hD : D ≤ 2^q) :
    (Fin n → Fin D) ↪ Qubits (n*q+a) where
  toFun α := Fin.append (flatReg n q (fun i => natToBits q (α i))) (fun _ : Fin a => false)
  inj' := by
    intro α β h
    funext i
    have hbits : natToBits q (α i) = natToBits q (β i) := by
      funext j
      have hh := congrFun h ((finProdFinEquiv (i,j)).castAdd a)
      simpa only [Fin.append_left, flatReg, Equiv.symm_apply_apply] using hh
    apply Fin.ext
    have hi : (α i:ℕ) < 2^q := (α i).isLt.trans_le hD
    have hj : (β i:ℕ) < 2^q := (β i).isLt.trans_le hD
    have hh := congrArg Fin.val (congrArg (bitsEquivFin q) hbits)
    simpa [natToBits, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hh

noncomputable def section5_ideal_hermite_coefficients (n D : ℕ)
    (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin n → Fin D) :=
  WithLp.toLp 2 fun α => (hermCoeff w (fun i => (α i:ℕ)) : ℂ)





end


