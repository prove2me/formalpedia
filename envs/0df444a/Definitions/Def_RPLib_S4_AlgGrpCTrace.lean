-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpCTrace
-- name    : RPLib_S4_AlgGrpCTrace
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:03:50.250049+00:00
-- url     : https://prove2.me/theorems/edb46dbe-be0e-4a26-aa0c-6179ee4388f9
-- title:
--   Larsen's alternative library: a non-nilpotent tangent vector pairs nontrivially with a replica
-- statement:
--   * `exists_trace_ne_zero` (K algebraically closed, char 0): if `X ∈ Lie H` is not nilpotent, then
--     some `Y ∈ Lie H` (a conjugate of a replica `diagonal (ψ ∘ lam)` of the semisimple part of `X`)
--     has `trace (X * Y) ≠ 0`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpCDiag

/-!
# S4-AlgGrpC, file Trace: a non-nilpotent tangent vector pairs nontrivially with a replica

* `exists_trace_ne_zero` (K algebraically closed, char 0): if `X ∈ Lie H` is not nilpotent, then
  some `Y ∈ Lie H` (a conjugate of a replica `diagonal (ψ ∘ lam)` of the semisimple part of `X`)
  has `trace (X * Y) ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpC

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- A diagonal matrix commuting with `N` commutes after any map on its entries. -/
theorem commute_diag_comp {lam : n → K} {N : Matrix n n K} (hc : Commute (Matrix.diagonal lam) N)
    (f : K → K) : Commute (Matrix.diagonal (fun j => f (lam j))) N := by
  ext i j
  have h := congr_fun (congr_fun hc.eq i) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h ⊢
  by_cases hN : N i j = 0
  · simp [hN]
  · have : lam i = lam j := mul_right_cancel₀ hN (by rw [h, mul_comm])
    rw [this, mul_comm]

/-- The trace of a nilpotent matrix over a field vanishes. -/
theorem trace_eq_zero_of_isNilpotent' {M : Matrix n n K} (hM : IsNilpotent M) : M.trace = 0 :=
  (Matrix.isNilpotent_trace_of_isNilpotent hM).eq_zero

/-- **Trace pairing with replicas.** A non-nilpotent `X ∈ Lie H` has some `Y ∈ Lie H` with
`trace (X * Y) ≠ 0`. -/
theorem exists_trace_ne_zero [IsAlgClosed K] [CharZero K]
    {H : Subgroup (Matrix.GeneralLinearGroup n K)} {X : Matrix n n K}
    (hX : X ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K))) (hXn : ¬ IsNilpotent X) :
    ∃ Y ∈ lieS (H : Set (Matrix.GeneralLinearGroup n K)), (X * Y).trace ≠ 0 := by
  obtain ⟨P, lam, N, hN, hc, hP⟩ := exists_diag_conj X
  let H' : Subgroup (Matrix.GeneralLinearGroup n K) := H.map (MulAut.conj P).toMonoidHom
  have hX' : Matrix.diagonal lam + N ∈ lieS (H' : Set (Matrix.GeneralLinearGroup n K)) := by
    rw [← hP]
    exact conj_mem_lieS' (fun h hh => Subgroup.mem_map.2 ⟨h, hh, MulAut.conj_apply P h⟩) hX
  -- some eigenvalue is nonzero
  obtain ⟨j0, hj0⟩ : ∃ j0, lam j0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hd : Matrix.diagonal lam = 0 := by
      rw [show lam = 0 from funext hall]
      exact Matrix.diagonal_zero
    obtain ⟨m, hm⟩ := hN
    apply hXn
    refine ⟨m, ?_⟩
    have hXe : X = ((P⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) *
        ((P : Matrix n n K) * X * ((P⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) *
        (P : Matrix n n K) := by
      simp only [mul_assoc, Units.inv_mul, mul_one]
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [hXe, hP, hd, zero_add, Units.conj_pow', hm, mul_zero, zero_mul]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℚ K, φ (lam j0) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hj0 ((Module.forall_dual_apply_eq_zero_iff ℚ (lam j0)).1 hall)
  let ψ : K →+ K := (algebraMap ℚ K).toAddMonoidHom.comp φ.toAddMonoidHom
  have hD' := diag_replica_mem_lieS lam hN hc hX' ψ
  set D' := Matrix.diagonal (fun j => ψ (lam j)) with hD'def
  have hY : ((P⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * D' * (P : Matrix n n K) ∈
      lieS (H : Set (Matrix.GeneralLinearGroup n K)) := by
    have := conj_mem_lieS' (Z' := (H : Set (Matrix.GeneralLinearGroup n K))) (g := P⁻¹)
      (fun h hh => by
        obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.1 hh
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        simpa [mul_assoc] using hh0) hD'
    rwa [inv_inv] at this
  refine ⟨_, hY, ?_⟩
  have htr : (X * (((P⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * D' * (P : Matrix n n K))).trace
      = ((Matrix.diagonal lam + N) * D').trace := by
    rw [← hP, ← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm]
    simp only [mul_assoc]
  have hND : (N * D').trace = 0 :=
    trace_eq_zero_of_isNilpotent' ((commute_diag_comp hc ψ).symm.isNilpotent_mul_right hN)
  rw [htr, add_mul, Matrix.trace_add, hND, add_zero, hD'def, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  intro h0
  have h1 := congr_arg φ h0
  rw [map_sum, map_zero] at h1
  have h2 : ∀ j, φ (lam j * ψ (lam j)) = φ (lam j) * φ (lam j) := fun j => by
    change φ (lam j * algebraMap ℚ K (φ (lam j))) = _
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
  simp only [h2] at h1
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (φ (lam j)))).1 h1 j0
    (Finset.mem_univ _)
  exact hφ (mul_self_eq_zero.1 h3)

end RamanujanPetersson.AlgGrpC


