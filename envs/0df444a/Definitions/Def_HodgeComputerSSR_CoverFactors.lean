-- Prove2me | Definitions.Def_HodgeComputerSSR_CoverFactors
-- name    : HodgeComputerSSR_CoverFactors
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T08:58:42.877991+00:00
-- url     : https://prove2.me/theorems/6439970b-2b93-4d94-9466-1537277ffdc7
-- title:
--   Monic degree-34 cover polynomial $P_{34}$ and split coprimality specs
-- statement:
--   Defines the monic degree-34 horizontal cover polynomial $P_{34} \in K_5[U]$ (via its integral model `P34_loc` in $\operatorname{LocK5}[U]$) and nonzero leading constant $\mathrm{lc}_{34} \in K_5^\times$ satisfying $\mathrm{nm}_z = \mathrm{lc}_{34}\, U^{15}\, \widetilde{c}_{b,h}^{12}\, P_{34}$, unpacks `cover_factorization`, and states the split nondegeneracy coprimality bundles `CoverCoprimalityQ5Spec` and `CoverCoprimalityP34Spec`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverAlgebra.lean#L3075-L3157

import Definitions.Def_HodgeComputerSSR_CoverParams
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_factorization

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.K5Field QuadraticCovers Polynomial
open scoped BigOperators

noncomputable section CoverFactorsSec

lemma k5Params_Q5_z_natDegree_le : k5Params.Q5_z.natDegree ≤ 5 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.Q5_deg_le
lemma k5Params_Q7_z_natDegree_le : k5Params.Q7_z.natDegree ≤ 7 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.Q7_deg_le
lemma X_pow_15_dvd_nm_z_K5 : (X : K5[X]) ^ 15 ∣ k5Params.nm_z :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.X15_dvd
lemma k5Params_nm_z_elim_symm : k5Params.ca_h ^ 12 * k5Params.nm_z = k5Params.cb_h ^ 12 * k5Params.nm_w :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.elim_symm
lemma M39_loc_dvd_nm_z : M39_loc ∣ locParams.nm_z :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.M39_dvd
lemma nm_z_loc_eq_M39_mul_Q34 : locParams.nm_z = M39_loc * Q34_loc :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.nm_z_eq_M39_Q34
lemma Q34_loc_evLoc : Q34_loc.map evLoc = C 946 * Poly1009.toPoly Poly1009.P34_m_list :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.Q34_evLoc
lemma Q34_loc_natDegree_le : Q34_loc.natDegree ≤ 34 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.Q34_deg_le
lemma Q34_lc_evLoc_ne : evLoc (Q34_loc.coeff 34) ≠ 0 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.Q34_lc_ne
lemma Q5_m_loc_spec : Q5_m_loc.Monic ∧ Q5_m_loc.natDegree = 5 ∧
    Q5_m_loc.map evLoc = Poly1009.toPoly Poly1009.Q5_m_list ∧
    locParams.Q5_z = C (locParams.Q5_z.coeff 5) * Q5_m_loc :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.Q5_m_spec
lemma Q5_K5_eq_mul_monic : k5Params.Q5_z = C ((locParams.Q5_z.coeff 5 : LocK5) : K5) * Q5_m_K5 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.Q5_K5_eq_mul
lemma Q5_K5_natDegree : k5Params.Q5_z.natDegree = 5 :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_factorization.Q5_K5_deg

/-- The monic degree-34 cover polynomial over `LocK5[X]`. -/
def P34_loc : LocK5[X] := C (LocK5.invOfNe (Q34_loc.coeff 34) Q34_lc_evLoc_ne) * Q34_loc

/-- The monic degree-34 cover polynomial over `K5[X]`. -/
def P34_K5 : K5[X] := P34_loc.map LocK5.subtype

/-- The nonzero leading constant `lc34 ∈ K5` in `nm_z = lc34 * X^15 * cb_h_m^12 * P34_K5`. -/
def lc34_K5 : K5 := (Q34_loc.coeff 34 : K5)

lemma lc34_K5_ne_zero : lc34_K5 ≠ 0 := LocK5.ne_zero_of_evLoc Q34_lc_evLoc_ne

lemma P34_loc_spec :
    P34_loc.Monic ∧ P34_loc.natDegree = 34 ∧
    P34_loc.map evLoc = Poly1009.toPoly Poly1009.P34_m_list ∧
    Q34_loc = C (Q34_loc.coeff 34) * P34_loc := by
  have hev_d : evLoc (Q34_loc.coeff 34) = 946 := by
    rw [← Polynomial.coeff_map, Q34_loc_evLoc, Polynomial.coeff_C_mul,
      ← Poly1009.P34_m_list_monic.2, Poly1009.P34_m_list_monic.1.coeff_natDegree, mul_one]
  have hcd : P34_loc.coeff 34 = 1 := by
    rw [P34_loc, Polynomial.coeff_C_mul, LocK5.invOfNe_mul]
  have hnd : P34_loc.natDegree = 34 :=
    le_antisymm ((Polynomial.natDegree_C_mul_le _ _).trans Q34_loc_natDegree_le)
      (Polynomial.le_natDegree_of_ne_zero (by rw [hcd]; exact one_ne_zero))
  refine ⟨by rw [Polynomial.Monic, Polynomial.leadingCoeff, hnd, hcd], hnd, ?_, ?_⟩
  · rw [P34_loc, Polynomial.map_mul, Polynomial.map_C, LocK5.evLoc_invOfNe, hev_d, Q34_loc_evLoc,
      ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by decide : (946 : ZMod 1009) ≠ 0), map_one, one_mul]
  · rw [P34_loc, ← mul_assoc, ← map_mul, LocK5.mul_invOfNe, map_one, one_mul]

lemma P34_K5_monic : P34_K5.Monic := P34_loc_spec.1.map LocK5.subtype
lemma P34_K5_natDegree : P34_K5.natDegree = 34 :=
  (P34_loc_spec.1.natDegree_map LocK5.subtype).trans P34_loc_spec.2.1

lemma nm_z_K5_factor :
    k5Params.nm_z = C lc34_K5 * X ^ 15 * cb_h_m_K5 ^ 12 * P34_K5 := by
  have h := congrArg (Polynomial.map LocK5.subtype) nm_z_loc_eq_M39_mul_Q34
  rw [P34_loc_spec.2.2.2, M39_loc] at h
  simp only [CoverParams.map_nm_z, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C] at h
  change k5Params.nm_z = X ^ 15 * cb_h_m_K5 ^ 12 * (C lc34_K5 * P34_K5) at h
  rw [h]; ring


/-- Bundled nondegeneracy coprimality conditions for `Q5_z` over `K5[X]`. -/
structure CoverCoprimalityQ5Spec : Prop where
  Q5_Q5d : IsCoprime k5Params.Q5_z k5Params.Q5_z.derivative
  Q5_Q7 : IsCoprime k5Params.Q5_z k5Params.Q7_z
  Q5_X : IsCoprime k5Params.Q5_z (X : K5[X])
  Q5_Xm1 : IsCoprime k5Params.Q5_z (X - 1 : K5[X])
  Q5_cb_h : IsCoprime k5Params.Q5_z k5Params.cb_h
  Q5_ca_h : IsCoprime k5Params.Q5_z k5Params.ca_h
  Q5_nm_WU : IsCoprime k5Params.Q5_z k5Params.nm_WU
  Q5_disc_E0 : IsCoprime k5Params.Q5_z k5Params.disc_E0

/-- Bundled nondegeneracy coprimality conditions for `P34_K5` over `K5[X]`. -/
structure CoverCoprimalityP34Spec : Prop where
  P34_P34d : IsCoprime P34_K5 P34_K5.derivative
  P34_X : IsCoprime P34_K5 (X : K5[X])
  P34_Xm1 : IsCoprime P34_K5 (X - 1 : K5[X])
  P34_Q5 : IsCoprime P34_K5 k5Params.Q5_z
  P34_cb_h : IsCoprime P34_K5 k5Params.cb_h
  P34_ca_h : IsCoprime P34_K5 k5Params.ca_h
  P34_nm_WU : IsCoprime P34_K5 k5Params.nm_WU
  P34_disc_E0 : IsCoprime P34_K5 k5Params.disc_E0
  P34_nm_d1_z : IsCoprime P34_K5 (k5Params.pnm k5Params.d1_z)
  P34_nm_disc_E2z : IsCoprime P34_K5 (k5Params.pnm k5Params.disc_E2z)
  P34_nm_detM_W : IsCoprime P34_K5 (k5Params.pnm k5Params.detM_W)

end CoverFactorsSec
end SymmetricSexticResidual.CoverAlgebra


