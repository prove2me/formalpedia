-- Prove2me | Definitions.Def_HodgeComputerSSR_CoverResidueDefs
-- name    : HodgeComputerSSR_CoverResidueDefs
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T09:26:30.406789+00:00
-- url     : https://prove2.me/theorems/0b1c1d51-3925-4951-a55d-556d5150b111
-- title:
--   Quadratic cover field $A_C$, cover 1-form $\eta$, and splitting field $\mathrm{CoverL}$
-- statement:
--   Defines the quadratic cover field $A_C = \operatorname{RatFunc}(K_5)[W]/(E_0)$, the explicit cover integrand $\eta_{A_C} \in A_C$ and its field trace $\eta \in \operatorname{RatFunc}(K_5)$, the regularized $P_{18}$ forms, regularity predicates `RegAC`, the splitting field $\mathrm{CoverL}/K_5$, the root sets $R_{34}, R_{Q_5} \subset \mathrm{CoverL}$, and the specification `CoverRegIdentitiesSpec`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/CoverResidue.lean#L491-L1339

import Definitions.Def_HodgeComputerFormal_CoverResidues
import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_CoverFactors
import Definitions.Def_HodgeComputerSSR_CoverE0
import Theorems.Thm_HodgeComputer_Formal_QuadraticCovers_simplePole_residue
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_coprimalities_Q5
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_coprimalities_P34
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_E0_irreducible
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.K5Field Polynomial
lemma isCoprime_Q5_Q5_deriv : IsCoprime k5Params.Q5_z k5Params.Q5_z.derivative := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5.Q5_Q5d
lemma isCoprime_Q5_Q7 : IsCoprime k5Params.Q5_z k5Params.Q7_z := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5.Q5_Q7
lemma isCoprime_Q5_X : IsCoprime k5Params.Q5_z (X : K5[X]) := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5.Q5_X
lemma isCoprime_Q5_X_sub_1 : IsCoprime k5Params.Q5_z (X - 1 : K5[X]) := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5.Q5_Xm1
lemma isCoprime_Q5_cb_h : IsCoprime k5Params.Q5_z k5Params.cb_h := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5.Q5_cb_h
lemma isCoprime_Q5_ca_h : IsCoprime k5Params.Q5_z k5Params.ca_h := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5.Q5_ca_h
lemma isCoprime_Q5_nm_WU : IsCoprime k5Params.Q5_z k5Params.nm_WU := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5.Q5_nm_WU
lemma isCoprime_Q5_disc_E0 : IsCoprime k5Params.Q5_z k5Params.disc_E0 := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_Q5.Q5_disc_E0
lemma isCoprime_P34_P34_deriv : IsCoprime P34_K5 P34_K5.derivative := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_P34d
lemma isCoprime_P34_X : IsCoprime P34_K5 (X : K5[X]) := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_X
lemma isCoprime_P34_X_sub_1 : IsCoprime P34_K5 (X - 1 : K5[X]) := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_Xm1
lemma isCoprime_P34_Q5 : IsCoprime P34_K5 k5Params.Q5_z := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_Q5
lemma isCoprime_P34_cb_h : IsCoprime P34_K5 k5Params.cb_h := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_cb_h
lemma isCoprime_P34_ca_h : IsCoprime P34_K5 k5Params.ca_h := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_ca_h
lemma isCoprime_P34_nm_WU : IsCoprime P34_K5 k5Params.nm_WU := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_nm_WU
lemma isCoprime_P34_disc_E0 : IsCoprime P34_K5 k5Params.disc_E0 := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_disc_E0
lemma isCoprime_P34_nm_d1_z : IsCoprime P34_K5 (k5Params.pnm k5Params.d1_z) := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_nm_d1_z
lemma isCoprime_P34_nm_disc_E2z : IsCoprime P34_K5 (k5Params.pnm k5Params.disc_E2z) := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_nm_disc_E2z
lemma isCoprime_P34_nm_detM_W : IsCoprime P34_K5 (k5Params.pnm k5Params.detM_W) := HodgeComputer.SymmetricSexticResidual.Proof.cover_coprimalities_P34.P34_nm_detM_W
end SymmetricSexticResidual.CoverAlgebra

noncomputable section
namespace SymmetricSexticResidual.CoverResidue
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra QuadraticCovers CrossedRationalResidue Polynomial
open scoped BigOperators Matrix Classical

lemma E0_poly_irreducible : Irreducible E0_poly :=
  HodgeComputer.SymmetricSexticResidual.Proof.cover_E0_irreducible

instance : Fact (Irreducible E0_poly) := ⟨E0_poly_irreducible⟩

abbrev A_C := AdjoinRoot E0_poly

instance : CharZero A_C :=
  charZero_of_injective_ringHom ((algebraMap (RatFunc K5) A_C).comp (algebraMap K5 (RatFunc K5))).injective

instance : FiniteDimensional (RatFunc K5) A_C :=
  Module.Finite.of_basis (AdjoinRoot.powerBasis' E0_poly_monic).basis

def W_C : A_C := AdjoinRoot.root E0_poly
def ιC_rat : RatFunc K5 →+* A_C := algebraMap (RatFunc K5) A_C
def ιC_K5 : K5 →+* A_C := ιC_rat.comp (algebraMap K5 (RatFunc K5))
def U_C : A_C := ιC_rat RatFunc.X
def V_C : A_C := W_C / U_C

lemma W_C_relation :
    W_C ^ 2 + ιC_rat (toRat k5Params.bW) * W_C + ιC_rat (toRat k5Params.cW) = 0 := by
  have he := AdjoinRoot.eval₂_root E0_poly
  change E0_poly.eval₂ ιC_rat W_C = 0 at he
  simpa only [E0_poly, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C] using he

/-- Embed a `PairAlg (RatFunc K5)` element `c0 + c1 * W` into `A_C`. -/
def evalAC (x : PairAlg (RatFunc K5)) : A_C :=
  ιC_rat x.c0 + ιC_rat x.c1 * W_C

lemma evalAC_zero : evalAC (PairAlg.zero : PairAlg (RatFunc K5)) = 0 := by simp [evalAC, PairAlg.zero]
lemma evalAC_one : evalAC (PairAlg.one : PairAlg (RatFunc K5)) = 1 := by simp [evalAC, PairAlg.one]
lemma evalAC_W : evalAC (PairAlg.W : PairAlg (RatFunc K5)) = W_C := by simp [evalAC, PairAlg.W]
lemma evalAC_ofScalar (s : RatFunc K5) : evalAC (PairAlg.ofScalar s) = ιC_rat s := by
  simp [evalAC, PairAlg.ofScalar]
lemma evalAC_add (x y : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.add x y) = evalAC x + evalAC y := by
  simp only [evalAC, PairAlg.add, map_add]; ring
lemma evalAC_sub (x y : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.sub x y) = evalAC x - evalAC y := by
  simp only [evalAC, PairAlg.sub, map_sub]; ring
lemma evalAC_neg (x : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.neg x) = -evalAC x := by
  simp only [evalAC, PairAlg.neg, map_neg]; ring
lemma evalAC_smul (s : RatFunc K5) (x : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.smul s x) = ιC_rat s * evalAC x := by
  simp only [evalAC, PairAlg.smul, map_mul]; ring
lemma evalAC_mul (x y : PairAlg (RatFunc K5)) :
    evalAC (PairAlg.mul (toRat k5Params.bW) (toRat k5Params.cW) x y) = evalAC x * evalAC y := by
  simp only [evalAC, PairAlg.mul, map_add, map_sub, map_mul]
  linear_combination -ιC_rat x.c1 * ιC_rat y.c1 * W_C_relation

/-- Extract `(c0, c1)` coordinates of an element of `A_C` in the power basis `{1, W_C}`. -/
def coordsAC (x : A_C) : PairAlg (RatFunc K5) :=
  let pb := AdjoinRoot.powerBasis' E0_poly_monic
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis'_dim, E0_poly_natDegree]
  ⟨pb.basis.repr x ⟨0, by omega⟩, pb.basis.repr x ⟨1, by omega⟩⟩

lemma evalAC_coordsAC (x : A_C) : evalAC (coordsAC x) = x := by
  let pb := AdjoinRoot.powerBasis' E0_poly_monic
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis'_dim, E0_poly_natDegree]
  have hsum := (pb.basis.sum_repr x).symm
  rw [show (Finset.univ : Finset (Fin pb.dim)) = {⟨0, by omega⟩, ⟨1, by omega⟩} by
    ext ⟨i, hi⟩; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq,
      true_iff]; omega] at hsum
  rw [Finset.sum_pair (by simp)] at hsum
  have hb0 : pb.basis ⟨0, by omega⟩ = 1 := by simp [pb, PowerBasis.basis_eq_pow]
  have hb1 : pb.basis ⟨1, by omega⟩ = W_C := by simp [pb, PowerBasis.basis_eq_pow, W_C]
  rw [hb0, hb1] at hsum
  simpa only [evalAC, coordsAC, Algebra.smul_def, ιC_rat, mul_one] using hsum.symm

lemma coordsAC_evalAC (p : PairAlg (RatFunc K5)) : coordsAC (evalAC p) = p := by
  let pb := AdjoinRoot.powerBasis' E0_poly_monic
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis'_dim, E0_poly_natDegree]
  have hb0 : pb.basis ⟨0, by omega⟩ = 1 := by simp [pb, PowerBasis.basis_eq_pow]
  have hb1 : pb.basis ⟨1, by omega⟩ = W_C := by simp [pb, PowerBasis.basis_eq_pow, W_C]
  have hev : evalAC p = p.c0 • pb.basis ⟨0, by omega⟩ + p.c1 • pb.basis ⟨1, by omega⟩ := by
    rw [hb0, hb1, evalAC, Algebra.smul_def, Algebra.smul_def, mul_one]; rfl
  ext
  · change pb.basis.repr (evalAC p) ⟨0, by omega⟩ = p.c0
    rw [hev, map_add, map_smul, map_smul, pb.basis.repr_self, pb.basis.repr_self]
    simp
  · change pb.basis.repr (evalAC p) ⟨1, by omega⟩ = p.c1
    rw [hev, map_add, map_smul, map_smul, pb.basis.repr_self, pb.basis.repr_self]
    simp

lemma evalAC_injective : Function.Injective evalAC :=
  Function.LeftInverse.injective coordsAC_evalAC

/-- Explicit trace of `c0 + c1 * W_C` from `A_C` to `RatFunc K5`. -/
lemma trace_AC_evalAC (p : PairAlg (RatFunc K5)) :
    Algebra.trace (RatFunc K5) A_C (evalAC p) = 2 * p.c0 - p.c1 * toRat k5Params.bW := by
  let pb := AdjoinRoot.powerBasis' E0_poly_monic
  have hdim : pb.dim = 2 := by rw [AdjoinRoot.powerBasis'_dim, E0_poly_natDegree]
  rw [Algebra.trace_eq_matrix_trace pb.basis]
  rw [Matrix.trace, show (Finset.univ : Finset (Fin pb.dim)) = {⟨0, by omega⟩, ⟨1, by omega⟩} by
    ext ⟨i, hi⟩; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq,
      true_iff]; omega]
  rw [Finset.sum_pair (by simp)]
  have hb0 : pb.basis ⟨0, by omega⟩ = 1 := by simp [pb, PowerBasis.basis_eq_pow]
  have hb1 : pb.basis ⟨1, by omega⟩ = W_C := by simp [pb, PowerBasis.basis_eq_pow, W_C]
  have h00 : (Algebra.leftMulMatrix pb.basis (evalAC p)).diag ⟨0, by omega⟩ = p.c0 := by
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one]
    exact congrArg PairAlg.c0 (coordsAC_evalAC p)
  have h11 : (Algebra.leftMulMatrix pb.basis (evalAC p)).diag ⟨1, by omega⟩ =
      p.c0 - p.c1 * toRat k5Params.bW := by
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hb1, ← evalAC_W, ← evalAC_mul]
    have hc := congrArg PairAlg.c1 (coordsAC_evalAC (PairAlg.mul (toRat k5Params.bW) (toRat k5Params.cW) p PairAlg.W))
    simpa [coordsAC, PairAlg.mul, PairAlg.W] using hc
  rw [h00, h11]; ring

/-- Quadratic Euler trace identity in `A_C`: cancels `disc_E0` identically. -/
lemma trace_AC_euler (x y : PairAlg (RatFunc K5))
    (hnm : PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) y ≠ 0) :
    Algebra.trace (RatFunc K5) A_C
      (evalAC x / (evalAC y * (2 * W_C + ιC_rat (toRat k5Params.bW)))) =
    (x.c1 * y.c0 - x.c0 * y.c1) / PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) y := by
  have hdisc_ne : toRat k5Params.disc_E0 ≠ 0 := by
    apply polynomialMap_ne_zero
    intro h0
    have hloc : locParams.disc_E0 = 0 :=
      Polynomial.map_injective LocK5.subtype Subtype.val_injective (by rw [CoverParams.map_disc_E0, Polynomial.map_zero]; exact h0)
    have hc4 := congrArg (fun p : LocK5[X] => evLoc (p.coeff 4)) hloc
    rw [Polynomial.coeff_zero, map_zero, ← Polynomial.coeff_map, CoverParams.map_disc_E0,
      locParams_map_evLoc, ← Poly1009.toPoly_c_disc_E0, Poly1009.toPoly_coeff_getD] at hc4
    exact (by decide : Poly1009.c_disc_E0.getD 4 0 ≠ 0) hc4
  have h2W_sq : (2 * W_C + ιC_rat (toRat k5Params.bW)) ^ 2 = ιC_rat (toRat k5Params.disc_E0) := by
    rw [CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat, map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * W_C_relation
  have h2W_ne : 2 * W_C + ιC_rat (toRat k5Params.bW) ≠ 0 := by
    intro h0; rw [h0, zero_pow (by omega)] at h2W_sq
    exact hdisc_ne (ιC_rat.injective (by simpa using h2W_sq.symm))
  have hy_conj : evalAC y * evalAC (PairAlg.conj (toRat k5Params.bW) y) =
      ιC_rat (PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) y) := by
    rw [← evalAC_mul, ← evalAC_ofScalar]
    congr 1; ext <;> (simp only [PairAlg.mul, PairAlg.conj, PairAlg.nm, PairAlg.ofScalar]; ring)
  have hy_ne : evalAC y ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hy_conj
    exact hnm (ιC_rat.injective (by simpa using hy_conj.symm))
  set b := toRat k5Params.bW
  set c := toRat k5Params.cW
  set d := toRat k5Params.disc_E0
  set N := PairAlg.nm b c y
  let w2 : PairAlg (RatFunc K5) := ⟨b, 2⟩
  let prod : PairAlg (RatFunc K5) :=
    PairAlg.mul b c (PairAlg.mul b c x (PairAlg.conj b y)) w2
  have hquot : evalAC x / (evalAC y * (2 * W_C + ιC_rat b)) =
      ιC_rat (N * d)⁻¹ * evalAC prod := by
    have hprod_ev : evalAC prod = evalAC x * evalAC (PairAlg.conj b y) * (2 * W_C + ιC_rat b) := by
      dsimp only [prod, w2, b, c]
      rw [evalAC_mul, evalAC_mul]
      simp only [evalAC, map_ofNat]
      ring
    rw [hprod_ev]
    have hNd_ne : ιC_rat (N * d) ≠ 0 := (map_ne_zero_iff ιC_rat ιC_rat.injective).mpr (mul_ne_zero hnm hdisc_ne)
    rw [map_inv₀, div_eq_iff (mul_ne_zero hy_ne h2W_ne), eq_comm, mul_assoc, inv_mul_eq_iff_eq_mul₀ hNd_ne]
    calc evalAC x * evalAC (PairAlg.conj b y) * (2 * W_C + ιC_rat b) * (evalAC y * (2 * W_C + ιC_rat b))
        = evalAC x * (evalAC y * evalAC (PairAlg.conj b y)) * (2 * W_C + ιC_rat b) ^ 2 := by ring
      _ = evalAC x * ιC_rat N * ιC_rat d := by rw [hy_conj, h2W_sq]
      _ = ιC_rat (N * d) * evalAC x := by rw [map_mul]; ring
  rw [hquot, show ιC_rat (N * d)⁻¹ * evalAC prod = (N * d)⁻¹ • evalAC prod from
      (Algebra.smul_def (N * d)⁻¹ (evalAC prod)).symm,
    map_smul, trace_AC_evalAC, smul_eq_mul]
  have htr : 2 * prod.c0 - prod.c1 * b = d * (x.c1 * y.c0 - x.c0 * y.c1) := by
    have hd_eq : d = b ^ 2 - 4 * c := by
      simp only [d, b, c, CoverParams.disc_E0, map_sub, map_pow, map_mul, map_ofNat]
    rw [hd_eq]
    simp only [prod, PairAlg.mul, PairAlg.conj, w2]
    ring
  rw [htr]
  field_simp [hnm, hdisc_ne]

/-- Universal two-branch specialization of `Algebra.trace (RatFunc K5) A_C` to ANY field `F`
over which `E0_poly` splits into two distinct roots `w1, w2`. -/
lemma map_trace_AC_euler {F : Type*} [Field F] (φ : RatFunc K5 →+* F)
    (x y : PairAlg (RatFunc K5)) (w1 w2 : F)
    (hsum : w1 + w2 = -φ (toRat k5Params.bW))
    (hprod : w1 * w2 = φ (toRat k5Params.cW))
    (hsep : w1 ≠ w2)
    (hy1 : PairAlg.evalAt w1 (PairAlg.map φ y) ≠ 0)
    (hy2 : PairAlg.evalAt w2 (PairAlg.map φ y) ≠ 0) :
    φ (Algebra.trace (RatFunc K5) A_C
        (evalAC x / (evalAC y * (2 * W_C + ιC_rat (toRat k5Params.bW))))) =
      PairAlg.evalAt w1 (PairAlg.map φ x) /
        (PairAlg.evalAt w1 (PairAlg.map φ y) * (2 * w1 + φ (toRat k5Params.bW))) +
      PairAlg.evalAt w2 (PairAlg.map φ x) /
        (PairAlg.evalAt w2 (PairAlg.map φ y) * (2 * w2 + φ (toRat k5Params.bW))) := by
  have hnm_phi : PairAlg.nm (φ (toRat k5Params.bW)) (φ (toRat k5Params.cW)) (PairAlg.map φ y) ≠ 0 := by
    rw [PairAlg.evalAt_nm _ _ w1 w2 hsum hprod]
    exact mul_ne_zero hy1 hy2
  have hnm : PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) y ≠ 0 := by
    intro h0; apply hnm_phi; rw [← PairAlg.map_nm, h0, map_zero]
  rw [trace_AC_euler x y hnm, map_div₀, map_sub, map_mul, map_mul, PairAlg.map_nm]
  exact (PairAlg.eulerTr_div (φ (toRat k5Params.bW)) (φ (toRat k5Params.cW)) w1 w2
    (PairAlg.map φ x) (PairAlg.map φ y) hsum hprod hsep hy1 hy2).symm


section CoverEq0
variable {F : Type*} [Field F] (φ : K5 →+* F)
abbrev pU (P : K5[X]) (U : F) : F := (P.map φ).eval U
abbrev pUW (x : PairAlg K5[X]) (U W : F) : F :=
  PairAlg.evalAt W (PairAlg.map (Polynomial.evalRingHom U |>.comp (Polynomial.mapRingHom φ)) x)
lemma pUW_eq (x : PairAlg K5[X]) (U W : F) : pUW φ x U W = pU φ x.c0 U + pU φ x.c1 U * W := rfl
variable [CharZero F]

lemma E0_of_cover (U W : F) (hU : U ≠ 0) :
    U * E_fn 0 (φ S_K) (φ Q_K) (φ T_K) 0 0 U (W / U) =
      φ k5Params.Av0 * (W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U) := by
  have hT3 : φ T_K - 3 ≠ 0 := by
    have := (map_ne_zero_iff φ φ.injective).mpr T_K_sub_3_ne
    simpa only [map_sub, map_ofNat] using this
  simp only [E_fn, H_cub, pU, CoverParams.bW, CoverParams.cW, CoverParams.Bv, CoverParams.quadU,
    CoverParams.Av0, CoverParams.Av0_inv, CoverParams.Cv0, CoverParams.Bv0, CoverParams.Bv1, CoverParams.Bv2,
    CoverParams.inv4, CoverParams.inv9, CoverParams.inv27, CoverParams.inv243,
    k5Params_inv2, k5Params_inv3, k5Params_inv7, k5Params_invT3, k5Params_S, k5Params_Q, k5Params_T,
    Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_neg,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_ofNat,
    eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_C, eval_X, eval_ofNat,
    map_add, map_sub, map_mul, map_pow, map_neg, map_inv₀, map_ofNat]
  field_simp [hU, hT3]; ring

end CoverEq0

/-- Helper evaluating a polynomial `P : K5[X]` in `A_C` at `U_C`. -/
def polyC (P : K5[X]) : A_C := ιC_rat (toRat P)

/-- Helper evaluating a `PairAlg K5[X]` in `A_C` at `(U_C, W_C)`. -/
def pairC (x : PairAlg K5[X]) : A_C := evalAC (PairAlg.map toRat x)

/-- The `z`-parametrized `P18_of` function in `A_C` (`b`-elimination: `a = z / W_C`,
`b = -(ca_h * z + c0W) / (W_C * cb_h)`). -/
def P18_z_AC (z : A_C) : A_C :=
  SheetCalculus.P18_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
    (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h))
    U_C V_C

/-- Numerator of the un-traced algebraic cover 1-form `eta_AC ∈ A_C`. -/
def eta_AC_num : A_C :=
  let p := interp4 P18_z_AC
  let P1 := remDeg4_P1 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0) p.1 p.2.1 p.2.2.1 p.2.2.2.1
  let P0 := remDeg4_P0 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0) p.1 p.2.1 p.2.2.1 p.2.2.2.2
  (-(P1 * pairC k5Params.d0_z - P0 * pairC k5Params.d1_z) *
    U_C ^ 3 * W_C * polyC k5Params.cb_h ^ 4)

/-- The un-traced algebraic cover 1-form `eta_AC ∈ A_C`. -/
def eta_AC : A_C :=
  eta_AC_num /
    (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) *
      polyC k5Params.Q5_z ^ 3 * pairC k5Params.res_z)

/-- The master rational 1-form `eta ∈ RatFunc K5` obtained by tracing `eta_AC` down from `A_C`. -/
def eta : RatFunc K5 := Algebra.trace (RatFunc K5) A_C eta_AC


section Regularity

lemma eval_ne_zero_of_isCoprime {L : Type*} [Field L] [Algebra K5 L]
    {P Q : K5[X]} (hcop : IsCoprime P Q) {r : L}
    (hP : (P.map (algebraMap K5 L)).eval r = 0) :
    (Q.map (algebraMap K5 L)).eval r ≠ 0 := by
  obtain ⟨u, v, huv⟩ := hcop
  intro hQ
  have h1 := congrArg (fun f : K5[X] => (f.map (algebraMap K5 L)).eval r) huv
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
    eval_add, eval_mul, eval_one, hP, hQ, mul_zero, add_zero] at h1
  exact zero_ne_one h1

-- Local ring closure properties of `RegularAt` and `valueAt` over any field `L`.
section LocalReg
variable {L : Type*} [Field L]

lemma regAt_zero (a : L) : RegularAt a (0 : RatFunc L) :=
  ⟨0, 1, by simp, by simp⟩

lemma regAt_one (a : L) : RegularAt a (1 : RatFunc L) :=
  ⟨1, 1, by simp, by simp⟩

lemma regAt_C (a c : L) : RegularAt a (RatFunc.C c) :=
  ⟨Polynomial.C c, 1, by simp, by simp⟩

lemma regAt_X (a : L) : RegularAt a (RatFunc.X : RatFunc L) :=
  ⟨Polynomial.X, 1, by simp, by simp⟩

lemma regAt_ofNat (a : L) (n : ℕ) [n.AtLeastTwo] :
    RegularAt a (OfNat.ofNat n : RatFunc L) :=
  ⟨Polynomial.C (OfNat.ofNat n), 1, by simp, by simp [map_ofNat]⟩

lemma regAt_neg_local {a : L} {f : RatFunc L} (hf : RegularAt a f) : RegularAt a (-f) := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  exact ⟨-P, Q, hQ, by simp [neg_div]⟩

lemma regAt_sub_local {a : L} {f g : RatFunc L} (hf : RegularAt a f) (hg : RegularAt a g) :
    RegularAt a (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add (regAt_neg_local hg)

lemma regAt_mul_local {a : L} {f g : RatFunc L} (hf : RegularAt a f) (hg : RegularAt a g) :
    RegularAt a (f * g) := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  obtain ⟨R, S, hS, rfl⟩ := hg
  refine ⟨P * R, Q * S, by simpa using mul_ne_zero hQ hS, ?_⟩
  simp only [map_mul]; ring

lemma regAt_pow_local {a : L} {f : RatFunc L} (hf : RegularAt a f) (n : ℕ) :
    RegularAt a (f ^ n) := by
  induction n with
  | zero => simpa using regAt_one a
  | succ k ih => rw [pow_succ]; exact regAt_mul_local ih hf

lemma valueAt_polynomial (a : L) (P : L[X]) :
    valueAt a (algebraMap L[X] (RatFunc L) P) = P.eval a := by
  have h := valueAt_div_polynomials a P 1 (by simp)
  simpa only [map_one, div_one, eval_one] using h

lemma valueAt_C (a c : L) : valueAt a (RatFunc.C c) = c := by
  rw [← RatFunc.algebraMap_C, valueAt_polynomial, eval_C]

lemma valueAt_X (a : L) : valueAt a (RatFunc.X : RatFunc L) = a := by
  rw [← RatFunc.algebraMap_X, valueAt_polynomial, eval_X]

lemma valueAt_mul_of_regularAt {a : L} {f g : RatFunc L}
    (hf : RegularAt a f) (hg : RegularAt a g) :
    valueAt a (f * g) = valueAt a f * valueAt a g := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  obtain ⟨R, S, hS, rfl⟩ := hg
  rw [show algebraMap L[X] (RatFunc L) P / algebraMap L[X] (RatFunc L) Q *
      (algebraMap L[X] (RatFunc L) R / algebraMap L[X] (RatFunc L) S) =
      algebraMap L[X] (RatFunc L) (P * R) / algebraMap L[X] (RatFunc L) (Q * S) by
    simp only [map_mul]; ring]
  rw [valueAt_div_polynomials a (P * R) (Q * S) (by simpa using mul_ne_zero hQ hS),
    valueAt_div_polynomials a P Q hQ, valueAt_div_polynomials a R S hS, eval_mul, eval_mul]
  ring

lemma valueAt_pow_of_regularAt {a : L} {f : RatFunc L} (hf : RegularAt a f) (n : ℕ) :
    valueAt a (f ^ n) = (valueAt a f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ← map_one RatFunc.C, valueAt_C]
  | succ k ih => rw [pow_succ, pow_succ, valueAt_mul_of_regularAt (regAt_pow_local hf k) hf, ih]

lemma regAt_inv_of_valueAt_ne {a : L} {f : RatFunc L}
    (hf : RegularAt a f) (hne : valueAt a f ≠ 0) : RegularAt a f⁻¹ := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  rw [valueAt_div_polynomials a P Q hQ] at hne
  have hP : P.eval a ≠ 0 := left_ne_zero_of_mul (by simpa [div_eq_mul_inv] using hne)
  exact ⟨Q, P, hP, by rw [inv_div]⟩

lemma regAt_div_of_valueAt_ne {a : L} {f g : RatFunc L}
    (hf : RegularAt a f) (hg : RegularAt a g) (hne : valueAt a g ≠ 0) :
    RegularAt a (f / g) := by
  rw [div_eq_mul_inv]; exact regAt_mul_local hf (regAt_inv_of_valueAt_ne hg hne)

lemma valueAt_div_of_regularAt {a : L} {f g : RatFunc L}
    (hf : RegularAt a f) (hg : RegularAt a g) (hne : valueAt a g ≠ 0) :
    valueAt a (f / g) = valueAt a f / valueAt a g := by
  have hg' : RegularAt a g⁻¹ := regAt_inv_of_valueAt_ne hg hne
  have hinv : valueAt a g⁻¹ = (valueAt a g)⁻¹ := by
    have h1 := valueAt_mul_of_regularAt hg hg'
    have hg0 : g ≠ 0 := by intro h0; rw [h0, map_zero] at hne; exact hne rfl
    rw [mul_inv_cancel₀ hg0, ← map_one RatFunc.C, valueAt_C] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  rw [div_eq_mul_inv, valueAt_mul_of_regularAt hf hg', hinv, div_eq_mul_inv]

end LocalReg

-- Nonzero constants and cover elements in `K5` and `A_C`.
lemma Av0_K5_ne_zero : k5Params.Av0 ≠ 0 := by
  have hT3 := T_K_sub_3_ne
  have h4 : (4 : K5) ≠ 0 := by exact_mod_cast (by decide : (4 : ℕ) ≠ 0)
  have h3 : (3 : K5) ≠ 0 := by exact_mod_cast (by decide : (3 : ℕ) ≠ 0)
  rw [CoverParams.Av0, CoverParams.inv243, k5Params_inv3, k5Params_T]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h4) (pow_ne_zero 5 (inv_ne_zero h3)))
    (pow_ne_zero 3 hT3)

lemma cW_coeff2_K5_ne_zero : k5Params.cW.coeff 2 ≠ 0 := by
  have hmap : locParams.cW.map LocK5.subtype = k5Params.cW :=
    CoverParams.map_cW locParams LocK5.subtype
  have hcoe : k5Params.cW.coeff 2 = (locParams.cW.coeff 2 : K5) := by
    rw [← hmap, Polynomial.coeff_map]; rfl
  rw [hcoe]
  apply LocK5.ne_zero_of_evLoc
  rw [← Polynomial.coeff_map, CoverParams.map_cW, locParams_map_evLoc,
    ← Poly1009.toPoly_c_cW, Poly1009.toPoly_coeff_getD]
  decide

lemma cW_K5_ne_zero : k5Params.cW ≠ 0 := fun h => cW_coeff2_K5_ne_zero (by rw [h, coeff_zero])

lemma cW_eval_ne_zero {L : Type*} [Field L] [Algebra K5 L] {r : L} (hr0 : r ≠ 0) :
    (k5Params.cW.map (algebraMap K5 L)).eval r ≠ 0 := by
  have hcW : k5Params.cW = C (k5Params.cW.coeff 2) * X ^ 2 := by
    rw [CoverParams.cW, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp
  rw [hcW, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    eval_mul, eval_C, eval_pow, eval_X]
  exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K5 L).injective).mpr cW_coeff2_K5_ne_zero)
    (pow_ne_zero 2 hr0)

lemma nm_WU_eval_one : k5Params.nm_WU.eval 1 = H0_K / k5Params.Av0 := by
  have h0 := E0_of_cover (RingHom.id K5) 1 1 one_ne_zero
  simp only [pU, RingHom.id_apply, Polynomial.map_id, div_one, one_mul, one_pow] at h0
  have hH : E_fn 0 S_K Q_K T_K 0 0 1 1 = H0_K := by
    have h1 := H_cub_eq_H0_A1_B1 S_K Q_K T_K 1 1
    simp only [u_of, v_of, sub_self, zero_div, zero_mul, add_zero, one_mul] at h1
    change H_cub S_K Q_K T_K 1 1 1 = H0_K
    rw [h1]
    simpa [SL, QL, TL, ιL] using H0_of_L (L := K5)
  rw [hH] at h0
  have hnm : k5Params.nm_WU.eval 1 = 1 + k5Params.bW.eval 1 + k5Params.cW.eval 1 := by
    simp only [CoverParams.nm_WU, CoverParams.pnm, PairAlg.nm, eval_add, eval_sub, eval_mul,
      eval_pow, eval_neg, eval_X, eval_one]; ring
  rw [hnm, eq_div_iff Av0_K5_ne_zero]
  linear_combination -h0

lemma nm_WU_eval_one_ne {L : Type*} [Field L] [Algebra K5 L] :
    (k5Params.nm_WU.map (algebraMap K5 L)).eval 1 ≠ 0 := by
  have h : (k5Params.nm_WU.map (algebraMap K5 L)).eval 1 = algebraMap K5 L (k5Params.nm_WU.eval 1) := by
    simpa only [map_one] using Polynomial.eval_map_apply (algebraMap K5 L) (1 : K5)
  rw [h, nm_WU_eval_one]
  exact (map_ne_zero_iff _ (algebraMap K5 L).injective).mpr (div_ne_zero H0_K_ne_zero Av0_K5_ne_zero)

lemma nm_WU_K5_ne_zero : k5Params.nm_WU ≠ 0 := fun h => by
  have h1 := nm_WU_eval_one_ne (L := K5)
  rw [h, Polynomial.map_zero, eval_zero] at h1
  exact h1 rfl

lemma cb_h_K5_ne_zero : k5Params.cb_h ≠ 0 := by
  rw [cb_h_K5_eq_mul_monic]
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr (LocK5.ne_zero_of_evLoc cb_h_lc_evLoc_ne))
    (cb_h_m_loc_spec.1.map LocK5.subtype).ne_zero

lemma ca_h_K5_ne_zero : k5Params.ca_h ≠ 0 := by
  intro h0
  have hcop := isCoprime_cb_h_ca_h
  rw [h0, isCoprime_zero_right] at hcop
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hcop
  rw [cb_h_K5_eq_mul_monic, Polynomial.natDegree_C_mul (LocK5.ne_zero_of_evLoc cb_h_lc_evLoc_ne),
    cb_h_m_K5, cb_h_m_loc_spec.1.natDegree_map, cb_h_m_loc_spec.2.1] at hdeg
  omega

lemma Q5_K5_ne_zero : k5Params.Q5_z ≠ 0 := by
  intro h0; have := Q5_K5_natDegree; rw [h0, natDegree_zero] at this; omega

lemma nm_z_K5_ne_zero : k5Params.nm_z ≠ 0 := by
  rw [nm_z_K5_factor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Polynomial.C_ne_zero.mpr lc34_K5_ne_zero)
    (pow_ne_zero 15 X_ne_zero)) (pow_ne_zero 12 (cb_h_m_loc_spec.1.map LocK5.subtype).ne_zero))
    P34_K5_monic.ne_zero

lemma nm_disc_E2z_K5_ne_zero : k5Params.pnm k5Params.disc_E2z ≠ 0 := by
  intro h0
  have hcop := isCoprime_P34_nm_disc_E2z
  rw [h0, isCoprime_zero_right] at hcop
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hcop
  rw [P34_K5_natDegree] at hdeg; omega

lemma polyC_ne_zero {P : K5[X]} (hP : P ≠ 0) : polyC P ≠ 0 :=
  (map_ne_zero_iff ιC_rat ιC_rat.injective).mpr (polynomialMap_ne_zero hP)

lemma pairC_ne_zero_of_pnm {x : PairAlg K5[X]} (h : k5Params.pnm x ≠ 0) : pairC x ≠ 0 := by
  intro h0
  have hnm : evalAC (PairAlg.map toRat x) *
      evalAC (PairAlg.conj (toRat k5Params.bW) (PairAlg.map toRat x)) =
      ιC_rat (toRat (k5Params.pnm x)) := by
    rw [← evalAC_mul, ← evalAC_ofScalar]
    congr 1; ext
    · simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map, CoverParams.pnm,
        PairAlg.nm, map_add, map_sub, map_mul, map_pow]; ring
    · simp only [PairAlg.mul, PairAlg.conj, PairAlg.ofScalar, PairAlg.map]; ring
  change evalAC (PairAlg.map toRat x) = 0 at h0
  rw [h0, zero_mul] at hnm
  exact polyC_ne_zero h hnm.symm

lemma U_C_ne_zero : U_C ≠ 0 := by
  have h : U_C = polyC X := by simp [U_C, polyC, RatFunc.algebraMap_X]
  rw [h]; exact polyC_ne_zero (X_ne_zero (R := K5))

lemma W_C_ne_zero : W_C ≠ 0 := by
  have hW : W_C = pairC PairAlg.W := by simp [pairC, PairAlg.map_W, evalAC_W]
  rw [hW]
  apply pairC_ne_zero_of_pnm
  simpa [CoverParams.pnm, PairAlg.nm, PairAlg.W] using cW_K5_ne_zero

lemma V_C_ne_zero : V_C ≠ 0 := div_ne_zero W_C_ne_zero U_C_ne_zero

lemma u_of_U_C_ne_zero : u_of U_C ≠ 0 := by
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have h1 : U_C - 1 ≠ 0 := by
    have heq : U_C - 1 = polyC (X - 1) := by
      simp [polyC, U_C, map_sub, RatFunc.algebraMap_X]
    rw [heq]; exact polyC_ne_zero (Polynomial.monic_X_sub_C 1).ne_zero
  exact div_ne_zero h1 h9

lemma v_of_V_C_ne_zero : v_of V_C ≠ 0 := by
  have h9 : (9 : A_C) ≠ 0 := by exact_mod_cast (by decide : (9 : ℕ) ≠ 0)
  have hwu : W_C - U_C ≠ 0 := by
    have heq : W_C - U_C = pairC ⟨-X, 1⟩ := by
      simp [pairC, evalAC, PairAlg.map, U_C, RatFunc.algebraMap_X]; ring
    rw [heq]; exact pairC_ne_zero_of_pnm nm_WU_K5_ne_zero
  have h1 : V_C - 1 ≠ 0 := by
    rw [V_C, show W_C / U_C - 1 = (W_C - U_C) / U_C by
      rw [sub_div, div_self U_C_ne_zero]]
    exact div_ne_zero hwu U_C_ne_zero
  exact div_ne_zero h1 h9


def P_G_pair : PairAlg K5[X] :=
  ⟨C DX2_K * X * (X - 1) - C DY2_K * X, C DY2_K⟩

def dB1_dT {R : Type*} [Field R] (T U V : R) : R :=
  (1 / 27) * U * (25 * (5 * T - 9) * (15 * T - 9) - 12 * (T - 3) ^ 2 * V)

def cB1_of {R : Type*} [Field R] (S Q T a b U V : R) : R :=
  let H0 := H0_of S Q T; let B1 := B1_of T U V
  (-B1 * dH0_fn 0 S Q T) * a + (-B1 * dH0_fn 1 S Q T) * b +
  (H0 * dB1_dT T U V - B1 * dH0_fn 2 S Q T)

def P18_regX_of {F : Type*} [Field F] (S Q T x y a b U V : F) : F :=
  let ξS := S - a * T; let ξQ := Q - b * T
  let M0 := A_0U a b ξS ξQ U V / U + A_0V a b ξS ξQ U V / V
  let MY := A_Y a b ξS ξQ U V
  let MX := A_X a b ξS ξQ U V
  let H0 := H0_of S Q T
  let qY := dot_ab (QY_num S Q T x y U V) a b / v_of V
  let qX := dot_ab (CX_of S Q T x y U V) a b / G_of S Q T x y U V ^ 2
  let q1 := H0 * A1_of S Q U V * qY + H0 * B1_of T U V * qX +
    (cA1_of S Q T a b U V / v_of V) * EB_of S Q T x y U V
  M0 * q1 + (MY * qY + MX * qX) * H0 ^ 2

/-- Regularized `P18_of` at `V = 1` (`qY = dot_ab CY_of / G^2` and `cA1 / v = -cB1 / u`). -/
def P18_regY_of {F : Type*} [Field F] (S Q T x y a b U V : F) : F :=
  let ξS := S - a * T; let ξQ := Q - b * T
  let M0 := A_0U a b ξS ξQ U V / U + A_0V a b ξS ξQ U V / V
  let MY := A_Y a b ξS ξQ U V
  let MX := A_X a b ξS ξQ U V
  let H0 := H0_of S Q T
  let qY := dot_ab (CY_of S Q T x y U V) a b / G_of S Q T x y U V ^ 2
  let qX := dot_ab (QX_num S Q T x y U V) a b / u_of U
  let q1 := H0 * A1_of S Q U V * qY + H0 * B1_of T U V * qX +
    (-cB1_of S Q T a b U V / u_of U) * EB_of S Q T x y U V
  M0 * q1 + (MY * qY + MX * qX) * H0 ^ 2

def P18_w_AC (w : A_C) : A_C :=
  SheetCalculus.P18_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
    (-(polyC k5Params.cb_h * w + pairC k5Params.c0W) / (W_C * polyC k5Params.ca_h))
    (w / W_C) U_C V_C

/-- Numerator of `eta_AC` under the mirror `a`-elimination. -/
def eta_AC_num_w : A_C :=
  let q := interp4 P18_w_AC
  let P1w := remDeg4_P1 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0) q.1 q.2.1 q.2.2.1 q.2.2.2.1
  let P0w := remDeg4_P0 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0) q.1 q.2.1 q.2.2.1 q.2.2.2.2
  let d1w := remDeg3_d1 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0)
    (pairC k5Params.e3_3) (pairC k5Params.e3_2) (pairC k5Params.e3_1)
  let d0w := remDeg3_d0 (pairC k5Params.e2_2) (pairC k5Params.e2_1) (pairC k5Params.e2_0)
    (pairC k5Params.e3_3) (pairC k5Params.e3_2) (pairC k5Params.e3_0)
  (P1w * d0w - P0w * d1w) * U_C ^ 3 * W_C * polyC k5Params.ca_h ^ 4


section RegACDefs
variable {L : Type*} [Field L] [Algebra K5 L]
abbrev RegAt (r : L) (g : RatFunc K5) : Prop := RegularAt r (mapRatFunc (algebraMap K5 L) g)
abbrev valAt (r : L) (g : RatFunc K5) : L := valueAt r (mapRatFunc (algebraMap K5 L) g)
abbrev RegUnitAt (r : L) (g : RatFunc K5) : Prop := RegAt r g ∧ valAt r g ≠ 0
structure RegAC (r : L) (x : A_C) : Prop where
  c0 : RegAt r (coordsAC x).c0
  c1 : RegAt r (coordsAC x).c1
def nmAC (x : A_C) : RatFunc K5 := PairAlg.nm (toRat k5Params.bW) (toRat k5Params.cW) (coordsAC x)
end RegACDefs
end Regularity

section SplittingAndResidues
open scoped Classical

lemma residue_div_simpleZero {K : Type*} [Field K] (r : K) (f : RatFunc K) (D : K[X])
    (hf : RegularAt r f) (hD0 : D.eval r = 0) (hDd : D.derivative.eval r ≠ 0) :
    CrossedRationalResidue.residue r (f / algebraMap K[X] (RatFunc K) D) =
      valueAt r f / D.derivative.eval r := by
  obtain ⟨P, Q, hQ, rfl⟩ := hf
  rw [div_div, ← map_mul]
  have hQD0 : (Q * D).eval r = 0 := by simp [hD0]
  have hQDd : (Q * D).derivative.eval r = Q.eval r * D.derivative.eval r := by
    simp [derivative_mul, hD0]
  have hQDd_ne : (Q * D).derivative.eval r ≠ 0 := by rw [hQDd]; exact mul_ne_zero hQ hDd
  rw [HodgeComputer.Formal.QuadraticCovers.simplePole_residue P (Q * D) r hQD0 hQDd_ne, hQDd, valueAt_div_polynomials r P Q hQ]
  field_simp [hQ, hDd]

lemma P34_K5_ne_zero : P34_K5 ≠ 0 := by
  intro h0
  have hdeg := P34_K5_natDegree
  rw [h0, natDegree_zero] at hdeg
  omega

/-- Base polynomial whose splitting field `L1` splits `eta.denom`, `P34_K5`, and `Q5_z`. -/
def Q_base : K5[X] := eta.denom * P34_K5 * k5Params.Q5_z

lemma Q_base_ne_zero : Q_base ≠ 0 :=
  mul_ne_zero (mul_ne_zero eta.denom_ne_zero P34_K5_ne_zero) Q5_K5_ne_zero

abbrev L1 : Type := Polynomial.SplittingField Q_base

/-- Product of all 34 fiber quadratics `W^2 + bW(r) * W + cW(r)` over `L1` for `r ∈ roots(P34)`. -/
def Q_quad : L1[X] :=
  ∏ r ∈ (P34_K5.map (algebraMap K5 L1)).roots.toFinset,
    (X ^ 2 + C ((k5Params.bW.map (algebraMap K5 L1)).eval r) * X +
      C ((k5Params.cW.map (algebraMap K5 L1)).eval r))

private lemma monic_quad_poly {F : Type*} [Field F] (b c : F) :
    (X ^ 2 + C b * X + C c : F[X]).Monic := by
  rw [add_assoc]
  apply (monic_X_pow 2).add_of_left
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))
  · exact lt_of_le_of_lt degree_C_le (by rw [degree_X_pow]; exact WithBot.coe_lt_coe.mpr (by omega))

private lemma natDegree_quad_poly {F : Type*} [Field F] (b c : F) :
    (X ^ 2 + C b * X + C c : F[X]).natDegree = 2 := by
  rw [add_assoc]
  have hlt : (C b * X + C c : F[X]).natDegree < 2 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ (by simp))
    exact lt_of_le_of_lt (natDegree_C_mul_le _ _) (by simp)
  rw [natDegree_add_eq_left_of_natDegree_lt (by simpa using hlt), natDegree_X_pow]

lemma Q_quad_ne_zero : Q_quad ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => (monic_quad_poly _ _).ne_zero

/-- Finite splitting field `CoverL / K5` splitting `eta.denom`, `P34_K5`, `Q5_z`, and every
quadratic fiber `W^2 + bW(r) * W + cW(r)` above `r ∈ R34`. -/
abbrev CoverL : Type := Polynomial.SplittingField Q_quad

instance : FiniteDimensional K5 CoverL :=
  Module.Finite.trans L1 CoverL

instance : CharZero CoverL :=
  charZero_of_injective_ringHom (algebraMap K5 CoverL).injective

abbrev ιL_K5 : K5 →+* CoverL := algebraMap K5 CoverL

/-- The base-changed cover 1-form `eta_L ∈ RatFunc CoverL`. -/
def eta_L : RatFunc CoverL := mapRatFunc ιL_K5 eta

/-- The 34 horizontal branch points `R_{34} ⊆ CoverL`. -/
def R34 : Finset CoverL := (P34_K5.map ιL_K5).roots.toFinset

/-- The 5 `Q_5 = 0` branch points `R_{Q5} ⊆ CoverL`. -/
def RQ5 : Finset CoverL := (k5Params.Q5_z.map ιL_K5).roots.toFinset

private lemma Q_base_splits_L1 : (Q_base.map (algebraMap K5 L1)).Splits :=
  Polynomial.SplittingField.splits Q_base

lemma P34_splits_L1 : (P34_K5.map (algebraMap K5 L1)).Splits := by
  apply Q_base_splits_L1.of_dvd (Polynomial.map_ne_zero Q_base_ne_zero)
  refine ⟨(eta.denom * k5Params.Q5_z).map (algebraMap K5 L1), ?_⟩
  simp only [Q_base, Polynomial.map_mul]; ring

lemma P34_splits_CoverL : (P34_K5.map ιL_K5).Splits := by
  have h := P34_splits_L1.map (algebraMap L1 CoverL)
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL] at h

lemma Q5_splits_CoverL : (k5Params.Q5_z.map ιL_K5).Splits := by
  have h1 : (k5Params.Q5_z.map (algebraMap K5 L1)).Splits := by
    apply Q_base_splits_L1.of_dvd (Polynomial.map_ne_zero Q_base_ne_zero)
    refine ⟨(eta.denom * P34_K5).map (algebraMap K5 L1), ?_⟩
    simp only [Q_base, Polynomial.map_mul]; ring
  have h := h1.map (algebraMap L1 CoverL)
  rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL] at h

lemma eta_L_denom_splits : eta_L.denom.Splits := by
  have h1 : (eta.denom.map (algebraMap K5 L1)).Splits := by
    apply Q_base_splits_L1.of_dvd (Polynomial.map_ne_zero Q_base_ne_zero)
    refine ⟨(P34_K5 * k5Params.Q5_z).map (algebraMap K5 L1), ?_⟩
    simp only [Q_base, Polynomial.map_mul]; ring
  have h2 : (eta.denom.map ιL_K5).Splits := by
    have h := h1.map (algebraMap L1 CoverL)
    rwa [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K5 L1 CoverL] at h
  exact h2.of_dvd (Polynomial.map_ne_zero eta.denom_ne_zero) (mapRatFunc_denom_dvd ιL_K5 eta)

lemma mem_R34_iff {r : CoverL} : r ∈ R34 ↔ (P34_K5.map ιL_K5).eval r = 0 := by
  simp only [R34, Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero P34_K5_ne_zero),
    Polynomial.IsRoot.def]

lemma mem_RQ5_iff {r : CoverL} : r ∈ RQ5 ↔ (k5Params.Q5_z.map ιL_K5).eval r = 0 := by
  simp only [RQ5, Multiset.mem_toFinset, Polynomial.mem_roots (Polynomial.map_ne_zero Q5_K5_ne_zero),
    Polynomial.IsRoot.def]

lemma zero_notMem_R34 : (0 : CoverL) ∉ R34 := by
  intro h0
  have h := eval_ne_zero_of_isCoprime isCoprime_P34_X (mem_R34_iff.mp h0)
  simp at h

lemma zero_notMem_RQ5 : (0 : CoverL) ∉ RQ5 := by
  intro h0
  have h := eval_ne_zero_of_isCoprime isCoprime_Q5_X (mem_RQ5_iff.mp h0)
  simp at h

lemma disjoint_R34_RQ5 : Disjoint R34 RQ5 := by
  rw [Finset.disjoint_left]
  intro r hr34 hr5
  exact eval_ne_zero_of_isCoprime isCoprime_P34_Q5 (mem_R34_iff.mp hr34) (mem_RQ5_iff.mp hr5)


def valAC (r w : CoverL) (x : A_C) : CoverL :=
  valueAt r (mapRatFunc ιL_K5 (coordsAC x).c0) + valueAt r (mapRatFunc ιL_K5 (coordsAC x).c1) * w

structure ValAC (r w : CoverL) (x : A_C) (v : CoverL) : Prop where
  reg : RegAC r x
  eq : valAC r w x = v

/-- Bundled algebraic cover-equation, degree, and regularized-form identities for `eta_AC`. -/
structure CoverRegIdentitiesSpec : Prop where
  numM_deg3 : ∀ {F : Type} [Field F] [CharZero F] (mi : Fin 10) (S Q T U V a1 a0 b1 b0 : F),
    IsPolyDeg 3 (fun z => SheetCalculus.numM mi (a1 * z + a0) (b1 * z + b0)
      (S - (a1 * z + a0) * T) (Q - (b1 * z + b0) * T) U V)
  P18_deg4 : ∀ {F : Type} [Field F] [CharZero F] (S Q T x y U V a1 a0 b1 b0 : F),
    IsPolyDeg 4 (fun z => SheetCalculus.P18_of S Q T x y (a1 * z + a0) (b1 * z + b0) U V)
  E1_cover : ∀ {F : Type} [Field F] [CharZero F] (φ : K5 →+* F) (a b U W : F), U ≠ 0 →
    W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0 →
    U * E_fn 1 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pU φ k5Params.ca_h U * (W * a) + pU φ k5Params.cb_h U * (W * b) + pUW φ k5Params.c0W U W
  E2_z_cover : ∀ {F : Type} [Field F] [CharZero F] (φ : K5 →+* F) (z U W : F),
    U ≠ 0 → W ≠ 0 → pU φ k5Params.cb_h U ≠ 0 →
    W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0 →
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    U * W * pU φ k5Params.cb_h U ^ 2 * E_fn 2 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pUW φ k5Params.d2_2 U W * z ^ 2 + pUW φ k5Params.d2_1 U W * z + pUW φ k5Params.d2_0 U W
  E3_z_cover : ∀ {F : Type} [Field F] [CharZero F] (φ : K5 →+* F) (z U W : F),
    U ≠ 0 → W ≠ 0 → pU φ k5Params.cb_h U ≠ 0 →
    W ^ 2 + pU φ k5Params.bW U * W + pU φ k5Params.cW U = 0 →
    let a := z / W
    let b := -(pU φ k5Params.ca_h U * z + pUW φ k5Params.c0W U W) / (W * pU φ k5Params.cb_h U)
    U * W ^ 2 * pU φ k5Params.cb_h U ^ 3 * E_fn 3 (φ S_K) (φ Q_K) (φ T_K) a b U (W / U) =
      pUW φ k5Params.d3_3 U W * z ^ 3 + pUW φ k5Params.d3_2 U W * z ^ 2 +
      pUW φ k5Params.d3_1 U W * z + pUW φ k5Params.d3_0 U W
  nine_U_G_AC : 9 * U_C * G_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K) U_C V_C = pairC P_G_pair
  pnm_P_G_one : ∀ {L : Type} [Field L] [Algebra K5 L],
    ((k5Params.pnm P_G_pair).map (algebraMap K5 L)).eval 1 =
      (algebraMap K5 L DY2_K) ^ 2 * (k5Params.nm_WU.map (algebraMap K5 L)).eval 1
  P18_regX : ∀ z : A_C, P18_z_AC z = P18_regX_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
    (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)) U_C V_C
  P18_regY : ∀ z : A_C, P18_z_AC z = P18_regY_of (ιC_K5 S_K) (ιC_K5 Q_K) (ιC_K5 T_K) (ιC_K5 x_K) (ιC_K5 y_K)
    (z / W_C) (-(polyC k5Params.ca_h * z + pairC k5Params.c0W) / (W_C * polyC k5Params.cb_h)) U_C V_C
  eta_a_elim : eta_AC = eta_AC_num_w /
    (81 * ιC_K5 k5Params.Av0 * (2 * W_C + polyC k5Params.bW) * polyC k5Params.Q5_z ^ 3 * pairC k5Params.res_w)

end SplittingAndResidues
end SymmetricSexticResidual.CoverResidue


