-- Prove2me | Definitions.Def_ChapterSmComparisonEsa
-- name    : ChapterSmComparisonEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T20:48:48.700553+00:00
-- url     : https://prove2.me/theorems/4178500b-ffe7-447b-a6cd-a95b5680542a
-- title:
--   ChapterSmComparisonEsa
-- statement:
--   ChapterSmComparisonEsa

import Definitions.Def_ChapterHermiteGraphApprox
import Definitions.Def_ChapterSmFarisLavine
import Definitions.Def_ChapterDegKatoEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Theorems.Thm_BookProof_KatoRellich_essentiallySelfAdjointOn_add_bounded
import Theorems.Thm_BookProof_QgHermiteFriedrichs_potLp_coeFn
import Theorems.Thm_BookProof_SmHamiltonian_realCoeff_smFormPoly
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_op


/-!
# The Standard-Model Faris–Lavine comparison operator is essentially self-adjoint

`BookProof/ChapterSmFarisLavine.lean` proves both Faris–Lavine inequalities for the pair
`(h, N)`, `N = 2h + Σ_m q_m² + c₀`, and reduces essential self-adjointness of the
Standard-Model one-particle Hamiltonian `h` on the Gauss–polynomial core of `L²(ℝ¹⁶³)` to
essential self-adjointness of `N` on the same core (`sm_h_esa_of_comparison_esa`).  That
remaining input is a Kato-type theorem for a Schrödinger operator with a coupled quartic
potential, which the Faris–Lavine criterion structurally cannot supply.

This module supplies it, and thereby removes the hypothesis:

* `smFlN_eq_hamCoreS` — on the core, `N = 2h + Σ_m q_m² + c₀` *is* the degenerate
  Schrödinger operator `−Δ_S + W` of `BookProof.DegSchrodinger`, with `S` the 40
  momentum-carrying coordinates and `W = Σ_r Φ_r² + Σ_m q_m² + c₀` a non-negative polynomial
  of degree four;
* `smFlN_esa` — hence `N` is essentially self-adjoint on the Gauss–polynomial core, by the
  Kato theorem of `BookProof.DegKatoEsa` and the Hermite graph approximation of
  `BookProof.HermiteGraphApprox`;
* **`sm_h_esa`** — hence so is the Standard-Model one-particle Hamiltonian itself.
-/

namespace BookProof.SmComparisonEsa

open MeasureTheory MvPolynomial
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgOneParticleCc BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.DegSchrodinger BookProof.DegKatoEsa BookProof.HermiteGraphApprox
open BookProof.SmOneParticle BookProof.SmHamiltonian BookProof.SmFarisLavine

noncomputable section

/-! ## 1. Transport of polynomial operators to the core, in coordinates -/

theorem equiv_pgLp (p : MvPolynomial (Fin 163) ℂ) :
    (coreRepPoly 163).equiv p = ⟨pgLp p, pgLp_mem_core p⟩ :=
  Subtype.ext ((coreRepPoly 163).coe_equiv p)

theorem equiv_symm_pgLp (p : MvPolynomial (Fin 163) ℂ) :
    (coreRepPoly 163).equiv.symm ⟨pgLp p, pgLp_mem_core p⟩ = p := by
  rw [← equiv_pgLp p, LinearEquiv.symm_apply_apply]

theorem op_pgLp (T : Module.End ℂ (MvPolynomial (Fin 163) ℂ)) (p : MvPolynomial (Fin 163) ℂ) :
    (coreRepPoly 163).op T ⟨pgLp p, pgLp_mem_core p⟩ = ⟨pgLp (T p), pgLp_mem_core _⟩ := by
  refine Subtype.ext ?_
  rw [CoreRep.coe_op, equiv_symm_pgLp]

/-! ## 2. The data of the comparison operator as a degenerate Schrödinger operator -/

/-- The 40 momentum-carrying coordinates of the Standard-Model field space. -/
def smS : Finset (Fin 163) := Finset.image smCoord Finset.univ

/-- The `r`-th field polynomial of the Standard-Model Hamiltonian. -/
def smPhi (P : SmParams) (r : Fin 49) : MvPolynomial (Fin 163) ℂ :=
  smFormPoly P (id : Fin 163 → Fin 163) (smFormFin.symm r)

theorem realCoeff_smPhi (P : SmParams) (r : Fin 49) : RealCoeff (smPhi P r) :=
  realCoeff_smFormPoly P _ _

/-- The potential of the comparison operator: `W = Σ_r Φ_r² + Σ_m q_m² + c₀`. -/
def smPotPoly (P : SmParams) (c0 : ℝ) : MvPolynomial (Fin 163) ℂ :=
  (∑ r : Fin 49, smPhi P r * smPhi P r) + smQPoly + C ((c0 : ℝ) : ℂ)

theorem realCoeff_C_ofReal {d : ℕ} (c : ℝ) :
    RealCoeff (C ((c : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ) :=
  realCoeff_C_real' c

theorem realCoeff_smPotPoly (P : SmParams) (c0 : ℝ) : RealCoeff (smPotPoly P c0) :=
  ((RealCoeff.sum fun r _ => (realCoeff_smPhi P r).mul (realCoeff_smPhi P r)).add
      realCoeff_smQPoly).add (realCoeff_C_ofReal c0)

/-- The potential is a sum of squares of real polynomials, plus `c₀`. -/
theorem polyW_smPotPoly (P : SmParams) (c0 : ℝ) (x : Vd 163) :
    polyW (smPotPoly P c0) x
      = (∑ r : Fin 49, (polyW (smPhi P r) x) ^ 2)
        + (∑ m : Fin 40, (x (smCoord m)) ^ 2) + c0 := by
  have hphi : ∀ r : Fin 49, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (smPhi P r)
      = ((polyW (smPhi P r) x : ℝ) : ℂ) :=
    fun r => (polyW_ofReal (realCoeff_smPhi P r) x).symm
  have key : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (smPotPoly P c0)
      = (∑ r : Fin 49, ((polyW (smPhi P r) x : ℝ) : ℂ) ^ 2)
        + (∑ m : Fin 40, ((x (smCoord m) : ℝ) : ℂ) ^ 2) + ((c0 : ℝ) : ℂ) := by
    simp only [smPotPoly, map_add, map_sum, map_mul, MvPolynomial.eval_C, smQPoly,
      MvPolynomial.eval_X, hphi, sq]
  have hcast : (∑ r : Fin 49, ((polyW (smPhi P r) x : ℝ) : ℂ) ^ 2)
        + (∑ m : Fin 40, ((x (smCoord m) : ℝ) : ℂ) ^ 2) + ((c0 : ℝ) : ℂ)
      = (((∑ r : Fin 49, (polyW (smPhi P r) x) ^ 2)
          + (∑ m : Fin 40, (x (smCoord m)) ^ 2) + c0 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [polyW, key, hcast, Complex.ofReal_re]

/-- The potential is bounded below by `c₀`. -/
theorem one_le_polyW_smPotPoly (P : SmParams) {c0 : ℝ} (hc0 : 1 ≤ c0) (x : Vd 163) :
    1 ≤ polyW (smPotPoly P c0) x := by
  rw [polyW_smPotPoly]
  have h1 : (0 : ℝ) ≤ ∑ r : Fin 49, (polyW (smPhi P r) x) ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ ∑ m : Fin 40, (x (smCoord m)) ^ 2 := by positivity
  linarith

/-! ## 3. The comparison operator is `−Δ_S + W` -/

/-- Multiplication by a real-coefficient polynomial is the potential term of `polyW`. -/
theorem potLp_polyW {d : ℕ} {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q)
    (p : MvPolynomial (Fin d) ℂ) :
    potLp (polyW q) (continuous_polyW q) (expBounded_polyW q) p = pgLp (q * p) := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [potLp_coeFn (polyW q) (continuous_polyW q) (expBounded_polyW q) p,
    pgLp_coeFn (q * p)] with x h1 h2
  rw [h1, h2, pgFun_mul_polyW hq]

/-- The momentum operator squared is the twisted second derivative. -/
theorem momOp_momOp (j : Fin 163) (p : MvPolynomial (Fin 163) ℂ) :
    momOp j (momOp j p) = -coreD j (coreD j p) := by
  have hstep : ∀ r : MvPolynomial (Fin 163) ℂ, momOp j r = (-Complex.I) • coreD j r := by
    intro r
    rw [momOp_apply, coreD]
    congr 1
    congr 1
    rw [MvPolynomial.smul_eq_C_mul]
    norm_num
  rw [hstep, hstep, coreD_smul, smul_smul]
  have hII : (-Complex.I) * (-Complex.I) = -1 := by
    simp [Complex.I_mul_I]
  rw [hII]
  module

/-- The sum of the momentum squares is the kinetic polynomial of the coordinate set `smS`. -/
theorem sum_momOp_eq_kinPolyS (p : MvPolynomial (Fin 163) ℂ) :
    (∑ m : Fin 40, momOp (smCoord m) (momOp (smCoord m) p)) = kinPolyS smS p := by
  have h : ∀ m : Fin 40, momOp (smCoord m) (momOp (smCoord m) p)
      = -coreD (smCoord m) (coreD (smCoord m) p) := fun m => momOp_momOp _ p
  rw [Finset.sum_congr rfl fun m _ => h m, kinPolyS, smS,
    Finset.sum_image (fun a _ b _ hab => smCoord_injective hab)]
  simp only [Finset.sum_neg_distrib]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
-- The identification unfolds the 40 + 49 summands of the 163-variable operator at once.
/-- **The comparison operator is a degenerate Schrödinger operator.**  On the
Gauss–polynomial core, `N = 2h + Σ_m q_m² + c₀` equals `−Δ_S + W` with `S` the momentum
coordinates and `W = Σ_r Φ_r² + Σ_m q_m² + c₀`. -/
theorem smFlN_eq_hamCoreS (P : SmParams) (c0 : ℝ) :
    smFlN P c0
      = hamCoreS (polyW (smPotPoly P c0)) (continuous_polyW _) (expBounded_polyW _) smS := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨p, hp⟩ := x.2
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := Subtype.ext hp.symm
  subst hx
  -- the two sides, written as `pgLp` of a polynomial
  have hpi : ∀ m : Fin 40,
      ((smPi m (smPi m ⟨pgLp p, pgLp_mem_core p⟩) : polyGaussCore (d := 163)) : L2d 163)
        = pgLp (momOp (smCoord m) (momOp (smCoord m) p)) := by
    intro m
    have h1 : smPi m ⟨pgLp p, pgLp_mem_core p⟩
        = ⟨pgLp (momOp (smCoord m) p), pgLp_mem_core _⟩ := by
      rw [show smPi m = (coreRepPoly 163).op (momOp (smCoord m)) from rfl, op_pgLp]
    rw [h1, show smPi m = (coreRepPoly 163).op (momOp (smCoord m)) from rfl, op_pgLp]
  have hfield : ∀ r : Fin 49,
      ((smField P r (smField P r ⟨pgLp p, pgLp_mem_core p⟩) : polyGaussCore (d := 163))
          : L2d 163)
        = pgLp (smPhi P r * (smPhi P r * p)) := by
    intro r
    have hop : smField P r = (coreRepPoly 163).op (mulOp (smPhi P r)) := rfl
    have h1 : smField P r ⟨pgLp p, pgLp_mem_core p⟩
        = ⟨pgLp (smPhi P r * p), pgLp_mem_core _⟩ := by
      rw [hop, op_pgLp]
      rfl
    rw [h1, hop, op_pgLp]
    rfl
  have hQ : smQL ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (smQPoly * p) := by
    rw [smQL_apply, show smQOp = (coreRepPoly 163).op (mulOp smQPoly) from rfl, op_pgLp]
    rfl
  have hH : smHamiltonian P ⟨pgLp p, pgLp_mem_core p⟩
      = ((1 / 2 : ℝ) : ℂ) • ((∑ m : Fin 40, pgLp (momOp (smCoord m) (momOp (smCoord m) p)))
          + ∑ r : Fin 49, pgLp (smPhi P r * (smPhi P r * p))) := by
    rw [smHamiltonian, weylOp_apply]
    have h1 : (∑ i : Fin 40,
          ((smPi i) ((smPi i) ⟨pgLp p, pgLp_mem_core p⟩) : L2d 163))
        = ∑ m : Fin 40, pgLp (momOp (smCoord m) (momOp (smCoord m) p)) :=
      Finset.sum_congr rfl fun m _ => hpi m
    have h2 : (∑ a : Fin 49,
          ((smField P a) ((smField P a) ⟨pgLp p, pgLp_mem_core p⟩) : L2d 163))
        = ∑ r : Fin 49, pgLp (smPhi P r * (smPhi P r * p)) :=
      Finset.sum_congr rfl fun r _ => hfield r
    rw [h1, h2]
  -- collect the left-hand side
  have hpgsum : ∀ (n : ℕ) (f : Fin n → MvPolynomial (Fin 163) ℂ),
      (∑ i : Fin n, pgLp (f i)) = pgLp (∑ i : Fin n, f i) := by
    intro n f
    rw [← HermiteProductCore.pgMap_apply, map_sum]
    rfl
  have hlhs : smFlN P c0 ⟨pgLp p, pgLp_mem_core p⟩
      = pgLp ((∑ m : Fin 40, momOp (smCoord m) (momOp (smCoord m) p))
          + (∑ r : Fin 49, smPhi P r * (smPhi P r * p)) + smQPoly * p
          + ((c0 : ℝ) : ℂ) • p) := by
    rw [smFlN_apply, hH, hQ]
    have hcoe : ((⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := 163)) : L2d 163) = pgLp p := rfl
    rw [hcoe, hpgsum, hpgsum]
    have hmap : ∀ r : MvPolynomial (Fin 163) ℂ, pgLp r = pgMap (d := 163) r := fun _ => rfl
    simp only [hmap, ← map_smul, ← map_add]
    congr 1
    push_cast
    module
  -- collect the right-hand side
  have hrhs : hamCoreS (polyW (smPotPoly P c0)) (continuous_polyW _) (expBounded_polyW _) smS
        ⟨pgLp p, pgLp_mem_core p⟩
      = pgLp (kinPolyS smS p + smPotPoly P c0 * p) := by
    rw [hamCoreS_pgLp, hamPolyS, potLp_polyW (realCoeff_smPotPoly P c0)]
    rw [← HermiteProductCore.pgMap_apply, ← HermiteProductCore.pgMap_apply, ← map_add]
    rfl
  rw [hlhs, hrhs]
  congr 1
  rw [← sum_momOp_eq_kinPolyS, smPotPoly]
  simp only [add_mul, Finset.sum_mul, mul_assoc]
  rw [MvPolynomial.smul_eq_C_mul]
  ring

/-! ## 4. Essential self-adjointness -/

/-- **The Faris–Lavine comparison operator of the Standard Model is essentially self-adjoint
on the Gauss–polynomial core of `L²(ℝ¹⁶³)`**, for every choice of couplings, structure
constants, electroweak generators and every shift `c₀ ≥ 1`. -/
theorem smFlN_esa_one_le (P : SmParams) {c0 : ℝ} (hc0 : 1 ≤ c0) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 163)) (smFlN P c0) := by
  rw [smFlN_eq_hamCoreS P c0]
  exact hamCoreS_esa (smPotPoly P c0) (realCoeff_smPotPoly P c0)
    (one_le_polyW_smPotPoly P hc0) smS

/-- **The Faris–Lavine comparison operator is essentially self-adjoint for every shift.**
Changing `c₀` is a bounded symmetric perturbation. -/
theorem smFlN_esa (P : SmParams) (c0 : ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 163)) (smFlN P c0) := by
  have hbase := smFlN_esa_one_le P (c0 := 1) le_rfl
  have hsym := smFlN_symmetricOn P 1
  have hkey := BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded (smFlN P 1) hsym hbase
    (((c0 - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (L2d 163)) (fun u v => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        inner_smul_left, inner_smul_right, Complex.conj_ofReal])
  have hid : smFlN P 1
      + ((((c0 - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (L2d 163)).toLinearMap
        ∘ₗ (polyGaussCore (d := 163)).subtype) = smFlN P c0 := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      Submodule.subtype_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smFlN_apply]
    push_cast
    module
  rwa [hid] at hkey

/-- **The Standard-Model one-particle Hamiltonian is essentially self-adjoint on the
Gauss–polynomial core of `L²(ℝ¹⁶³)`** — unconditionally. -/
theorem sm_h_esa (P : SmParams) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 163)) (smHamiltonian P) :=
  sm_h_esa_of_comparison_esa P (c0 := 1) zero_le_one (smFlN_esa P 1)

end

end BookProof.SmComparisonEsa


