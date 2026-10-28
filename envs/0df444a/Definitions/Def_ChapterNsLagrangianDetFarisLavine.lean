-- Prove2me | Definitions.Def_ChapterNsLagrangianDetFarisLavine
-- name    : ChapterNsLagrangianDetFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T09:09:56.877643+00:00
-- url     : https://prove2.me/theorems/48f66a00-7254-405f-b9e1-3ef65463a8b9
-- title:
--   ChapterNsLagrangianDetFarisLavine
-- statement:
--   ChapterNsLagrangianDetFarisLavine

import Definitions.Def_ChapterKoopmanLyapunovFarisLavine
import Definitions.Def_ChapterNsLagrangianDetConvolution
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Theorems.Thm_BookProof_NsLagrangianDet_volPot_eval_nonneg
import Theorems.Thm_BookProof_NsLagrangianDet_conjP_volPot


/-!
# Lagrangian Navier–Stokes with the determinant constraint, through Faris–Lavine

The fluid is described in **Lagrangian variables**: the displacement `ξ(a)` of the material point
with reference position `a ∈ 𝕋³` and its material velocity `v(a) = ξ̇(a)`, both Galerkin fields on a
finite set `K` of wave vectors (`BookProof.ChapterNsLagrangianDetConvolution`).  The phase space is
`ℝ^{PIdx K}`, with coordinates `x_{(false, k, i, Re/Im)}` (the displacement coefficients `ξ̂_{k,i}`)
and `x_{(true, k, i, Re/Im)}` (the velocity coefficients `v̂_{k,i}`).

**Incompressibility** is the constraint `det(I + ∇ξ) = 1`.  Its Fourier coefficients are the
momentum-convolution polynomials `volCoef q` of the displacement coordinates, in which every
spatial derivative has become the momentum `i k` (`NsLagrangianDet.det_deformation_eq`).  The
constraint enters the dynamics through the **volume penalty**
`V_κ = (κ/2) Σ_q |(det F − 1)^(q)|²` (bulk modulus `κ`), whose gradient is the Lagrange-multiplier
(pressure / Piola) force and whose zero set is incompressible
(`NsLagrangianDet.det_eq_one_of_volPot_eq_zero`).  The Galerkin equations are

```
ξ̇ = v,          v̇ = −ν |k|² v − ∂V_κ/∂ξ ,
```

(unit mass per real coordinate; the Parseval factor is absorbed in `κ`).  The Koopman–von Neumann
generator of this flow is `H_L = ½ Σ (π F + F π)` (`lagKoopmanOp`), the Weyl-ordered first-order
operator on `L²(ℝ^{PIdx K})`, with the **exact** degree-five constraint force (no linearization of
the determinant).

## What is proved

* `lagFlux_eq` — the **energy identity**: for the Lagrangian energy
  `E = 1 + ½|v|² + V_κ(ξ)`, the derivative along the flow is `F·∇E = −ν Σ |k|² v²`: the constraint
  force does no net work (it is the gradient of the potential part of `E`);
* `lagDiv_eq` — the **Liouville identity** `div F = −ν Σ |k|²` (constant);
* `lagKoopmanOp_symmetricOn` — `H_L` is symmetric on the Gauss–polynomial core;
* `lagComparison_commForm` — with the comparison operator `N_L = H_L² + E`, the exact
  commutation relation `⟪x, i[H_L, N_L] x⟫ = ⟪x, (−ν Σ |k|² v²) x⟫`;
* `lagComparison_commForm_bound` — `|⟪x, i[H_L, N_L] x⟫| ≤ 2νΛ ⟪x, N_L x⟫`;
* `lagComparison_quadForm_ge`, `lagComparison_relBound` — `N_L ≥ 1` and `‖H_L x‖ ≤ ‖N_L x‖ + ‖x‖`;
* **`lagKoopman_esa_of_comparison_esa`** — Faris–Lavine: if `N_L` is essentially self-adjoint on
  the core, then so is the Lagrangian Navier–Stokes generator `H_L`.

## Honest boundary

* As for the Eulerian generator (`NsNonlinearFarisLavine`), the essential self-adjointness of the
  comparison operator `N_L` is an **explicit hypothesis**, not proved.  Everything else in the
  Faris–Lavine criterion is discharged.
* The constraint is imposed by the penalty `V_κ` (a slightly compressible fluid with bulk modulus
  `κ`); the exactly incompressible dynamics is the formal limit `κ → ∞`, which is not taken here.
* The viscous term is `ν Δ_a v` in the reference coordinates (`−ν|k|² v̂_k`), which is the
  Lagrangian viscous term at `F = I`; the exact Lagrangian viscous term (with `F^{−1}`) is not
  polynomial and is not used.
-/

namespace BookProof.NsLagrangianDetFL

open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman BookProof.KoopmanLyapunov BookProof.NsLagrangianDet

noncomputable section

variable {K : Type*} [Fintype K]

/-! ## 1. The phase space and the data -/

/-- Phase-space indices: `(false, j)` the displacement coordinate `j`, `(true, j)` the velocity
coordinate `j`. -/
abbrev PIdx (K : Type*) := Bool × DIdx K

/-- The displacement coordinates inside the phase space. -/
def dispVar (j : DIdx K) : PIdx K := (false, j)

omit [Fintype K] in
theorem dispVar_injective : Function.Injective (dispVar (K := K)) := by
  intro a b h; simpa [dispVar] using h

/-- **Lagrangian Navier–Stokes data**: the base wave vectors, the viscosity `ν ≥ 0` and the bulk
modulus `κ ≥ 0` of the incompressibility penalty. -/
structure LagNsData (K : Type*) where
  /-- The base wave vectors `k ∈ ℝ³`. -/
  kvec : K → Fin 3 → ℝ
  /-- The kinematic viscosity `ν`. -/
  nu : ℝ
  /-- The bulk modulus `κ` of the volume penalty. -/
  kappa : ℝ
  nu_nonneg : 0 ≤ nu
  kappa_nonneg : 0 ≤ kappa

variable (S : LagNsData K)

/-- The Stokes eigenvalue `|k|²` of a coordinate. -/
def lam (j : DIdx K) : ℝ := ∑ c, S.kvec j.1 c ^ 2

omit [Fintype K] in
theorem lam_nonneg (j : DIdx K) : 0 ≤ lam S j := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The volume penalty `V_κ(ξ)` as a function on the phase space. -/
def potP : MvPolynomial (PIdx K) ℂ := rename dispVar (volPot S.kappa S.kvec)

/-- **The Lagrangian Navier–Stokes vector field**: `ξ̇ = v`, `v̇ = −ν|k|² v − ∂V_κ/∂ξ`. -/
def lagDrift : PIdx K → MvPolynomial (PIdx K) ℂ
  | (false, j) => X (true, j)
  | (true, j) => -(((S.nu * lam S j : ℝ) : ℂ) • X (true, j)) - pderiv (false, j) (potP S)

/-- **The Lagrangian energy** `E = 1 + ½|v|² + V_κ(ξ)`. -/
def lagEnergy : MvPolynomial (PIdx K) ℂ :=
  1 + ((1 / 2 : ℝ) : ℂ) • ∑ j : DIdx K, (X (true, j) : MvPolynomial (PIdx K) ℂ) * X (true, j)
    + potP S

/-- The viscous dissipation `−ν Σ |k|² v²`. -/
def lagFlux : MvPolynomial (PIdx K) ℂ :=
  ∑ j : DIdx K,
    ((-(S.nu * lam S j) : ℝ) : ℂ) • ((X (true, j) : MvPolynomial (PIdx K) ℂ) * X (true, j))

/-! ## 2. The energy and Liouville identities -/

omit [Fintype K] in
theorem pderiv_vel_rename (j : DIdx K) (p : MvPolynomial (DIdx K) ℂ) :
    pderiv ((true, j) : PIdx K) (rename dispVar p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, dispVar]

theorem pderiv_vel_potP (j : DIdx K) : pderiv ((true, j) : PIdx K) (potP S) = 0 :=
  pderiv_vel_rename j _

theorem pderiv_disp_potP (j : DIdx K) :
    pderiv ((false, j) : PIdx K) (potP S) = rename dispVar (pderiv j (volPot S.kappa S.kvec)) :=
  pderiv_rename dispVar_injective j _

theorem pderiv_disp_vsq (j : DIdx K) :
    pderiv ((false, j) : PIdx K)
      (∑ l : DIdx K, (X (true, l) : MvPolynomial (PIdx K) ℂ) * X (true, l)) = 0 := by
  classical
  simp [pderiv_X]

theorem pderiv_vel_vsq (j : DIdx K) :
    pderiv ((true, j) : PIdx K)
      (∑ l : DIdx K, (X (true, l) : MvPolynomial (PIdx K) ℂ) * X (true, l))
      = (2 : ℂ) • X (true, j) := by
  classical
  rw [map_sum, Finset.sum_eq_single j (fun l _ hl => by
    rw [pderiv_mul, pderiv_X_of_ne (by simpa using hl)]
    simp) (fun h => absurd (Finset.mem_univ j) h)]
  rw [pderiv_mul, pderiv_X_self, one_mul, mul_one]
  module

theorem pderiv_disp_energy (j : DIdx K) :
    pderiv ((false, j) : PIdx K) (lagEnergy S) = pderiv (false, j) (potP S) := by
  rw [lagEnergy, map_add, map_add, Derivation.map_smul, pderiv_disp_vsq]
  simp

theorem pderiv_vel_energy (j : DIdx K) :
    pderiv ((true, j) : PIdx K) (lagEnergy S) = X (true, j) := by
  rw [lagEnergy, map_add, map_add, Derivation.map_smul, pderiv_vel_vsq, pderiv_vel_potP,
    smul_smul]
  have : ((1 / 2 : ℝ) : ℂ) * 2 = 1 := by push_cast; ring
  rw [this]
  simp

/-- **The energy identity**: along the Lagrangian flow, `F·∇E = −ν Σ |k|² v²`.  The
incompressibility (penalty) force is a gradient and does no net work. -/
theorem lagFlux_eq : ∑ i, lagDrift S i * pderiv i (lagEnergy S) = lagFlux S := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [lagDrift, pderiv_disp_energy, pderiv_vel_energy]
  rw [← Finset.sum_add_distrib, lagFlux]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [MvPolynomial.smul_eq_C_mul, Complex.ofReal_neg, map_neg]
  ring

/-- **The Liouville identity**: `div F = −ν Σ |k|²`. -/
theorem lagDiv_eq :
    ∑ i, pderiv i (lagDrift S i)
      = ((-(S.nu * ∑ j, lam S j) : ℝ) : ℂ) • (1 : MvPolynomial (PIdx K) ℂ) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [lagDrift, map_sub, map_neg, pderiv_disp_potP, pderiv_vel_rename, sub_zero]
  have h0 : ∀ j : DIdx K,
      pderiv ((false, j) : PIdx K) (X (true, j) : MvPolynomial (PIdx K) ℂ) = 0 := by
    classical
    intro j; simp [pderiv_X]
  simp only [h0, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  push_cast
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.map_smul, pderiv_X_self]
  module

/-! ## 3. Pointwise facts -/

theorem eval_potP (z : PIdx K → ℝ) :
    MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (potP S)
      = ev (fun j => z (dispVar j)) (volPot S.kappa S.kvec) := by
  rw [potP, eval_rename]
  rfl

theorem eval_lagEnergy_re (z : PIdx K → ℝ) :
    (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagEnergy S)).re
      = 1 + (1 / 2) * ∑ j : DIdx K, z (true, j) ^ 2
        + (ev (fun j => z (dispVar j)) (volPot S.kappa S.kvec)).re := by
  rw [lagEnergy, map_add, map_add, eval_potP, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.eval_C, map_sum]
  simp only [map_mul, MvPolynomial.eval_X, map_one, Complex.add_re, Complex.one_re,
    Complex.re_ofReal_mul]
  have hs : (∑ x : DIdx K, ((z (true, x) : ℝ) : ℂ) * ((z (true, x) : ℝ) : ℂ)).re
      = ∑ j : DIdx K, z (true, j) ^ 2 := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hs]

theorem eval_lagFlux_re (z : PIdx K → ℝ) :
    (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagFlux S)).re
      = -(S.nu * ∑ j : DIdx K, lam S j * z (true, j) ^ 2) := by
  rw [lagFlux, map_sum, Complex.re_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, map_mul, MvPolynomial.eval_X,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- `E ≥ 1 + ½|v|²` pointwise. -/
theorem eval_lagEnergy_ge (z : PIdx K → ℝ) :
    1 + (1 / 2) * ∑ j : DIdx K, z (true, j) ^ 2
      ≤ (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagEnergy S)).re := by
  rw [eval_lagEnergy_re]
  have := volPot_eval_nonneg S.kappa_nonneg S.kvec (fun j => z (dispVar j))
  linarith

/-- **The pointwise Lyapunov bound** `|F·∇E| ≤ 2νΛ E`, `Λ = Σ |k|²`. -/
theorem abs_eval_lagFlux_le (z : PIdx K → ℝ) :
    |(MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagFlux S)).re|
      ≤ (2 * S.nu * ∑ j, lam S j)
        * (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagEnergy S)).re := by
  have hE := eval_lagEnergy_ge S z
  rw [eval_lagFlux_re]
  set L := ∑ j, lam S j
  have hL : ∀ j, lam S j ≤ L := fun j =>
    Finset.single_le_sum (fun l _ => lam_nonneg S l) (Finset.mem_univ j)
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun l _ => lam_nonneg S l
  have hs0 : 0 ≤ ∑ j : DIdx K, lam S j * z (true, j) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (lam_nonneg S j) (sq_nonneg _)
  have hsq : 0 ≤ ∑ j : DIdx K, z (true, j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsL : ∑ j : DIdx K, lam S j * z (true, j) ^ 2 ≤ L * ∑ j : DIdx K, z (true, j) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hL j) (sq_nonneg _)
  have hnu := S.nu_nonneg
  rw [abs_neg, abs_of_nonneg (mul_nonneg hnu hs0)]
  have h1 : S.nu * ∑ j : DIdx K, lam S j * z (true, j) ^ 2
      ≤ S.nu * (L * ∑ j : DIdx K, z (true, j) ^ 2) := mul_le_mul_of_nonneg_left hsL hnu
  nlinarith [mul_nonneg hnu hL0]

/-! ## 4. Real coefficients -/

/-- Complex conjugation of the coefficients of a phase-space polynomial. -/
def conjQ (p : MvPolynomial (PIdx K) ℂ) : MvPolynomial (PIdx K) ℂ := map (starRingEnd ℂ) p

theorem conjQ_potP : conjQ (potP S) = potP S := by
  rw [conjQ, potP, map_rename]
  congr 1
  exact conjP_volPot S.kappa S.kvec

omit [Fintype K] in
theorem conjQ_pderiv (i : PIdx K) (p : MvPolynomial (PIdx K) ℂ) :
    conjQ (pderiv i p) = pderiv i (conjQ p) := (MvPolynomial.pderiv_map).symm

theorem conjQ_lagDrift (i : PIdx K) : conjQ (lagDrift S i) = lagDrift S i := by
  obtain ⟨b, j⟩ := i
  cases b
  · simp [lagDrift, conjQ]
  · simp only [lagDrift]
    rw [conjQ, map_sub, map_neg, MvPolynomial.smul_eq_C_mul, map_mul, map_C, map_X,
      Complex.conj_ofReal]
    change _ - conjQ _ = _
    rw [conjQ_pderiv, conjQ_potP]

theorem conjQ_lagEnergy : conjQ (lagEnergy S) = lagEnergy S := by
  rw [lagEnergy, conjQ, map_add, map_add, map_one, MvPolynomial.smul_eq_C_mul, map_mul, map_C,
    Complex.conj_ofReal, map_sum]
  simp only [map_mul, map_X]
  change _ + conjQ _ = _
  rw [conjQ_potP]

/-! ## 5. Transport to `L²(ℝᵈ)` and the Faris–Lavine argument -/

/-- The dimension of the Lagrangian phase space. -/
abbrev lagDim (K : Type*) [Fintype K] : ℕ := Fintype.card (PIdx K)

/-- An enumeration of the phase-space coordinates. -/
def lagEquiv : PIdx K ≃ Fin (lagDim K) := Fintype.equivFin _

/-- The Lagrangian vector field in the coordinates `Fin (lagDim K)`. -/
def lagG (i : Fin (lagDim K)) : MvPolynomial (Fin (lagDim K)) ℂ :=
  rename lagEquiv (lagDrift S (lagEquiv.symm i))

/-- The Lagrangian energy in the coordinates `Fin (lagDim K)`. -/
def lagE : MvPolynomial (Fin (lagDim K)) ℂ := rename lagEquiv (lagEnergy S)

theorem realCoeff_rename {p : MvPolynomial (PIdx K) ℂ} (hp : conjQ p = p) :
    RealCoeff (rename (lagEquiv (K := K)) p) := by
  change map (starRingEnd ℂ) (rename lagEquiv p) = rename lagEquiv p
  rw [map_rename]
  change rename lagEquiv (conjQ p) = _
  rw [hp]

theorem lagG_realCoeff (i : Fin (lagDim K)) : RealCoeff (lagG S i) :=
  realCoeff_rename (conjQ_lagDrift S _)

theorem lagE_realCoeff : RealCoeff (lagE S) := realCoeff_rename (conjQ_lagEnergy S)

/-- The flux identity in the coordinates `Fin (lagDim K)`. -/
theorem lagG_flux :
    ∑ i, lagG S i * pderiv i (lagE S) = rename lagEquiv (lagFlux S) := by
  rw [← lagFlux_eq, map_sum]
  rw [← (lagEquiv (K := K)).symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := pderiv_rename (lagEquiv (K := K)).injective (lagEquiv.symm i) (lagEnergy S)
  rw [Equiv.apply_symm_apply] at h
  rw [lagG, lagE, h, map_mul]

theorem eval_rename_lagEquiv (y : Vd (lagDim K)) (p : MvPolynomial (PIdx K) ℂ) :
    MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (rename lagEquiv p)
      = MvPolynomial.eval (fun i => (((fun j => y (lagEquiv j)) i : ℝ) : ℂ)) p := by
  rw [eval_rename]
  rfl

/-- **The Lagrangian Navier–Stokes Hamiltonian** `H_L = ½ Σ (π F + F π)` on the Gauss–polynomial
core of `L²(ℝ^{PIdx K})`: the Koopman generator of the Lagrangian flow with the determinant
(incompressibility) constraint in momentum-convolution form. -/
def lagKoopmanOp : (polyGaussCore (d := lagDim K)) →ₗ[ℂ] L2d (lagDim K) := kvnGenOp (lagG S)

/-- **The Faris–Lavine comparison operator** `N_L = H_L² + E`. -/
def lagComparison : (polyGaussCore (d := lagDim K)) →ₗ[ℂ] L2d (lagDim K) :=
  lyapunovComparison (lagG S) (lagE S)

theorem lagKoopmanOp_symmetricOn :
    SymmetricOn (polyGaussCore (d := lagDim K)) (lagKoopmanOp S) :=
  kvnGenOp_symmetricOn (lagG_realCoeff S)

theorem lagComparison_symmetricOn :
    SymmetricOn (polyGaussCore (d := lagDim K)) (lagComparison S) :=
  lyapunovComparison_symmetricOn (lagG_realCoeff S) (lagE_realCoeff S)

theorem lagE_eval_ge (y : Vd (lagDim K)) :
    1 ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (lagE S)).re := by
  rw [lagE, eval_rename_lagEquiv]
  have := eval_lagEnergy_ge S (fun j => y (lagEquiv j))
  have hsq : (0 : ℝ) ≤ ∑ j : DIdx K, (y (lagEquiv (true, j))) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

theorem lagFlux_eval_bound (y : Vd (lagDim K)) :
    |(MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (∑ i, lagG S i * pderiv i (lagE S))).re|
      ≤ (2 * S.nu * ∑ j, lam S j)
        * (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (lagE S)).re := by
  rw [lagG_flux, lagE, eval_rename_lagEquiv, eval_rename_lagEquiv]
  exact abs_eval_lagFlux_le S _

/-- **`N_L ≥ 1`.** -/
theorem lagComparison_quadForm_ge (x : polyGaussCore (d := lagDim K)) :
    ‖(x : L2d (lagDim K))‖ ^ 2 ≤ quadForm (lagComparison S) x := by
  rw [lagComparison, lyapunovComparison_quadForm (lagG_realCoeff S)]
  have h1 : ‖(x : L2d (lagDim K))‖ ^ 2 ≤ quadForm (mulCoreOp (lagE S)) x := by
    set p := (coreRepPoly (lagDim K)).equiv.symm x
    rw [norm_core_sq, quadForm_mulCoreOp]
    have := gpair_mul_mono (g := 1) (s := lagE S) (fun y => by
      simpa using lagE_eval_ge S y) p
    simpa using this
  nlinarith [sq_nonneg ‖kvnGenOp (lagG S) x‖]

/-- **`N_L` dominates the generator**: `‖H_L x‖ ≤ ‖N_L x‖ + ‖x‖`. -/
theorem lagComparison_relBound (x : polyGaussCore (d := lagDim K)) :
    ‖lagKoopmanOp S x‖ ≤ ‖lagComparison S x‖ + ‖(x : L2d (lagDim K))‖ :=
  lyapunovComparison_relBound (lagG_realCoeff S)
    (fun y => le_trans zero_le_one (lagE_eval_ge S y)) x

/-- **The exact commutation relation**: `⟪x, i[H_L, N_L] x⟫` is the expectation of the viscous
dissipation `−ν Σ |k|² v²`; the square `H_L²` commutes with `H_L`, and the incompressibility force
drops out by the energy identity. -/
theorem lagComparison_commForm (x : polyGaussCore (d := lagDim K)) :
    commForm (lagKoopmanOp S) (lagComparison S) x
      = (gpair ((coreRepPoly (lagDim K)).equiv.symm x)
          (rename lagEquiv (lagFlux S) * (coreRepPoly (lagDim K)).equiv.symm x)).re := by
  rw [lagKoopmanOp, lagComparison, lyapunovComparison_commForm (lagG_realCoeff S),
    commForm_kvnGen_mul (lagG_realCoeff S) (lagE_realCoeff S)]
  have h := lagG_flux S
  exact congrArg (fun r => (gpair ((coreRepPoly (lagDim K)).equiv.symm x)
    (r * (coreRepPoly (lagDim K)).equiv.symm x)).re) h

/-- **The Faris–Lavine commutator inequality for the Lagrangian generator**:
`|⟪x, i[H_L, N_L] x⟫| ≤ 2νΛ ⟪x, N_L x⟫` with `Λ = Σ |k|²`. -/
theorem lagComparison_commForm_bound (x : polyGaussCore (d := lagDim K)) :
    |commForm (lagKoopmanOp S) (lagComparison S) x|
      ≤ (2 * S.nu * ∑ j, lam S j) * quadForm (lagComparison S) x := by
  rw [lagKoopmanOp, lagComparison, lyapunovComparison_commForm (lagG_realCoeff S)]
  refine le_trans (commForm_kvnGen_mul_bound (lagG_realCoeff S) (lagE_realCoeff S)
    (lagFlux_eval_bound S) x) ?_
  have hc : 0 ≤ 2 * S.nu * ∑ j, lam S j :=
    mul_nonneg (by linarith [S.nu_nonneg]) (Finset.sum_nonneg fun j _ => lam_nonneg S j)
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [lyapunovComparison_quadForm (lagG_realCoeff S)]
  nlinarith [sq_nonneg ‖kvnGenOp (lagG S) x‖]

/-- **Faris–Lavine for Lagrangian Navier–Stokes with the determinant constraint.**  For every
finite set of wave vectors, viscosity `ν ≥ 0` and bulk modulus `κ ≥ 0`: if the comparison
operator `N_L = H_L² + 1 + ½|v|² + V_κ(ξ)` is essentially self-adjoint on the Gauss–polynomial
core, then so is the Lagrangian Navier–Stokes Koopman generator `H_L`. -/
theorem lagKoopman_esa_of_comparison_esa
    (hN : EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagComparison S)) :
    EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagKoopmanOp S) :=
  kvnGen_esa_of_lyapunov (lagG_realCoeff S) (lagE_realCoeff S)
    (mul_nonneg (by linarith [S.nu_nonneg]) (Finset.sum_nonneg fun j _ => lam_nonneg S j))
    (fun y => le_trans zero_le_one (lagE_eval_ge S y)) (lagFlux_eval_bound S) hN

end

end BookProof.NsLagrangianDetFL


