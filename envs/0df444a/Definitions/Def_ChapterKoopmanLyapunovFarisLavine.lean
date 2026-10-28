-- Prove2me | Definitions.Def_ChapterKoopmanLyapunovFarisLavine
-- name    : ChapterKoopmanLyapunovFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T03:04:23.218723+00:00
-- url     : https://prove2.me/theorems/2416d1a8-86e0-4eed-a324-0991a76c9398
-- title:
--   ChapterKoopmanLyapunovFarisLavine
-- statement:
--   ChapterKoopmanLyapunovFarisLavine

import Definitions.Def_ChapterNsNonlinearFarisLavine
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Theorems.Thm_BookProof_YangMillsHermite_derOp_apply
import Definitions.Def_ChapterHermiteRelativeBound


/-!
# Faris–Lavine for the Koopman generator of a polynomial vector field with a Lyapunov energy

For a polynomial vector field `G` on `ℝᵈ` with real coefficients, the Koopman–von Neumann
(Liouville) generator of its flow is the Weyl-ordered first-order operator

```
H_G = ½ Σ_i (π_i G_i + G_i π_i) = −i ( Σ_i G_i ∂_i + ½ div G ),        π_i = −i ∂_i .
```

This module proves, on the Gauss–polynomial core of `L²(ℝᵈ)` and for an **arbitrary** such `G`:

* `kvnGen_polySym`, `kvnGenOp_symmetricOn` — `H_G` is symmetric;
* `kvnGen_apply` — the formula above;
* `kvnGen_comm_mul` — for any polynomial `E`, `[H_G, E] = −i (G·∇E)`: the commutator of the
  generator with a multiplication operator is multiplication by the derivative of `E` along the
  flow;
* **`kvnGen_esa_of_lyapunov`** — the Faris–Lavine criterion with the comparison operator
  `N = H_G² + E`: if `E ≥ 0` is a real polynomial whose derivative along the flow is controlled,
  `|G·∇E| ≤ c E` pointwise, and `N` is essentially self-adjoint on the core, then `H_G` is
  essentially self-adjoint on the core.

This is the abstract form of `NsNonlinearFarisLavine.nsKoopman_esa_of_squareComparison_esa`
(which is the case `G = −νλu + B(u,u)`, `E = 1 + ‖u‖²`); the Lagrangian Navier–Stokes system of
`BookProof.ChapterNsLagrangianDetFarisLavine` is another instance.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.KoopmanLyapunov

open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman

noncomputable section

variable {d : ℕ}

/-- **The Koopman–von Neumann generator** `H_G = ½ Σ_i (π_i G_i + G_i π_i)` of a polynomial
vector field `G`. -/
def kvnGen (G : Fin d → MvPolynomial (Fin d) ℂ) : Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  ∑ i, weylProd (momOp i) (mulOp (G i))

/-- `H_G` is symmetric on the core for a real vector field. -/
theorem kvnGen_polySym {G : Fin d → MvPolynomial (Fin d) ℂ} (hG : ∀ i, RealCoeff (G i)) :
    PolySym (kvnGen G) :=
  polySym_sum fun i _ => weylProd_polySym (momOp_polySym i) (mulOp_polySym (hG i))

/-- `H_G = −i (Σ_i G_i ∂_i + ½ div G)` (on the polynomial factor of a core vector). -/
theorem kvnGen_apply (G : Fin d → MvPolynomial (Fin d) ℂ) (p : MvPolynomial (Fin d) ℂ) :
    kvnGen G p = (-Complex.I) • ((∑ i, G i * derOp i p)
      + ((1 / 2 : ℝ) : ℂ) • ((∑ i, pderiv i (G i)) * p)) := by
  have hsum : kvnGen G p = ∑ i, weylProd (momOp i) (mulOp (G i)) p := by
    rw [kvnGen]; simp
  rw [hsum, Finset.sum_congr rfl fun i _ => weylProd_mom_mul_apply (G i) p i,
    ← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_mul]

/-- **The commutator with a multiplication operator**: `[H_G, E] = −i (G·∇E)`. -/
theorem kvnGen_comm_mul (G : Fin d → MvPolynomial (Fin d) ℂ) (E p : MvPolynomial (Fin d) ℂ) :
    kvnGen G (E * p) - E * kvnGen G p = (-Complex.I) • ((∑ i, G i * pderiv i E) * p) := by
  have hder : ∀ i : Fin d, derOp i (E * p) = pderiv i E * p + E * derOp i p := by
    intro i
    rw [derOp_apply, derOp_apply, pderiv_mul]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  rw [kvnGen_apply, kvnGen_apply]
  have hsum : (∑ i, G i * derOp i (E * p))
      = (∑ i, G i * pderiv i E) * p + E * ∑ i, G i * derOp i p := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hder i]; ring
  rw [hsum]
  simp only [mul_add, mul_smul_comm, smul_add]
  have e1 : (∑ i, pderiv i (G i)) * (E * p) = E * ((∑ i, pderiv i (G i)) * p) := by ring
  rw [e1]
  module

/-! ## On the Gauss–polynomial core -/

/-- `H_G` as a map of the Gauss–polynomial core into itself. -/
def kvnGenCore (G : Fin d → MvPolynomial (Fin d) ℂ) :
    (polyGaussCore (d := d)) →ₗ[ℂ] (polyGaussCore (d := d)) :=
  (coreRepPoly d).op (kvnGen G)

/-- `H_G` on the Gauss–polynomial core of `L²(ℝᵈ)`. -/
def kvnGenOp (G : Fin d → MvPolynomial (Fin d) ℂ) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ kvnGenCore G

/-- Multiplication by a polynomial on the Gauss–polynomial core. -/
def mulCoreOp (E : MvPolynomial (Fin d) ℂ) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ (coreRepPoly d).op (mulOp E)

theorem kvnGenOp_symmetricOn {G : Fin d → MvPolynomial (Fin d) ℂ} (hG : ∀ i, RealCoeff (G i)) :
    SymmetricOn (polyGaussCore (d := d)) (kvnGenOp G) :=
  (coreRepPoly d).symmetricOn_op (kvnGen_polySym hG)

theorem mulCoreOp_symmetricOn {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E) :
    SymmetricOn (polyGaussCore (d := d)) (mulCoreOp E) :=
  (coreRepPoly d).symmetricOn_op (mulOp_polySym hE)

theorem quadForm_mulCoreOp (E : MvPolynomial (Fin d) ℂ) (x : polyGaussCore (d := d)) :
    quadForm (mulCoreOp E) x
      = (gpair ((coreRepPoly d).equiv.symm x) (E * (coreRepPoly d).equiv.symm x)).re := by
  have h1 : mulCoreOp E x = pgLp (E * (coreRepPoly d).equiv.symm x) :=
    (coreRepPoly d).coe_op (mulOp E) x
  rw [quadForm, h1, coe_core_eq, inner_pgLp_pgLp]
  rfl

/-- A multiplication operator with a pointwise non-negative symbol is non-negative. -/
theorem quadForm_mulCoreOp_nonneg {E : MvPolynomial (Fin d) ℂ}
    (hE : ∀ y : Vd d, 0 ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re)
    (x : polyGaussCore (d := d)) : 0 ≤ quadForm (mulCoreOp E) x := by
  rw [quadForm_mulCoreOp]
  have h := gpair_mul_mono (g := 0) (s := E) (fun y => by simpa using hE y)
    ((coreRepPoly d).equiv.symm x)
  simpa [gpair, gaussInt] using h

/-- **The commutator form of `H_G` against a multiplication operator** is the expectation of the
derivative of the symbol along the flow, `G·∇E`. -/
theorem commForm_kvnGen_mul {G : Fin d → MvPolynomial (Fin d) ℂ} (hG : ∀ i, RealCoeff (G i))
    {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E) (x : polyGaussCore (d := d)) :
    commForm (kvnGenOp G) (mulCoreOp E) x
      = (gpair ((coreRepPoly d).equiv.symm x)
          ((∑ i, G i * pderiv i E) * (coreRepPoly d).equiv.symm x)).re := by
  set p := (coreRepPoly d).equiv.symm x with hp
  have hH : (kvnGenOp G) x = pgLp (kvnGen G p) := (coreRepPoly d).coe_op (kvnGen G) x
  have hN : mulCoreOp E x = pgLp (E * p) := (coreRepPoly d).coe_op (mulOp E) x
  have h1 : (inner ℂ ((kvnGenOp G) x) (mulCoreOp E x) : ℂ)
      = gpair p (kvnGen G (E * p)) := by
    rw [hH, hN, ← gpair_eq_inner]
    exact kvnGen_polySym hG p (E * p)
  have h2 : (inner ℂ (mulCoreOp E x) ((kvnGenOp G) x) : ℂ)
      = gpair p (E * kvnGen G p) := by
    rw [hH, hN, ← gpair_eq_inner]
    exact mulOp_polySym hE p (kvnGen G p)
  rw [commForm, h1, h2, ← gpair_sub_right, kvnGen_comm_mul, gpair_smul_right]
  simp [Complex.mul_re, Complex.mul_im]

/-- **The Faris–Lavine commutator inequality from a pointwise Lyapunov bound**: if
`|G·∇E| ≤ c E` at every point, then `|⟪x, i[H_G, E] x⟫| ≤ c ⟪x, E x⟫`. -/
theorem commForm_kvnGen_mul_bound {G : Fin d → MvPolynomial (Fin d) ℂ}
    (hG : ∀ i, RealCoeff (G i)) {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E) {c : ℝ}
    (hflux : ∀ y : Vd d, |(MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
      (∑ i, G i * pderiv i E)).re| ≤ c * (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re)
    (x : polyGaussCore (d := d)) :
    |commForm (kvnGenOp G) (mulCoreOp E) x| ≤ c * quadForm (mulCoreOp E) x := by
  set p := (coreRepPoly d).equiv.symm x with hp
  set Φ := ∑ i, G i * pderiv i E with hΦ
  have hscal : ∀ t : ℝ, (gpair p ((((t : ℝ) : ℂ) • E) * p)).re = t * (gpair p (E * p)).re := by
    intro t
    rw [smul_mul_assoc, gpair_smul_right]
    simp
  have hev : ∀ (t : ℝ) (y : Vd d), (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
      (((t : ℝ) : ℂ) • E)).re = t * (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re := by
    intro t y
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, Complex.re_ofReal_mul]
  rw [commForm_kvnGen_mul hG hE, quadForm_mulCoreOp, abs_le]
  constructor
  · have := gpair_mul_mono (g := ((-c : ℝ) : ℂ) • E) (s := Φ) (fun y => by
      rw [hev]; have := (abs_le.mp (hflux y)).1; linarith) p
    rw [hscal] at this
    linarith
  · have := gpair_mul_mono (g := Φ) (s := ((c : ℝ) : ℂ) • E) (fun y => by
      rw [hev]; exact (abs_le.mp (hflux y)).2) p
    rw [hscal] at this
    linarith

/-- **The comparison operator** `N = H_G² + E` on the Gauss–polynomial core. -/
def lyapunovComparison (G : Fin d → MvPolynomial (Fin d) ℂ) (E : MvPolynomial (Fin d) ℂ) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  kvnGenOp G ∘ₗ kvnGenCore G + mulCoreOp E

theorem lyapunovComparison_symmetricOn {G : Fin d → MvPolynomial (Fin d) ℂ}
    (hG : ∀ i, RealCoeff (G i)) {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E) :
    SymmetricOn (polyGaussCore (d := d)) (lyapunovComparison G E) :=
  symmetricOn_square_comparison (kvnGenCore G) _ (kvnGenOp_symmetricOn hG)
    (mulCoreOp_symmetricOn hE)

/-- `⟪x, N x⟫ = ‖H_G x‖² + ⟪x, E x⟫`. -/
theorem lyapunovComparison_quadForm {G : Fin d → MvPolynomial (Fin d) ℂ}
    (hG : ∀ i, RealCoeff (G i)) (E : MvPolynomial (Fin d) ℂ) (x : polyGaussCore (d := d)) :
    quadForm (lyapunovComparison G E) x = ‖kvnGenOp G x‖ ^ 2 + quadForm (mulCoreOp E) x :=
  quadForm_square_comparison (kvnGenCore G) _ (kvnGenOp_symmetricOn hG) x

/-- `N` dominates the generator: `‖H_G x‖ ≤ ‖N x‖ + ‖x‖`. -/
theorem lyapunovComparison_relBound {G : Fin d → MvPolynomial (Fin d) ℂ}
    (hG : ∀ i, RealCoeff (G i)) {E : MvPolynomial (Fin d) ℂ}
    (hEpos : ∀ y : Vd d, 0 ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re)
    (x : polyGaussCore (d := d)) :
    ‖kvnGenOp G x‖ ≤ ‖lyapunovComparison G E x‖ + ‖(x : L2d d)‖ :=
  norm_le_square_comparison (kvnGenCore G) _ (kvnGenOp_symmetricOn hG)
    (quadForm_mulCoreOp_nonneg hEpos) x

/-- The commutator of `N` with the generator is exactly that of `E`: `H_G` commutes with `H_G²`. -/
theorem lyapunovComparison_commForm {G : Fin d → MvPolynomial (Fin d) ℂ}
    (hG : ∀ i, RealCoeff (G i)) (E : MvPolynomial (Fin d) ℂ) (x : polyGaussCore (d := d)) :
    commForm (kvnGenOp G) (lyapunovComparison G E) x = commForm (kvnGenOp G) (mulCoreOp E) x :=
  commForm_square_comparison (kvnGenCore G) _ (kvnGenOp_symmetricOn hG) x

/-- **Faris–Lavine for Koopman generators with a Lyapunov energy.**  Let `G` be a real polynomial
vector field and `E ≥ 0` a real polynomial with `|G·∇E| ≤ c E` pointwise.  If the comparison
operator `N = H_G² + E` is essentially self-adjoint on the Gauss–polynomial core, then so is the
Koopman generator `H_G`. -/
theorem kvnGen_esa_of_lyapunov {G : Fin d → MvPolynomial (Fin d) ℂ}
    (hG : ∀ i, RealCoeff (G i)) {E : MvPolynomial (Fin d) ℂ} (hE : RealCoeff E) {c : ℝ}
    (hc : 0 ≤ c)
    (hEpos : ∀ y : Vd d, 0 ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re)
    (hflux : ∀ y : Vd d, |(MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
      (∑ i, G i * pderiv i E)).re| ≤ c * (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) E).re)
    (hN : EssentiallySelfAdjointOn (polyGaussCore (d := d)) (lyapunovComparison G E)) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (kvnGenOp G) :=
  essentiallySelfAdjointOn_of_square_comparison polyGaussCore_dense (kvnGenCore G)
    (mulCoreOp E) c (kvnGenOp_symmetricOn hG) (mulCoreOp_symmetricOn hE) hc
    (quadForm_mulCoreOp_nonneg hEpos) (commForm_kvnGen_mul_bound hG hE hflux) hN

end

end BookProof.KoopmanLyapunov


