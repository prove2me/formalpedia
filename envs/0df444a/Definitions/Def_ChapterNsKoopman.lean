-- Prove2me | Definitions.Def_ChapterNsKoopman
-- name    : ChapterNsKoopman
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T02:55:06.248738+00:00
-- url     : https://prove2.me/theorems/d9f2425b-dabc-4a21-a5ce-f004c72d3e03
-- title:
--   Chapter NsKoopman
-- statement:
--   The mainstream Navier-Stokes Koopman-von Neumann Hamiltonian: the exact nonlinear quadratic advection system NsSystem, the Weyl-ordered Hamiltonian kvnPoly, its indefiniteness on the Gauss-polynomial core, and the Leray-energy Faris-Lavine comparison operator with its commutator bound. Source chapters BookProof/ChapterNsKoopman/Part1.lean and Part2.lean.
-- source:
--   BookProof/ChapterNsKoopman/Part1.lean

import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGaussCoreQuadBounds
import Mathlib


-- Toolkit of `BookProof.ChapterYangMillsHermite` that chapter's def bundle does
-- not carry (leaf selection); needed here for `kvnPoly` and the Gauss pairing.
namespace BookProof.YangMillsHermite

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

@[simp] theorem starP_add (p q : MvPolynomial (Fin d) ℂ) :
    starP (p + q) = starP p + starP q := map_add _ _ _

@[simp] theorem starP_mul (p q : MvPolynomial (Fin d) ℂ) :
    starP (p * q) = starP p * starP q := map_mul _ _ _

@[simp] theorem starP_X (j : Fin d) : starP (X j : MvPolynomial (Fin d) ℂ) = X j := by
  simp [starP]

@[simp] theorem starP_C (c : ℂ) : starP (C c : MvPolynomial (Fin d) ℂ) = C ((starRingEnd ℂ) c) := by
  simp [starP]

@[simp] theorem starP_zero : starP (0 : MvPolynomial (Fin d) ℂ) = 0 := map_zero _

theorem starP_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    starP (∑ i ∈ s, f i) = ∑ i ∈ s, starP (f i) := map_sum _ _ _

theorem starP_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    starP (c • p) = ((starRingEnd ℂ) c) • starP p := by
  rw [smul_eq_C_mul, starP_mul, starP_C, smul_eq_C_mul]

theorem starP_real_smul (t : ℝ) (p : MvPolynomial (Fin d) ℂ) :
    starP ((t : ℂ) • p) = (t : ℂ) • starP p := by
  rw [starP_smul, Complex.conj_ofReal]

theorem RealCoeff.add {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p + q) := by
  change starP (p + q) = p + q
  rw [starP_add, show starP p = p from hp, show starP q = q from hq]

theorem RealCoeff.mul {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p * q) := by
  change starP (p * q) = p * q
  rw [starP_mul, show starP p = p from hp, show starP q = q from hq]

theorem RealCoeff.smul {t : ℝ} {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) :
    RealCoeff ((t : ℂ) • p) := by
  rw [RealCoeff, starP_real_smul, hp]

theorem RealCoeff.sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin d) ℂ}
    (h : ∀ i ∈ s, RealCoeff (f i)) : RealCoeff (∑ i ∈ s, f i) := by
  rw [RealCoeff, starP_sum]
  exact Finset.sum_congr rfl h

theorem realCoeff_X (j : Fin d) : RealCoeff (X j : MvPolynomial (Fin d) ℂ) := starP_X j

/-- Conjugation of the coefficients is conjugation of the values at real points. -/
theorem eval_starP (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  rw [starP, eval_map]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- **The inner product of two core vectors is a Gaussian polynomial integral.** -/
theorem inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (starP p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  have hev : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p * q)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
        * MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q := by
    rw [map_mul, eval_starP]
  rw [hx, hev, pgFun, pgFun, gaussWD_eq_sq]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-! ## Polynomial-level operators and Gauss symmetry -/

theorem PolySym.add {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (S + T) := by
  intro p q
  simp only [LinearMap.add_apply, starP_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, hS, hT]

theorem PolySym.real_smul {t : ℝ} {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hT : PolySym T) :
    PolySym (((t : ℂ)) • T) := by
  intro p q
  simp only [LinearMap.smul_apply, starP_real_smul, smul_mul_assoc, mul_smul_comm]
  rw [gaussInt_smul, gaussInt_smul, hT]

theorem PolyAdj.symm_of {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (h : PolyAdj S T) (h' : PolyAdj T S) : PolySym (S + T) := by
  intro p q
  simp only [LinearMap.add_apply, starP_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, h, h']
  ring

/-- The composition of two Gauss-symmetric operators is adjoint to the reversed
composition. -/
theorem PolySym.comp_adj {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolyAdj (S.comp T) (T.comp S) := by
  intro p q
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hS, hT]

/-- **The Weyl-ordered product of two symmetric operators is symmetric** (F.5). -/
theorem weylProd_polySym {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (weylProd S T) :=
  PolySym.real_smul ((hS.comp_adj hT).symm_of (hT.comp_adj hS))

/-! ### Multiplication operators (F.2) -/

@[simp] theorem mulOp_apply (f p : MvPolynomial (Fin d) ℂ) : mulOp f p = f * p := rfl

/-- **Multiplication by a real polynomial is Gauss symmetric.** -/
theorem mulOp_polySym {f : MvPolynomial (Fin d) ℂ} (hf : RealCoeff f) : PolySym (mulOp f) := by
  intro p q
  simp only [mulOp_apply, starP_mul, show starP f = f from hf]
  congr 1
  ring

/-! ### Momentum operators (F.3) -/

theorem derOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    derOp j p = pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p) := rfl

theorem momOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j p = (-Complex.I) • (pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p)) := rfl

theorem starP_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (pderiv j p) = pderiv j (starP p) := (MvPolynomial.pderiv_map).symm

@[simp] theorem starP_neg (p : MvPolynomial (Fin d) ℂ) : starP (-p) = -starP p := map_neg _ _

@[simp] theorem starP_sub (p q : MvPolynomial (Fin d) ℂ) :
    starP (p - q) = starP p - starP q := map_sub _ _ _

theorem gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h := gaussInt_add r (-s)
  rw [show (-s) = (-1 : ℂ) • s by module, gaussInt_smul] at h
  rw [show r - s = r + (-1 : ℂ) • s by module, h]
  ring

/-- The Leibniz rule combined with Gaussian integration by parts:
`∫ (∂_j P) Q e^{-‖x‖²/2} + ∫ P (∂_j Q) e^{-‖x‖²/2} = ∫ x_j P Q e^{-‖x‖²/2}`. -/
theorem gaussInt_leibniz (j : Fin d) (P Q : MvPolynomial (Fin d) ℂ) :
    gaussInt (pderiv j P * Q) + gaussInt (P * pderiv j Q) = gaussInt (X j * (P * Q)) := by
  rw [← gaussInt_pderiv j (P * Q), ← gaussInt_add]
  congr 1
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem starP_momOp (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (momOp j p)
      = Complex.I • (pderiv j (starP p) - ((1 / 2 : ℝ) : ℂ) • (X j * starP p)) := by
  rw [momOp_apply, neg_smul, starP_neg, starP_smul, starP_sub, starP_pderiv, starP_real_smul,
    starP_mul, starP_X, Complex.conj_I, neg_smul, neg_neg]

/-- **The momentum operator is Gauss symmetric** (F.3) — this is exactly the
`d`-dimensional Gaussian integration by parts `gaussInt_pderiv`. -/
theorem momOp_polySym (j : Fin d) : PolySym (momOp (d := d) j) := by
  intro p q
  have hleib := gaussInt_leibniz j (starP p) q
  have e1 : (X j : MvPolynomial (Fin d) ℂ) * starP p * q = X j * (starP p * q) := by ring
  have e2 : starP p * (X j * q) = X j * (starP p * q) := by ring
  have hL : gaussInt (starP (momOp j p) * q)
      = Complex.I * (gaussInt (pderiv j (starP p) * q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [starP_momOp, smul_mul_assoc, gaussInt_smul, sub_mul, gaussInt_sub, smul_mul_assoc,
      gaussInt_smul, e1]
  have hR : gaussInt (starP p * momOp j q)
      = -Complex.I * (gaussInt (starP p * pderiv j q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [momOp_apply, mul_smul_comm, gaussInt_smul, mul_sub, gaussInt_sub, mul_smul_comm,
      gaussInt_smul, e2]
  rw [hL, hR]
  push_cast
  linear_combination Complex.I * hleib

end

end BookProof.YangMillsHermite

-- Clusters missing from the published bundles of their chapters (leaf selection),
-- needed here: `pderiv_hermiteMv` (HermiteProductBasis), the Faris–Lavine criterion
-- (FarisLavineCore), the `CoreRep` transport lemmas (YangMillsHermite Part2), and
-- `gaussInt_re_mono` (GaussCoreQuadBounds).
namespace BookProof.HermiteProductBasis

open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem pderiv_aeval_self (i : Fin d) (q : Polynomial ℂ) :
    pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q)
      = Polynomial.aeval (X i) (Polynomial.derivative q) := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, map_mul,
        Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [mul_comm, mul_assoc, algebraMap_eq]

theorem pderiv_aeval_other {i j : Fin d} (h : j ≠ i) (q : Polynomial ℂ) :
    pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q) = 0 := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [h, algebraMap_eq]

theorem pderiv_hermiteFactor_self (i : Fin d) (n : ℕ) :
    pderiv i (hermiteFactor i n) = (n : ℂ) • hermiteFactor i (n - 1) := by
  cases n with
  | zero => simp [hermiteFactor, hermiteCx_zero]
  | succ m =>
      rw [hermiteFactor, pderiv_aeval_self]
      have h : Polynomial.derivative (hermiteCx (m + 1)) = ((m : ℂ) + 1) • hermiteCx m := by
        have hm := congrArg (Polynomial.map (Int.castRingHom ℂ)) (derivative_hermiteZ m)
        simpa [hermiteCx, Polynomial.derivative_map, Polynomial.smul_eq_C_mul,
          Polynomial.map_mul] using hm
      rw [h]
      simp [hermiteFactor, map_smul]

theorem pderiv_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    pderiv i (hermiteMv a) = ((a i : ℂ)) • hermiteMv (a - Finsupp.single i 1) := by
  classical
  have hrest : ∀ b : Fin d →₀ ℕ, (∀ j : Fin d, j ≠ i → b j = a j) →
      ∏ j ∈ Finset.univ.erase i, hermiteFactor j (b j)
        = ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) :=
    fun b hb => Finset.prod_congr rfl fun j hj => by rw [hb j (Finset.ne_of_mem_erase hj)]
  have hsub : ∀ j : Fin d, j ≠ i → (a - Finsupp.single i 1 : Fin d →₀ ℕ) j = a j := by
    intro j hj; simp [Finsupp.tsub_apply, hj]
  have hsi : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 := by simp [Finsupp.tsub_apply]
  have hzero : pderiv i (∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j)) = 0 := by
    refine Finset.prod_induction _ (fun p => pderiv i p = 0) ?_ (by simp) ?_
    · intro p q hp hq
      rw [Derivation.leibniz, hp, hq]; simp
    · intro j hj
      exact pderiv_aeval_other (Finset.ne_of_mem_erase hj).symm _
  rw [hermiteMv_erase i a, hermiteMv_erase i (a - Finsupp.single i 1), hrest _ hsub, hsi,
    Derivation.leibniz, hzero, pderiv_hermiteFactor_self]
  simp [mul_comm]

end

end BookProof.HermiteProductBasis

namespace BookProof.FarisLavine

open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem inner_im_swap (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]

/-- The expectation of a symmetric operator is real. -/

theorem inner_apply_self_im (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) (x : D) :
    (inner ℂ (T x) (x : F) : ℂ).im = 0 := by
  have h := congrArg Complex.im (hT x x)
  rw [inner_im_swap (T x) (x : F)] at h
  linarith

/-- The quadratic form of a symmetric operator is real. -/

theorem quadForm_im (N : D →ₗ[ℂ] F) (hN : SymmetricOn D N) (x : D) :
    (inner ℂ (x : F) (N x) : ℂ).im = 0 := by
  rw [inner_im_swap (N x) (x : F), inner_apply_self_im N hN x, neg_zero]

/-- The commutator form is `-2 Im ⟪H x, N x⟫`; in particular it is real, and the
Faris–Lavine hypothesis `± i[H, N] ≤ c N` is the bound `|commForm| ≤ c quadForm`. -/

theorem commForm_eq (H N : D →ₗ[ℂ] F) (x : D) :
    commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im := by
  rw [commForm, Complex.mul_re]
  simp [Complex.sub_im, inner_im_swap (H x) (N x)]
  ring

/-! ## The computation of Faris–Lavine

With `N` replaced by `N + 1` (which changes neither the commutator form, since
`⟪H x, x⟫` is real, nor the validity of the bound, since the form of `N` only
grows), the vector `g = (N+1)⁻¹ w` is admissible, and the deficiency identity at
`d i` reads `Im ⟪H g, (N+1) g⟫ = d ⟪g, (N+1) g⟫`.  The commutator bound turns
this into `2|d| t ≤ c t` with `t = ⟪g, (N+1)g⟫ ≥ ‖g‖²`, so `t = 0` as soon as
`2|d| > c`. -/

/-- **The Faris–Lavine estimate.**  Under the hypotheses of Theorem 1 the
deficiency space of `H*` at `d i` is trivial for every real `d` with `2|d| > c`;
equivalently the range of `H + d i` is dense. -/

theorem deficiencyTrivialAt_of_farisLavine
    (H N : D →ₗ[ℂ] F) (c d : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hd : c < 2 * |d|) :
    DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) := by
  intro w hw
  obtain ⟨g, hg⟩ := hNsurj w
  have key := hw g
  rw [← hg, inner_add_right, inner_add_right] at key
  have him := congrArg Complex.im key
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re] at him
  have hBim : (inner ℂ (H g) (g : F) : ℂ).im = 0 := inner_apply_self_im H hH g
  have hPim : (inner ℂ (g : F) (N g) : ℂ).im = 0 := quadForm_im N hN g
  have hQim : (inner ℂ (g : F) (g : F) : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) (g : F)
  have hQre : (inner ℂ (g : F) (g : F) : ℂ).re = ‖(g : F)‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (g : F)
  set t : ℝ := quadForm N g + ‖(g : F)‖ ^ 2 with ht
  have hAim : (inner ℂ (H g) (N g) : ℂ).im = d * t := by
    rw [hBim, hPim, hQim, hQre] at him
    simp only [quadForm, ht]
    linarith [him]
  have htnn : 0 ≤ t := by have := hNpos g; positivity
  have habs : |commForm H N g| = 2 * |d| * t := by
    rw [commForm_eq, hAim, abs_mul, abs_mul, abs_of_nonneg htnn]
    norm_num
    ring
  have h1 : 2 * |d| * t ≤ c * quadForm N g := habs ▸ hcomm g
  have h2 : c * quadForm N g ≤ c * t := by
    have hle : quadForm N g ≤ t := by rw [ht]; nlinarith [sq_nonneg ‖(g : F)‖]
    exact mul_le_mul_of_nonneg_left hle hc
  have ht0 : t = 0 := by nlinarith
  have hgz : (g : F) = 0 := by
    have hnn := hNpos g
    have h4 : ‖(g : F)‖ ^ 2 = 0 := by rw [ht] at ht0; nlinarith [sq_nonneg ‖(g : F)‖]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (g : F)])
  have hg0 : g = 0 := Subtype.ext hgz
  rw [← hg, hg0]
  simp

/-! ## From dense ranges at one conjugate pair to essential self-adjointness -/

/-- The Pythagoras identity for a symmetric operator: `H x` and `d i x` are
orthogonal, because `⟪H x, x⟫` is real. -/

theorem norm_sub_smul_sq (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (d : ℝ) (x : D) :
    ‖H x - ((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = ‖H x‖ ^ 2 + d ^ 2 * ‖(x : F)‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  have h1 : (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ)
      = ((d : ℂ) * Complex.I) * inner ℂ (H x) (x : F) := inner_smul_right _ _ _
  have h2 : RCLike.re (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ) = 0 := by
    rw [h1]; simp [inner_apply_self_im H hH x]
  have h3 : ‖((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = d ^ 2 * ‖(x : F)‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow, sq_abs]
  rw [h2, h3]; ring

/-- Triviality of a deficiency space is the same as weak density of a range, and
for a complete space weak density is density. -/

theorem dense_range_of_deficiencyTrivialAt [CompleteSpace F] (H : D →ₗ[ℂ] F) (w₀ : ℂ)
    (h : DeficiencyTrivialAt D H (starRingEnd ℂ w₀)) :
    Dense (Set.range fun x : D => H x - w₀ • (x : F)) := by
  set K : Submodule ℂ F := LinearMap.range (H - w₀ • D.subtype) with hK
  have hset : (K : Set F) = Set.range fun x : D => H x - w₀ • (x : F) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
  rw [← hset, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  refine h f fun v => ?_
  have hv := (Submodule.mem_orthogonal K f).mp hf (H v - w₀ • (v : F))
    ⟨v, by simp [LinearMap.sub_apply]⟩
  rw [inner_sub_left, inner_smul_left, sub_eq_zero] at hv
  exact hv

/-- **The graph closure of a symmetric operator with dense range hits every
vector.**  If the range of `H - d i` is dense (`d ≠ 0` real), then for every `y`
there are `u, z` in the closure of the graph of `H` — that is, `⟪H v, u⟫ = ⟪v, z⟫`
for all `v` in the domain, with `⟪z, u⟫` still real — such that `z - d i u = y`.

This is the only place where completeness of the space is used.  The proof is
the classical one: the identity `‖H x - d i x‖² = ‖H x‖² + d²‖x‖²` makes both an
approximating sequence and its image Cauchy. -/

theorem exists_weak_graph_limit [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H)
    (d : ℝ) (hd : d ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)))
    (y : F) :
    ∃ u z : F, (∀ v : D, (inner ℂ (H v) u : ℂ) = inner ℂ (v : F) z) ∧
      z - ((d : ℂ) * Complex.I) • u = y ∧ (inner ℂ z u : ℂ).im = 0 := by
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hchoice : ∀ n : ℕ, ∃ x : D, ‖(H x - ((d : ℂ) * Complex.I) • (x : F)) - y‖ < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨p, hp1, x, hx⟩ := Metric.dense_iff.mp hdense y (1 / (n + 1)) hpos
    refine ⟨x, ?_⟩
    rw [← hx] at hp1
    simpa [dist_eq_norm] using hp1
  choose x hx using hchoice
  set Y : ℕ → F := fun n => H (x n) - ((d : ℂ) * Complex.I) • ((x n : F)) with hY
  have hYtend : Filter.Tendsto Y Filter.atTop (nhds y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hx n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hYcauchy : CauchySeq Y := hYtend.cauchySeq
  have hest : ∀ m n : ℕ, |d| * ‖(x m : F) - (x n : F)‖ ≤ ‖Y m - Y n‖ ∧
      ‖H (x m) - H (x n)‖ ≤ ‖Y m - Y n‖ := by
    intro m n
    have hsplit : Y m - Y n = H (x m - x n) - ((d : ℂ) * Complex.I) • ((x m - x n : D) : F) := by
      simp [hY, map_sub, smul_sub]
      abel
    have hsq := norm_sub_smul_sq H hH d (x m - x n)
    rw [← hsplit] at hsq
    have hcoe : ((x m - x n : D) : F) = (x m : F) - (x n : F) := rfl
    rw [hcoe, map_sub] at hsq
    constructor
    · nlinarith [norm_nonneg (Y m - Y n), norm_nonneg ((x m : F) - (x n : F)),
        norm_nonneg (H (x m) - H (x n)), sq_abs d, sq_nonneg (‖H (x m) - H (x n)‖)]
    · nlinarith [norm_nonneg (Y m - Y n), norm_nonneg ((x m : F) - (x n : F)),
        norm_nonneg (H (x m) - H (x n)), sq_nonneg d, sq_nonneg (d * ‖(x m : F) - (x n : F)‖)]
  have hxcauchy : CauchySeq (fun n => (x n : F)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hYcauchy (ε * |d|) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := (hest m n).1
    have h2 := hN m hm n hn
    rw [dist_eq_norm] at h2 ⊢
    nlinarith
  have hHxcauchy : CauchySeq (fun n => H (x n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hYcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := (hest m n).2
    have h2 := hN m hm n hn
    rw [dist_eq_norm] at h2 ⊢
    linarith
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hxcauchy
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hHxcauchy
  refine ⟨u, z, ?_, ?_, ?_⟩
  · intro v
    have h1 : Filter.Tendsto (fun n => (inner ℂ (H v) (x n : F) : ℂ)) Filter.atTop
        (nhds (inner ℂ (H v) u)) := Filter.Tendsto.inner tendsto_const_nhds hu
    have h2 : Filter.Tendsto (fun n => (inner ℂ (v : F) (H (x n)) : ℂ)) Filter.atTop
        (nhds (inner ℂ (v : F) z)) := Filter.Tendsto.inner tendsto_const_nhds hz
    have heq : ∀ n, (inner ℂ (H v) (x n : F) : ℂ) = inner ℂ (v : F) (H (x n)) := fun n => hH v (x n)
    exact tendsto_nhds_unique (by simpa [heq] using h1) h2
  · have hlim : Filter.Tendsto Y Filter.atTop (nhds (z - ((d : ℂ) * Complex.I) • u)) := by
      simpa [hY] using hz.sub (Filter.Tendsto.const_smul hu ((d : ℂ) * Complex.I))
    exact tendsto_nhds_unique hlim hYtend
  · have h1 : Filter.Tendsto (fun n => (inner ℂ (H (x n)) (x n : F) : ℂ)) Filter.atTop
        (nhds (inner ℂ z u)) := Filter.Tendsto.inner hz hu
    have h2 : Filter.Tendsto (fun n => (inner ℂ (H (x n)) (x n : F) : ℂ).im) Filter.atTop
        (nhds ((inner ℂ z u : ℂ).im)) := (Complex.continuous_im.tendsto _).comp h1
    have h3 : ∀ n, (inner ℂ (H (x n)) (x n : F) : ℂ).im = 0 :=
      fun n => inner_apply_self_im H hH (x n)
    simp only [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds

/-- **The basic criterion.**  For a symmetric operator, if the deficiency space
at one point `e i` (`e ≠ 0` real) vanishes and the range of `H - e i` is dense,
then the deficiency space at *every* non-real point vanishes.  This is what turns
the Faris–Lavine estimate — valid only for `2|d| > c` — into essential
self-adjointness. -/

theorem deficiencyTrivialAt_of_dense_range [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (e : ℝ) (he : e ≠ 0) (σ : ℂ) (hσ : σ.im ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F)))
    (hdef : DeficiencyTrivialAt D H ((e : ℂ) * Complex.I)) :
    DeficiencyTrivialAt D H σ := by
  intro w hw
  obtain ⟨u, z, hu, hzy, him⟩ :=
    exists_weak_graph_limit H hH e he hdense ((σ - (e : ℂ) * Complex.I) • w)
  have hzeq : z = ((e : ℂ) * Complex.I) • u + (σ - (e : ℂ) * Complex.I) • w := by
    rw [← hzy]; abel
  have hs : ∀ v : D, (inner ℂ (H v) (w - u) : ℂ)
      = ((e : ℂ) * Complex.I) * inner ℂ (v : F) (w - u) := by
    intro v
    rw [inner_sub_right, inner_sub_right, hw v, hu v, hzeq, inner_add_right,
      inner_smul_right, inner_smul_right]
    ring
  have hwu : w = u := sub_eq_zero.mp (hdef (w - u) hs)
  have hzs : z = σ • w := by rw [hzeq, ← hwu]; module
  have hinner : (inner ℂ z u : ℂ) = starRingEnd ℂ σ * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [hzs, ← hwu, inner_smul_left, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hinner, Complex.mul_im] at him
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.conj_im, mul_zero, zero_add] at him
  have hnorm : ‖w‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd (by linarith [neg_eq_zero.mp h] : σ.im = 0) hσ
    · exact h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])

/-! ## Theorem 1 of Faris–Lavine -/

/-- **Theorem 1 (Faris–Lavine 1974).**  Let `H` be a Hermitian operator and `N`
a positive operator on a common dense domain `D` of a Hilbert space, such that

* `± i[H, N] ≤ c N` as quadratic forms on `D` (hypothesis (ii) of the paper), and
* `N + 1` maps `D` onto the whole space — the one consequence of "`N ≥ 0` is
  self-adjoint" that the argument uses.

Then `H` is essentially self-adjoint: both deficiency spaces of its adjoint
vanish.

Hypothesis (i) of the paper, `𝒟(N) ⊆ 𝒟(H)`, is built into the statement by
giving `H` and `N` the same domain; the conclusion is about the restriction of
`H` to `𝒟(N)`, which is the sharper statement.  Density of `D` is not needed as a
hypothesis: it follows from surjectivity of `N + 1`. -/

theorem essentiallySelfAdjointOn_of_farisLavine [CompleteSpace F]
    (H N : D →ₗ[ℂ] F) (c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    EssentiallySelfAdjointOn D H := by
  set d : ℝ := c + 1 with hdd
  have hdpos : 0 < d := by simp [hdd]; linarith
  have hdabs : |d| = d := abs_of_pos hdpos
  have hd0 : d ≠ 0 := ne_of_gt hdpos
  have hdgt : c < 2 * |d| := by rw [hdabs, hdd]; linarith
  have hplus : DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) :=
    deficiencyTrivialAt_of_farisLavine H N c d hH hN hc hNpos hNsurj hcomm hdgt
  have hminus : DeficiencyTrivialAt D H (((-d : ℝ) : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_farisLavine H N c (-d) hH hN hc hNpos hNsurj hcomm ?_
    rwa [abs_neg]
  have hconj : starRingEnd ℂ ((d : ℂ) * Complex.I) = ((-d : ℝ) : ℂ) * Complex.I := by
    simp
  have hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) :=
    dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (by rw [hconj]; exact hminus)
  exact ⟨deficiencyTrivialAt_of_dense_range H hH d hd0 Complex.I (by simp) hdense hplus,
    deficiencyTrivialAt_of_dense_range H hH d hd0 (-Complex.I) (by simp) hdense hplus⟩

-- square-comparison criterion (ChapterFarisLavineDenseCore), same missing-cluster reason.
theorem norm_le_norm_add_of_pos (N : D →ₗ[ℂ] F)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x) (g : D) :
    ‖N g‖ ^ 2 + ‖(g : F)‖ ^ 2 ≤ ‖N g + (g : F)‖ ^ 2 := by
  have h := norm_add_sq (𝕜 := ℂ) (N g) (g : F)
  have hre : RCLike.re (inner ℂ (N g) (g : F) : ℂ) = quadForm N g := by
    have h1 : (inner ℂ (N g) (g : F) : ℂ) = starRingEnd ℂ (inner ℂ (g : F) (N g)) :=
      (inner_conj_symm (𝕜 := ℂ) (N g) (g : F)).symm
    rw [h1]
    simp only [RCLike.re_to_complex, Complex.conj_re]
    rfl
  rw [hre] at h
  have := hNpos g
  linarith

/-- **The Faris–Lavine estimate on a core.** -/

theorem deficiencyTrivialAt_of_farisLavine_dense [CompleteSpace F]
    (H N : D →ₗ[ℂ] F) (a b c d : ℝ)
    (hD : Dense (D : Set F))
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNdense : Dense (Set.range fun x : D => N x + (x : F)))
    (hrel : ∀ x : D, ‖H x‖ ≤ a * ‖N x‖ + b * ‖(x : F)‖)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hd : c < 2 * |d|) :
    DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) := by
  intro w hw
  -- approximate `w` by `(N + 1) g_n`
  have hex : ∀ n : ℕ, ∃ g : D, ‖N g + (g : F) - w‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, ⟨g, rfl⟩, hy⟩ :=
      hNdense.exists_dist_lt w (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    exact ⟨g, by rw [← dist_eq_norm, dist_comm]; exact hy⟩
  choose g hg using hex
  set M : ℝ := ‖w‖ + 1 with hM
  set e : ℕ → F := fun n => w - (N (g n) + (g n : F)) with he
  have he_le : ∀ n, ‖e n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n; rw [he]; simp only; rw [norm_sub_rev]; exact (hg n).le
  have hinv_le : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hNg_le : ∀ n, ‖N (g n) + (g n : F)‖ ≤ M := by
    intro n
    have h1 : N (g n) + (g n : F) = w - e n := by simp [he]
    rw [h1, hM]
    calc ‖w - e n‖ ≤ ‖w‖ + ‖e n‖ := norm_sub_le _ _
      _ ≤ ‖w‖ + 1 := by linarith [he_le n, hinv_le n]
  have hsq : ∀ n, ‖N (g n)‖ ≤ M ∧ ‖(g n : F)‖ ≤ M := by
    intro n
    have h := norm_le_norm_add_of_pos N hNpos (g n)
    have hM0 : 0 ≤ M := by positivity
    have h2 : ‖N (g n) + (g n : F)‖ ^ 2 ≤ M ^ 2 := by
      have := hNg_le n; gcongr
    constructor
    · nlinarith [norm_nonneg (N (g n)), sq_nonneg ‖(g n : F)‖]
    · nlinarith [norm_nonneg (g n : F), sq_nonneg ‖N (g n)‖]
  set A : ℝ := |a| * M + |b| * M with hA
  have hHg : ∀ n, ‖H (g n)‖ ≤ A := by
    intro n
    have h := hrel (g n)
    have h1 : a * ‖N (g n)‖ ≤ |a| * M :=
      le_trans (le_abs_self _) (by rw [abs_mul, abs_norm]; gcongr; exact (hsq n).1)
    have h2 : b * ‖(g n : F)‖ ≤ |b| * M :=
      le_trans (le_abs_self _) (by rw [abs_mul, abs_norm]; gcongr; exact (hsq n).2)
    linarith
  -- the quantity `t_n = ⟪g_n, (N + 1) g_n⟫`
  set t : ℕ → ℝ := fun n => quadForm N (g n) + ‖(g n : F)‖ ^ 2 with ht
  have hdc : 0 < |d| - c / 2 := by linarith
  have ht_le : ∀ n, t n ≤ (A + |d| * M) * (1 / ((n : ℝ) + 1)) / (|d| - c / 2) := by
    intro n
    set gn := g n
    have key := hw gn
    have hw' : w = N gn + (gn : F) + e n := by simp [he, gn]
    rw [hw', inner_add_right, inner_add_right, inner_add_right, inner_add_right] at key
    -- imaginary parts
    have him := congrArg Complex.im key
    have hBim : (inner ℂ (H gn) (gn : F) : ℂ).im = 0 := inner_apply_self_im H hH gn
    have hPim : (inner ℂ (gn : F) (N gn) : ℂ).im = 0 := quadForm_im N hN gn
    have hQim : (inner ℂ (gn : F) (gn : F) : ℂ).im = 0 := by
      simpa using inner_self_im (𝕜 := ℂ) (gn : F)
    have hQre : (inner ℂ (gn : F) (gn : F) : ℂ).re = ‖(gn : F)‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (gn : F)
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re, hBim, hPim, hQim,
      hQre] at him
    -- error terms
    have hE1 : |(inner ℂ (H gn) (e n) : ℂ).im| ≤ A * (1 / ((n : ℝ) + 1)) := by
      calc |(inner ℂ (H gn) (e n) : ℂ).im| ≤ ‖(inner ℂ (H gn) (e n) : ℂ)‖ :=
            Complex.abs_im_le_norm _
        _ ≤ ‖H gn‖ * ‖e n‖ := norm_inner_le_norm _ _
        _ ≤ A * (1 / ((n : ℝ) + 1)) :=
            mul_le_mul (hHg n) (he_le n) (norm_nonneg _) (le_trans (norm_nonneg _) (hHg n))
    have hE2 : |(inner ℂ (gn : F) (e n) : ℂ).re| ≤ M * (1 / ((n : ℝ) + 1)) := by
      calc |(inner ℂ (gn : F) (e n) : ℂ).re| ≤ ‖(inner ℂ (gn : F) (e n) : ℂ)‖ :=
            Complex.abs_re_le_norm _
        _ ≤ ‖(gn : F)‖ * ‖e n‖ := norm_inner_le_norm _ _
        _ ≤ M * (1 / ((n : ℝ) + 1)) :=
            mul_le_mul (hsq n).2 (he_le n) (norm_nonneg _) (by positivity)
    have hcf : |commForm H N gn| = 2 * |(inner ℂ (H gn) (N gn) : ℂ).im| := by
      rw [commForm_eq, abs_mul]; norm_num
    have hc1 := hcomm gn
    rw [hcf] at hc1
    have hq : quadForm N gn = (inner ℂ (gn : F) (N gn) : ℂ).re := rfl
    have htn : t n = (inner ℂ (gn : F) (N gn) : ℂ).re + ‖(gn : F)‖ ^ 2 := rfl
    have hqle : quadForm N gn ≤ t n := by
      rw [htn, ← hq]; nlinarith [sq_nonneg ‖(gn : F)‖]
    have hc0 : 0 ≤ c := hc
    -- `d t = Im⟪H g, N g⟫ + Im⟪H g, e⟫ - d Re⟪g, e⟫`
    have hdt : d * t n = (inner ℂ (H gn) (N gn) : ℂ).im + (inner ℂ (H gn) (e n) : ℂ).im
        - d * (inner ℂ (gn : F) (e n) : ℂ).re := by
      rw [htn]; linarith
    have habs : |d| * t n ≤ c / 2 * t n + (A + |d| * M) * (1 / ((n : ℝ) + 1)) := by
      have htnn : 0 ≤ t n := by have := hNpos gn; positivity
      have h1 : |d * t n| = |d| * t n := by rw [abs_mul, abs_of_nonneg htnn]
      have h2 : |d * t n| ≤ |(inner ℂ (H gn) (N gn) : ℂ).im|
          + |(inner ℂ (H gn) (e n) : ℂ).im| + |d| * |(inner ℂ (gn : F) (e n) : ℂ).re| := by
        rw [hdt, ← abs_mul]
        exact le_trans (abs_sub _ _) (by gcongr; exact abs_add_le _ _)
      have h3 : |(inner ℂ (H gn) (N gn) : ℂ).im| ≤ c / 2 * t n := by
        have : 2 * |(inner ℂ (H gn) (N gn) : ℂ).im| ≤ c * t n :=
          le_trans hc1 (mul_le_mul_of_nonneg_left hqle hc0)
        linarith
      have h4 : |d| * |(inner ℂ (gn : F) (e n) : ℂ).re| ≤ |d| * (M * (1 / ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hE2 (abs_nonneg d)
      nlinarith
    rw [le_div_iff₀ hdc]
    nlinarith
  -- `g_n → 0`
  have hg0 : Tendsto (fun n => (g n : F)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hK : Tendsto (fun n : ℕ => (A + |d| * M) * (1 / ((n : ℝ) + 1)) / (|d| - c / 2))
        atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (A + |d| * M)
      simpa using this.div_const (|d| - c / 2)
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt
        ((A + |d| * M) * (1 / ((n : ℝ) + 1)) / (|d| - c / 2))) atTop (𝓝 0) := by
      simpa [Function.comp] using! (Real.continuous_sqrt.tendsto 0).comp hK
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsqrt
    apply Real.le_sqrt_of_sq_le
    have h1 := ht_le n
    have h2 := hNpos (g n)
    have : ‖(g n : F)‖ ^ 2 ≤ t n := by simp only [ht]; linarith
    linarith
  -- `(N + 1) g_n → w`
  have hNw : Tendsto (fun n => N (g n) + (g n : F)) atTop (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hg n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- `w ⊥ D`
  have horth : ∀ v : D, (inner ℂ w (v : F) : ℂ) = 0 := by
    intro v
    have h1 : Tendsto (fun n => (inner ℂ (N (g n) + (g n : F)) (v : F) : ℂ)) atTop
        (𝓝 (inner ℂ w (v : F))) :=
      ((continuous_inner.comp
        (Continuous.prodMk continuous_id continuous_const)).tendsto w).comp hNw
    have h2 : (fun n => (inner ℂ (N (g n) + (g n : F)) (v : F) : ℂ))
        = fun n => (inner ℂ (g n : F) (N v + (v : F)) : ℂ) := by
      funext n
      rw [inner_add_left, inner_add_right, hN (g n) v]
    have h3 : Tendsto (fun n => (inner ℂ (g n : F) (N v + (v : F)) : ℂ)) atTop
        (𝓝 (inner ℂ (0 : F) (N v + (v : F)))) :=
      ((continuous_inner.comp
        (Continuous.prodMk continuous_id continuous_const)).tendsto 0).comp hg0
    rw [inner_zero_left] at h3
    rw [h2] at h1
    exact tendsto_nhds_unique h1 h3
  -- `D` dense, so `w = 0`
  have hclosed : IsClosed {x : F | (inner ℂ w x : ℂ) = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : (D : Set F) ⊆ {x : F | (inner ℂ w x : ℂ) = 0} := fun x hx => horth ⟨x, hx⟩
  have hall : closure (D : Set F) ⊆ {x : F | (inner ℂ w x : ℂ) = 0} :=
    closure_minimal hsub hclosed
  rw [hD.closure_eq] at hall
  have hww : (inner ℂ w w : ℂ) = 0 := hall (Set.mem_univ w)
  exact inner_self_eq_zero.mp hww

/-- **Faris–Lavine on a core** (Corollary 1.1 of the paper, with every hypothesis stated on the
core only).  `D` dense, `H` and `N` symmetric on `D`, `N ≥ 0` with `(N + 1) D` dense (for a
positive symmetric operator this is essential self-adjointness of `N` on `D`), `H` relatively
bounded by `N` and `|⟪x, i[H, N] x⟫| ≤ c ⟪x, N x⟫` on `D`.  Then `H` is essentially
self-adjoint on `D`. -/

theorem essentiallySelfAdjointOn_of_farisLavine_dense [CompleteSpace F]
    (H N : D →ₗ[ℂ] F) (a b c : ℝ)
    (hD : Dense (D : Set F))
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNdense : Dense (Set.range fun x : D => N x + (x : F)))
    (hrel : ∀ x : D, ‖H x‖ ≤ a * ‖N x‖ + b * ‖(x : F)‖)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    EssentiallySelfAdjointOn D H := by
  set d : ℝ := c + 1 with hdd
  have hdpos : 0 < d := by simp [hdd]; linarith
  have hdabs : |d| = d := abs_of_pos hdpos
  have hd0 : d ≠ 0 := ne_of_gt hdpos
  have hdgt : c < 2 * |d| := by rw [hdabs, hdd]; linarith
  have hplus : DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) :=
    deficiencyTrivialAt_of_farisLavine_dense H N a b c d hD hH hN hc hNpos hNdense hrel hcomm hdgt
  have hminus : DeficiencyTrivialAt D H (((-d : ℝ) : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_farisLavine_dense H N a b c (-d) hD hH hN hc hNpos hNdense hrel
      hcomm ?_
    rwa [abs_neg]
  have hconj : starRingEnd ℂ ((d : ℂ) * Complex.I) = ((-d : ℝ) : ℂ) * Complex.I := by
    simp
  have hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) :=
    dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (by rw [hconj]; exact hminus)
  exact ⟨deficiencyTrivialAt_of_dense_range H hH d hd0 Complex.I (by simp) hdense hplus,
    deficiencyTrivialAt_of_dense_range H hH d hd0 (-Complex.I) (by simp) hdense hplus⟩

/-! ## Essential self-adjointness of a positive `N` gives dense range of `N + 1` -/

/-- For a **positive** symmetric operator, essential self-adjointness on `D` implies that
`(N + 1) D` is dense.  (So the density hypothesis of
`essentiallySelfAdjointOn_of_farisLavine_dense` is exactly essential self-adjointness of `N`.) -/

theorem dense_range_add_one_of_esa_of_pos [CompleteSpace F] (N : D →ₗ[ℂ] F)
    (hN : SymmetricOn D N) (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hesa : EssentiallySelfAdjointOn D N) :
    Dense (Set.range fun x : D => N x + (x : F)) := by
  have hI : Dense (Set.range fun x : D => N x - (-Complex.I) • (x : F)) :=
    dense_range_of_deficiencyTrivialAt N (-Complex.I) (by simpa using hesa.1)
  -- `range (N + 1)` is a submodule; show its orthogonal complement is trivial
  set K : Submodule ℂ F := LinearMap.range (N + D.subtype) with hK
  have hset : (K : Set F) = Set.range fun x : D => N x + (x : F) := by
    ext u; constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp⟩
  rw [← hset, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_orthogonal] at hw
  have hw' : ∀ v : D, (inner ℂ (N v + (v : F)) w : ℂ) = 0 := fun v =>
    hw _ ⟨v, by simp⟩
  -- approximate `w` by `(N + i) v_n`
  have hex : ∀ n : ℕ, ∃ v : D, ‖N v + Complex.I • (v : F) - w‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, ⟨v, rfl⟩, hy⟩ :=
      hI.exists_dist_lt w (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    refine ⟨v, ?_⟩
    rw [← dist_eq_norm, dist_comm]
    simpa [sub_neg_eq_add] using hy
  choose v hv using hex
  set e : ℕ → F := fun n => w - (N (v n) + Complex.I • (v n : F)) with he
  have he_le : ∀ n, ‖e n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n; simp only [he]; rw [norm_sub_rev]; exact (hv n).le
  have hinv_le : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set M : ℝ := ‖w‖ + 1 with hM
  have hbd : ∀ n, ‖N (v n)‖ ≤ M ∧ ‖(v n : F)‖ ≤ M := by
    intro n
    have hnorm : ‖N (v n) + Complex.I • (v n : F)‖ ^ 2 = ‖N (v n)‖ ^ 2 + ‖(v n : F)‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
      have him : (inner ℂ (N (v n)) (v n : F) : ℂ).im = 0 := inner_apply_self_im N hN (v n)
      simp [him]
    have h1 : N (v n) + Complex.I • (v n : F) = w - e n := by simp [he]
    have h2 : ‖N (v n) + Complex.I • (v n : F)‖ ≤ M := by
      rw [h1]
      calc ‖w - e n‖ ≤ ‖w‖ + ‖e n‖ := norm_sub_le _ _
        _ ≤ M := by rw [hM]; linarith [he_le n, hinv_le n]
    have hM0 : 0 ≤ M := by positivity
    have h3 : ‖N (v n)‖ ^ 2 + ‖(v n : F)‖ ^ 2 ≤ M ^ 2 := by
      rw [← hnorm]; gcongr
    constructor
    · nlinarith [norm_nonneg (N (v n)), sq_nonneg ‖(v n : F)‖]
    · nlinarith [norm_nonneg (v n : F), sq_nonneg ‖N (v n)‖]
  -- the key identity `0 = ⟪(N+1) v, (N+i) v⟫ + ⟪(N+1) v, e⟫`
  have hkey : ∀ n, ‖N (v n)‖ ^ 2 + ‖(v n : F)‖ ^ 2 ≤ 4 * M * (1 / ((n : ℝ) + 1)) := by
    intro n
    set x := v n
    have h0 := hw' x
    have hw2 : w = N x + Complex.I • (x : F) + e n := by simp [he, x]
    rw [hw2, inner_add_right, inner_add_right, inner_smul_right, inner_add_left,
      inner_add_left] at h0
    have hq : (inner ℂ (x : F) (N x) : ℂ).im = 0 := quadForm_im N hN x
    have hq' : (inner ℂ (N x) (x : F) : ℂ).im = 0 := inner_apply_self_im N hN x
    have hNN : (inner ℂ (N x) (N x) : ℂ) = ((‖N x‖ ^ 2 : ℝ) : ℂ) := by
      simp
    have hxx : (inner ℂ (x : F) (x : F) : ℂ) = ((‖(x : F)‖ ^ 2 : ℝ) : ℂ) := by
      simp
    have hqq : (inner ℂ (x : F) (N x) : ℂ).re = (inner ℂ (N x) (x : F) : ℂ).re := by
      rw [← inner_conj_symm (𝕜 := ℂ) (N x) (x : F), Complex.conj_re]
    set r : ℂ := inner ℂ (N x + (x : F)) (e n) with hr
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    rw [hNN, hxx] at hre him
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
      hq, hq'] at hre him
    have hpos : 0 ≤ (inner ℂ (N x) (x : F) : ℂ).re := by
      have := hNpos x; simp only [quadForm] at this; linarith
    have hE : ‖r‖ ≤ 2 * M * (1 / ((n : ℝ) + 1)) := by
      calc ‖r‖ ≤ ‖N x + (x : F)‖ * ‖e n‖ := norm_inner_le_norm _ _
        _ ≤ (2 * M) * (1 / ((n : ℝ) + 1)) := by
            apply mul_le_mul _ (he_le n) (norm_nonneg _) (by positivity)
            calc ‖N x + (x : F)‖ ≤ ‖N x‖ + ‖(x : F)‖ := norm_add_le _ _
              _ ≤ 2 * M := by linarith [(hbd n).1, (hbd n).2]
    have h1 := (abs_le.mp (le_trans (Complex.abs_re_le_norm r) hE)).1
    have h2 := (abs_le.mp (le_trans (Complex.abs_im_le_norm r) hE)).1
    nlinarith
  -- hence `(N + i) v_n → 0`, and also `→ w`
  have hlim0 : Tendsto (fun n => N (v n) + Complex.I • (v n : F)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hK : Tendsto (fun n : ℕ => Real.sqrt (4 * M * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 * M))
      simpa [Function.comp] using! (Real.continuous_sqrt.tendsto 0).comp (by simpa using this)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hK
    apply Real.le_sqrt_of_sq_le
    have hnorm : ‖N (v n) + Complex.I • (v n : F)‖ ^ 2 = ‖N (v n)‖ ^ 2 + ‖(v n : F)‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
      have him : (inner ℂ (N (v n)) (v n : F) : ℂ).im = 0 := inner_apply_self_im N hN (v n)
      simp [him]
    rw [hnorm]; exact hkey n
  have hlimw : Tendsto (fun n => N (v n) + Complex.I • (v n : F)) atTop (𝓝 w) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hv n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_nhds_unique hlimw hlim0

/-! ## The square comparison `N = H² + E` -/

/-- The quadratic form of the square comparison: `⟪x, (H² + E) x⟫ = ‖H x‖² + ⟪x, E x⟫`. -/

theorem quadForm_square_comparison (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (x : D) :
    quadForm ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x
      = ‖(D.subtype ∘ₗ H₀) x‖ ^ 2 + quadForm E x := by
  have h1 : (inner ℂ (x : F) ((D.subtype ∘ₗ H₀) (H₀ x)) : ℂ)
      = inner ℂ ((D.subtype ∘ₗ H₀) x) ((D.subtype ∘ₗ H₀) x) := by
    rw [← hH x (H₀ x)]; rfl
  have h2 : (inner ℂ ((D.subtype ∘ₗ H₀) x) ((D.subtype ∘ₗ H₀) x) : ℂ).re
      = ‖(D.subtype ∘ₗ H₀) x‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((D.subtype ∘ₗ H₀) x)
  have h3 : ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x = (D.subtype ∘ₗ H₀) (H₀ x) + E x := rfl
  rw [quadForm, h3, inner_add_right, Complex.add_re, h1, h2]
  rfl

/-- **The exact commutation relation of the square comparison**: `H` commutes with `H²`, so
`⟪x, i[H, H² + E] x⟫ = ⟪x, i[H, E] x⟫`. -/

theorem commForm_square_comparison (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (x : D) :
    commForm (D.subtype ∘ₗ H₀) ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x
      = commForm (D.subtype ∘ₗ H₀) E x := by
  have hsq : (inner ℂ ((D.subtype ∘ₗ H₀) x) ((D.subtype ∘ₗ H₀) (H₀ x)) : ℂ).im = 0 :=
    quadForm_im (D.subtype ∘ₗ H₀) hH (H₀ x)
  have h3 : ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x = (D.subtype ∘ₗ H₀) (H₀ x) + E x := rfl
  rw [commForm_eq, commForm_eq, h3, inner_add_right, Complex.add_im, hsq, zero_add]

/-- The square comparison `H² + E` is symmetric. -/

theorem symmetricOn_square_comparison (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (hE : SymmetricOn D E) :
    SymmetricOn D ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) := by
  intro x y
  have h3 : ∀ z : D, ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) z = (D.subtype ∘ₗ H₀) (H₀ z) + E z :=
    fun z => rfl
  rw [h3, h3, inner_add_left, inner_add_right, hE x y, hH (H₀ x) y, ← hH x (H₀ y)]
  rfl

/-- The relative bound of the square comparison: `‖H x‖ ≤ ‖(H² + E) x‖ + ‖x‖` when `E ≥ 0`. -/

theorem norm_le_square_comparison (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (hEpos : ∀ x : D, 0 ≤ quadForm E x) (x : D) :
    ‖(D.subtype ∘ₗ H₀) x‖ ≤ ‖((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E) x‖ + ‖(x : F)‖ := by
  set N := (D.subtype ∘ₗ H₀) ∘ₗ H₀ + E
  have h1 : ‖(D.subtype ∘ₗ H₀) x‖ ^ 2 ≤ quadForm N x := by
    rw [quadForm_square_comparison H₀ E hH]; linarith [hEpos x]
  have h2 : quadForm N x ≤ ‖(x : F)‖ * ‖N x‖ := by
    calc quadForm N x ≤ ‖(inner ℂ (x : F) (N x) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖(x : F)‖ * ‖N x‖ := norm_inner_le_norm _ _
  have h3 : ‖(D.subtype ∘ₗ H₀) x‖ ^ 2 ≤ (‖N x‖ + ‖(x : F)‖) ^ 2 := by
    nlinarith [norm_nonneg (N x), norm_nonneg (x : F)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-- **Faris–Lavine with the comparison operator `N = H² + E`.**  Let `H = ι ∘ H₀` be symmetric
on `D` and map `D` into itself (`H₀ : D → D`), and let `E ≥ 0` be symmetric on `D` with
`|⟪x, i[H, E] x⟫| ≤ c ⟪x, E x⟫`.  Put `N = H² + E`.  Then

* `⟪x, N x⟫ = ‖H x‖² + ⟪x, E x⟫ ≥ 0`,
* `‖H x‖ ≤ ‖N x‖ + ‖x‖`,
* `⟪x, i[H, N] x⟫ = ⟪x, i[H, E] x⟫` — the square commutes with `H` exactly,

so the Faris–Lavine hypotheses hold with the same constant `c`, and `H` is essentially
self-adjoint on `D` as soon as `N` is. -/

theorem essentiallySelfAdjointOn_of_square_comparison [CompleteSpace F]
    (hD : Dense (D : Set F)) (H₀ : D →ₗ[ℂ] D) (E : D →ₗ[ℂ] F) (c : ℝ)
    (hH : SymmetricOn D (D.subtype ∘ₗ H₀)) (hE : SymmetricOn D E) (hc : 0 ≤ c)
    (hEpos : ∀ x : D, 0 ≤ quadForm E x)
    (hcomm : ∀ x : D, |commForm (D.subtype ∘ₗ H₀) E x| ≤ c * quadForm E x)
    (hNesa : EssentiallySelfAdjointOn D ((D.subtype ∘ₗ H₀) ∘ₗ H₀ + E)) :
    EssentiallySelfAdjointOn D (D.subtype ∘ₗ H₀) := by
  set H : D →ₗ[ℂ] F := D.subtype ∘ₗ H₀ with hHdef
  set N : D →ₗ[ℂ] F := H ∘ₗ H₀ + E with hNdef
  have hHx : ∀ x : D, H x = ((H₀ x : D) : F) := fun x => rfl
  have hNx : ∀ x : D, N x = H (H₀ x) + E x := fun x => rfl
  have hqN : ∀ x : D, quadForm N x = ‖H x‖ ^ 2 + quadForm E x :=
    quadForm_square_comparison H₀ E hH
  have hN : SymmetricOn D N := symmetricOn_square_comparison H₀ E hH hE
  have hNpos : ∀ x : D, 0 ≤ quadForm N x := fun x => by
    rw [hqN]; have := hEpos x; positivity
  -- the relative bound
  have hrel : ∀ x : D, ‖H x‖ ≤ 1 * ‖N x‖ + 1 * ‖(x : F)‖ := fun x => by
    simp only [hHx, hNx, one_mul]
    exact norm_le_square_comparison H₀ E hH hEpos x
  -- the commutator: the square drops out
  have hcommN : ∀ x : D, |commForm H N x| ≤ c * quadForm N x := by
    intro x
    have hcf : commForm H N x = commForm H E x := commForm_square_comparison H₀ E hH x
    rw [hcf]
    have hle : quadForm E x ≤ quadForm N x := by rw [hqN]; nlinarith [sq_nonneg ‖H x‖]
    exact le_trans (hcomm x) (mul_le_mul_of_nonneg_left hle hc)
  exact essentiallySelfAdjointOn_of_farisLavine_dense H N 1 1 c hD hH hN hc hNpos
    (dense_range_add_one_of_esa_of_pos N hN hNpos hNesa) hrel hcommN

end BookProof.FarisLavine

namespace BookProof.YangMillsHermite

open MvPolynomial BookProof.HermiteProductCore BookProof.FarisLavine

variable {d : ℕ}
variable {D : Submodule ℂ (L2d d)}

theorem CoreRep.op_apply (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (x : D) :
    Φ.op T x = Φ.equiv (T (Φ.equiv.symm x)) := rfl

theorem CoreRep.coe_op (Φ : CoreRep d D) (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (x : D) :
    ((Φ.op T x : D) : L2d d) = pgLp (T (Φ.equiv.symm x)) := by
  rw [CoreRep.op_apply, Φ.coe_equiv]

theorem CoreRep.coe_symm (Φ : CoreRep d D) (x : D) : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x) := by
  rw [← Φ.coe_equiv (Φ.equiv.symm x), LinearEquiv.apply_symm_apply]

set_option maxHeartbeats 1000000 in
-- the `L²` coercions in the rewrite chain need more than the default budget
/-- **Gauss-symmetric polynomial operators transport to symmetric operators on the
core.** -/

theorem CoreRep.symmetricOn_op (Φ : CoreRep d D) {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hT : PolySym T) : SymmetricOn D (D.subtype.comp (Φ.op T)) := by
  intro x y
  have hx : ((D.subtype.comp (Φ.op T)) x) = pgLp (T (Φ.equiv.symm x)) := Φ.coe_op T x
  have hy : ((D.subtype.comp (Φ.op T)) y) = pgLp (T (Φ.equiv.symm y)) := Φ.coe_op T y
  have hcx : ((x : D) : L2d d) = pgLp (Φ.equiv.symm x) := Φ.coe_symm x
  have hcy : ((y : D) : L2d d) = pgLp (Φ.equiv.symm y) := Φ.coe_symm y
  have e1 := inner_pgLp_pgLp (T (Φ.equiv.symm x)) (Φ.equiv.symm y)
  have e2 := inner_pgLp_pgLp (Φ.equiv.symm x) (T (Φ.equiv.symm y))
  rw [hx, hy, hcx, hcy, e1, e2]
  exact hT _ _

end BookProof.YangMillsHermite

namespace BookProof.GaussCoreQuadBounds

open Finset MvPolynomial
open BookProof.HermiteProductCore

noncomputable section

variable {D : ℕ}

theorem gaussInt_re (r : MvPolynomial (Fin D) ℂ) :
    (gaussInt r).re
      = ∫ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re * gaussWD x := by
  rw [gaussInt, ← Complex.reCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_gwFun r)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.mul_re]

/-- Monotonicity of the Gaussian integral on real parts. -/

theorem gaussInt_re_mono {r s : MvPolynomial (Fin D) ℂ}
    (h : ∀ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re
      ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) s).re) :
    (gaussInt r).re ≤ (gaussInt s).re := by
  have hint : ∀ t : MvPolynomial (Fin D) ℂ, MeasureTheory.Integrable
      (fun x : Vd D => (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) t).re * gaussWD x) := by
    intro t
    refine ((integrable_gwFun t).re).congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  rw [gaussInt_re, gaussInt_re]
  refine MeasureTheory.integral_mono (hint r) (hint s) fun x => ?_
  have hw : (0 : ℝ) ≤ gaussWD x := le_of_lt (Real.exp_pos _)
  exact mul_le_mul_of_nonneg_right (h x) hw

end

end BookProof.GaussCoreQuadBounds


/-!
# The mainstream Navier–Stokes Hamiltonian and why it is not bounded below

The Navier–Stokes system, written in the functional (Leray–Galerkin) form in which it is
always stated,

```
u̇ = − ν A u + B(u, u),      ⟨u, B(u, u)⟩ = 0,      div_u B = 0,
```

is a *first-order* evolution, and its Hamiltonian — the generator of the flow it induces on
wave functions, i.e. the Koopman–von Neumann (Liouville) generator

```
H_NS = ½ Σ_m (π_m F_m + F_m π_m) = −i ( Σ_m F_m ∂_m + ½ div F ),      F = − ν A u + B(u,u),
```

— is symmetric but **indefinite**: it is bounded neither below nor above.  Consequently it can
never be the *positive* comparison operator `N` of the Faris–Lavine criterion, and the shortcut
`H = N`, `c = 0` used elsewhere in this project for the auxiliary sum-of-squares operator is not
available for it.  This module proves exactly that, on the Gauss–polynomial core of `L²(ℝᵈ)`:

* `NsSystem` — the data of the mainstream system: viscosity `ν ≥ 0`, the (diagonalized) Stokes
  eigenvalues `λ_i = |k_i|² ≥ 0`, and the exact quadratic advection
  `B_i(u,u) = Σ_{j,k} b_{ijk}u_ju_k`
  subject to the two structural identities of incompressible Navier–Stokes — Leray's energy
  identity `Σ_i u_i B_i(u,u) = 0` (the advection and the pressure gradient do no work) and the
  phase-space Liouville identity `Σ_i ∂_i B_i = 0`;
* `kvnPoly` — the Hamiltonian `H_NS` above, Weyl-ordered, with the *exact* nonlinearity: no
  square of a residual, no linearization, no perturbative splitting;
* `kvnPoly_polySym` — it is symmetric on the core;
* `quadP_starP` — the antiunitary conjugation `C ψ = ψ̄` satisfies `C H_NS C = − H_NS`, so the
  numerical range of `H_NS` is symmetric about `0`: bounded below iff bounded above;
* `gpair_hermite_kvn` — the exact matrix element of `H_NS` between the one-mode Hermite states
  `|n⟩` and `|n+2⟩`.  The advection drops out of it by a parity selection rule
  (`gpair_parity`), so the element is the viscous one and grows like `n`;
* `kvn_quadP_not_bounded_below`, `nsKoopmanOp_not_bounded_below` — **the headline**: for
  `ν > 0` and one positive Stokes eigenvalue, the quadratic form of `H_NS` on the core satisfies
  `inf ⟪x, H_NS x⟫ / ‖x‖² = −∞`.  In particular `H_NS` is not positive
  (`nsKoopmanOp_not_positive`) and is not a Faris–Lavine comparison operator for itself.

`BookProof.ChapterNsKoopman.Part2` supplies the replacement comparison operator and the
Faris–Lavine commutator bound that the mainstream Hamiltonian does satisfy.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsKoopman

open MvPolynomial
open BookProof.HermiteCore BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.GaussCoreQuadBounds

noncomputable section

variable {d : ℕ}

/-! ## 1. The Gauss pairing of two core vectors -/

/-- The Gauss pairing `⟪p, q⟫ = ∫ p̄ q e^{−‖x‖²/2}`: the `L²` inner product of the two core
vectors `p·e^{−‖x‖²/4}` and `q·e^{−‖x‖²/4}`. -/
def gpair (p q : MvPolynomial (Fin d) ℂ) : ℂ := gaussInt (starP p * q)

theorem gpair_eq_inner (p q : MvPolynomial (Fin d) ℂ) :
    gpair p q = (inner ℂ (pgLp p) (pgLp q) : ℂ) := (inner_pgLp_pgLp p q).symm

theorem gpair_conj (p q : MvPolynomial (Fin d) ℂ) :
    gpair q p = (starRingEnd ℂ) (gpair p q) := by
  rw [gpair_eq_inner, gpair_eq_inner, inner_conj_symm]

theorem gpair_add_right (p q r : MvPolynomial (Fin d) ℂ) :
    gpair p (q + r) = gpair p q + gpair p r := by
  simp only [gpair, mul_add]
  exact gaussInt_add _ _

theorem gpair_smul_right (c : ℂ) (p q : MvPolynomial (Fin d) ℂ) :
    gpair p (c • q) = c * gpair p q := by
  simp only [gpair, mul_smul_comm]
  exact gaussInt_smul _ _

theorem gpair_add_left (p q r : MvPolynomial (Fin d) ℂ) :
    gpair (p + q) r = gpair p r + gpair q r := by
  simp only [gpair, starP_add, add_mul]
  exact gaussInt_add _ _

theorem gpair_smul_left (c : ℂ) (p q : MvPolynomial (Fin d) ℂ) :
    gpair (c • p) q = (starRingEnd ℂ) c * gpair p q := by
  simp only [gpair, starP_smul, smul_mul_assoc]
  exact gaussInt_smul _ _

theorem gpair_sum_right {ι : Type*} (s : Finset ι) (p : MvPolynomial (Fin d) ℂ)
    (f : ι → MvPolynomial (Fin d) ℂ) : gpair p (∑ v ∈ s, f v) = ∑ v ∈ s, gpair p (f v) := by
  classical
  induction s using Finset.induction with
  | empty => simp [gpair, gaussInt]
  | insert v s hv ih => rw [Finset.sum_insert hv, Finset.sum_insert hv, gpair_add_right, ih]

theorem norm_pgLp_sq_eq (p : MvPolynomial (Fin d) ℂ) : ‖pgLp p‖ ^ 2 = (gpair p p).re := by
  rw [gpair_eq_inner]
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (pgLp p)).symm

theorem gpair_sub_right (p q r : MvPolynomial (Fin d) ℂ) :
    gpair p (q - r) = gpair p q - gpair p r := by
  rw [show q - r = q + (-1 : ℂ) • r by module, gpair_add_right, gpair_smul_right]
  ring

theorem gpair_self_nonneg (p : MvPolynomial (Fin d) ℂ) : 0 ≤ (gpair p p).re := by
  rw [← norm_pgLp_sq_eq]
  positivity

/-- The Gauss pairing of two product Hermite polynomials: the orthogonality relation. -/
theorem gpair_hermiteMv (a b : Fin d →₀ ℕ) :
    gpair (hermiteMv a) (hermiteMv b)
      = if a = b then (((∏ i, ((a i).factorial : ℝ)) * Real.sqrt (2 * Real.pi) ^ d : ℝ) : ℂ)
        else 0 := by
  rw [gpair_eq_inner, inner_pgLp_hermiteMv]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hprod : (∏ i, hermiteInner (a i) (a i))
        = (∏ i, ((a i).factorial : ℝ)) * Real.sqrt (2 * Real.pi) ^ d := by
      have : ∀ i : Fin d, hermiteInner (a i) (a i)
          = ((a i).factorial : ℝ) * Real.sqrt (2 * Real.pi) := by
        intro i; rw [hermiteInner_eq]; simp
      rw [Finset.prod_congr rfl fun i _ => this i, Finset.prod_mul_distrib]
      simp
    rw [hprod]
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ : ∃ i : Fin d, a i ≠ b i := by
      by_contra hcon
      push_neg at hcon
      exact hab (Finsupp.ext hcon)
    have hz : (∏ i, hermiteInner (a i) (b i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hermiteInner_eq, if_neg hi])
    rw [hz]
    simp

/-! ## 2. The mainstream Navier–Stokes system in Leray–Galerkin form -/

/-- The advection field `B_i(u,u) = Σ_{j,k} b_{ijk} u_j u_k` of a Galerkin form of the
incompressible Navier–Stokes equation: the exact quadratic term, with the pressure already
eliminated by the Leray projection (that elimination is what the two structural identities of
`NsSystem` record). -/
def advOf (b : Fin d → Fin d → Fin d → ℝ) (i : Fin d) : MvPolynomial (Fin d) ℂ :=
  ∑ j, ∑ k, ((b i j k : ℝ) : ℂ) • (X j * X k)

/-- **The mainstream incompressible Navier–Stokes system**, in the functional form
`u̇ = −νAu + B(u,u)` in which it is always written: `nu` is the viscosity, `lam i = |k_i|²` the
Stokes eigenvalues in the divergence-free Fourier basis, and `bcoef` the structure constants of
the exact quadratic advection.  The two hypotheses `leray` and `liouville` are the two
structural identities of the incompressible equation: the nonlinearity (advection together with
the pressure gradient) does no work on the velocity, and the phase-space flow is
volume-preserving. -/
structure NsSystem (d : ℕ) where
  /-- The kinematic viscosity `ν`. -/
  nu : ℝ
  /-- The Stokes eigenvalues `λ_i = |k_i|²`. -/
  lam : Fin d → ℝ
  /-- The structure constants of the advection `B_i(u,u) = Σ_{j,k} b_{ijk}u_ju_k`. -/
  bcoef : Fin d → Fin d → Fin d → ℝ
  nu_nonneg : 0 ≤ nu
  lam_nonneg : ∀ i, 0 ≤ lam i
  /-- **Leray's energy identity** `⟨u, B(u,u)⟩ = 0`. -/
  leray : ∑ i, X i * advOf bcoef i = (0 : MvPolynomial (Fin d) ℂ)
  /-- **The Liouville identity** `div_u B = 0`: the phase-space flow of the advection preserves
  volume. -/
  liouville : ∑ i, pderiv i (advOf bcoef i) = (0 : MvPolynomial (Fin d) ℂ)

variable (S : NsSystem d)

/-- The **drift field** of the mainstream system: the right-hand side
`F_i(u) = −ν λ_i u_i + B_i(u,u)` of the Navier–Stokes equation. -/
def drift (i : Fin d) : MvPolynomial (Fin d) ℂ :=
  -(((S.nu * S.lam i : ℝ) : ℂ) • X i) + advOf S.bcoef i

/-- **The Navier–Stokes Hamiltonian** `H_NS = ½ Σ_m (π_m F_m + F_m π_m)`: the Weyl-ordered
Koopman–von Neumann (Liouville) generator of the mainstream Navier–Stokes flow.  No square of a
residual, no linearization and no perturbative splitting occurs in it. -/
def kvnPoly : Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  ∑ i, weylProd (momOp i) (mulOp (drift S i))

/-- The total Stokes trace `ν Σ_i λ_i`, i.e. `− div F`. -/
def viscTrace : ℝ := S.nu * ∑ i, S.lam i

theorem realCoeff_neg {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) : RealCoeff (-p) := by
  change starP (-p) = -p
  rw [starP_neg, show starP p = p from hp]

theorem realCoeff_one : RealCoeff (1 : MvPolynomial (Fin d) ℂ) := map_one _

theorem realCoeff_sub {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p - q) := by
  change starP (p - q) = p - q
  rw [starP_sub, show starP p = p from hp, show starP q = q from hq]

theorem advOf_realCoeff (b : Fin d → Fin d → Fin d → ℝ) (i : Fin d) : RealCoeff (advOf b i) :=
  RealCoeff.sum fun _ _ => RealCoeff.sum fun _ _ =>
    RealCoeff.smul ((realCoeff_X _).mul (realCoeff_X _))

theorem drift_realCoeff (i : Fin d) : RealCoeff (drift S i) :=
  (realCoeff_neg (RealCoeff.smul (realCoeff_X i))).add (advOf_realCoeff S.bcoef i)

theorem polySym_zero : PolySym (0 : Module.End ℂ (MvPolynomial (Fin d) ℂ)) := by
  intro p q
  simp [gaussInt]

theorem polySym_sum {ι : Type*} {s : Finset ι} {T : ι → Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (h : ∀ i ∈ s, PolySym (T i)) : PolySym (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using polySym_zero
  | insert v s hv ih =>
      rw [Finset.sum_insert hv]
      exact (h v (Finset.mem_insert_self v s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **The Navier–Stokes Hamiltonian is symmetric on the core.** -/
theorem kvnPoly_polySym : PolySym (kvnPoly S) :=
  polySym_sum fun i _ => weylProd_polySym (momOp_polySym i) (mulOp_polySym (drift_realCoeff S i))

/-- The Weyl-ordered product of a momentum and a multiplication operator, expanded. -/
theorem weylProd_mom_mul_apply (f p : MvPolynomial (Fin d) ℂ) (i : Fin d) :
    weylProd (momOp i) (mulOp f) p
      = (-Complex.I) • (f * derOp i p + ((1 / 2 : ℝ) : ℂ) • (pderiv i f * p)) := by
  have hder : derOp i (f * p) = pderiv i f * p + f * derOp i p := by
    rw [derOp_apply, derOp_apply, pderiv_mul]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  simp only [weylProd, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    mulOp_apply, momOp, hder, mul_smul_comm]
  push_cast
  module

theorem pderiv_drift (i : Fin d) :
    pderiv i (drift S i) = -(((S.nu * S.lam i : ℝ) : ℂ) • 1) + pderiv i (advOf S.bcoef i) := by
  rw [drift, map_add, map_neg, MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_X_self]
  simp [MvPolynomial.smul_eq_C_mul]

theorem sum_pderiv_drift :
    ∑ i, pderiv i (drift S i) = ((-(viscTrace S) : ℝ) : ℂ) • (1 : MvPolynomial (Fin d) ℂ) := by
  simp only [pderiv_drift]
  rw [Finset.sum_add_distrib, S.liouville, add_zero]
  have hterm : ∀ x : Fin d,
      -((((S.nu * S.lam x : ℝ)) : ℂ) • (1 : MvPolynomial (Fin d) ℂ))
        = (((-(S.nu * S.lam x) : ℝ)) : ℂ) • (1 : MvPolynomial (Fin d) ℂ) := by
    intro x
    push_cast
    module
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_smul]
  congr 1
  rw [viscTrace, Finset.mul_sum]
  push_cast
  rw [← Finset.sum_neg_distrib]

/-- **The Hamiltonian is the Liouville generator of the Navier–Stokes flow**:
`H_NS = −i (Σ_i F_i ∂_i + ½ div F)`, and by the Liouville identity `div F = −ν Σ_i λ_i`. -/
theorem kvnPoly_apply (p : MvPolynomial (Fin d) ℂ) :
    kvnPoly S p
      = (-Complex.I) • ((∑ i, drift S i * derOp i p) + ((-(viscTrace S) / 2 : ℝ) : ℂ) • p) := by
  have hsum : kvnPoly S p = ∑ i, weylProd (momOp i) (mulOp (drift S i)) p := by
    rw [kvnPoly]
    simp
  rw [hsum, Finset.sum_congr rfl fun i _ => weylProd_mom_mul_apply (drift S i) p i,
    ← Finset.smul_sum, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_mul,
    sum_pderiv_drift]
  congr 2
  rw [smul_mul_assoc, one_mul, smul_smul]
  congr 1
  push_cast
  ring

/-! ## 3. The conjugation `C ψ = ψ̄` reverses the sign of the form -/

theorem starP_derOp (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (derOp i p) = derOp i (starP p) := by
  rw [derOp_apply, derOp_apply, starP_sub, starP_pderiv, starP_real_smul, starP_mul, starP_X]

/-- **`C H_NS C = − H_NS`**: the Hamiltonian anticommutes with the antiunitary conjugation, the
first-order operator being `i` times a real one. -/
theorem starP_kvnPoly (p : MvPolynomial (Fin d) ℂ) :
    starP (kvnPoly S p) = - kvnPoly S (starP p) := by
  rw [kvnPoly_apply, kvnPoly_apply, starP_smul, starP_add, starP_sum, starP_real_smul,
    Complex.conj_neg_I]
  have hterm : ∀ i : Fin d, starP (drift S i * derOp i p) = drift S i * derOp i (starP p) := by
    intro i
    rw [starP_mul, show starP (drift S i) = drift S i from drift_realCoeff S i, starP_derOp]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  module

/-- The quadratic form of the Navier–Stokes Hamiltonian at a core vector. -/
def quadP (p : MvPolynomial (Fin d) ℂ) : ℝ := (gpair p (kvnPoly S p)).re

theorem starP_starP (p : MvPolynomial (Fin d) ℂ) : starP (starP p) = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [starP_add, starP_add, hp, hq]
  | mul_X p i hp => rw [starP_mul, starP_X, starP_mul, starP_X, hp]

theorem gaussInt_starP (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (starP r) = (starRingEnd ℂ) (gaussInt r) := by
  rw [gaussInt, gaussInt, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [eval_starP, map_mul, Complex.conj_ofReal]

theorem gpair_starP (p q : MvPolynomial (Fin d) ℂ) :
    gpair (starP p) (starP q) = (starRingEnd ℂ) (gpair p q) := by
  rw [gpair, gpair, starP_starP, ← gaussInt_starP, starP_mul, starP_starP]

/-- **The numerical range of `H_NS` is symmetric about `0`.** -/
theorem quadP_starP (p : MvPolynomial (Fin d) ℂ) : quadP S (starP p) = - quadP S p := by
  have hH : kvnPoly S (starP p) = - starP (kvnPoly S p) := by
    have h := starP_kvnPoly S (starP p)
    rw [starP_starP] at h
    calc kvnPoly S (starP p) = starP (starP (kvnPoly S (starP p))) := (starP_starP _).symm
      _ = starP (-kvnPoly S p) := by rw [h]
      _ = - starP (kvnPoly S p) := starP_neg _
  have hneg : gpair p (-kvnPoly S p) = - gpair p (kvnPoly S p) := by
    rw [show (-kvnPoly S p) = (-1 : ℂ) • kvnPoly S p from (neg_one_smul ℂ _).symm,
      gpair_smul_right]
    ring
  rw [quadP, quadP, hH, show (-starP (kvnPoly S p)) = starP (-kvnPoly S p) from
      (starP_neg _).symm, gpair_starP, hneg]
  simp

/-- On real core vectors the form vanishes. -/
theorem quadP_of_realCoeff {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) : quadP S p = 0 := by
  have h := quadP_starP S p
  rw [show starP p = p from hp] at h
  linarith

/-- The Hamiltonian is symmetric for the Gauss pairing. -/
theorem gpair_kvn_symm (p q : MvPolynomial (Fin d) ℂ) :
    gpair (kvnPoly S p) q = gpair p (kvnPoly S q) := kvnPoly_polySym S p q

theorem gpair_expand (α β : MvPolynomial (Fin d) ℂ) (s : ℂ)
    (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    gpair (α + s • β) (T (α + s • β))
      = gpair α (T α) + s * gpair α (T β) + (starRingEnd ℂ) s * gpair β (T α)
        + (starRingEnd ℂ) s * (s * gpair β (T β)) := by
  rw [map_add, map_smul, gpair_add_left, gpair_add_right, gpair_add_right, gpair_smul_right,
    gpair_smul_left, gpair_smul_left, gpair_smul_right]
  ring

/-- The form of `H_NS` on the two-real-vector family `α + i t β`. -/
theorem quadP_real_pair {α β : MvPolynomial (Fin d) ℂ} (hα : RealCoeff α) (hβ : RealCoeff β)
    (t : ℝ) :
    quadP S (α + ((t : ℂ) * Complex.I) • β) = -2 * t * (gpair α (kvnPoly S β)).im := by
  have hA : (gpair α (kvnPoly S α)).re = 0 := quadP_of_realCoeff S hα
  have hB : (gpair β (kvnPoly S β)).re = 0 := quadP_of_realCoeff S hβ
  have hC : gpair β (kvnPoly S α) = (starRingEnd ℂ) (gpair α (kvnPoly S β)) := by
    rw [← gpair_kvn_symm, gpair_conj]
  rw [quadP, gpair_expand α β ((t : ℂ) * Complex.I) (kvnPoly S), hC]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, hA, hB]
  ring

theorem gpair_real_real {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    (starRingEnd ℂ) (gpair p q) = gpair p q := by
  rw [← gpair_starP, show starP p = p from hp, show starP q = q from hq]

/-- The squared norm of the same family. -/
theorem gpair_real_pair {α β : MvPolynomial (Fin d) ℂ} (hα : RealCoeff α) (hβ : RealCoeff β)
    (t : ℝ) :
    (gpair (α + ((t : ℂ) * Complex.I) • β) (α + ((t : ℂ) * Complex.I) • β)).re
      = (gpair α α).re + t ^ 2 * (gpair β β).re := by
  have hC : gpair β α = (starRingEnd ℂ) (gpair α β) := gpair_conj α β
  have him : (gpair α β).im = 0 := by
    have h := gpair_real_real hα hβ
    have := congrArg Complex.im h
    simp only [Complex.conj_im] at this
    linarith
  have hexp := gpair_expand α β ((t : ℂ) * Complex.I)
    (LinearMap.id : Module.End ℂ (MvPolynomial (Fin d) ℂ))
  simp only [LinearMap.id_coe, id_eq] at hexp
  rw [hexp, hC]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, him]
  ring

/-! ## 4. The parity selection rule -/

/-- The total degree of a multi-index. -/
def mdeg (a : Fin d →₀ ℕ) : ℕ := ∑ i, a i

/-- The span of the product Hermite polynomials of a fixed degree parity. -/
def parSpan (d : ℕ) (e : ZMod 2) : Submodule ℂ (MvPolynomial (Fin d) ℂ) :=
  Submodule.span ℂ {p | ∃ a : Fin d →₀ ℕ, ((mdeg a : ℕ) : ZMod 2) = e ∧ p = hermiteMv a}

theorem hermiteMv_mem_parSpan (a : Fin d →₀ ℕ) :
    hermiteMv a ∈ parSpan d ((mdeg a : ℕ) : ZMod 2) :=
  Submodule.subset_span ⟨a, rfl, rfl⟩

theorem mdeg_add_single (a : Fin d →₀ ℕ) (i : Fin d) :
    mdeg (a + Finsupp.single i 1) = mdeg a + 1 := by
  classical
  simp only [mdeg, Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  simp [Finsupp.single_apply]

theorem mdeg_sub_single {a : Fin d →₀ ℕ} {i : Fin d} (h : 1 ≤ a i) :
    mdeg (a - Finsupp.single i 1) + 1 = mdeg a := by
  classical
  have hsub : ∀ j : Fin d, (a - Finsupp.single i 1 : Fin d →₀ ℕ) j
      = a j - (if j = i then 1 else 0) := by
    intro j
    simp [Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]
  have hsplit : mdeg (a - Finsupp.single i 1)
      = ∑ j, (a j - (if j = i then 1 else 0)) := Finset.sum_congr rfl fun j _ => hsub j
  rw [hsplit, mdeg, ← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j => a j) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i, (a j - (if j = i then 1 else 0))
      = ∑ j ∈ Finset.univ.erase i, a j :=
    Finset.sum_congr rfl fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]; omega
  rw [hrest, if_pos rfl]
  omega

theorem zmod_two_shift : ∀ x y : ZMod 2, x + 1 = y → x = y + 1 := by decide

theorem zmod_two_add_two : ∀ x : ZMod 2, x + 1 + 1 = x := by decide

theorem X_mul_mem_parSpan {e : ZMod 2} (i : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) : X i * p ∈ parSpan d (e + 1) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [hermiteMv_X_mul]
      have h1 : hermiteMv (a + Finsupp.single i 1) ∈ parSpan d (e + 1) := by
        refine Submodule.subset_span ⟨a + Finsupp.single i 1, ?_, rfl⟩
        rw [mdeg_add_single, ← ha]
        push_cast
        ring
      refine add_mem h1 ?_
      rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
      · simp [h0]
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a - Finsupp.single i 1, ?_, rfl⟩)
        have hd := mdeg_sub_single (a := a) (i := i) hpos
        refine zmod_two_shift _ _ ?_
        rw [← ha, ← hd]
        push_cast
        ring
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem pderiv_mem_parSpan {e : ZMod 2} (i : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) : pderiv i p ∈ parSpan d (e + 1) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [pderiv_hermiteMv]
      rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
      · simp [h0]
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a - Finsupp.single i 1, ?_, rfl⟩)
        have hd := mdeg_sub_single (a := a) (i := i) hpos
        refine zmod_two_shift _ _ ?_
        rw [← ha, ← hd]
        push_cast
        ring
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
      rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, ← MvPolynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ hx

theorem derOp_mem_parSpan {e : ZMod 2} (i : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) : derOp i p ∈ parSpan d (e + 1) := by
  rw [derOp_apply]
  exact sub_mem (pderiv_mem_parSpan i hp)
    (Submodule.smul_mem _ _ (X_mul_mem_parSpan i hp))

theorem X_X_mul_mem_parSpan {e : ZMod 2} (j k : Fin d) {p : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) : X j * X k * p ∈ parSpan d e := by
  have h := X_mul_mem_parSpan j (X_mul_mem_parSpan k hp)
  rw [zmod_two_add_two e] at h
  rw [mul_assoc]
  exact h

/-- Multiplication by the (quadratic) advection field preserves the degree parity. -/
theorem advOf_mul_mem_parSpan {e : ZMod 2} (b : Fin d → Fin d → Fin d → ℝ) (i : Fin d)
    {p : MvPolynomial (Fin d) ℂ} (hp : p ∈ parSpan d e) : advOf b i * p ∈ parSpan d e := by
  rw [advOf, Finset.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Finset.sum_mul]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [smul_mul_assoc]
  exact Submodule.smul_mem _ _ (X_X_mul_mem_parSpan j k hp)

/-- **The parity selection rule**: core vectors of different degree parity are orthogonal. -/
theorem gpair_parity {e e' : ZMod 2} (hee : e ≠ e') {p q : MvPolynomial (Fin d) ℂ}
    (hp : p ∈ parSpan d e) (hq : q ∈ parSpan d e') : gpair p q = 0 := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      induction hq using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨c, hc, rfl⟩ := hy
          have hne : a ≠ c := by
            intro hac
            exact hee (ha ▸ hac ▸ hc.symm ▸ rfl)
          rw [gpair_hermiteMv, if_neg hne]
      | zero => simp [gpair, gaussInt]
      | add u v _ _ hu hv => rw [gpair_add_right, hu, hv, add_zero]
      | smul c u _ hu => rw [gpair_smul_right, hu, mul_zero]
  | zero => simp [gpair, gaussInt]
  | add u v _ _ hu hv => rw [gpair_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [gpair_smul_left, hu, mul_zero]

/-! ## 5. The matrix element between the one-mode Hermite states `|n⟩` and `|n+2⟩` -/

theorem realCoeff_prod {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin d) ℂ}
    (h : ∀ i ∈ s, RealCoeff (f i)) : RealCoeff (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using realCoeff_one
  | insert v s hv ih =>
      rw [Finset.prod_insert hv]
      exact (h v (Finset.mem_insert_self v s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem realCoeff_hermiteFactor (i : Fin d) (n : ℕ) : RealCoeff (hermiteFactor i n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simpa [hermiteFactor_zero] using (realCoeff_one (d := d))
      | (m + 1) =>
          have h := hermiteFactor_X_mul i m
          have heq : hermiteFactor i (m + 1)
              = X i * hermiteFactor i m - (((m : ℝ)) : ℂ) • hermiteFactor i (m - 1) := by
            rw [h]
            push_cast
            module
          rw [heq]
          exact realCoeff_sub ((realCoeff_X i).mul (ih m (by omega)))
            (RealCoeff.smul (ih (m - 1) (by omega)))

theorem realCoeff_hermiteMv (a : Fin d →₀ ℕ) : RealCoeff (hermiteMv a) :=
  realCoeff_prod fun i _ => realCoeff_hermiteFactor i (a i)

/-! ### The one-mode multi-indices -/

/-- The multi-index with `m` quanta in the mode `i₀` and none elsewhere. -/
def st (i0 : Fin d) (m : ℕ) : Fin d →₀ ℕ := Finsupp.single i0 m

@[simp] theorem st_apply_self (i0 : Fin d) (m : ℕ) : st i0 m i0 = m := by
  simp [st]

theorem st_apply_other {i0 i : Fin d} (h : i ≠ i0) (m : ℕ) : st i0 m i = 0 := by
  simp [st, Ne.symm h]

theorem st_add_single (i0 : Fin d) (m : ℕ) :
    st i0 m + Finsupp.single i0 1 = st i0 (m + 1) := by
  rw [st, st, ← Finsupp.single_add]

theorem st_sub_single (i0 : Fin d) (m : ℕ) :
    st i0 m - Finsupp.single i0 1 = st i0 (m - 1) := by
  classical
  ext j
  by_cases hj : j = i0
  · subst hj; simp [st, Finsupp.tsub_apply]
  · simp [st, Finsupp.tsub_apply, Ne.symm hj]

theorem st_ne_st {i0 : Fin d} {m m' : ℕ} (h : m ≠ m') : st i0 m ≠ st i0 m' := by
  intro hc
  exact h (by simpa using congrArg (fun a : Fin d →₀ ℕ => a i0) hc)

theorem st_ne_add_other {i0 i : Fin d} (h : i ≠ i0) (m m' : ℕ) (c : ℕ) (hc : c ≠ 0) :
    st i0 m ≠ st i0 m' + Finsupp.single i c := by
  intro hcon
  have := congrArg (fun a : Fin d →₀ ℕ => a i) hcon
  simp [st, Ne.symm h] at this
  exact hc this.symm

/-- The squared norm of the one-mode Hermite state `|m⟩`. -/
theorem gpair_st_self (i0 : Fin d) (m : ℕ) :
    gpair (hermiteMv (st i0 m)) (hermiteMv (st i0 m))
      = (((m.factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ d : ℝ) : ℂ) := by
  classical
  rw [gpair_hermiteMv, if_pos rfl]
  congr 2
  rw [show ((m.factorial : ℝ)) = ((((st i0 m) i0).factorial : ℕ) : ℝ) by rw [st_apply_self]]
  exact Finset.prod_eq_single i0 (fun j _ hj => by rw [st_apply_other hj]; simp)
    (fun h => absurd (Finset.mem_univ i0) h)

theorem gpair_neg_right (p q : MvPolynomial (Fin d) ℂ) : gpair p (-q) = - gpair p q := by
  rw [show (-q) = (-1 : ℂ) • q from (neg_one_smul ℂ q).symm, gpair_smul_right]
  ring

theorem mdeg_st (i0 : Fin d) (m : ℕ) : mdeg (st i0 m) = m := by
  classical
  rw [mdeg, Finset.sum_eq_single i0 (fun j _ hj => st_apply_other hj m)
    (fun h => absurd (Finset.mem_univ i0) h), st_apply_self]

theorem gpair_alpha_st (i0 : Fin d) (n m : ℕ) (hm : m ≠ n + 2) :
    gpair (hermiteMv (st i0 (n + 2))) (hermiteMv (st i0 m)) = 0 := by
  rw [gpair_hermiteMv, if_neg (st_ne_st (Ne.symm hm))]

theorem st_ne_of_apply {a : Fin d →₀ ℕ} {i0 i : Fin d} (h : i ≠ i0) {m : ℕ} (hai : a i ≠ 0) :
    st i0 m ≠ a := fun hc => hai (by rw [← hc, st_apply_other h])

theorem X_mul_st (i0 : Fin d) (m : ℕ) :
    X i0 * hermiteMv (st i0 m)
      = hermiteMv (st i0 (m + 1)) + (m : ℂ) • hermiteMv (st i0 (m - 1)) := by
  rw [hermiteMv_X_mul, st_add_single, st_sub_single, st_apply_self]

theorem pderiv_st (i0 : Fin d) (m : ℕ) :
    pderiv i0 (hermiteMv (st i0 m)) = (m : ℂ) • hermiteMv (st i0 (m - 1)) := by
  rw [pderiv_hermiteMv, st_sub_single, st_apply_self]

theorem pderiv_st_other {i0 i : Fin d} (h : i ≠ i0) (m : ℕ) :
    pderiv i (hermiteMv (st i0 m)) = 0 := by
  rw [pderiv_hermiteMv, st_apply_other h]
  simp

theorem X_mul_st_other {i0 i : Fin d} (h : i ≠ i0) (m : ℕ) :
    X i * hermiteMv (st i0 m) = hermiteMv (st i0 m + Finsupp.single i 1) := by
  rw [hermiteMv_X_mul, st_apply_other h]
  simp

/-- **The advection contributes nothing to the matrix element**: its parity is wrong. -/
theorem gpair_adv_vanishes (i0 : Fin d) (n : ℕ) (i : Fin d) :
    gpair (hermiteMv (st i0 (n + 2))) (advOf S.bcoef i * derOp i (hermiteMv (st i0 n))) = 0 := by
  have hshift : ((n + 2 : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2) := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    push_cast
    rw [h2, add_zero]
  have hne : (((n + 2 : ℕ) : ℕ) : ZMod 2) ≠ ((n : ℕ) : ZMod 2) + 1 := by
    rw [hshift]
    have hx : ∀ x : ZMod 2, x ≠ x + 1 := by decide
    exact hx _
  refine gpair_parity hne ?_ ?_
  · have h := hermiteMv_mem_parSpan (st i0 (n + 2))
    rwa [mdeg_st] at h
  · refine advOf_mul_mem_parSpan _ _ (derOp_mem_parSpan i ?_)
    have h := hermiteMv_mem_parSpan (st i0 n)
    rwa [mdeg_st] at h

/-- The viscous term of a mode other than `i₀` contributes nothing either. -/
theorem gpair_visc_other (i0 : Fin d) (n : ℕ) {i : Fin d} (h : i ≠ i0) :
    gpair (hermiteMv (st i0 (n + 2))) (X i * derOp i (hermiteMv (st i0 n))) = 0 := by
  have hd : derOp i (hermiteMv (st i0 n))
      = -(((1 / 2 : ℝ) : ℂ) • hermiteMv (st i0 n + Finsupp.single i 1)) := by
    rw [derOp_apply, pderiv_st_other h, X_mul_st_other h]
    module
  have haii : ((st i0 n + Finsupp.single i 1 + Finsupp.single i 1 : Fin d →₀ ℕ) i) ≠ 0 := by
    simp [st_apply_other h]
  have hX : X i * hermiteMv (st i0 n + Finsupp.single i 1)
      = hermiteMv (st i0 n + Finsupp.single i 1 + Finsupp.single i 1)
        + (1 : ℂ) • hermiteMv (st i0 n) := by
    rw [hermiteMv_X_mul]
    congr 2
    · simp [st_apply_other h]
    · simp
  rw [hd, mul_neg, mul_smul_comm, hX, gpair_neg_right, gpair_smul_right, gpair_add_right,
    gpair_smul_right, gpair_hermiteMv, gpair_hermiteMv,
    if_neg (st_ne_of_apply h haii), if_neg (st_ne_st (by omega))]
  simp

/-- The expansion of the viscous term of the mode `i₀` in the Hermite basis. -/
theorem X_derOp_st_expand (i0 : Fin d) (n : ℕ) :
    X i0 * derOp i0 (hermiteMv (st i0 n))
      = (-(1 / 2 : ℂ)) • hermiteMv (st i0 (n + 2)) + (-(1 / 2 : ℂ)) • hermiteMv (st i0 n)
        + (((n : ℂ) * ((n - 1 : ℕ) : ℂ)) / 2) • hermiteMv (st i0 (n - 1 - 1)) := by
  cases n with
  | zero =>
      simp only [derOp_apply, pderiv_st, mul_sub, mul_add, mul_smul_comm, X_mul_st]
      push_cast
      module
  | succ m =>
      simp only [derOp_apply, pderiv_st, mul_sub, mul_add, mul_smul_comm, X_mul_st,
        Nat.add_sub_cancel]
      push_cast
      module

/-- The viscous term of the mode `i₀`: the only surviving matrix element. -/
theorem gpair_visc_self (i0 : Fin d) (n : ℕ) :
    gpair (hermiteMv (st i0 (n + 2))) (X i0 * derOp i0 (hermiteMv (st i0 n)))
      = (-(1 / 2 : ℂ)) * (((n + 2).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ d : ℝ) := by
  rw [X_derOp_st_expand, gpair_add_right, gpair_add_right, gpair_smul_right, gpair_smul_right,
    gpair_smul_right, gpair_st_self, gpair_alpha_st i0 n n (by omega),
    gpair_alpha_st i0 n (n - 1 - 1) (by omega)]
  push_cast
  ring

/-- **The exact matrix element** `⟪n+2| H_NS |n⟫` in a single mode `i₀`: the advection drops out
by the parity selection rule, and what remains is the viscous (dilation) part, of size
proportional to `(n+2)!`. -/
theorem gpair_hermite_kvn (i0 : Fin d) (n : ℕ) :
    gpair (hermiteMv (st i0 (n + 2))) (kvnPoly S (hermiteMv (st i0 n)))
      = (-Complex.I)
        * (((S.nu * S.lam i0 / 2) * ((n + 2).factorial : ℝ)
            * Real.sqrt (2 * Real.pi) ^ d : ℝ) : ℂ) := by
  classical
  have hterm : ∀ i : Fin d,
      gpair (hermiteMv (st i0 (n + 2))) (drift S i * derOp i (hermiteMv (st i0 n)))
        = if i = i0 then
            ((S.nu * S.lam i0 : ℝ) : ℂ) * (1 / 2)
              * (((n + 2).factorial : ℝ) * Real.sqrt (2 * Real.pi) ^ d : ℝ)
          else 0 := by
    intro i
    rw [drift, add_mul, gpair_add_right, gpair_adv_vanishes S i0 n i, add_zero, neg_mul,
      smul_mul_assoc, gpair_neg_right, gpair_smul_right]
    by_cases hi : i = i0
    · subst hi
      rw [if_pos rfl, gpair_visc_self]
      push_cast
      ring
    · rw [if_neg hi, gpair_visc_other i0 n hi]
      simp
  rw [kvnPoly_apply, gpair_smul_right, gpair_add_right, gpair_sum_right, gpair_smul_right,
    gpair_alpha_st i0 n n (by omega), mul_zero, add_zero,
    Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_ite_eq' Finset.univ i0,
    if_pos (Finset.mem_univ i0)]
  push_cast
  ring

/-! ## 6. The Hamiltonian is not bounded below -/

/-- **The quadratic form of the mainstream Navier–Stokes Hamiltonian is not bounded below** on
the Gauss–polynomial core: for every `c` there is a core vector with
`⟪p, H_NS p⟫ < − c ‖p‖²`. -/
theorem kvn_quadP_not_bounded_below (i0 : Fin d) (hnu : 0 < S.nu) (hlam : 0 < S.lam i0) (c : ℝ) :
    ∃ p : MvPolynomial (Fin d) ℂ, quadP S p < -c * (gpair p p).re := by
  have hnl : 0 < S.nu * S.lam i0 := mul_pos hnu hlam
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * max c 0 < ((n : ℝ) + 1) * (S.nu * S.lam i0) := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((2 * max c 0) / (S.nu * S.lam i0))
    refine ⟨n, ?_⟩
    have h1 : (2 * max c 0) < (n : ℝ) * (S.nu * S.lam i0) := by
      rw [div_lt_iff₀ hnl] at hn
      exact hn
    nlinarith [hnl]
  set K : ℝ := Real.sqrt (2 * Real.pi) ^ d with hKdef
  have hK : 0 < K := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact pow_pos this d
  set B : ℝ := (n.factorial : ℝ) * K with hBdef
  set A : ℝ := ((n + 2).factorial : ℝ) * K with hAdef
  have hBpos : 0 < B := by
    have : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    positivity
  have hAB : A = ((n : ℝ) + 1) * ((n : ℝ) + 2) * B := by
    rw [hAdef, hBdef]
    have hf : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * (((n : ℝ) + 1) * (n.factorial : ℝ)) := by
      rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hf]
    ring
  have hApos : 0 < A := by
    rw [hAB]
    positivity
  refine ⟨hermiteMv (st i0 (n + 2))
    + (((-((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) • hermiteMv (st i0 n), ?_⟩
  rw [quadP_real_pair S (realCoeff_hermiteMv _) (realCoeff_hermiteMv _),
    gpair_real_pair (realCoeff_hermiteMv _) (realCoeff_hermiteMv _),
    gpair_hermite_kvn, gpair_st_self, gpair_st_self]
  have him : ((-Complex.I)
      * (((S.nu * S.lam i0 / 2) * ((n + 2).factorial : ℝ) * K : ℝ) : ℂ)).im
      = -((S.nu * S.lam i0 / 2) * A) := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, hAdef]
    ring
  rw [him]
  simp only [Complex.ofReal_re]
  have hcA : c * (A + ((n : ℝ) + 1) ^ 2 * B) ≤ 2 * max c 0 * A := by
    have h1 : ((n : ℝ) + 1) ^ 2 * B ≤ A := by
      rw [hAB]
      nlinarith [hBpos, Nat.cast_nonneg (α := ℝ) n]
    have h3 : (0 : ℝ) ≤ max c 0 := le_max_right _ _
    have hY : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 * B := by positivity
    rcases le_or_gt c 0 with hc | hc
    · have hle : c * (A + ((n : ℝ) + 1) ^ 2 * B) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
      nlinarith [hApos, h3]
    · rw [max_eq_left hc.le]
      nlinarith [h1, hc]
  nlinarith [hn, hApos, hcA]

/-! ## 7. The same statements on the Gauss–polynomial core of `L²(ℝᵈ)` -/

/-- **The Navier–Stokes Hamiltonian on the Gauss–polynomial core of `L²(ℝᵈ)`.** -/
def nsKoopmanOp : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype.comp ((coreRepPoly d).op (kvnPoly S))

/-- **The Navier–Stokes Hamiltonian is symmetric on the core.** -/
theorem nsKoopmanOp_symmetricOn : SymmetricOn (polyGaussCore (d := d)) (nsKoopmanOp S) :=
  (coreRepPoly d).symmetricOn_op (kvnPoly_polySym S)

theorem coe_core_eq (x : polyGaussCore (d := d)) :
    ((x : L2d d)) = pgLp ((coreRepPoly d).equiv.symm x) := (coreRepPoly d).coe_symm x

theorem quadForm_nsKoopmanOp (x : polyGaussCore (d := d)) :
    quadForm (nsKoopmanOp S) x = quadP S ((coreRepPoly d).equiv.symm x) := by
  have h1 : (nsKoopmanOp S) x = pgLp (kvnPoly S ((coreRepPoly d).equiv.symm x)) :=
    (coreRepPoly d).coe_op (kvnPoly S) x
  rw [quadForm, h1, coe_core_eq, inner_pgLp_pgLp]
  rfl

theorem norm_core_sq (x : polyGaussCore (d := d)) :
    ‖(x : L2d d)‖ ^ 2
      = (gpair ((coreRepPoly d).equiv.symm x) ((coreRepPoly d).equiv.symm x)).re := by
  rw [coe_core_eq, norm_pgLp_sq_eq]

/-- **The mainstream Navier–Stokes Hamiltonian is not bounded below on the core.**  This is the
reason it cannot play the role of the *positive* comparison operator `N` of the Faris–Lavine
criterion. -/
theorem nsKoopmanOp_not_bounded_below (i0 : Fin d) (hnu : 0 < S.nu) (hlam : 0 < S.lam i0)
    (c : ℝ) :
    ∃ x : polyGaussCore (d := d), quadForm (nsKoopmanOp S) x < -c * ‖(x : L2d d)‖ ^ 2 := by
  obtain ⟨p, hp⟩ := kvn_quadP_not_bounded_below S i0 hnu hlam c
  refine ⟨(coreRepPoly d).equiv p, ?_⟩
  rw [quadForm_nsKoopmanOp, norm_core_sq, LinearEquiv.symm_apply_apply]
  exact hp

/-- **The mainstream Navier–Stokes Hamiltonian is not a positive operator.** -/
theorem nsKoopmanOp_not_positive (i0 : Fin d) (hnu : 0 < S.nu) (hlam : 0 < S.lam i0) :
    ¬ ∀ x : polyGaussCore (d := d), 0 ≤ quadForm (nsKoopmanOp S) x := by
  intro hpos
  obtain ⟨x, hx⟩ := nsKoopmanOp_not_bounded_below S i0 hnu hlam 0
  have := hpos x
  simp only [neg_zero, zero_mul] at hx
  linarith

end

end BookProof.NsKoopman


/-!
# The Faris–Lavine comparison operator for the mainstream Navier–Stokes Hamiltonian

`BookProof.ChapterNsKoopman.Part1` shows that the Hamiltonian `H_NS` of the mainstream
Navier–Stokes system is unbounded below, so that the comparison operator `N` of the
Faris–Lavine criterion cannot be `H_NS` itself.  This part supplies a comparison operator that
does work and verifies, for the exact nonlinear Hamiltonian, the inequality the criterion
actually consumes.

Faris–Lavine (Theorem 1, as proved in `BookProof.ChapterFarisLavineCore`) asks for a positive
symmetric `N` on the domain of `H`, with `N + 1` onto and

```
|⟪x, i[H, N] x⟫| ≤ c ⟪x, N x⟫ .
```

*No positivity of `H` is required*, which is exactly why the criterion is the right instrument
for an indefinite `H_NS`.

The comparison operator is the **Leray energy**

```
N_E = multiplication by  E(u) = 1 + ‖u‖² = 1 + Σ_i u_i² ,
```

and the commutator is computed exactly:

* `kvn_comm_energy` — `i[H_NS, N_E] = multiplication by F·∇E = 2 Σ_i u_i F_i`;
* `fluxPoly_eq` — and by **Leray's energy identity** the advection and the pressure gradient
  drop out of `F·∇E` completely, leaving the viscous dissipation
  `F·∇E = −2ν Σ_i λ_i u_i² ≤ 0`;
* `commForm_kvn_energy_bound` — hence `|⟪x, i[H_NS, N_E] x⟫| ≤ 2νΛ ⟪x, N_E x⟫` with
  `Λ = max_i λ_i`: **the Faris–Lavine commutator inequality holds for the exact nonlinear
  Navier–Stokes Hamiltonian**, with a constant fixed by the viscosity and the largest Stokes
  eigenvalue of the truncation, and it holds *because* of the energy structure of the true
  nonlinearity — a Hamiltonian in which the advection were replaced by anything that does work
  on the velocity would fail it;
* `nsKoopman_esa_of_energy_comparison` — the resulting Faris–Lavine conclusion.  Its remaining
  hypothesis is the surjectivity of `N_E + 1` from the common domain, the one input of the
  criterion that the Gauss–polynomial core does not supply; it is carried as an explicit named
  hypothesis, never as an axiom.
* `nsTriad` — a non-vacuity witness: the Navier–Stokes Fourier **triad**
  `u̇₁ = −νλ₁u₁ + a u₂u₃`, `u̇₂ = −νλ₂u₂ + b u₃u₁`, `u̇₃ = −νλ₃u₃ + c u₁u₂` with `a + b + c = 0`
  is an `NsSystem`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsKoopman

open MvPolynomial
open BookProof.HermiteCore BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.GaussCoreQuadBounds

noncomputable section

variable {d : ℕ}

/-! ## 1. Gaussian integrals of a real multiplication operator -/

/-- The pointwise value of the integrand of `⟪p, g p⟫` for a real multiplication operator. -/
theorem eval_star_mul (g p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p * (g * p))).re
      = (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g).re
        * Complex.normSq (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  rw [map_mul, map_mul, eval_starP]
  set z := MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p
  set w := MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g
  have h : (starRingEnd ℂ) z * (w * z) = w * ((Complex.normSq z : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [h]
  simp [Complex.mul_re]

/-- Monotonicity of the expectation of a multiplication operator in its symbol. -/
theorem gpair_mul_mono {g s : MvPolynomial (Fin d) ℂ}
    (h : ∀ x : Vd d, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g).re
      ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) s).re) (p : MvPolynomial (Fin d) ℂ) :
    (gpair p (g * p)).re ≤ (gpair p (s * p)).re := by
  refine gaussInt_re_mono fun x => ?_
  rw [eval_star_mul, eval_star_mul]
  exact mul_le_mul_of_nonneg_right (h x) (Complex.normSq_nonneg _)

/-! ## 2. The Leray energy as a comparison operator -/

/-- The **Leray energy** `E(u) = 1 + ‖u‖²`, the comparison observable. -/
def energyPoly (d : ℕ) : MvPolynomial (Fin d) ℂ := 1 + ∑ i, X i * X i

theorem energyPoly_realCoeff : RealCoeff (energyPoly d) :=
  realCoeff_one.add (RealCoeff.sum fun i _ => (realCoeff_X i).mul (realCoeff_X i))

/-- **The comparison operator `N_E`**: multiplication by the Leray energy. -/
def energyOp (d : ℕ) : Module.End ℂ (MvPolynomial (Fin d) ℂ) := mulOp (energyPoly d)

theorem energyOp_polySym : PolySym (energyOp d) := mulOp_polySym energyPoly_realCoeff

/-- The value of the Leray energy at a real configuration. -/
theorem eval_energyPoly (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (energyPoly d)
      = ((1 + ∑ i, (x i) ^ 2 : ℝ) : ℂ) := by
  rw [energyPoly, map_add, map_one, map_sum, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPolynomial.eval_X]
  push_cast
  ring

theorem pderiv_energyPoly (i : Fin d) :
    pderiv i (energyPoly d) = (2 : ℂ) • X i := by
  classical
  have h1 : pderiv i (1 : MvPolynomial (Fin d) ℂ) = 0 := by simp
  rw [energyPoly, map_add, h1, zero_add, map_sum]
  rw [Finset.sum_eq_single i (fun j _ hj => by
    rw [pderiv_mul, pderiv_X_of_ne hj]
    simp) (fun h => absurd (Finset.mem_univ i) h)]
  rw [pderiv_mul, pderiv_X_self, one_mul, mul_one]
  module

variable (S : NsSystem d)

/-- The **energy flux** `F·∇E = 2 Σ_i u_i F_i` of the Navier–Stokes drift. -/
def fluxPoly : MvPolynomial (Fin d) ℂ :=
  ∑ i, ((-2 * S.nu * S.lam i : ℝ) : ℂ) • (X i * X i)

/-- **Leray's identity in the Hamiltonian**: in the energy flux of the drift the advection and
the pressure gradient cancel exactly, and only the viscous dissipation survives. -/
theorem fluxPoly_eq : ∑ i, drift S i * (pderiv i (energyPoly d)) = fluxPoly S := by
  have hterm : ∀ i : Fin d, drift S i * (pderiv i (energyPoly d))
      = ((-2 * S.nu * S.lam i : ℝ) : ℂ) • (X i * X i) + (2 : ℂ) • (X i * advOf S.bcoef i) := by
    intro i
    rw [pderiv_energyPoly, drift, add_mul, mul_smul_comm, mul_smul_comm, neg_mul, smul_mul_assoc]
    simp only [mul_comm (advOf S.bcoef i) (X i)]
    push_cast
    module
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.smul_sum,
    S.leray, smul_zero, add_zero, fluxPoly]

theorem eval_fluxPoly (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (fluxPoly S)
      = ((-2 * S.nu * ∑ i, S.lam i * (x i) ^ 2 : ℝ) : ℂ) := by
  rw [fluxPoly, map_sum,
    show ((-2 * S.nu * ∑ i, S.lam i * (x i) ^ 2 : ℝ) : ℂ)
        = ∑ i, (((-2 * S.nu * S.lam i * (x i) ^ 2 : ℝ)) : ℂ) by
      rw [← Complex.ofReal_sum]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, map_mul, MvPolynomial.eval_X]
  push_cast
  ring

/-! ## 3. The commutator of the Hamiltonian with the comparison operator -/

/-- **The commutator identity** `[H_NS, N_E] = −i · (F·∇E)`, i.e. `i[H_NS, N_E]` is
multiplication by the energy flux. -/
theorem kvn_comm_energy (p : MvPolynomial (Fin d) ℂ) :
    kvnPoly S (energyPoly d * p) - energyPoly d * kvnPoly S p
      = (-Complex.I) • (fluxPoly S * p) := by
  have hder : ∀ i : Fin d, derOp i (energyPoly d * p)
      = pderiv i (energyPoly d) * p + energyPoly d * derOp i p := by
    intro i
    rw [derOp_apply, derOp_apply, pderiv_mul]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  rw [kvnPoly_apply, kvnPoly_apply]
  have hsum : (∑ i, drift S i * derOp i (energyPoly d * p))
      = fluxPoly S * p + energyPoly d * ∑ i, drift S i * derOp i p := by
    have : ∀ i : Fin d, drift S i * derOp i (energyPoly d * p)
        = (drift S i * pderiv i (energyPoly d)) * p
          + energyPoly d * (drift S i * derOp i p) := by
      intro i
      rw [hder i]
      ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, ← Finset.sum_mul,
      fluxPoly_eq, ← Finset.mul_sum]
  rw [hsum]
  simp only [mul_add, mul_smul_comm]
  module

/-! ## 4. The Faris–Lavine commutator inequality -/

/-- The comparison operator on the Gauss–polynomial core of `L²(ℝᵈ)`. -/
def nsEnergyOp : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype.comp ((coreRepPoly d).op (energyOp d))

theorem nsEnergyOp_symmetricOn : SymmetricOn (polyGaussCore (d := d)) (nsEnergyOp (d := d)) :=
  (coreRepPoly d).symmetricOn_op energyOp_polySym

theorem nsEnergyOp_apply (x : polyGaussCore (d := d)) :
    nsEnergyOp (d := d) x = pgLp (energyPoly d * (coreRepPoly d).equiv.symm x) :=
  (coreRepPoly d).coe_op (energyOp d) x

theorem quadForm_nsEnergyOp (x : polyGaussCore (d := d)) :
    quadForm (nsEnergyOp (d := d)) x
      = (gpair ((coreRepPoly d).equiv.symm x)
          (energyPoly d * (coreRepPoly d).equiv.symm x)).re := by
  rw [quadForm, nsEnergyOp_apply, coe_core_eq, inner_pgLp_pgLp]
  rfl

/-- **`N_E ≥ 1`**: the comparison operator dominates the norm, as Faris–Lavine requires. -/
theorem nsEnergyOp_quadForm_ge (x : polyGaussCore (d := d)) :
    ‖(x : L2d d)‖ ^ 2 ≤ quadForm (nsEnergyOp (d := d)) x := by
  set p := (coreRepPoly d).equiv.symm x
  have h1 : ‖(x : L2d d)‖ ^ 2 = (gpair p ((1 : MvPolynomial (Fin d) ℂ) * p)).re := by
    rw [norm_core_sq, one_mul]
  rw [h1, quadForm_nsEnergyOp]
  refine gpair_mul_mono (fun y => ?_) p
  rw [eval_energyPoly]
  simp only [map_one, Complex.one_re, Complex.ofReal_re]
  have : (0 : ℝ) ≤ ∑ i, (y i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem nsEnergyOp_quadForm_nonneg (x : polyGaussCore (d := d)) :
    0 ≤ quadForm (nsEnergyOp (d := d)) x :=
  le_trans (by positivity) (nsEnergyOp_quadForm_ge x)

/-- The commutator form of the Hamiltonian against the comparison operator is the expectation of
the energy flux. -/
theorem commForm_kvn_energy (x : polyGaussCore (d := d)) :
    commForm (nsKoopmanOp S) (nsEnergyOp (d := d)) x
      = (gpair ((coreRepPoly d).equiv.symm x)
          (fluxPoly S * (coreRepPoly d).equiv.symm x)).re := by
  set p := (coreRepPoly d).equiv.symm x with hp
  have hH : (nsKoopmanOp S) x = pgLp (kvnPoly S p) := (coreRepPoly d).coe_op (kvnPoly S) x
  have hN : nsEnergyOp (d := d) x = pgLp (energyPoly d * p) := nsEnergyOp_apply x
  have h1 : (inner ℂ ((nsKoopmanOp S) x) (nsEnergyOp (d := d) x) : ℂ)
      = gpair p (kvnPoly S (energyPoly d * p)) := by
    rw [hH, hN, ← gpair_eq_inner, gpair_kvn_symm]
  have h2 : (inner ℂ (nsEnergyOp (d := d) x) ((nsKoopmanOp S) x) : ℂ)
      = gpair p (energyPoly d * kvnPoly S p) := by
    rw [hH, hN, ← gpair_eq_inner]
    exact energyOp_polySym p (kvnPoly S p)
  rw [commForm, h1, h2, ← gpair_sub_right, kvn_comm_energy, gpair_smul_right]
  simp [Complex.mul_re, Complex.mul_im]

/-- **The Faris–Lavine commutator inequality for the exact nonlinear Navier–Stokes
Hamiltonian**: `|⟪x, i[H_NS, N_E] x⟫| ≤ 2νΛ ⟪x, N_E x⟫`, where `Λ` bounds the Stokes
eigenvalues.  It holds because the advection and the pressure gradient do no work — Leray's
identity — so that the whole commutator is the (sign-definite) viscous dissipation. -/
theorem commForm_kvn_energy_bound {L : ℝ} (hL : ∀ i, S.lam i ≤ L) (hL0 : 0 ≤ L)
    (x : polyGaussCore (d := d)) :
    |commForm (nsKoopmanOp S) (nsEnergyOp (d := d)) x|
      ≤ (2 * S.nu * L) * quadForm (nsEnergyOp (d := d)) x := by
  set p := (coreRepPoly d).equiv.symm x with hp
  have hnu := S.nu_nonneg
  have hlam := S.lam_nonneg
  -- the expectation of a real multiple of the energy
  have hscal : ∀ t : ℝ, (gpair p ((((t : ℝ) : ℂ) • energyPoly d) * p)).re
      = t * (gpair p (energyPoly d * p)).re := by
    intro t
    rw [smul_mul_assoc, gpair_smul_right]
    simp
  -- the pointwise bounds on the energy flux
  have hpt : ∀ y : Vd d,
      (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (fluxPoly S)).re
          ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
              ((((2 * S.nu * L : ℝ) : ℂ) • energyPoly d))).re
        ∧ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
              ((((-(2 * S.nu * L) : ℝ) : ℂ) • energyPoly d))).re
          ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (fluxPoly S)).re := by
    intro y
    have hflux : (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (fluxPoly S)).re
        = -2 * S.nu * ∑ i, S.lam i * (y i) ^ 2 := by
      rw [eval_fluxPoly, Complex.ofReal_re]
    have hE : ∀ t : ℝ, (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
        ((((t : ℝ) : ℂ) • energyPoly d))).re = t * (1 + ∑ i, (y i) ^ 2) := by
      intro t
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, eval_energyPoly,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    have hs0 : 0 ≤ ∑ i, S.lam i * (y i) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (sq_nonneg _)
    have hsq : (0 : ℝ) ≤ ∑ i, (y i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsL : ∑ i, S.lam i * (y i) ^ 2 ≤ L * (1 + ∑ i, (y i) ^ 2) := by
      have h1 : ∑ i, S.lam i * (y i) ^ 2 ≤ ∑ i, L * (y i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hL i) (sq_nonneg _)
      have h2 : ∑ i, L * (y i) ^ 2 = L * ∑ i, (y i) ^ 2 := by rw [Finset.mul_sum]
      nlinarith [hL0, hsq]
    refine ⟨?_, ?_⟩
    · rw [hflux, hE]
      nlinarith [hnu, hL0, hs0, hsq]
    · rw [hflux, hE]
      nlinarith [hnu, hL0, hsL, hsq]
  have hQ : 0 ≤ quadForm (nsEnergyOp (d := d)) x := nsEnergyOp_quadForm_nonneg x
  rw [commForm_kvn_energy, quadForm_nsEnergyOp, abs_le]
  constructor
  · have := gpair_mul_mono (fun y => (hpt y).2) p
    rw [hscal] at this
    rw [quadForm_nsEnergyOp] at hQ
    linarith
  · have := gpair_mul_mono (fun y => (hpt y).1) p
    rw [hscal] at this
    linarith

/-- **Faris–Lavine for the mainstream Navier–Stokes Hamiltonian.**  With the Leray energy as
comparison operator, all the inequalities of the criterion are proved above; the one remaining
input is the surjectivity of `N_E + 1` on the common domain, which is carried here as an
explicit hypothesis. -/
theorem nsKoopman_esa_of_energy_comparison {L : ℝ} (hL : ∀ i, S.lam i ≤ L) (hL0 : 0 ≤ L)
    (hsurj : ∀ f : L2d d, ∃ x : polyGaussCore (d := d),
      nsEnergyOp (d := d) x + (x : L2d d) = f) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (nsKoopmanOp S) :=
  essentiallySelfAdjointOn_of_farisLavine (nsKoopmanOp S) (nsEnergyOp (d := d)) (2 * S.nu * L)
    (nsKoopmanOp_symmetricOn S) nsEnergyOp_symmetricOn
    (mul_nonneg (by linarith [S.nu_nonneg]) hL0) nsEnergyOp_quadForm_nonneg hsurj
    (commForm_kvn_energy_bound S hL hL0)

/-! ## 5. A non-vacuity witness: the Navier–Stokes Fourier triad -/

/-- The structure constants of the Navier–Stokes **triad**
`u̇₁ = −νλ₁u₁ + a u₂u₃`, `u̇₂ = −νλ₂u₂ + b u₃u₁`, `u̇₃ = −νλ₃u₃ + c u₁u₂`. -/
def triadCoef (a b c : ℝ) : Fin 3 → Fin 3 → Fin 3 → ℝ := fun i j k =>
  if i = 0 ∧ j = 1 ∧ k = 2 then a
  else if i = 1 ∧ j = 2 ∧ k = 0 then b
  else if i = 2 ∧ j = 0 ∧ k = 1 then c
  else 0

theorem triadCoef_zero (a b c : ℝ) (j k : Fin 3) :
    triadCoef a b c 0 j k = if j = 1 ∧ k = 2 then a else 0 := by
  fin_cases j <;> fin_cases k <;> simp [triadCoef, Fin.ext_iff]

theorem triadCoef_one (a b c : ℝ) (j k : Fin 3) :
    triadCoef a b c 1 j k = if j = 2 ∧ k = 0 then b else 0 := by
  fin_cases j <;> fin_cases k <;> simp [triadCoef, Fin.ext_iff]

theorem triadCoef_two (a b c : ℝ) (j k : Fin 3) :
    triadCoef a b c 2 j k = if j = 0 ∧ k = 1 then c else 0 := by
  fin_cases j <;> fin_cases k <;> simp [triadCoef, Fin.ext_iff]

theorem advOf_triad_zero (a b c : ℝ) :
    advOf (triadCoef a b c) 0 = ((a : ℝ) : ℂ) • (X 1 * X 2) := by
  simp only [advOf, Fin.sum_univ_three, triadCoef_zero]
  norm_num [Fin.ext_iff]

theorem advOf_triad_one (a b c : ℝ) :
    advOf (triadCoef a b c) 1 = ((b : ℝ) : ℂ) • (X 2 * X 0) := by
  simp only [advOf, Fin.sum_univ_three, triadCoef_one]
  norm_num [Fin.ext_iff]

theorem advOf_triad_two (a b c : ℝ) :
    advOf (triadCoef a b c) 2 = ((c : ℝ) : ℂ) • (X 0 * X 1) := by
  simp only [advOf, Fin.sum_univ_three, triadCoef_two]
  norm_num [Fin.ext_iff]

/-- **The Navier–Stokes triad is a mainstream Navier–Stokes system**: the resonant three-mode
interaction of the Fourier-space Euler/Navier–Stokes nonlinearity, energy-conserving
(`a + b + c = 0`) and volume-preserving. -/
def nsTriad (nu : ℝ) (hnu : 0 ≤ nu) (lam : Fin 3 → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (a b c : ℝ) (habc : a + b + c = 0) : NsSystem 3 where
  nu := nu
  lam := lam
  bcoef := triadCoef a b c
  nu_nonneg := hnu
  lam_nonneg := hlam
  leray := by
    have hC : (C ((a : ℝ) : ℂ) + C ((b : ℝ) : ℂ) + C ((c : ℝ) : ℂ)
        : MvPolynomial (Fin 3) ℂ) = 0 := by
      rw [← map_add, ← map_add,
        show (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) + ((c : ℝ) : ℂ)) = (((a + b + c : ℝ)) : ℂ) by
          push_cast; ring, habc]
      simp
    simp only [Fin.sum_univ_three, advOf_triad_zero, advOf_triad_one, advOf_triad_two,
      MvPolynomial.smul_eq_C_mul]
    linear_combination (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) ℂ) * hC
  liouville := by
    simp [Fin.sum_univ_three, advOf_triad_zero, advOf_triad_one, advOf_triad_two,
      MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_X, Fin.ext_iff]

end

end BookProof.NsKoopman


