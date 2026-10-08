-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordBasis_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordBasis_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:48:11.014892+00:00
-- url     : https://prove2.me/theorems/1b3f8f33-6e29-48ef-99c6-afe92ba42aab
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordBasis source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordBasis

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordBasis
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumford_p0

set_option autoImplicit false




/-!
# The rank-two basis of a smooth sextic affine ring

For a model `Y² = f(X)`, every element of the affine coordinate ring is
written uniquely as `p(X) + q(X)Y`.  This is the coefficient API used by
the Mumford ideal and normal-form layers.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

def xClassHom : K[X] →+* CoordinateRing M :=
  AdjoinRoot.of (curvePoly M)

@[simp] theorem xClassHom_apply (p : K[X]) :
    xClassHom M p = xClass M p := rfl

@[simp] theorem xClass_zero : xClass M 0 = 0 := by
  exact map_zero (xClassHom M)

@[simp] theorem xClass_one : xClass M 1 = 1 := by
  exact map_one (xClassHom M)

@[simp] theorem xClass_add (p q : K[X]) :
    xClass M (p + q) = xClass M p + xClass M q := by
  exact map_add (xClassHom M) p q

@[simp] theorem xClass_sub (p q : K[X]) :
    xClass M (p - q) = xClass M p - xClass M q := by
  exact map_sub (xClassHom M) p q

@[simp] theorem xClass_neg (p : K[X]) :
    xClass M (-p) = -xClass M p := by
  exact map_neg (xClassHom M) p

@[simp] theorem xClass_mul (p q : K[X]) :
    xClass M (p * q) = xClass M p * xClass M q := by
  exact map_mul (xClassHom M) p q

@[simp] theorem xClass_pow (p : K[X]) (n : ℕ) :
    xClass M (p ^ n) = xClass M p ^ n := by
  exact map_pow (xClassHom M) p n

def normalPoly : CoordinateRing M →ₗ[K[X]] K[X][X] :=
  AdjoinRoot.modByMonicHom (curvePoly_monic M)

def coeff0 : CoordinateRing M →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 0).comp (normalPoly M)

def coeffY : CoordinateRing M →ₗ[K[X]] K[X] :=
  (Polynomial.lcoeff K[X] 1).comp (normalPoly M)

@[simp] theorem normalPoly_mk (g : K[X][X]) :
    normalPoly M (mk M g) = g %ₘ curvePoly M := by
  rfl

@[simp] theorem coeff0_mk (g : K[X][X]) :
    coeff0 M (mk M g) = (g %ₘ curvePoly M).coeff 0 := by
  rfl

@[simp] theorem coeffY_mk (g : K[X][X]) :
    coeffY M (mk M g) = (g %ₘ curvePoly M).coeff 1 := by
  rfl

private theorem degree_curvePoly : (curvePoly M).degree = 2 := by
  rw [degree_eq_natDegree (curvePoly_monic M).ne_zero,
    curvePoly_natDegree]
  norm_num

theorem normalPoly_eq_C_add_C_mul_X (z : CoordinateRing M) :
    normalPoly M z = C (coeff0 M z) + C (coeffY M z) * X := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      change g %ₘ curvePoly M =
        C ((g %ₘ curvePoly M).coeff 0) +
          C ((g %ₘ curvePoly M).coeff 1) * X
      have hsum := Polynomial.sum_modByMonic_coeff
        (p := g) (q := curvePoly M) (curvePoly_monic M)
        (n := 2) (by rw [degree_curvePoly]; norm_num)
      rw [Fin.sum_univ_two] at hsum
      simpa [← Polynomial.C_mul_X_pow_eq_monomial] using hsum.symm

theorem recompose (z : CoordinateRing M) :
    xClass M (coeff0 M z) + xClass M (coeffY M z) * yClass M = z := by
  induction z using AdjoinRoot.induction_on with
  | ih g =>
      calc
        xClass M (coeff0 M (AdjoinRoot.mk (curvePoly M) g)) +
              xClass M (coeffY M (AdjoinRoot.mk (curvePoly M) g)) * yClass M =
            AdjoinRoot.mk (curvePoly M)
              (C (coeff0 M (AdjoinRoot.mk (curvePoly M) g)) +
                C (coeffY M (AdjoinRoot.mk (curvePoly M) g)) * X) := by
                  simp only [xClass, yClass, mk, map_add, map_mul,
                    AdjoinRoot.mk_C, AdjoinRoot.mk_X]
        _ = AdjoinRoot.mk (curvePoly M)
              (normalPoly M (AdjoinRoot.mk (curvePoly M) g)) := by
                rw [normalPoly_eq_C_add_C_mul_X]
        _ = AdjoinRoot.mk (curvePoly M) g :=
          AdjoinRoot.mk_leftInverse (curvePoly_monic M)
            (AdjoinRoot.mk (curvePoly M) g)

@[simp] theorem coeff0_xClass (p : K[X]) :
    coeff0 M (xClass M p) = p := by
  change (C p %ₘ curvePoly M).coeff 0 = p
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)

@[simp] theorem coeffY_xClass (p : K[X]) :
    coeffY M (xClass M p) = 0 := by
  change (C p %ₘ curvePoly M).coeff 1 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · exact degree_C_le.trans_lt (by rw [degree_curvePoly]; norm_num)

@[simp] theorem coeff0_yClass : coeff0 M (yClass M) = 0 := by
  change (X %ₘ curvePoly M).coeff 0 = 0
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num

@[simp] theorem coeffY_yClass : coeffY M (yClass M) = 1 := by
  change (X %ₘ curvePoly M).coeff 1 = 1
  rw [(modByMonic_eq_self_iff (curvePoly_monic M)).mpr]
  · simp
  · rw [degree_X, degree_curvePoly]
    norm_num

theorem eq_iff_coeff (z w : CoordinateRing M) :
    z = w ↔ coeff0 M z = coeff0 M w ∧ coeffY M z = coeffY M w := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, hY⟩
    rw [← recompose M z, ← recompose M w, h0, hY]

/-! ## Hyperelliptic conjugation and the quadratic norm -/

private theorem neg_y_relation :
    (curvePoly M).eval₂ (AdjoinRoot.of (curvePoly M)) (-(yClass M)) = 0 := by
  change (X ^ 2 - C M.f).eval₂
      (AdjoinRoot.of (curvePoly M)) (-(yClass M)) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change (-(yClass M)) ^ 2 - xClass M M.f = 0
  rw [neg_sq, yClass_sq]
  exact sub_self _

def conjugate : CoordinateRing M →+* CoordinateRing M :=
  AdjoinRoot.lift (AdjoinRoot.of (curvePoly M)) (-(yClass M))
    (neg_y_relation M)

@[simp] theorem conjugate_xClass (p : K[X]) :
    conjugate M (xClass M p) = xClass M p := by
  change conjugate M (AdjoinRoot.of (curvePoly M) p) =
    AdjoinRoot.of (curvePoly M) p
  exact AdjoinRoot.lift_of (neg_y_relation M)

@[simp] theorem conjugate_yClass :
    conjugate M (yClass M) = -(yClass M) := by
  exact AdjoinRoot.lift_root (neg_y_relation M)

theorem conjugate_involutive : Function.Involutive (conjugate M) := by
  have hcomp : (conjugate M).comp (conjugate M) =
      RingHom.id (CoordinateRing M) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro k
        change conjugate M (conjugate M (xClass M (C k))) = xClass M (C k)
        rw [conjugate_xClass, conjugate_xClass]
      · change conjugate M (conjugate M (xClass M X)) = xClass M X
        rw [conjugate_xClass, conjugate_xClass]
    · change conjugate M (conjugate M (yClass M)) = yClass M
      rw [conjugate_yClass, map_neg, conjugate_yClass, neg_neg]
  intro z
  exact DFunLike.congr_fun hcomp z

def norm (z : CoordinateRing M) : CoordinateRing M :=
  z * conjugate M z

theorem norm_recompose (p q : K[X]) :
    norm M (xClass M p + xClass M q * yClass M) =
      xClass M (p ^ 2 - q ^ 2 * M.f) := by
  simp only [norm, map_add, map_mul, conjugate_xClass, conjugate_yClass]
  calc
    (xClass M p + xClass M q * yClass M) *
          (xClass M p + xClass M q * -yClass M) =
        xClass M p ^ 2 - xClass M q ^ 2 * yClass M ^ 2 := by ring
    _ = xClass M p ^ 2 - xClass M q ^ 2 * xClass M M.f := by
      rw [yClass_sq]
    _ = xClass M (p ^ 2 - q ^ 2 * M.f) := by
      change
        AdjoinRoot.of (curvePoly M) p ^ 2 -
            AdjoinRoot.of (curvePoly M) q ^ 2 *
              AdjoinRoot.of (curvePoly M) M.f =
          AdjoinRoot.of (curvePoly M) (p ^ 2 - q ^ 2 * M.f)
      simp only [map_sub, map_mul, map_pow]

end

end MazurProof.SexticMumford


