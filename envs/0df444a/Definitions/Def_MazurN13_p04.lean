-- Prove2me | Definitions.Def_MazurN13_p04
-- name    : MazurN13_p04
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-08T00:11:28.702986+00:00
-- url     : https://prove2.me/theorems/8b04f489-5163-433b-9009-e421bb9f6425
-- title:
--   Mazur order 13 (Huang FLT port), part 4/33
-- statement:
--   Part 4 of 33 of a machine-checked Lean proof that no elliptic curve over $\mathbb{Q}$ has a rational point of exact order $13$ (the case $N=13$ of Mazur's torsion theorem). The chain as a whole proves that the only rational affine points of the genus-two curve $Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$ (a model of $X_1(13)$) have $X\in\{0,-1\}$ (cusps); the final result is `MazurProof.N13ConstructedRationalPointTheorem.affine_x_is_cuspidal` in part {N}.
--
--   This part is not a single definition: it is a verbatim, sorry-free slice of Xiang Huang's Lean development, ported to this Mathlib and split into compile-sized pieces, each importing the previous part. It contains the modules:
--
--   - `FLT.Assumptions.MazurProof.SexticMumfordPrincipalScale`
--   - `FLT.Assumptions.MazurProof.SexticMumfordRecover`
--   - `FLT.Assumptions.MazurProof.N13MumfordRigidity`
--   - `FLT.Assumptions.MazurProof.SexticMumfordGroup`
--   - `FLT.Assumptions.MazurProof.SexticMumfordPrimitivePart`
--   - `FLT.Assumptions.MazurProof.SexticMumfordCantorReduction`
--   - `FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction`
--
--   Port notes: API drift fixes only (transparency options, renamed lemmas, explicit instances); local notations expanded, `private` removed.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT commit 51bbb4f, directory FLT/Assumptions/MazurProof (N13* and SexticMumford* modules and their dependencies)

import Mathlib
import Definitions.Def_MazurN13_p03
set_option maxHeartbeats 1000000

-- module FLT.Assumptions.MazurProof.SexticMumfordPrincipalScale
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordPrincipalScale =====
section

/-!
# Cancelling a principal scale between Mumford ideals

If a principal fractional-ideal relation scales the first polynomial
generator to a unit multiple of the second, the associated integral
Mumford ideals satisfy the cross-multiplied equality.  Contracting that
equality to the polynomial subring recovers equality of the monic
`u`-polynomials.
-/

open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u v

theorem scaled_ideal_eq_of_principal_scale
    {R : Type u} [CommRing R]
    {L : Type v} [Field L] [Algebra R L] [IsFractionRing R L]
    (I₁ I₂ : Ideal R) (α : Lˣ) (u₁ u₂ c d : R)
    (hIdeal :
      (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (α : L) = I₂)
    (hscale : (α : L) * algebraMap R L u₁ =
      algebraMap R L u₂ * algebraMap R L c)
    (hunit : c * d = 1) :
    I₁ * Ideal.span ({u₂} : Set R) =
      I₂ * Ideal.span ({u₁} : Set R) := by
  apply (FractionalIdeal.coeIdeal_inj (K := L)).mp
  have hc : IsUnit c := IsUnit.of_mul_eq_one d hunit
  have hspan_c :
      FractionalIdeal.spanSingleton R⁰ (algebraMap R L c) = 1 := by
    calc
      FractionalIdeal.spanSingleton R⁰ (algebraMap R L c) =
          (Ideal.span ({c} : Set R) : FractionalIdeal R⁰ L) :=
        (FractionalIdeal.coeIdeal_span_singleton c).symm
      _ = (⊤ : Ideal R) := by
        rw [Ideal.span_singleton_eq_top.mpr hc]
      _ = 1 := by simp
  calc
    ((I₁ * Ideal.span ({u₂} : Set R) : Ideal R) :
          FractionalIdeal R⁰ L) =
        (I₁ : FractionalIdeal R⁰ L) *
          (Ideal.span ({u₂} : Set R) : FractionalIdeal R⁰ L) :=
      FractionalIdeal.coeIdeal_mul I₁ (Ideal.span ({u₂} : Set R))
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₂) := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₂) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L c) := by
      rw [hspan_c, mul_one]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰
            (algebraMap R L u₂ * algebraMap R L c) := by
      rw [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰
            ((α : L) * algebraMap R L u₁) := by
      rw [hscale]
    _ =
        (I₁ : FractionalIdeal R⁰ L) *
          (FractionalIdeal.spanSingleton R⁰ (α : L) *
            FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₁)) := by
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton]
    _ =
        ((I₁ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (α : L)) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₁) := by
      rw [mul_assoc]
    _ =
        (I₂ : FractionalIdeal R⁰ L) *
          FractionalIdeal.spanSingleton R⁰ (algebraMap R L u₁) := by
      rw [hIdeal]
    _ =
        (I₂ : FractionalIdeal R⁰ L) *
          (Ideal.span ({u₁} : Set R) : FractionalIdeal R⁰ L) := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        ((I₂ * Ideal.span ({u₁} : Set R) : Ideal R) :
          FractionalIdeal R⁰ L) := by
      exact
        (FractionalIdeal.coeIdeal_mul I₂
          (Ideal.span ({u₁} : Set R))).symm

theorem mumford_u_eq_of_principal_scale
    {K : Type u} [Field K] (M : Model K)
    (D₁ D₂ : SemiMumford M) (α : (FunctionField M)ˣ)
    (c d : CoordinateRing M)
    (hIdeal :
      mumfordIdealUnit M D₁ *
          toPrincipalIdeal (CoordinateRing M) (FunctionField M) α =
        mumfordIdealUnit M D₂)
    (hscale :
      (α : FunctionField M) *
          algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₁.u) =
        algebraMap (CoordinateRing M) (FunctionField M) (xClass M D₂.u) *
          algebraMap (CoordinateRing M) (FunctionField M) c)
    (hunit : c * d = 1) :
    D₁.u = D₂.u := by
  have hfrac := congrArg
    (fun U : InvFrac M =>
      (U : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) hIdeal
  rw [Units.val_mul, coe_toPrincipalIdeal,
    coe_mumfordIdealUnit, coe_mumfordIdealUnit] at hfrac
  have hscaled := scaled_ideal_eq_of_principal_scale
    (mumfordIdeal M D₁.u D₁.v)
    (mumfordIdeal M D₂.u D₂.v)
    α (xClass M D₁.u) (xClass M D₂.u) c d
    hfrac hscale hunit
  have h₁₂ := u_dvd_of_scaled_mumfordIdeal_eq
    M D₁.u D₁.v D₂.u D₂.v hscaled
  have h₂₁ := u_dvd_of_scaled_mumfordIdeal_eq
    M D₂.u D₂.v D₁.u D₁.v hscaled.symm
  exact Polynomial.eq_of_monic_of_associated D₁.u_monic D₂.u_monic
    (associated_of_dvd_dvd h₁₂ h₂₁)

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordRecover
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordRecover =====
section

/-!
# Recovering Mumford polynomials from their ideals

Contraction to the polynomial subring recovers the monic polynomial `u` from
the ideal `(u, Y - v)`, and the canonical remainder condition then recovers
`v`.
-/

open Polynomial

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

variable (M : Model K)

theorem u_eq_of_mumfordIdeal_eq {D₁ D₂ : SemiMumford M}
    (h : mumfordIdeal M D₁.u D₁.v = mumfordIdeal M D₂.u D₂.v) :
    D₁.u = D₂.u := by
  have hc := congrArg (fun I : Ideal (CoordinateRing M) ↦
    I.comap (xClassHom M)) h
  rw [mumfordIdeal_comap_base M D₁, mumfordIdeal_comap_base M D₂] at hc
  exact eq_of_monic_of_associated D₁.u_monic D₂.u_monic
    (Ideal.span_singleton_eq_span_singleton.mp hc)

theorem v_eq_of_mumfordIdeal_eq_of_u_eq {D₁ D₂ : SemiMumford M}
    (hu : D₁.u = D₂.u)
    (h : mumfordIdeal M D₁.u D₁.v = mumfordIdeal M D₂.u D₂.v) :
    D₁.v = D₂.v := by
  have hy₂ : ySubClass M D₂.v ∈ mumfordIdeal M D₁.u D₁.v := by
    rw [h]
    exact Ideal.subset_span (by simp)
  have hker : ySubClass M D₂.v ∈ RingHom.ker (mumfordEval M D₁) := by
    rw [ker_mumfordEval M D₁]
    exact hy₂
  have heval : mumfordEval M D₁ (ySubClass M D₂.v) = 0 :=
    RingHom.mem_ker.mp hker
  have hquot : Ideal.Quotient.mk (Ideal.span ({D₁.u} : Set K[X]))
      (D₁.v - D₂.v) = 0 := by
    simpa only [ySubClass, map_sub, mumfordEval_yClass,
      mumfordEval_xClass, sub_eq_zero] using heval
  have hdvd : D₁.u ∣ D₁.v - D₂.v :=
    Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
  have hmod : D₁.v % D₁.u = D₂.v % D₁.u :=
    mod_eq_of_dvd_sub hdvd
  rw [D₁.v_reduced, hu, D₂.v_reduced] at hmod
  exact hmod

theorem uv_eq_of_mumfordIdeal_eq {D₁ D₂ : SemiMumford M}
    (h : mumfordIdeal M D₁.u D₁.v = mumfordIdeal M D₂.u D₂.v) :
    D₁.u = D₂.u ∧ D₁.v = D₂.v := by
  have hu := u_eq_of_mumfordIdeal_eq M h
  exact ⟨hu, v_eq_of_mumfordIdeal_eq_of_u_eq M hu h⟩

theorem mumford_eq_of_ideal_eq_of_nInf_eq {D₁ D₂ : Mumford M}
    (hIdeal : mumfordIdeal M D₁.u D₁.v = mumfordIdeal M D₂.u D₂.v)
    (hInf : D₁.nInf = D₂.nInf) : D₁ = D₂ := by
  obtain ⟨hu, hv⟩ := uv_eq_of_mumfordIdeal_eq M
    (D₁ := D₁.toSemi) (D₂ := D₂.toSemi) hIdeal
  cases D₁
  cases D₂
  simp_all

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.N13MumfordRigidity
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13MumfordRigidity =====
section

/-!
# Constant-principal rigidity for balanced `X₁(13)` Mumford data

Once a principal multiplier between two balanced representatives is known to
be constant, its fractional ideal and its order at the positive infinity are
both trivial.  The generic ideal-kernel calculation then recovers `u`, `v`,
and the infinity coordinate.

The remaining normal-form uniqueness problem is therefore geometric: prove
that a function with the relevant small pole bounds is constant.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13Mumford

open SexticMumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem principal_between_balanced_of_constant
    {D₁ D₂ : Mumford K} {α : (FunctionField K)ˣ}
    (c : Kˣ)
    (hα : α = N13Infinity.functionConstUnit K c)
    (hIdeal :
      mumfordIdealUnit (model K) D₁.toSemi *
          toPrincipalIdeal (CoordinateRing K) (FunctionField K) α =
        mumfordIdealUnit (model K) D₂.toSemi)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N13Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    D₁ = D₂ := by
  subst α
  have hUnits :
      mumfordIdealUnit (model K) D₁.toSemi =
        mumfordIdealUnit (model K) D₂.toSemi := by
    simpa only [N13Infinity.principalIdeal_functionConstUnit, mul_one] using
      hIdeal
  have hFrac := congrArg
    (fun I : InvFrac (model K) ↦
      (I : FractionalIdeal (CoordinateRing K)⁰ (FunctionField K))) hUnits
  simp only [coe_mumfordIdealUnit] at hFrac
  have hIdeal' :
      mumfordIdeal (model K) D₁.u D₁.v =
        mumfordIdeal (model K) D₂.u D₂.v :=
    FractionalIdeal.coeIdeal_inj.mp hFrac
  have hInf' :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) := by
    simpa only [N13Infinity.ordPlus_functionConstUnit, mul_one] using hInf
  have hz : ((D₁.nInf : ℤ) - 1) = ((D₂.nInf : ℤ) - 1) :=
    Multiplicative.ofAdd.injective hInf'
  have hn : D₁.nInf = D₂.nInf := by omega
  exact mumford_eq_of_ideal_eq_of_nInf_eq (model K) hIdeal' hn

end

end MazurProof.N13Mumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordGroup
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordGroup =====
section

/-!
# The Mumford group law from oriented Picard normal forms

Given unique balanced Mumford representatives of the oriented Picard classes,
transport the ambient abelian group structure to those representatives.
-/

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

class NormalFormData (O : outParam (InfinityOrder M)) : Prop where
  existsUnique : ∀ c : ConcretePic M O,
    ∃! D : Mumford M, classOf M O D = c

def normalize [NormalFormData M O] (c : ConcretePic M O) : Mumford M :=
  Classical.choose (NormalFormData.existsUnique c)

@[simp]
theorem classOf_normalize [NormalFormData M O] (c : ConcretePic M O) :
    classOf M O (normalize M O c) = c :=
  (Classical.choose_spec (NormalFormData.existsUnique c)).1

theorem normalize_eq_of_class [NormalFormData M O]
    (c : ConcretePic M O) (D : Mumford M) (hD : classOf M O D = c) :
    normalize M O c = D := by
  exact ((Classical.choose_spec (NormalFormData.existsUnique c)).2 D hD).symm

def normalFormEquiv [NormalFormData M O] : Mumford M ≃ ConcretePic M O where
  toFun := classOf M O
  invFun := normalize M O
  left_inv D := by
    exact normalize_eq_of_class M O (classOf M O D) D rfl
  right_inv := classOf_normalize M O

/-- The group law is inherited from the oriented Picard group.  The
orientation in `NormalFormData` is an output parameter, so this instance is
selected only after the oriented normal-form data have been fixed. -/
noncomputable instance instAddCommGroupMumford [NormalFormData M O] :
    AddCommGroup (Mumford M) :=
  Equiv.addCommGroup (normalFormEquiv M O)

def classEquiv [NormalFormData M O] : Mumford M ≃+ ConcretePic M O :=
  Equiv.addEquiv (normalFormEquiv M O)

@[simp]
theorem classEquiv_apply [NormalFormData M O] (D : Mumford M) :
    classEquiv M O D = classOf M O D := by
  rfl

@[simp]
theorem classOf_add [NormalFormData M O] (D E : Mumford M) :
    classOf M O (D + E) = classOf M O D + classOf M O E := by
  simpa only [classEquiv_apply] using (classEquiv M O).map_add D E

@[simp]
theorem classOf_neg [NormalFormData M O] (D : Mumford M) :
    classOf M O (-D) = -classOf M O D := by
  simpa only [classEquiv_apply] using (classEquiv M O).map_neg D

@[simp]
theorem classOf_nsmul [NormalFormData M O] (n : ℕ) (D : Mumford M) :
    classOf M O (n • D) = n • classOf M O D := by
  simpa only [classEquiv_apply] using map_nsmul (classEquiv M O) n D

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordPrimitivePart
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordPrimitivePart =====
section

/-!
# Primitive content of an integral sextic ideal

Every integral ideal in the quadratic coordinate ring has a polynomial
content: the common principal ideal generated by all of its `Y`
coefficients.  Dividing by that content is implemented as a colon ideal.
This gives a primitive integral ideal structurally, without enumeration or
Riemann--Roch.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K)

/-! ## The coefficient-content ideal -/

/-- The ideal of all `Y` coefficients of elements of an integral ideal. -/
def yCoeffIdeal (J : Ideal (CoordinateRing M)) : Ideal K[X] where
  carrier :=
    { b | ∃ z : CoordinateRing M, z ∈ J ∧ coeffY M z = b }
  zero_mem' := ⟨0, J.zero_mem, map_zero (coeffY M)⟩
  add_mem' := by
    rintro b₁ b₂ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, rfl⟩
    exact ⟨z₁ + z₂, J.add_mem hz₁ hz₂, map_add (coeffY M) z₁ z₂⟩
  smul_mem' := by
    rintro r b ⟨z, hz, rfl⟩
    refine ⟨xClass M r * z, J.mul_mem_left (xClass M r) hz, ?_⟩
    exact coeffY_xClass_mul M r z

@[simp] theorem mem_yCoeffIdeal
    (J : Ideal (CoordinateRing M)) (b : K[X]) :
    b ∈ yCoeffIdeal M J ↔
      ∃ z : CoordinateRing M, z ∈ J ∧ coeffY M z = b :=
  Iff.rfl

theorem coeffY_mem_yCoeffIdeal
    (J : Ideal (CoordinateRing M)) {z : CoordinateRing M}
    (hz : z ∈ J) :
    coeffY M z ∈ yCoeffIdeal M J :=
  ⟨z, hz, rfl⟩

/-- Multiplication by `Y` exchanges the two coefficients, up to the
quadratic equation in the constant coefficient. -/
@[simp] theorem coeffY_yClass_mul (z : CoordinateRing M) :
    coeffY M (yClass M * z) = coeff0 M z := by
  conv_lhs =>
    rw [← recompose M z]
  rw [mul_add, map_add]
  have hfirst :
      coeffY M (yClass M * xClass M (coeff0 M z)) =
        coeff0 M z := by
    rw [mul_comm, coeffY_xClass_mul, coeffY_yClass, mul_one]
  have hsecond :
      coeffY M
          (yClass M *
            (xClass M (coeffY M z) * yClass M)) = 0 := by
    calc
      coeffY M
          (yClass M *
            (xClass M (coeffY M z) * yClass M)) =
          coeffY M
            (xClass M (coeffY M z) * yClass M ^ 2) := by
              congr 1
              ring
      _ = coeffY M
            (xClass M (coeffY M z) * xClass M M.f) := by
              rw [yClass_sq]
      _ = coeffY M (xClass M (coeffY M z * M.f)) := by
              rw [xClass_mul]
      _ = 0 := coeffY_xClass M _
  rw [hfirst, hsecond, add_zero]

/-- Ideal stability under multiplication by `Y` puts the constant
coefficient in the same content ideal. -/
theorem coeff0_mem_yCoeffIdeal
    (J : Ideal (CoordinateRing M)) {z : CoordinateRing M}
    (hz : z ∈ J) :
    coeff0 M z ∈ yCoeffIdeal M J := by
  refine ⟨yClass M * z, J.mul_mem_left (yClass M) hz, ?_⟩
  exact coeffY_yClass_mul M z

theorem yCoeffIdeal_ne_bot
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥) :
    yCoeffIdeal M J ≠ ⊥ := by
  obtain ⟨z, hzJ, hz⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hJ
  intro hbot
  have hY : coeffY M z = 0 := by
    rw [← Ideal.mem_bot, ← hbot]
    exact coeffY_mem_yCoeffIdeal M J hzJ
  have h0 : coeff0 M z = 0 := by
    rw [← Ideal.mem_bot, ← hbot]
    exact coeff0_mem_yCoeffIdeal M J hzJ
  apply hz
  rw [← recompose M z, h0, hY, xClass_zero, zero_mul, add_zero]

/-- A canonical (not prematurely normalized) generator of the coefficient
content. -/
def contentGenerator (J : Ideal (CoordinateRing M)) : K[X] :=
  Submodule.IsPrincipal.generator (yCoeffIdeal M J)

theorem span_contentGenerator (J : Ideal (CoordinateRing M)) :
    Ideal.span ({contentGenerator M J} : Set K[X]) =
      yCoeffIdeal M J :=
  Ideal.span_singleton_generator (yCoeffIdeal M J)

theorem contentGenerator_ne_zero
    (J : Ideal (CoordinateRing M)) (hJ : J ≠ ⊥) :
    contentGenerator M J ≠ 0 := by
  intro hzero
  apply yCoeffIdeal_ne_bot M J hJ
  exact
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
      (yCoeffIdeal M J)).2 hzero

/-- Every element of `J` is visibly divisible in the coordinate ring by
the coefficient-content generator. -/
theorem exists_content_factor
    (J : Ideal (CoordinateRing M)) {z : CoordinateRing M}
    (hz : z ∈ J) :
    ∃ q : CoordinateRing M,
      xClass M (contentGenerator M J) * q = z := by
  have h0 := coeff0_mem_yCoeffIdeal M J hz
  have hY := coeffY_mem_yCoeffIdeal M J hz
  rw [← span_contentGenerator M J, Ideal.mem_span_singleton] at h0 hY
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := hY
  refine ⟨xClass M a + xClass M b * yClass M, ?_⟩
  calc
    xClass M (contentGenerator M J) *
          (xClass M a + xClass M b * yClass M) =
        xClass M (contentGenerator M J * a) +
          xClass M (contentGenerator M J * b) * yClass M := by
            simp only [mul_add, xClass_mul]
            ring
    _ = xClass M (coeff0 M z) +
          xClass M (coeffY M z) * yClass M := by
            rw [← ha, ← hb]
    _ = z := recompose M z

/-! ## Division by content as a colon ideal -/

/-- The integral colon ideal `{z | d z ∈ J}`. -/
def primitivePart
    (J : Ideal (CoordinateRing M)) (d : K[X]) :
    Ideal (CoordinateRing M) where
  carrier := {z | xClass M d * z ∈ J}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    simpa [mul_add] using J.add_mem hz hw
  smul_mem' := by
    intro a z hz
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      J.mul_mem_left a hz

@[simp] theorem mem_primitivePart
    (J : Ideal (CoordinateRing M)) (d : K[X])
    (z : CoordinateRing M) :
    z ∈ primitivePart M J d ↔ xClass M d * z ∈ J :=
  Iff.rfl

/-- Exact content factorization of the original integral ideal. -/
theorem span_content_mul_primitivePart
    (J : Ideal (CoordinateRing M)) :
    Ideal.span
          ({xClass M (contentGenerator M J)} :
            Set (CoordinateRing M)) *
        primitivePart M J (contentGenerator M J) =
      J := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro r hr z hz
    rw [Ideal.mem_span_singleton'] at hr
    obtain ⟨a, rfl⟩ := hr
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      J.mul_mem_left a hz
  · rw [Ideal.le_span_singleton_mul_iff]
    intro z hz
    obtain ⟨q, hq⟩ := exists_content_factor M J hz
    refine ⟨q, ?_, hq⟩
    change xClass M (contentGenerator M J) * q ∈ J
    rw [hq]
    exact hz

/-- The divided ideal contains an element with `Y` coefficient one. -/
theorem primitivePart_isPrimitive
    (J : Ideal (CoordinateRing M)) :
    IdealIsPrimitive M
      (primitivePart M J (contentGenerator M J)) := by
  have hd :
      contentGenerator M J ∈ yCoeffIdeal M J :=
    Submodule.IsPrincipal.generator_mem (yCoeffIdeal M J)
  obtain ⟨z, hzJ, hzY⟩ := hd
  have h0 := coeff0_mem_yCoeffIdeal M J hzJ
  rw [← span_contentGenerator M J, Ideal.mem_span_singleton] at h0
  obtain ⟨c, hc⟩ := h0
  let q : CoordinateRing M := xClass M c + yClass M
  have hdq :
      xClass M (contentGenerator M J) * q = z := by
    calc
      xClass M (contentGenerator M J) * q =
          xClass M (contentGenerator M J * c) +
            xClass M (contentGenerator M J) * yClass M := by
              simp only [q, mul_add, xClass_mul]
      _ = xClass M (coeff0 M z) +
            xClass M (coeffY M z) * yClass M := by
              rw [← hc, hzY]
      _ = z := recompose M z
  refine ⟨q, ?_, ?_⟩
  · change xClass M (contentGenerator M J) * q ∈ J
    rw [hdq]
    exact hzJ
  · simp [q]

/-! ## Fractional invertibility -/

theorem primitivePart_fractional_isUnit
    (J : Ideal (CoordinateRing M))
    (hJ :
      IsUnit
        (J :
          FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))) :
    IsUnit
      (primitivePart M J (contentGenerator M J) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) := by
  have hmul :
      IsUnit (
        ((Ideal.span
              ({xClass M (contentGenerator M J)} :
                Set (CoordinateRing M)) :
              Ideal (CoordinateRing M)) :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M)) *
          (primitivePart M J (contentGenerator M J) :
            FractionalIdeal
              (CoordinateRing M)⁰ (FunctionField M))) := by
    rw [← FractionalIdeal.coeIdeal_mul,
      span_content_mul_primitivePart M J]
    exact hJ
  exact (IsUnit.mul_iff.mp hmul).2

/-! ## Oriented primitive representatives -/

def contentFunctionUnit
    (d : K[X]) (hd : d ≠ 0) :
    (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (xClass M d))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (xClass_ne_zero M hd))

@[simp] theorem coe_contentFunctionUnit
    (d : K[X]) (hd : d ≠ 0) :
    (contentFunctionUnit M d hd : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (xClass M d) := rfl

namespace IntegralOrientedRep

variable (O : InfinityOrder M)

def primitivePartUnit (R : IntegralOrientedRep M) : InvFrac M :=
  (primitivePart_fractional_isUnit M R.ideal
    (R.ideal_isUnit M)).unit

@[simp] theorem coe_primitivePartUnit
    (R : IntegralOrientedRep M) :
    (R.primitivePartUnit M :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      primitivePart M R.ideal (contentGenerator M R.ideal) :=
  (primitivePart_fractional_isUnit M R.ideal
    (R.ideal_isUnit M)).unit_spec

def contentUnit (R : IntegralOrientedRep M) :
    (FunctionField M)ˣ :=
  contentFunctionUnit M (contentGenerator M R.ideal)
    (contentGenerator_ne_zero M R.ideal (R.ideal_ne_bot M))

/-- Divide the integral ideal by its polynomial content and adjust the
stored orientation by the exact `ordPlus` of that principal factor. -/
def primitivePartRep (R : IntegralOrientedRep M) :
    IntegralOrientedRep M where
  ideal := primitivePart M R.ideal (contentGenerator M R.ideal)
  unit := R.primitivePartUnit M
  coe_unit := coe_primitivePartUnit M R
  atInfinity :=
    R.atInfinity -
      Multiplicative.toAdd (O.ordPlus (R.contentUnit M))

@[simp] theorem primitivePartRep_ideal
    (R : IntegralOrientedRep M) :
    (R.primitivePartRep M O).ideal =
      primitivePart M R.ideal (contentGenerator M R.ideal) := rfl

@[simp] theorem primitivePartRep_atInfinity
    (R : IntegralOrientedRep M) :
    (R.primitivePartRep M O).atInfinity =
      R.atInfinity -
        Multiplicative.toAdd (O.ordPlus (R.contentUnit M)) := rfl

theorem primitivePartRep_isPrimitive
    (R : IntegralOrientedRep M) :
    IdealIsPrimitive M (R.primitivePartRep M O).ideal :=
  primitivePart_isPrimitive M R.ideal

theorem primitivePartUnit_mul_contentUnit
    (R : IntegralOrientedRep M) :
    R.primitivePartUnit M *
        toPrincipalIdeal (CoordinateRing M) (FunctionField M)
          (R.contentUnit M) =
      R.unit := by
  apply Units.ext
  simp only [Units.val_mul, coe_primitivePartUnit,
    coe_toPrincipalIdeal, contentUnit,
    coe_contentFunctionUnit]
  calc
    (primitivePart M R.ideal (contentGenerator M R.ideal) :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) *
        FractionalIdeal.spanSingleton
          (CoordinateRing M)⁰
          (algebraMap (CoordinateRing M) (FunctionField M)
            (xClass M (contentGenerator M R.ideal))) =
      (primitivePart M R.ideal (contentGenerator M R.ideal) :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) *
        (Ideal.span
            ({xClass M (contentGenerator M R.ideal)} :
              Set (CoordinateRing M)) :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) := by
              rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        ((Ideal.span
              ({xClass M (contentGenerator M R.ideal)} :
                Set (CoordinateRing M)) :
            Ideal (CoordinateRing M)) *
          primitivePart M R.ideal (contentGenerator M R.ideal) :
          Ideal (CoordinateRing M)) := by
            rw [FractionalIdeal.coeIdeal_mul]
            ac_rfl
    _ = (R.ideal :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) := by
              rw [span_content_mul_primitivePart M R.ideal]
    _ = (R.unit :
          FractionalIdeal
            (CoordinateRing M)⁰ (FunctionField M)) := R.coe_unit.symm

/-- Removing content is an exact principal equivalence in the oriented
quotient, not merely an equality of unoriented ideal classes. -/
theorem primitivePartRep_picClass
    (R : IntegralOrientedRep M) :
    (R.primitivePartRep M O).picClass M O =
      R.picClass M O := by
  change
    QuotientGroup.mk' (principalOriented M O).range
        ((R.primitivePartRep M O).raw M) =
      QuotientGroup.mk' (principalOriented M O).range (R.raw M)
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨principalOriented M O (R.contentUnit M),
    MonoidHom.mem_range.mpr ⟨R.contentUnit M, rfl⟩, ?_⟩
  apply Prod.ext
  · exact primitivePartUnit_mul_contentUnit M R
  · change
      Multiplicative.ofAdd
          (R.atInfinity -
            Multiplicative.toAdd
              (O.ordPlus (R.contentUnit M))) *
        O.ordPlus (R.contentUnit M) =
      Multiplicative.ofAdd R.atInfinity
    change
      R.atInfinity -
          Multiplicative.toAdd
            (O.ordPlus (R.contentUnit M)) +
        Multiplicative.toAdd
          (O.ordPlus (R.contentUnit M)) =
      R.atInfinity
    omega

end IntegralOrientedRep

/-- Every oriented Picard class has a primitive integral representative.
This closes the missing bridge between denominator clearing and Mumford
graph extraction. -/
theorem exists_primitiveIntegralRepresentative
    (O : InfinityOrder M) (c : ConcretePic M O) :
    ∃ R : IntegralOrientedRep M,
      IdealIsPrimitive M R.ideal ∧ R.picClass M O = c := by
  obtain ⟨R, hR⟩ := exists_integralRepresentative M O c
  refine ⟨R.primitivePartRep M O,
    R.primitivePartRep_isPrimitive M O, ?_⟩
  exact (R.primitivePartRep_picClass M O).trans hR

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordCantorReduction
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordCantorReduction =====
section

/-!
# One-step Cantor reduction for a monic sextic

This file isolates the structural algebra used by a well-founded Cantor
reduction.  It contains no enumeration and no Riemann--Roch input.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K)

local instance : DecidableEq K := Classical.decEq K

/-! ## Changing the graph polynomial modulo `u` -/

/-- Replacing `v` by a congruent polynomial modulo `u` does not change the
Mumford ideal. -/
theorem mumfordIdeal_eq_of_dvd_sub
    (u v V : K[X]) (h : u ∣ V - v) :
    mumfordIdeal M u V = mumfordIdeal M u v := by
  obtain ⟨t, ht⟩ := h
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal M u v
    · have hmultiple :
          xClass M (V - v) ∈ mumfordIdeal M u v := by
        rw [ht, xClass_mul, mul_comm]
        exact Ideal.mul_mem_left _ (xClass M t)
          (xClass_mem_mumfordIdeal M u v)
      have heq :
          ySubClass M V =
            ySubClass M v - xClass M (V - v) := by
        simp [ySubClass, xClass_sub]
      rw [heq]
      exact Ideal.sub_mem _
        (ySubClass_mem_mumfordIdeal M u v) hmultiple
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact xClass_mem_mumfordIdeal M u V
    · have hmultiple :
          xClass M (V - v) ∈ mumfordIdeal M u V := by
        rw [ht, xClass_mul, mul_comm]
        exact Ideal.mul_mem_left _ (xClass M t)
          (xClass_mem_mumfordIdeal M u V)
      have heq :
          ySubClass M v =
            ySubClass M V + xClass M (V - v) := by
        simp [ySubClass, xClass_sub]
      rw [heq]
      exact Ideal.add_mem _
        (ySubClass_mem_mumfordIdeal M u V) hmultiple

/-- Multiplying the first generator by a polynomial unit does not change a
Mumford ideal.  The divisibility formulation avoids choosing that unit. -/
theorem mumfordIdeal_eq_of_dvd_dvd
    (u u' v : K[X]) (huu' : u ∣ u') (hu'u : u' ∣ u) :
    mumfordIdeal M u v = mumfordIdeal M u' v := by
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := hu'u
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u' v)
    · exact ySubClass_mem_mumfordIdeal M u' v
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · obtain ⟨t, rfl⟩ := huu'
      rw [xClass_mul]
      exact Ideal.mul_mem_right _ _
        (xClass_mem_mumfordIdeal M u v)
    · exact ySubClass_mem_mumfordIdeal M u v

theorem mumfordIdeal_normalize
    (u v : K[X]) :
    mumfordIdeal M (_root_.normalize u) v = mumfordIdeal M u v := by
  exact mumfordIdeal_eq_of_dvd_dvd M (_root_.normalize u) u v
    (associated_normalize u).symm.dvd
    (associated_normalize u).dvd

/-! ## The Cantor product identity -/

/-- The ideal product at the heart of one Cantor reduction step.

The Bezout condition is exactly the one supplied by `mumford_bezout` for
the semireduced pair `(u,V)` when `w = (f-V²)/u`. -/
theorem mumfordIdeal_mul_cantor
    (u w V : K[X])
    (hcurve : M.f - V ^ 2 = u * w)
    (hbezout :
      ∃ a b c : K[X],
        a * u + b * (2 * V) + c * w = 1) :
    mumfordIdeal M u V * mumfordIdeal M w V =
      Ideal.span ({ySubClass M V} : Set (CoordinateRing M)) := by
  let I := mumfordIdeal M u V
  let J := mumfordIdeal M w V
  let g := ySubClass M V
  apply le_antisymm
  · rw [mumfordIdeal, mumfordIdeal,
      Ideal.span_pair_mul_span_pair]
    apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · have hfactor :
          xClass M u * xClass M w =
            ySubClass M V * (yClass M + xClass M V) := by
        symm
        calc
          ySubClass M V * (yClass M + xClass M V) =
              xClass M (M.f - V ^ 2) := by
            simp only [ySubClass]
            calc
              (yClass M - xClass M V) *
                  (yClass M + xClass M V) =
                  yClass M ^ 2 - xClass M V ^ 2 := by ring
              _ = xClass M M.f - xClass M V ^ 2 := by
                rw [yClass_sq]
              _ = xClass M (M.f - V ^ 2) := by
                rw [xClass_sub, xClass_pow]
          _ = xClass M (u * w) := by rw [hcurve]
          _ = xClass M u * xClass M w := by rw [xClass_mul]
      rw [hfactor]
      exact Ideal.mul_mem_right (yClass M + xClass M V) _
        (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (xClass M u) (Ideal.subset_span (Set.mem_singleton _))
    · rw [mul_comm]
      exact Ideal.mul_mem_left _
        (xClass M w) (Ideal.subset_span (Set.mem_singleton _))
    · exact Ideal.mul_mem_left _
        (ySubClass M V) (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨a, b, c, hbez⟩ := hbezout
    have huI : xClass M u ∈ I :=
      xClass_mem_mumfordIdeal M u V
    have hwJ : xClass M w ∈ J :=
      xClass_mem_mumfordIdeal M w V
    have hgI : g ∈ I :=
      ySubClass_mem_mumfordIdeal M u V
    have hgJ : g ∈ J :=
      ySubClass_mem_mumfordIdeal M w V
    have hug : xClass M u * g ∈ I * J :=
      Ideal.mul_mem_mul huI hgJ
    have hgw : g * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul hgI hwJ
    have hgg : g * g ∈ I * J :=
      Ideal.mul_mem_mul hgI hgJ
    have huw : xClass M u * xClass M w ∈ I * J :=
      Ideal.mul_mem_mul huI hwJ
    have htwoVg : xClass M (2 * V) * g ∈ I * J := by
      have hdifference := Ideal.sub_mem (I * J) huw hgg
      convert hdifference using 1
      change
        xClass M (2 * V) * ySubClass M V =
          xClass M u * xClass M w -
            ySubClass M V * ySubClass M V
      have hxTwo :
          xClass M (2 : K[X]) = (2 : CoordinateRing M) := by
        exact map_natCast (xClassHom M) 2
      calc
        xClass M (2 * V) * ySubClass M V =
            xClass M (M.f - V ^ 2) -
              ySubClass M V ^ 2 := by
          simp only [ySubClass]
          rw [show xClass M (M.f - V ^ 2) =
            yClass M ^ 2 - xClass M V ^ 2 by
              rw [yClass_sq, xClass_sub, xClass_pow]]
          simp only [xClass_mul]
          rw [hxTwo]
          ring
        _ = xClass M (u * w) -
              ySubClass M V ^ 2 := by rw [hcurve]
        _ = xClass M u * xClass M w -
              ySubClass M V * ySubClass M V := by
          rw [xClass_mul, pow_two]
    have ha : xClass M a * (xClass M u * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M a) hug
    have hb : xClass M b * (xClass M (2 * V) * g) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M b) htwoVg
    have hc : xClass M c * (g * xClass M w) ∈ I * J :=
      Ideal.mul_mem_left _ (xClass M c) hgw
    have hsum :=
      Ideal.add_mem (I * J) (Ideal.add_mem (I * J) ha hb) hc
    have heq :
        xClass M a * (xClass M u * g) +
            xClass M b * (xClass M (2 * V) * g) +
            xClass M c * (g * xClass M w) = g := by
      calc
        _ = xClass M
              (a * u + b * (2 * V) + c * w) * g := by
          simp only [xClass_add, xClass_mul]
          ring
        _ = g := by rw [hbez, xClass_one, one_mul]
    rw [heq] at hsum
    exact hsum

/-- Bezout transvection for the graph change `v ↦ v + u t`.  It is the
algebraic reason that the cubic boundary step needs no new coprimality
argument. -/
theorem cantorBezout_add_mul
    (D : SemiMumford M) (t w : K[X])
    (hcurve :
      M.f - (D.v + D.u * t) ^ 2 = D.u * w) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * (D.v + D.u * t)) + c * w = 1 := by
  obtain ⟨w₀, a, b, c, hw₀, hbez⟩ := mumford_bezout M D
  have hwEq :
      w₀ = w + 2 * D.v * t + D.u * t ^ 2 := by
    apply mul_left_cancel₀ D.u_monic.ne_zero
    calc
      D.u * w₀ = M.f - D.v ^ 2 := hw₀.symm
      _ = (M.f - (D.v + D.u * t) ^ 2) +
          D.u * (2 * D.v * t + D.u * t ^ 2) := by ring
      _ = D.u * w +
          D.u * (2 * D.v * t + D.u * t ^ 2) := by rw [hcurve]
      _ = D.u * (w + 2 * D.v * t + D.u * t ^ 2) := by ring
  refine ⟨a - 2 * b * t - c * t ^ 2, b + c * t, c, ?_⟩
  rw [hwEq] at hbez
  linear_combination hbez

/-! ## Degree descent -/

/-- A factor in `f - V² = u w` cannot vanish. -/
theorem cantorFactor_ne_zero
    (u V w : K[X]) (hcurve : M.f - V ^ 2 = u * w) :
    w ≠ 0 := by
  intro hw
  have hsub : M.f - V ^ 2 = 0 := by
    simpa [hw] using hcurve
  have hsq : V ^ 2 = M.f := (sub_eq_zero.mp hsub).symm
  have hVunit : IsUnit V := by
    apply M.squarefree V
    refine ⟨1, ?_⟩
    simpa only [mul_one, pow_two] using hsq.symm
  have hfunit : IsUnit M.f := by
    rw [← hsq]
    exact hVunit.pow 2
  exact M.not_isUnit hfunit

/-- Above genus two, the quotient in a Cantor step has strictly smaller
degree than the old monic denominator. -/
theorem cantorFactor_natDegree_lt
    (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w)
    (hdeg : 3 < D.u.natDegree) :
    w.natDegree < D.u.natDegree := by
  have hw : w ≠ 0 := cantorFactor_ne_zero M D.u D.v w hcurve
  have hvDegree : D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hvNatDegree : D.v.natDegree < D.u.natDegree := by
    by_cases hv : D.v = 0
    · rw [hv]
      simp
      omega
    · exact natDegree_lt_natDegree hv hvDegree
  have hnum :
      (M.f - D.v ^ 2).natDegree ≤
        max 6 (2 * D.v.natDegree) := by
    calc
      (M.f - D.v ^ 2).natDegree ≤
          max M.f.natDegree (D.v ^ 2).natDegree :=
        natDegree_sub_le _ _
      _ = max 6 (2 * D.v.natDegree) := by
        rw [M.natDegree, natDegree_pow]
  have hproduct :
      D.u.natDegree + w.natDegree =
        (M.f - D.v ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero hw, ← hcurve]
  have hbound :
      max 6 (2 * D.v.natDegree) <
        2 * D.u.natDegree := by
    rw [Nat.max_lt]
    omega
  omega

/-- In the cubic boundary case one replaces `v` by `v + u`.  The leading
terms of `f` and `(v+u)²` then cancel, so the quotient has degree at most
two. -/
theorem cubicCantorFactor
    (D : SemiMumford M) (w : K[X])
    (hdeg : D.u.natDegree = 3)
    (hcurve :
      M.f - (D.v + D.u) ^ 2 = D.u * w) :
    w ≠ 0 ∧ w.natDegree ≤ 2 := by
  have hvDegree : D.v.degree < D.u.degree :=
    (mod_eq_self_iff D.u_monic.ne_zero).mp D.v_reduced
  have hVMonic : (D.v + D.u).Monic :=
    D.u_monic.add_of_right hvDegree
  have hVNatDegree : (D.v + D.u).natDegree = 3 := by
    rw [natDegree_add_eq_right_of_degree_lt hvDegree, hdeg]
  have hf : IsMonicOfDegree M.f 6 :=
    ⟨M.natDegree, M.monic⟩
  have hV : IsMonicOfDegree (D.v + D.u) 3 :=
    ⟨hVNatDegree, hVMonic⟩
  have hV2 : IsMonicOfDegree ((D.v + D.u) ^ 2) 6 := by
    simpa using hV.pow 2
  have hnum :
      (M.f - (D.v + D.u) ^ 2).natDegree < 6 :=
    hf.natDegree_sub_lt (by norm_num) hV2
  have hw : w ≠ 0 :=
    cantorFactor_ne_zero M D.u (D.v + D.u) w hcurve
  have hproduct :
      D.u.natDegree + w.natDegree =
        (M.f - (D.v + D.u) ^ 2).natDegree := by
    rw [← natDegree_mul D.u_monic.ne_zero hw, ← hcurve]
  constructor
  · exact hw
  · omega

/-! ## The normalized next semirepresentative -/

theorem normalize_dvd_sub_mod
    (p q : K[X]) :
    _root_.normalize q ∣ p - p % _root_.normalize q := by
  refine ⟨p / _root_.normalize q, ?_⟩
  have hdiv := EuclideanDomain.mod_add_div p (_root_.normalize q)
  calc
    p - p % _root_.normalize q =
        (p % _root_.normalize q + _root_.normalize q * (p / _root_.normalize q)) -
          p % _root_.normalize q := by
      rw [hdiv]
    _ = _root_.normalize q * (p / _root_.normalize q) := by ring

/-- Normalize the quotient and reduce the complementary graph polynomial.
This is the inverse affine class; the actual Cantor successor is its
hyperelliptic conjugate below. -/
def cantorComplementSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w)
    (hw : w ≠ 0) :
    SemiMumford M where
  u := _root_.normalize w
  v := V % _root_.normalize w
  nInf := n
  u_monic := monic_normalize hw
  v_reduced := by
    apply (mod_eq_self_iff (monic_normalize hw).ne_zero).mpr
    exact degree_mod_lt _ (monic_normalize hw).ne_zero
  curve_dvd := by
    have hnW : _root_.normalize w ∣ w :=
      (associated_normalize w).symm.dvd
    have hnBase : _root_.normalize w ∣ M.f - V ^ 2 := by
      obtain ⟨c, hc⟩ := hnW
      refine ⟨D.u * c, ?_⟩
      calc
        M.f - V ^ 2 = D.u * w := hcurve
        _ = D.u * (_root_.normalize w * c) :=
          congrArg (fun z : K[X] ↦ D.u * z) hc
        _ = _root_.normalize w * (D.u * c) := by ring
    have hnGraph :
        _root_.normalize w ∣ V - V % _root_.normalize w :=
      normalize_dvd_sub_mod V w
    obtain ⟨a, ha⟩ := hnBase
    obtain ⟨b, hb⟩ := hnGraph
    refine ⟨a + b * (V + V % _root_.normalize w), ?_⟩
    calc
      M.f - (V % _root_.normalize w) ^ 2 =
          (M.f - V ^ 2) +
            (V - V % _root_.normalize w) *
              (V + V % _root_.normalize w) := by ring
      _ = _root_.normalize w * a +
            (_root_.normalize w * b) *
              (V + V % _root_.normalize w) := by rw [ha, hb]
      _ = _root_.normalize w *
            (a + b * (V + V % _root_.normalize w)) := by ring

@[simp] theorem cantorComplementSemi_u
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).u = _root_.normalize w := rfl

@[simp] theorem cantorComplementSemi_v
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).v =
      V % _root_.normalize w := rfl

@[simp] theorem cantorComplementSemi_nInf
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorComplementSemi M D V w n hcurve hw).nInf = n := rfl

theorem mumfordIdeal_cantorComplementSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdeal M
        (cantorComplementSemi M D V w n hcurve hw).u
        (cantorComplementSemi M D V w n hcurve hw).v =
      mumfordIdeal M w V := by
  change
    mumfordIdeal M (_root_.normalize w) (V % _root_.normalize w) =
      mumfordIdeal M w V
  calc
    mumfordIdeal M (_root_.normalize w) (V % _root_.normalize w) =
        mumfordIdeal M (_root_.normalize w) V :=
      (mumfordIdeal_eq_of_dvd_sub M (_root_.normalize w)
        (V % _root_.normalize w) V
        (normalize_dvd_sub_mod V w)).symm
    _ = mumfordIdeal M w V := mumfordIdeal_normalize M w V

theorem mumfordIdeal_mul_cantorComplement
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdeal M D.u D.v *
        mumfordIdeal M
          (cantorComplementSemi M D V w n hcurve hw).u
          (cantorComplementSemi M D V w n hcurve hw).v =
      Ideal.span ({ySubClass M V} : Set (CoordinateRing M)) := by
  rw [← mumfordIdeal_eq_of_dvd_sub M D.u D.v V hcongr,
    mumfordIdeal_cantorComplementSemi M D V w n hcurve hw]
  exact mumfordIdeal_mul_cantor M D.u w V hcurve hbezout

/-! ## Conjugating the complement -/

/-- The affine Cantor successor is the conjugate of the complement.  Its
graph polynomial is `(-V) mod _root_.normalize w`, up to the definitional
linearity of polynomial remainder. -/
def cantorConjugateSemi
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    SemiMumford M :=
  conjugateSemiMumford M
    (cantorComplementSemi M D V w n hcurve hw)

@[simp] theorem cantorConjugateSemi_u
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).u =
      _root_.normalize w := rfl

@[simp] theorem cantorConjugateSemi_v
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).v =
      -(V % _root_.normalize w) := rfl

@[simp] theorem cantorConjugateSemi_nInf
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorConjugateSemi M D V w n hcurve hw).nInf = n := rfl

/-! ## Principal functions in one oriented step -/

theorem ySubClass_ne_zero (V : K[X]) :
    ySubClass M V ≠ 0 := by
  intro h
  have hcoeff : (1 : K[X]) = 0 := by
    simpa using congrArg (coeffY M) h
  exact one_ne_zero hcoeff

def ySubFunctionUnit (V : K[X]) : (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (ySubClass M V))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (ySubClass_ne_zero M V))

@[simp] theorem coe_ySubFunctionUnit (V : K[X]) :
    (ySubFunctionUnit M V : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (ySubClass M V) := rfl

def xClassFunctionUnit (p : K[X]) (hp : p ≠ 0) :
    (FunctionField M)ˣ :=
  Units.mk0
    (algebraMap (CoordinateRing M) (FunctionField M)
      (xClass M p))
    (by
      simpa using
        (IsFractionRing.injective
          (CoordinateRing M) (FunctionField M)).ne
          (xClass_ne_zero M hp))

@[simp] theorem coe_xClassFunctionUnit
    (p : K[X]) (hp : p ≠ 0) :
    (xClassFunctionUnit M p hp : FunctionField M) =
      algebraMap (CoordinateRing M) (FunctionField M)
        (xClass M p) := rfl

/-- The principal correction taking the conjugate complement back to the
original affine ideal class: `(Y-V) / _root_.normalize(w)`. -/
def cantorCorrectionUnit
    (V w : K[X]) (hw : w ≠ 0) :
    (FunctionField M)ˣ :=
  ySubFunctionUnit M V *
    (xClassFunctionUnit M (_root_.normalize w)
      (monic_normalize hw).ne_zero)⁻¹

theorem mumfordIdealUnit_mul_cantorComplement
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdealUnit M D *
        mumfordIdealUnit M
          (cantorComplementSemi M D V w n hcurve hw) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (ySubFunctionUnit M V) := by
  apply Units.ext
  simp only [Units.val_mul, coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, coe_ySubFunctionUnit]
  rw [← FractionalIdeal.coeIdeal_mul,
    mumfordIdeal_mul_cantorComplement M D V w n hcurve hw
      hcongr hbezout,
    FractionalIdeal.coeIdeal_span_singleton]

theorem mumfordIdealUnit_complement_mul_conjugate
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    mumfordIdealUnit M
          (cantorComplementSemi M D V w n hcurve hw) *
        mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) =
      toPrincipalIdeal (CoordinateRing M) (FunctionField M)
        (xClassFunctionUnit M (_root_.normalize w)
          (monic_normalize hw).ne_zero) := by
  let E := cantorComplementSemi M D V w n hcurve hw
  apply Units.ext
  simp only [Units.val_mul, coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, coe_xClassFunctionUnit]
  change
    (mumfordIdeal M E.u E.v :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) *
      (mumfordIdeal M E.u (-E.v) :
        FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
      FractionalIdeal.spanSingleton (CoordinateRing M)⁰
        (algebraMap (CoordinateRing M) (FunctionField M)
          (xClass M E.u))
  rw [← FractionalIdeal.coeIdeal_mul,
    mumfordIdeal_mul_conj_integral M E,
    FractionalIdeal.coeIdeal_span_singleton]

theorem cantorConjugateSemi_principalRelation
    (D : SemiMumford M) (V w : K[X]) (n : ℤ)
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        toPrincipalIdeal (CoordinateRing M) (FunctionField M)
          (cantorCorrectionUnit M V w hw) =
      mumfordIdealUnit M D := by
  have hprod :=
    mumfordIdealUnit_mul_cantorComplement M D V w n
      hcurve hw hcongr hbezout
  have hnorm :=
    mumfordIdealUnit_complement_mul_conjugate M D V w n
      hcurve hw
  rw [cantorCorrectionUnit, map_mul, map_inv]
  calc
    mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        (toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (ySubFunctionUnit M V) *
          (toPrincipalIdeal (CoordinateRing M) (FunctionField M)
            (xClassFunctionUnit M (_root_.normalize w)
              (monic_normalize hw).ne_zero))⁻¹) =
      mumfordIdealUnit M
          (cantorConjugateSemi M D V w n hcurve hw) *
        ((mumfordIdealUnit M D *
            mumfordIdealUnit M
              (cantorComplementSemi M D V w n hcurve hw)) *
          (mumfordIdealUnit M
              (cantorComplementSemi M D V w n hcurve hw) *
            mumfordIdealUnit M
              (cantorConjugateSemi M D V w n hcurve hw))⁻¹) := by
        rw [hprod, hnorm]
    _ = mumfordIdealUnit M D := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-! ## Exact oriented update -/

/-- The raw oriented class attached to an integral semirepresentative.  The
`-1` agrees exactly with `mumfordRaw` on balanced representatives. -/
def semiMumfordRaw (D : SemiMumford M) : OrientedFrac M :=
  (mumfordIdealUnit M D,
    Multiplicative.ofAdd (D.nInf - 1))

def semiMumfordClass (O : InfinityOrder M) (D : SemiMumford M) :
    OrientedPic M O :=
  Additive.ofMul <|
    QuotientGroup.mk' (principalOriented M O).range
      (semiMumfordRaw M D)

theorem semiMumfordClass_eq_iff
    (O : InfinityOrder M) (D₁ D₂ : SemiMumford M) :
    semiMumfordClass M O D₁ = semiMumfordClass M O D₂ ↔
      ∃ alpha : (FunctionField M)ˣ,
        mumfordIdealUnit M D₁ *
              toPrincipalIdeal (CoordinateRing M) (FunctionField M)
                alpha =
            mumfordIdealUnit M D₂ ∧
        Multiplicative.ofAdd (D₁.nInf - 1) *
              O.ordPlus alpha =
            Multiplicative.ofAdd (D₂.nInf - 1) := by
  change QuotientGroup.mk'
      (principalOriented M O).range (semiMumfordRaw M D₁) =
    QuotientGroup.mk'
      (principalOriented M O).range (semiMumfordRaw M D₂) ↔ _
  rw [QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨z, hz, hmul⟩
    obtain ⟨alpha, rfl⟩ := MonoidHom.mem_range.mp hz
    exact ⟨alpha, congrArg Prod.fst hmul, congrArg Prod.snd hmul⟩
  · rintro ⟨alpha, hIdeal, hInf⟩
    refine ⟨principalOriented M O alpha,
      MonoidHom.mem_range.mpr ⟨alpha, rfl⟩, ?_⟩
    exact Prod.ext hIdeal hInf

@[simp] theorem semiMumfordClass_toSemi
    (O : InfinityOrder M) (D : Mumford M) :
    semiMumfordClass M O D.toSemi = classOf M O D := rfl

/-- The unique integer correction forced by the order of the principal
function `(Y-V)/_root_.normalize(w)` at the chosen positive infinity. -/
def cantorNextNInf
    (O : InfinityOrder M) (D : SemiMumford M)
    (V w : K[X]) (hw : w ≠ 0) : ℤ :=
  D.nInf -
    Multiplicative.toAdd
      (O.ordPlus (cantorCorrectionUnit M V w hw))

/-- One structurally complete Cantor step, including the sign of the next
graph polynomial and the exact oriented-infinity correction. -/
def cantorNextSemi
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    SemiMumford M :=
  cantorConjugateSemi M D V w
    (cantorNextNInf M O D V w hw) hcurve hw

@[simp] theorem cantorNextSemi_u
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).u = _root_.normalize w := rfl

@[simp] theorem cantorNextSemi_nInf
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).nInf =
      D.nInf -
        Multiplicative.toAdd
          (O.ordPlus (cantorCorrectionUnit M V w hw)) := rfl

theorem cantorNextSemi_class
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0)
    (hcongr : D.u ∣ V - D.v)
    (hbezout :
      ∃ a b c : K[X],
        a * D.u + b * (2 * V) + c * w = 1) :
    semiMumfordClass M O
        (cantorNextSemi M O D V w hcurve hw) =
      semiMumfordClass M O D := by
  apply (semiMumfordClass_eq_iff M O
    (cantorNextSemi M O D V w hcurve hw) D).2
  refine ⟨cantorCorrectionUnit M V w hw, ?_, ?_⟩
  · exact cantorConjugateSemi_principalRelation M D V w
      (cantorNextNInf M O D V w hw) hcurve hw hcongr hbezout
  · change
      Multiplicative.ofAdd
          (D.nInf -
              Multiplicative.toAdd
                (O.ordPlus (cantorCorrectionUnit M V w hw)) - 1) *
          O.ordPlus (cantorCorrectionUnit M V w hw) =
        Multiplicative.ofAdd (D.nInf - 1)
    change
      D.nInf -
          Multiplicative.toAdd
            (O.ordPlus (cantorCorrectionUnit M V w hw)) - 1 +
        Multiplicative.toAdd
          (O.ordPlus (cantorCorrectionUnit M V w hw)) =
      D.nInf - 1
    omega

theorem natDegree_normalize_eq
    (p : K[X]) :
    (_root_.normalize p).natDegree = p.natDegree := by
  exact natDegree_eq_natDegree degree_normalize

@[simp] theorem cantorNextSemi_natDegree
    (O : InfinityOrder M) (D : SemiMumford M) (V w : K[X])
    (hcurve : M.f - V ^ 2 = D.u * w) (hw : w ≠ 0) :
    (cantorNextSemi M O D V w hcurve hw).u.natDegree =
      w.natDegree := by
  rw [cantorNextSemi_u, natDegree_normalize_eq]

theorem cantorBezout_of_semi_factor
    (D : SemiMumford M) (w : K[X])
    (hcurve : M.f - D.v ^ 2 = D.u * w) :
    ∃ a b c : K[X],
      a * D.u + b * (2 * D.v) + c * w = 1 := by
  obtain ⟨w', a, b, c, hw', hbez⟩ := mumford_bezout M D
  have hwEq : w' = w := by
    apply mul_left_cancel₀ D.u_monic.ne_zero
    exact hw'.symm.trans hcurve
  subst w'
  exact ⟨a, b, c, hbez⟩

end

end MazurProof.SexticMumford

end
end

-- module FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction =====
section

/-!
# Structural reduction of oriented sextic ideals

This file joins the two algebraic seams:

* polynomial-content division produces a primitive integral ideal;
* primitive integral ideals have semi-Mumford graph form.

It then packages the well-founded affine-degree step.  Infinity balancing
is deliberately a separate phase.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]
variable (M : Model K) (O : InfinityOrder M)

theorem IntegralOrientedRep.exists_semiMumford
    (R : IntegralOrientedRep M)
    (hprimitive : IdealIsPrimitive M R.ideal) :
    ∃ D : SemiMumford M,
      semiMumfordClass M O D = R.picClass M O ∧
      mumfordIdeal M D.u D.v = R.ideal := by
  obtain ⟨D, hIdeal, -, hn⟩ :=
    exists_semiMumford_of_primitive M R.ideal
      (R.ideal_ne_bot M) hprimitive (R.atInfinity + 1)
  have hunit : mumfordIdealUnit M D = R.unit := by
    apply Units.ext
    rw [coe_mumfordIdealUnit, hIdeal, ← R.coe_unit]
  have hraw : semiMumfordRaw M D = R.raw M := by
    apply Prod.ext
    · exact hunit
    · change
        Multiplicative.ofAdd (D.nInf - 1) =
          Multiplicative.ofAdd R.atInfinity
      congr 1
      rw [hn]
      omega
  refine ⟨D, ?_, hIdeal⟩
  change
    Additive.ofMul
        (QuotientGroup.mk' (principalOriented M O).range
          (semiMumfordRaw M D)) =
      Additive.ofMul
        (QuotientGroup.mk' (principalOriented M O).range
          (R.raw M))
  rw [hraw]

/-- Every oriented class has a semi-Mumford representative before any
degree reduction. -/
theorem exists_semiMumfordRepresentative
    (c : ConcretePic M O) :
    ∃ D : SemiMumford M, semiMumfordClass M O D = c := by
  obtain ⟨R, hprimitive, hR⟩ :=
    exists_primitiveIntegralRepresentative M O c
  obtain ⟨D, hD, -⟩ :=
    R.exists_semiMumford M O hprimitive
  exact ⟨D, hD.trans hR⟩

/-! ## A canonical affine-degree step -/

/-- At degree three use the monic lift `v+u`; otherwise use the reduced
graph polynomial itself. -/
def degreeLift (D : SemiMumford M) : K[X] :=
  if D.u.natDegree = 3 then D.v + D.u else D.v

theorem degreeLift_congr (D : SemiMumford M) :
    D.u ∣ degreeLift M D - D.v := by
  unfold degreeLift
  split_ifs
  · refine ⟨1, ?_⟩
    ring
  · simp

theorem degreeLift_curve_dvd (D : SemiMumford M) :
    D.u ∣ M.f - (degreeLift M D) ^ 2 := by
  unfold degreeLift
  split_ifs
  · obtain ⟨w, hw⟩ := D.curve_dvd
    refine ⟨w - 2 * D.v - D.u, ?_⟩
    calc
      M.f - (D.v + D.u) ^ 2 =
          (M.f - D.v ^ 2) -
            2 * D.u * D.v - D.u ^ 2 := by ring
      _ = D.u * w - 2 * D.u * D.v - D.u ^ 2 := by
            rw [hw]
      _ = D.u * (w - 2 * D.v - D.u) := by ring
  · exact D.curve_dvd

def degreeStepFactor (D : SemiMumford M) : K[X] :=
  Classical.choose (degreeLift_curve_dvd M D)

theorem degreeStepFactor_spec (D : SemiMumford M) :
    M.f - (degreeLift M D) ^ 2 =
      D.u * degreeStepFactor M D :=
  Classical.choose_spec (degreeLift_curve_dvd M D)

theorem degreeStepFactor_ne_zero (D : SemiMumford M) :
    degreeStepFactor M D ≠ 0 :=
  cantorFactor_ne_zero M D.u (degreeLift M D)
    (degreeStepFactor M D) (degreeStepFactor_spec M D)

def degreeStep
    (D : SemiMumford M) :
    SemiMumford M :=
  cantorNextSemi M O D (degreeLift M D) (degreeStepFactor M D)
    (degreeStepFactor_spec M D) (degreeStepFactor_ne_zero M D)

theorem degreeStep_class
    (D : SemiMumford M) :
    semiMumfordClass M O (degreeStep M O D) =
      semiMumfordClass M O D := by
  unfold degreeStep
  apply cantorNextSemi_class M O D
    (degreeLift M D) (degreeStepFactor M D)
    (degreeStepFactor_spec M D) (degreeStepFactor_ne_zero M D)
    (degreeLift_congr M D)
  unfold degreeLift
  split_ifs with hdeg
  · simpa using
      cantorBezout_add_mul M D 1 (degreeStepFactor M D)
        (by
          simpa [degreeLift, hdeg] using
            degreeStepFactor_spec M D)
  · simpa using
      cantorBezout_of_semi_factor M D (degreeStepFactor M D)
        (by
          simpa [degreeLift, hdeg] using
            degreeStepFactor_spec M D)

theorem degreeStep_lt
    (D : SemiMumford M) (hlarge : 2 < D.u.natDegree) :
    (degreeStep M O D).u.natDegree < D.u.natDegree := by
  unfold degreeStep
  rw [cantorNextSemi_natDegree]
  by_cases hthree : D.u.natDegree = 3
  · have hspec :
        M.f - (D.v + D.u) ^ 2 =
          D.u * degreeStepFactor M D := by
      simpa [degreeLift, hthree] using degreeStepFactor_spec M D
    have hle :=
      (cubicCantorFactor M D (degreeStepFactor M D) hthree
        hspec).2
    omega
  · have hspec :
        M.f - D.v ^ 2 =
          D.u * degreeStepFactor M D := by
      simpa [degreeLift, hthree] using degreeStepFactor_spec M D
    apply cantorFactor_natDegree_lt M D
      (degreeStepFactor M D) hspec
    omega

set_option maxHeartbeats 4000000 in
attribute [local irreducible] MazurProof.SexticMumford.curvePoly in
/-- A semi-Mumford representative together with the terminal affine degree
bound.  This does not yet impose the independent infinity-balance bounds. -/
structure LowDegreeSemi where
  toSemi : SemiMumford M
  degree_le_two : toSemi.u.natDegree ≤ 2

def reduceDegree (D : SemiMumford M) : LowDegreeSemi M :=
  if hsmall : D.u.natDegree ≤ 2 then
    ⟨D, hsmall⟩
  else
    reduceDegree (degreeStep M O D)
termination_by D.u.natDegree
decreasing_by
  exact degreeStep_lt M O D (by omega)

@[simp] theorem reduceDegree_class
    (D : SemiMumford M) :
    semiMumfordClass M O (reduceDegree M O D).toSemi =
      semiMumfordClass M O D := by
  rw [reduceDegree]
  split_ifs with hsmall
  · rfl
  · rw [reduceDegree_class, degreeStep_class]
termination_by D.u.natDegree
decreasing_by
  exact degreeStep_lt M O D (by omega)

/-- Phase I of the structural reduction: every oriented class has a
representative of affine degree at most two.  No claim about the independent
`nInf` balance is made here. -/
theorem exists_lowDegreeSemiRepresentative
    (c : ConcretePic M O) :
    ∃ D : LowDegreeSemi M,
      semiMumfordClass M O D.toSemi = c := by
  obtain ⟨D, hD⟩ := exists_semiMumfordRepresentative M O c
  exact ⟨reduceDegree M O D, (reduceDegree_class M O D).trans hD⟩

end

end MazurProof.SexticMumford

end
end


