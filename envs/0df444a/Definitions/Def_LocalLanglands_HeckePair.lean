-- Prove2me | Definitions.Def_LocalLanglands_HeckePair
-- name    : LocalLanglands_HeckePair
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/82f3c27b-be6d-55be-bad5-fa58864d63c5
-- title:
--   Convolution algebra of bi-invariant functions on a Hecke pair
-- statement:
--   Fix a group $G$, a subgroup $U \le G$ and a commutative ring $R_0$. The predicate [`HeckePair.IsHeckeFun`](../def/LocalLanglands_HeckePair.html#L18) on a function $f : G \to R_0$ is a structure with three fields: $f(ux) = f(x)$ for all $u \in U$ and $x \in G$; $f(xu) = f(x)$ for all $u \in U$ and $x \in G$; and the image of the support of $f$ in the left-coset space $G/U$ is finite (note: finiteness of the image of the support in $G/U$, not finiteness of the support itself, and there is no hypothesis making $U$ open, compact or of finite index). The functions satisfying this predicate form an $R_0$-submodule [`HeckePair.heckeSubmodule`](../def/LocalLanglands_HeckePair.html#L57) of $G \to R_0$, abbreviated [`HeckePair.HeckeAlgebra U R₀`](../def/LocalLanglands_HeckePair.html#L63). Multiplication is convolution: [`HeckePair.convTerm f₁ f₂ x`](../def/LocalLanglands_HeckePair.html#L91) is the well-defined function on $G/U$ sending $yU \mapsto f_1(y) f_2(y^{-1}x)$ (well-definedness uses right $U$-invariance of $f_1$ and left $U$-invariance of $f_2$), and [`HeckePair.conv f₁ f₂ x`](../def/LocalLanglands_HeckePair.html#L113) is its unconditional sum $\sum^{\mathrm{f}}_{c \in G/U}$ over the coset space, finite because the support of `convTerm` lies in the image of the support of $f_1$. The unit [`HeckePair.heckeOne`](../def/LocalLanglands_HeckePair.html#L190) is the indicator function of $U$. Accompanying lemmas check closure under addition and scalar multiplication, the support bounds needed for finiteness, bilinearity, the unit laws and associativity, yielding `Ring` and `Algebra R₀` instances on `HeckeAlgebra U R₀`. Finally [`HeckePair.doubleCoset U g`](../def/LocalLanglands_HeckePair.html#L405) is the set $U\{g\}U$, with the membership criterion $x = ugv$, stability under left and right multiplication by $U$, and the identity of images in $G/U$ of $UgU$ and $Ug$; [`HeckePair.heckeIndicator R₀ g hfin`](../def/LocalLanglands_HeckePair.html#L443) is the indicator of $UgU$, an element of the algebra given a proof `hfin` that the image of $Ug$ in $G/U$ is finite, and it equals $1$ when $g \in U$.
--
--   **Relation to Mathlib.** Mathlib has no Hecke algebra of an abstract Hecke pair; this construction, including the `IsHeckeFun` predicate, the convolution product and the resulting `Ring`/`Algebra` instances, is the project's own, built on Mathlib's quotient groups, submodules and unconditional sums.
--
--   **Where it is used.** The construction is stated for an abstract pair $(G,U)$ so that it can be instantiated at $(\mathrm{GL}_2(L_w), \mathrm{GL}_2(\mathcal{O}_w))$ for completions of the number fields occurring in the argument, giving the local spherical Hecke algebras and the double-coset operators used on the automorphic side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalLanglands_HeckePair.lean

import Mathlib
import Definitions.Def_AbstractHeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise
open Function MulAction

namespace HeckePair

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
variable (R₀ : Type*) [CommRing R₀]

variable {U R₀} in

structure IsHeckeFun (f : G → R₀) : Prop where

  left_inv : ∀ u ∈ U, ∀ x, f (u * x) = f x

  right_inv : ∀ u ∈ U, ∀ x, f (x * u) = f x

  finite_cosets : ((QuotientGroup.mk '' (Function.support f)) : Set (G ⧸ U)).Finite

variable {U R₀} in

theorem IsHeckeFun.zero : IsHeckeFun (U := U) (0 : G → R₀) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, by simp⟩

variable {U R₀} in

theorem IsHeckeFun.add {f g : G → R₀} (hf : IsHeckeFun (U := U) f) (hg : IsHeckeFun (U := U) g) :
    IsHeckeFun (U := U) (f + g) := by
  refine ⟨fun u hu x => ?_, fun u hu x => ?_, ?_⟩
  · simp only [Pi.add_apply, hf.left_inv u hu, hg.left_inv u hu]
  · simp only [Pi.add_apply, hf.right_inv u hu, hg.right_inv u hu]
  · refine ((hf.finite_cosets.union hg.finite_cosets).subset ?_)
    rw [← Set.image_union]
    refine Set.image_mono fun x hx => ?_
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
    exact hx (by simp [Pi.add_apply, hcon.1, hcon.2])

variable {U R₀} in

theorem IsHeckeFun.smul {f : G → R₀} (r : R₀) (hf : IsHeckeFun (U := U) f) :
    IsHeckeFun (U := U) (r • f) := by
  refine ⟨fun u hu x => ?_, fun u hu x => ?_, ?_⟩
  · simp only [Pi.smul_apply, hf.left_inv u hu]
  · simp only [Pi.smul_apply, hf.right_inv u hu]
  · refine hf.finite_cosets.subset (Set.image_mono ?_)
    intro x hx
    simp only [Function.mem_support, Pi.smul_apply, smul_eq_mul] at hx
    exact Function.mem_support.mpr (right_ne_zero_of_mul hx)

def heckeSubmodule : Submodule R₀ (G → R₀) where
  carrier := {f | IsHeckeFun (U := U) f}
  add_mem' hf hg := hf.add hg
  zero_mem' := IsHeckeFun.zero
  smul_mem' r _ hf := hf.smul r

abbrev HeckeAlgebra := heckeSubmodule U R₀

variable {U R₀}

theorem mem_heckeSubmodule_iff {f : G → R₀} :
    f ∈ heckeSubmodule U R₀ ↔ IsHeckeFun (U := U) f := Iff.rfl

theorem isHeckeFun (f : HeckeAlgebra U R₀) : IsHeckeFun (U := U) (f : G → R₀) := f.2

theorem apply_left_mul (f : HeckeAlgebra U R₀) {u : G} (hu : u ∈ U) (x : G) :
    (f : G → R₀) (u * x) = (f : G → R₀) x := f.2.left_inv u hu x

theorem apply_mul_right (f : HeckeAlgebra U R₀) {u : G} (hu : u ∈ U) (x : G) :
    (f : G → R₀) (x * u) = (f : G → R₀) x := f.2.right_inv u hu x

theorem finite_cosets (f : HeckeAlgebra U R₀) :
    ((QuotientGroup.mk '' (Function.support (f : G → R₀))) : Set (G ⧸ U)).Finite :=
  f.2.finite_cosets

@[ext] theorem ext {f g : HeckeAlgebra U R₀} (h : ∀ x, (f : G → R₀) x = (g : G → R₀) x) :
    f = g := Subtype.ext (funext h)

@[simp] theorem coe_apply_add (f g : HeckeAlgebra U R₀) (x : G) :
    ((f + g : HeckeAlgebra U R₀) : G → R₀) x = (f : G → R₀) x + (g : G → R₀) x := rfl

@[simp] theorem coe_apply_smul (r : R₀) (f : HeckeAlgebra U R₀) (x : G) :
    ((r • f : HeckeAlgebra U R₀) : G → R₀) x = r * (f : G → R₀) x := rfl

def convTerm (f₁ f₂ : HeckeAlgebra U R₀) (x : G) : G ⧸ U → R₀ :=
  Quotient.lift (fun y => (f₁ : G → R₀) y * (f₂ : G → R₀) (y⁻¹ * x)) <| by
    intro a b hab
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, a * u = b :=
      ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩
    rw [apply_mul_right f₁ hu, mul_inv_rev, mul_assoc, apply_left_mul f₂ (inv_mem hu)]

@[simp] theorem convTerm_mk (f₁ f₂ : HeckeAlgebra U R₀) (x y : G) :
    convTerm f₁ f₂ x (QuotientGroup.mk y) = (f₁ : G → R₀) y * (f₂ : G → R₀) (y⁻¹ * x) := rfl

theorem support_convTerm_subset (f₁ f₂ : HeckeAlgebra U R₀) (x : G) :
    Function.support (convTerm f₁ f₂ x)
      ⊆ QuotientGroup.mk '' (Function.support (f₁ : G → R₀)) := by
  intro c hc
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  rw [Function.mem_support, convTerm_mk] at hc
  exact ⟨y, left_ne_zero_of_mul hc, rfl⟩

theorem finite_support_convTerm (f₁ f₂ : HeckeAlgebra U R₀) (x : G) :
    (Function.support (convTerm f₁ f₂ x)).Finite :=
  (finite_cosets f₁).subset (support_convTerm_subset f₁ f₂ x)

def conv (f₁ f₂ : HeckeAlgebra U R₀) (x : G) : R₀ :=
  ∑ᶠ c : G ⧸ U, convTerm f₁ f₂ x c

theorem conv_eq_sum (f₁ f₂ : HeckeAlgebra U R₀) (x : G) {T : Finset (G ⧸ U)}
    (hT : QuotientGroup.mk '' (Function.support (f₁ : G → R₀)) ⊆ (T : Set (G ⧸ U))) :
    conv f₁ f₂ x = ∑ c ∈ T, convTerm f₁ f₂ x c :=
  finsum_eq_sum_of_support_subset _ <| (support_convTerm_subset f₁ f₂ x).trans hT

theorem support_conv_subset (f₁ f₂ : HeckeAlgebra U R₀) :
    Function.support (conv f₁ f₂)
      ⊆ Function.support (f₁ : G → R₀) * Function.support (f₂ : G → R₀) := by
  intro x hx
  have h : ∃ c, convTerm f₁ f₂ x c ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by simp only [conv, finsum_congr h, finsum_zero])
  obtain ⟨c, hc⟩ := h
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  rw [convTerm_mk] at hc
  exact ⟨y, left_ne_zero_of_mul hc, y⁻¹ * x, right_ne_zero_of_mul hc, by group⟩

theorem finite_image_mk_mul_support (f₁ f₂ : HeckeAlgebra U R₀) :
    ((QuotientGroup.mk ''
      (Function.support (f₁ : G → R₀) * Function.support (f₂ : G → R₀))) :
        Set (G ⧸ U)).Finite := by
  refine Set.Finite.subset (Set.Finite.image2 (fun c d => Quotient.out c • d)
    (finite_cosets f₁) (finite_cosets f₂)) ?_
  rintro _ ⟨_, ⟨y, hy, z, hz, rfl⟩, rfl⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U y
  refine Set.mem_image2.mpr ⟨QuotientGroup.mk y, ⟨y, hy, rfl⟩,
    QuotientGroup.mk ((u : G)⁻¹ * z), ⟨(u : G)⁻¹ * z, ?_, rfl⟩, ?_⟩
  ·
    simpa only [Function.mem_support, apply_left_mul f₂ (inv_mem u.2)] using hz
  ·
    rw [hu, MulAction.Quotient.smul_mk, smul_eq_mul]
    congr 1
    group

theorem finite_image_mk_support_conv (f₁ f₂ : HeckeAlgebra U R₀) :
    ((QuotientGroup.mk '' (Function.support (conv f₁ f₂))) : Set (G ⧸ U)).Finite :=
  (finite_image_mk_mul_support f₁ f₂).subset <| Set.image_mono <| support_conv_subset f₁ f₂

theorem convTerm_smul_left (f₁ f₂ : HeckeAlgebra U R₀) {u : G} (hu : u ∈ U) (x : G) (y : G) :
    convTerm f₁ f₂ (u * x) (QuotientGroup.mk (u * y))
      = convTerm f₁ f₂ x (QuotientGroup.mk y) := by
  rw [convTerm_mk, convTerm_mk, apply_left_mul f₁ hu]
  congr 2
  group

theorem isHeckeFun_conv (f₁ f₂ : HeckeAlgebra U R₀) : IsHeckeFun (U := U) (conv f₁ f₂) := by
  refine ⟨fun u hu x => ?_, fun u hu x => ?_, finite_image_mk_support_conv f₁ f₂⟩
  ·
    calc conv f₁ f₂ (u * x)
        = ∑ᶠ c : G ⧸ U, convTerm f₁ f₂ (u * x) ((MulAction.toPerm u) c) :=
          (finsum_comp_equiv (MulAction.toPerm u)).symm
      _ = ∑ᶠ c : G ⧸ U, convTerm f₁ f₂ x c := by
          refine finsum_congr fun c => ?_
          obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
          rw [MulAction.toPerm_apply, MulAction.Quotient.smul_mk, smul_eq_mul]
          exact convTerm_smul_left f₁ f₂ hu x y
      _ = conv f₁ f₂ x := rfl
  ·
    refine finsum_congr fun c => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    rw [convTerm_mk, convTerm_mk, ← mul_assoc, apply_mul_right f₂ hu]

instance : Mul (HeckeAlgebra U R₀) :=
  ⟨fun f₁ f₂ => ⟨conv f₁ f₂, isHeckeFun_conv f₁ f₂⟩⟩

theorem coe_mul (f₁ f₂ : HeckeAlgebra U R₀) :
    ((f₁ * f₂ : HeckeAlgebra U R₀) : G → R₀) = conv f₁ f₂ := rfl

theorem mul_apply (f₁ f₂ : HeckeAlgebra U R₀) (x : G) :
    ((f₁ * f₂ : HeckeAlgebra U R₀) : G → R₀) x = ∑ᶠ c : G ⧸ U, convTerm f₁ f₂ x c := rfl

variable (U R₀) in

def heckeOne : HeckeAlgebra U R₀ :=
  ⟨Set.indicator (U : Set G) 1, by
    refine ⟨fun u hu x => ?_, fun u hu x => ?_, ?_⟩
    · by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem (mul_mem hu hx : u * x ∈ U),
          Set.indicator_of_mem hx, Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun h => hx (by simpa using mul_mem (inv_mem hu) h)),
          Set.indicator_of_notMem hx]
    · by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem (mul_mem hx hu : x * u ∈ U),
          Set.indicator_of_mem hx, Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun h => hx (by simpa using mul_mem h (inv_mem hu))),
          Set.indicator_of_notMem hx]
    · refine (Set.finite_singleton (QuotientGroup.mk (1 : G))).subset ?_
      rintro _ ⟨y, hy, rfl⟩
      have hyU : y ∈ U := by
        by_contra hyU
        exact hy (Set.indicator_of_notMem hyU 1)
      exact Set.mem_singleton_iff.mpr (QuotientGroup.eq.mpr (by simpa using inv_mem hyU))⟩

instance : One (HeckeAlgebra U R₀) := ⟨heckeOne U R₀⟩

theorem coe_one : ((1 : HeckeAlgebra U R₀) : G → R₀) = Set.indicator (U : Set G) 1 := rfl

theorem one_apply_of_mem {x : G} (hx : x ∈ U) : ((1 : HeckeAlgebra U R₀) : G → R₀) x = 1 :=
  Set.indicator_of_mem hx 1

theorem one_apply_of_notMem {x : G} (hx : x ∉ U) :
    ((1 : HeckeAlgebra U R₀) : G → R₀) x = 0 :=
  Set.indicator_of_notMem hx 1

protected theorem one_mul (f : HeckeAlgebra U R₀) : 1 * f = f := by
  ext x
  rw [mul_apply]

  refine (finsum_eq_single _ (QuotientGroup.mk (1 : G)) fun c hc => ?_).trans ?_
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    rw [convTerm_mk, one_apply_of_notMem, zero_mul]
    intro hyU
    exact hc (QuotientGroup.eq.mpr (by simpa using inv_mem hyU))
  · rw [convTerm_mk, one_apply_of_mem (one_mem U), one_mul, inv_one, one_mul]

protected theorem mul_one (f : HeckeAlgebra U R₀) : f * 1 = f := by
  ext x
  rw [mul_apply]

  refine (finsum_eq_single _ (QuotientGroup.mk x) fun c hc => ?_).trans ?_
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    rw [convTerm_mk, one_apply_of_notMem, mul_zero]
    intro hyx
    exact hc (QuotientGroup.eq.mpr hyx)
  · rw [convTerm_mk, inv_mul_cancel, one_apply_of_mem (one_mem U), mul_one]

protected theorem zero_mul (f : HeckeAlgebra U R₀) : 0 * f = 0 := by
  ext x
  rw [mul_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  rw [convTerm_mk]
  exact zero_mul _

protected theorem mul_zero (f : HeckeAlgebra U R₀) : f * 0 = 0 := by
  ext x
  rw [mul_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  rw [convTerm_mk]
  exact mul_zero _

protected theorem add_mul (f₁ f₂ g : HeckeAlgebra U R₀) :
    (f₁ + f₂) * g = f₁ * g + f₂ * g := by
  ext x
  rw [mul_apply]
  have h : ∀ c : G ⧸ U, convTerm (f₁ + f₂) g x c
      = convTerm f₁ g x c + convTerm f₂ g x c := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [convTerm_mk, coe_apply_add, add_mul]
  rw [finsum_congr h,
    finsum_add_distrib (finite_support_convTerm f₁ g x) (finite_support_convTerm f₂ g x)]
  rfl

protected theorem mul_add (f g₁ g₂ : HeckeAlgebra U R₀) :
    f * (g₁ + g₂) = f * g₁ + f * g₂ := by
  ext x
  rw [mul_apply]
  have h : ∀ c : G ⧸ U, convTerm f (g₁ + g₂) x c
      = convTerm f g₁ x c + convTerm f g₂ x c := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [convTerm_mk, coe_apply_add, mul_add]
  rw [finsum_congr h,
    finsum_add_distrib (finite_support_convTerm f g₁ x) (finite_support_convTerm f g₂ x)]
  rfl

protected theorem smul_mul (r : R₀) (f g : HeckeAlgebra U R₀) :
    (r • f) * g = r • (f * g) := by
  ext x
  rw [mul_apply]
  have h : ∀ c : G ⧸ U, convTerm (r • f) g x c = r * convTerm f g x c := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [convTerm_mk, coe_apply_smul, mul_assoc]
  rw [finsum_congr h, ← mul_finsum' _ _ (finite_support_convTerm f g x)]
  rfl

protected theorem mul_smul_comm (r : R₀) (f g : HeckeAlgebra U R₀) :
    f * (r • g) = r • (f * g) := by
  ext x
  rw [mul_apply]
  have h : ∀ c : G ⧸ U, convTerm f (r • g) x c = r * convTerm f g x c := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    simp only [convTerm_mk, coe_apply_smul]
    ring
  rw [finsum_congr h, ← mul_finsum' _ _ (finite_support_convTerm f g x)]
  rfl

protected theorem mul_assoc (f₁ f₂ f₃ : HeckeAlgebra U R₀) :
    f₁ * f₂ * f₃ = f₁ * (f₂ * f₃) := by
  ext x

  set A : G ⧸ U → G ⧸ U → R₀ :=
    fun c d => convTerm f₁ f₂ (Quotient.out c) d * (f₃ : G → R₀) ((Quotient.out c)⁻¹ * x)
    with hA

  set T₁ : Finset (G ⧸ U) := (finite_image_mk_mul_support f₁ f₂).toFinset with hT₁def
  set T₂ : Finset (G ⧸ U) := (finite_cosets f₁).toFinset with hT₂def
  have hT₁ : (QuotientGroup.mk ''
      (Function.support (f₁ : G → R₀) * Function.support (f₂ : G → R₀))
        : Set (G ⧸ U)) ⊆ ↑T₁ := by rw [hT₁def]; simp
  have hT₂ : (QuotientGroup.mk '' (Function.support (f₁ : G → R₀)) : Set (G ⧸ U)) ⊆ ↑T₂ := by
    rw [hT₂def]; simp

  have hAsupp₂ : ∀ c, Function.support (A c) ⊆ ↑T₂ := by
    intro c d hd
    refine hT₂ (support_convTerm_subset f₁ f₂ (Quotient.out c) (Function.mem_support.mpr ?_))
    intro h0
    apply hd
    simp only [hA, h0, zero_mul]
  have hAsupp₁ : ∀ d, Function.support (A · d) ⊆ ↑T₁ := by
    intro d c hc
    refine hT₁ ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective d
    simp only [hA, convTerm_mk, Function.mem_support] at hc
    have h₁ : (f₁ : G → R₀) z ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hc)
    have h₂ : (f₂ : G → R₀) (z⁻¹ * Quotient.out c) ≠ 0 :=
      right_ne_zero_of_mul (left_ne_zero_of_mul hc)
    exact ⟨Quotient.out c, ⟨z, h₁, z⁻¹ * Quotient.out c, h₂, by group⟩,
      QuotientGroup.out_eq' c⟩

  have lhs_eq : ((f₁ * f₂ * f₃ : HeckeAlgebra U R₀) : G → R₀) x = ∑ᶠ c, ∑ᶠ d, A c d := by
    rw [mul_apply]
    refine finsum_congr fun c => ?_
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rw [convTerm_mk, mul_apply, finsum_mul' _ _ (finite_support_convTerm f₁ f₂ _)]

  have swap_eq : (∑ᶠ c, ∑ᶠ d, A c d) = ∑ᶠ d, ∑ᶠ c, A c d := by
    have e₁ : (∑ᶠ c, ∑ᶠ d, A c d) = ∑ᶠ c, ∑ d ∈ T₂, A c d :=
      finsum_congr fun c => finsum_eq_sum_of_support_subset _ (hAsupp₂ c)
    have e₂ : (∑ᶠ d, ∑ᶠ c, A c d) = ∑ᶠ d, ∑ c ∈ T₁, A c d :=
      finsum_congr fun d => finsum_eq_sum_of_support_subset _ (hAsupp₁ d)
    rw [e₁, e₂,
      finsum_eq_sum_of_support_subset (fun c => ∑ d ∈ T₂, A c d)
        (fun c hc => by
          obtain ⟨d, _, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
          exact hAsupp₁ d hd),
      finsum_eq_sum_of_support_subset (fun d => ∑ c ∈ T₁, A c d)
        (fun d hd => by
          obtain ⟨c, _, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
          exact hAsupp₂ c hc)]
    exact Finset.sum_comm

  have inner_eq : ∀ d, (∑ᶠ c, A c d) = convTerm f₁ (f₂ * f₃) x d := by
    intro d
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective d
    rw [convTerm_mk, mul_apply, mul_finsum' _ _ (finite_support_convTerm f₂ f₃ (z⁻¹ * x)),
      ← finsum_comp_equiv (MulAction.toPerm z)]
    refine finsum_congr fun e => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective e
    simp only [MulAction.toPerm_apply, MulAction.Quotient.smul_mk, smul_eq_mul, hA]
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (z * w)
    rw [hu, convTerm_mk,
      show z⁻¹ * (z * w * (u : G)) = w * (u : G) by group, apply_mul_right f₂ u.2,
      show (z * w * (u : G))⁻¹ * x = (u : G)⁻¹ * (w⁻¹ * (z⁻¹ * x)) by group,
      apply_left_mul f₃ (inv_mem u.2), convTerm_mk, mul_assoc]

  show ((f₁ * f₂ * f₃ : HeckeAlgebra U R₀) : G → R₀) x
    = ((f₁ * (f₂ * f₃) : HeckeAlgebra U R₀) : G → R₀) x
  rw [lhs_eq, swap_eq, finsum_congr inner_eq]
  rfl

instance : Ring (HeckeAlgebra U R₀) where
  __ : AddCommGroup (HeckeAlgebra U R₀) := inferInstance
  mul := (· * ·)
  one := 1
  mul_assoc := HeckePair.mul_assoc
  one_mul := HeckePair.one_mul
  mul_one := HeckePair.mul_one
  left_distrib := HeckePair.mul_add
  right_distrib := fun f₁ f₂ g => HeckePair.add_mul f₁ f₂ g
  zero_mul := HeckePair.zero_mul
  mul_zero := HeckePair.mul_zero

instance : SMulCommClass R₀ (HeckeAlgebra U R₀) (HeckeAlgebra U R₀) :=
  ⟨fun r f g => (HeckePair.mul_smul_comm r f g).symm⟩

instance : IsScalarTower R₀ (HeckeAlgebra U R₀) (HeckeAlgebra U R₀) :=
  ⟨fun r f g => by rw [smul_eq_mul, smul_eq_mul, HeckePair.smul_mul]⟩

instance : Algebra R₀ (HeckeAlgebra U R₀) :=
  Algebra.ofModule HeckePair.smul_mul HeckePair.mul_smul_comm

variable (U) in

def doubleCoset (g : G) : Set G := (U : Set G) * {g} * (U : Set G)

theorem mem_doubleCoset_iff {g x : G} :
    x ∈ doubleCoset U g ↔ ∃ u ∈ U, ∃ v ∈ U, u * g * v = x := by
  constructor
  · rintro ⟨_, ⟨u, hu, _, rfl, rfl⟩, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u * g, ⟨u, hu, g, rfl, rfl⟩, v, hv, rfl⟩

theorem self_mem_doubleCoset (g : G) : g ∈ doubleCoset U g :=
  mem_doubleCoset_iff.mpr ⟨1, one_mem U, 1, one_mem U, by group⟩

theorem mul_mem_doubleCoset {g x : G} (hx : x ∈ doubleCoset U g) {u : G} (hu : u ∈ U) :
    u * x ∈ doubleCoset U g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hx
  exact mem_doubleCoset_iff.mpr ⟨u * a, mul_mem hu ha, b, hb, by group⟩

theorem doubleCoset_mul_mem {g x : G} (hx : x ∈ doubleCoset U g) {u : G} (hu : u ∈ U) :
    x * u ∈ doubleCoset U g := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hx
  exact mem_doubleCoset_iff.mpr ⟨a, ha, b * u, mul_mem hb hu, by group⟩

theorem image_mk_doubleCoset (g : G) :
    (QuotientGroup.mk '' (doubleCoset U g) : Set (G ⧸ U))
      = QuotientGroup.mk '' ((U : Set G) * {g}) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hx
    refine ⟨a * g, ⟨a, ha, g, rfl, rfl⟩, QuotientGroup.eq.mpr ?_⟩
    rw [show (a * g)⁻¹ * (a * g * b) = b by group]
    exact hb
  · rintro _ ⟨w, ⟨a, ha, v, hv, rfl⟩, rfl⟩
    obtain rfl : v = g := hv
    exact ⟨a * v, mem_doubleCoset_iff.mpr ⟨a, ha, 1, one_mem U, by group⟩, rfl⟩

variable (R₀) in

def heckeIndicator (g : G) (hfin : (QuotientGroup.mk '' ((U : Set G) * {g})
    : Set (G ⧸ U)).Finite) : HeckeAlgebra U R₀ :=
  ⟨Set.indicator (doubleCoset U g) 1, by
    refine ⟨fun u hu x => ?_, fun u hu x => ?_, ?_⟩
    · by_cases hx : x ∈ doubleCoset U g
      · simp only [Set.indicator_of_mem (mul_mem_doubleCoset hx hu), Set.indicator_of_mem hx,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun h => hx ?_), Set.indicator_of_notMem hx]
        simpa using mul_mem_doubleCoset h (inv_mem hu)
    · by_cases hx : x ∈ doubleCoset U g
      · simp only [Set.indicator_of_mem (doubleCoset_mul_mem hx hu), Set.indicator_of_mem hx,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun h => hx ?_), Set.indicator_of_notMem hx]
        simpa using doubleCoset_mul_mem h (inv_mem hu)
    · rw [← image_mk_doubleCoset] at hfin
      refine hfin.subset (Set.image_mono ?_)
      intro y hy
      by_contra hyD
      exact hy (Set.indicator_of_notMem hyD 1)⟩

theorem heckeIndicator_apply_of_mem {g x : G} (hfin) (hx : x ∈ doubleCoset U g) :
    ((heckeIndicator R₀ g hfin : HeckeAlgebra U R₀) : G → R₀) x = 1 :=
  Set.indicator_of_mem hx 1

theorem heckeIndicator_apply_of_notMem {g x : G} (hfin) (hx : x ∉ doubleCoset U g) :
    ((heckeIndicator R₀ g hfin : HeckeAlgebra U R₀) : G → R₀) x = 0 :=
  Set.indicator_of_notMem hx 1

theorem heckeIndicator_of_mem {u : G} (hu : u ∈ U) (hfin) :
    heckeIndicator R₀ u hfin = (1 : HeckeAlgebra U R₀) := by
  ext x
  rw [coe_one]
  by_cases hx : x ∈ U
  · rw [heckeIndicator_apply_of_mem _ (mem_doubleCoset_iff.mpr
      ⟨x * u⁻¹, mul_mem hx (inv_mem hu), 1, one_mem U, by group⟩), Set.indicator_of_mem hx]
    rfl
  · rw [heckeIndicator_apply_of_notMem, Set.indicator_of_notMem hx]
    intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp h
    exact hx (mul_mem (mul_mem ha hu) hb)

end
end HeckePair


