-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebraLevel
-- name    : GroundTheory_AutomorphicForms_HeckeAlgebraLevel
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:53:53.929416+00:00
-- url     : https://prove2.me/theorems/1b8dd48b-bc11-4196-a33b-1045f2a86b3c
-- title:
--   Hecke Algebra Level
-- statement:
--   Definitions and structural lemmas for Hecke Algebra Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HeckeAlgebraLevel.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mul_apply
import Theorems.Thm_GroundTheory_Automorphic_indicator_mem_locallyConstantCompactSupport
import Theorems.Thm_GroundTheory_Automorphic_mem_fixedVectors_iff_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G]
  [BorelSpace G] in

theorem smooth_of_mem_fixedVectors {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} (hKo : IsOpen (K : Set G)) {v : V}
    (hv : v ∈ fixedVectors ρ K) : v ∈ smoothVectors ρ :=
  Subgroup.isOpen_mono (mem_fixedVectors_iff_le.1 hv) hKo
namespace HeckeAlgebra
variable (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G} (hKc : IsCompact (K : Set G))
  (hKo : IsOpen (K : Set G))
include hKc hKo in

theorem measureReal_compactOpen_pos : 0 < μ.real (K : Set G) :=
  ENNReal.toReal_pos (hKo.measure_ne_zero μ ⟨1, K.one_mem⟩) hKc.measure_lt_top.ne
def idem : HeckeAlgebra μ :=
  mk μ ((K : Set G).indicator fun _ => ((μ.real (K : Set G) : ℂ))⁻¹)
    (indicator_mem_locallyConstantCompactSupport hKc hKo _)
variable {μ}
theorem idem_apply (x : G) :
    idem μ hKc hKo x = (K : Set G).indicator (fun _ => ((μ.real (K : Set G) : ℂ))⁻¹) x := rfl
theorem idem_apply_of_mem {x : G} (hx : x ∈ K) : idem μ hKc hKo x = ((μ.real (K : Set G) : ℂ))⁻¹ := by
  rw [idem_apply]
  exact Set.indicator_of_mem (show x ∈ (K : Set G) from hx) _
theorem idem_apply_of_notMem {x : G} (hx : x ∉ K) : idem μ hKc hKo x = 0 := by
  rw [idem_apply]
  exact Set.indicator_of_notMem (show x ∉ (K : Set G) from hx) _
theorem idem_mul_left {k : G} (hk : k ∈ K) (x : G) : idem μ hKc hKo (k * x) = idem μ hKc hKo x := by
  by_cases hx : x ∈ K
  · rw [idem_apply_of_mem hKc hKo (mul_mem hk hx), idem_apply_of_mem hKc hKo hx]
  · rw [idem_apply_of_notMem hKc hKo hx, idem_apply_of_notMem hKc hKo]
    exact fun h => hx (by simpa using mul_mem (inv_mem hk) h)
theorem idem_mul_right {k : G} (hk : k ∈ K) (x : G) : idem μ hKc hKo (x * k) = idem μ hKc hKo x := by
  by_cases hx : x ∈ K
  · rw [idem_apply_of_mem hKc hKo (mul_mem hx hk), idem_apply_of_mem hKc hKo hx]
  · rw [idem_apply_of_notMem hKc hKo hx, idem_apply_of_notMem hKc hKo]
    exact fun h => hx (by simpa using mul_mem h (inv_mem hk))
theorem idem_inv (x : G) : idem μ hKc hKo x⁻¹ = idem μ hKc hKo x := by
  by_cases hx : x ∈ K
  · rw [idem_apply_of_mem hKc hKo (inv_mem hx), idem_apply_of_mem hKc hKo hx]
  · have hx' : x⁻¹ ∉ K := fun h => hx (by simpa using inv_mem h)
    rw [idem_apply_of_notMem hKc hKo hx, idem_apply_of_notMem hKc hKo hx']
theorem integral_idem_mul {F : G → ℂ} (hF : ∀ k ∈ K, F k = F 1) :
    ∫ g, idem μ hKc hKo g * F g ∂μ = F 1 := by
  have hpt : (fun g => idem μ hKc hKo g * F g) =
      (K : Set G).indicator (fun _ => ((μ.real (K : Set G) : ℂ))⁻¹ * F 1) := by
    funext g
    by_cases hg : g ∈ K
    · rw [idem_apply_of_mem hKc hKo hg, hF g hg,
        Set.indicator_of_mem (show g ∈ (K : Set G) from hg)]
    · rw [idem_apply_of_notMem hKc hKo hg, zero_mul,
        Set.indicator_of_notMem (show g ∉ (K : Set G) from hg)]
  have hne : ((μ.real (K : Set G) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (measureReal_compactOpen_pos μ hKc hKo).ne'
  rw [hpt, integral_indicator_const _ hKo.measurableSet, Complex.real_smul, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
theorem heckeAct_idem_of_mem {v : V} (hv : v ∈ fixedVectors ρ K) :
    heckeAct μ ρ (idem μ hKc hKo) v = v := by
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct μ (idem μ hKc hKo).mem (smooth_of_mem_fixedVectors hKo hv),
    integral_idem_mul hKc hKo (F := fun g => φ (ρ g v)) (fun k hk => by simp [hv k hk])]
  simp
theorem heckeAct_idem_mem {v : V} (hv : v ∈ smoothVectors ρ) :
    heckeAct μ ρ (idem μ hKc hKo) v ∈ fixedVectors ρ K :=
  heckeAct_mem_fixedVectors (idem μ hKc hKo).mem (fun _ hk x => idem_mul_left hKc hKo hk x) hv
variable (μ) in

def biInvariant (K : Subgroup G) : NonUnitalSubalgebra ℂ (HeckeAlgebra μ) where
  carrier := {f | ∀ k ∈ K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x}
  add_mem' {a b} ha hb k hk x := by
    simp only [coe_add, Pi.add_apply, (ha k hk x).1, (hb k hk x).1, (ha k hk x).2, (hb k hk x).2,
      and_self]
  zero_mem' k _ x := by simp
  mul_mem' {a b} ha hb k hk x := by
    constructor
    · rw [mul_apply, mul_apply, ← integral_mul_left_eq_self _ k]
      congr 1
      funext y
      rw [(ha k hk y).1, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    · rw [coe_mul, groupConv_mul_right (fun g => (hb k hk g).2)]
  smul_mem' c a ha k hk x := by
    simp only [coe_smul, Pi.smul_apply, smul_eq_mul, (ha k hk x).1, (ha k hk x).2, and_self]
theorem mem_biInvariant {f : HeckeAlgebra μ} :
    f ∈ biInvariant μ K ↔ ∀ k ∈ K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x := Iff.rfl
theorem idem_mul_eq_self_iff {f : HeckeAlgebra μ} :
    idem μ hKc hKo * f = f ↔ ∀ k ∈ K, ∀ x, f (k * x) = f x := by
  rw [← mem_fixedVectors_leftReg, ← heckeAct_leftReg]
  constructor
  · intro h
    rw [← h]
    exact heckeAct_idem_mem hKc hKo (isSmooth_leftReg f)
  · exact heckeAct_idem_of_mem hKc hKo
theorem mul_idem_eq_self_iff {f : HeckeAlgebra μ} :
    f * idem μ hKc hKo = f ↔ ∀ k ∈ K, ∀ x, f (x * k) = f x := by
  constructor
  · intro h k hk x
    rw [← h, coe_mul, groupConv_mul_right (fun g => idem_mul_right hKc hKo hk g)]
  · intro h
    ext x
    rw [mul_apply, ← integral_mul_left_eq_self _ x]
    simp only [mul_inv_rev, inv_mul_cancel_right, idem_inv]
    simp_rw [mul_comm (f _)]
    rw [integral_idem_mul (μ := μ) hKc hKo (F := fun y => f (x * y)) (fun k hk => by simp [h k hk x]),
      mul_one]
theorem mem_biInvariant_iff_idem {f : HeckeAlgebra μ} :
    f ∈ biInvariant μ K ↔ idem μ hKc hKo * f = f ∧ f * idem μ hKc hKo = f := by
  rw [idem_mul_eq_self_iff, mul_idem_eq_self_iff, mem_biInvariant]
  exact ⟨fun h => ⟨fun k hk x => (h k hk x).1, fun k hk x => (h k hk x).2⟩,
    fun h k hk x => ⟨h.1 k hk x, h.2 k hk x⟩⟩
theorem isIdempotentElem_idem : IsIdempotentElem (idem μ hKc hKo) :=
  (idem_mul_eq_self_iff hKc hKo).2 fun _ hk x => idem_mul_left hKc hKo hk x
theorem idem_mem_biInvariant : idem μ hKc hKo ∈ biInvariant μ K :=
  (mem_biInvariant_iff_idem hKc hKo).2 ⟨isIdempotentElem_idem hKc hKo, isIdempotentElem_idem hKc hKo⟩
theorem biInvariant_eq_range :
    (biInvariant μ K : Set (HeckeAlgebra μ)) = range fun f => idem μ hKc hKo * f * idem μ hKc hKo := by
  ext f
  constructor
  · intro hf
    obtain ⟨h1, h2⟩ := (mem_biInvariant_iff_idem hKc hKo).1 hf
    exact ⟨f, by show idem μ hKc hKo * f * idem μ hKc hKo = f; rw [h1, h2]⟩
  · rintro ⟨g, rfl⟩
    have hi := isIdempotentElem_idem hKc hKo (μ := μ)
    refine (mem_biInvariant_iff_idem hKc hKo).2 ⟨?_, ?_⟩
    · rw [← mul_assoc, ← mul_assoc, hi.eq]
    · rw [mul_assoc, hi.eq]
variable (μ) in

def HeckeAlgebraLevel (K : Subgroup G) (_hKc : IsCompact (K : Set G)) (_hKo : IsOpen (K : Set G)) :
    Type _ :=
  biInvariant μ K
namespace HeckeAlgebraLevel
instance : NonUnitalRing (HeckeAlgebraLevel μ K hKc hKo) :=
  inferInstanceAs (NonUnitalRing (biInvariant μ K))
instance : Module ℂ (HeckeAlgebraLevel μ K hKc hKo) :=
  inferInstanceAs (Module ℂ (biInvariant μ K))
def val (h : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ :=
  (show biInvariant μ K from h).1
instance : CoeOut (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebra μ) := ⟨val hKc hKo⟩
theorem val_mem (h : HeckeAlgebraLevel μ K hKc hKo) : (h : HeckeAlgebra μ) ∈ biInvariant μ K :=
  (show biInvariant μ K from h).2
def mk (f : HeckeAlgebra μ) (hf : f ∈ biInvariant μ K) : HeckeAlgebraLevel μ K hKc hKo :=
  (⟨f, hf⟩ : biInvariant μ K)
@[simp] theorem val_mk (f : HeckeAlgebra μ) (hf : f ∈ biInvariant μ K) :
    ((mk hKc hKo f hf : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) = f := rfl
theorem val_injective : Function.Injective (val hKc hKo : HeckeAlgebraLevel μ K hKc hKo → _) :=
  fun _ _ h => Subtype.ext h
@[ext] theorem ext {a b : HeckeAlgebraLevel μ K hKc hKo} (h : (a : HeckeAlgebra μ) = b) : a = b :=
  val_injective hKc hKo h
@[simp] theorem val_mul (a b : HeckeAlgebraLevel μ K hKc hKo) :
    ((a * b : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) = a * b := rfl
@[simp] theorem val_add (a b : HeckeAlgebraLevel μ K hKc hKo) :
    ((a + b : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) = a + b := rfl
@[simp] theorem val_zero : ((0 : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) = 0 := rfl
@[simp] theorem val_smul (c : ℂ) (a : HeckeAlgebraLevel μ K hKc hKo) :
    ((c • a : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) = c • (a : HeckeAlgebra μ) := rfl
@[simp] theorem val_neg (a : HeckeAlgebraLevel μ K hKc hKo) :
    ((-a : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) = -(a : HeckeAlgebra μ) := rfl
@[simp] theorem val_sub (a b : HeckeAlgebraLevel μ K hKc hKo) :
    ((a - b : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) = a - b := rfl
instance : Ring (HeckeAlgebraLevel μ K hKc hKo) :=
  { (inferInstance : NonUnitalRing (HeckeAlgebraLevel μ K hKc hKo)) with
    one := mk hKc hKo (idem μ hKc hKo) (idem_mem_biInvariant hKc hKo)
    one_mul := fun a => ext hKc hKo ((mem_biInvariant_iff_idem hKc hKo).1 (val_mem hKc hKo a)).1
    mul_one := fun a => ext hKc hKo ((mem_biInvariant_iff_idem hKc hKo).1 (val_mem hKc hKo a)).2 }
@[simp] theorem val_one : ((1 : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) = idem μ hKc hKo :=
  rfl
theorem apply_mul_left (h : HeckeAlgebraLevel μ K hKc hKo) {k : G} (hk : k ∈ K) (x : G) :
    (h : HeckeAlgebra μ) (k * x) = (h : HeckeAlgebra μ) x :=
  (val_mem hKc hKo h k hk x).1
def corner (f : HeckeAlgebra μ) : HeckeAlgebraLevel μ K hKc hKo :=
  mk hKc hKo (idem μ hKc hKo * f * idem μ hKc hKo)
    (by rw [← SetLike.mem_coe, biInvariant_eq_range hKc hKo]; exact ⟨f, rfl⟩)
@[simp] theorem val_corner (f : HeckeAlgebra μ) :
    ((corner hKc hKo f : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) =
      idem μ hKc hKo * f * idem μ hKc hKo := rfl
instance instModuleFixedVectors : Module (HeckeAlgebraLevel μ K hKc hKo) (fixedVectors ρ K) where
  smul h v := ⟨heckeAct μ ρ (h : HeckeAlgebra μ) v,
    heckeAct_mem_fixedVectors (h : HeckeAlgebra μ).mem (fun _ hk x => apply_mul_left hKc hKo h hk x)
      (smooth_of_mem_fixedVectors hKo v.2)⟩
  one_smul v := Subtype.ext (heckeAct_idem_of_mem hKc hKo v.2)
  mul_smul a b v := Subtype.ext (by
    change heckeAct μ ρ ((a * b : HeckeAlgebra μ) : G → ℂ) v = heckeAct μ ρ (a : HeckeAlgebra μ)
      (heckeAct μ ρ (b : HeckeAlgebra μ) v)
    rw [coe_mul]
    exact heckeAct_groupConv (a : HeckeAlgebra μ).mem (b : HeckeAlgebra μ).mem
      (smooth_of_mem_fixedVectors hKo v.2))
  smul_zero a := Subtype.ext (heckeAct_zero_right (a : HeckeAlgebra μ).mem)
  smul_add a v w := Subtype.ext (heckeAct_add_right (a : HeckeAlgebra μ).mem
    (smooth_of_mem_fixedVectors hKo v.2) (smooth_of_mem_fixedVectors hKo w.2))
  add_smul a b v := Subtype.ext (by
    change heckeAct μ ρ (((a + b : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) : G → ℂ) v = _
    rw [val_add, coe_add]
    exact heckeAct_add_left (a : HeckeAlgebra μ).mem (b : HeckeAlgebra μ).mem
      (smooth_of_mem_fixedVectors hKo v.2))
  zero_smul v := Subtype.ext (by
    change heckeAct μ ρ (((0 : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) : G → ℂ) v = 0
    rw [val_zero, coe_zero]
    exact heckeAct_zero_left (smooth_of_mem_fixedVectors hKo v.2))
end HeckeAlgebraLevel
def heckeRep (hρ : IsSmooth ρ) : HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ V where
  toFun f :=
    { toFun := heckeAct μ ρ f
      map_add' := fun v w => heckeAct_add_right f.mem (hρ v) (hρ w)
      map_smul' := fun c v => heckeAct_smul_right f.mem c (hρ v) }
  map_add' f g := LinearMap.ext fun v => heckeAct_add_left f.mem g.mem (hρ v)
  map_zero' := LinearMap.ext fun v => heckeAct_zero_left (hρ v)
  map_smul' c f := LinearMap.ext fun v => heckeAct_smul_left c f.mem (hρ v)
  map_mul' f g := LinearMap.ext fun v => heckeAct_groupConv f.mem g.mem (hρ v)
end HeckeAlgebra
end GroundTheory.Automorphic


