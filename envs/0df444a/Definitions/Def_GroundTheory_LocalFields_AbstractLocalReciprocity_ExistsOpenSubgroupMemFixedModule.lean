-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:37.657087+00:00
-- url     : https://prove2.me/theorems/3977cc53-bc02-41d0-b57f-c2f3156f2305
-- title:
--   Exists Open Subgroup Mem Fixed Module
-- statement:
--   Definitions and structural lemmas for Exists Open Subgroup Mem Fixed Module, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsOpenSubgroupMemFixedModule.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
section FixedModule
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
def fixedModule (H : Subgroup G) : Subgroup A where
  carrier := {a | ∀ g ∈ H, g • a = a}
  mul_mem' {a b} ha hb g hg := by rw [smul_mul', ha g hg, hb g hg]
  one_mem' g _ := smul_one g
  inv_mem' {a} ha g hg := by rw [smul_inv', ha g hg]
variable {A}
end FixedModule
section Discrete
class IsDiscreteModule (G : Type*) [Group G] [TopologicalSpace G] (A : Type*) [CommGroup A]
    [MulDistribMulAction G A] : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (MulAction.stabilizer G a : Set G)
variable {G : Type*} [Group G] [TopologicalSpace G] {A : Type*} [CommGroup A]
  [MulDistribMulAction G A]
end Discrete
section Norm
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable (K L : Subgroup G)
def cosetSMul (a : fixedModule A L) : K ⧸ L.subgroupOf K → A :=
  Quotient.lift (fun σ : K => (σ : G) • (a : A)) fun σ τ hστ => by
    have h : σ⁻¹ * τ ∈ L.subgroupOf K := QuotientGroup.leftRel_apply.mp hστ
    rw [Subgroup.mem_subgroupOf] at h
    have ha := a.2 _ h
    calc (σ : G) • (a : A) = (σ : G) • ((((σ⁻¹ * τ : K)) : G) • (a : A)) := by rw [ha]
      _ = (τ : G) • (a : A) := by rw [smul_smul]; simp
variable {A K L}
@[simp] theorem cosetSMul_mk (a : fixedModule A L) (σ : K) :
    cosetSMul A K L a (σ : K ⧸ L.subgroupOf K) = (σ : G) • (a : A) :=
  rfl
theorem cosetSMul_one (q : K ⧸ L.subgroupOf K) : cosetSMul A K L 1 q = 1 := by
  induction q using QuotientGroup.induction_on with
  | H σ => simp
theorem cosetSMul_mul (a b : fixedModule A L) (q : K ⧸ L.subgroupOf K) :
    cosetSMul A K L (a * b) q = cosetSMul A K L a q * cosetSMul A K L b q := by
  induction q using QuotientGroup.induction_on with
  | H σ => simp [smul_mul']
theorem smul_cosetSMul (a : fixedModule A L) (g : K) (q : K ⧸ L.subgroupOf K) :
    (g : G) • cosetSMul A K L a q = cosetSMul A K L a (g • q) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    rw [cosetSMul_mk, smul_smul]
    rfl
variable (A K L)
noncomputable def normFun (a : fixedModule A L) : A :=
  ∏ᶠ q, cosetSMul A K L a q
variable [(L.subgroupOf K).FiniteIndex]
theorem normFun_mem_fixedModule (a : fixedModule A L) : normFun A K L a ∈ fixedModule A K := by
  intro g hg
  unfold normFun
  rw [smul_finprod']
  simp_rw [smul_cosetSMul a ⟨g, hg⟩]
  exact finprod_comp_equiv (MulAction.toPerm (⟨g, hg⟩ : K))
noncomputable def norm : fixedModule A L →* fixedModule A K where
  toFun a := ⟨normFun A K L a, normFun_mem_fixedModule A K L a⟩
  map_one' := by
    ext
    simp [normFun, cosetSMul_one]
  map_mul' a b := by
    classical
    let _ := Fintype.ofFinite (K ⧸ L.subgroupOf K)
    ext
    simp only [normFun, Subgroup.coe_mul, finprod_eq_prod_of_fintype, cosetSMul_mul,
      Finset.prod_mul_distrib]
variable {A K L}
variable (A K L)
def augmentation : Subgroup A :=
  Subgroup.closure {x | ∃ g ∈ K, ∃ a ∈ fixedModule A L, x = g • a / a}
abbrev tateZero : Type _ :=
  fixedModule A K ⧸ (norm A K L).range
abbrev tateNegOne : Type _ :=
  (norm A K L).ker ⧸
    (augmentation A K L).comap ((fixedModule A L).subtype.comp (norm A K L).ker.subtype)
variable {A K L}
end Norm
section Data
instance finiteIndex_openSubgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : OpenSubgroup G) : (U : Subgroup G).FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient
variable {G : Type*} [Group G]
noncomputable def inertiaDegree (d : G →* Multiplicative ℤ̂) (K : Subgroup G) : ℕ :=
  (K.map d).index
noncomputable def ramificationIndex (d : G →* Multiplicative ℤ̂) (K : Subgroup G) : ℕ :=
  K.relIndex d.ker
variable (G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (A : Type*) [CommGroup A] [MulDistribMulAction G A]
structure ClassFieldData where

  deg : G →* Multiplicative ℤ̂
  continuous_deg : Continuous deg
  surjective_deg : Function.Surjective deg

  val : fixedModule A (⊤ : Subgroup G) →* Multiplicative ℤ̂

  intCast_mem_range_val : ∀ n : ℤ, Multiplicative.ofAdd (n : ℤ̂) ∈ val.range

  exists_eq_intCast_add_nsmul : ∀ n : ℕ, 0 < n → ∀ a : fixedModule A (⊤ : Subgroup G),
    ∃ (m : ℤ) (b : fixedModule A (⊤ : Subgroup G)),
      Multiplicative.toAdd (val a) = (m : ℤ̂) + n • Multiplicative.toAdd (val b)

  range_val_comp_norm : ∀ K : OpenSubgroup G,
    (val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range =
      val.range.map (powMonoidHom (inertiaDegree deg (K : Subgroup G)))
def ClassFieldAxiom : Prop :=
  ∀ K L : OpenSubgroup G, L ≤ K → ∀ [((L : Subgroup G).subgroupOf K).Normal],
    IsCyclic (K ⧸ (L : Subgroup G).subgroupOf K) →
      Nat.card (tateZero A (K : Subgroup G) (L : Subgroup G)) = (L : Subgroup G).relIndex K ∧
        Nat.card (tateNegOne A (K : Subgroup G) (L : Subgroup G)) = 1
structure ClassFieldTheory extends ClassFieldData G A where
  isDiscreteModule : IsDiscreteModule G A
  classFieldAxiom : ClassFieldAxiom G A
end Data
end GroundTheory.LocalField.Abstract


