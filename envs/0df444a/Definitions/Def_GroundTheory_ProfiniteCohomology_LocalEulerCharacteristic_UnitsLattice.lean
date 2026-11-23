-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
-- name    : GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:55.003564+00:00
-- url     : https://prove2.me/theorems/23b37c63-7f4b-40fd-aa50-cd38353c5628
-- title:
--   Units Lattice
-- statement:
--   Definitions and structural lemmas for Units Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/UnitsLattice.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsPower
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Theorems.Thm_GroundTheory_LocalField_algEquiv_mem_normalLattice
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_coeff_injective
import Theorems.Thm_GroundTheory_LocalField_mem_integer_of_mem_normalLattice
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IsLocalRing
section Galois
variable (E F : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
noncomputable abbrev integerAction : MulSemiringAction (F ≃ₐ[E] F) 𝒪[F] where
  smul σ x := integerAlgEquiv E F σ x
  one_smul x := by ext; rfl
  mul_smul σ τ x := by ext; rfl
  smul_zero σ := map_zero (integerAlgEquiv E F σ)
  smul_add σ := map_add (integerAlgEquiv E F σ)
  smul_one σ := map_one (integerAlgEquiv E F σ)
  smul_mul σ := map_mul (integerAlgEquiv E F σ)
attribute [local instance] integerAction
variable {E F}
theorem coe_integer_smul (σ : F ≃ₐ[E] F) (x : 𝒪[F]) : ((σ • x : 𝒪[F]) : F) = σ (x : F) :=
  rfl
theorem coe_integerUnits_smul (σ : F ≃ₐ[E] F) (u : 𝒪[F]ˣ) :
    ((σ • u : 𝒪[F]ˣ) : 𝒪[F]) = σ • (u : 𝒪[F]) :=
  rfl
theorem smul_mem_maximalIdeal (σ : F ≃ₐ[E] F) {x : 𝒪[F]} (hx : x ∈ 𝓂[F]) : σ • x ∈ 𝓂[F] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro h
  apply hx
  have := h.map (MulSemiringAction.toRingHom (F ≃ₐ[E] F) 𝒪[F] σ⁻¹)
  simpa [MulSemiringAction.toRingHom_apply, smul_smul] using this
theorem smul_mem_maximalIdeal_pow (σ : F ≃ₐ[E] F) {k : ℕ} {x : 𝒪[F]} (hx : x ∈ 𝓂[F] ^ k) :
    σ • x ∈ 𝓂[F] ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hx
  rw [smul_mul', smul_pow']
  exact Ideal.mul_mem_right _ _
    (Ideal.pow_mem_pow (smul_mem_maximalIdeal σ (uniformizer_mem_maximalIdeal hϖ)) k)
theorem smul_mem_unitFiltration (σ : F ≃ₐ[E] F) {k : ℕ} {u : 𝒪[F]ˣ}
    (hu : u ∈ unitFiltration F k) : σ • u ∈ unitFiltration F k := by
  rw [mem_unitFiltration, coe_integerUnits_smul, ← smul_one σ, ← smul_sub]
  · exact smul_mem_maximalIdeal_pow σ hu
end Galois
section ModN
variable {G : Type*} [AddCommGroup G]
theorem mem_range_lsmul_iff {n : ℕ} {x : G} :
    x ∈ LinearMap.range (LinearMap.lsmul ℤ G n) ↔ ∃ y : G, n • y = x := by
  simp [LinearMap.mem_range, natCast_zsmul]
end ModN
section Filtration
variable (E F : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]
attribute [local instance] integerAction
noncomputable abbrev unitFiltrationAction (k : ℕ) :
    MulDistribMulAction (F ≃ₐ[E] F) (unitFiltration F k) where
  smul σ u := ⟨σ • (u : 𝒪[F]ˣ), smul_mem_unitFiltration σ u.2⟩
  one_smul u := Subtype.ext (one_smul _ (u : 𝒪[F]ˣ))
  mul_smul σ τ u := Subtype.ext (mul_smul σ τ (u : 𝒪[F]ˣ))
  smul_mul σ u v := Subtype.ext (smul_mul' σ (u : 𝒪[F]ˣ) v)
  smul_one σ := Subtype.ext (smul_one σ)
variable {F} in

noncomputable def maxPow (F : Type*) [Field F] [ValuativeRel F] (k : ℕ) : AddSubgroup 𝒪[F] :=
  (𝓂[F] ^ k).toAddSubgroup
noncomputable abbrev maxPowAction (k : ℕ) : DistribMulAction (F ≃ₐ[E] F) (maxPow F k) :=
  subgroupDistribMulAction (maxPow F k) fun σ _ hx ↦ smul_mem_maximalIdeal_pow σ hx
attribute [local instance] unitFiltrationAction maxPowAction
variable {E F}
variable {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {p : ℕ} {e : ℕ} {ε : 𝒪[F]ˣ}
  (hpe : (p : 𝒪[F]) = ϖ ^ e * ε)
include hϖ hpe
omit hϖ hpe in
theorem sub_one_mem_maxPow {k : ℕ} (u : unitFiltration F k) :
    ((u : 𝒪[F]ˣ) : 𝒪[F]) - 1 ∈ maxPow F k :=
  u.2
noncomputable def unitToModN {k : ℕ} (hk : e ≤ k) :
    Additive (unitFiltration F k) →+ ModN (maxPow F k) p where
  toFun u := Submodule.Quotient.mk ⟨((u.toMul : 𝒪[F]ˣ) : 𝒪[F]) - 1, sub_one_mem_maxPow u.toMul⟩
  map_zero' := by
    rw [Submodule.Quotient.mk_eq_zero]
    have h : (⟨_, sub_one_mem_maxPow (Additive.toMul (0 : Additive (unitFiltration F k)))⟩ :
        maxPow F k) = 0 := by
      ext; simp
    exact h ▸ Submodule.zero_mem _
  map_add' u v := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, mem_range_lsmul_iff]
    obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ u.toMul
    obtain ⟨b, hb⟩ := exists_sub_one_eq_mul hϖ v.toMul
    obtain ⟨m, rfl⟩ : ∃ m, k = e + m := ⟨k - e, by omega⟩
    have hy : ϖ ^ (e + m) * (ϖ ^ m * a * b * ((ε⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) ∈ 𝓂[F] ^ (e + m) := by
      rw [mem_maximalIdeal_pow_iff hϖ]
      exact dvd_mul_right _ _
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_sub, AddSubgroup.coe_add, toMul_add,
      Subgroup.coe_mul, Units.val_mul, nsmul_eq_mul]
    have h1 : ((u.toMul : 𝒪[F]ˣ) : 𝒪[F]) = 1 + ϖ ^ (e + m) * a := by
      rw [← ha]; ring
    have h2 : ((v.toMul : 𝒪[F]ˣ) : 𝒪[F]) = 1 + ϖ ^ (e + m) * b := by
      rw [← hb]; ring
    rw [h1, h2, hpe]
    have := ε.mul_inv
    linear_combination (ϖ ^ (e + m) * (ϖ ^ e * (ϖ ^ m * a * b))) * this
end Filtration
section Lattice
variable {E F : Type*} [Field E] [ValuativeRel E] [Field F] [ValuativeRel F] [Algebra E F]
  [FiniteDimensional E F]
variable (E) in

noncomputable def normalSub (θ : F) : AddSubgroup 𝒪[F] :=
  (normalLattice (1 : 𝒪[E]) θ 0).toAddSubgroup.comap (𝒪[F].subtype : 𝒪[F] →+* F).toAddMonoidHom
omit [FiniteDimensional E F] in
theorem mem_normalSub {θ : F} {x : 𝒪[F]} :
    x ∈ normalSub E θ ↔ (x : F) ∈ normalLattice (1 : 𝒪[E]) θ 0 :=
  Iff.rfl
omit [ValuativeRel F] in
theorem sum_smul_mem_normalLattice {θ : F} (c : (F ≃ₐ[E] F) → 𝒪[E]) :
    ∑ σ, c σ • σ θ ∈ normalLattice (1 : 𝒪[E]) θ 0 :=
  (mem_normalLattice_iff 1 θ).mpr ⟨c, by simp⟩
variable [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [ValuativeExtension E F]
attribute [local instance] integerAction
noncomputable abbrev normalSubAction (θ : F) : DistribMulAction (F ≃ₐ[E] F) (normalSub E θ) :=
  subgroupDistribMulAction (normalSub E θ) fun σ x hx ↦ by
    rw [mem_normalSub, coe_integer_smul]
    exact algEquiv_mem_normalLattice 1 θ σ hx
attribute [local instance] normalSubAction
variable {θ : F} (hθ : LinearIndependent E fun σ : F ≃ₐ[E] F ↦ σ θ)
  (hθO : ∀ σ : F ≃ₐ[E] F, σ θ ∈ 𝒪[F])
omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in
include hθO in
theorem sum_smul_mem_integer (c : (F ≃ₐ[E] F) → 𝒪[E]) : ∑ σ, c σ • σ θ ∈ 𝒪[F] :=
  mem_integer_of_mem_normalLattice 1 θ hθO (sum_smul_mem_normalLattice c)
noncomputable def normalSubOfCoeff : ((F ≃ₐ[E] F) → 𝒪[E]) →+ normalSub E θ where
  toFun c := ⟨⟨∑ σ, c σ • σ θ, sum_smul_mem_integer hθO c⟩, sum_smul_mem_normalLattice c⟩
  map_zero' := by ext; simp
  map_add' c d := by ext; simp [add_smul, Finset.sum_add_distrib]
omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in
theorem coe_normalSubOfCoeff (c : (F ≃ₐ[E] F) → 𝒪[E]) :
    ((normalSubOfCoeff hθO c : 𝒪[F]) : F) = ∑ σ, c σ • σ θ :=
  rfl
omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in
include hθ in
theorem normalSubOfCoeff_bijective : Function.Bijective (normalSubOfCoeff hθO) := by
  constructor
  · intro c d h
    have := congrArg (fun x : normalSub E θ ↦ ((x : 𝒪[F]) : F)) h
    exact coeff_injective θ hθ this
  · intro x
    obtain ⟨c, hc⟩ := (mem_normalLattice_iff 1 θ).mp (mem_normalSub.mp x.2)
    refine ⟨c, ?_⟩
    ext
    rw [coe_normalSubOfCoeff, ← hc]
    simp
noncomputable def normalSubEquiv : ((F ≃ₐ[E] F) → 𝒪[E]) ≃+ normalSub E θ :=
  AddEquiv.ofBijective (normalSubOfCoeff hθO) (normalSubOfCoeff_bijective hθ hθO)
end Lattice
section Regular
variable {Γ O : Type*} [Fintype Γ] [AddCommGroup O] {p n : ℕ}
  (b : Module.Basis (Fin n) (ZMod p) (ModN O p))
noncomputable def coeffToRegular : (Γ → O) →+ (Fin n → MonoidAlgebra (ZMod p) Γ) where
  toFun c i := ∑ σ, MonoidAlgebra.single σ (b.repr (Submodule.Quotient.mk (c σ)) i)
  map_zero' := by
    funext i
    simp
  map_add' c d := by
    funext i
    simp [Finset.sum_add_distrib, MonoidAlgebra.single_add]
end Regular
end GroundTheory.ProfCoh


