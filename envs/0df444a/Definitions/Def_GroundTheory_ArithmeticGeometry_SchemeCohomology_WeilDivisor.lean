-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:36:08.989723+00:00
-- url     : https://prove2.me/theorems/a8d5ac84-ab22-4df7-a65e-23975153b285
-- title:
--   Weil Divisor
-- statement:
--   Definitions and structural lemmas for Weil Divisor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/WeilDivisor.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology
universe u
class IsNormalScheme (X : Scheme.{u}) : Prop where
  isDomain_stalk : ∀ x : X, IsDomain (X.presheaf.stalk x)
  isIntegrallyClosed_stalk : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)
def PrimeDivisor (X : Scheme.{u}) : Type u :=
  {x : X // ringKrullDim (X.presheaf.stalk x) = 1}
abbrev WeilDivisor (X : Scheme.{u}) : Type u := PrimeDivisor X →₀ ℤ
variable {X : Scheme.{u}}
namespace PrimeDivisor
def point (x : PrimeDivisor X) : X := x.1
lemma ringKrullDim_stalk (x : PrimeDivisor X) :
    ringKrullDim (X.presheaf.stalk x.point) = 1 := x.2
lemma coheight_point (x : PrimeDivisor X) : Order.coheight x.point = 1 := by
  have h := x.ringKrullDim_stalk
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h
lemma point_injective : Function.Injective (point (X := X)) := fun _ _ h => Subtype.ext h
lemma maximalIdeal_ne_bot (x : PrimeDivisor X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x.point) ≠ ⊥ := by
  intro h
  have hf : IsField (X.presheaf.stalk x.point) :=
    (IsLocalRing.isField_iff_maximalIdeal_eq).mpr h
  have := x.ringKrullDim_stalk
  rw [ringKrullDim_eq_zero_of_isField hf] at this
  exact zero_ne_one this
variable [IsIntegral X]
lemma dimensionLEOne_stalk (x : PrimeDivisor X) :
    Ring.DimensionLEOne (X.presheaf.stalk x.point) := by
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk x.point) := by
    rw [Ring.krullDimLE_iff, x.ringKrullDim_stalk]
    norm_num
  refine ⟨fun {p} hp hprime => ?_⟩
  rcases Ring.krullDimLE_one_iff.mp hle p hprime with h | h
  · rw [IsDomain.minimalPrimes_eq_singleton_bot] at h
    exact absurd h hp
  · exact h
variable [IsLocallyNoetherian X] [IsNormalScheme X]
lemma isDedekindDomain_stalk (x : PrimeDivisor X) :
    IsDedekindDomain (X.presheaf.stalk x.point) := by
  have := x.dimensionLEOne_stalk
  have := IsNormalScheme.isIntegrallyClosed_stalk (X := X) x.point
  exact (isDedekindDomain_iff _ (FractionRing (X.presheaf.stalk x.point))).mpr
    ⟨inferInstance, inferInstance, inferInstance,
      fun {y} hy => IsIntegrallyClosed.isIntegral_iff.mp hy⟩
noncomputable def heightOneSpectrum (x : PrimeDivisor X) :
    HeightOneSpectrum (X.presheaf.stalk x.point) :=
  ⟨IsLocalRing.maximalIdeal _, (IsLocalRing.maximalIdeal.isMaximal _).isPrime,
    x.maximalIdeal_ne_bot⟩
noncomputable def valuation (x : PrimeDivisor X) : Valuation X.functionField (WithZero (Multiplicative ℤ)) :=
  @HeightOneSpectrum.valuation _ _ x.isDedekindDomain_stalk _ _ _ _ x.heightOneSpectrum
noncomputable def ord (x : PrimeDivisor X) (f : X.functionField) : ℤ :=
  - WithZero.log (x.valuation f)
lemma ord_mul (x : PrimeDivisor X) {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    x.ord (f * g) = x.ord f + x.ord g := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf) ((Valuation.ne_zero_iff _).mpr hg)]
  ring
lemma ord_one (x : PrimeDivisor X) : x.ord 1 = 0 := by
  simp [ord]
end PrimeDivisor
namespace PrimeDivisor
variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
lemma ord_algebraMap_of_isUnit (x : PrimeDivisor X) {a : X.presheaf.stalk x.point}
    (ha : IsUnit a) : x.ord (algebraMap _ X.functionField a) = 0 := by
  have := x.isDedekindDomain_stalk
  have h1 : x.valuation (algebraMap _ X.functionField a) = 1 := by
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun hm => (IsLocalRing.mem_maximalIdeal a).mp hm ha
  simp [ord, h1]
lemma ord_germToFunctionField_of_isUnit (x : PrimeDivisor X) {U : X.Opens} [Nonempty U]
    (hx : x.point ∈ U) {g : Γ(X, U)} (hg : IsUnit g) :
    x.ord (X.germToFunctionField U g) = 0 := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
  exact x.ord_algebraMap_of_isUnit (hg.map _)
end PrimeDivisor
lemma PrimeDivisor.eq_genericPoint_of_mem [IsIntegral X] (x : PrimeDivisor X) {T : Set X}
    (hT : IsIrreducible T) (hTc : IsClosed T) (hgen : genericPoint X ∉ T) (hx : x.point ∈ T) :
    x.point = hT.genericPoint := by
  set c := hT.genericPoint
  have hc : IsGenericPoint c T := by
    have := hT.isGenericPoint_genericPoint_closure
    rwa [hTc.closure_eq] at this
  have hcx : c ⤳ x.point := hc.specializes hx
  have hcT : c ∈ T := hc.mem
  have hηc : genericPoint X ⤳ c := (genericPoint_spec X).specializes (Set.mem_univ _)
  have hηne : genericPoint X ≠ c := fun h => hgen (h ▸ hcT)
  have hlt1 : c < genericPoint X := by
    refine ⟨hηc, fun h => hηne (h.antisymm hηc).eq.symm⟩
  by_contra hne
  have hlt2 : x.point < c := ⟨hcx, fun h => hne (hcx.antisymm h).eq.symm⟩
  have h1 := Order.coheight_add_one_le hlt1
  have h2 := Order.coheight_add_one_le hlt2
  rw [x.coheight_point] at h2
  have h4 : (1 : ℕ∞) ≤ Order.coheight c := le_trans le_add_self h1
  have h5 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add_left h4 1) h2
  norm_num at h5
section Finite
variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]
theorem PrimeDivisor.finite_ord_ne_zero {f : X.functionField} (hf : f ≠ 0) :
    {x : PrimeDivisor X | x.ord f ≠ 0}.Finite := by
  obtain ⟨U, -, g, hne, hgf, hgu⟩ := exists_isUnit_germ_eq X f hf
  set Z : Set X := (U : Set X)ᶜ with hZ
  have hZc : IsClosed Z := U.isOpen.isClosed_compl
  have hgenU : genericPoint X ∈ U := by
    obtain ⟨⟨y, hy⟩⟩ := hne
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hsub : {x : PrimeDivisor X | x.ord f ≠ 0} ⊆ {x | x.point ∈ Z} := by
    intro x hx
    by_contra hxU
    simp only [Set.mem_ofPred_eq, hZ, Set.mem_compl_iff, not_not] at hxU
    exact hx (hgf ▸ x.ord_germToFunctionField_of_isUnit hxU hgu)
  refine Set.Finite.subset ?_ hsub
  have key : ∀ (x : PrimeDivisor X) (hx : x.point ∈ Z) (C : Set Z),
      C ∈ irreducibleComponents Z → (⟨x.point, hx⟩ : Z) ∈ C →
      ∃ hT : IsIrreducible (closure (Subtype.val '' C)), x.point = hT.genericPoint := by
    intro x hx C hC hxC
    have hT : IsIrreducible (closure (Subtype.val '' C)) :=
      (hC.1.image _ continuous_subtype_val.continuousOn).closure
    refine ⟨hT, x.eq_genericPoint_of_mem hT isClosed_closure ?_ ?_⟩
    · intro hg
      have : closure (Subtype.val '' C) ⊆ Z :=
        closure_minimal (Subtype.coe_image_subset _ _) hZc
      exact this hg hgenU
    · exact subset_closure ⟨_, hxC, rfl⟩
  have hcomp : ∀ x : {x : PrimeDivisor X | x.point ∈ Z}, ∃ C ∈ irreducibleComponents Z,
      {(⟨x.1.point, x.2⟩ : Z)} ⊆ C := fun x =>
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ isIrreducible_singleton
  let φ : {x : PrimeDivisor X | x.point ∈ Z} → irreducibleComponents Z := fun x =>
    ⟨(hcomp x).choose, (hcomp x).choose_spec.1⟩
  have : Finite (irreducibleComponents Z) :=
    (NoetherianSpace.finite_irreducibleComponents (α := Z)).to_subtype
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hx := (hcomp x).choose_spec
    have hy := (hcomp y).choose_spec
    have hC : (hcomp x).choose = (hcomp y).choose := congrArg Subtype.val hxy
    obtain ⟨hT, hxT⟩ := key x.1 x.2 _ hx.1 (hx.2 rfl)
    obtain ⟨hT', hyT⟩ := key y.1 y.2 _ hy.1 (hy.2 rfl)
    apply Subtype.ext
    apply PrimeDivisor.point_injective
    rw [hxT, hyT]
    simp only [hC]
  have : Finite {x : PrimeDivisor X | x.point ∈ Z} := Finite.of_injective φ hφ
  exact Set.toFinite _
end Finite
section Divisor
variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]
noncomputable def divisorOf (f : (X.functionField)ˣ) : WeilDivisor X :=
  Finsupp.ofSupportFinite (fun x => x.ord (f : X.functionField))
    (PrimeDivisor.finite_ord_ne_zero f.ne_zero)
lemma divisorOf_apply (f : (X.functionField)ˣ) (x : PrimeDivisor X) :
    divisorOf f x = x.ord (f : X.functionField) := rfl
noncomputable def principalDivisor : Additive (X.functionField)ˣ →+ WeilDivisor X where
  toFun f := divisorOf f.toMul
  map_zero' := by
    ext x
    simp [divisorOf_apply, PrimeDivisor.ord_one]
  map_add' f g := by
    ext x
    simp only [divisorOf_apply, toMul_add, Units.val_mul, Finsupp.coe_add, Pi.add_apply]
    exact x.ord_mul f.toMul.ne_zero g.toMul.ne_zero
variable (X) in

noncomputable def principalDivisors : AddSubgroup (WeilDivisor X) :=
  (principalDivisor (X := X)).range
variable (X) in

abbrev ClassGroup : Type u := WeilDivisor X ⧸ principalDivisors X
end Divisor
end GroundTheory.Arith.SchemeCoh


