-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.ffEquiv_symm_stalkMap_eq_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f7d4b038-9417-579c-b31a-05c35338ecd0

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap

set_option autoImplicit false

namespace HG1bRigidity

set_option linter.unusedSectionVars false

open IsLocalRing AlgebraicCurve

section FieldSide

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

theorem ord_nonneg_of_mem (v : Place K L) {f : L} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hϖ
  have hcoe : f = ((u : v.toValuationSubring) : L) * ((ϖ : L) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hϖ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_of_ord_nonneg (v : Place K L) {f : L} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hϖ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (ϖ : v.toValuationSubring).2 _)

theorem ord_coe_eq_zero_iff_isUnit (v : Place K L) (a : v.toValuationSubring) (ha : (a : L) ≠ 0) :
    v.ord (a : L) = 0 ↔ IsUnit a := by
  rw [← v.adicValuation_coe_eq_one_iff]
  have hne := v.adicValuation_ne_zero ha
  show -(WithZero.log (v.adicValuation (a : L))) = 0 ↔ _
  constructor
  · intro h
    have h' : WithZero.log (v.adicValuation (a : L)) = 0 := by omega
    rw [← WithZero.exp_log hne, h', WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one, neg_zero]

theorem mem_maximalIdeal_iff_ord_pos (v : Place K L) (a : v.toValuationSubring) (ha : (a : L) ≠ 0) :
    a ∈ maximalIdeal v.toValuationSubring ↔ 0 < v.ord (a : L) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← ord_coe_eq_zero_iff_isUnit v a ha]
  have := ord_nonneg_of_mem v a.2
  omega

def VanishesAt (w : Place K L) (z : L) : Prop :=
  ∃ h : z ∈ w.toValuationSubring, (⟨z, h⟩ : w.toValuationSubring) ∈ maximalIdeal w.toValuationSubring

theorem VanishesAt.sub {w : Place K L} {a b : L} (ha : VanishesAt w a) (hb : VanishesAt w b) :
    VanishesAt w (a - b) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  exact ⟨sub_mem ha1 hb1, sub_mem ha2 hb2⟩

theorem vanishesAt_zero (w : Place K L) : VanishesAt w (0 : L) :=
  ⟨zero_mem _, by
    have h0 : (⟨(0 : L), zero_mem _⟩ : w.toValuationSubring) = 0 := rfl
    rw [h0]
    exact zero_mem _⟩

theorem vanishesAt_of_mem_maximalIdeal {w : Place K L} {a : w.toValuationSubring}
    (ha : a ∈ maximalIdeal w.toValuationSubring) : VanishesAt w (a : L) :=
  ⟨a.2, by simpa using ha⟩

theorem vanishesAt_of_ord_pos {w : Place K L} {z : L} (hz : 0 < w.ord z) : VanishesAt w z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact vanishesAt_zero w
  · have hmem := mem_of_ord_nonneg w hz0 hz.le
    exact ⟨hmem, (mem_maximalIdeal_iff_ord_pos w ⟨z, hmem⟩ hz0).2 hz⟩

theorem VanishesAt.eq_zero_or_ord_pos {w : Place K L} {z : L} (h : VanishesAt w z) :
    z = 0 ∨ 0 < w.ord z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact Or.inl rfl
  · obtain ⟨h1, h2⟩ := h
    exact Or.inr ((mem_maximalIdeal_iff_ord_pos w ⟨z, h1⟩ hz0).1 h2)

theorem finite_setOf_ord_ne_zero [HasPrincipalDivisors K L] {g : L} (hg : g ≠ 0) :
    {w : Place K L | w.ord g ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  refine Set.Finite.subset D.support.finite_toSet fun w hw => ?_
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, hD w]
  exact hw

theorem exists_sub_algebraMap_mem_maximalIdeal [IsAlgClosed K] (v : Place K L)
    [Module.Finite K v.ResidueField] (a : v.toValuationSubring) :
    ∃ c : K, a - algebraMap K v.toValuationSubring c ∈ maximalIdeal v.toValuationSubring := by
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨c, hc⟩ := hbij.2 (residue v.toValuationSubring a)
  refine ⟨c, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc]
  exact IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c

theorem exists_ord_pos_of_ord_neg [IsAlgClosed K] [IsCurveOver K L] {g : L} (hg : g ≠ 0)
    {w₀ : Place K L} (hneg : w₀.ord g < 0) : ∃ w : Place K L, 0 < w.ord g := by
  classical
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg
  by_contra hcon
  push_neg at hcon
  have hdeg1 : ∀ w : Place K L, w.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have hw0 : w₀ ∈ D.support := by
    rw [Finsupp.mem_support_iff, hD]
    omega
  have hlt : Divisor.degree D < 0 := by
    have hsum : Divisor.degree D = D.sum (fun v n => n * (v.deg : ℤ)) := by
      simp only [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.coe_mulRight]
    rw [hsum]
    simp only [hdeg1, Nat.cast_one, mul_one]
    rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hw0]
    have h1 : D w₀ < 0 := by rw [hD]; exact hneg
    have h2 : ∑ v ∈ D.support.erase w₀, D v ≤ 0 :=
      Finset.sum_nonpos fun v _ => by rw [hD]; exact hcon v
    omega
  omega

theorem infinite_place [IsAlgClosed K] [IsCurveOver K L] (w₀ : Place K L) : Infinite (Place K L) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible w₀.toValuationSubring
  set t : L := ((ϖ : L))⁻¹ with ht_def
  have ht : w₀.ord t = -1 := by rw [ht_def, Place.ord_inv, w₀.ord_coe_irreducible hϖ]
  have ht_not_mem : t ∉ w₀.toValuationSubring := fun h => by
    have := ord_nonneg_of_mem w₀ h
    omega
  have hne : ∀ c : K, t - algebraMap K L c ≠ 0 := fun c h0 =>
    ht_not_mem (by rw [sub_eq_zero.mp h0]; exact w₀.algebraMap_mem' c)
  have hneg : ∀ c : K, w₀.ord (t - algebraMap K L c) < 0 := by
    intro c
    by_contra h
    push_neg at h
    have hmem : t - algebraMap K L c ∈ w₀.toValuationSubring := mem_of_ord_nonneg w₀ (hne c) h
    exact ht_not_mem (by simpa using add_mem hmem (w₀.algebraMap_mem' c))
  choose wc hwc using fun c => exists_ord_pos_of_ord_neg (hne c) (hneg c)
  haveI : Infinite K := inferInstance
  refine Infinite.of_injective wc fun c c' h => ?_
  by_contra hcc
  have h1 : 0 < (wc c).ord (t - algebraMap K L c) := hwc c
  have h2 : 0 < (wc c).ord (t - algebraMap K L c') := by rw [h]; exact hwc c'
  have hd := (vanishesAt_of_ord_pos h2).sub (vanishesAt_of_ord_pos h1)
  have hval : t - algebraMap K L c' - (t - algebraMap K L c) = algebraMap K L (c - c') := by
    rw [map_sub]; ring
  rw [hval] at hd
  rcases hd.eq_zero_or_ord_pos with h0 | hpos
  · exact hcc (sub_eq_zero.mp ((map_eq_zero _).mp h0)).symm.symm
  ·
    have hu : IsUnit (algebraMap K (wc c).toValuationSubring (c - c')) :=
      (IsUnit.mk0 _ (sub_ne_zero.2 (fun e => hcc e))).map _
    have hz : ((algebraMap K (wc c).toValuationSubring (c - c') : (wc c).toValuationSubring) : L) ≠ 0 := by
      rw [Place.coe_algebraMap]; exact (map_ne_zero _).2 (sub_ne_zero.2 fun e => hcc e)
    have := (ord_coe_eq_zero_iff_isUnit (wc c) _ hz).2 hu
    rw [Place.coe_algebraMap] at this
    omega

theorem eq_zero_of_vanishesAt_off_finite [IsAlgClosed K] [IsCurveOver K L] [Nonempty (Place K L)]
    {g : L} (S : Set (Place K L)) (hS : S.Finite) (h : ∀ w, w ∉ S → VanishesAt w g) : g = 0 := by
  by_contra hg
  haveI := infinite_place (K := K) (Classical.arbitrary (Place K L))
  have hT := finite_setOf_ord_ne_zero (K := K) hg
  have hsub : (Set.univ : Set (Place K L)) ⊆ S ∪ {w | w.ord g ≠ 0} := fun w _ => by
    by_cases hw : w ∈ S
    · exact Or.inl hw
    · rcases (h w hw).eq_zero_or_ord_pos with h0 | hpos
      · exact absurd h0 hg
      · exact Or.inr hpos.ne'
  exact Set.infinite_univ ((hS.union hT).subset hsub)

theorem mem_maximalIdeal_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (x : R) :
    x ∈ maximalIdeal R ↔ e x ∈ maximalIdeal S := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hx hu; exact hx (by simpa using hu.map e.symm)
  · intro hx hu; exact hx (hu.map e)

end FieldSide

section ModelSide

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

noncomputable def stalkToField (M : CurveModel K L) (z : M.C) : M.C.presheaf.stalk z →+* L :=
  (M.ffEquiv.symm : M.C.functionField ≃+* L).toRingHom.comp
    (algebraMap (M.C.presheaf.stalk z) M.C.functionField)

theorem stalkToField_apply (M : CurveModel K L) (z : M.C) (s : M.C.presheaf.stalk z) :
    stalkToField M z s = M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk z) M.C.functionField s) := rfl

theorem stalkToField_injective (M : CurveModel K L) (z : M.C) : Function.Injective (stalkToField M z) :=
  M.ffEquiv.symm.injective.comp (FaithfulSMul.algebraMap_injective _ _)

noncomputable def stalkEquivOfRange (M : CurveModel K L) (z : M.C) (P : Place K L)
    (hr : (stalkToField M z).range = P.toValuationSubring.toSubring) :
    M.C.presheaf.stalk z ≃+* P.toValuationSubring :=
  RingEquiv.ofBijective
    ((stalkToField M z).codRestrict P.toValuationSubring fun s => by
      have : stalkToField M z s ∈ (stalkToField M z).range := ⟨s, rfl⟩
      rw [hr] at this
      exact this)
    ⟨fun a b h => stalkToField_injective M z (congrArg Subtype.val h), fun t => by
      have ht : (t : L) ∈ (stalkToField M z).range := by rw [hr]; exact t.2
      obtain ⟨s, hs⟩ := ht
      exact ⟨s, Subtype.ext hs⟩⟩

@[scoped simp] theorem coe_stalkEquivOfRange (M : CurveModel K L) (z : M.C) (P : Place K L)
    (hr : (stalkToField M z).range = P.toValuationSubring.toSubring) (s : M.C.presheaf.stalk z) :
    ((stalkEquivOfRange M z P hr s : P.toValuationSubring) : L) = stalkToField M z s := rfl

theorem nonempty_place [IsAlgClosed K] (M : CurveModel K L) : Nonempty (Place K L) := by
  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  have hne : (closedPoints M.C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hJ := JacobsonSpace.closure_inter_closedPoints (X := M.C) (Z := Set.univ) isClosed_univ
    rw [h, Set.inter_empty, closure_empty] at hJ
    exact Set.empty_ne_univ hJ
  obtain ⟨z, hz⟩ := hne
  exact ⟨M.placeOfPoint ⟨z, hz⟩⟩

end ModelSide

section Rigidity

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F']
  [Algebra k F] [Algebra k F']
  [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
  [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
  (M : CurveModel k F) (M' : CurveModel k F')
  (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
  (φ : M.C.functionField →+* M'.C.functionField)
  (hφk : ∀ a : k, φ (baseToFunctionField M.toBase a) = baseToFunctionField M'.toBase a)
  (hφnat : ∀ (p : M'.C) (s : M.C.presheaf.stalk (π.base p)),
    algebraMap _ M'.C.functionField (π.stalkMap p s) = φ (algebraMap _ M.C.functionField s))

noncomputable def psi : F →+* F' :=
  ((M'.ffEquiv.symm : M'.C.functionField ≃+* F').toRingHom.comp φ).comp
    (M.ffEquiv : F ≃+* M.C.functionField).toRingHom

theorem psi_apply (f : F) : psi M M' φ f = M'.ffEquiv.symm (φ (M.ffEquiv f)) := rfl

include hφk in

theorem psi_algebraMap (c : k) : psi M M' φ (algebraMap k F c) = algebraMap k F' c := by
  rw [psi_apply, M.ffEquiv_algebraMap, hφk, ← M'.ffEquiv_algebraMap, RingEquiv.symm_apply_apply]

include hφnat in

theorem stalkToField_stalkMap (p : M'.C) (s : M.C.presheaf.stalk (π.base p)) :
    stalkToField M' p (π.stalkMap p s) = psi M M' φ (stalkToField M (π.base p) s) := by
  rw [stalkToField_apply, hφnat, psi_apply, stalkToField_apply, RingEquiv.apply_symm_apply]

include hπ hφk hφnat in

theorem vanishesAt_psi_sub
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
    (s : M.C.presheaf.stalk (π.base (pointEquivClosedPoint M'.toBase y).1)) :
    VanishesAt (M'.pointEquivPlace y)
      (psi M M' φ (stalkToField M _ s) - algebraMap F F' (stalkToField M _ s)) := by

  set w : Place k F' := M'.pointEquivPlace y with hw
  let x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    ⟨y.1 ≫ π, by rw [Category.assoc, hπ]; exact y.2⟩
  have hxpt : ((pointEquivClosedPoint M.toBase x) : M.C) = π.base (pointEquivClosedPoint M'.toBase y).1 := by
    rw [pointEquivClosedPoint_apply_coe, pointEquivClosedPoint_apply_coe]
    rfl
  have hclosed : IsClosed ({π.base (pointEquivClosedPoint M'.toBase y).1} : Set M.C) := hxpt ▸ (pointEquivClosedPoint M.toBase x).2
  have hv : w.restrict F = M.placeOfPoint ⟨π.base (pointEquivClosedPoint M'.toBase y).1, hclosed⟩ := by
    rw [hplace y x rfl, CurveModel.pointEquivPlace_apply]
    congr 1
  have hry : (stalkToField M' (pointEquivClosedPoint M'.toBase y).1).range = w.toValuationSubring.toSubring := M'.range_stalk_eq (pointEquivClosedPoint M'.toBase y)
  have hrx : (stalkToField M (π.base (pointEquivClosedPoint M'.toBase y).1)).range = (w.restrict F).toValuationSubring.toSubring := by
    rw [hv]; exact M.range_stalk_eq ⟨π.base (pointEquivClosedPoint M'.toBase y).1, hclosed⟩
  let θy := stalkEquivOfRange M' (pointEquivClosedPoint M'.toBase y).1 w hry
  let θx := stalkEquivOfRange M (π.base (pointEquivClosedPoint M'.toBase y).1) (w.restrict F) hrx

  haveI : Module.Finite k (w.restrict F).ResidueField := IsCurveOver.finiteResidue _
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_maximalIdeal (w.restrict F) (θx s)
  set sc := θx.symm (algebraMap k (w.restrict F).toValuationSubring c) with hsc

  have h1 : s - sc ∈ maximalIdeal (M.C.presheaf.stalk (π.base (pointEquivClosedPoint M'.toBase y).1)) := by
    rw [mem_maximalIdeal_iff_of_ringEquiv θx, map_sub, hsc, θx.apply_symm_apply]
    exact hc

  have h2 : π.stalkMap (pointEquivClosedPoint M'.toBase y).1 (s - sc) ∈ maximalIdeal (M'.C.presheaf.stalk (pointEquivClosedPoint M'.toBase y).1) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun hu => h1 ((isUnit_map_iff (π.stalkMap (pointEquivClosedPoint M'.toBase y).1).hom (s - sc)).1 hu)
  have h3 : θy (π.stalkMap (pointEquivClosedPoint M'.toBase y).1 (s - sc)) ∈ maximalIdeal w.toValuationSubring :=
    (mem_maximalIdeal_iff_of_ringEquiv θy _).1 h2

  have hE1 : VanishesAt w (psi M M' φ (stalkToField M _ s) - algebraMap k F' c) := by
    have hv3 := vanishesAt_of_mem_maximalIdeal h3
    have hcoe : ((θy (π.stalkMap (pointEquivClosedPoint M'.toBase y).1 (s - sc)) : w.toValuationSubring) : F')
        = psi M M' φ (stalkToField M _ s) - algebraMap k F' c := by
      rw [coe_stalkEquivOfRange, stalkToField_stalkMap M M' π φ hφnat, map_sub, map_sub,
        ← psi_algebraMap M M' φ hφk c]
      congr 2

      have : ((θx sc : (w.restrict F).toValuationSubring) : F) = algebraMap k F c := by
        rw [hsc, θx.apply_symm_apply, Place.coe_algebraMap]
      rwa [coe_stalkEquivOfRange] at this
    rwa [hcoe] at hv3

  have hE2 : VanishesAt w (algebraMap F F' (stalkToField M _ s) - algebraMap k F' c) := by
    have hd : ((θx s - algebraMap k (w.restrict F).toValuationSubring c :
        (w.restrict F).toValuationSubring) : F) = stalkToField M _ s - algebraMap k F c := by
      push_cast
      rw [coe_stalkEquivOfRange, Place.coe_algebraMap]
    have heq : algebraMap F F' (stalkToField M _ s) - algebraMap k F' c
        = algebraMap F F' (stalkToField M _ s - algebraMap k F c) := by
      rw [map_sub, ← IsScalarTower.algebraMap_apply]
    rw [heq, ← hd]
    set d := θx s - algebraMap k (w.restrict F).toValuationSubring c with hd_def
    rcases eq_or_ne (d : F) 0 with hd0 | hd0
    · rw [hd0, map_zero]; exact vanishesAt_zero w
    · have hposv : 0 < (w.restrict F).ord (d : F) := (mem_maximalIdeal_iff_ord_pos _ d hd0).1 hc
      apply vanishesAt_of_ord_pos
      rw [Place.ord_restrict]
      exact mul_pos (by exact_mod_cast w.ramificationIndex_pos (F := F)) hposv

  have hg : psi M M' φ (stalkToField M _ s) - algebraMap F F' (stalkToField M _ s)
      = (psi M M' φ (stalkToField M _ s) - algebraMap k F' c)
        - (algebraMap F F' (stalkToField M _ s) - algebraMap k F' c) := by ring
  rw [hg]
  exact hE1.sub hE2

include hπ hφk hφnat in

theorem key
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (f : F) : M'.ffEquiv.symm (φ (M.ffEquiv f)) = algebraMap F F' f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  haveI : Nonempty (Place k F') := nonempty_place M'
  rw [← psi_apply, ← sub_eq_zero]

  have hT : {v : Place k F | v.ord f ≠ 0}.Finite := finite_setOf_ord_ne_zero (K := k) hf0
  let S : Set (Place k F') := ⋃ v ∈ {v : Place k F | v.ord f ≠ 0}, {w | w.restrict F = v}
  have hS : S.Finite := hT.biUnion fun v _ => Place.restrict_fiber_finite (K := k) (F := F) v
  refine eq_zero_of_vanishesAt_off_finite (K := k) S hS fun w hw => ?_

  have hordv : (w.restrict F).ord f = 0 := by
    by_contra h
    exact hw (Set.mem_biUnion (show w.restrict F ∈ {v : Place k F | v.ord f ≠ 0} from h) rfl)
  obtain ⟨y, rfl⟩ := M'.pointEquivPlace.surjective w
  have hfmem : f ∈ ((M'.pointEquivPlace y).restrict F).toValuationSubring :=
    mem_of_ord_nonneg _ hf0 hordv.ge

  let x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _} :=
    ⟨y.1 ≫ π, by rw [Category.assoc, hπ]; exact y.2⟩
  have hxpt : ((pointEquivClosedPoint M.toBase x) : M.C) = π.base (pointEquivClosedPoint M'.toBase y).1 := by
    rw [pointEquivClosedPoint_apply_coe, pointEquivClosedPoint_apply_coe]
    rfl
  have hclosed : IsClosed ({π.base (pointEquivClosedPoint M'.toBase y).1} : Set M.C) := hxpt ▸ (pointEquivClosedPoint M.toBase x).2
  have hv : (M'.pointEquivPlace y).restrict F = M.placeOfPoint ⟨π.base (pointEquivClosedPoint M'.toBase y).1, hclosed⟩ := by
    rw [hplace y x rfl, CurveModel.pointEquivPlace_apply]
    congr 1
  have hrx : (stalkToField M (π.base (pointEquivClosedPoint M'.toBase y).1)).range
      = ((M'.pointEquivPlace y).restrict F).toValuationSubring.toSubring := by
    rw [hv]; exact M.range_stalk_eq ⟨π.base (pointEquivClosedPoint M'.toBase y).1, hclosed⟩
  have hfr : f ∈ (stalkToField M (π.base (pointEquivClosedPoint M'.toBase y).1)).range := by
    rw [hrx]; exact hfmem
  obtain ⟨s, hs⟩ := hfr
  rw [← hs]
  exact vanishesAt_psi_sub M M' π hπ φ hφk hφnat hplace y s

end Rigidity

end HG1bRigidity
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap.HG1bRigidity"

set_option linter.unusedSectionVars false

section RigiditySchemeSide
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve Topology

universe u v

namespace HG1bRig

variable {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]

omit [IsAlgClosed k] [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
  [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] [IsFinite π] [LocallyOfFinitePresentation π] in

theorem apply_genericPoint_eq : π.base (genericPoint M'.C) = genericPoint M.C := by
  obtain ⟨a, ha, hπa⟩ := Flat.generalizingMap π (genericPoint_specializes (π.base (genericPoint M'.C)))

  have hgen : IsGenericPoint a (Set.univ : Set M'.C) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    simp only [Set.mem_univ, iff_true]
    exact ha.trans (genericPoint_specializes y)
  have : a = genericPoint M'.C := hgen.eq (genericPoint_spec M'.C)
  rw [← this]; exact hπa

noncomputable def fieldMap : M.C.functionField →+* M'.C.functionField :=
  (π.stalkMap (genericPoint M'.C)).hom.comp
    (M.C.presheaf.stalkSpecializes
      (specializes_of_eq (apply_genericPoint_eq M M' π) : π.base (genericPoint M'.C) ⤳ genericPoint M.C)).hom

theorem algebraMap_stalkMap (p : M'.C) (s : M.C.presheaf.stalk (π.base p)) :
    algebraMap _ M'.C.functionField (π.stalkMap p s) = fieldMap M M' π (algebraMap _ M.C.functionField s) := by
  change (M'.C.presheaf.stalkSpecializes (genericPoint_specializes p)).hom (π.stalkMap p s) =
    (π.stalkMap (genericPoint M'.C)).hom ((M.C.presheaf.stalkSpecializes _).hom
      ((M.C.presheaf.stalkSpecializes (genericPoint_specializes (π.base p))).hom s))
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply π (genericPoint M'.C) p (genericPoint_specializes p) s]
  congr 1
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

include hπ in

theorem fieldMap_baseToFunctionField (a : k) :
    fieldMap M M' π (baseToFunctionField M.toBase a) = baseToFunctionField M'.toBase a := by
  change (π.stalkMap (genericPoint M'.C)).hom ((M.C.presheaf.stalkSpecializes _).hom
      ((M.C.presheaf.germ ⊤ (genericPoint M.C) trivial).hom
        (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)))) =
    (M'.C.presheaf.germ ⊤ (genericPoint M'.C) trivial).hom
      (M'.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a))
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]
  have happ : (π.app ⊤).hom (M.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) =
      M'.toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) := by
    rw [← hπ]
    rfl
  rw [happ]
  rfl

include hπ in

theorem rigidity_of_key
    (key : ∀ (φ : M.C.functionField →+* M'.C.functionField)
      (hφk : ∀ a : k, φ (baseToFunctionField M.toBase a) = baseToFunctionField M'.toBase a)
      (hφnat : ∀ (p : M'.C) (s : M.C.presheaf.stalk (π.base p)),
        algebraMap _ M'.C.functionField (π.stalkMap p s) = φ (algebraMap _ M.C.functionField s))
      (f : F), M'.ffEquiv.symm (φ (M.ffEquiv f)) = algebraMap F F' f)
    (p : M'.C) (s : M.C.presheaf.stalk (π.base p)) :
    M'.ffEquiv.symm (algebraMap _ M'.C.functionField (π.stalkMap p s)) =
      algebraMap F F' (M.ffEquiv.symm (algebraMap _ M.C.functionField s)) := by
  rw [algebraMap_stalkMap M M' π p s]
  conv_lhs => rw [← M.ffEquiv.apply_symm_apply (algebraMap _ M.C.functionField s)]
  exact key (fieldMap M M' π) (fieldMap_baseToFunctionField M M' π hπ) (algebraMap_stalkMap M M' π) _

end HG1bRig
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap.HG1bRigidity"

end RigiditySchemeSide
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap.HG1bRigidity"

section RigiditySolution
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u v

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {F F' : Type v} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    [IsCurveOver k F] [IsCurveOver k F'] [Algebra.EssFiniteType k F] [Algebra.EssFiniteType k F']
    [Algebra F F'] [IsScalarTower k F F'] [Algebra.IsIntegral F F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (π : M'.C ⟶ M.C) (hπ : π ≫ M.toBase = M'.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
        (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x)
    (p : M'.C) (s : M.C.presheaf.stalk (π.base p)) :
    M'.ffEquiv.symm (algebraMap _ M'.C.functionField (π.stalkMap p s)) =
      algebraMap F F' (M.ffEquiv.symm (algebraMap _ M.C.functionField s)) :=
  HG1bRig.rigidity_of_key M M' π hπ
    (fun φ hφk hφnat f => HG1bRigidity.key M M' π hπ φ hφk hφnat hplace f) p s

end RigiditySolution
p2m_reactivate "P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap.HG1bRigidity"

end S_AlgebraicCurve_CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_ffEquiv_symm_stalkMap_eq_algebraMap (solution)
