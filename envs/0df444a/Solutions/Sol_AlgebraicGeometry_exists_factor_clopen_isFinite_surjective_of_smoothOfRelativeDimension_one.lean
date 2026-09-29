-- Prove2me | solution 1 for AlgebraicGeometry.exists_factor_clopen_isFinite_surjective_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/abf3c494-9781-586b-abd9-0906e4405c38

import Mathlib
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_factor_clopen_isFinite_surjective_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

universe u

namespace C0ToUBody

theorem main
    {k : Type u} [Field k] {M XH : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 πM]
    (πXH : XH ⟶ Spec (CommRingCat.of k)) (πH : M ⟶ XH) (hπHX : πH ≫ πXH = πM) [IsFinite πH]
    (C₀ : M.Opens) (hC₀cl : IsClosed (C₀ : Set M)) (hC₀conn : _root_.IsConnected (C₀ : Set M))
    [IsIntegral (C₀ : Scheme.{u})]
    (U : XH.Opens) (hUcl : IsClosed (U : Set XH)) [IsIntegral (U : Scheme.{u})]
    [SmoothOfRelativeDimension 1 (U.ι ≫ πXH)]
    (x : M) (hx : x ∈ C₀) (hxU : πH.base x ∈ U) :
    ∃ c : (C₀ : Scheme.{u}) ⟶ (U : Scheme.{u}), c ≫ U.ι = C₀.ι ≫ πH ∧ IsFinite c ∧ Function.Surjective c.base := by
  classical

  have hrange : Set.range (C₀.ι ≫ πH).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    refine (hC₀conn.image _ πH.base.hom.continuous.continuousOn).isPreconnected.subset_isClopen
      ⟨hUcl, U.isOpen⟩ ⟨πH.base x, ⟨x, hx, rfl⟩, hxU⟩
  let c : (C₀ : Scheme.{u}) ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι (C₀.ι ≫ πH) hrange
  have hc : c ≫ U.ι = C₀.ι ≫ πH := IsOpenImmersion.lift_fac _ _ _

  haveI : IsClosedImmersion C₀.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hC₀cl)
  haveI : IsFinite (c ≫ U.ι) := by rw [hc]; infer_instance
  haveI hcfin : IsFinite c := IsFinite.of_comp c U.ι
  refine ⟨c, hc, hcfin, ?_⟩

  intro u
  by_contra hu

  haveI : SmoothOfRelativeDimension 1 (C₀.ι ≫ πM) := by
    have := smoothOfRelativeDimension_comp 0 1 C₀.ι πM
    rwa [zero_add] at this
  haveI : Nonempty (C₀ : Scheme.{u}) := ⟨(⟨x, hx⟩ : C₀)⟩
  have h1 : ((1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim (C₀ : Scheme.{u}) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.le_topologicalKrullDim (C₀.ι ≫ πM) 1
  rw [Nat.cast_one] at h1
  obtain ⟨A, B, hAB⟩ := Order.one_le_krullDim_iff.mp h1

  set a := A.isIrreducible.genericPoint with ha_def
  set b := B.isIrreducible.genericPoint with hb_def
  have ha : IsGenericPoint a (A : Set (C₀ : Scheme.{u})) :=
    A.isIrreducible.isGenericPoint_genericPoint A.isClosed
  have hb : IsGenericPoint b (B : Set (C₀ : Scheme.{u})) :=
    B.isIrreducible.isGenericPoint_genericPoint B.isClosed
  have hba : b ⤳ a := by
    rw [specializes_iff_mem_closure, hb.def]
    exact hAB.le ha.mem
  have hab : a ≠ b := by
    intro h
    apply hAB.ne
    apply IrreducibleCloseds.ext
    rw [← ha.def, ← hb.def, h]

  have hsp : c.base b ⤳ c.base a := hba.map c.base.hom.continuous
  by_cases heq : c.base a = c.base b
  ·
    have hd := c.isDiscrete_preimage_singleton (c.base b)
    exact hab (hd.eq_of_specializes hba rfl heq).symm
  ·
    have h2 : topologicalKrullDim (U : Scheme.{u}) ≤ (1 : ℕ) :=
      AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le (U.ι ≫ πXH) 1
    let Za : IrreducibleCloseds (U : Scheme.{u}) :=
      ⟨closure {c.base a}, isIrreducible_singleton.closure, isClosed_closure⟩
    let Zb : IrreducibleCloseds (U : Scheme.{u}) :=
      ⟨closure {c.base b}, isIrreducible_singleton.closure, isClosed_closure⟩
    let ZU : IrreducibleCloseds (U : Scheme.{u}) :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
    have hab' : Za < Zb := by
      refine lt_of_le_of_ne ?_ ?_
      · change closure {c.base a} ⊆ closure {c.base b}
        exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hsp))
          isClosed_closure
      · intro h
        apply heq
        have h' : closure {c.base a} = closure {c.base b} := congrArg IrreducibleCloseds.carrier h
        exact (inseparable_iff_closure_eq.mpr h').eq
    have hbU : Zb < ZU := by
      refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_
      intro h
      have h' : closure {c.base b} = Set.univ := congrArg IrreducibleCloseds.carrier h

      have hcl : IsClosed (Set.range c.base) := c.isClosedMap.isClosed_range
      have hsub : closure {c.base b} ⊆ Set.range c.base :=
        closure_minimal (Set.singleton_subset_iff.mpr ⟨b, rfl⟩) hcl
      rw [h'] at hsub
      exact hu (hsub (Set.mem_univ u))
    let p : LTSeries (IrreducibleCloseds (U : Scheme.{u})) :=
      ((RelSeries.singleton _ Za).snoc Zb hab').snoc ZU (by
        rw [RelSeries.last_snoc]; exact hbU)
    have hp : p.length = 2 := by simp [p]
    have := Order.LTSeries.length_le_krullDim p
    rw [hp] at this
    have h3 : ((2 : ℕ) : WithBot ℕ∞) ≤ (1 : ℕ) := this.trans h2
    exact absurd (WithBot.coe_le_coe.mp h3) (by norm_num)

end C0ToUBody

theorem solution
    {k : Type u} [Field k] {M XH : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 πM]
    (πXH : XH ⟶ Spec (CommRingCat.of k)) (πH : M ⟶ XH) (hπHX : πH ≫ πXH = πM) [IsFinite πH]
    (C₀ : M.Opens) (hC₀cl : IsClosed (C₀ : Set M)) (hC₀conn : _root_.IsConnected (C₀ : Set M))
    [IsIntegral (C₀ : Scheme.{u})]
    (U : XH.Opens) (hUcl : IsClosed (U : Set XH)) [IsIntegral (U : Scheme.{u})]
    [SmoothOfRelativeDimension 1 (U.ι ≫ πXH)]
    (x : M) (hx : x ∈ C₀) (hxU : πH.base x ∈ U) :
    ∃ c : (C₀ : Scheme.{u}) ⟶ (U : Scheme.{u}), c ≫ U.ι = C₀.ι ≫ πH ∧ IsFinite c ∧ Function.Surjective c.base :=
  C0ToUBody.main πM πXH πH hπHX C₀ hC₀cl hC₀conn U hUcl x hx hxU

end S_AlgebraicGeometry_exists_factor_clopen_isFinite_surjective_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_factor_clopen_isFinite_surjective_of_smoothOfRelativeDimension_one (solution)
