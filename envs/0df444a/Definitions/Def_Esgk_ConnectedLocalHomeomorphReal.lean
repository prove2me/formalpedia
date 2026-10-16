-- Prove2me | Definitions.Def_Esgk_ConnectedLocalHomeomorphReal
-- name    : Esgk_ConnectedLocalHomeomorphReal
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:43:49.775179+00:00
-- url     : https://prove2.me/theorems/74ed93bd-8963-41d8-9156-e8dc29e1642b
-- title:
--   Inverse branches for real-valued local homeomorphisms
-- statement:
--   For a real-valued local homeomorphism on a Hausdorff space, this defines continuous inverse branches on open intervals and gluing of compatible branches. When the source is connected, it proves injectivity and constructs a homeomorphism onto the range.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order.IntermediateValue

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology Filter

namespace Esgk

variable {X : Type*} [TopologicalSpace X] [T2Space X] {f : X → ℝ}

structure bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch (f : X → ℝ) where
  domain : Set ℝ
  isOpen_domain : IsOpen domain
  ordConnected_domain : OrdConnected domain
  toFun : ℝ → X
  continuousOn_toFun : ContinuousOn toFun domain
  right_inv : ∀ t ∈ domain, f (toFun t) = t

theorem bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch.agree (hf : IsLocalHomeomorph f)
    (b c : bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch f) {t : ℝ} (htb : t ∈ b.domain) (htc : t ∈ c.domain)
    (ht : b.toFun t = c.toFun t) : EqOn b.toFun c.toFun (b.domain ∩ c.domain) := by
  apply (T2Space.isSeparatedMap f).eqOn_of_comp_eqOn hf.isLocallyInjective
    (b.ordConnected_domain.inter c.ordConnected_domain).isPreconnected
    (b.continuousOn_toFun.mono inter_subset_left)
    (c.continuousOn_toFun.mono inter_subset_right) ?_ ⟨htb, htc⟩ ht
  intro u hu
  exact (b.right_inv u hu.1).trans (c.right_inv u hu.2).symm

omit [T2Space X] in
theorem bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch.isOpen_image (hf : IsLocalHomeomorph f)
    (b : bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch f) : IsOpen (b.toFun '' b.domain) := by
  have hc : Continuous (b.domain.domRestrict b.toFun) :=
    continuousOn_iff_continuous_domRestrict.mp b.continuousOn_toFun
  have he : IsOpenEmbedding (f ∘ b.domain.domRestrict b.toFun) := by
    have h : f ∘ b.domain.domRestrict b.toFun = (Subtype.val : b.domain → ℝ) := by
      funext t
      exact b.right_inv t t.property
    rw [h]
    exact b.isOpen_domain.isOpenEmbedding_subtypeVal
  simpa only [range_domRestrict] using (hf.isOpenEmbedding_of_comp he hc).isOpen_range

def bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch.union (b c : bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch f)
    (hc : (b.domain ∩ c.domain).Nonempty)
    (he : EqOn b.toFun c.toFun (b.domain ∩ c.domain)) : bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch f := by
  classical
  let g := b.domain.piecewise b.toFun c.toFun
  have hb : EqOn g b.toFun b.domain := by
    intro t ht
    exact piecewise_eq_of_mem _ _ _ ht
  have hd : EqOn g c.toFun c.domain := by
    intro t ht
    by_cases htb : t ∈ b.domain
    · exact (hb htb).trans (he ⟨htb, ht⟩)
    · exact piecewise_eq_of_notMem _ _ _ htb
  exact {
    domain := b.domain ∪ c.domain
    isOpen_domain := b.isOpen_domain.union c.isOpen_domain
    ordConnected_domain := (b.ordConnected_domain.isPreconnected.union' hc
      c.ordConnected_domain.isPreconnected).ordConnected
    toFun := g
    continuousOn_toFun := (b.continuousOn_toFun.congr hb).union_of_isOpen
      (c.continuousOn_toFun.congr hd) b.isOpen_domain c.isOpen_domain
    right_inv := fun t ht ↦ ht.elim
      (fun h ↦ (congrArg f (hb h)).trans (b.right_inv t h))
      (fun h ↦ (congrArg f (hd h)).trans (c.right_inv t h)) }

omit [T2Space X] in
theorem bundle_Esgk_ConnectedLocalHomeomorphReal_exists_realInverseBranch (hf : IsLocalHomeomorph f) (x : X) :
    ∃ b : bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch f, f x ∈ b.domain ∧ b.toFun (f x) = x := by
  obtain ⟨e, hx, he⟩ := hf x
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (e.open_target.mem_nhds (e.map_source hx))
  refine ⟨{
    domain := Ioo a b
    isOpen_domain := isOpen_Ioo
    ordConnected_domain := ordConnected_Ioo
    toFun := e.symm
    continuousOn_toFun := e.continuousOn_symm.mono hsub
    right_inv := ?_ }, ?_, ?_⟩
  · intro t ht
    rw [he]
    exact e.right_inv (hsub ht)
  · simpa only [he] using hab
  · change e.symm (f x) = x
    rw [he]
    exact e.left_inv hx


theorem injective_of_isLocalHomeomorph_real [ConnectedSpace X]
    (hf : IsLocalHomeomorph f) : Function.Injective f := by
  classical
  let x₀ : X := Classical.choice inferInstance
  let U : Set X := {x | ∃ b : bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch f,
    f x₀ ∈ b.domain ∧ b.toFun (f x₀) = x₀ ∧ x ∈ b.toFun '' b.domain}
  have hopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨b, hb, he, hx⟩
    exact mem_of_superset ((b.isOpen_image hf).mem_nhds hx)
      (fun y hy ↦ ⟨b, hb, he, hy⟩)
  have hclosed : IsClosed U := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨c, hc, hcx⟩ := bundle_Esgk_ConnectedLocalHomeomorphReal_exists_realInverseBranch hf x
    have him : x ∈ c.toFun '' c.domain := ⟨f x, hc, hcx⟩
    refine mem_of_superset ((c.isOpen_image hf).mem_nhds him) ?_
    rintro y ⟨t, ht, hty⟩ hy
    obtain ⟨b, hb, hbx, u, hu, huy⟩ := hy
    have htu : t = u := by
      rw [← c.right_inv t ht, ← b.right_inv u hu, hty, huy]
    subst u
    have he := b.agree hf c hu ht (huy.trans hty.symm)
    let d := b.union c ⟨t, hu, ht⟩ he
    apply hx
    refine ⟨d, Or.inl hb, ?_, f x, Or.inr hc, ?_⟩
    · simpa only [d, bundle_Esgk_ConnectedLocalHomeomorphReal_RealInverseBranch.union, piecewise_eq_of_mem _ _ _ hb] using hbx
    · change b.domain.piecewise b.toFun c.toFun (f x) = x
      by_cases hxb : f x ∈ b.domain
      · rw [piecewise_eq_of_mem _ _ _ hxb, he ⟨hxb, hc⟩, hcx]
      · rw [piecewise_eq_of_notMem _ _ _ hxb, hcx]
  have hne : U.Nonempty := by
    obtain ⟨b, hb, hbx⟩ := bundle_Esgk_ConnectedLocalHomeomorphReal_exists_realInverseBranch hf x₀
    exact ⟨x₀, b, hb, hbx, f x₀, hb, hbx⟩
  have hall : U = univ := (IsClopen.eq_univ ⟨hclosed, hopen⟩ hne)
  intro x y hxy
  obtain ⟨b, hb, hbx, s, hs, hsx⟩ : x ∈ U := hall ▸ mem_univ x
  obtain ⟨c, hc, hcx, t, ht, hty⟩ : y ∈ U := hall ▸ mem_univ y
  have hst : s = t := by
    rw [← b.right_inv s hs, ← c.right_inv t ht, hsx, hty, hxy]
  subst t
  exact hsx.symm.trans ((b.agree hf c hb hc (hbx.trans hcx.symm) ⟨hs, ht⟩).trans hty)


def homeomorphRangeOfIsLocalHomeomorphReal [ConnectedSpace X]
    (hf : IsLocalHomeomorph f) : X ≃ₜ Set.range f :=
  (hf.isOpenEmbedding_of_injective (injective_of_isLocalHomeomorph_real hf)).isEmbedding.toHomeomorph


end Esgk


