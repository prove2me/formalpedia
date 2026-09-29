-- Prove2me | solution 1 for AlgebraicGeometry.isAffineOpen_of_dense_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fa3d7718-8092-55fa-ad69-fb318967e1cb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isAffineOpen_of_dense_of_ringKrullDim_le_one

set_option autoImplicit false

universe u

open PrimeSpectrum

namespace P4A

variable {B : Type u} [CommRing B]

theorem isMaximal_of_not_mem_minimalPrimes (hB : ringKrullDim B ≤ 1) (q : Ideal B) [hq : q.IsPrime]
    (h : q ∉ minimalPrimes B) : q.IsMaximal := by
  have : Ring.KrullDimLE 1 B := (Order.krullDimLE_iff 1 (PrimeSpectrum B)).mpr (by exact_mod_cast hB)
  exact ((Ring.krullDimLE_one_iff.mp this) q hq).resolve_left h

theorem zeroLocus_finite_of_forall_isMaximal [IsNoetherianRing B] (I : Ideal B)
    (hI : ∀ q : Ideal B, q.IsPrime → I ≤ q → q.IsMaximal) :
    (zeroLocus (I : Set B)).Finite := by
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
  have hpre : (PrimeSpectrum.asIdeal ⁻¹' I.minimalPrimes : Set (PrimeSpectrum B)).Finite :=
    hfin.preimage (fun x _ y _ h => PrimeSpectrum.ext h)
  refine hpre.subset fun x hx => ?_
  rw [mem_zeroLocus, SetLike.coe_subset_coe] at hx
  obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le hx
  have hpmax : p.IsMaximal := hI p hp.1.1 hp.1.2
  have : p = x.asIdeal := (hpmax.eq_of_le x.isPrime.ne_top hpx)
  show x.asIdeal ∈ I.minimalPrimes
  rwa [← this]

theorem not_mem_minimalPrimes_of_interior_eq_empty [IsNoetherianRing B]
    (Z : Set (PrimeSpectrum B)) (hZ : IsClosed Z) (hZi : interior Z = ∅)
    (z : PrimeSpectrum B) (hz : z ∈ Z) : z.asIdeal ∉ minimalPrimes B := by
  intro hmin

  have hfin : (minimalPrimes B).Finite := minimalPrimes.finite_of_isNoetherianRing B
  let W : Set (PrimeSpectrum B) := (⋃ p ∈ (minimalPrimes B) \ {z.asIdeal}, zeroLocus (p : Set B))ᶜ
  have hWopen : IsOpen W := by
    refine (Set.Finite.isClosed_biUnion (hfin.diff) fun p _ => isClosed_zeroLocus _).isOpen_compl
  have hzW : z ∈ W := by
    simp only [W, Set.mem_compl_iff, Set.mem_iUnion, mem_zeroLocus, not_exists, exists_prop, not_and]
    intro p hp hpz

    exact hp.2 (le_antisymm (hmin.2 ⟨hp.1.1.1, bot_le⟩ hpz) hpz ▸ rfl)
  have hWZ : W ⊆ Z := by
    intro w hw

    obtain ⟨p, hp, hpw⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := w.asIdeal) bot_le
    have hpz : p = z.asIdeal := by
      by_contra hne
      simp only [W, Set.mem_compl_iff, Set.mem_iUnion, mem_zeroLocus, not_exists, exists_prop, not_and] at hw
      exact hw p ⟨hp, hne⟩ hpw
    have : w ∈ zeroLocus (z.asIdeal : Set B) := by rw [mem_zeroLocus, ← hpz]; exact hpw
    rw [← PrimeSpectrum.closure_singleton] at this
    exact hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hz) this
  have : z ∈ interior Z := mem_interior.mpr ⟨W, hWZ, hWopen, hzW⟩
  rw [hZi] at this
  exact this

theorem exists_mem_forall_not_mem_minimalPrimes [IsNoetherianRing B] (z : PrimeSpectrum B)
    (hz : z.asIdeal ∉ minimalPrimes B) : ∃ t ∈ z.asIdeal, ∀ p ∈ minimalPrimes B, t ∉ p := by
  classical
  have hfin : (minimalPrimes B).Finite := minimalPrimes.finite_of_isNoetherianRing B
  by_contra hcon
  push Not at hcon
  have hsub : (z.asIdeal : Set B) ⊆ ⋃ p ∈ hfin.toFinset, ((p : Ideal B) : Set B) := by
    intro t ht
    obtain ⟨p, hp, htp⟩ := hcon t ht
    exact Set.mem_iUnion₂.mpr ⟨p, hfin.mem_toFinset.mpr hp, htp⟩
  obtain ⟨p, hp, hzp⟩ := (Ideal.subset_union_prime z.asIdeal z.asIdeal
    (fun p hp _ _ => (hfin.mem_toFinset.mp hp).1.1)).mp hsub
  have hpmin := hfin.mem_toFinset.mp hp
  have : z.asIdeal = p := le_antisymm hzp (hpmin.2 ⟨z.isPrime, bot_le⟩ hzp)
  exact hz (this ▸ hpmin)

theorem exists_not_mem_forall_mem {F : Set (PrimeSpectrum B)} (hF : F.Finite) (z : PrimeSpectrum B)
    (hzF : z ∉ F) (hmax : ∀ w ∈ F, w.asIdeal.IsMaximal) :
    ∃ h : B, h ∉ z.asIdeal ∧ ∀ w ∈ F, h ∈ w.asIdeal := by
  classical
  have hpick : ∀ w : PrimeSpectrum B, ∃ a : B, w ∈ F → a ∈ w.asIdeal ∧ a ∉ z.asIdeal := by
    intro w
    by_cases hw : w ∈ F
    · have hne : ¬ w.asIdeal ≤ z.asIdeal := fun hle =>
        hzF (PrimeSpectrum.ext ((hmax w hw).eq_of_le z.isPrime.ne_top hle).symm ▸ hw)
      obtain ⟨a, haw, haz⟩ := Set.not_subset.mp (show ¬ ((w.asIdeal : Set B) ⊆ z.asIdeal) from hne)
      exact ⟨a, fun _ => ⟨haw, haz⟩⟩
    · exact ⟨0, fun h => (hw h).elim⟩
  choose a ha using hpick
  refine ⟨∏ w ∈ hF.toFinset, a w, ?_, ?_⟩
  · intro hmem
    obtain ⟨w, hw, haw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := z.isPrime)).mp hmem
    exact (ha w (hF.mem_toFinset.mp hw)).2 haw
  · intro w hw
    exact Ideal.prod_mem _ (hF.mem_toFinset.mpr hw) (ha w hw).1

theorem exists_basicOpen_inter_compl_eq [IsNoetherianRing B] (hB : ringKrullDim B ≤ 1)
    (Z : Set (PrimeSpectrum B)) (hZ : IsClosed Z) (hZi : interior Z = ∅)
    (z : PrimeSpectrum B) (hz : z ∈ Z) :
    ∃ h t : B, h ∉ z.asIdeal ∧
      (basicOpen h : Set (PrimeSpectrum B)) ∩ Zᶜ = (basicOpen (h * t) : Set (PrimeSpectrum B)) := by
  classical

  have hZmin : ∀ w ∈ Z, w.asIdeal ∉ minimalPrimes B :=
    fun w hw => not_mem_minimalPrimes_of_interior_eq_empty Z hZ hZi w hw
  have hZmax : ∀ w ∈ Z, w.asIdeal.IsMaximal :=
    fun w hw => isMaximal_of_not_mem_minimalPrimes hB w.asIdeal (hZmin w hw)

  obtain ⟨t, htz, ht⟩ := exists_mem_forall_not_mem_minimalPrimes z (hZmin z hz)

  have hVtmax : ∀ w ∈ zeroLocus ({t} : Set B), w.asIdeal.IsMaximal := by
    intro w hw
    refine isMaximal_of_not_mem_minimalPrimes hB w.asIdeal fun hmin => ht _ hmin ?_
    simpa [mem_zeroLocus] using hw
  have hVtfin : (zeroLocus ({t} : Set B)).Finite := by
    have := zeroLocus_finite_of_forall_isMaximal (Ideal.span {t}) (fun q hq hle => ?_)
    · rwa [zeroLocus_span] at this
    · haveI := hq
      refine isMaximal_of_not_mem_minimalPrimes hB q fun hmin => ht q hmin ?_
      exact hle (Ideal.subset_span (Set.mem_singleton t))
  have hZfin : Z.Finite := by
    have := zeroLocus_finite_of_forall_isMaximal (vanishingIdeal Z) (fun q hq hle => ?_)
    · rwa [zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq] at this
    · haveI := hq
      have hmem : (⟨q, hq⟩ : PrimeSpectrum B) ∈ Z := by
        rw [← hZ.closure_eq, ← zeroLocus_vanishingIdeal_eq_closure, mem_zeroLocus]
        exact hle
      exact hZmax _ hmem

  let F : Set (PrimeSpectrum B) := (Z ∪ zeroLocus ({t} : Set B)) \ {z}
  have hF : F.Finite := (hZfin.union hVtfin).diff
  obtain ⟨h, hhz, hhF⟩ := exists_not_mem_forall_mem hF z (fun hm => hm.2 rfl)
    (fun w hw => hw.1.elim (hZmax w) (hVtmax w))
  refine ⟨h, t, hhz, Set.ext fun x => ?_⟩
  simp only [Set.mem_inter_iff, SetLike.mem_coe, basicOpen_eq_zeroLocus_compl, Set.mem_compl_iff,
    mem_zeroLocus, Set.singleton_subset_iff]
  constructor
  · rintro ⟨hxh, hxZ⟩

    intro hht
    rcases x.isPrime.mem_or_mem hht with hh | hxt
    · exact hxh hh
    · have hxF : x ∈ F := ⟨Or.inr (by simpa [mem_zeroLocus] using hxt), fun hxz => hxZ (hxz ▸ hz)⟩
      exact hxh (hhF x hxF)
  · intro hx
    refine ⟨fun hh => hx (Ideal.mul_mem_right _ _ hh), fun hxZ => ?_⟩
    by_cases hxz : x = z
    · subst hxz; exact hx (Ideal.mul_mem_left _ _ htz)
    · exact hx (Ideal.mul_mem_right _ _ (hhF x ⟨Or.inl hxZ, hxz⟩))

end P4A

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Spec Scheme isAffineOpen_of_isAffineOpen_basicOpen IsAffineOpen basicOpen_eq_of_affine Scheme.ΓSpecIso IsAffineOpen.Spec_basicOpen" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in
open CategoryTheory _root_.AlgebraicGeometry Opposite in

theorem AlgebraicGeometry.isAffineOpen_of_dense_of_ringKrullDim_le_one'
    {B : Type u} [CommRing B] [IsNoetherianRing B] (hB : ringKrullDim B ≤ 1)
    (U : (Spec (CommRingCat.of B)).Opens) (hU : Dense (U : Set (Spec (CommRingCat.of B)))) :
    IsAffineOpen U := by
  classical
  let X := Spec (CommRingCat.of B)
  let U' : Set (PrimeSpectrum B) := (U : Set X)
  have hUo : IsOpen U' := U.2
  let Z : Set (PrimeSpectrum B) := U'ᶜ
  have hZ : IsClosed Z := hUo.isClosed_compl
  have hZi : interior Z = ∅ := by
    have : Dense U' := hU
    exact this.interior_compl

  have hloc : ∀ z : PrimeSpectrum B, ∃ h t : B, z ∈ Z → h ∉ z.asIdeal ∧
      (basicOpen h : Set (PrimeSpectrum B)) ∩ Zᶜ = (basicOpen (h * t) : Set (PrimeSpectrum B)) := by
    intro z
    by_cases hz : z ∈ Z
    · obtain ⟨h, t, hh, he⟩ := P4A.exists_basicOpen_inter_compl_eq hB Z hZ hZi z hz
      exact ⟨h, t, fun _ => ⟨hh, he⟩⟩
    · exact ⟨1, 1, fun h => (hz h).elim⟩
  choose h t hht using hloc

  let S₀ : Set B := {f : B | (basicOpen f : Set (PrimeSpectrum B)) ⊆ U'} ∪ Set.range (fun z : Z => h z)
  have hspan : Ideal.span S₀ = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    by_contra h1
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span S₀) (fun htop => h1 (htop ▸ Submodule.mem_top))
    let x : PrimeSpectrum B := ⟨m, hm.isPrime⟩
    by_cases hx : x ∈ U'
    ·
      obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
        PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hUo
      have hfS : f ∈ S₀ := Or.inl hfU
      exact hxf (hle (Ideal.subset_span hfS))
    · have hzS : h x ∈ S₀ := Or.inr ⟨⟨x, hx⟩, rfl⟩
      exact (hht x hx).1 (hle (Ideal.subset_span hzS))

  let φ : B →+* Γ(X, U) :=
    (X.presheaf.map (homOfLE le_top).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have hφ : ∀ b : B, X.basicOpen (φ b) = U ⊓ PrimeSpectrum.basicOpen b := by
    intro b
    show X.basicOpen (X.presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) = _
    rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]
  refine isAffineOpen_of_isAffineOpen_basicOpen U (φ '' S₀) ?_ ?_
  · rw [← Ideal.map_span, hspan, Ideal.map_top]
  · rintro _ ⟨b, hb, rfl⟩
    rw [hφ]
    rcases hb with hbU | ⟨z, rfl⟩
    ·
      have : U ⊓ PrimeSpectrum.basicOpen b = PrimeSpectrum.basicOpen b :=
        inf_eq_right.mpr (fun y hy => hbU hy)
      rw [this]
      exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of B) b
    ·
      have : U ⊓ PrimeSpectrum.basicOpen (h z) = PrimeSpectrum.basicOpen (h z * t z) := by
        apply TopologicalSpace.Opens.ext
        rw [TopologicalSpace.Opens.coe_inf, Set.inter_comm]
        have := (hht z.1 z.2).2
        simp only [Z, compl_compl] at this
        exact this
      rw [this]
      exact IsAffineOpen.Spec_basicOpen (R := CommRingCat.of B) (h z * t z)

open CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_isAffineOpen_of_dense_of_ringKrullDim_le_one.AlgebraicGeometry in

theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (hB : ringKrullDim B ≤ 1)
    (U : (Spec (CommRingCat.of B)).Opens) (hU : Dense (U : Set (Spec (CommRingCat.of B)))) :
    IsAffineOpen U :=
  AlgebraicGeometry.isAffineOpen_of_dense_of_ringKrullDim_le_one' hB U hU

end S_AlgebraicGeometry_isAffineOpen_of_dense_of_ringKrullDim_le_one
end P2MW
export P2MW.S_AlgebraicGeometry_isAffineOpen_of_dense_of_ringKrullDim_le_one (solution)
