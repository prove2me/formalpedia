-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_forall_eq_appLE_of_forall_map_eq_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f022c9a6-204c-5522-b019-5d8ffd816b13

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_nonempty_of_compactSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace G5cAffineFamilyConstAux

variable {P : Scheme.{u}}

noncomputable abbrev rr {O O' : P.Opens} (h : O ≤ O') : Γ(P, O') →+* Γ(P, O) :=
  (P.presheaf.map (homOfLE h).op).hom

theorem rr_rr {O O' O'' : P.Opens} (h : O ≤ O') (h' : O' ≤ O'') (x : Γ(P, O'')) :
    rr h (rr h' x) = rr (h.trans h') x := by
  change (P.presheaf.map (homOfLE h').op ≫ P.presheaf.map (homOfLE h).op).hom x = _
  rw [← Functor.map_comp]
  rfl

theorem restrict_inter (𝒲 : P.OrderedAffineCover) {R : Type u} [CommRing R] (π : P ⟶ Spec (.of R))
    [IsSeparated π] {W : P.Opens} (hW : IsAffineOpen W) {b : ℕ} (t : (𝒲.restrict π hW).Idx b) :
    (𝒲.restrict π hW).inter t = 𝒲.inter t ⊓ W := by
  show (⨅ j, 𝒲.U (t.1 j) ⊓ W) = (⨅ j, 𝒲.U (t.1 j)) ⊓ W
  exact le_antisymm (le_inf (iInf_mono fun _ => inf_le_left) ((iInf_le _ 0).trans inf_le_right))
    (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

end G5cAffineFamilyConstAux

open G5cAffineFamilyConstAux in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact fX] [IsSeparated fX]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ fX.appTop).hom)
    (a : ∀ U : X.affineOpens, Γ(X, U.1))
    (ha : ∀ (U U' : X.affineOpens) (h : U'.1 ≤ U.1),
      (X.presheaf.map (homOfLE h).op).hom (a U) = a U') :
    ∃ c : R, ∀ U : X.affineOpens,
      a U = (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  obtain ⟨𝒳⟩ := Scheme.OrderedAffineCover.nonempty_of_compactSpace X
  letI := Scheme.OrderedAffineCoverOf.moduleSections fX

  have hKaff : ∀ {b : ℕ} (t : 𝒳.Idx b), IsAffineOpen (𝒳.toCoverOf.inter t) :=
    fun t => Scheme.OrderedAffineCover.isAffineOpen_inter fX 𝒳 t
  let A : ∀ {b : ℕ}, 𝒳.Idx b → X.affineOpens := fun t => ⟨𝒳.toCoverOf.inter t, hKaff t⟩
  have hRaff : ∀ (U : X.affineOpens) {b : ℕ} (t : (𝒳.restrict fX U.2).Idx b),
      IsAffineOpen ((𝒳.restrict fX U.2).inter t) := by
    intro U b t
    rw [restrict_inter]
    exact Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated fX
      (Scheme.OrderedAffineCover.isAffineOpen_inter fX 𝒳 t) U.2
  let A' : ∀ (U : X.affineOpens) {b : ℕ}, (𝒳.restrict fX U.2).Idx b → X.affineOpens :=
    fun U {b} t => ⟨(𝒳.restrict fX U.2).inter t, hRaff U t⟩

  have hmem : (fun t => a (A t) : 𝒳.toCoverOf.cochain 0) ∈ LinearMap.ker (𝒳.toCoverOf.d fX 0) := by
    rw [LinearMap.mem_ker]
    funext s
    rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
    have hj : ∀ j : Fin (0 + 2),
        rr (𝒳.toCoverOf.inter_le_inter_face s j) (a (A (𝒳.toCoverOf.face s j))) = a (A s) :=
      fun j => ha (A (𝒳.toCoverOf.face s j)) (A s) (𝒳.toCoverOf.inter_le_inter_face s j)
    calc ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          rr (𝒳.toCoverOf.inter_le_inter_face s j) (a (A (𝒳.toCoverOf.face s j)))
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • a (A s) := Finset.sum_congr rfl fun j _ => by rw [hj]
      _ = 0 := by rw [Fin.sum_univ_two]; simp
  have hrange : (fun t => a (A t) : 𝒳.toCoverOf.cochain 0) ∈ LinearMap.range (𝒳.toCoverOf.aug fX) := by
    rw [← AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
    exact hmem
  obtain ⟨sec, hsec⟩ := hrange

  obtain ⟨c, hc⟩ := hX.2 sec
  refine ⟨c, fun U => ?_⟩
  have hsU : (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
      = rr (le_top : U.1 ≤ ⊤) sec := by
    rw [← hc]
    rfl
  rw [hsU]

  apply AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective fX (𝒳.restrict fX U.2)
  funext t
  rw [Scheme.OrderedAffineCoverOf.aug_apply, Scheme.OrderedAffineCoverOf.aug_apply]
  change rr _ (a U) = rr _ (rr _ sec)
  have hle1 : (𝒳.restrict fX U.2).inter t ≤ 𝒳.toCoverOf.inter t := by
    rw [restrict_inter]; exact inf_le_left
  have h1 : rr ((𝒳.restrict fX U.2).inter_le_base t) (a U) = a (A' U t) := ha U (A' U t) _
  have h2 : rr hle1 (a (A t)) = a (A' U t) := ha (A t) (A' U t) hle1
  have h3 : rr (𝒳.toCoverOf.inter_le_base t) sec = a (A t) := congrFun hsec t
  rw [h1, rr_rr, ← h2, ← h3, rr_rr]

end S_AlgebraicGeometry_Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective (solution)
