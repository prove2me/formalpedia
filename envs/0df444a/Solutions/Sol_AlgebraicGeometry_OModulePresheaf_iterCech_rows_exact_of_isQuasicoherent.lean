-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.iterCech_rows_exact_of_isQuasicoherent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/486ed762-04fa-5d25-a1b0-4cbde504a805

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_IterCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_restrict
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_iterCech_rows_exact_of_isQuasicoherent
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace G3Sol

p2m_open "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.OModulePresheaf"

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (.of R))

omit π in
theorem inf_iInf_fin {n : ℕ} (a : Z.Opens) (f : Fin (n + 1) → Z.Opens) : a ⊓ (⨅ j, f j) = ⨅ j, (a ⊓ f j) :=
  le_antisymm (le_iInf fun j => inf_le_inf_left _ (iInf_le _ j))
    (le_inf ((iInf_le _ 0).trans inf_le_left) (le_iInf fun j => (iInf_le _ j).trans inf_le_right))

theorem isAffineOpen_iInf_fin [IsSeparated π] :
    ∀ (n : ℕ) (f : Fin (n + 1) → Z.Opens), (∀ j, IsAffineOpen (f j)) → IsAffineOpen (⨅ j, f j) := by
  intro n
  induction n with
  | zero =>
    intro f hf
    have h1 : (⨅ j : Fin 1, f j) = f 0 :=
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    rw [h1]; exact hf 0
  | succ m ih =>
    intro f hf
    have hsplit : (⨅ j : Fin (m + 2), f j) = f 0 ⊓ (⨅ j : Fin (m + 1), f j.succ) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
    rw [hsplit]
    exact Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π (hf 0) (ih _ fun j => hf j.succ)

variable (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))

include haff in

theorem isAffineOpen_slot [IsSeparated π] {p q : ℕ} (s : 𝔄.Idx p) (t : 𝔅.Idx q) :
    IsAffineOpen (𝔄.inter s ⊓ 𝔅.inter t) := by
  have h1 : 𝔄.inter s ⊓ 𝔅.inter t = ⨅ i, (𝔄.U (s.1 i) ⊓ 𝔅.inter t) := by
    show (⨅ i, 𝔄.U (s.1 i)) ⊓ 𝔅.inter t = _
    rw [inf_comm, inf_iInf_fin]
    exact iInf_congr fun i => inf_comm _ _
  rw [h1]
  refine isAffineOpen_iInf_fin π _ _ fun i => ?_
  show IsAffineOpen (𝔄.U (s.1 i) ⊓ ⨅ j, 𝔅.U (t.1 j))
  rw [inf_iInf_fin]
  exact isAffineOpen_iInf_fin π _ _ fun j => haff _ _

variable (ℭ : Z.OrderedAffineCover)

def sliceCover [IsSeparated π] (O : Z.Opens) (hO : IsAffineOpen O) : (O : Scheme.{u}).OrderedAffineCover where
  ι := ℭ.ι
  U k := O.ι ⁻¹ᵁ (O ⊓ ℭ.U k)
  isAffineOpen k := (Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π hO (ℭ.isAffineOpen k))
    |>.preimage_of_isOpenImmersion O.ι (by rw [Scheme.Opens.opensRange_ι]; exact inf_le_left)
  iSup_eq_top := by
    apply eq_top_iff.mpr
    intro x _
    have hx : (O.ι.base x) ∈ (⨆ k, ℭ.U k) := by rw [ℭ.iSup_eq_top]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, ⟨x.2, hk⟩⟩

theorem sliceCover_U [IsSeparated π] (O : Z.Opens) (hO : IsAffineOpen O) (k : ℭ.ι) :
    (sliceCover π ℭ O hO).U k = O.ι ⁻¹ᵁ (O ⊓ ℭ.U k) := rfl

theorem image_inter_sliceCover_le [IsSeparated π] (O : Z.Opens) (hO : IsAffineOpen O) {r : ℕ} (K : ℭ.Idx r) :
    O.ι ''ᵁ (sliceCover π ℭ O hO).inter (show (sliceCover π ℭ O hO).Idx r from K) ≤ O ⊓ ℭ.toOpenFamily.inter K := by
  refine le_inf ((Scheme.Hom.image_le_opensRange _ _).trans (by rw [Scheme.Opens.opensRange_ι]))
    (le_iInf fun l => ?_)
  refine (Scheme.Hom.image_mono _ (iInf_le _ l)).trans ?_
  show O.ι ''ᵁ (O.ι ⁻¹ᵁ (O ⊓ ℭ.U (K.1 l))) ≤ ℭ.U (K.1 l)
  exact (Scheme.Hom.image_preimage_le _ _).trans inf_le_right

theorem le_image_inter_sliceCover [IsSeparated π] (O : Z.Opens) (hO : IsAffineOpen O) {r : ℕ} (K : ℭ.Idx r) :
    O ⊓ ℭ.toOpenFamily.inter K ≤ O.ι ''ᵁ (sliceCover π ℭ O hO).inter (show (sliceCover π ℭ O hO).Idx r from K) := by
  have h1 : O.ι ⁻¹ᵁ (O ⊓ ℭ.toOpenFamily.inter K) ≤ (sliceCover π ℭ O hO).inter (show (sliceCover π ℭ O hO).Idx r from K) :=
    le_iInf fun l => Scheme.Hom.preimage_mono _ (inf_le_inf_left _ (iInf_le _ l))
  calc O ⊓ ℭ.toOpenFamily.inter K = O.ι ''ᵁ O.ι ⁻¹ᵁ (O ⊓ ℭ.toOpenFamily.inter K) := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
          inf_eq_right.mpr inf_le_left]
    _ ≤ _ := Scheme.Hom.image_mono _ h1

theorem image_top_le (O : Z.Opens) : O.ι ''ᵁ ⊤ ≤ O := (Scheme.Opens.ι_image_top O).le
theorem le_image_top (O : Z.Opens) : O ≤ O.ι ''ᵁ ⊤ := (Scheme.Opens.ι_image_top O).ge

theorem slot_le {p q r : ℕ} (s : 𝔄.Idx p) (t : 𝔅.Idx q) (K : ℭ.Idx r) :
    𝔄.inter s ⊓ (𝔅.restr (ℭ.toOpenFamily.inter K)).inter (show (𝔅.restr _).Idx q from t)
      ≤ (𝔄.inter s ⊓ 𝔅.inter t) ⊓ ℭ.toOpenFamily.inter K :=
  le_inf (inf_le_inf_left _ ((𝔅.restr_inter_le _ t).trans inf_le_left))
    (inf_le_right.trans ((𝔅.restr_inter_le _ t).trans inf_le_right))

theorem le_slot {p q r : ℕ} (s : 𝔄.Idx p) (t : 𝔅.Idx q) (K : ℭ.Idx r) :
    (𝔄.inter s ⊓ 𝔅.inter t) ⊓ ℭ.toOpenFamily.inter K
      ≤ 𝔄.inter s ⊓ (𝔅.restr (ℭ.toOpenFamily.inter K)).inter (show (𝔅.restr _).Idx q from t) := by
  refine le_inf (inf_le_left.trans inf_le_left) ?_
  exact (inf_le_inf_right _ inf_le_right).trans (𝔅.le_restr_inter _ t)

section Slot

variable (N : Z.Modules)

local notation "FX" => OModulePresheaf.ofModules π N

noncomputable def slotD (O : Z.Opens) (r : ℕ)
    (y : ∀ K : ℭ.Idx r, (OModulePresheaf.ofModules π N).obj (O ⊓ ℭ.toOpenFamily.inter K))
    (K : ℭ.Idx (r + 1)) : (OModulePresheaf.ofModules π N).obj (O ⊓ ℭ.toOpenFamily.inter K) :=
  ∑ j : Fin (r + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    (OModulePresheaf.ofModules π N).res (inf_le_inf_left O (ℭ.toOpenFamily.inter_le_inter_face K j))
      (y (ℭ.toOpenFamily.face K j))

variable [IsSeparated π]

omit [IsSeparated π] in
theorem resO_eq (O : Z.Opens) {W W' : (O : Scheme.{u}).Opens} (h : W ≤ W') (y : (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).obj W') :
    (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).res h y = (FX).res (O.ι.image_mono h) (show (FX).obj (O.ι ''ᵁ W') from y) := by
  show (N.restrict O.ι).presheaf.map (homOfLE h).op y = N.presheaf.map (homOfLE _).op y
  rw [Scheme.Modules.restrict_map]
  exact congrArg (fun g : (O.ι ''ᵁ W ⟶ O.ι ''ᵁ W') => N.presheaf.map g.op y) (Subsingleton.elim _ _)

noncomputable def up (O : Z.Opens) (hO : IsAffineOpen O) {r : ℕ} (K : ℭ.Idx r)
    (v : (FX).obj (O ⊓ ℭ.toOpenFamily.inter K)) :
    (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).obj ((sliceCover π ℭ O hO).inter (show (sliceCover π ℭ O hO).Idx r from K)) :=
  show (FX).obj (O.ι ''ᵁ (sliceCover π ℭ O hO).inter (show (sliceCover π ℭ O hO).Idx r from K)) from
    (FX).res (image_inter_sliceCover_le π ℭ O hO K) v

noncomputable def down (O : Z.Opens) (hO : IsAffineOpen O) {r : ℕ} (K : ℭ.Idx r)
    (w : (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).obj ((sliceCover π ℭ O hO).inter (show (sliceCover π ℭ O hO).Idx r from K))) :
    (FX).obj (O ⊓ ℭ.toOpenFamily.inter K) :=
  (FX).res (le_image_inter_sliceCover π ℭ O hO K)
    (show (FX).obj (O.ι ''ᵁ (sliceCover π ℭ O hO).inter (show (sliceCover π ℭ O hO).Idx r from K)) from w)

theorem down_up (O : Z.Opens) (hO : IsAffineOpen O) {r : ℕ} (K : ℭ.Idx r)
    (v : (FX).obj (O ⊓ ℭ.toOpenFamily.inter K)) : down π ℭ N O hO K (up π ℭ N O hO K v) = v := by
  show (FX).res _ ((FX).res _ v) = v
  rw [OModulePresheaf.res_res]; exact OModulePresheaf.res_refl_apply _ _ _

theorem up_down (O : Z.Opens) (hO : IsAffineOpen O) {r : ℕ} (K : ℭ.Idx r)
    (w : (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).obj ((sliceCover π ℭ O hO).inter (show (sliceCover π ℭ O hO).Idx r from K))) :
    up π ℭ N O hO K (down π ℭ N O hO K w) = w := by
  show (FX).res _ ((FX).res _ w) = w
  rw [OModulePresheaf.res_res]; exact OModulePresheaf.res_refl_apply _ _ _

theorem d_up (O : Z.Opens) (hO : IsAffineOpen O) (r : ℕ)
    (y : ∀ K : ℭ.Idx r, (FX).obj (O ⊓ ℭ.toOpenFamily.inter K)) (K : ℭ.Idx (r + 1)) :
    (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).d (sliceCover π ℭ O hO) r (fun K => up π ℭ N O hO K (y K)) K
      = up π ℭ N O hO K (slotD π ℭ N O r y K) := by
  rw [OModulePresheaf.d_apply]
  show _ = (FX).res _ (slotD π ℭ N O r y K)
  rw [slotD, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [resO_eq, map_zsmul]
  show _ = ((-1 : ℤ) ^ (j : ℕ)) • (FX).res _ ((FX).res _ (y _))
  rw [OModulePresheaf.res_res]
  show ((-1 : ℤ) ^ (j : ℕ)) • (FX).res _ ((FX).res _ (y _)) = _
  rw [OModulePresheaf.res_res]
  rfl

theorem slot_exact (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (O : Z.Opens) (hO : IsAffineOpen O) (r : ℕ)
    (y : ∀ K : ℭ.Idx (r + 1), (OModulePresheaf.ofModules π N).obj (O ⊓ ℭ.toOpenFamily.inter K))
    (hy : ∀ K', slotD π ℭ N O (r + 1) y K' = 0) :
    ∃ b : ∀ K : ℭ.Idx r, (OModulePresheaf.ofModules π N).obj (O ⊓ ℭ.toOpenFamily.inter K),
      ∀ K, y K = slotD π ℭ N O r b K := by
  haveI : IsAffine (O : Scheme.{u}) := hO
  have hF' : (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).IsQuasicoherent := OModulePresheaf.isQuasicoherent_ofModules_restrict π N hN O
  set y' : (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).cochain (sliceCover π ℭ O hO) (r + 1) := fun K => up π ℭ N O hO K (y K) with hy'
  have hker : y' ∈ LinearMap.ker ((OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).d (sliceCover π ℭ O hO) (r + 1)) := by
    rw [LinearMap.mem_ker]
    funext K
    rw [hy', d_up, hy]
    exact map_zero _
  obtain ⟨b', hb'⟩ := OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)) hF' _ r hker
  refine ⟨fun K => down π ℭ N O hO K (b' K), fun K => ?_⟩
  rw [← down_up π ℭ N O hO K (y K), ← down_up π ℭ N O hO K (slotD π ℭ N O r _ K), ← d_up]
  congr 1
  rw [show ((OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).d (sliceCover π ℭ O hO) r)
      (fun K => up π ℭ N O hO K (down π ℭ N O hO K (b' K))) = y' from by
    rw [← hb']; congr 1; exact funext fun K => up_down π ℭ N O hO K _]

theorem slot_exact_zero (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (O : Z.Opens) (hO : IsAffineOpen O)
    (y : ∀ K : ℭ.Idx 0, (OModulePresheaf.ofModules π N).obj (O ⊓ ℭ.toOpenFamily.inter K))
    (hy : ∀ K', slotD π ℭ N O 0 y K' = 0) :
    ∃! x : (OModulePresheaf.ofModules π N).obj O,
      ∀ K, y K = (OModulePresheaf.ofModules π N).res inf_le_left x := by
  haveI : IsAffine (O : Scheme.{u}) := hO
  have hF' : (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).IsQuasicoherent := OModulePresheaf.isQuasicoherent_ofModules_restrict π N hN O
  set y' : (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).cochain (sliceCover π ℭ O hO) 0 := fun K => up π ℭ N O hO K (y K) with hy'
  have hd : (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).d (sliceCover π ℭ O hO) 0 y' = 0 := by
    funext K
    rw [hy', d_up, hy]
    exact map_zero _
  obtain ⟨x', hx', huniq⟩ :=
    (OModulePresheaf.d_zero_eq_zero_iff_existsUnique_of_isQuasicoherent (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)) hF' _ y').mp hd

  refine ⟨(FX).res (le_image_top O) (show (FX).obj (O.ι ''ᵁ ⊤) from x'), fun K => ?_, fun x₁ hx₁ => ?_⟩
  · rw [← down_up π ℭ N O hO K (y K), show up π ℭ N O hO K (y K) = y' K from rfl, hx' K, resO_eq]
    show (FX).res _ ((FX).res _ x') = (FX).res _ ((FX).res _ x')
    rw [OModulePresheaf.res_res, OModulePresheaf.res_res]
  · have h1 : (show (OModulePresheaf.ofModules (O.ι ≫ π) (N.restrict O.ι)).obj ⊤ from (FX).res (image_top_le O) x₁) = x' := by
      refine huniq _ fun K => ?_
      rw [show y' K = up π ℭ N O hO K (y K) from rfl, hx₁ K, resO_eq]
      show (FX).res _ ((FX).res _ x₁) = (FX).res _ ((FX).res _ x₁)
      rw [OModulePresheaf.res_res, OModulePresheaf.res_res]
    rw [← h1]
    show x₁ = (FX).res _ ((FX).res _ x₁)
    rw [OModulePresheaf.res_res]; exact (OModulePresheaf.res_refl_apply _ _ _).symm

end Slot

section Rows

variable (N : Z.Modules)

local notation "FX" => OModulePresheaf.ofModules π N
local notation "ℭf" => Scheme.OrderedAffineCover.toOpenFamily ℭ

noncomputable def toSlot {r m : ℕ} (c : OModulePresheaf.IterCech.C FX 𝔄 𝔅 ℭf r m) (pq : DoubleComplex.Diag m)
    (st : 𝔄.Idx pq.1.1 × 𝔅.Idx pq.1.2) (K : ℭ.Idx r) :
    (FX).obj ((𝔄.inter st.1 ⊓ 𝔅.inter st.2) ⊓ (ℭf).inter K) :=
  (FX).res (le_slot 𝔄 𝔅 ℭ st.1 st.2 K) (c K pq st)

theorem res_res_self' {O O' : Z.Opens} (h : O ≤ O') (h' : O' ≤ O) (y : (FX).obj O) :
    (FX).res h ((FX).res h' y) = y := by
  rw [OModulePresheaf.res_res]; exact OModulePresheaf.res_refl_apply _ _ _

theorem toSlot_dH {r m : ℕ} (c : OModulePresheaf.IterCech.C FX 𝔄 𝔅 ℭf r m) (pq : DoubleComplex.Diag m)
    (st : 𝔄.Idx pq.1.1 × 𝔅.Idx pq.1.2) (K : ℭ.Idx (r + 1)) :
    toSlot π 𝔄 𝔅 ℭ N (OModulePresheaf.IterCech.dH FX 𝔄 𝔅 ℭf r m c) pq st K
      = slotD π ℭ N (𝔄.inter st.1 ⊓ 𝔅.inter st.2) r (toSlot π 𝔄 𝔅 ℭ N c pq st) K := by
  rw [toSlot, OModulePresheaf.IterCech.dH_apply, Finset.sum_apply, Finset.sum_apply, map_sum, slotD]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, map_zsmul, OModulePresheaf.IterCech.resTot_apply, toSlot,
    OModulePresheaf.res_res, OModulePresheaf.res_res]

theorem res_toSlot {r m : ℕ} (c : OModulePresheaf.IterCech.C FX 𝔄 𝔅 ℭf r m) (pq : DoubleComplex.Diag m)
    (st : 𝔄.Idx pq.1.1 × 𝔅.Idx pq.1.2) (K : ℭ.Idx r) :
    (FX).res (slot_le 𝔄 𝔅 ℭ st.1 st.2 K) (toSlot π 𝔄 𝔅 ℭ N c pq st K) = c K pq st :=
  res_res_self' π N _ _ _

variable [IsSeparated π] (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)

include hN haff in

theorem rows_exact (r m : ℕ) :
    LinearMap.ker (OModulePresheaf.IterCech.dH FX 𝔄 𝔅 ℭf (r + 1) m)
      ≤ LinearMap.range (OModulePresheaf.IterCech.dH FX 𝔄 𝔅 ℭf r m) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc

  have hslot : ∀ (pq : DoubleComplex.Diag m) (st : 𝔄.Idx pq.1.1 × 𝔅.Idx pq.1.2) (K' : ℭ.Idx (r + 2)),
      slotD π ℭ N (𝔄.inter st.1 ⊓ 𝔅.inter st.2) (r + 1) (toSlot π 𝔄 𝔅 ℭ N c pq st) K' = 0 := by
    intro pq st K'
    rw [← toSlot_dH, hc]; exact map_zero _
  choose b hb using fun (pq : DoubleComplex.Diag m) (st : 𝔄.Idx pq.1.1 × 𝔅.Idx pq.1.2) =>
    slot_exact π ℭ N hN _ (isAffineOpen_slot π 𝔄 𝔅 haff st.1 st.2) r (toSlot π 𝔄 𝔅 ℭ N c pq st) (hslot pq st)
  refine ⟨fun K pq st => (FX).res (slot_le 𝔄 𝔅 ℭ st.1 st.2 K) (b pq st K), ?_⟩
  funext K pq st
  rw [← res_toSlot π 𝔄 𝔅 ℭ N (OModulePresheaf.IterCech.dH FX 𝔄 𝔅 ℭf r m _) pq st K, toSlot_dH,
    ← res_toSlot π 𝔄 𝔅 ℭ N c pq st K, hb pq st K]
  congr 1
  refine congrArg (fun y => slotD π ℭ N _ r y K) ?_
  funext K'
  exact res_res_self' π N _ _ _

include hN haff in

theorem ker_dH_zero_eq (m : ℕ) :
    LinearMap.ker (OModulePresheaf.IterCech.dH FX 𝔄 𝔅 ℭf 0 m)
      = LinearMap.range (OModulePresheaf.IterCech.augTot FX 𝔄 𝔅 ℭf m) := by
  refine le_antisymm ?_ ?_
  · intro c hc
    rw [LinearMap.mem_ker] at hc
    have hslot : ∀ (pq : DoubleComplex.Diag m) (st : 𝔄.Idx pq.1.1 × 𝔅.Idx pq.1.2) (K' : ℭ.Idx 1),
        slotD π ℭ N (𝔄.inter st.1 ⊓ 𝔅.inter st.2) 0 (toSlot π 𝔄 𝔅 ℭ N c pq st) K' = 0 := by
      intro pq st K'
      rw [← toSlot_dH, hc]; exact map_zero _
    choose a ha _ using fun (pq : DoubleComplex.Diag m) (st : 𝔄.Idx pq.1.1 × 𝔅.Idx pq.1.2) =>
      slot_exact_zero π ℭ N hN _ (isAffineOpen_slot π 𝔄 𝔅 haff st.1 st.2) (toSlot π 𝔄 𝔅 ℭ N c pq st) (hslot pq st)
    refine ⟨fun pq st => a pq st, ?_⟩
    funext K pq st
    rw [OModulePresheaf.IterCech.augTot_apply, OModulePresheaf.IterCech.resTot₀_apply,
      ← res_toSlot π 𝔄 𝔅 ℭ N c pq st K, ha pq st K, OModulePresheaf.res_res]
  · rintro c ⟨a, rfl⟩
    exact LinearMap.mem_ker.mpr (congrFun (congrArg DFunLike.coe
      (OModulePresheaf.IterCech.dH_comp_augTot FX 𝔄 𝔅 ℭf m)) a)

include hN haff in

theorem augTot_injective (m : ℕ) :
    Function.Injective (OModulePresheaf.IterCech.augTot FX 𝔄 𝔅 ℭf m) := by
  refine (LinearMap.ker_eq_bot.mp ((Submodule.eq_bot_iff _).mpr fun a ha => ?_))
  rw [LinearMap.mem_ker] at ha
  funext pq st
  have h0 : ∀ K' : ℭ.Idx 1, slotD π ℭ N (𝔄.inter st.1 ⊓ 𝔅.inter st.2) 0
      (fun K => (0 : (FX).obj ((𝔄.inter st.1 ⊓ 𝔅.inter st.2) ⊓ (ℭf).inter K))) K' = 0 := by
    intro K'; simp only [slotD, map_zero, smul_zero, Finset.sum_const_zero]
  obtain ⟨x, -, huniq⟩ := slot_exact_zero π ℭ N hN _ (isAffineOpen_slot π 𝔄 𝔅 haff st.1 st.2) _ h0
  have h1 : a pq st = x := huniq (a pq st) fun K => by
    have h := congrFun (congrFun (congrFun ha K) pq) st
    rw [OModulePresheaf.IterCech.augTot_apply, OModulePresheaf.IterCech.resTot₀_apply] at h
    show (0 : _) = (FX).res _ (a pq st)
    rw [← OModulePresheaf.res_res _ (le_slot 𝔄 𝔅 ℭ st.1 st.2 K)
      (inf_le_inf_left _ (le_trans (𝔅.restr_inter_le _ st.2) inf_le_left)) (a pq st), h]
    exact (map_zero _).symm
  have h2 : (0 : (FX).obj (𝔄.inter st.1 ⊓ 𝔅.inter st.2)) = x := huniq 0 fun K => by rw [map_zero]
  exact h1.trans h2.symm

end Rows

end G3Sol

open G3Sol in
theorem solution
    {R : Type u} [CommRing R] {Z : Scheme.{u}} (π : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (N : Z.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent)
    (𝔄 𝔅 : Z.OrderedOpenFamily) (haff : ∀ i j, IsAffineOpen (𝔄.U i ⊓ 𝔅.U j))
    (ℭ : Z.OrderedAffineCover) :
    (∀ m, Function.Injective
        (OModulePresheaf.IterCech.augTot (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily m)) ∧
      (∀ m, LinearMap.ker (OModulePresheaf.IterCech.dH (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily 0 m)
        = LinearMap.range (OModulePresheaf.IterCech.augTot (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily m)) ∧
      ∀ r m, LinearMap.ker (OModulePresheaf.IterCech.dH (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily (r + 1) m)
        ≤ LinearMap.range (OModulePresheaf.IterCech.dH (OModulePresheaf.ofModules π N) 𝔄 𝔅 ℭ.toOpenFamily r m) :=
  ⟨fun m => augTot_injective π 𝔄 𝔅 haff ℭ N hN m, fun m => ker_dH_zero_eq π 𝔄 𝔅 haff ℭ N hN m,
    fun r m => rows_exact π 𝔄 𝔅 haff ℭ N hN r m⟩

end S_AlgebraicGeometry_OModulePresheaf_iterCech_rows_exact_of_isQuasicoherent
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_iterCech_rows_exact_of_isQuasicoherent (solution)
