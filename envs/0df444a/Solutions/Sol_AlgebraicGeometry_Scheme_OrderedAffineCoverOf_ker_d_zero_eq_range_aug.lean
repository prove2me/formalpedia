-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/970da4d5-0c75-5747-a8a0-4c5d921153c3

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme Scheme.OrderedAffineCoverOf Scheme.OrderedAffineCoverOf.face Scheme.OrderedAffineCoverOf.moduleSections Scheme.OrderedAffineCoverOf.res_apply Scheme.OrderedAffineCoverOf.d_apply Scheme.OrderedAffineCoverOf.aug"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ Opens OrderedAffineCoverOf OrderedAffineCoverOf.face OrderedAffineCoverOf.moduleSections OrderedAffineCoverOf.res_apply OrderedAffineCoverOf.d_apply OrderedAffineCoverOf.aug"
namespace OrderedAffineCoverOf
p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCoverOf" "Idx inter face inter_le_base moduleSections cochain res_apply d d_apply aug U le iSup_eq ι"
namespace Acyclic
p2m_open "AlgebraicGeometry.Scheme.OrderedAffineCoverOf AlgebraicGeometry.Scheme AlgebraicGeometry"

universe u
section AltImg

variable {V : Scheme.{u}} {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W)

abbrev altImg {i : ℕ} (s : K.Idx i) : Finset K.ι :=
  Finset.univ.image s.1

theorem card_altImg {i : ℕ} (s : K.Idx i) :
    (altImg K s).card = i + 1 := by
  rw [Finset.card_image_of_injective _ s.2.injective, Finset.card_univ, Fintype.card_fin]

theorem altIdx_canonical {i : ℕ} (s : K.Idx i) :
    s.1 = (altImg K s).orderEmbOfFin (card_altImg K s) :=
  Finset.orderEmbOfFin_unique _ (fun k => Finset.mem_image_of_mem _ (Finset.mem_univ k)) s.2

theorem altIdx_eq_of_altImg {i : ℕ} {s t : K.Idx i}
    (h : altImg K s = altImg K t) : s = t := by
  apply Subtype.ext
  rw [altIdx_canonical K s]
  exact (Finset.orderEmbOfFin_unique (card_altImg K s)
    (fun k => h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ k)) t.2).symm

theorem altOpen_eq_biInf {i : ℕ} (s : K.Idx i) :
    K.inter s = ⨅ j ∈ altImg K s, K.U j := by
  refine le_antisymm (le_iInf₂ fun j hj => ?_) (le_iInf fun k => biInf_le _
    (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hj
  exact iInf_le _ k

theorem altImg_altFace {i : ℕ} (s : K.Idx (i + 1))
    (j : Fin (i + 2)) :
    altImg K (K.face s j)
      = (altImg K s).erase (s.1 j) := by
  ext x
  simp only [altImg, Scheme.OrderedAffineCoverOf.face, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_erase, Function.comp_apply]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨s.2.injective.ne (Fin.succAbove_ne j k), Fin.succAbove j k, rfl⟩
  · rintro ⟨hne, k, rfl⟩
    obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq (fun h => hne (congrArg s.1 h))
    exact ⟨k', rfl⟩

def altOfFinset {i : ℕ} (T : Finset K.ι) (hT : T.card = i + 1) :
    K.Idx i :=
  ⟨T.orderEmbOfFin hT, (T.orderEmbOfFin hT).strictMono⟩

theorem altImg_altOfFinset {i : ℕ} (T : Finset K.ι) (hT : T.card = i + 1) :
    altImg K (altOfFinset K T hT) = T :=
  Finset.image_orderEmbOfFin_univ T hT

theorem altImg_deg0 (σ : K.Idx 0) :
    altImg K σ = {σ.1 0} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ 0), fun x hx => ?_⟩
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx; rw [← hj, Fin.fin_one_eq_zero j]

def altPos {i : ℕ} (s : K.Idx i) (j : K.ι)
    (hj : j ∈ altImg K s) : Fin (i + 1) :=
  ((altImg K s).orderIsoOfFin (card_altImg K s)).symm ⟨j, hj⟩

theorem altIdx_val_altPos {i : ℕ} (s : K.Idx i)
    (j : K.ι) (hj : j ∈ altImg K s) :
    s.1 (altPos K s j hj) = j := by
  rw [altIdx_canonical K s, ← Finset.coe_orderIsoOfFin_apply,
    altPos, OrderIso.apply_symm_apply]

theorem altPos_val {i : ℕ} (s : K.Idx i) (p : Fin (i + 1)) :
    altPos K s (s.1 p) (Finset.mem_image_of_mem _ (Finset.mem_univ p)) = p :=
  s.2.injective (altIdx_val_altPos K s (s.1 p) _)

def altInsert {i : ℕ} (s : K.Idx i) (j : K.ι)
    (hj : j ∉ altImg K s) : K.Idx (i + 1) :=
  altOfFinset K (insert j (altImg K s))
    (by rw [Finset.card_insert_of_notMem hj, card_altImg])

theorem altImg_altInsert {i : ℕ} (s : K.Idx i)
    (j : K.ι) (hj : j ∉ altImg K s) :
    altImg K (altInsert K s j hj)
      = insert j (altImg K s) :=
  altImg_altOfFinset K _ _

def insPos {i : ℕ} (s : K.Idx i) (j : K.ι)
    (hj : j ∉ altImg K s) : Fin (i + 2) :=
  altPos K (altInsert K s j hj) j
    (by rw [altImg_altInsert]; exact Finset.mem_insert_self j _)

theorem altInsert_val_insPos {i : ℕ} (s : K.Idx i)
    (j : K.ι) (hj : j ∉ altImg K s) :
    (altInsert K s j hj).1 (insPos K s j hj) = j :=
  altIdx_val_altPos K _ j _

theorem altFace_altInsert_insPos {i : ℕ} (s : K.Idx i)
    (j : K.ι) (hj : j ∉ altImg K s) :
    K.face (altInsert K s j hj)
      (insPos K s j hj) = s := by
  apply altIdx_eq_of_altImg
  rw [altImg_altFace, altInsert_val_insPos,
    altImg_altInsert, Finset.erase_insert hj]

theorem altPos_congr {i : ℕ} {s t : K.Idx i}
    (h : s = t) (j : K.ι) (hjs : j ∈ altImg K s)
    (hjt : j ∈ altImg K t) :
    altPos K s j hjs = altPos K t j hjt := by
  subst h; rfl

theorem altInsert_altFace_altPos {i : ℕ} (σ : K.Idx (i + 1))
    (j : K.ι) (hj : j ∈ altImg K σ)
    (hjp : j ∉ altImg K
      (K.face σ (altPos K σ j hj))) :
    altInsert K (K.face σ (altPos K σ j hj))
      j hjp = σ := by
  apply altIdx_eq_of_altImg
  rw [altImg_altInsert, altImg_altFace,
    altIdx_val_altPos, Finset.insert_erase hj]

theorem insPos_altFace_altPos {i : ℕ} (σ : K.Idx (i + 1))
    (j : K.ι) (hj : j ∈ altImg K σ)
    (hjp : j ∉ altImg K
      (K.face σ (altPos K σ j hj))) :
    insPos K (K.face σ (altPos K σ j hj)) j hjp
      = altPos K σ j hj := by
  unfold insPos
  exact altPos_congr K
    (altInsert_altFace_altPos K σ j hj hjp) j _ hj

theorem altFace_altInsert_ne {i : ℕ} (s : K.Idx (i + 1))
    (j : K.ι) (hj : j ∉ altImg K s)
    (k : Fin (i + 3)) (hk : k ≠ insPos K s j hj) :
    ∃ (p : Fin (i + 2)) (hjp : j ∉ altImg K (K.face s p)),
      K.face (altInsert K s j hj) k
        = altInsert K (K.face s p) j hjp
      ∧ (altInsert K s j hj).1 k = s.1 p := by
  set m := (altInsert K s j hj).1 k with hm_def
  have hmne : m ≠ j := fun heq => hk ((altInsert K s j hj).2.injective
    (heq.trans (altInsert_val_insPos K s j hj).symm))
  have hmem : m ∈ altImg K s := by
    have : m ∈ altImg K (altInsert K s j hj) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ k)
    rw [altImg_altInsert] at this
    exact (Finset.mem_insert.mp this).resolve_left hmne
  refine ⟨altPos K s m hmem, ?_, ?_, ?_⟩
  · rw [altImg_altFace, altIdx_val_altPos]
    exact fun h => hj (Finset.mem_of_mem_erase h)
  · apply altIdx_eq_of_altImg
    rw [altImg_altFace, altImg_altInsert,
      altImg_altInsert, altImg_altFace,
      altIdx_val_altPos, Finset.erase_insert_of_ne hmne.symm]
  · exact (altIdx_val_altPos K s m hmem).symm

end AltImg

section ResHelpers

variable {V : Scheme.{u}}

theorem res_refl {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) :
    (V.presheaf.map (homOfLE h).op).hom x = x := by
  have : (homOfLE h : O ⟶ O) = 𝟙 O := rfl
  rw [this, op_id, V.presheaf.map_id]; rfl

theorem res_res {O₁ O₂ O₃ : V.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃)
    (x : Γ(V, O₃)) :
    (V.presheaf.map (homOfLE h12).op).hom ((V.presheaf.map (homOfLE h23).op).hom x)
      = (V.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem altC_at_eq {W : V.Opens} {K : Scheme.OrderedAffineCoverOf W}
    {n : ℕ} (z : K.cochain n) {σ τ : K.Idx n} (h : σ = τ)
    {O : V.Opens} (hσ : O ≤ K.inter σ) (hτ : O ≤ K.inter τ) :
    (V.presheaf.map (homOfLE hσ).op).hom (z σ)
      = (V.presheaf.map (homOfLE hτ).op).hom (z τ) := by
  subst h; rfl

end ResHelpers

section Idx0
variable {V : Scheme.{u}} {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W) (i₀ : K.ι)

def idx0 : K.Idx 0 :=
  ⟨fun _ => i₀, fun a b h => absurd (Subsingleton.elim (α := Fin 1) a b) (ne_of_lt h)⟩
end Idx0

section Acyclic0

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
variable {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W)
include π

theorem affine_acyclic₀ :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    LinearMap.ker (K.d π 0) = LinearMap.range (K.aug π) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  refine le_antisymm (fun z hz => ?_) ?_
  ·
    have hcov : W ≤ ⨆ σ : K.Idx 0, K.inter σ := by
      refine K.iSup_eq.ge.trans (iSup_le fun i => ?_)
      exact le_iSup_of_le (idx0 K i) (le_iInf fun _ => le_rfl)

    have hcore : ∀ (a b : K.ι), a < b → ∀ (σ τ : K.Idx 0),
        σ.1 0 = a → τ.1 0 = b → ∀ {O : V.Opens}
        (hOσ : O ≤ K.inter σ) (hOτ : O ≤ K.inter τ),
        O ≤ K.U a ⊓ K.U b →
        (V.presheaf.map (homOfLE hOσ).op).hom (z σ)
          = (V.presheaf.map (homOfLE hOτ).op).hom (z τ) := by
      intro a b hab σ τ hσ hτ O hOσ hOτ hOab
      let ρ : K.Idx 1 := ⟨![a, b], by
        intro c d hcd; fin_cases c <;> fin_cases d <;> simp_all⟩
      have hρ0 : K.face ρ 0 = τ := altIdx_eq_of_altImg K
        (by rw [altImg_deg0, altImg_deg0, hτ]; rfl)
      have hρ1 : K.face ρ 1 = σ := altIdx_eq_of_altImg K
        (by rw [altImg_deg0, altImg_deg0, hσ]; rfl)
      have hOρ : O ≤ K.inter ρ :=
        le_iInf fun j => by fin_cases j
                            · exact hOab.trans inf_le_left
                            · exact hOab.trans inf_le_right
      have hker := congrFun (LinearMap.mem_ker.mp hz) ρ
      rw [Scheme.OrderedAffineCoverOf.d_apply, Fin.sum_univ_two] at hker
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
        Pi.zero_apply, add_neg_eq_zero] at hker
      have key := congrArg (V.presheaf.map (homOfLE hOρ).op).hom hker
      rw [res_res, res_res,
        altC_at_eq z hρ0 _ hOτ,
        altC_at_eq z hρ1 _ hOσ] at key
      exact key.symm
    have hcompat : TopCat.Presheaf.IsCompatible V.sheaf.1
        (K.inter (i := 0)) z := by
      intro σ τ
      have hOab : K.inter σ ⊓ K.inter τ
          ≤ K.U (σ.1 0) ⊓ K.U (τ.1 0) :=
        inf_le_inf (iInf_le _ 0) (iInf_le _ 0)
      rcases lt_trichotomy (σ.1 0) (τ.1 0) with h | h | h
      · exact hcore _ _ h σ τ rfl rfl inf_le_left inf_le_right hOab
      · have heq : σ = τ := altIdx_eq_of_altImg K
          (by rw [altImg_deg0, altImg_deg0, h])
        subst heq; rfl
      · exact (hcore _ _ h τ σ rfl rfl inf_le_right inf_le_left
          (hOab.trans (inf_comm _ _).le)).symm
    obtain ⟨w, hw, -⟩ := V.sheaf.existsUnique_gluing' (K.inter (i := 0)) W
      (fun σ => homOfLE (K.inter_le_base σ)) hcov z hcompat
    exact ⟨w, funext fun σ => hw σ⟩
  ·
    rintro _ ⟨w, rfl⟩
    refine LinearMap.mem_ker.mpr (funext fun τ => ?_)
    rw [Scheme.OrderedAffineCoverOf.d_apply, Fin.sum_univ_two]
    simp only [Scheme.OrderedAffineCoverOf.aug, LinearMap.pi_apply, Scheme.OrderedAffineCoverOf.res_apply,
      res_res, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
      neg_one_smul, Pi.zero_apply, add_neg_cancel]

end Acyclic0

end AlgebraicGeometry.Scheme.OrderedAffineCoverOf.Acyclic

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {W : V.Opens}
    (K : V.OrderedAffineCoverOf W) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    LinearMap.ker (K.d π 0) = LinearMap.range (K.aug π) :=
  Scheme.OrderedAffineCoverOf.Acyclic.affine_acyclic₀ π K

end S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug (solution)
