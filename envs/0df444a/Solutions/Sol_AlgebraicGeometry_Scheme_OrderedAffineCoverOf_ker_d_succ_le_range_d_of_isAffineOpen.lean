-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9392061d-8735-51a5-89e5-9604b290040d

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Spec Scheme IsSeparated IsAffineOpen Scheme.OrderedAffineCoverOf Scheme.OrderedAffineCoverOf.Idx Scheme.OrderedAffineCoverOf.inter Scheme.OrderedAffineCoverOf.face Scheme.OrderedAffineCoverOf.moduleSections Scheme.OrderedAffineCoverOf.cochain Scheme.OrderedAffineCoverOf.res Scheme.OrderedAffineCoverOf.res_apply Scheme.OrderedAffineCoverOf.d Scheme.OrderedAffineCoverOf.d_apply Scheme.OrderedAffineCoverOf.aug Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated Scheme.OrderedAffineCover"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "basicOpen_res Γ basicOpen Opens basicOpen_le restrict OrderedAffineCoverOf OrderedAffineCoverOf.Idx OrderedAffineCoverOf.inter OrderedAffineCoverOf.face OrderedAffineCoverOf.moduleSections OrderedAffineCoverOf.cochain OrderedAffineCoverOf.res OrderedAffineCoverOf.res_apply OrderedAffineCoverOf.d OrderedAffineCoverOf.d_apply OrderedAffineCoverOf.aug OrderedAffineCover.isAffineOpen_inf_of_isSeparated OrderedAffineCover"
namespace OrderedAffineCoverOf
p2m_export "AlgebraicGeometry.Scheme.OrderedAffineCoverOf" "Idx inter face inter_le_inter_face inter_le_base moduleSections cochain res res_apply d d_apply aug isAffineOpen U le iSup_eq ι"
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

section WholeSpace

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
variable {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W) (i₀ : K.ι) (hi₀ : K.U i₀ = W)
include hi₀

theorem altOpen_altInsert {i : ℕ} (s : K.Idx i)
    (hj : i₀ ∉ altImg K s) :
    K.inter (altInsert K s i₀ hj)
      = K.inter s := by
  refine le_antisymm ?_ (le_iInf fun k => ?_)
  · have := K.inter_le_inter_face (altInsert K s i₀ hj)
      (insPos K s i₀ hj)
    rwa [altFace_altInsert_insPos] at this
  · by_cases hk : k = insPos K s i₀ hj
    · rw [hk, altInsert_val_insPos, hi₀]
      exact K.inter_le_base s
    · have hmem : (altInsert K s i₀ hj).1 k ∈ altImg K s := by
        have h1 : (altInsert K s i₀ hj).1 k
            ∈ altImg K (altInsert K s i₀ hj) :=
          Finset.mem_image_of_mem _ (Finset.mem_univ k)
        rw [altImg_altInsert] at h1
        refine (Finset.mem_insert.mp h1).resolve_left fun heq => hk ?_
        exact (altInsert K s i₀ hj).2.injective
          (heq.trans (altInsert_val_insPos K s i₀ hj).symm)
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hmem
      rw [← hp]; exact iInf_le _ p

def htpy (i : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    K.cochain (i + 1) →ₗ[R] K.cochain i :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  LinearMap.pi fun σ =>
    if hσ : i₀ ∈ altImg K σ then 0
    else ((-1 : ℤ) ^ ((insPos K σ i₀ hσ : ℕ))) •
      ((Scheme.OrderedAffineCoverOf.res π
        (ge_of_eq (altOpen_altInsert K i₀ hi₀ σ hσ))).comp
        (LinearMap.proj (R := R) (altInsert K σ i₀ hσ)))

theorem htpy_apply (i : ℕ) (z : K.cochain (i + 1))
    (σ : K.Idx i) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    htpy π K i₀ hi₀ i z σ =
      if hσ : i₀ ∈ altImg K σ then 0
      else ((-1 : ℤ) ^ ((insPos K σ i₀ hσ : ℕ))) •
        (V.presheaf.map (homOfLE (ge_of_eq
          (altOpen_altInsert K i₀ hi₀ σ hσ))).op).hom
          (z (altInsert K σ i₀ hσ)) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  simp only [htpy, LinearMap.pi_apply]
  split_ifs with h
  · rfl
  · simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Scheme.OrderedAffineCoverOf.res_apply]

omit hi₀ in

theorem notMem_altImg_altFace {i : ℕ} (σ : K.Idx (i + 1))
    (hσ : i₀ ∉ altImg K σ) (p : Fin (i + 2)) :
    i₀ ∉ altImg K (K.face σ p) := by
  rw [altImg_altFace]; exact fun h => hσ (Finset.mem_of_mem_erase h)

omit hi₀ in

theorem sign_rel {i : ℕ} (σ : K.Idx (i + 1))
    (hσ : i₀ ∉ altImg K σ) (p : Fin (i + 2)) :
    K.face (altInsert K σ i₀ hσ)
        ((insPos K σ i₀ hσ).succAbove p)
      = altInsert K (K.face σ p) i₀
          (notMem_altImg_altFace K i₀ σ hσ p)
    ∧ (insPos K σ i₀ hσ : ℕ)
        + ((insPos K σ i₀ hσ).succAbove p : ℕ)
      = (p : ℕ) + (insPos K (K.face σ p) i₀
          (notMem_altImg_altFace K i₀ σ hσ p) : ℕ) + 1 := by
  have hjp := notMem_altImg_altFace K i₀ σ hσ p

  have hval : (altInsert K σ i₀ hσ).1
      ((insPos K σ i₀ hσ).succAbove p) = σ.1 p :=
    congrFun (congrArg Subtype.val (altFace_altInsert_insPos K σ i₀ hσ)) p

  have heq : K.face (altInsert K σ i₀ hσ)
        ((insPos K σ i₀ hσ).succAbove p)
      = altInsert K (K.face σ p) i₀ hjp := by
    apply altIdx_eq_of_altImg
    rw [altImg_altFace, altImg_altInsert,
      altImg_altInsert, altImg_altFace, hval,
      Finset.erase_insert_of_ne
        (fun h => hσ (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, h.symm⟩))]
  refine ⟨heq, ?_⟩

  have hq_eq : (insPos K σ i₀ hσ : Fin _)
      = ((insPos K σ i₀ hσ).succAbove p).succAbove
          (insPos K (K.face σ p) i₀ hjp) := by
    refine (altInsert K σ i₀ hσ).2.injective ?_
    have step : (altInsert K σ i₀ hσ).1
        (((insPos K σ i₀ hσ).succAbove p).succAbove
          (insPos K (K.face σ p) i₀ hjp))
        = (altInsert K (K.face σ p) i₀ hjp).1
            (insPos K (K.face σ p) i₀ hjp) :=
      congrFun (congrArg Subtype.val heq) _
    rw [altInsert_val_insPos K σ i₀ hσ, step,
      altInsert_val_insPos]

  set q := insPos K σ i₀ hσ
  set q' := insPos K (K.face σ p) i₀ hjp
  have hcast : ∀ {n} (a : Fin n), (a.castSucc : ℕ) = (a : ℕ) := fun _ => rfl
  rcases lt_or_ge p.castSucc q with hpq | hpq
  · have hkp : (q.succAbove p : ℕ) = (p : ℕ) := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hpq, hcast]
    have hpqN : (p : ℕ) < (q : ℕ) := by have := hpq; rwa [Fin.lt_def, hcast] at this
    have hqq' : (q : ℕ) = (q' : ℕ) + 1 := by
      rcases lt_or_ge q'.castSucc (q.succAbove p) with h | h
      · exfalso
        have hN : (q' : ℕ) < (q.succAbove p : ℕ) := by rwa [Fin.lt_def, hcast] at h
        have : (q : ℕ) = (q' : ℕ) := by
          rw [show (q:ℕ) = ((q.succAbove p).succAbove q':ℕ) from congrArg Fin.val hq_eq,
            Fin.succAbove_of_castSucc_lt _ _ h, hcast]
        omega
      · rw [show (q:ℕ) = ((q.succAbove p).succAbove q':ℕ) from congrArg Fin.val hq_eq,
          Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
    omega
  · have hkp : (q.succAbove p : ℕ) = (p : ℕ) + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ hpq, Fin.val_succ]
    have hpqN : (q : ℕ) ≤ (p : ℕ) := by have := hpq; rwa [Fin.le_def, hcast] at this
    have hqq' : (q : ℕ) = (q' : ℕ) := by
      rcases lt_or_ge q'.castSucc (q.succAbove p) with h | h
      · rw [show (q:ℕ) = ((q.succAbove p).succAbove q':ℕ) from congrArg Fin.val hq_eq,
          Fin.succAbove_of_castSucc_lt _ _ h, hcast]
      · exfalso
        have hN : (q.succAbove p : ℕ) ≤ (q' : ℕ) := by rwa [Fin.le_def, hcast] at h
        have : (q : ℕ) = (q' : ℕ) + 1 := by
          rw [show (q:ℕ) = ((q.succAbove p).succAbove q':ℕ) from congrArg Fin.val hq_eq,
            Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
        omega
    omega

theorem htpy_rel (i : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    K.d π i ∘ₗ htpy π K i₀ hi₀ i
      + htpy π K i₀ hi₀ (i + 1) ∘ₗ K.d π (i + 1)
      = LinearMap.id := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  refine LinearMap.ext fun z => funext fun σ => ?_
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, Pi.add_apply]
  by_cases hσ : i₀ ∈ altImg K σ
  ·
    rw [htpy_apply π K i₀ hi₀, dif_pos hσ, add_zero,
      Scheme.OrderedAffineCoverOf.d_apply]
    set p₀ := altPos K σ i₀ hσ with hp₀
    have hjp₀ : i₀ ∉ altImg K (K.face σ p₀) := by
      rw [altImg_altFace, hp₀, altIdx_val_altPos]
      exact Finset.notMem_erase _ _
    rw [Finset.sum_eq_single p₀]
    · rw [htpy_apply π K i₀ hi₀, dif_neg hjp₀,
        insPos_altFace_altPos K σ i₀ hσ hjp₀, map_zsmul, smul_smul,
        ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul,
        res_res,
        altC_at_eq z (altInsert_altFace_altPos K σ i₀ hσ hjp₀)
          _ le_rfl,
        res_refl]
    · intro j _ hj
      have hjmem : i₀ ∈ altImg K (K.face σ j) := by
        rw [altImg_altFace]
        refine Finset.mem_erase.mpr ⟨fun heq => hj ?_, hσ⟩
        have h1 : σ.1 j = σ.1 p₀ :=
          heq.symm.trans (altIdx_val_altPos K σ i₀ hσ).symm
        exact σ.2.injective h1
      rw [htpy_apply π K i₀ hi₀, dif_pos hjmem, map_zero, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  ·
    rw [htpy_apply π K i₀ hi₀, dif_neg hσ,
      Scheme.OrderedAffineCoverOf.d_apply π K (i + 1) z,
      Fin.sum_univ_succAbove _ (insPos K σ i₀ hσ), map_add, smul_add,
      map_zsmul, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul,
      res_res,
      altC_at_eq z (altFace_altInsert_insPos K σ i₀ hσ) _ le_rfl,
      res_refl, map_sum, Finset.smul_sum,
      Scheme.OrderedAffineCoverOf.d_apply π K i,
      add_comm (z σ), ← add_assoc, add_eq_right, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun p _ => ?_
    have hjp := notMem_altImg_altFace K i₀ σ hσ p
    obtain ⟨heq, hparity⟩ := sign_rel K i₀ σ hσ p
    rw [htpy_apply π K i₀ hi₀, dif_neg hjp,
      map_zsmul, smul_smul, ← pow_add, res_res,
      map_zsmul, smul_smul, ← pow_add, res_res,
      altC_at_eq z heq _
        ((K.inter_le_inter_face σ p).trans
          (ge_of_eq (altOpen_altInsert K i₀ hi₀ _ hjp))),
      hparity, pow_succ, mul_neg_one, neg_smul, add_neg_cancel]

omit hi₀ in

def idx0 : K.Idx 0 :=
  ⟨fun _ => i₀, fun a b h => absurd (Subsingleton.elim (α := Fin 1) a b) (ne_of_lt h)⟩

theorem altOpen_idx0 :
    K.inter (idx0 K i₀) = W := by
  refine le_antisymm ((iInf_le _ 0).trans (le_of_eq hi₀)) (le_iInf fun j => ge_of_eq hi₀)

def hAug :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    K.cochain 0 →ₗ[R] Γ(V, W) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  (Scheme.OrderedAffineCoverOf.res π (altOpen_idx0 K i₀ hi₀).ge).comp
    (LinearMap.proj (idx0 K i₀))

theorem htpy_rel₀ :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    (htpy π K i₀ hi₀ 0 ∘ₗ K.d π 0
        + K.aug π ∘ₗ hAug π K i₀ hi₀ = LinearMap.id)
      ∧ hAug π K i₀ hi₀ ∘ₗ K.aug π = LinearMap.id := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  have hone : ∀ (a : Fin 2), (a : ℕ) + ((a.succAbove 0 : Fin 2) : ℕ) = 1 := by decide
  have hle_idx0 : ∀ (σ : K.Idx 0),
      K.inter σ ≤ K.inter (idx0 K i₀) :=
    fun σ => (K.inter_le_base σ).trans (altOpen_idx0 K i₀ hi₀).ge
  refine ⟨LinearMap.ext fun z => funext fun σ => ?_, LinearMap.ext fun w => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, Pi.add_apply,
      Scheme.OrderedAffineCoverOf.aug, hAug, LinearMap.pi_apply, LinearMap.proj_apply,
      Scheme.OrderedAffineCoverOf.res_apply, res_res]
    by_cases hσ : i₀ ∈ altImg K σ
    ·
      have hσ0 : σ.1 0 = i₀ := by
        obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hσ; rwa [Fin.fin_one_eq_zero j] at hj
      have hσeq : σ = idx0 K i₀ :=
        Subtype.ext (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact hσ0)
      rw [htpy_apply, dif_pos hσ, zero_add,
        altC_at_eq z hσeq.symm (hle_idx0 σ) le_rfl, res_refl]
    ·
      rw [htpy_apply, dif_neg hσ, Scheme.OrderedAffineCoverOf.d_apply,
        Fin.sum_univ_succAbove _ (insPos K σ i₀ hσ), Fin.sum_univ_one,
        map_add, smul_add, map_zsmul, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul,
        res_res,
        altC_at_eq z (altFace_altInsert_insPos K σ i₀ hσ) _ le_rfl,
        res_refl,
        map_zsmul, smul_smul, ← pow_add, hone, pow_one, neg_one_smul,
        res_res]

      have hne : i₀ ≠ σ.1 0 := fun h =>
        hσ (altImg_deg0 K σ ▸ Finset.mem_singleton.mpr h)
      have hface0 : K.face (altInsert K σ i₀ hσ)
          ((insPos K σ i₀ hσ).succAbove 0) = idx0 K i₀ := by
        apply altIdx_eq_of_altImg
        have hval0 : (altInsert K σ i₀ hσ).1
            ((insPos K σ i₀ hσ).succAbove 0) = σ.1 0 :=
          congrFun (congrArg Subtype.val
            (altFace_altInsert_insPos K σ i₀ hσ)) 0
        rw [altImg_altFace, altImg_altInsert, hval0,
          altImg_deg0, altImg_deg0,
          Finset.erase_insert_of_ne hne]
        simp only [Finset.erase_singleton, if_pos rfl, Finset.insert_empty]
        rfl
      rw [altC_at_eq z hface0 _ (hle_idx0 σ)]
      abel
  · simp only [LinearMap.comp_apply, LinearMap.id_apply, hAug,
      Scheme.OrderedAffineCoverOf.aug, LinearMap.pi_apply, LinearMap.proj_apply,
      Scheme.OrderedAffineCoverOf.res_apply, res_res, res_refl]

theorem wholeSpace_exact (i : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    LinearMap.ker (K.d π (i + 1))
      ≤ LinearMap.range (K.d π i) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  intro z hz
  have key := htpy_rel π K i₀ hi₀ i
  have : z = K.d π i (htpy π K i₀ hi₀ i z) := by
    have := LinearMap.congr_fun key z
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.mem_ker.mp hz, map_zero, add_zero] at this
    exact this.symm
  exact ⟨_, this.symm⟩

theorem wholeSpace_exact₀ :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    LinearMap.ker (K.d π 0) = LinearMap.range (K.aug π) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  obtain ⟨hrel, hid⟩ := htpy_rel₀ π K i₀ hi₀
  refine le_antisymm (fun z hz => ?_) ?_
  · have := LinearMap.congr_fun hrel z
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearMap.mem_ker.mp hz, map_zero, zero_add] at this
    exact ⟨_, this⟩
  · rintro _ ⟨w, rfl⟩
    refine LinearMap.mem_ker.mpr (funext fun τ => ?_)
    rw [Scheme.OrderedAffineCoverOf.d_apply, Fin.sum_univ_two]
    simp only [Scheme.OrderedAffineCoverOf.aug, LinearMap.pi_apply, Scheme.OrderedAffineCoverOf.res_apply,
      res_res, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
      neg_one_smul, Pi.zero_apply, add_neg_cancel]

end WholeSpace

section AffineAcyclic

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
variable [IsSeparated π] {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W)
include π

theorem isAffineOpen_altOpen :
    ∀ {i : ℕ} (σ : K.Idx i),
      IsAffineOpen (K.inter σ) := by
  intro i
  induction i with
  | zero =>
    intro σ
    have heq : K.inter σ = K.U (σ.1 0) :=
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by rw [Fin.fin_one_eq_zero j])
    exact heq ▸ K.isAffineOpen _
  | succ n ih =>
    intro σ
    have heq : K.inter σ
        = K.U (σ.1 0) ⊓ K.inter (K.face σ 0) := by
      refine le_antisymm (le_inf (iInf_le _ 0) (K.inter_le_inter_face σ 0))
        (le_iInf fun j => ?_)
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · exact inf_le_left
      · exact inf_le_right.trans (iInf_le _ k)
    exact heq ▸ Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π (K.isAffineOpen _) (ih _)

omit π in

@[reducible] noncomputable def moduleW_altC (i : ℕ) :
    Module Γ(V, W) (K.cochain i) :=
  @Pi.module _ _ _ _ _ (fun σ =>
    ((V.presheaf.map (homOfLE (K.inter_le_base σ)).op).hom).toModule)

omit π in
theorem smulW_apply {i : ℕ} (a : Γ(V, W)) (x : K.cochain i)
    (σ : K.Idx i) :
    letI := moduleW_altC K i
    (a • x) σ = (V.presheaf.map (homOfLE (K.inter_le_base σ)).op).hom a * x σ :=
  rfl

theorem altd_smulW (i : ℕ) (a : Γ(V, W)) (x : K.cochain i) :
    letI := moduleW_altC K i
    letI := moduleW_altC K (i + 1)
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    K.d π i (a • x) = a • K.d π i x := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  funext τ
  rw [Scheme.OrderedAffineCoverOf.d_apply, smulW_apply, Scheme.OrderedAffineCoverOf.d_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smulW_apply, map_mul, res_res, mul_smul_comm]

noncomputable def rangeW (p : ℕ) :
    letI := moduleW_altC K (p + 1)
    Submodule Γ(V, W) (K.cochain (p + 1)) :=
  letI := moduleW_altC K (p + 1)
  letI := moduleW_altC K p
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  { carrier := Set.range (K.d π p)
    add_mem' := fun ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ => ⟨w₁ + w₂, by rw [map_add, h₁, h₂]⟩
    zero_mem' := ⟨0, map_zero _⟩
    smul_mem' := fun a _ ⟨w, hw⟩ =>
      ⟨a • w, (altd_smulW π K p a w).trans (congrArg (a • ·) hw)⟩ }

noncomputable def restrictBasic (hW : IsAffineOpen W) (f : Γ(V, W)) :
    Scheme.OrderedAffineCoverOf (V.basicOpen f) :=
  { ι := K.ι
    U := fun i => K.U i ⊓ V.basicOpen f
    isAffineOpen := fun i => Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π (K.isAffineOpen i) (hW.basicOpen f)
    le := fun _ => inf_le_right
    iSup_eq := by rw [← iSup_inf_eq, K.iSup_eq]; exact inf_of_le_right (V.basicOpen_le f) }

theorem altOpen_restrictBasic (hW : IsAffineOpen W) (f : Γ(V, W))
    {i : ℕ} (σ : Scheme.OrderedAffineCoverOf.Idx (restrictBasic π K hW f) i) :
    Scheme.OrderedAffineCoverOf.inter (restrictBasic π K hW f) σ
      = K.inter σ ⊓ V.basicOpen f := by
  refine le_antisymm (le_inf (le_iInf fun j => (iInf_le _ j).trans inf_le_left)
    ((iInf_le _ 0).trans inf_le_right)) (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

theorem altOpen_restrictBasic_le (hW : IsAffineOpen W) (f : Γ(V, W))
    {i : ℕ} (σ : Scheme.OrderedAffineCoverOf.Idx (restrictBasic π K hW f) i) :
    Scheme.OrderedAffineCoverOf.inter (restrictBasic π K hW f) σ
      ≤ K.inter σ :=
  (altOpen_restrictBasic π K hW f σ).le.trans inf_le_left

noncomputable def resBasic (hW : IsAffineOpen W) (f : Γ(V, W)) (q : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    K.cochain q
      →ₗ[R] Scheme.OrderedAffineCoverOf.cochain (restrictBasic π K hW f) q :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  LinearMap.pi fun σ =>
    (Scheme.OrderedAffineCoverOf.res π (altOpen_restrictBasic_le π K hW f σ)).comp
      (LinearMap.proj σ)

theorem resBasic_apply (hW : IsAffineOpen W) (f : Γ(V, W)) (q : ℕ)
    (x : K.cochain q)
    (σ : Scheme.OrderedAffineCoverOf.Idx (restrictBasic π K hW f) q) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    resBasic π K hW f q x σ
      = (V.presheaf.map (homOfLE
          (altOpen_restrictBasic_le π K hW f σ)).op).hom (x σ) := by
  simp only [resBasic, LinearMap.pi_apply, LinearMap.comp_apply,
    Scheme.OrderedAffineCoverOf.res_apply]
  rfl

theorem altd_resBasic (hW : IsAffineOpen W) (f : Γ(V, W)) (q : ℕ)
    (x : K.cochain q) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    Scheme.OrderedAffineCoverOf.d π (restrictBasic π K hW f) q
        (resBasic π K hW f q x)
      = resBasic π K hW f (q + 1) (K.d π q x) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  funext τ
  rw [Scheme.OrderedAffineCoverOf.d_apply, resBasic_apply, Scheme.OrderedAffineCoverOf.d_apply,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [resBasic_apply, map_zsmul, res_res,
    res_res]
  rfl

theorem away_surj (hW : IsAffineOpen W) (f : Γ(V, W))
    {q : ℕ} (σ : Scheme.OrderedAffineCoverOf.Idx (restrictBasic π K hW f) q)
    (y : Γ(V, Scheme.OrderedAffineCoverOf.inter (restrictBasic π K hW f) σ)) :
    ∃ (n : ℕ) (a : Γ(V, K.inter σ)),
      (V.presheaf.map (homOfLE
          (altOpen_restrictBasic_le π K hW f σ)).op).hom a
        = (V.presheaf.map (homOfLE
            (((altOpen_restrictBasic π K hW f σ).le.trans inf_le_right).trans
              (V.basicOpen_le f))).op).hom f ^ n * y := by
  set g : Γ(V, K.inter σ) :=
    (V.presheaf.map (homOfLE (K.inter_le_base σ)).op).hom f
  have hDg : V.basicOpen g = Scheme.OrderedAffineCoverOf.inter (restrictBasic π K hW f) σ := by
    rw [Scheme.basicOpen_res, altOpen_restrictBasic]
  haveI := (isAffineOpen_altOpen π K σ).isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g ((V.presheaf.map (homOfLE hDg.le).op).hom y)
  refine ⟨n, a, ?_⟩
  have key := congrArg (V.presheaf.map (homOfLE hDg.ge).op).hom ha
  rw [map_mul, map_pow,
    show (algebraMap (V.presheaf.obj (Opposite.op (K.inter σ))) (V.presheaf.obj (Opposite.op (V.basicOpen g))) : _ →+* _)
        = (V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom from rfl,
    res_res, res_res, res_res,
    res_refl, res_res, mul_comm] at key
  exact key.symm

theorem away_ker (hW : IsAffineOpen W) (f : Γ(V, W))
    {q : ℕ} (σ : Scheme.OrderedAffineCoverOf.Idx (restrictBasic π K hW f) q)
    (x : Γ(V, K.inter σ))
    (hx : (V.presheaf.map (homOfLE
        (altOpen_restrictBasic_le π K hW f σ)).op).hom x = 0) :
    ∃ m : ℕ,
      (V.presheaf.map (homOfLE (K.inter_le_base σ)).op).hom f ^ m * x = 0 := by
  set g : Γ(V, K.inter σ) :=
    (V.presheaf.map (homOfLE (K.inter_le_base σ)).op).hom f
  have hDg : V.basicOpen g = Scheme.OrderedAffineCoverOf.inter (restrictBasic π K hW f) σ := by
    rw [Scheme.basicOpen_res, altOpen_restrictBasic]
  haveI := (isAffineOpen_altOpen π K σ).isLocalization_basicOpen g
  have hx' : (algebraMap (V.presheaf.obj (Opposite.op (K.inter σ))) (V.presheaf.obj (Opposite.op (V.basicOpen g)))) x = 0 := by
    rw [show (algebraMap _ _ : _ →+* _)
          = (V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom from rfl,
      ← res_res hDg.le (altOpen_restrictBasic_le π K hW f σ),
      hx, map_zero]
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers g) Γ(V, V.basicOpen g) x).mp hx'
  exact ⟨m, hm⟩

omit π in

theorem exists_refinement (hW : IsAffineOpen W) :
    ∃ (s : Set Γ(V, W)) (ι : s → K.ι),
      Ideal.span s = ⊤ ∧ ∀ r : s, V.basicOpen (r : Γ(V, W)) ≤ K.U (ι r) := by
  have hch : ∀ x : W, ∃ (g : Γ(V, W)) (i : K.ι),
      V.basicOpen g ≤ K.U i ∧ (x : V) ∈ V.basicOpen g := by
    intro x
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (K.iSup_eq.ge x.2)
    obtain ⟨g, hgle, hxg⟩ := hW.exists_basicOpen_le ⟨x, hxi⟩ x.2
    exact ⟨g, i, hgle, hxg⟩
  choose g ιg hgle hxg using hch
  refine ⟨Set.range g, fun r => ιg r.2.choose, ?_, fun r => ?_⟩
  · rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun r => V.basicOpen_le _) (fun x hxW => ?_)
    exact Opens.mem_iSup.mpr ⟨⟨g ⟨x, hxW⟩, ⟨_, rfl⟩⟩, hxg ⟨x, hxW⟩⟩
  · have : g r.2.choose = r.1 := r.2.choose_spec
    exact this ▸ hgle r.2.choose

theorem smul_pow_mem_range (hW : IsAffineOpen W)
    (f : Γ(V, W)) (i₀ : K.ι) (hfi : V.basicOpen f ≤ K.U i₀)
    (p : ℕ) (z : K.cochain (p + 1))
    (hz : letI := Scheme.OrderedAffineCoverOf.moduleSections π
          K.d π (p + 1) z = 0) :
    letI := moduleW_altC K (p + 1)
    ∃ N : ℕ, f ^ N • z ∈ rangeW π K p := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  letI := moduleW_altC K (p + 1)
  letI := moduleW_altC K p
  set Kf := restrictBasic π K hW f with hKf

  have hi₀f : Kf.U i₀ = V.basicOpen f := inf_eq_right.mpr hfi
  have hzf : Scheme.OrderedAffineCoverOf.d π Kf (p + 1) (resBasic π K hW f (p + 1) z)
      = 0 := by
    rw [altd_resBasic, hz, map_zero]
  obtain ⟨w, hw⟩ := wholeSpace_exact π Kf i₀ hi₀f p
    (LinearMap.mem_ker.mpr hzf)

  choose nσ aσ haσ using fun σ => away_surj π K hW f σ (w σ)
  set N₁ : ℕ := Finset.univ.sup nσ with hN₁
  have hN₁le : ∀ σ, nσ σ ≤ N₁ := fun σ => Finset.le_sup (Finset.mem_univ σ)

  set a : K.cochain p := fun σ =>
    (V.presheaf.map (homOfLE (K.inter_le_base σ)).op).hom f ^ (N₁ - nσ σ) * aσ σ
    with ha_def

  have hresA : ∀ σ, resBasic π K hW f p a σ
      = (V.presheaf.map (homOfLE (((altOpen_restrictBasic π K hW f σ).le.trans
          inf_le_right).trans (V.basicOpen_le f))).op).hom f ^ N₁ * w σ := by
    intro σ
    rw [resBasic_apply, ha_def, map_mul, map_pow, res_res,
      haσ σ, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hN₁le σ)]

  have hstep : resBasic π K hW f (p + 1) (K.d π p a)
      = resBasic π K hW f (p + 1) (f ^ N₁ • z) := by
    rw [← altd_resBasic]
    funext τ
    rw [Scheme.OrderedAffineCoverOf.d_apply, resBasic_apply, smulW_apply,
      map_pow, map_mul, map_pow, res_res]
    have hwτ := congrFun hw τ
    rw [Scheme.OrderedAffineCoverOf.d_apply, resBasic_apply] at hwτ
    rw [← hwτ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hresA, map_mul, map_pow, res_res, mul_smul_comm]

  have hker : ∀ τ : K.Idx (p + 1), ∃ m : ℕ,
      (V.presheaf.map (homOfLE (K.inter_le_base τ)).op).hom f ^ m
        * (K.d π p a τ - (f ^ N₁ • z) τ) = 0 := by
    intro τ
    refine away_ker π K hW f τ _ ?_
    have := congrFun hstep τ
    rw [resBasic_apply, resBasic_apply] at this
    rw [map_sub, this, sub_self]
  choose mτ hmτ using hker
  set N₂ : ℕ := Finset.univ.sup mτ
  refine ⟨N₁ + N₂, f ^ N₂ • a, ?_⟩
  rw [altd_smulW]
  funext τ
  rw [smulW_apply, smulW_apply, map_pow, map_pow]
  have hN₂le : mτ τ ≤ N₂ := Finset.le_sup (f := mτ) (Finset.mem_univ τ)
  have key := hmτ τ
  rw [smulW_apply, map_pow] at key
  have key2 : (V.presheaf.map (homOfLE (K.inter_le_base τ)).op).hom f ^ N₂
      * (K.d π p a τ
        - (V.presheaf.map (homOfLE (K.inter_le_base τ)).op).hom f ^ N₁ * z τ)
      = 0 := by
    conv_lhs => rw [← Nat.sub_add_cancel hN₂le, pow_add, mul_assoc, key]
    exact mul_zero _
  rw [mul_sub, ← mul_assoc, ← pow_add, sub_eq_zero, add_comm N₂ N₁] at key2
  exact key2

theorem affine_acyclic (hW : IsAffineOpen W) (p : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    LinearMap.ker (K.d π (p + 1))
      ≤ LinearMap.range (K.d π p) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections π
  letI := moduleW_altC K (p + 1)
  intro z hz
  obtain ⟨s, ιs, hspan, hle⟩ := exists_refinement K hW
  have : z ∈ rangeW π K p :=
    Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hspan z fun r =>
      smul_pow_mem_range π K hW r (ιs r) (hle r) p z hz
  exact this

end AffineAcyclic

end AlgebraicGeometry.Scheme.OrderedAffineCoverOf.Acyclic

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] {W : V.Opens}
    (K : V.OrderedAffineCoverOf W) (hW : IsAffineOpen W) (p : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections π
    LinearMap.ker (K.d π (p + 1)) ≤ LinearMap.range (K.d π p) :=
  Scheme.OrderedAffineCoverOf.Acyclic.affine_acyclic π K hW p

end S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen (solution)
