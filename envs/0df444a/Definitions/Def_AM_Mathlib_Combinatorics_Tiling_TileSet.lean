-- Prove2me | Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
-- name    : AM_Mathlib_Combinatorics_Tiling_TileSet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T05:50:56.935814+00:00
-- url     : https://prove2.me/theorems/cb9c60bd-0365-4b81-8258-233d7da068aa
-- title:
--   Tile Set
-- statement:
--   Definitions and structural lemmas for Tile Set, from jsm28/AperiodicMonotilesLean contributors (see pinned LICENSE and source headers)'s pinned Periodicity and isohedrality of tilings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
noncomputable section
namespace DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ι ιₜ ιₜ' ιₜ'' ιₜ''' E E' F : Type*} {ιₜι ιₜ'ι : ι → Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
variable (ps ιₜ) in
/-- A `TileSet ps ιₜ` is an indexed family of `PlacedTile ps`. This is a separate definition
rather than just using plain functions to facilitate defining associated API that can be used
with dot notation. -/
@[ext] structure TileSet where
  /-- The tiles in the family. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₜ → PlacedTile ps
namespace TileSet
instance [Nonempty ιₚ] : Nonempty (TileSet ps ιₜ) := ⟨⟨fun _ ↦ Classical.arbitrary _⟩⟩
instance [IsEmpty ιₜ] : Unique (TileSet ps ιₜ) where
  default := ⟨isEmptyElim⟩
  uniq _ := TileSet.ext <| funext isEmptyElim
instance : CoeFun (TileSet ps ιₜ) (fun _ ↦ ιₜ → PlacedTile ps) where
  coe := tiles
attribute [coe] tiles
@[simp, norm_cast] lemma coe_inj {t₁ t₂ : TileSet ps ιₜ} :
    (t₁ : ιₜ → PlacedTile ps) = t₂ ↔ t₁ = t₂ :=
  TileSet.ext_iff.symm
@[coe] def coeSet (t : TileSet ps ιₜ) : Set (PlacedTile ps) := Set.range t
instance : CoeOut (TileSet ps ιₜ) (Set (PlacedTile ps)) where
  coe := coeSet
instance : Membership (PlacedTile ps) (TileSet ps ιₜ) where
  mem t pt := pt ∈ (t : Set (PlacedTile ps))
@[simp] lemma mem_coeSet {pt : PlacedTile ps} {t : TileSet ps ιₜ} :
    pt ∈ (t : Set (PlacedTile ps)) ↔ pt ∈ t :=
  Iff.rfl
lemma coeSet_apply (t : TileSet ps ιₜ) : t = Set.range t := rfl
@[simp] lemma exists_mem_iff {t : TileSet ps ιₜ} {f : PlacedTile ps → Prop} :
    (∃ pt ∈ t, f pt) ↔ ∃ i, f (t i) := by
  simp_rw [← mem_coeSet, coeSet_apply, Set.exists_range_iff]
@[simp] lemma forall_mem_iff {t : TileSet ps ιₜ} {f : PlacedTile ps → Prop} :
    (∀ pt ∈ t, f pt) ↔ ∀ i, f (t i) := by
  simp_rw [← mem_coeSet, coeSet_apply, Set.forall_mem_range]
def reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) : TileSet ps ιₜ' where
  tiles := ↑t ∘ f
@[simp] lemma coe_reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) : t.reindex f = ↑t ∘ f := rfl
@[simp] lemma reindex_apply (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) (i : ιₜ') :
    t.reindex f i = t (f i) :=
  rfl
@[simp] lemma reindex_id (t : TileSet ps ιₜ) : t.reindex id = t := rfl
@[simp] lemma injective_reindex_iff_injective {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ}
    (ht : Injective t) : Injective (↑t ∘ f) ↔ Injective f :=
  ht.of_comp_iff _
@[simp] lemma reindex_reindex (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) (f' : ιₜ'' → ιₜ') :
    (t.reindex f).reindex f' = t.reindex (f ∘ f') :=
  rfl
@[simp] lemma reindex_eq_reindex_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f : ιₜ' → ιₜ}
    (h : Surjective f) : t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ := by
  refine ⟨fun he ↦ TileSet.ext <| funext <| h.forall.2 fun i ↦ ?_,
          fun he ↦ congrArg₂ _ he rfl⟩
  simp_rw [← reindex_apply, he]
@[simp] lemma reindex_eq_reindex_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} (f : E) :
    t₁.reindex f = t₂.reindex f ↔ t₁ = t₂ :=
  reindex_eq_reindex_iff_of_surjective (EquivLike.surjective f)
@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ}
    {f₁ f₂ : ιₜ' → ιₜ} {f : ιₜ'' → ιₜ'} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ := by
  rw [← reindex_reindex, ← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]
@[simp] lemma reindex_comp_eq_reindex_comp_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ}
    {f₁ f₂ : ιₜ' → ιₜ} (f : E') :
    t₁.reindex (f₁ ∘ f) = t₂.reindex (f₂ ∘ f) ↔ t₁.reindex f₁ = t₂.reindex f₂ :=
  reindex_comp_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)
@[simp] lemma reindex_comp_eq_reindex_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]
@[simp] lemma reindex_comp_eq_reindex_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    (f : E) : t₁.reindex (f₁ ∘ f) = t₂.reindex f ↔ t₁.reindex f₁ = t₂ :=
  reindex_comp_eq_reindex_iff_of_surjective (EquivLike.surjective f)
@[simp] lemma reindex_eq_reindex_comp_iff_of_surjective {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    {f : ιₜ' → ιₜ} (h : Surjective f) :
    t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ := by
  rw [← reindex_reindex, reindex_eq_reindex_iff_of_surjective h]
@[simp] lemma reindex_eq_reindex_comp_iff_of_equivLike {t₁ t₂ : TileSet ps ιₜ} {f₁ : ιₜ → ιₜ}
    (f : E) : t₁.reindex f = t₂.reindex (f₁ ∘ f) ↔ t₁ = t₂.reindex f₁ :=
  reindex_eq_reindex_comp_iff_of_surjective (EquivLike.surjective f)
@[simp] lemma coeSet_reindex_of_surjective (t : TileSet ps ιₜ) {f : ιₜ' → ιₜ} (h : Surjective f) :
    (t.reindex f : Set (PlacedTile ps)) = t :=
  h.range_comp _
@[simp] lemma coeSet_reindex_of_equivLike (t : TileSet ps ιₜ) (f : E) :
    (t.reindex f : Set (PlacedTile ps)) = t :=
  t.coeSet_reindex_of_surjective <| EquivLike.surjective f
@[simp] lemma mem_reindex_iff_of_surjective {t : TileSet ps ιₜ} {f : ιₜ' → ιₜ} {pt : PlacedTile ps}
    (h : Surjective f) : pt ∈ t.reindex f ↔ pt ∈ t :=
  iff_of_eq <| congrArg (pt ∈ ·) <| t.coeSet_reindex_of_surjective h
@[simp] lemma mem_reindex_iff_of_equivLike {t : TileSet ps ιₜ} (f : E) {pt : PlacedTile ps} :
    pt ∈ t.reindex f ↔ pt ∈ t :=
  mem_reindex_iff_of_surjective <| EquivLike.surjective f
def equivOfCoeSetEqOfInjective {t₁ : TileSet ps ιₜ} {t₂ : TileSet ps ιₜ'}
    (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁) (h₂ : Injective t₂) : ιₜ' ≃ ιₜ :=
  ((Equiv.ofInjective t₂ h₂).trans (Equiv.cast (congrArg _ h.symm))).trans
    (Equiv.ofInjective t₁ h₁).symm
set_option backward.isDefEq.respectTransparency false in
@[simp] lemma reindex_equivOfCoeSetEqOfInjective {t₁ : TileSet ps ιₜ} {t₂ : TileSet ps ιₜ'}
    (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁) (h₂ : Injective t₂) :
    t₁.reindex (equivOfCoeSetEqOfInjective h h₁ h₂) = t₂ := by
  ext i : 2
  simp only [equivOfCoeSetEqOfInjective, Equiv.coe_trans, reindex_apply, comp_apply,
    Equiv.ofInjective_apply, Equiv.cast_apply]
  erw [Equiv.apply_ofInjective_symm h₁]
  rw [Subtype.coe_eq_iff]
  simp_rw [coeSet_apply] at h
  refine ⟨h ▸ Set.mem_range_self _, ?_⟩
  rw [cast_eq_iff_heq, Subtype.heq_iff_coe_eq]
  simp [h]
instance : MulAction G (TileSet ps ιₜ) where
  smul g t := ⟨(g • ·) ∘ ↑t⟩
  one_smul _ := TileSet.ext <| funext <| fun _ ↦ one_smul _ _
  mul_smul _ _ _ := TileSet.ext <| funext <| fun _ ↦ mul_smul _ _ _
lemma smul_coe (g : G) (t : TileSet ps ιₜ) : (g • t : TileSet ps ιₜ) = (g • ·) ∘ ↑t := rfl
lemma smul_apply (g : G) (t : TileSet ps ιₜ) (i : ιₜ) : (g • t) i = g • (t i) := rfl
@[simp] lemma smul_mem_smul_apply_iff (g : G) {x : X} {t : TileSet ps ιₜ} {i : ιₜ} :
    g • x ∈ (g • t) i ↔ x ∈ t i :=
  PlacedTile.smul_mem_smul_iff g
@[simp] lemma smul_reindex (g : G) (t : TileSet ps ιₜ) (f : ιₜ' → ιₜ) :
    g • (t.reindex f) = (g • t).reindex f :=
  rfl
@[simp] lemma injective_smul_iff (g : G) {t : TileSet ps ιₜ} : Injective (g • t) ↔ Injective t :=
  Injective.of_comp_iff (MulAction.injective g) t
@[simp] lemma coeSet_smul (g : G) (t : TileSet ps ιₜ) :
    (g • t : TileSet ps ιₜ) = g • (t : Set (PlacedTile ps)) := by
  simp [coeSet_apply, smul_coe, Set.range_comp]
@[simp] lemma smul_mem_smul_iff {pt : PlacedTile ps} (g : G) {t : TileSet ps ιₜ} :
    g • pt ∈ g • t ↔ pt ∈ t := by
  rw [← mem_coeSet, ← mem_coeSet, coeSet_smul, Set.smul_mem_smul_set_iff]
@[simp] lemma smul_inter_smul (g : G) (t : TileSet ps ιₜ) (s : Set X) (i : ιₜ) :
    g • s ∩ (g • t) i = g • (s ∩ t i) := by
  simp [smul_apply, Set.smul_set_inter]
instance : MulAction (G × Equiv.Perm ιₜ) (TileSet ps ιₜ) where
  smul g t := (g.fst • t).reindex g.snd.symm
  one_smul _ := TileSet.ext <| funext <| fun _ ↦ one_smul _ _
  mul_smul g h t := TileSet.ext <| funext <| fun i ↦ by
    change (g.1 * h.1) • t ((g.2 * h.2)⁻¹ i) = g.1 • h.1 • t (h.2⁻¹ (g.2⁻¹ i))
    simp [mul_smul]
def symmetryGroup (t : TileSet ps ιₜ) : Subgroup G :=
  (MulAction.stabilizer (G × Equiv.Perm ιₜ) t).map (MonoidHom.fst _ _)
protected def sum (t : TileSet ps ιₜ) (t' : TileSet ps ιₜ') : TileSet ps (ιₜ ⊕ ιₜ') where
  tiles := Sum.elim t.tiles t'.tiles
protected def sigma (t : (i : ι) → TileSet ps (ιₜι i)) : TileSet ps (Σ i, ιₜι i) where
  tiles := Sigma.uncurry (fun i ↦ ↑(t i))
end TileSet
end DiscreteTiling


