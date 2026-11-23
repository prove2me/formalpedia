-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
-- name    : GroundTheory_AutomorphicForms_GLnLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:00.397795+00:00
-- url     : https://prove2.me/theorems/d07de446-152b-4bc3-8729-d3c61b8efed5
-- title:
--   GLn Lattice
-- statement:
--   Definitions and structural lemmas for GLn Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
namespace GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
section Algebraic
def glLin (g : GL (Fin n) F) : (Fin n → F) →ₗ[𝒪[F]] (Fin n → F) :=
  (Matrix.toLin' (g : Matrix (Fin n) (Fin n) F)).restrictScalars 𝒪[F]
@[simp]
theorem glLin_apply (g : GL (Fin n) F) (v : Fin n → F) :
    glLin F n g v = (g : Matrix (Fin n) (Fin n) F) *ᵥ v :=
  rfl
def mapSubmodule (g : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F)) :
    Submodule 𝒪[F] (Fin n → F) :=
  L.map (glLin F n g)
theorem mapSubmodule_one (L : Submodule 𝒪[F] (Fin n → F)) : mapSubmodule F n 1 L = L := by
  have : glLin F n 1 = LinearMap.id := LinearMap.ext fun v => by simp
  rw [mapSubmodule, this, Submodule.map_id]
theorem mapSubmodule_mul (g h : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F)) :
    mapSubmodule F n (g * h) L = mapSubmodule F n g (mapSubmodule F n h L) := by
  have : glLin F n (g * h) = glLin F n g ∘ₗ glLin F n h := LinearMap.ext fun v => by
    simp [Matrix.mulVec_mulVec]
  rw [mapSubmodule, mapSubmodule, mapSubmodule, this, Submodule.map_comp]
theorem mapSubmodule_inv_mapSubmodule (g : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F)) :
    mapSubmodule F n g⁻¹ (mapSubmodule F n g L) = L := by
  rw [← mapSubmodule_mul, inv_mul_cancel, mapSubmodule_one]
theorem mapSubmodule_mapSubmodule_inv (g : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F)) :
    mapSubmodule F n g (mapSubmodule F n g⁻¹ L) = L := by
  rw [← mapSubmodule_mul, mul_inv_cancel, mapSubmodule_one]
theorem isLattice_mapSubmodule (g : GL (Fin n) F) (L : Submodule 𝒪[F] (Fin n → F))
    [L.IsLattice F] : (mapSubmodule F n g L).IsLattice F where
  fg := (Submodule.IsLattice.fg (A := F) (M := L)).map _
  span_eq_top := by
    have : ((mapSubmodule F n g L : Submodule 𝒪[F] (Fin n → F)) : Set (Fin n → F)) =
        Matrix.toLin' (g : Matrix (Fin n) (Fin n) F) '' (L : Set (Fin n → F)) := by
      rw [mapSubmodule, Submodule.map_coe]
      rfl
    rw [this, Submodule.span_image, Submodule.IsLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    intro v
    refine ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
def standardLattice : Submodule 𝒪[F] (Fin n → F) where
  carrier := {v | ∀ i, v i ∈ 𝒪[F]}
  add_mem' ha hb i := Subring.add_mem _ (ha i) (hb i)
  zero_mem' _ := Subring.zero_mem _
  smul_mem' c _ hv i := Subring.mul_mem _ c.2 (hv i)
theorem single_mem_standardLattice (j : Fin n) : Pi.single j (1 : F) ∈ standardLattice F n := by
  intro i
  rw [Pi.single_apply]
  split_ifs <;> simp
theorem standardLattice_eq_span :
    standardLattice F n = Submodule.span 𝒪[F] (Set.range fun j => Pi.single j (1 : F)) := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · have : v = ∑ j, (⟨v j, hv j⟩ : 𝒪[F]) • (Pi.single j (1 : F) : Fin n → F) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    exact single_mem_standardLattice F n j
instance isLattice_standardLattice : (standardLattice F n).IsLattice F where
  fg := by
    rw [standardLattice_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    refine eq_top_iff.mpr ((Pi.basisFun F (Fin n)).span_eq.symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply]
    exact single_mem_standardLattice F n j
theorem mulVec_mem_standardLattice {A : Matrix (Fin n) (Fin n) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    {v : Fin n → F} (hv : v ∈ standardLattice F n) : A *ᵥ v ∈ standardLattice F n := fun i => by
  rw [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hv j)
theorem mapSubmodule_le_standardLattice_iff {g : GL (Fin n) F} :
    mapSubmodule F n g (standardLattice F n) ≤ standardLattice F n ↔ ∀ i j, g i j ∈ 𝒪[F] := by
  constructor
  · intro h i j
    have := h (Submodule.mem_map_of_mem (f := glLin F n g) (single_mem_standardLattice F n j)) i
    rwa [glLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] at this
  · rintro h _ ⟨v, hv, rfl⟩
    exact mulVec_mem_standardLattice F n h hv
theorem mapSubmodule_standardLattice_eq_iff {g : GL (Fin n) F} :
    mapSubmodule F n g (standardLattice F n) = standardLattice F n ↔ g ∈ integralGL F n := by
  rw [mem_integralGL_iff]
  constructor
  · intro h
    refine ⟨(mapSubmodule_le_standardLattice_iff F n).mp h.le,
      (mapSubmodule_le_standardLattice_iff F n).mp ?_⟩
    conv_lhs => rw [← h]
    rw [mapSubmodule_inv_mapSubmodule]
  · rintro ⟨h1, h2⟩
    refine le_antisymm ((mapSubmodule_le_standardLattice_iff F n).mpr h1) ?_
    conv_lhs => rw [← mapSubmodule_mapSubmodule_inv F n g (standardLattice F n)]
    exact Submodule.map_mono ((mapSubmodule_le_standardLattice_iff F n).mpr h2)
def Lattice : Type _ := {L : Submodule 𝒪[F] (Fin n → F) // L.IsLattice F}
instance (L : Lattice F n) : L.1.IsLattice F := L.2
instance : MulAction (GL (Fin n) F) (Lattice F n) where
  smul g L := ⟨mapSubmodule F n g L.1, isLattice_mapSubmodule F n g L.1⟩
  one_smul L := Subtype.ext (mapSubmodule_one F n L.1)
  mul_smul g h L := Subtype.ext (mapSubmodule_mul F n g h L.1)
@[simp]
theorem coe_smul (g : GL (Fin n) F) (L : Lattice F n) :
    (g • L).1 = mapSubmodule F n g L.1 :=
  rfl
def standard : Lattice F n := ⟨standardLattice F n, inferInstance⟩
theorem smul_standard_eq_iff {g : GL (Fin n) F} :
    g • standard F n = standard F n ↔ g ∈ integralGL F n := by
  rw [← mapSubmodule_standardLattice_eq_iff]
  exact Subtype.ext_iff
theorem smul_standard_eq_smul_standard_iff {g h : GL (Fin n) F} :
    g • standard F n = h • standard F n ↔ g⁻¹ * h ∈ integralGL F n := by
  rw [eq_comm, ← inv_smul_eq_iff, smul_smul, smul_standard_eq_iff]
section MaximalCompact
def transvectionGL {i j : Fin n} (hij : i ≠ j) : GL (Fin n) F :=
  ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
    by rw [Matrix.transvection_mul_transvection_same _ _ hij, add_neg_cancel,
      Matrix.transvection_zero],
    by rw [Matrix.transvection_mul_transvection_same _ _ hij, neg_add_cancel,
      Matrix.transvection_zero]⟩
end MaximalCompact
end Algebraic
section Topological
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
theorem exists_smul_standard (L : Lattice F n) : ∃ g : GL (Fin n) F, g • standard F n = L := by
  obtain ⟨L, hL⟩ := L
  let b := Module.Free.chooseBasis 𝒪[F] L
  let B := b.extendOfIsLattice F
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex 𝒪[F] L) = n := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  let M : Matrix (Fin n) (Fin n) F := (Pi.basisFun F (Fin n)).toMatrix (B.reindex e)
  let : Invertible M := (Pi.basisFun F (Fin n)).invertibleToMatrix (B.reindex e)
  refine ⟨unitOfInvertible M, Subtype.ext ?_⟩
  have hspan : Submodule.span 𝒪[F] (Set.range fun k => (b k : Fin n → F)) = L := by
    have := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at this
    exact this
  have hcol : ∀ j, glLin F n (unitOfInvertible M) (Pi.single j 1) = (b (e.symm j) : Fin n → F) := by
    intro j
    ext i
    rw [glLin_apply, show ((unitOfInvertible M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M
      from rfl, Matrix.mulVec_single_one, Matrix.col_apply]
    simp [M, Module.Basis.toMatrix_apply, B]
  have hfun : (glLin F n (unitOfInvertible M) ∘ fun j => Pi.single j (1 : F)) =
      (fun k => (b k : Fin n → F)) ∘ e.symm := funext hcol
  change mapSubmodule F n _ (standardLattice F n) = L
  rw [standardLattice_eq_span, mapSubmodule, Submodule.map_span, ← Set.range_comp, hfun,
    e.symm.surjective.range_comp, hspan]
def quotientEquivLattice : GL (Fin n) F ⧸ integralGL F n ≃ Lattice F n :=
  Equiv.ofBijective
    (Quotient.lift (fun g : GL (Fin n) F => g • standard F n) fun a b h => by
      have h' : (a : GL (Fin n) F ⧸ integralGL F n) = b := Quotient.sound h
      rw [QuotientGroup.eq] at h'
      exact (smul_standard_eq_smul_standard_iff F n).mpr h')
    ⟨fun x y => Quotient.inductionOn₂ x y fun a b h =>
      (QuotientGroup.eq (s := integralGL F n)).mpr ((smul_standard_eq_smul_standard_iff F n).mp h),
    fun L => (exists_smul_standard F n L).elim fun g hg =>
      ⟨(g : GL (Fin n) F ⧸ integralGL F n), hg⟩⟩
end Topological
section Compact
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
def IsMaximalCompact {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) : Prop :=
  IsCompact (H : Set G) ∧ ∀ H' : Subgroup G, IsCompact (H' : Set G) → H ≤ H' → H' = H
end Compact
end GLnLocal
end GroundTheory.Automorphic


