-- Prove2me | Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Decomposition
-- name    : PretorsionImageClosed_IndecomposableClosures_Decomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T03:58:05.177365+00:00
-- url     : https://prove2.me/theorems/02cfc45b-a5f3-4c4b-be32-72ebdce341ee
-- title:
--   Decomposition
-- statement:
--   Definitions and structural lemmas for Decomposition, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/IndecomposableClosures/Decomposition.lean

module
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.Ring
public import Definitions.Def_PretorsionImageClosed_IndecomposableClosures_Skeleton
public import Theorems.Thm_PretorsionImageClosed_IsIndecomposableModule_of_linearEquiv

set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PretorsionImageClosed.FiniteLengthDecomposition
universe u w
variable {R : Type u} [Ring R] [IsNoetherianRing R]
attribute [local instance]
  HasFiniteBiproducts.of_hasFiniteCoproducts
structure PiDecomposition (X : FGModuleCat.{w} R) where
  index : FintypeCat.{0}
  summand : index → FGModuleCat.{w} R
  indecomposable :
    ∀ i, PretorsionImageClosed.IsIndecomposableModule R (summand i)
  equiv : X ≃ₗ[R] (∀ i, summand i)
namespace PiDecomposition
variable {X Y : FGModuleCat.{w} R}
def empty (X : FGModuleCat.{w} R) [Subsingleton X] :
    PiDecomposition X where
  index := FintypeCat.of (Fin 0)
  summand := fun _ ↦ X
  indecomposable := fun i ↦ Fin.elim0 i
  equiv := LinearEquiv.ofSubsingleton X (∀ _ : Fin 0, X)
def singleton (X : FGModuleCat.{w} R)
    (hX : PretorsionImageClosed.IsIndecomposableModule R X) :
    PiDecomposition X where
  index := FintypeCat.of PUnit
  summand := fun _ ↦ X
  indecomposable := fun _ ↦ hX
  equiv := (LinearEquiv.piUnique R (fun _ : PUnit ↦ X)).symm
def ofIsCompl
    (X : FGModuleCat.{w} R)
    (N P : Submodule R X) (hNP : IsCompl N P)
    (dN : PiDecomposition (FGModuleCat.of R N))
    (dP : PiDecomposition (FGModuleCat.of R P)) :
    PiDecomposition X where
  index := FintypeCat.of (dN.index ⊕ dP.index)
  summand := fun i ↦ Sum.elim dN.summand dP.summand i
  indecomposable := by
    intro i
    cases i with
    | inl i => exact dN.indecomposable i
    | inr i => exact dP.indecomposable i
  equiv :=
    (N.prodEquivOfIsCompl P hNP).symm ≪≫ₗ
      dN.equiv.prodCongr dP.equiv ≪≫ₗ
        (LinearEquiv.sumPiEquivProdPi R dN.index dP.index
          (fun i ↦ ↥(Sum.elim dN.summand dP.summand i))).symm
def toBiproductIso (d : PiDecomposition X) :
    X ≅ biproduct d.summand := by
  let F :=
    forget₂ (FGModuleCat.{w} R) (ModuleCat.{w} R)
  letI : PreservesBiproduct d.summand F :=
    preservesBiproduct_of_preservesProduct F
  let e :
      biproduct d.summand ≅
        FGModuleCat.of R (∀ i, d.summand i) :=
    F.preimageIso
      (F.mapBiproduct d.summand ≪≫
        ModuleCat.biproductIsoPi
          (fun i ↦ F.obj (d.summand i)))
  exact d.equiv.toFGModuleCatIso ≪≫ e.symm
end PiDecomposition
noncomputable def piDecompositionOfLengthEq :
    ∀ n : ℕ, ∀ X : FGModuleCat.{w} R,
      IsFiniteLength R X →
      Module.length R X = n →
      PiDecomposition X := by
  intro n
  refine Nat.strongRec (motive := fun n ↦
    ∀ X : FGModuleCat.{w} R,
      IsFiniteLength R X →
      Module.length R X = n →
      PiDecomposition X) ?_ n
  intro n ih X hfinite hlength
  classical
  by_cases hindecomposable :
      PretorsionImageClosed.IsIndecomposableModule R X
  · exact PiDecomposition.singleton X hindecomposable
  by_cases hnontrivial : Nontrivial X
  · have hfailure :
        ¬ ∀ N P : Submodule R X,
          IsCompl N P → N = ⊥ ∨ P = ⊥ := by
      intro hall
      exact hindecomposable ⟨hnontrivial, hall⟩
    push Not at hfailure
    let N : Submodule R X := Classical.choose hfailure
    have hPexists :
        ∃ P : Submodule R X,
          IsCompl N P ∧ N ≠ ⊥ ∧ P ≠ ⊥ :=
      Classical.choose_spec hfailure
    let P : Submodule R X := Classical.choose hPexists
    have hsplit :
        IsCompl N P ∧ N ≠ ⊥ ∧ P ≠ ⊥ :=
      Classical.choose_spec hPexists
    have hNP : IsCompl N P := hsplit.1
    have hNbot : N ≠ ⊥ := hsplit.2.1
    have hPbot : P ≠ ⊥ := hsplit.2.2
    have horders :=
      isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite
    letI : IsNoetherian R X := horders.1
    letI : IsArtinian R X := horders.2
    have hNtop : N ≠ ⊤ := by
      intro hN
      apply hPbot
      apply top_disjoint.mp
      simpa [hN] using hNP.disjoint
    have hPtop : P ≠ ⊤ := by
      intro hP
      apply hNbot
      apply disjoint_top.mp
      simpa [hP] using hNP.disjoint
    have hNfinite : IsFiniteLength R N :=
      hfinite.of_injective (Submodule.injective_subtype N)
    have hPfinite : IsFiniteLength R P :=
      hfinite.of_injective (Submodule.injective_subtype P)
    let nN := (Module.length R N).toNat
    let nP := (Module.length R P).toNat
    have hNne : Module.length R N ≠ ⊤ :=
      Module.length_ne_top_iff.mpr hNfinite
    have hPne : Module.length R P ≠ ⊤ :=
      Module.length_ne_top_iff.mpr hPfinite
    have hNcoe : (nN : ℕ∞) = Module.length R N :=
      ENat.coe_toNat hNne
    have hPcoe : (nP : ℕ∞) = Module.length R P :=
      ENat.coe_toNat hPne
    have hNltCoe : (nN : ℕ∞) < (n : ℕ∞) := by
      rw [hNcoe, ← hlength]
      exact Submodule.length_lt hNtop
    have hPltCoe : (nP : ℕ∞) < (n : ℕ∞) := by
      rw [hPcoe, ← hlength]
      exact Submodule.length_lt hPtop
    have hNlt : nN < n := ENat.coe_lt_coe.mp hNltCoe
    have hPlt : nP < n := ENat.coe_lt_coe.mp hPltCoe
    let dN : PiDecomposition (FGModuleCat.of R N) :=
      ih nN hNlt (FGModuleCat.of R N) hNfinite hNcoe.symm
    let dP : PiDecomposition (FGModuleCat.of R P) :=
      ih nP hPlt (FGModuleCat.of R P) hPfinite hPcoe.symm
    exact PiDecomposition.ofIsCompl X N P hNP dN dP
  · letI : Subsingleton X :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    exact PiDecomposition.empty X
noncomputable def piDecomposition
    (X : FGModuleCat.{w} R) (hfinite : IsFiniteLength R X) :
    PiDecomposition X := by
  let n := (Module.length R X).toNat
  have hne : Module.length R X ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hfinite
  exact piDecompositionOfLengthEq n X hfinite (ENat.coe_toNat hne).symm
theorem exists_fin_biproduct_decomposition
    (X : FGModuleCat.{w} R) (hfinite : IsFiniteLength R X) :
    ∃ (n : ℕ) (Y : Fin n → FGModuleCat.{w} R),
      (∀ j, PretorsionImageClosed.IsIndecomposableModule R (Y j)) ∧
      Nonempty (X ≅ biproduct Y) := by
  let d := piDecomposition X hfinite
  letI : Fintype d.index := Fintype.ofFinite d.index
  let e : d.index ≃ Fin (Fintype.card d.index) :=
    Fintype.equivFin d.index
  let Y : Fin (Fintype.card d.index) → FGModuleCat.{w} R :=
    fun j ↦ d.summand (e.symm j)
  have hY :
      ∀ j, PretorsionImageClosed.IsIndecomposableModule R (Y j) :=
    fun j ↦ d.indecomposable (e.symm j)
  let reindex :
      biproduct d.summand ≅ biproduct Y :=
    biproduct.whiskerEquiv e
      (fun j ↦ eqToIso (by simp [Y]))
  exact ⟨Fintype.card d.index, Y, hY,
    ⟨d.toBiproductIso ≪≫ reindex⟩⟩
def CanonicalIndecomposableIndex
    (R : Type u) [Ring R] [IsNoetherianRing R] :=
  {i : Skeleton (FGModuleCat.{w} R) //
    PretorsionImageClosed.IsIndecomposableModule R
      ((fromSkeleton (FGModuleCat.{w} R)).obj i)}
noncomputable def canonicalIndecomposableSkeleton
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X) :
    IndecomposableSkeleton R (CanonicalIndecomposableIndex.{u, w} R) where
  obj i := (fromSkeleton (FGModuleCat.{w} R)).obj i.1
  indecomposable i := i.2
  finiteLength i := hfinite _
  eq_of_iso := by
    intro i j h
    apply Subtype.ext
    rcases h with ⟨e⟩
    exact skeleton_skeletal _ ⟨(fromSkeleton _).preimageIso e⟩
  complete := by
    intro X hX
    let e :
        X ≅
          (fromSkeleton (FGModuleCat.{w} R)).obj
            (toSkeleton X) :=
      (fromSkeletonToSkeletonIso X).symm
    have hi :
        PretorsionImageClosed.IsIndecomposableModule R
          ((fromSkeleton (FGModuleCat.{w} R)).obj
            (toSkeleton X)) :=
      hX.of_linearEquiv (FGModuleCat.isoToLinearEquiv e)
    exact ⟨⟨toSkeleton X, hi⟩, ⟨e⟩⟩
  decomposes := by
    intro X
    obtain ⟨n, Y, hY, ⟨e⟩⟩ :=
      exists_fin_biproduct_decomposition X (hfinite X)
    let a :
        Fin n → CanonicalIndecomposableIndex.{u, w} R :=
      fun t ↦
        ⟨toSkeleton (Y t),
          (hY t).of_linearEquiv
            (FGModuleCat.isoToLinearEquiv
              (fromSkeletonToSkeletonIso (Y t)).symm)⟩
    refine ⟨n, a, ⟨e ≪≫ biproduct.mapIso (fun t ↦ ?_)⟩⟩
    exact (fromSkeletonToSkeletonIso (Y t)).symm
noncomputable def canonicalFiniteIndecomposableSkeleton
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    [Finite (CanonicalIndecomposableIndex.{u, w} R)] :
    FiniteIndecomposableSkeleton R where
  ι := CanonicalIndecomposableIndex.{u, w} R
  finite_ι := inferInstance
  skeleton := canonicalIndecomposableSkeleton hfinite
end PretorsionImageClosed.FiniteLengthDecomposition
namespace PretorsionImageClosed
universe u w
abbrev CanonicalIndecomposableIndex
    (R : Type u) [Ring R] [IsNoetherianRing R] :=
  FiniteLengthDecomposition.CanonicalIndecomposableIndex.{u, w} R
def IsRepresentationFinite
    (R : Type u) [Ring R] [IsNoetherianRing R] : Prop :=
  Finite (CanonicalIndecomposableIndex.{u, w} R)
noncomputable abbrev indecomposableSkeletonOfFiniteLength
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X) :
    IndecomposableSkeleton R (CanonicalIndecomposableIndex.{u, w} R) :=
  FiniteLengthDecomposition.canonicalIndecomposableSkeleton hfinite
noncomputable abbrev finiteIndecomposableSkeletonOfFiniteLength
    {R : Type u} [Ring R] [IsNoetherianRing R]
    (hfinite : ∀ X : FGModuleCat.{w} R, IsFiniteLength R X)
    [Finite (CanonicalIndecomposableIndex.{u, w} R)] :
    FiniteIndecomposableSkeleton R :=
  FiniteLengthDecomposition.canonicalFiniteIndecomposableSkeleton hfinite
end PretorsionImageClosed


