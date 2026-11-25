-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:05.103404+00:00
-- url     : https://prove2.me/theorems/3ce77335-ea02-43a0-b1df-01467f47a18c
-- title:
--   Is Affine Split Torus Left
-- statement:
--   Definitions and structural lemmas for Is Affine Split Torus Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/IsAffineSplitTorusLeft.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Theorems.Thm_GlobalTheory_splitTorus_properties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZJ
structure Charts (X : Scheme.{0}) where
  I : Type
  [fin : Finite I]
  Cl : Type
  [finC : Finite Cl]
  wt : I → Cl
  c₀ : Cl
  W : {i // wt i = c₀} → X.Opens
  aff : ∀ i, IsAffineOpen (W i)
  cover : ⨆ i, W i = ⊤
  r : ∀ i, I → Γ(X, W i)
  r_self : ∀ i, r i i.1 = 1
  inter : ∀ i i', W i ⊓ W i' = X.basicOpen (r i i'.1)
  trans : ∀ i i' j, resG X (inf_le_left : W i ⊓ W i' ≤ W i) (r i j) =
    resG X (inf_le_left : W i ⊓ W i' ≤ W i) (r i i'.1) * resG X (inf_le_right : W i ⊓ W i' ≤ W i') (r i' j)
attribute [instance] Charts.fin Charts.finC
def Charts.pull {X Y : Scheme.{0}} (C : Charts X) (φ : Y ⟶ X) [IsAffineHom φ] : Charts Y where
  I := C.I
  Cl := C.Cl
  wt := C.wt
  c₀ := C.c₀
  W := fun i => φ ⁻¹ᵁ C.W i
  aff := fun i => (C.aff i).preimage φ
  cover := by rw [← Scheme.Hom.preimage_iSup, C.cover, Scheme.Hom.preimage_top]
  r := fun i j => (φ.app (C.W i)).hom (C.r i j)
  r_self := fun i => by rw [C.r_self, map_one]
  inter := fun i i' => by rw [← Scheme.preimage_basicOpen, ← C.inter, Scheme.Hom.preimage_inf]
  trans := fun i i' j => by
    have key : ∀ (V : X.Opens) (h : C.W i ⊓ C.W i' ≤ V) (h' : φ ⁻¹ᵁ C.W i ⊓ φ ⁻¹ᵁ C.W i' ≤ φ ⁻¹ᵁ V) (u : Γ(X, V)),
        resG Y h' ((φ.app V).hom u) =
          (φ.appLE (C.W i ⊓ C.W i') (φ ⁻¹ᵁ C.W i ⊓ φ ⁻¹ᵁ C.W i') φ.preimage_inf.ge).hom (resG X h u) := by
      intro V h h' u
      change (φ.app V ≫ Y.presheaf.map (homOfLE h').op).hom u =
        (X.presheaf.map (homOfLE h).op ≫ φ.appLE _ _ _).hom u
      rw [Scheme.Hom.map_appLE]
      rfl
    rw [key _ inf_le_left, key _ inf_le_left, key _ inf_le_right, C.trans i i' j, map_mul]
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
def Stable (i : splitTorus S X ⟶ H) (V : H.left.Opens) : Prop :=
  ∀ (Y : Over S) (t : Y ⟶ splitTorus S X) (g : Y ⟶ H), ⊤ ≤ g.left ⁻¹ᵁ V → ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V
def HasWt (i : splitTorus S X ⟶ H) (V : H.left.Opens) (u : Γ(H.left, V)) (χ : X) : Prop :=
  ∀ (Y : Over S) (t : Y ⟶ splitTorus S X) (g : Y ⟶ H) (h : ⊤ ≤ g.left ⁻¹ᵁ V) (h' : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V),
    (((t ≫ i) * g).left.appLE V ⊤ h').hom u = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE V ⊤ h).hom u
structure Charts.Torus (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) (i : splitTorus S (Fin d → ℤ) ⟶ H) : Prop where
  hom : IsMonHom i
  stable : ∀ a, Stable i (C.W a)
  inv : ∀ a j, C.wt j = C.c₀ → HasWt i (C.W a) (C.r a j) 0
  wt : ∀ a j k, C.wt j = c k → HasWt i (C.W a) (C.r a j) (Pi.single k 1)
  bpf : ∀ k (x : H.left), ∃ a j, C.wt j = c k ∧ x ∈ H.left.basicOpen (C.r a j)
  gen : ∀ a (u : Γ(H.left, C.W a)), HasWt i (C.W a) u 0 →
    u ∈ Subring.closure (Set.range (H.hom.appLE ⊤ (C.W a) le_top).hom ∪ {v | ∃ j, C.wt j = C.c₀ ∧ v = C.r a j})
def Charts.Split (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) : Prop :=
  GeometricallyConnected H.hom ∧ ∃ i : splitTorus S (Fin d → ℤ) ⟶ H, C.Torus c i
def Charts.SplitOn {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (C : Charts G.left) {d : ℕ}
    (c : Fin d → C.Cl) (Sg : Set (Sp R)) : Prop :=
  ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R) (_ : IsAffineHom (pullback.fst G.hom t)), Set.range t = {x} ∧
    Charts.Split (H := (Over.pullback t).obj G) (C.pull (pullback.fst G.hom t)) c
def Core.HasCharts (C : Core) : Prop :=
  ∀ z : C.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (t : Sp R ⟶ C.Z) (_ : IsImmersion t),
    t (⊥ : PrimeSpectrum R) = z ∧ ∃ Ch : Charts (pullback C.GG.hom t),
    ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (x : Sp (kb p) ⟶ Sp R), x ≫ t = rPt p ≫ y →
      ∀ (h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom t) [IsAffineHom h],
        h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f → h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ x →
        ∃ d ≤ C.g, ∃ c : Fin d → Ch.Cl,
          Charts.Split (H := (Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) (Ch.pull h) c
def SplitAll {Z : Scheme.{0}} (G : Over Z) [GrpObj G] : Prop :=
  ∀ z : Z, ∃ E : SplitExt (Sp (Z.residueField z)), E.IsGt ((Over.pullback (Z.fromSpecResidueField z)).obj G)
theorem isUnit_resG_basicOpen (X : Scheme.{0}) (s : Γ(X, ⊤)) :
    IsUnit (resG X (le_top : X.basicOpen s ≤ ⊤) s) := by
  exact X.toRingedSpace.isUnit_res_basicOpen s
def Charts.ofSections (X : Scheme.{0}) [IsAffine X] {I Cl : Type} [Finite I] [Finite Cl] (wt : I → Cl) (c₀ : Cl)
    (s : I → Γ(X, ⊤)) (hs : ⨆ i : {i // wt i = c₀}, X.basicOpen (s i.1) = ⊤) : Charts X where
  I := I
  Cl := Cl
  wt := wt
  c₀ := c₀
  W := fun i => X.basicOpen (s i.1)
  aff := fun i => (isAffineOpen_top X).basicOpen (s i.1)
  cover := hs
  r := fun i j => resG X le_top (s j) * ↑(isUnit_resG_basicOpen X (s i.1)).unit⁻¹
  r_self := fun i => (isUnit_resG_basicOpen X (s i.1)).mul_val_inv
  inter := fun i i' => by
    rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)]
    erw [X.basicOpen_res (s i'.1) (homOfLE le_top).op]
    exact (inf_eq_left.2 inf_le_left).symm
  trans := fun i i' j => by
    have h := congrArg (resG X (inf_le_right : X.basicOpen (s i.1) ⊓ X.basicOpen (s i'.1) ≤ _))
      (isUnit_resG_basicOpen X (s i'.1)).mul_val_inv
    have e : ∀ (V : X.Opens) (h : X.basicOpen (s i.1) ⊓ X.basicOpen (s i'.1) ≤ V) (u : Γ(X, ⊤)),
        resG X h (resG X le_top u) = resG X le_top u := by
      intro V h u
      change (X.presheaf.map _ ≫ X.presheaf.map _).hom u = _
      rw [← X.presheaf.map_comp]
      rfl
    rw [map_mul, map_one, e] at h
    simp only [map_mul, e]
    linear_combination (-(resG X le_top (s j)) * resG X inf_le_left
      ↑(isUnit_resG_basicOpen X (s i.1)).unit⁻¹) * h
def Charts.single (X : Scheme.{0}) [IsAffine X] {J : Type} [Finite J] (f : J → Γ(X, ⊤)) : Charts X where
  I := Option J
  Cl := Option J
  wt := id
  c₀ := none
  W := fun _ => ⊤
  aff := fun _ => isAffineOpen_top X
  cover := by
    have : Nonempty {i : Option J // id i = none} := ⟨⟨none, rfl⟩⟩
    exact iSup_const
  r := fun _ j => j.elim 1 f
  r_self := by
    rintro ⟨i, hi⟩
    obtain rfl : i = none := hi
    rfl
  inter := by
    rintro i ⟨i', hi⟩
    obtain rfl : i' = none := hi
    exact (inf_idem _).trans (X.basicOpen_of_isUnit isUnit_one).symm
  trans := by
    rintro i ⟨i', hi⟩ j
    obtain rfl : i' = none := hi
    change _ = resG X _ 1 * _
    rw [map_one, _root_.one_mul]
instance isAffine_splitTorus_left (S : Scheme.{0}) [IsAffine S] (d : ℕ) :
    IsAffine (splitTorus S (Fin d → ℤ)).left :=
  have := ((splitTorus_properties S).1 (Fin d → ℤ)).1
  isAffine_of_isAffineHom (splitTorus S (Fin d → ℤ)).hom
def Charts.ofTorus (S : Scheme.{0}) [IsAffine S] (d : ℕ) : Charts (splitTorus S (Fin d → ℤ)).left :=
  Charts.single _ fun k : Fin d => (charUnit S (Fin d → ℤ) (Pi.single k 1)).val
example (X : Scheme.{0}) [IsAffine X] (f : Γ(X, ⊤)) :
    ∃ (C : Charts X) (i i' : {i // C.wt i = C.c₀}), C.W i = X.basicOpen f ∧ C.W i' = X.basicOpen (1 - f) := by
  refine ⟨Charts.ofSections X (fun _ : Bool => ()) () (fun b => if b then f else 1 - f) ?_,
    ⟨true, rfl⟩, ⟨false, rfl⟩, rfl, rfl⟩
  have h := X.basicOpen_add_le f (1 - f)
  rw [add_sub_cancel, X.basicOpen_of_isUnit isUnit_one] at h
  exact top_unique (h.trans (sup_le (le_iSup_of_le ⟨true, rfl⟩ le_rfl) (le_iSup_of_le ⟨false, rfl⟩ le_rfl)))
example (S : Scheme.{0}) [IsAffine S] (a) :
    (Charts.ofTorus S 1).r a (some 0) = (charUnit S (Fin 1 → ℤ) (Pi.single 0 1)).val := rfl
end GlobalTheory.ZJ
end


