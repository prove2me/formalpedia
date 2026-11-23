-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
-- name    : Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:50.384977+00:00
-- url     : https://prove2.me/theorems/27bddcb2-0ca0-4ab0-8d69-b4a105464c78
-- title:
--   First Cohomology Vanishes Spec Of Is Local Ring
-- statement:
--   Definitions and structural lemmas for First Cohomology Vanishes Spec Of Is Local Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/FirstCohomologyVanishesSpecOfIsLocalRing.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R : Type} [CommRing R]
abbrev rs (X : Scheme.{0}) {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom
def cst (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) : R →+* Γ(X, W) :=
  (rs X le_top).comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
def pw (H : LB X) (t : ℤ) : LB X := ⟨H.ι, H.U, fun i j => H.g i j ^ t⟩
def tw (M H : LB X) (t : ℤ) : LB X := LB.div M (pw H (-t))
def VeryAmpleBy (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) {m : ℕ} (s : Fin (m + 1) → LB.Sec H) : Prop :=
  (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
    ∃ r : Fin (m + 1) → Γ(X, nonzeroLocus (s i)),
      (∀ j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r j) *
          rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (cst f (nonzeroLocus (s i))) r)
def IsProjBy (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∃ H : LB X, H.IsLB ∧ ∃ (m : ℕ) (s : Fin (m + 1) → LB.Sec H), VeryAmpleBy f H s
def FirstCohomologyVanishes (M : LB X) : Prop :=
  ∀ (I : Type) (V : I → X.Opens) (c : I → M.ι) (hV : ∀ a, V a ≤ M.U (c a)), ⨆ a, V a = ⊤ →
    ∀ φ : ∀ a b, Γ(X, V a ⊓ V b),
      (∀ a b d, rs X (inf_le_left : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b) (φ a b) +
          rs X (le_inf ((inf_le_left.trans inf_le_left).trans (hV a)) ((inf_le_left.trans inf_le_right).trans (hV b)) :
            V a ⊓ V b ⊓ V d ≤ M.U (c a) ⊓ M.U (c b)) (M.g (c a) (c b)).val *
          rs X (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d) (φ b d) =
        rs X (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d) (φ a d)) →
      ∃ ψ : ∀ a, Γ(X, V a), ∀ a b, φ a b = rs X inf_le_left (ψ a) -
        rs X (inf_le_inf (hV a) (hV b) : V a ⊓ V b ≤ M.U (c a) ⊓ M.U (c b)) (M.g (c a) (c b)).val * rs X inf_le_right (ψ b)
theorem le_pull (M : LB X) (π : X' ⟶ X) {W : X.Opens} {i : M.ι} (h : W ≤ M.U i) :
    π ⁻¹ᵁ W ≤ (M.pull π).U (fun _ => i) := fun _ hy => Set.mem_iInter.2 fun _ => h hy
structure Perf (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X) where

  a : ℕ

  b : ℕ

  c : ℕ

  D₀ : Matrix (Fin b) (Fin a) R

  D₁ : Matrix (Fin c) (Fin b) R

  comp : D₁ * D₀ = 0

  I : Type

  W : I → X.Opens

  ch : I → M.ι

  le : ∀ i, W i ≤ M.U (ch i)

  cover : ⨆ i, W i = ⊤

  u : Fin a → ∀ i, Γ(X, W i)

  sec : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')),
    IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
    ∃ E : {v : Fin a → R' // (D₀.map g).mulVec v = 0} ≃ LB.Sec (M.pull π),
      ∀ v i, rs X' (le_pull M π (le i)) ((E v).f (fun _ => ch i)) =
        ∑ k, cst f' (π ⁻¹ᵁ W i) (v.1 k) * (π.app (W i)).hom (u k i)

  exact : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')),
    IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → FirstCohomologyVanishes (M.pull π) →
    ∀ w : Fin b → R', (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w
def Triv (M : LB X) : Prop := ∃ t : LB.Gen M, t.IsGen
theorem rs_rs {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    rs X h₂ (rs X h₁ x) = rs X (h₂.trans h₁) x := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) x = _
  rw [← Functor.map_comp]
  rfl
theorem rs_self {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)) : rs X h x = x := by
  change (X.presheaf.map (𝟙 (Opposite.op U))).hom x = x
  rw [X.presheaf.map_id]
  rfl
theorem rs_cst (f : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U) (r : R) :
    rs X h (cst f U r) = cst f V r :=
  rs_rs le_top h _
theorem firstCohomologyVanishes_of_every_cover_trivial (M : LB X)
    (hX : ∀ (I : Type) (V : I → X.Opens), ⨆ a, V a = ⊤ → ∃ a, V a = ⊤) : FirstCohomologyVanishes M := by
  intro I V c hV hc φ hφ
  obtain ⟨d, hd⟩ := hX I V hc
  have hle : ∀ U : X.Opens, U ≤ V d := fun U => hd ▸ le_top
  refine ⟨fun a => rs X (le_inf le_rfl (hle _) : V a ≤ V a ⊓ V d) (φ a d), fun a b => ?_⟩
  have h := congrArg (rs X (le_inf le_rfl (hle _) : V a ⊓ V b ≤ V a ⊓ V b ⊓ V d)) (hφ a b d)
  simp only [map_add, map_mul, rs_rs, rs_self] at h
  simp only [rs_rs]
  exact eq_sub_of_add_eq h
theorem firstCohomologyVanishes_spec_of_isLocalRing [IsLocalRing R] (M : LB (Spec (CommRingCat.of R))) : FirstCohomologyVanishes M := by
  refine firstCohomologyVanishes_of_every_cover_trivial M fun I V hc => ?_
  have hx : IsLocalRing.closedPoint R ∈ (⨆ a, V a) := by rw [hc]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨a, (IsLocalRing.closedPoint_mem_iff (V a)).1 ha⟩
theorem cst_bijective (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] {W : X.Opens} (hW : W = ⊤) :
    Function.Bijective (cst f W) := by
  subst hW
  have h₁ : Function.Bijective (rs X (le_top : (⊤ : X.Opens) ≤ ⊤)) := by
    have : ⇑(rs X (le_top : (⊤ : X.Opens) ≤ ⊤)) = id := funext fun x => rs_self _ x
    rw [this]
    exact Function.bijective_id
  have h₂ : Function.Bijective f.appTop.hom := ConcreteCategory.bijective_of_isIso (f.app ⊤)
  have h₃ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv
  exact h₁.comp (h₂.comp h₃)
def oneSec (X : Scheme.{0}) : LB.Sec (Inh.trivLB X) where
  f := fun _ => 1
  compat := fun _ _ => by
    rw [map_one, map_one, _root_.mul_one]
    rfl
theorem nonzeroLocus_oneSec (X : Scheme.{0}) : nonzeroLocus (oneSec X) = ⊤ := by
  apply top_unique
  intro x _
  simp only [nonzeroLocus, oneSec, Scheme.basicOpen_one]
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨PUnit.unit, trivial⟩
theorem veryAmpleBy_oneSec (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] :
    VeryAmpleBy f (Inh.trivLB X) (m := 0) (fun _ => oneSec X) := by
  refine ⟨by simp only [iSup_const]; exact nonzeroLocus_oneSec X, fun _ => ⟨?_, fun _ => 1, ?_, ?_⟩⟩
  · rw [nonzeroLocus_oneSec]
    have : IsAffine X := isAffine_of_isAffineHom f
    exact isAffineOpen_top X
  · intro j k
    rw [map_one, _root_.one_mul]
  · intro p
    obtain ⟨a, rfl⟩ := (cst_bijective f (nonzeroLocus_oneSec X)).2 p
    exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
theorem isProjBy_of_isIso (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] : IsProjBy f :=
  ⟨Inh.trivLB X, Inh.trivLB_isLB X, 0, fun _ => oneSec X, veryAmpleBy_oneSec f⟩
theorem isProjBy_id (R : Type) [CommRing R] : IsProjBy (𝟙 (Spec (CommRingCat.of R))) :=
  isProjBy_of_isIso _
theorem pull_trivLB_U (π : X' ⟶ X) (j : ((Inh.trivLB X).pull π).ι) :
    ((Inh.trivLB X).pull π).U j = ⊤ :=
  top_unique fun _ _ => Set.mem_iInter.2 fun _ => trivial
def cstSec (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R)) (r : R) :
    LB.Sec ((Inh.trivLB X).pull π) where
  f := fun j => cst f' _ r
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_cst f' _ r).trans (rs_cst f' _ r).symm
theorem cstSec_bijective (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R)) [IsIso f'] :
    Function.Bijective (cstSec π f') := by
  let j₀ : ((Inh.trivLB X).pull π).ι := fun _ => PUnit.unit
  have hb := cst_bijective f' (pull_trivLB_U π j₀)
  refine ⟨fun r r' h => hb.1 (congrArg (fun s => s.f j₀) h), fun s => ?_⟩
  obtain ⟨r, hr⟩ := hb.2 (s.f j₀)
  refine ⟨r, ?_⟩
  obtain ⟨sf, hs⟩ := s
  have : (fun j => cst f' (((Inh.trivLB X).pull π).U j) r) = sf := funext fun _ => hr
  subst this
  rfl
def perfTriv (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] : Perf f (Inh.trivLB X) where
  a := 1
  b := 0
  c := 0
  D₀ := 0
  D₁ := 0
  comp := Subsingleton.elim _ _
  I := PUnit
  W := fun _ => ⊤
  ch := fun _ => PUnit.unit
  le := fun _ => le_rfl
  cover := iSup_const
  u := fun _ _ => 1
  sec := fun R' _ g X' π f' h => by
    haveI : IsIso f' := h.isIso_snd_of_isIso
    refine ⟨((Equiv.subtypeUnivEquiv fun _ => Subsingleton.elim _ _).trans
      (Equiv.funUnique (Fin 1) R')).trans (Equiv.ofBijective _ (cstSec_bijective π f')), ?_⟩
    intro v i
    rw [Fin.sum_univ_one, map_one, _root_.mul_one]
    exact rs_cst f' _ _
  exact := fun R' _ g X' π f' _ _ w _ => ⟨0, Subsingleton.elim _ _⟩
example (R : Type) [CommRing R] :
    Nonempty (Perf (𝟙 (Spec (CommRingCat.of R))) (Inh.trivLB _)) := ⟨perfTriv _⟩
example (R : Type) [CommRing R] : (perfTriv (𝟙 (Spec (CommRingCat.of R)))).a = 1 := rfl
example : IsProjBy (𝟙 (Spec (CommRingCat.of ℤ))) := isProjBy_id ℤ
example : FirstCohomologyVanishes (Inh.trivLB (Spec (CommRingCat.of ℚ))) := firstCohomologyVanishes_spec_of_isLocalRing _
end GlobalTheory.AbLaw


