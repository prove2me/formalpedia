-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_EndomorphismPullbackRigid
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_EndomorphismPullbackRigid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:50.184091+00:00
-- url     : https://prove2.me/theorems/a7475700-41d2-43a4-9f25-5eb27a955f7a
-- title:
--   Endomorphism Pullback Rigid
-- statement:
--   Definitions and structural lemmas for Endomorphism Pullback Rigid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/EndomorphismPullbackRigid.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {A : Over X}
abbrev PullPow (L : LB A.left) {Z : Over X} (x : Z ⟶ A) (k : ℤ) : LB Z.left :=
  LB.LinComb L (K := Fin 1) (fun _ => x.left) (fun _ => k)
abbrev PowOver (L : LB A.left) (k : ℤ) (T : Over X) : LB (T ⊗ A).left :=
  PullPow L (snd T A) k
def Lands (L : LB A.left) {W : Over X} (v : W ⟶ A) (i : L.ι) : Prop :=
  ⊤ ≤ v.left ⁻¹ᵁ L.U i
lemma Lands.le_wchart {L : LB A.left} {W Z : Over X} {x : Z ⟶ A} {p : W ⟶ Z} {v : W ⟶ A}
    (hv : p ≫ x = v) {i : L.ι} (h : Lands L v i) :
    ⊤ ≤ p.left ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => x.left) (fun _ => i) := by
  subst hv
  intro y hy
  exact Set.mem_iInter.2 fun _ => h hy
def secVal {L : LB A.left} {k : ℤ} {T W : Over X} (s : LB.Sec (PowOver L k T)) (t : W ⟶ T)
    (v : W ⟶ A) (i : L.ι) (hi : Lands L v i) : Γ(W.left, ⊤) :=
  ((lift t v).left.appLE _ ⊤ (Lands.le_wchart (lift_snd t v) hi)).hom (s.f fun _ => i)
def isoVal {L : LB A.left} {a b : ℤ} {T W : Over X} {f : T ⊗ A ⟶ A}
    (w : LB.Iso (PullPow L f b) (PowOver L a T)) (t : W ⟶ T) (v u : W ⟶ A)
    (hu : lift t v ≫ f = u) (i j : L.ι) (hi : Lands L v i) (hj : Lands L u j) : Γ(W.left, ⊤)ˣ :=
  Units.map ((lift t v).left.appLE
      ((LB.div (PowOver L a T) (PullPow L f b)).U (fun _ => i, fun _ => j)) ⊤
      (fun _ hy => ⟨Lands.le_wchart (lift_snd t v) hi hy, Lands.le_wchart hu hj hy⟩)).hom.toMonoidHom
    (w.s (fun _ => i, fun _ => j))
def Carries {L : LB A.left} {a b : ℤ} {T : Over X} {f : T ⊗ A ⟶ A}
    (w : LB.Iso (PullPow L f b) (PowOver L a T)) (s : LB.Sec (PowOver L b T))
    (s' : LB.Sec (PowOver L a T)) : Prop :=
  ∀ (W : Over X) (t : W ⟶ T) (v : W ⟶ A) (i j : L.ι) (hi : Lands L v i)
    (hj : Lands L (lift t v ≫ f) j),
    secVal s' t v i hi = (isoVal w t v _ rfl i j hi hj : Γ(W.left, ⊤)) * secVal s t _ j hj
variable [GrpObj A] [IsCommMonObj A]
def rigVal (L : RigLB A) (W : Over X) (i : L.L.ι) (hi : Lands L.L (1 : W ⟶ A) i) :
    Γ(W.left, ⊤)ˣ :=
  Units.map ((toUnit W).left.appLE
      (LB.wchart L.L (K := PUnit) (fun _ => eSec A) (fun _ => i)) ⊤
      (fun _ hy => Set.mem_iInter.2 fun _ => hi hy)).hom.toMonoidHom
    (L.rig.s fun _ => i)
lemma origin_comp {T W : Over X} (t : W ⟶ T) (φ : A ⟶ A) [IsMonHom φ] :
    lift t (1 : W ⟶ A) ≫ snd T A ≫ φ = 1 := by
  rw [lift_snd_assoc, Hom.one_def, Category.assoc, IsMonHom.one_hom]
def IsNormalisedIso (L : RigLB A) (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ) (T : Over X)
    (w : LB.Iso (PullPow L.L (snd T A ≫ φ) b) (PowOver L.L a T)) : Prop :=
  w.IsGen ∧
  ∀ (W : Over X) (t : W ⟶ T) (i j : L.L.ι) (hi : Lands L.L (1 : W ⟶ A) i)
    (hj : Lands L.L (1 : W ⟶ A) j),
    rigVal L W i hi ^ a = isoVal w t 1 1 (origin_comp t φ) i j hi hj * rigVal L W j hj ^ b
def IsEndPull (L : RigLB A) (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ) {T : Over X}
    (s : LB.Sec (PowOver L.L b T)) (s' : LB.Sec (PowOver L.L a T)) : Prop :=
  ∃ w : LB.Iso (PullPow L.L (snd T A ≫ φ) b) (PowOver L.L a T),
    IsNormalisedIso L φ a b T w ∧ Carries w s s'
def transl {T : Over X} (b : T ⟶ A) : T ⊗ A ⟶ A := snd T A * (fst T A ≫ b)
lemma lift_transl {T W : Over X} (b : T ⟶ A) (t : W ⟶ T) (v : W ⟶ A) :
    lift t v ≫ transl b = v * (t ≫ b) := by
  rw [transl, comp_mul, lift_snd, lift_fst_assoc]
lemma lift_neg {T W : Over X} (t : W ⟶ T) (v : W ⟶ A) :
    lift t v ≫ snd T A ≫ ι[A] = v⁻¹ := by
  rw [lift_snd_assoc, Hom.inv_def]
abbrev Lift (L : LB A.left) (k : ℤ) {T : Over X} (b : T ⟶ A) : Type :=
  LB.Iso (PullPow L (transl b) k) (PowOver L k T)
def PowEqOne {L : LB A.left} {k : ℤ} {T : Over X} {b : T ⟶ A} (U : Lift L k b) (N : ℕ) : Prop :=
  ∀ (W : Over X) (t : W ⟶ T) (v : W ⟶ A) (c : ℕ → L.ι)
    (hc : ∀ m, Lands L (v * (t ≫ b) ^ m) (c m)), c N = c 0 →
    ∏ m ∈ Finset.range N, isoVal U t (v * (t ≫ b) ^ m) (v * (t ≫ b) ^ (m + 1))
      (by rw [lift_transl, pow_succ, _root_.mul_assoc]) (c m) (c (m + 1)) (hc m) (hc (m + 1)) = 1
def IsSymmetricLift {L : LB A.left} {k : ℤ} {T : Over X} {b : T ⟶ A}
    (J : LB.Iso (PullPow L (snd T A ≫ ι[A]) k) (PowOver L k T)) (U : Lift L k b) : Prop :=
  ∀ (W : Over X) (t : W ⟶ T) (v : W ⟶ A) (i j l m : L.ι) (hi : Lands L v i)
    (hj : Lands L (v * (t ≫ b)) j) (hl : Lands L (v * (t ≫ b))⁻¹ l) (hm : Lands L v⁻¹ m),
    isoVal U t v _ (lift_transl b t v) i j hi hj *
      isoVal J t _ _ (lift_neg t _) j l hj hl *
      isoVal U t _ _ (by rw [lift_transl, mul_inv_rev, mul_comm (t ≫ b)⁻¹, inv_mul_cancel_right])
        l m hl hm =
    isoVal J t v _ (lift_neg t v) i m hi hm
def IsSymTranslate (L : RigLB A) (N : ℕ) {T : Over X} (b : T ⟶ A)
    (s s' : LB.Sec (PowOver L.L N T)) : Prop :=
  Odd N ∧ b ^ N = 1 ∧
  ∃ (J : LB.Iso (PullPow L.L (snd T A ≫ ι[A]) N) (PowOver L.L N T)) (U : Lift L.L N b),
    IsNormalisedIso L ι[A] N N T J ∧ U.IsGen ∧ IsSymmetricLift J U ∧ PowEqOne U N ∧
      Carries U s s'
def IsTranslatedPull (L : RigLB A) (φ : A ⟶ A) [IsMonHom φ] (N : ℕ) {T : Over X} (b : T ⟶ A)
    (s : LB.Sec (PowOver L.L 1 T)) (hh : LB.Sec (PowOver L.L N T)) : Prop :=
  ∃ s₀ : LB.Sec (PowOver L.L N T), IsEndPull L φ N 1 s s₀ ∧ IsSymTranslate L N b s₀ hh
def trivL (Y : Scheme.{0}) : LB Y := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
lemma linComb_trivL_g {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ Y)) (ε : K → ℤ)
    (j j') : (LB.LinComb (trivL Y) φ ε).g j j' = 1 :=
  Finset.prod_eq_one fun k _ => by
    have h : pullU (φ k) _ ((trivL Y).g (j k) (j' k)) = 1 := map_one _
    rw [h]
    exact (congrArg (· ^ ε k) (map_one _)).trans (one_zpow _)
def trivRig (A : Over X) [GrpObj A] : RigLB A where
  L := trivL A.left
  rig := ⟨fun _ => 1⟩
  isLB := ⟨by simp [trivL], fun _ => map_one _, fun _ _ _ =>
    (congrArg₂ (· * ·) (map_one _) (map_one _)).trans ((_root_.one_mul _).trans (map_one _).symm)⟩
  rigGen := fun _ _ => by rw [linComb_trivL_g, map_one, map_one, _root_.one_mul]
def trivOne (k : ℤ) (T : Over X) : LB.Sec (PowOver (trivRig A).L k T) where
  f := fun _ => 1
  compat := fun i j => by
    have h : (PowOver (trivRig A).L k T).g i j = 1 := linComb_trivL_g _ _ _ _
    rw [h, map_one, map_one, Units.val_one, _root_.one_mul]
def trivIso {T : Over X} (f : T ⊗ A ⟶ A) (a b : ℤ) :
    LB.Iso (PullPow (trivRig A).L f b) (PowOver (trivRig A).L a T) := ⟨fun _ => 1⟩
end
end GlobalTheory.IndefiniteRowSideFullHecke.EndomorphismPullbackRigid


