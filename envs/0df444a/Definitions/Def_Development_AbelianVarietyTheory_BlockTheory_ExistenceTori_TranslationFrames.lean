-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_TranslationFrames
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_TranslationFrames
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:40.800861+00:00
-- url     : https://prove2.me/theorems/01da8437-5a3e-46fe-8149-596e4bbfe7d6
-- title:
--   Translation Frames
-- statement:
--   Definitions and structural lemmas for Translation Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/TranslationFrames.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslationFrames
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
abbrev MulIso (L : LB A.left) (N : ℕ) : Type :=
  LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1])
abbrev FrameAt (L : LB A.left) (k : ℤ) {T : Over S} (x : T ⟶ A) : Type :=
  LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => k))
theorem comp_mulA {T : Over S} (x : T ⟶ A) (N : ℕ) : x ≫ mulA A N = x ^ N := by
  induction N with
  | zero => simp [mulA, MonObj.comp_one]
  | succ n ih =>
    have ih' : x ≫ 𝟙 A ^ n = x ^ n := ih
    simp only [mulA, pow_succ, MonObj.comp_mul, ih', Category.comp_id]
theorem mulIsoT_le (L : LB A.left) (N : ℕ) (T : Over S) (j : Fin 2 → L.ι) :
    LB.wchart L ![(snd T A).left, (snd T A ^ N).left] j ≤
      (snd T A).left ⁻¹ᵁ LB.wchart L ![𝟙 A.left, (mulA A N).left] j := by
  intro y hy
  have h0 : (snd T A).left.base y ∈ (L.U (j 0) : Set A.left) := Set.mem_iInter.1 hy 0
  have h1 : (snd T A ^ N).left.base y ∈ (L.U (j 1) : Set A.left) := Set.mem_iInter.1 hy 1
  have e : (snd T A).left ≫ (mulA A N).left = (snd T A ^ N).left := by
    rw [← Over.comp_left, comp_mulA]
  rw [← e] at h1
  refine Set.mem_iInter.2 fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
def mulIsoT (L : LB A.left) (N : ℕ) (α : MulIso A L N) (T : Over S) :
    LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]) where
  s := fun j => res (mulIsoT_le A L N T j) (pullU (snd T A).left _ (α.s j))
theorem one_left (T : Over S) : (1 : T ⟶ A).left = T.hom ≫ eSec A := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  rfl
theorem originFrame_le (L : LB A.left) (T : Over S) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => (1 : T ⟶ A).left) j ≤
      LB.wchart L (fun _ : Fin 1 => T.hom ≫ eSec A) j :=
  le_of_eq (by rw [one_left])
def originFrame (L : LB A.left) (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (T : Over S) :
    FrameAt A L k (1 : T ⟶ A) where
  s := fun j => res (originFrame_le A L T j) ((rigT A L rig T k).s j)
def pullFrame (L : LB A.left) (k : ℤ) {T T' : Over S} (π : T' ⟶ T) (x : T ⟶ A)
    (τ : FrameAt A L k x) : FrameAt A L k (π ≫ x) :=
  LB.pullGen L _ _ τ π.left
def IsOddSymLift (L : LB A.left) (k : ℤ) {T : Over S} (x : T ⟶ A) (U : ThetaGrp A L k T) : Prop :=
  ∃ M : ℕ, Odd M ∧ x ^ M = 1 ∧ SymLift A L k M x U
def IsRigMulIso (L : RigLB A) (N : ℕ) (α : MulIso A L.L N) : Prop :=
  α.IsGen ∧ IsNormMul A L.L L.rig N α
def IsActMulPull (L : LB A.left) (N : ℕ) (α : MulIso A L N) {T : Over S}
    (U : ThetaGrp A L ((N : ℤ) ^ 2) T) (s : LB.Sec (LPow A L 1 T))
    (F : LB.Sec (LPow A L ((N : ℤ) ^ 2) T)) : Prop :=
  ∃ s₁ : LB.Sec (LPow A L ((N : ℤ) ^ 2) T),
    IsTwistPull A L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 (mulIsoT A L N α T) s s₁ ∧
    IsActOf A L ((N : ℤ) ^ 2) U s₁ F
def IsActMulFrame (L : RigLB A) (N : ℕ) (α : MulIso A L.L N) {T : Over S}
    (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T) (t : T ⟶ A) (τ : FrameAt A L.L 1 t) : Prop :=
  U.pt ^ N = t ∧ τ.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _
      (LB.mulGen L.L _ _ _ _
        (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ U.φ (ptSecT A 1).left)
          (LB.pullGen L.L _ _ α U.pt.left)) τ)
      (rigT A L.L L.rig T ((N : ℤ) ^ 2))
def IsTranslPullAt [IsCommMonObj A] (L : RigLB A) (N : ℕ) {T : Over S} (t t' : T ⟶ A)
    (s : LB.Sec (LPow A L.L 1 T)) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  Odd N ∧ t' ^ N = t ∧
    ∃ (α : MulIso A L.L N) (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
      IsRigMulIso A L N α ∧ IsOddSymLift A L.L ((N : ℤ) ^ 2) t' U ∧ IsActMulPull A L.L N α U s F
def IsTranslFrameAt [IsCommMonObj A] (L : RigLB A) (N : ℕ) {T : Over S} (t t' : T ⟶ A)
    (τ : FrameAt A L.L 1 t) : Prop :=
  Odd N ∧ t' ^ N = t ∧
    ∃ (α : MulIso A L.L N) (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
      IsRigMulIso A L N α ∧ IsOddSymLift A L.L ((N : ℤ) ^ 2) t' U ∧ IsActMulFrame A L N α U t τ
def IsTranslPullOver [IsCommMonObj A] (L : RigLB A) (N : ℕ) (C : ∀ T : Over S, (T ⟶ A) → Prop)
    {T : Over S} (t : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T))
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  ∃ t' : T ⟶ A, C T t' ∧ IsTranslPullAt A L N t t' s F
def IsTranslFrameOver [IsCommMonObj A] (L : RigLB A) (N : ℕ) (C : ∀ T : Over S, (T ⟶ A) → Prop)
    {T : Over S} (t : T ⟶ A) (τ : FrameAt A L.L 1 t) : Prop :=
  ∃ t' : T ⟶ A, C T t' ∧ IsTranslFrameAt A L N t t' τ
def IsTranslPull [IsCommMonObj A] (L : RigLB A) (N : ℕ) (C : ∀ T : Over S, (T ⟶ A) → Prop)
    {T : Over S} (t : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T))
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  Odd N ∧ ∀ p : T.left, ∃ (T' : Over S) (π : T' ⟶ T), Etale π.left ∧ (∃ q : T'.left, π.left.base q = p) ∧
    ∃ (s' : LB.Sec (LPow A L.L 1 T')) (F' : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T')),
      IsPullSec A L.L 1 (π ▷ A) (whiskerRight_snd _ _) s s' ∧
      IsPullSec A L.L ((N : ℤ) ^ 2) (π ▷ A) (whiskerRight_snd _ _) F F' ∧
      IsTranslPullOver A L N C (π ≫ t) s' F'
def IsTranslFrame [IsCommMonObj A] (L : RigLB A) (N : ℕ) (C : ∀ T : Over S, (T ⟶ A) → Prop)
    {T : Over S} (t : T ⟶ A) (τ : FrameAt A L.L 1 t) : Prop :=
  Odd N ∧ τ.IsGen ∧
    ∀ p : T.left, ∃ (T' : Over S) (π : T' ⟶ T), Etale π.left ∧ (∃ q : T'.left, π.left.base q = p) ∧
      IsTranslFrameOver A L N C (π ≫ t) (pullFrame A L.L 1 π t τ)
def ValueNamedSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  ∀ (N : ℕ) (α : MulIso A L.L N), α.IsGen → ∀ {T : Over S} (U : ThetaGrp A L.L ((N : ℤ) ^ 2) T)
    (t : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T)) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T))
    (τ : FrameAt A L.L 1 t), IsActMulPull A L.L N α U s F → IsActMulFrame A L N α U t τ →
    ∀ v : Γ(T.left, ⊤),
      IsValueAt A L.L ((N : ℤ) ^ 2) F 1 (originFrame A L.L L.rig ((N : ℤ) ^ 2) T) v ↔
        IsValueAt A L.L 1 s t τ v
def ValueSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  IsAbelianScheme A → ∀ (N : ℕ) {T : Over S} (t t' : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T))
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (τ : FrameAt A L.L 1 t),
    IsTranslPullAt A L N t t' s F → IsTranslFrameAt A L N t t' τ →
    ∀ v : Γ(T.left, ⊤),
      IsValueAt A L.L ((N : ℤ) ^ 2) F 1 (originFrame A L.L L.rig ((N : ℤ) ^ 2) T) v ↔
        IsValueAt A L.L 1 s t τ v
def OddSymLiftSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  IsAbelianScheme A → Sym A L.L → ∀ (k : ℤ) {T : Over S} (x : T ⟶ A) (M : ℕ), Odd M → x ^ M = 1 →
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : ThetaGrp A L.L k (overRes V), θ.pt = overResι V ≫ x) →
    ∃ U : ThetaGrp A L.L k T, SymLift A L.L k M x U ∧
      ∀ U' : ThetaGrp A L.L k T, IsOddSymLift A L.L k x U' → U' = U
def DescentFixSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  IsAbelianScheme A → Sym A L.L → ∀ (N : ℕ) (α : MulIso A L.L N), IsRigMulIso A L N α →
    ∀ {T : Over S} (x : T ⟶ A) (s : LB.Sec (LPow A L.L 1 T))
      (s₁ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)), Odd N → x ^ N = 1 →
      IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1
        (mulIsoT A L.L N α T) s s₁ →
      IsTranslPullAt A L N 1 x s s₁
def FreeOfDivisionSt [IsCommMonObj A] (L : RigLB A) : Prop :=
  IsAbelianScheme A → Sym A L.L → ∀ (N : ℕ) {T : Over S} (t t₁ t₂ : T ⟶ A),
    WeilIs A L.L ((N : ℤ) ^ 2) t₁ t₂ 1 →
    (∀ (s : LB.Sec (LPow A L.L 1 T)) (F₁ F₂ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)),
      IsTranslPullAt A L N t t₁ s F₁ → IsTranslPullAt A L N t t₂ s F₂ → F₁ = F₂) ∧
    ∀ τ₁ τ₂ : FrameAt A L.L 1 t,
      IsTranslFrameAt A L N t t₁ τ₁ → IsTranslFrameAt A L N t t₂ τ₂ → τ₁ = τ₂
end GlobalTheory.IndefiniteRowSideFullHecke.TranslationFrames


