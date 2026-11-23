-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FirstOrderRigidityLevel
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_FirstOrderRigidityLevel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:13.146335+00:00
-- url     : https://prove2.me/theorems/322bea00-31cc-411c-875a-665cd70b4039
-- title:
--   First Order Rigidity Level
-- statement:
--   Definitions and structural lemmas for First Order Rigidity Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/FirstOrderRigidityLevel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel
abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)
def Conv (g n k : ℕ) : Prop :=
  n.Prime ∧ Odd n ∧ 2 ≤ k ∧ 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < (((n ^ k) ^ 2 : ℕ) : ℝ)
abbrev bigN (n k j : ℕ) : ℕ := n ^ j * (n ^ k) ^ 2
abbrev Lab (g M : ℕ) : Type := Fin (2 * g) → ZMod M
abbrev SubLab (g M r : ℕ) : Type := {a : Lab g M // r • a = 0}
section General
variable {S : Scheme.{0}}
def lab {P : PolAV S} {g M : ℕ} {ze : Γ(S, ⊤)ˣ} (hg : P.g = g) (lev : Level P M ze) (c : Lab g M) :
    baseOver S ⟶ P.A :=
  lev.toPt fun i => c (Fin.cast (by rw [hg]) i)
def IsThetaPoint {P : PolAV S} {g : ℕ} (r : ℕ) {ze : Γ(S, ⊤)ˣ} (hg : P.g = g)
    (lev : Level P (r ^ 2) ze) (v : Lab g (r ^ 2) → Γ(S, ⊤)) : Prop :=
  IsThetaPt P r (T := baseOver S) (lab hg lev) v
def IsCoord {P : PolAV S} {g M : ℕ} (m : ℕ) {ze : Γ(S, ⊤)ˣ} (hg : P.g = g) (lev : Level P M ze)
    (s : SubLab g M (m ^ 2) → LB.Sec (LPow P.A P.L ((m : ℤ) ^ 2) (baseOver S))) : Prop :=
  ∃ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))) (s₁ : LB.Sec (LPow P.A P.L ((m : ℤ) ^ 2) (baseOver S)))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2)
      ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left] ![(m : ℤ) ^ 2, -1]))
    (U : SubLab g M (m ^ 2) → ThetaGrp P.A P.L ((m : ℤ) ^ 2) (baseOver S)),
    IsGenSec P.A P.L 1 th ∧ α.IsGen ∧
    IsTwistPull P.A P.L (mulT P.A (baseOver S) m) (snd (baseOver S) P.A ^ m) (lift_snd _ _)
      ((m : ℤ) ^ 2) 1 α th s₁ ∧
    (∀ a, SymLift P.A P.L ((m : ℤ) ^ 2) (m ^ 2) (lab hg lev a.1) (U a)) ∧
    ∀ a, IsActOf P.A P.L ((m : ℤ) ^ 2) (U a) s₁ (s a)
def IsPolIso {P₁ P₂ : PolAV S} (f : P₁.A ≅ P₂.A) : Prop :=
  IsMonHom f.hom ∧ ∃ t : LB.Iso (P₂.L.pull f.hom.left) P₁.L, t.IsGen
def IsBaseChange {S' : Scheme.{0}} (f : S' ⟶ S) {P : PolAV S} {P' : PolAV S'} {g M : ℕ}
    {ze : Γ(S, ⊤)ˣ} {ze' : Γ(S', ⊤)ˣ} (hg : P.g = g) (lev : Level P M ze) (hg' : P'.g = g)
    (lev' : Level P' M ze') (π : P'.A.left ⟶ P.A.left) : Prop :=
  ∃ hπ : IsPullback π P'.A.hom P.A.hom f,
    (∀ (T : Over S') (x y : T ⟶ P'.A), toBase hπ.w (x * y) = toBase hπ.w x * toBase hπ.w y) ∧
    (∃ t : LB.Iso (P.L.pull π) P'.L, t.IsGen) ∧
    f.appTop.hom (ze : Γ(S, ⊤)) = (ze' : Γ(S', ⊤)) ∧
    ∀ c : Lab g M, (lab hg' lev' c).left ≫ π = f ≫ (lab hg lev c).left
end General
section Forms
variable {R : Type} [CommRing R] {P : PolAV (Sp R)} {I : Type} {e : ℤ}
def evalForm (s : I → LB.Sec (LPow P.A P.L e (baseOver (Sp R)))) (F : MvPolynomial I R)
    (j : Fin 1 → P.L.ι) :
    Γ((baseOver (Sp R) ⊗ P.A).left, (LPow P.A P.L e (baseOver (Sp R))).U j) :=
  MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (baseOver (Sp R) ⊗ P.A).hom _) (fun a => (s a).f j) F
def Vanishes (s : I → LB.Sec (LPow P.A P.L e (baseOver (Sp R)))) (F : MvPolynomial I R) : Prop :=
  ∀ j, evalForm s F j = 0
def CutOutInDegree (s : I → LB.Sec (LPow P.A P.L e (baseOver (Sp R)))) (d₀ : ℕ) : Prop :=
  ∀ (d : ℕ) (G : MvPolynomial I R), G.IsHomogeneous d → Vanishes s G → ∀ a : I, ∃ l : ℕ,
    MvPolynomial.X a ^ l * G ∈ Ideal.span {F : MvPolynomial I R | F.IsHomogeneous d₀ ∧ Vanishes s F}
def HomogeneousFormsSurjectFromDegree (s : I → LB.Sec (LPow P.A P.L e (baseOver (Sp R)))) (d₀ : ℕ) : Prop :=
  ∀ d : ℕ, d₀ ≤ d → ∀ σ : LB.Sec (LPow P.A P.L (e * d) (baseOver (Sp R))),
    ∃ F : MvPolynomial I R, F.IsHomogeneous d ∧ ∀ j, σ.f j = evalForm s F j
end Forms
section Norm
variable {K : Type} [Field K] (P : PolAV (Sp K))
def HasTrace (ψ : P.A ⟶ P.A) (t : ℤ) : Prop :=
  ∀ M : ℕ, (M : K) ≠ 0 → ∀ y : Fin (2 * P.g) → (baseOver (Sp K) ⟶ P.A), (∀ i, y i ^ M = 1) →
    (∀ z : baseOver (Sp K) ⟶ P.A, z ^ M = 1 → ∃ c : Fin (2 * P.g) → ℕ, linComb y c = z) →
    ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) ℕ,
      (∀ i, y i ≫ ψ = linComb y fun l => B l i) → ((B.trace : ℕ) : ZMod M) = (t : ZMod M)
def RosatiNormLE (φ : P.A ⟶ P.A) (b : ℕ) : Prop :=
  ∃ φ' : P.A ⟶ P.A, IsMonHom φ' ∧ RosatiAdj P.A P.L φ φ' ∧ ∃ t : ℤ, HasTrace P (φ' ≫ φ) t ∧ t ≤ b
end Norm
def CoordTheta : Prop :=
  ∀ g n k j : ℕ, Conv g n k →
    ∃ ρ : SubLab g (bigN n k j ^ 2) ((n ^ k) ^ 2) → SubLab g (bigN n k j ^ 2) (bigN n k j) →
        Lab g (bigN n k j ^ 2) → ℕ,
      ∀ (R : Type) [CommRing R] [IsLocalRing R], IsUnit (n : R) →
        ∀ (P : PolAV (Sp R)) (hg : P.g = g) (ze : Γ(Sp R, ⊤)ˣ) (lev : Level P (bigN n k j ^ 2) ze)
          (v : Lab g (bigN n k j ^ 2) → Γ(Sp R, ⊤)), IsThetaPoint (bigN n k j) hg lev v →
        ∀ s, IsCoord (n ^ k) hg lev s →
        ∀ (b : SubLab g (bigN n k j ^ 2) (bigN n k j))
          (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1)
            (fun _ => (lab hg lev b.1).left) (fun _ => ((n ^ k : ℕ) : ℤ) ^ 2)))
          (w : SubLab g (bigN n k j ^ 2) ((n ^ k) ^ 2) → Γ(Sp R, ⊤)), τ.IsGen →
          (∀ a, IsValueAt P.A P.L (((n ^ k : ℕ) : ℤ) ^ 2) (s a) (lab hg lev b.1) τ (w a)) →
          ∃ u : Γ(Sp R, ⊤)ˣ, ∀ (a : SubLab g (bigN n k j ^ 2) ((n ^ k) ^ 2)) (c : Lab g (bigN n k j ^ 2)),
            bigN n k j • c = (n ^ k) • (a.1 + b.1) →
            w a = (u : Γ(Sp R, ⊤)) * (ze : Γ(Sp R, ⊤)) ^ ρ a b c * v c
def ThetaDetermines : Prop :=
  ∀ g n k : ℕ, Conv g n k → ∃ B : ℕ, ∀ j : ℕ, B < bigN n k j →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (n : K) ≠ 0 → ∀ (ze : Γ(Sp K, ⊤)ˣ)
      (P₁ : PolAV (Sp K)) (h₁ : P₁.g = g) (lev₁ : Level P₁ (bigN n k j ^ 2) ze)
      (P₂ : PolAV (Sp K)) (h₂ : P₂.g = g) (lev₂ : Level P₂ (bigN n k j ^ 2) ze)
      (v : Lab g (bigN n k j ^ 2) → Γ(Sp K, ⊤)),
      IsThetaPoint (bigN n k j) h₁ lev₁ v → IsThetaPoint (bigN n k j) h₂ lev₂ v →
      ∃ f : P₁.A ≅ P₂.A, IsPolIso f ∧
        ∀ b : SubLab g (bigN n k j ^ 2) (bigN n k j), lab h₁ lev₁ b.1 ≫ f.hom = lab h₂ lev₂ b.1
def LevelSqDetermined : Prop :=
  ∀ g n k j : ℕ, Conv g n k →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (n : K) ≠ 0 → ∀ (ze : Γ(Sp K, ⊤)ˣ)
      (P : PolAV (Sp K)) (h : P.g = g) (lev₁ lev₂ : Level P (bigN n k j ^ 2) ze)
      (v : Lab g (bigN n k j ^ 2) → Γ(Sp K, ⊤)),
      (∀ b : SubLab g (bigN n k j ^ 2) (bigN n k j), lab h lev₁ b.1 = lab h lev₂ b.1) →
      IsThetaPoint (bigN n k j) h lev₁ v → IsThetaPoint (bigN n k j) h lev₂ v →
      ∀ c, lab h lev₁ c = lab h lev₂ c
def ThetaDeterminesLevel : Prop :=
  ∀ g n k : ℕ, Conv g n k → ∃ B : ℕ, ∀ j : ℕ, B < bigN n k j →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (n : K) ≠ 0 → ∀ (ze : Γ(Sp K, ⊤)ˣ)
      (P₁ : PolAV (Sp K)) (h₁ : P₁.g = g) (lev₁ : Level P₁ (bigN n k j ^ 2) ze)
      (P₂ : PolAV (Sp K)) (h₂ : P₂.g = g) (lev₂ : Level P₂ (bigN n k j ^ 2) ze)
      (v : Lab g (bigN n k j ^ 2) → Γ(Sp K, ⊤)),
      IsThetaPoint (bigN n k j) h₁ lev₁ v → IsThetaPoint (bigN n k j) h₂ lev₂ v →
      ∃ f : P₁.A ≅ P₂.A, IsPolIso f ∧ ∀ c, lab h₁ lev₁ c ≫ f.hom = lab h₂ lev₂ c
def EndDeterminedOnTorsion : Prop :=
  ∀ g b : ℕ, ∃ B : ℕ, ∀ r : ℕ, B < r →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (r : K) ≠ 0 → ∀ (P : PolAV (Sp K)), P.g = g →
      ∀ φ ψ : P.A ⟶ P.A, IsMonHom φ → IsMonHom ψ → RosatiNormLE P φ b → RosatiNormLE P ψ b →
        (∀ y : baseOver (Sp K) ⟶ P.A, y ^ r = 1 → y ≫ φ = y ≫ ψ) → φ = ψ
def ThetaDeterminesAction : Prop :=
  ∀ (O : Type) [Ring O] [StarRing O] [Module.Finite ℤ O] (g n k : ℕ), Conv g n k →
    ∃ B : ℕ, ∀ j : ℕ, B < bigN n k j →
    ∀ (ν : O → SubLab g (bigN n k j ^ 2) (bigN n k j) → SubLab g (bigN n k j ^ 2) (bigN n k j))
      (K : Type) [Field K] [IsAlgClosed K], (n : K) ≠ 0 → ∀ (ze : Γ(Sp K, ⊤)ˣ)
      (P₁ : PolAV (Sp K)) (h₁ : P₁.g = g) (lev₁ : Level P₁ (bigN n k j ^ 2) ze) (ι₁ : P₁.OAct O)
      (P₂ : PolAV (Sp K)) (h₂ : P₂.g = g) (lev₂ : Level P₂ (bigN n k j ^ 2) ze) (ι₂ : P₂.OAct O)
      (v : Lab g (bigN n k j ^ 2) → Γ(Sp K, ⊤)),
      (∀ a b, lab h₁ lev₁ b.1 ≫ ι₁.act a = lab h₁ lev₁ (ν a b).1) →
      (∀ a b, lab h₂ lev₂ b.1 ≫ ι₂.act a = lab h₂ lev₂ (ν a b).1) →
      IsThetaPoint (bigN n k j) h₁ lev₁ v → IsThetaPoint (bigN n k j) h₂ lev₂ v →
      ∃ f : P₁.A ≅ P₂.A, IsPolIso f ∧ (∀ c, lab h₁ lev₁ c ≫ f.hom = lab h₂ lev₂ c) ∧
        ∀ a, ι₁.act a ≫ f.hom = f.hom ≫ ι₂.act a
def redMap (K : Type) [Field K] : Sp K ⟶ Sp (DualNumber K) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
def strMap (K : Type) [Field K] : Sp (DualNumber K) ⟶ Sp K :=
  Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))
def RigidAt {K : Type} [Field K] {g : ℕ} (m r : ℕ) {P : PolAV (Sp K)} {ze : Γ(Sp K, ⊤)ˣ} (h : P.g = g)
    (lev : Level P (r ^ 2) ze)
    (s : SubLab g (r ^ 2) (m ^ 2) → LB.Sec (LPow P.A P.L ((m : ℤ) ^ 2) (baseOver (Sp K)))) : Prop :=
  ∀ (P' : PolAV (Sp (DualNumber K))) (h' : P'.g = g) (ze' : Γ(Sp (DualNumber K), ⊤)ˣ)
    (lev' : Level P' (r ^ 2) ze') (i : P.A.left ⟶ P'.A.left),
    IsBaseChange (redMap K) h' lev' h lev i →
    ∀ v : Lab g (r ^ 2) → Γ(Sp K, ⊤), IsThetaPoint r h lev v →
      IsThetaPoint r h' lev' (fun c => (strMap K).appTop.hom (v c)) →
      (∃ p : P'.A.left ⟶ P.A.left, IsBaseChange (strMap K) h lev h' lev' p ∧ i ≫ p = 𝟙 _) ∧
      ∀ s', IsCoord m h' lev' s' →
        ∀ (d : ℕ) (F : MvPolynomial (SubLab g (r ^ 2) (m ^ 2)) K), F.IsHomogeneous d → Vanishes s F →
          Vanishes s' (MvPolynomial.map (algebraMap K (DualNumber K)) F)
def FirstOrderRigid : Prop :=
  ∀ g n k d₀ : ℕ, Conv g n k → ∃ B : ℕ, ∀ j : ℕ, B < bigN n k j →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (n : K) ≠ 0 →
      ∀ (P : PolAV (Sp K)) (h : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Level P (bigN n k j ^ 2) ze) (s),
        IsCoord (n ^ k) h lev s → CutOutInDegree s d₀ → RigidAt (n ^ k) (bigN n k j) h lev s
def FirstOrderRigidityH1Vanish : Prop :=
  ∀ g n k d₀ : ℕ, Conv g n k → ∃ B : ℕ, ∀ j : ℕ, B < bigN n k j →
    ∀ (K : Type) [Field K] [IsAlgClosed K], (n : K) ≠ 0 →
      ∀ (P : PolAV (Sp K)) (h : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Level P (bigN n k j ^ 2) ze) (s),
        IsCoord (n ^ k) h lev s → CutOutInDegree s d₀ → HomogeneousFormsSurjectFromDegree s d₀ →
          RigidAt (n ^ k) (bigN n k j) h lev s
def Statement : Prop :=
  CoordTheta ∧ ThetaDetermines ∧ LevelSqDetermined ∧ ThetaDeterminesLevel ∧ EndDeterminedOnTorsion ∧
    ThetaDeterminesAction ∧ FirstOrderRigid
example : Conv 2 3 2 := ⟨by norm_num, by decide, le_rfl, by norm_num⟩
end GlobalTheory.IndefiniteRowSideFullHecke.FirstOrderRigidityLevel


