-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:02.092748+00:00
-- url     : https://prove2.me/theorems/6a4df186-46b4-42f8-870f-970a0ac8fe26
-- title:
--   HTBasis
-- statement:
--   Definitions and structural lemmas for HTBasis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/HTBasis.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Cyc
open Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [Fact l.Prime]
def IsActC (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) : Prop :=
  (∀ (g : GQ l) (x : Om l), act g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l)) ∧
    ∀ (g : GQ l) (y : PadicComplex l), ‖act g y‖ = ‖y‖
def IsCyc (χ : GQ l →* ℚ_[l]ˣ) : Prop :=
  ∀ (g : GQ l) (m : ℕ) (ζ : Om l), ζ ^ (l ^ m) = 1 →
    ∃ a : ℕ, ‖(χ g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a
def chiC (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) (g : GQ l) : PadicComplex l :=
  algebraMap ℚ_[l] (PadicComplex l) ((χ g ^ i : ℚ_[l]ˣ) : ℚ_[l])
def Kinf (K : FinExt l) : IntermediateField ℚ_[l] (Om l) :=
  K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x | ∃ j : ℕ, x ^ (l ^ j) = 1}
def Hinf (K : FinExt l) : Subgroup (GQ l) := (Kinf K).fixingSubgroup
def Gj (K : FinExt l) (j : ℕ) : Subgroup (GQ l) := (Ks K j).fixingSubgroup
def Lev (l j : ℕ) : Prop := 1 ≤ j ∧ (l = 2 → 2 ≤ j)
def IsGen (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (j : ℕ) (g : GQ l) : Prop :=
  g ∈ Gj K j ∧ ‖(χ g : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(j : ℤ))
def inC (F : IntermediateField ℚ_[l] (Om l)) : Set (PadicComplex l) :=
  (fun x : Om l => (x : PadicComplex l)) '' (F : Set (Om l))
def intC (F : IntermediateField ℚ_[l] (Om l)) : Set (PadicComplex l) := {y | y ∈ inC F ∧ ‖y‖ ≤ 1}
def Ohat (K : FinExt l) : Set (PadicComplex l) := closure (intC (Kinf K))
def Xlev (K : FinExt l) (i : ℕ) : AddSubgroup (PadicComplex l) :=
  AddSubgroup.closure {z | ∃ ζ y : PadicComplex l, IsPrimitiveRoot ζ (l ^ i) ∧
    y ∈ intC (Ks K (i - 1)) ∧ z = ζ * y}
def Xj (K : FinExt l) (j : ℕ) : AddSubgroup (PadicComplex l) :=
  (⨆ (i : ℕ) (_ : j < i), Xlev K i).topologicalClosure
def rho1 (l : ℕ) : ℝ := (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) - 1))
def twAct (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (y : Fin r → PadicComplex l) :
    Fin r → PadicComplex l :=
  chiC χ i g • (U g).mulVec (fun a => act g (y a))
def CocOn {X : Type} [AddCommGroup X] [TopologicalSpace X] (G : Subgroup (GQ l)) (A : GQ l → X → X)
    (M : Set X) (c : GQ l → X) : Prop :=
  ContinuousOn c G ∧ (∀ g ∈ G, c g ∈ M) ∧ ∀ g ∈ G, ∀ h ∈ G, c (g * h) = c g + A g (c h)
def CobOn {X : Type} [AddCommGroup X] (G : Subgroup (GQ l)) (A : GQ l → X → X) (M : Set X)
    (c : GQ l → X) : Prop :=
  ∃ x ∈ M, ∀ g ∈ G, c g = A g x - x
def ball (l : ℕ) [Fact l.Prime] (r : ℕ) : Set (Fin r → PadicComplex l) := {y | ∀ a, ‖y a‖ ≤ 1}
def Frame (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m : ℕ) {r : ℕ}
    (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) : Prop :=
  IsGen χ K m g ∧ (∀ a b, ContinuousOn (fun σ => U σ a b) (Gj K m)) ∧
    (∀ σ ∈ Gj K m, ∀ a b, U σ a b ∈ intC (Ks K m)) ∧
    (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, U (σ * τ) = U σ * U τ) ∧ (∀ σ ∈ Hinf K, U σ = 1) ∧
    ∀ a b, ‖(U g - 1) a b‖ < rho1 l
def HTBasis (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (G : Subgroup (GQ l)) {r : ℕ} (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (J : Set ℤ) : Prop :=
  ∃ (e : Fin r → Fin r → PadicComplex l) (u : Fin r → ℤ), LinearIndependent (PadicComplex l) e ∧
    (∀ k, u k ∈ J) ∧ ∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k
end GlobalTheory.Cyc


