-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_HformSelfStar
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T12:56:47.813834+00:00
-- url     : https://prove2.me/theorems/15b2630d-6aa7-4c5f-8966-476f49ff752e
-- title:
--   Hform Self Star
-- statement:
--   Definitions and structural lemmas for Hform Self Star, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/HformSelfStar.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_StGenusOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelClassFin
open Formalism.UG NumberField
open scoped Matrix
section Defs
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def HInt {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (M : Submodule (𝓞 E) (Fin m → E)) : Prop :=
  ∀ x ∈ M, ∀ y ∈ M, hform (starRingEnd E) J x y ∈ (algebraMap (𝓞 E) E).range
def HDual {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (M : Submodule (𝓞 E) (Fin m → E)) (d : ℕ) : Prop :=
  ∀ w : Fin m → E, (∀ x ∈ M, hform (starRingEnd E) J x w ∈ (algebraMap (𝓞 E) E).range) → (d : E) • w ∈ M
variable (E) in

def Lat (m d : ℕ) : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)) :=
  {p | IsHerm (starRingEnd E) p.1 ∧ p.1.det ≠ 0 ∧ p.2.FG ∧ Submodule.span E (p.2 : Set (Fin m → E)) = ⊤ ∧
    HInt p.1 p.2 ∧ HDual p.1 p.2 d}
def Iso {m : ℕ} (p q : Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)) : Prop :=
  ∃ A : GL (Fin m) E, cT (starRingEnd E) (A : Matrix (Fin m) (Fin m) E) * p.1 * (A : Matrix (Fin m) (Fin m) E) = q.1 ∧
    IsImg A q.2 p.2
def FinCl {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E))) : Prop :=
  ∃ T : Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)), T.Finite ∧ ∀ p ∈ S, ∃ q ∈ T, Iso p q
variable (E) in

def HL (m : ℕ) : Prop := ∀ d : ℕ, 1 ≤ d → FinCl (Lat E m d)
def gram {m k : ℕ} (J : Matrix (Fin m) (Fin m) E) (v : Fin k → Fin m → E) : Matrix (Fin k) (Fin k) E :=
  Matrix.of fun i j => hform (starRingEnd E) J (v i) (v j)
variable (E) in

def SplitSet (m k d : ℕ) (G : Set (Matrix (Fin k) (Fin k) E)) :
    Set (Matrix (Fin m) (Fin m) E × Submodule (𝓞 E) (Fin m → E)) :=
  {p | p ∈ Lat E m d ∧ ∃ v : Fin k → Fin m → E, (∀ i, v i ∈ p.2) ∧ gram p.1 v ∈ G}
end Defs
def PartShort : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ m d : ℕ, 1 ≤ m → 1 ≤ d → ∃ C : ℚ, ∀ p ∈ Lat E m d, ∃ x ∈ p.2, x ≠ 0 ∧
      |Algebra.norm ℚ (hform (starRingEnd E) p.1 x x)| ≤ C
def PartUnits : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ C : ℚ, ∃ R : Set E, R.Finite ∧ (0 : E) ∉ R ∧
      ∀ a ∈ (algebraMap (𝓞 E) E).range, star a = a → a ≠ 0 → |Algebra.norm ℚ a| ≤ C →
        ∃ u : (𝓞 E)ˣ, ∃ r ∈ R, a = star (algebraMap (𝓞 E) E (u : 𝓞 E)) * algebraMap (𝓞 E) E (u : 𝓞 E) * r
def PartIso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ m d : ℕ, 1 ≤ d → ∃ G : Set (Matrix (Fin 2) (Fin 2) E), G.Finite ∧ (∀ Γ ∈ G, Γ.det ≠ 0) ∧
      ∀ p ∈ Lat E m d, ∀ x ∈ p.2, x ≠ 0 → hform (starRingEnd E) p.1 x x = 0 →
        ∃ v : Fin 2 → Fin m → E, (∀ i, v i ∈ p.2) ∧ gram p.1 v ∈ G
def PartSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E →
    ∀ m k : ℕ, 1 ≤ k → (∀ j < m, HL E j) → ∀ d : ℕ, 1 ≤ d → ∀ G : Set (Matrix (Fin k) (Fin k) E), G.Finite →
      (∀ Γ ∈ G, Γ.det ≠ 0) → FinCl (SplitSet E m k d G)
def PartBetween : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (N : Submodule (𝓞 E) (Fin m → E)), N.FG → ∀ δ : 𝓞 E, δ ≠ 0 →
    {M : Submodule (𝓞 E) (Fin m → E) | N ≤ M ∧ ∀ x ∈ M, δ • x ∈ N}.Finite
def PartMink : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, ∀ G : Matrix (Fin N) (Fin N) ℝ, G.PosDef →
    ∃ c : Fin N → ℤ, c ≠ 0 ∧ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) ≤ K * G.det ^ ((1 : ℝ) / N)
section Lemmas
variable {E : Type} [Field E] [NumberField E] [StarRing E]
end Lemmas
end PIW.AdelClassFin


