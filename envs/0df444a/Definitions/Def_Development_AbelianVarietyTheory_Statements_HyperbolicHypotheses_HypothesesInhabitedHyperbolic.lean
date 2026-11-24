-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
-- name    : Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:51.886428+00:00
-- url     : https://prove2.me/theorems/39bd1cef-ecd7-455b-b57c-96183cbb5013
-- title:
--   Hypotheses Inhabited Hyperbolic
-- statement:
--   Definitions and structural lemmas for Hypotheses Inhabited Hyperbolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/HyperbolicHypotheses/HypothesesInhabitedHyperbolic.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TestObj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_OneAddZeta21PowSevenAddPowFourteenEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ToMatrixTrFormBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
def AllClassesSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty),
    l.A = 1 → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty →
    ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), D'.p = D.p → D'.q = D.q →
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
        (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) →
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') →
      ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La),
        (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧
        ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
          ∃ e, gam (f l.M a) = U.t i a + l.M • e
namespace AllClasses
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def IsIsometryTower (D D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) : Prop :=
  ((∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
    (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e)) ∧
  ∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a'
def SameMarking (l : Level H) {D D' : Datum H} (s t : D.La → D'.La) : Prop :=
  ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, s a = t a + l.M • e
def Occurs {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (U : FamilyUnif Xo σ ty) (D' : Datum H) (s : D.La → D'.La) : Prop :=
  ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La),
    (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧ SameMarking l (fun a => gam (s a)) (U.t i)
theorem exists_sign (n : ℕ) : ∃ s : ℤ, 0 < n → ((ordProj[2] n : ℕ) : ℤ) ∣ s - 1 ∧ ((ordCompl[2] n : ℕ) : ℤ) ∣ s + 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
  have hc : IsCoprime ((ordProj[2] n : ℕ) : ℤ) ((ordCompl[2] n : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_ordCompl Nat.prime_two hn.ne').pow_left _)
  obtain ⟨u, v, huv⟩ := hc
  exact ⟨v * (ordCompl[2] n : ℕ) - u * (ordProj[2] n : ℕ), fun _ =>
    ⟨⟨-2 * u, by linear_combination huv⟩, ⟨2 * v, by linear_combination -huv⟩⟩⟩
def sign (n : ℕ) : ℤ := (exists_sign n).choose
theorem isTorsionFree (D : Datum H) : Module.IsTorsionFree (𝓞 E) D.La := by
  have := D.proj
  infer_instance
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
theorem subsingleton_of_rank_zero (D : Datum H) (hD : D.p + D.q = 0) : Subsingleton D.La := by
  have := D.fin
  have := isTorsionFree D
  exact Module.finrank_zero_iff.mp (D.rank.trans hD)
theorem occurs_of_rank_zero (U : FamilyUnif Xo σ ty) (hD : D.p + D.q = 0) (D' : Datum H) (hp : D'.p = D.p)
    (hq : D'.q = D.q) (s : D.La → D'.La) : Occurs U D' s := by
  let i : Fin U.n := ⟨0, U.n_pos⟩
  have := subsingleton_of_rank_zero D' (by omega)
  have := subsingleton_of_rank_zero (U.Di i) (by have := U.sig i; omega)
  exact ⟨i, LinearEquiv.ofSubsingleton _ _, fun a a' => by
    rw [Subsingleton.elim a 0, map_zero, map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply],
    fun a _ => ⟨0, Subsingleton.elim _ _⟩⟩
example (H : Host E) (l : Level H) (Xo : Moduli (Test.zeroDatum H) l) (σ : KA l →+* ℂ) (ty : Fin 0 → (E →+* ℂ))
    (U : FamilyUnif Xo σ ty) : Occurs U (Test.zeroDatum H) fun a => a :=
  occurs_of_rank_zero U rfl _ rfl rfl _
end AllClasses
end GlobalTheory


