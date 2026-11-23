-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:46:33.090275+00:00
-- url     : https://prove2.me/theorems/54eb366b-c0b6-45af-bd6c-5fe5d44e192e
-- title:
--   Exists Gen Of Is VBOne
-- statement:
--   Definitions and structural lemmas for Exists Gen Of Is VBOne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]
def NormalCpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Prop :=
  ∀ (p : Cpt ξ) (a : Ω), IsIntegral (regAt ξ p) a → a ∈ regAt ξ p
def zeroSet (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω) : Set X :=
  {q | ∃ h : genPt ξ ⤳ q, ¬ unitAt ξ ⟨q, h⟩ ϖ}
def TrivMod (L : Lat ξ E) (ϖ : Ω) : Prop :=
  ∃ t : Cpt ξ → E, ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧
    ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      t p ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {t p} ∧ ∃ y ∈ L q, t p - t q = ϖ • y
def TrivRed (L : Lat ξ E) (ϖ : Ω) : Prop :=
  ∃ t : Cpt ξ → E, ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧
    ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      t p ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {t p} ∧
        ∃ c ∈ regAt ξ q, ¬ unitAt ξ q c ∧ t p - t q = c • t p
def OrderAt (L : Lat ξ E) (σ : E) (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) : Prop :=
  ∃ (e : E) (c : Ω), e ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {e} ∧ σ = c • e ∧ unitAt ξ p (c ^ M / ϖ ^ a)
namespace ZUnit
variable {p : Cpt ξ} {a b : Ω}
theorem one : unitAt ξ p 1 := ⟨one_ne_zero, one_mem _, by simp⟩
theorem mul (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩
theorem pow (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩
theorem of_mul (ha : a ∈ regAt ξ p) (hb : b ∈ regAt ξ p) (h : unitAt ξ p (a * b)) : unitAt ξ p a := by
  have ha0 := left_ne_zero_of_mul h.1
  have hb0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [this]
  exact mul_mem hb h.2.2
theorem exists_of_span_eq {e e' : E} (he : e ≠ 0)
    (h : Submodule.span (regAt ξ p) {e} = Submodule.span (regAt ξ p) {e'}) :
    ∃ u : Ω, unitAt ξ p u ∧ e = u • e' := by
  have h1 : e ∈ Submodule.span (regAt ξ p) {e'} := by
    rw [← h]; exact Submodule.mem_span_singleton_self _
  have h2 : e' ∈ Submodule.span (regAt ξ p) {e} := by
    rw [h]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 h2
  replace hu : (u : Ω) • e' = e := hu
  replace hv : (v : Ω) • e = e' := hv
  have huv : (u : Ω) * v = 1 := by
    apply smul_left_injective Ω he
    simp only [mul_smul, hv, hu, one_smul]
  exact ⟨u, of_mul u.2 v.2 (by rw [huv]; exact one), hu.symm⟩
end ZUnit
section Order
variable {L : Lat ξ E} {σ : E} {ϖ : Ω} {M M' : ℕ} {a a' : ℤ} {p : Cpt ξ}
theorem OrderAt.unitAt (h : OrderAt L σ ϖ M a p) {e : E} {c : Ω} (hL : L p = Submodule.span (regAt ξ p) {e})
    (hσ : σ = c • e) : unitAt ξ p (c ^ M / ϖ ^ a) := by
  obtain ⟨e₀, c₀, he₀, hL₀, hσ₀, h⟩ := h
  obtain ⟨u, hu, e'⟩ := ZUnit.exists_of_span_eq he₀ (hL₀.symm.trans hL)
  have he : e ≠ 0 := by rintro rfl; exact he₀ (by rw [e', smul_zero])
  have hc : c = c₀ * u := by
    apply smul_left_injective Ω he
    simp only [mul_smul, ← e', ← hσ, ← hσ₀]
  have : c ^ M / ϖ ^ a = c₀ ^ M / ϖ ^ a * u ^ M := by rw [hc, mul_pow]; ring
  rw [this]
  exact ZUnit.mul h (ZUnit.pow hu M)
end Order
example {e : E} (he : e ≠ 0) {ϖ : Ω} (h0 : ϖ ≠ 0) (n : ℤ) (p : Cpt ξ) :
    OrderAt (fun p => Submodule.span (regAt ξ p) {e} : Lat ξ E) (ϖ ^ n • e) ϖ 1 n p :=
  ⟨e, ϖ ^ n, he, rfl, rfl, by rw [pow_one, div_self (zpow_ne_zero n h0)]; exact ZUnit.one⟩
example {e : E} (he : e ≠ 0) {ϖ : Ω} (h0 : ϖ ≠ 0) (p : Cpt ξ) :
    OrderAt (fun p => Submodule.span (regAt ξ p) {e} : Lat ξ E) (ϖ ^ 3 • e) (ϖ ^ 2) 2 3 p :=
  ⟨e, ϖ ^ 3, he, rfl, rfl, by
    rw [show (ϖ ^ 3) ^ 2 / (ϖ ^ 2) ^ (3 : ℤ) = 1 by rw [zpow_ofNat]; field_simp]; exact ZUnit.one⟩
example (σ : E) (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) : ¬ OrderAt (fun _ => ⊥ : Lat ξ E) σ ϖ M a p :=
  fun ⟨_, _, he, h, _⟩ => he (Submodule.span_singleton_eq_bot.1 h.symm)
example (ϖ : Ω) (M : ℕ) (a : ℤ) (p : Cpt ξ) :
    ¬ OrderAt (fun p => Submodule.span (regAt ξ p) {((1 : Ω), (0 : Ω))} : Lat ξ (Ω × Ω)) (0, 1) ϖ M a p := by
  rintro ⟨e, c, he, h, hσ, -⟩
  obtain ⟨u, -, rfl⟩ := ZUnit.exists_of_span_eq he h.symm
  simpa using congrArg Prod.snd hσ
example {ϖ : Ω} {p : Cpt ξ} (hp : ¬ unitAt ξ p ϖ) : ¬ TrivRed (fun _ => ⊥ : Lat ξ E) ϖ := by
  rintro ⟨t, ht⟩
  obtain ⟨U, hU, h⟩ := ht p hp
  obtain ⟨h0, h1, -⟩ := h p hU hp
  exact h0 (Submodule.span_singleton_eq_bot.1 h1.symm)
example : zeroSet ξ 1 = ∅ ∧ zeroSet ξ 0 = {q | genPt ξ ⤳ q} :=
  ⟨Set.eq_empty_of_forall_notMem fun _ ⟨_, h⟩ => h ZUnit.one,
    Set.ext fun _ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun hu => hu.1 rfl⟩⟩⟩
end GlobalTheory.CompanionTheory.Ar.Flat


