-- Prove2me | Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
-- name    : Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:43.265896+00:00
-- url     : https://prove2.me/theorems/3d45b6cc-9270-4661-b5ca-f0e264de3c3b
-- title:
--   Global Bound Refinements
-- statement:
--   Definitions and structural lemmas for Global Bound Refinements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
theorem theta_identity : ThetaIdentity := by
  intro R X Y _ _ _ _ _ θ eX pr e hc hk Mt
  have key : ∀ m, θ (pr (eX m)) = e (θ m) := by
    intro m
    have h1 := hk (eX m) (LinearMap.mem_range_self eX m)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    rw [← h1, ← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply]
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
    exact ⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩
  · rintro ⟨z, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨pr (eX m), ⟨eX m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩
theorem theta_identity_orthogonal : ThetaIdentityOrth := by
  intro R X Y A _ _ _ _ _ _ θ eX p e h hc hsym hp hker hrange
  have hkerθ : ∀ k ∈ LinearMap.ker θ, eX k ∈ LinearMap.ker θ := by
    intro k hk
    rw [LinearMap.mem_ker] at hk ⊢
    rw [← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hk, map_zero]
  have hpp : ∀ x, p (p x) = p x := fun x => by rw [← LinearMap.comp_apply p p, hp]
  have hrp : ∀ x, p x ∈ LinearMap.range p := fun x => LinearMap.mem_range_self p x
  have hsub : ∀ x, x - p x ∈ LinearMap.ker θ := fun x => by
    rw [← hker, LinearMap.mem_ker, map_sub, hpp, sub_self]
  have hEr : ∀ x ∈ LinearMap.range p, eX x ∈ LinearMap.range p := by
    intro x hx
    rw [hrange] at hx ⊢
    intro k hk
    rw [← hsym]
    exact hx _ (hkerθ k hk)
  have hfix : ∀ y ∈ LinearMap.range p, p y = y := by
    rintro y ⟨z, rfl⟩
    exact hpp z
  have hcomm : ∀ x, p (eX x) = eX (p x) := by
    intro x
    have h1 : eX x = eX (p x) + eX (x - p x) := by
      rw [← map_add]
      congr 1
      abel
    have h2 : p (eX (x - p x)) = 0 := by
      rw [← LinearMap.mem_ker, hker]
      exact hkerθ _ (hsub x)
    rw [h1, map_add, h2, add_zero, hfix _ (hEr _ (hrp x))]
  refine ⟨LinearMap.ext hcomm, fun x hx => ⟨?_, hsub x, fun k hk => (hrange (p x)).1 (hrp x) k hk⟩, fun Mt => ?_⟩
  · obtain ⟨y, rfl⟩ := hx
    rw [hcomm]
    exact LinearMap.mem_range_self eX (p y)
  · have key : ∀ m, θ (eX (p m)) = e (θ m) := by
      intro m
      have hm : θ (p m) = θ m := by
        have := hsub m
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
        exact this.symm
      rw [← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hm]
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
      exact ⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩
    · rintro ⟨z, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨eX (p m), ⟨p m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩
theorem constant_b_bound : ConstB := by
  intro RR PP DF d' n1 nW g' qmin hRR hDF hd hn1 hn hq hqg hPP
  have hg : 0 < g' := lt_of_lt_of_le hq hqg
  have hnW : 0 ≤ nW := le_trans hn1 hn
  have hd3 : 0 ≤ d' ^ 3 := pow_nonneg hd 3
  have hd4 : 0 ≤ d' ^ 4 := pow_nonneg hd 4
  have hPP0 : 0 ≤ PP := by nlinarith [mul_nonneg hd4 hnW]
  have hDF2 : 1 ≤ DF ^ 2 := by nlinarith
  have k1 : 0 ≤ RR * DF ^ 2 * (PP - (d' ^ 4 * nW + 2 * d' ^ 3)) :=
    mul_nonneg (mul_nonneg hRR (sq_nonneg DF)) (by linarith)
  have k2 : 0 ≤ RR * d' ^ 4 * (nW * DF ^ 2 - n1 / 4) :=
    mul_nonneg (mul_nonneg hRR hd4) (by nlinarith)
  have hC : n1 * d' * (RR * d' ^ 3) / 4 + 2 * (RR * d' ^ 3) * DF ^ 2 ≤ RR * PP * DF ^ 2 := by
    nlinarith [k1, k2]
  have hN : 0 ≤ RR * PP * DF ^ 2 := mul_nonneg (mul_nonneg hRR hPP0) (sq_nonneg DF)
  have hinv : g'⁻¹ ≤ qmin⁻¹ := by
    first
      | exact inv_anti₀ hq hqg
      | exact inv_le_inv_of_le hq hqg
      | exact (inv_le_inv hg hq).2 hqg
  calc n1 * d' * (RR * d' ^ 3) / (4 * g') + 2 * (RR * d' ^ 3) * DF ^ 2 / g'
      = (n1 * d' * (RR * d' ^ 3) / 4 + 2 * (RR * d' ^ 3) * DF ^ 2) * g'⁻¹ := by
        first
          | ring
          | (field_simp; ring)
    _ ≤ RR * PP * DF ^ 2 * g'⁻¹ := mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hg.le)
    _ ≤ RR * PP * DF ^ 2 * qmin⁻¹ := mul_le_mul_of_nonneg_left hinv hN
    _ = RR * PP * DF ^ 2 / qmin := by rw [div_eq_mul_inv]
theorem gapConditions_of_largeGaps : GapNum := by
  intro T D nW r t h0 c hD hr ht hnW hT
  have h2 : 2 * (D + 2) ≤ (D + 2) * nW := by nlinarith
  have hb : 0 ≤ T + D + 2 + r := by linarith
  have hle : T + D + 2 + r ≤ 3 / 2 * T := by linarith
  have hsq := mul_self_le_mul_self hb hle
  have key : (T + D + 2) * (T + D + 2 + 2 * r) ≤ 9 / 4 * T ^ 2 := by nlinarith [sq_nonneg r]
  have e : (3.75 : ℝ) = 15 / 4 := by norm_num
  rw [e]
  exact ⟨by nlinarith [sq_nonneg T], fun hh hc => by nlinarith [sq_nonneg T]⟩
example : ⌈((1 : ℤ) : ℝ) * (((3 : ℕ) : ℝ) * ((2 : ℝ) / (15 - 1) + 1))⌉ = (1 : ℤ) * (((3 : ℕ) : ℤ) + 1) := by
  rw [Int.ceil_eq_iff]; constructor <;> norm_num
example : ¬ (⌈((1 : ℤ) : ℝ) * (((3 : ℕ) : ℝ) * ((2 : ℝ) / (2 - 1) + 1))⌉ ≤ (1 : ℤ) * (((3 : ℕ) : ℤ) + 1)) := by
  rw [Int.ceil_le]; norm_num
example : (1 : ℝ) * 1 * (1 * 1 ^ 3) / (4 * 1) + 2 * (1 * 1 ^ 3) * 1 ^ 2 / 1 ≤ 1 * 3 * 1 ^ 2 / 1 :=
  constant_b_bound 1 3 1 1 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
example (Mt : Submodule ℤ (ℤ × ℤ)) :
    ((Mt.map (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ)).map
      ((LinearMap.inl ℤ ℤ ℤ) ∘ₗ (LinearMap.fst ℤ ℤ ℤ))).map (LinearMap.fst ℤ ℤ ℤ) =
      (Mt.map (LinearMap.fst ℤ ℤ ℤ)).map (LinearMap.id : ℤ →ₗ[ℤ] ℤ) :=
  theta_identity ℤ (ℤ × ℤ) ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id _ LinearMap.id rfl
    (by intro x _; simp [LinearMap.mem_ker]) Mt
example : (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) ∘ₗ (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ) =
    (LinearMap.id : ℤ × ℤ →ₗ[ℤ] ℤ × ℤ) ∘ₗ (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) :=
  (theta_identity_orthogonal ℤ (ℤ × ℤ) ℤ ℤ (LinearMap.fst ℤ ℤ ℤ) LinearMap.id
    (LinearMap.inl ℤ ℤ ℤ ∘ₗ LinearMap.fst ℤ ℤ ℤ) LinearMap.id (fun x y => x.1 * y.1 + x.2 * y.2) rfl
    (fun _ _ => rfl) (by ext <;> simp)
    (by ext x; simp [LinearMap.mem_ker])
    (by
      intro x
      constructor
      · rintro ⟨y, rfl⟩ k hk
        have : k.1 = 0 := by simpa [LinearMap.mem_ker] using hk
        simp [this]
      · intro hx
        have := hx (0, 1) (by simp [LinearMap.mem_ker])
        refine ⟨x, ?_⟩
        ext <;> simp at this ⊢
        exact this.symm)).1
example : ((8 : ℝ) + 0 + 2) * (8 + 0 + 2 + 2 * 2) ≤ 3.75 * 8 ^ 2 :=
  (gapConditions_of_largeGaps 8 0 2 2 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
example : ⌈((2 : ℤ) : ℝ) * (1.25 : ℝ)⌉ < 2 * ⌈((1 : ℤ) : ℝ) * (1.25 : ℝ)⌉ := by
  have a : ⌈((2 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 3 := by rw [Int.ceil_eq_iff]; norm_num
  have b : ⌈((1 : ℤ) : ℝ) * (1.25 : ℝ)⌉ = 2 := by rw [Int.ceil_eq_iff]; norm_num
  rw [a, b]; norm_num
section Instance
variable (K : Type) [Field K] [NumberField K] [StarRing K]
def unitLat : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
end Instance
end Formalism.EigenvalueLevelCeiling


