-- Prove2me | Definitions.Def_ChapterStoneGroup
-- name    : ChapterStoneGroup
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-09T23:27:23.451042+00:00
-- url     : https://prove2.me/theorems/82960d0b-b7fc-4d24-801c-3ee4901fb940
-- title:
--   Building on `BookProof.ChapterStoneResolvent`, this module constructs the bounded **Yosida approximations**
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.StoneGroup`, source chapter `BookProof/ChapterStoneGroup.lean`).
--
--   Building on `BookProof.ChapterStoneResolvent`, this module constructs the bounded **Yosida approximations**
--
--   `A_n = n² A (A² + n²)⁻¹ = n² (A + in)⁻¹ + i n³ (A - in)⁻¹ (A + in)⁻¹`
--
--   of an unbounded self-adjoint operator `A`, and proves that they are bounded, self-adjoint, mutually commuting, and that `A_n x → A x` for `x` in the domain.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterStoneGroup.lean

import Definitions.Def_ChapterStoneResolvent
import Mathlib

import Mathlib

/-!
# The general Stone theorem, part II: the Yosida approximation

Building on `BookProof.ChapterStoneResolvent`, this module constructs the bounded
**Yosida approximations**

`A_n = n² A (A² + n²)⁻¹ = n² (A + in)⁻¹ + i n³ (A - in)⁻¹ (A + in)⁻¹`

of an unbounded self-adjoint operator `A`, and proves that they are bounded,
self-adjoint, mutually commuting, and that `A_n x → A x` for `x` in the domain.
-/

open scoped InnerProductSpace
open Filter Topology

namespace BookProof.ChapterStoneResolvent

open BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace UnboundedSelfAdjoint

variable (T : UnboundedSelfAdjoint H)

/-! ## The first resolvent identity -/



/-! ## The Yosida approximation -/

/-- The **Yosida approximation** `A_n = n² A (A² + n²)⁻¹`, written out in
resolvents as `n² (A + in)⁻¹ + i n³ (A - in)⁻¹ (A + in)⁻¹`. -/
noncomputable def yosida (n : ℝ) : H →L[ℂ] H :=
  ((n : ℂ) ^ 2) • T.resCLM (-n) + (((n : ℂ) ^ 3) * Complex.I) • (T.resCLM n * T.resCLM (-n))









/-! ## Symmetry of the Yosida approximation -/





/-! ## Commutation -/





/-! ## The approximate identity `J_n = (1 + A²/n²)⁻¹` -/

/-- `J_n = n² (A - in)⁻¹ (A + in)⁻¹ = (1 + A²/n²)⁻¹`, a contraction converging
strongly to the identity. -/
noncomputable def jn (n : ℝ) : H →L[ℂ] H := ((n : ℂ) ^ 2) • (T.resCLM n * T.resCLM (-n))

/-- The **first resolvent identity** `R(il) - R(im) = i(l - m) R(il) R(im)`. -/
theorem res_sub {l m : ℝ} (hl : l ≠ 0) (hm : m ≠ 0) (y : H) :
    T.resCLM l y - T.resCLM m y
      = (((l : ℂ) - (m : ℂ)) * Complex.I) • T.resCLM l (T.resCLM m y) := by
  set u : T.domain := T.res m y with hudef
  set v : T.domain := T.res l y with hvdef
  set w : T.domain := T.res l ((u : H)) with hwdef
  have hu : T.op u - ((m : ℂ) * Complex.I) • (u : H) = y := by
    have := T.shift_res hm y; rwa [shift_apply] at this
  have hv : T.op v - ((l : ℂ) * Complex.I) • (v : H) = y := by
    have := T.shift_res hl y; rwa [shift_apply] at this
  have hw : T.op w - ((l : ℂ) * Complex.I) • (w : H) = (u : H) := by
    have := T.shift_res hl ((u : H)); rwa [shift_apply] at this
  set c : ℂ := (((l : ℂ) - (m : ℂ)) * Complex.I) with hc
  have hzero : T.shift l (v - u - c • w) = 0 := by
    rw [map_sub, map_sub, map_smul, shift_apply, shift_apply, shift_apply]
    rw [hv, hw]
    have hop : T.op u = y + ((m : ℂ) * Complex.I) • (u : H) := by
      rw [← hu]; abel
    rw [hop, hc]
    module
  have hzero' : T.shift l (v - u - c • w) = T.shift l 0 := by simpa using hzero
  have hsub : v - u - c • w = 0 := T.shift_injective hl hzero'
  have hcoe : ((v : H)) - (u : H) - c • (w : H) = 0 := by
    have h2 : ((v - u - c • w : T.domain) : H) = ((0 : T.domain) : H) := by rw [hsub]
    simpa using h2
  have : ((v : H)) - (u : H) = c • (w : H) := by
    have := hcoe
    linear_combination (norm := module) this
  simpa [hudef, hvdef, hwdef, hc] using this

theorem yosida_apply (n : ℝ) (y : H) :
    T.yosida n y = ((n : ℂ) ^ 2) • T.resCLM (-n) y
      + (((n : ℂ) ^ 3) * Complex.I) • T.resCLM n (T.resCLM (-n) y) := rfl

/-- The Yosida approximation is `n² A R(in) R(-in)`. -/
theorem yosida_eq_op {n : ℝ} (hn : n ≠ 0) (y : H) :
    T.yosida n y = ((n : ℂ) ^ 2) • T.op (T.res n (T.resCLM (-n) y)) := by
  have h := T.op_res hn (T.resCLM (-n) y)
  rw [yosida_apply, h]
  simp only [resCLM_apply, smul_add]
  rw [smul_smul]
  congr 2
  ring

/-- The resolvent vanishes at the meaningless parameter `0`. -/
@[simp] theorem resCLM_zero : T.resCLM (0 : ℝ) = 0 := by
  ext y
  simp [resCLM, res]

@[simp] theorem yosida_zero : T.yosida (0 : ℝ) = 0 := by
  simp [yosida]

theorem yosida_inner (n : ℝ) (y z : H) :
    ⟪ T.yosida n y, z ⟫_ℂ = ⟪ y, T.yosida n z ⟫_ℂ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : -n ≠ 0 := neg_ne_zero.mpr hn
  have e1 : ∀ w v : H, ⟪ T.resCLM (-n) w, v ⟫_ℂ = ⟪ w, T.resCLM n v ⟫_ℂ := by
    intro w v
    have := T.inner_res hn' w v
    simpa using this
  have e2 : ∀ w v : H, ⟪ T.resCLM n w, v ⟫_ℂ = ⟪ w, T.resCLM (-n) v ⟫_ℂ := by
    intro w v
    have := T.inner_res hn w v
    simpa using this
  have hres : T.resCLM n z - T.resCLM (-n) z
      = (((n : ℂ) - ((-n : ℝ) : ℂ)) * Complex.I) • T.resCLM n (T.resCLM (-n) z) :=
    T.res_sub hn hn' z
  have hz : T.resCLM n z
      = T.resCLM (-n) z + ((2 * (n : ℂ)) * Complex.I) • T.resCLM n (T.resCLM (-n) z) := by
    have := hres
    push_cast at this ⊢
    linear_combination (norm := module) this
  rw [yosida_apply, yosida_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_left, inner_smul_right, inner_smul_right]
  rw [e1 y z, e2 (T.resCLM (-n) y) z, e1 y (T.resCLM (-n) z), hz]
  rw [inner_add_right, inner_smul_right]
  simp only [map_pow, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem yosida_isSelfAdjoint (n : ℝ) : IsSelfAdjoint (T.yosida n) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (fun y z => T.yosida_inner n y z)

theorem resCLM_commute (l m : ℝ) : Commute (T.resCLM l) (T.resCLM m) := by
  rcases eq_or_ne l 0 with rfl | hl
  · simp [Commute, SemiconjBy]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [Commute, SemiconjBy]
  ext y
  simpa using T.res_comm hl hm y

theorem yosida_commute (n m : ℝ) : Commute (T.yosida n) (T.yosida m) := by
  have h : ∀ a b : ℝ, Commute (T.resCLM a) (T.resCLM b) := T.resCLM_commute
  unfold yosida
  refine Commute.add_left (Commute.smul_left ?_ _) (Commute.smul_left ?_ _) <;>
    refine Commute.add_right (Commute.smul_right ?_ _) (Commute.smul_right ?_ _) <;>
    first
      | exact h _ _
      | exact (h _ _).mul_right (h _ _)
      | exact (h _ _).mul_left (h _ _)
      | exact Commute.mul_left ((h _ _).mul_right (h _ _)) ((h _ _).mul_right (h _ _))

theorem jn_apply (n : ℝ) (y : H) :
    T.jn n y = ((n : ℂ) ^ 2) • T.resCLM n (T.resCLM (-n) y) := rfl

theorem norm_resCLM_apply_le' {n : ℝ} (y : H) :
    ‖T.resCLM (-n) y‖ ≤ (1 / |n|) * ‖y‖ := by
  simpa using T.norm_resCLM_apply_le (-n) y

theorem norm_jn_apply_le (n : ℝ) (y : H) : ‖T.jn n y‖ ≤ ‖y‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [jn]
  have habs : 0 < |n| := abs_pos.mpr hn
  have h1 : ‖T.resCLM (-n) y‖ ≤ (1 / |n|) * ‖y‖ := T.norm_resCLM_apply_le' y
  have h2 : ‖T.resCLM n (T.resCLM (-n) y)‖ ≤ (1 / |n|) * ‖T.resCLM (-n) y‖ :=
    T.norm_resCLM_apply_le n _
  have h3 : ‖((n : ℂ) ^ 2)‖ = |n| ^ 2 := by
    simp [norm_pow]
  rw [jn_apply, norm_smul, h3]
  have h4 : ‖T.resCLM n (T.resCLM (-n) y)‖ ≤ (1 / |n|) * ((1 / |n|) * ‖y‖) := by
    refine h2.trans ?_
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  calc |n| ^ 2 * ‖T.resCLM n (T.resCLM (-n) y)‖
      ≤ |n| ^ 2 * ((1 / |n|) * ((1 / |n|) * ‖y‖)) := by
        exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = ‖y‖ := by field_simp

/-- On the domain, `J_n x - x` is expressed through resolvents of `A x`. -/
theorem jn_apply_domain {n : ℝ} (hn : n ≠ 0) (x : T.domain) :
    T.jn n (x : H) = (x : H) - T.resCLM n (T.op x)
      + ((n : ℂ) * Complex.I) • T.resCLM n (T.resCLM (-n) (T.op x)) := by
  have hn' : -n ≠ 0 := neg_ne_zero.mpr hn
  have E1 : T.resCLM (-n) (T.op x) = (x : H) - ((n : ℂ) * Complex.I) • T.resCLM (-n) (x : H) := by
    have h1 : ((T.res (-n) (T.op x) : T.domain) : H) = T.op (T.res (-n) (x : H)) :=
      T.res_op hn' x
    have h2 : T.op (T.res (-n) (x : H))
        = (x : H) + (((-n : ℝ) : ℂ) * Complex.I) • ((T.res (-n) (x : H) : T.domain) : H) :=
      T.op_res hn' (x : H)
    have := h1.trans h2
    simp only [resCLM_apply]
    rw [this]
    push_cast
    module
  have E2 : T.resCLM n (T.op x) = (x : H) + ((n : ℂ) * Complex.I) • T.resCLM n (x : H) := by
    have h1 : ((T.res n (T.op x) : T.domain) : H) = T.op (T.res n (x : H)) := T.res_op hn x
    have h2 : T.op (T.res n (x : H))
        = (x : H) + ((n : ℂ) * Complex.I) • ((T.res n (x : H) : T.domain) : H) :=
      T.op_res hn (x : H)
    simp only [resCLM_apply]
    rw [h1.trans h2]
  have E3 : T.resCLM n (T.resCLM (-n) (T.op x))
      = T.resCLM n (x : H) - ((n : ℂ) * Complex.I) • T.resCLM n (T.resCLM (-n) (x : H)) := by
    rw [E1, map_sub, map_smul]
  rw [jn_apply, E2, E3]
  match_scalars <;> ring_nf
  simp [Complex.I_sq]

theorem norm_jn_sub_domain {n : ℝ} (hn : n ≠ 0) (x : T.domain) :
    ‖T.jn n (x : H) - (x : H)‖ ≤ 2 * ‖T.op x‖ / |n| := by
  have habs : 0 < |n| := abs_pos.mpr hn
  have hid : T.jn n (x : H) - (x : H)
      = -T.resCLM n (T.op x) + ((n : ℂ) * Complex.I) • T.resCLM n (T.resCLM (-n) (T.op x)) := by
    rw [T.jn_apply_domain hn x]; abel
  have h1 : ‖T.resCLM n (T.op x)‖ ≤ ‖T.op x‖ / |n| := by
    have := T.norm_resCLM_apply_le n (T.op x)
    rw [div_eq_inv_mul]
    simpa [one_div] using this
  have h2 : ‖((n : ℂ) * Complex.I) • T.resCLM n (T.resCLM (-n) (T.op x))‖ ≤ ‖T.op x‖ / |n| := by
    rw [norm_smul]
    have hc : ‖(n : ℂ) * Complex.I‖ = |n| := by simp
    have ha : ‖T.resCLM n (T.resCLM (-n) (T.op x))‖ ≤ (1 / |n|) * ((1 / |n|) * ‖T.op x‖) := by
      refine (T.norm_resCLM_apply_le n _).trans ?_
      exact mul_le_mul_of_nonneg_left (T.norm_resCLM_apply_le' (T.op x)) (by positivity)
    rw [hc]
    calc |n| * ‖T.resCLM n (T.resCLM (-n) (T.op x))‖
        ≤ |n| * ((1 / |n|) * ((1 / |n|) * ‖T.op x‖)) :=
          mul_le_mul_of_nonneg_left ha (le_of_lt habs)
      _ = ‖T.op x‖ / |n| := by field_simp
  calc ‖T.jn n (x : H) - (x : H)‖
      ≤ ‖-T.resCLM n (T.op x)‖
        + ‖((n : ℂ) * Complex.I) • T.resCLM n (T.resCLM (-n) (T.op x))‖ := by
        rw [hid]; exact norm_add_le _ _
    _ ≤ ‖T.op x‖ / |n| + ‖T.op x‖ / |n| := by
        rw [norm_neg]; exact add_le_add h1 h2
    _ = 2 * ‖T.op x‖ / |n| := by ring

/-- `J_n → 1` strongly. -/
theorem jn_tendsto (y : H) :
    Tendsto (fun k : ℕ => T.jn ((k : ℝ) + 1) y) atTop (𝓝 y) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨z, hz, hdist⟩ := T.denseDomain.exists_dist_lt y (ε := ε / 3) (by linarith)
  set x : T.domain := ⟨z, hz⟩ with hx
  obtain ⟨N, hN⟩ := exists_nat_gt (6 * ‖T.op x‖ / ε)
  refine ⟨N, fun k hk => ?_⟩
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hn : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hpos
  have habs : |(k : ℝ) + 1| = (k : ℝ) + 1 := abs_of_pos hpos
  have hyz : ‖y - z‖ < ε / 3 := by
    rw [dist_eq_norm] at hdist; exact hdist
  have hkey : ‖T.jn ((k : ℝ) + 1) (x : H) - (x : H)‖ ≤ 2 * ‖T.op x‖ / ((k : ℝ) + 1) := by
    have := T.norm_jn_sub_domain hn x
    rwa [habs] at this
  have hklarge : 2 * ‖T.op x‖ / ((k : ℝ) + 1) < ε / 3 := by
    rw [div_lt_iff₀ hpos]
    have hNk : (6 * ‖T.op x‖ / ε) < (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have h6 : 6 * ‖T.op x‖ < ε * ((k : ℝ) + 1) := by
      rw [div_lt_iff₀ hε] at hNk
      linarith
    linarith
  have hsplit : T.jn ((k : ℝ) + 1) y - y
      = T.jn ((k : ℝ) + 1) (y - z) + (T.jn ((k : ℝ) + 1) (x : H) - (x : H)) + (z - y) := by
    have : T.jn ((k : ℝ) + 1) (y - z) = T.jn ((k : ℝ) + 1) y - T.jn ((k : ℝ) + 1) z := by
      rw [map_sub]
    rw [this]
    simp only [hx]
    abel
  have hb1 : ‖T.jn ((k : ℝ) + 1) (y - z)‖ ≤ ‖y - z‖ := T.norm_jn_apply_le _ _
  have hb3 : ‖z - y‖ = ‖y - z‖ := norm_sub_rev z y
  rw [dist_eq_norm]
  calc ‖T.jn ((k : ℝ) + 1) y - y‖
      ≤ ‖T.jn ((k : ℝ) + 1) (y - z)‖ + ‖T.jn ((k : ℝ) + 1) (x : H) - (x : H)‖ + ‖z - y‖ := by
        rw [hsplit]
        exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [hb3]
        have := hkey.trans_lt hklarge
        linarith [hb1.trans_lt hyz]
    _ = ε := by ring

/-- The Yosida approximation applied to a domain vector is `J_n (A x)`. -/
theorem yosida_apply_domain {n : ℝ} (hn : n ≠ 0) (x : T.domain) :
    T.yosida n (x : H) = T.jn n (T.op x) := by
  rw [T.yosida_eq_op hn, jn_apply]
  congr 1
  have h1 : ((T.res n (T.resCLM (-n) (x : H)) : T.domain) : H)
      = ((T.res n ((T.res (-n) (x : H) : T.domain) : H) : T.domain) : H) := rfl
  have hn' : -n ≠ 0 := neg_ne_zero.mpr hn
  have e1 : ((T.res (-n) (T.op x) : T.domain) : H) = T.op (T.res (-n) (x : H)) := T.res_op hn' x
  have e2 : ((T.res n (T.op (T.res (-n) (x : H))) : T.domain) : H)
      = T.op (T.res n ((T.res (-n) (x : H) : T.domain) : H)) := T.res_op hn _
  simp only [resCLM_apply]
  rw [← e2, ← e1]

/-- **The Yosida approximation converges**: `A_n x → A x` for `x` in the domain. -/
theorem yosida_tendsto (x : T.domain) :
    Tendsto (fun k : ℕ => T.yosida ((k : ℝ) + 1) (x : H)) atTop (𝓝 (T.op x)) := by
  have h : ∀ k : ℕ, T.yosida ((k : ℝ) + 1) (x : H) = T.jn ((k : ℝ) + 1) (T.op x) := by
    intro k
    exact T.yosida_apply_domain (by positivity) x
  simp only [h]
  exact T.jn_tendsto (T.op x)

















end UnboundedSelfAdjoint

end BookProof.ChapterStoneResolvent


