-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:20.029448+00:00
-- url     : https://prove2.me/theorems/ca235af2-c870-4db7-9e71-ba99bfbbdf48
-- title:
--   Eq Zero Of Forall Exists Lsum ETwo Pi
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Forall Exists Lsum ETwo Pi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/EqZeroOfForallExistsLsumETwoPi.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.expandConv_u


set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology
open Filter
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (eTwoPi SumsAt)
noncomputable section
namespace GlobalTheory.Conv
def cuspRadius (T : ℝ) : ℝ := Real.exp (-(2 * Real.pi * T))
theorem cuspRadius_pos (T : ℝ) : 0 < cuspRadius T := Real.exp_pos _
theorem cuspRadius_strictAnti : StrictAnti cuspRadius := by
  intro a b h
  exact Real.exp_lt_exp.2 (by nlinarith [Real.pi_pos])
theorem eTwoPi_ne_zero (w : ℂ) : eTwoPi w ≠ 0 := Complex.exp_ne_zero _
theorem norm_eTwoPi (w : ℂ) : ‖eTwoPi w‖ = cuspRadius w.im := by
  show ‖Complex.exp (2 * Real.pi * Complex.I * w)‖ = Real.exp (-(2 * Real.pi * w.im))
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
theorem exists_eTwoPi_eq {v : ℂ} (hv : v ≠ 0) : ∃ w, eTwoPi w = v := by
  refine ⟨Complex.log v / (2 * Real.pi * Complex.I), ?_⟩
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  show Complex.exp (2 * Real.pi * Complex.I * (Complex.log v / (2 * Real.pi * Complex.I))) = v
  rw [mul_div_cancel₀ _ hc, Complex.exp_log hv]
theorem eTwoPi_mem_puncturedDisc {T : ℝ} {w : ℂ} :
    eTwoPi w ∈ puncturedDisc (cuspRadius T) ↔ T < w.im := by
  rw [mem_puncturedDisc, norm_eTwoPi]
  have key : cuspRadius w.im < cuspRadius T ↔ T < w.im := by
    rw [cuspRadius, cuspRadius, Real.exp_lt_exp]
    constructor <;> intro h <;> nlinarith [Real.pi_pos]
  exact ⟨fun h => key.1 h.2, fun h => ⟨eTwoPi_ne_zero w, key.2 h⟩⟩
def halfRing (T : ℝ) : Subalgebra ℂ ℂ⸨X⸩ where
  carrier := {s | ∀ w : ℂ, T < w.im → Summable fun n : ℤ => s.coeff n * eTwoPi w ^ n}
  mul_mem' hf hg w hw := (hasSum_mul_laurent (eTwoPi_ne_zero w) (hf w hw) (hg w hw)).summable
  add_mem' hf hg w hw := by simpa [add_mul] using (hf w hw).add (hg w hw)
  algebraMap_mem' c w hw :=
    (puncturedRing _).algebraMap_mem c _ (eTwoPi_mem_puncturedDisc.2 hw)
theorem mem_halfRing {T : ℝ} {s : ℂ⸨X⸩} :
    s ∈ halfRing T ↔ ∀ w : ℂ, T < w.im → Summable fun n : ℤ => s.coeff n * eTwoPi w ^ n := Iff.rfl
theorem mem_halfRing_iff_puncturedRing {T : ℝ} {s : ℂ⸨X⸩} :
    s ∈ halfRing T ↔ s ∈ puncturedRing (cuspRadius T) := by
  rw [mem_halfRing, mem_puncturedRing]
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := exists_eTwoPi_eq (mem_puncturedDisc.1 hv).1
    exact h w (eTwoPi_mem_puncturedDisc.1 hv)
  · intro h w hw
    exact h _ (eTwoPi_mem_puncturedDisc.2 hw)
theorem halfRing_eq (T : ℝ) : halfRing T = puncturedRing (cuspRadius T) :=
  Subalgebra.ext fun _ => mem_halfRing_iff_puncturedRing
theorem halfRing_mono : Monotone halfRing := by
  intro a b h
  rw [halfRing_eq, halfRing_eq]
  exact puncturedRing_anti (StrictAnti.antitone cuspRadius_strictAnti h)
theorem single_mem_halfRing (T : ℝ) (m : ℤ) (c : ℂ) :
    (HahnSeries.single m c : ℂ⸨X⸩) ∈ halfRing T := by
  rw [halfRing_eq]
  exact single_mem_puncturedRing _ m c
def ev (T : ℝ) (w : ℂ) (hw : T < w.im) : halfRing T →ₐ[ℂ] ℂ where
  toFun s := lsum s (eTwoPi w)
  map_one' := by simpa using lsum_single 0 1 (eTwoPi w)
  map_mul' f g := (hasSum_mul_laurent (eTwoPi_ne_zero w) (f.2 w hw) (g.2 w hw)).tsum_eq
  map_zero' := by simp [lsum]
  map_add' f g := by
    simpa [lsum, add_mul] using (f.2 w hw).tsum_add (g.2 w hw)
  commutes' c := lsum_algebraMap c _
@[simp] theorem ev_apply {T : ℝ} {w : ℂ} (hw : T < w.im) (s : halfRing T) :
    ev T w hw s = lsum s (eTwoPi w) := rfl
theorem halfRing_le_convLaurent (T : ℝ) : halfRing T ≤ convLaurent.toSubalgebra := by
  rw [halfRing_eq]
  exact puncturedRing_le_convLaurent (cuspRadius_pos T)
def halfIncl (T : ℝ) : halfRing T →ₐ[ℂ] convLaurent :=
  Subalgebra.inclusion (halfRing_le_convLaurent T)
@[simp] theorem coe_halfIncl {T : ℝ} (s : halfRing T) : (halfIncl T s : ℂ⸨X⸩) = s := rfl
def locRing (T : ℝ) (s : halfRing T) : Subalgebra (halfRing T) ℂ⸨X⸩ :=
  Algebra.adjoin (halfRing T) {(s : ℂ⸨X⸩)⁻¹}
theorem coe_mem_locRing {T : ℝ} (s f : halfRing T) : (f : ℂ⸨X⸩) ∈ locRing T s :=
  (locRing T s).algebraMap_mem f
theorem inv_mem_locRing {T : ℝ} (s : halfRing T) : (s : ℂ⸨X⸩)⁻¹ ∈ locRing T s :=
  Algebra.subset_adjoin (Set.mem_singleton _)
@[simp] theorem coe_algebraMap_locRing {T : ℝ} (s f : halfRing T) :
    (algebraMap (halfRing T) (locRing T s) f : ℂ⸨X⸩) = f := rfl
theorem mem_locRing {T : ℝ} {s : halfRing T} (h0 : s ≠ 0) {x : ℂ⸨X⸩} :
    x ∈ locRing T s ↔ ∃ (n : ℕ) (f : halfRing T), x * (s : ℂ⸨X⸩) ^ n = f := by
  have hs0 : (s : ℂ⸨X⸩) ≠ 0 := fun h => h0 (Subtype.ext h)
  constructor
  · intro hx
    unfold locRing at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact ⟨1, 1, by simp [hs0]⟩
    | algebraMap r =>
      exact ⟨0, r, by rw [pow_zero, mul_one]; rfl⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨n, f, hf⟩ := ihx
      obtain ⟨m, g, hg⟩ := ihy
      refine ⟨n + m, f * s ^ m + g * s ^ n, ?_⟩
      push_cast
      rw [← hf, ← hg]
      ring
    | mul x y _ _ ihx ihy =>
      obtain ⟨n, f, hf⟩ := ihx
      obtain ⟨m, g, hg⟩ := ihy
      refine ⟨n + m, f * g, ?_⟩
      push_cast
      rw [← hf, ← hg]
      ring
  · rintro ⟨n, f, hf⟩
    have hx : x = f * ((s : ℂ⸨X⸩)⁻¹) ^ n := by
      rw [← hf, mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, mul_one]
    rw [hx]
    exact mul_mem (coe_mem_locRing s f) (pow_mem (inv_mem_locRing s) n)
theorem isLocalization_locRing {T : ℝ} {s : halfRing T} (h0 : s ≠ 0) :
    IsLocalization.Away s (locRing T s) := by
  have hs0 : (s : ℂ⸨X⸩) ≠ 0 := fun h => h0 (Subtype.ext h)
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    show IsUnit (algebraMap (halfRing T) (locRing T s) (s ^ n))
    rw [map_pow]
    refine IsUnit.pow n (isUnit_iff_exists_inv.2 ⟨⟨_, inv_mem_locRing s⟩, Subtype.ext ?_⟩)
    exact mul_inv_cancel₀ hs0
  · intro z
    obtain ⟨n, f, hf⟩ := (mem_locRing h0).1 z.2
    refine ⟨⟨f, ⟨s ^ n, n, rfl⟩⟩, Subtype.ext ?_⟩
    show (z : ℂ⸨X⸩) * ((s ^ n : halfRing T) : ℂ⸨X⸩) = f
    rw [SubmonoidClass.coe_pow]
    exact hf
  · intro x y hxy
    refine ⟨1, ?_⟩
    rw [Submonoid.coe_one, one_mul, one_mul]
    have hv := congrArg Subtype.val hxy
    exact Subtype.ext hv
def evLoc (T : ℝ) (w : ℂ) (hw : T < w.im) (s : halfRing T) (hs : ev T w hw s ≠ 0) :
    locRing T s →ₐ[ℂ] ℂ :=
  haveI := isLocalization_locRing (s := s) fun h => hs (by rw [h, map_zero])
  IsLocalization.Away.liftAlgHom s (f := ev T w hw) hs.isUnit
end GlobalTheory.Conv


