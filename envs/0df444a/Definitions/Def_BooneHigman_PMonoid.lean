-- Prove2me | Definitions.Def_BooneHigman_PMonoid
-- name    : BooneHigman_PMonoid
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-14T09:15:28.334569+00:00
-- url     : https://prove2.me/theorems/b149a23f-2edf-43fd-8916-1190515c8421
-- title:
--   The monoid $P$ of partial affine maps of $\mathbb{Q}$ (Lemma 6.1)
-- statement:
--   The monoid `PElem` of partial affine maps used in Lemma 6.1 of OpenAI's "Finite algebraic envelopes and the Boone-Higman conjecture" preprint (Section 6.1). An element is a triple `(m, b, r)` representing the map $x \mapsto 2^m x + b$ on the domain $[r, \infty) \cap \mathbb{Q}$ (or all of $\mathbb{Q}$ when $r = -\infty$, modeled by `WithBot ℚ`). Composition applies the right-hand factor first, matching the paper's convention; the resulting data is exactly the $(a, b, r)$ triple of Lemma 6.1's proof with $a = 2^m$. Also provides the two generators `u(x) = x/2`, `v(x) = (x+1)/2`, the partial identities `e_a` on $[a, \infty) \cap \mathbb{Q}$, and verifies equation (27) ($e_a e_b = e_{\max(a,b)}$ and $w e_a w^{-1} = e_{w(a)}$ for $w \in \{u, v\}$), used later in Lemma 6.4.
-- source:
--   OpenAI, "Finite algebraic envelopes and the Boone-Higman conjecture", OpenAI Math Release, 2026-09-23, Section 6.1 (Lemma 6.1 and the paragraph preceding Theorem 6.2).

import Mathlib

/-!
Lemma 6.1's monoid `P` of partial affine maps of `ℚ`, from OpenAI's "Finite algebraic envelopes
and the Boone-Higman conjecture" preprint, Section 6.1. An element is a triple `(m, b, r)`
representing the partial map `x ↦ 2^m * x + b` on the domain `[r, ∞) ∩ ℚ` (or all of `ℚ` if
`r = ⊥`, using `WithBot ℚ` for `-∞`). Composition applies the right-hand factor first.
-/

namespace OAI
namespace FiniteAlgebraicEnvelopes

structure PElem where
  m : ℤ
  b : ℚ
  r : WithBot ℚ
deriving DecidableEq

namespace PElem

/-- `(r - d) / c` on `WithBot ℚ`, treating `⊥` as absorbing (used for the composite domain). -/
def shiftedBound (r : WithBot ℚ) (d : ℚ) (c : ℚ) : WithBot ℚ :=
  r.map (fun r0 => (r0 - d) / c)

@[simp] theorem shiftedBound_bot (d c : ℚ) : shiftedBound ⊥ d c = ⊥ := rfl

@[simp] theorem shiftedBound_coe (r0 d c : ℚ) :
    shiftedBound (r0 : WithBot ℚ) d c = (((r0 - d) / c : ℚ) : WithBot ℚ) := rfl

@[simp] theorem shiftedBound_zero_one (r : WithBot ℚ) : shiftedBound r 0 1 = r := by
  cases r with
  | bot => rfl
  | coe r0 => simp

theorem shiftedBound_mono {d c : ℚ} (hc : 0 < c) :
    Monotone (fun r => shiftedBound r d c) := by
  intro r1 r2 h12
  cases r1 with
  | bot => simp
  | coe r0 =>
    cases r2 with
    | bot => simp at h12
    | coe r0' =>
      simp only [shiftedBound_coe, WithBot.coe_le_coe] at h12 ⊢
      gcongr

theorem shiftedBound_max {d c : ℚ} (hc : 0 < c) (a b : WithBot ℚ) :
    shiftedBound (max a b) d c = max (shiftedBound a d c) (shiftedBound b d c) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (shiftedBound_mono hc h)]
  · rw [max_eq_left h, max_eq_left (shiftedBound_mono hc h)]

/-- Composing the pullback twice: pulling `r` back through `(d,c)` then through `(d',c')`
equals pulling it back once through the composite shift. -/
theorem shiftedBound_shiftedBound (r : WithBot ℚ) (d c d' c' : ℚ) (hc : c ≠ 0) (hc' : c' ≠ 0) :
    shiftedBound (shiftedBound r d c) d' c' = shiftedBound r (c * d' + d) (c * c') := by
  cases r with
  | bot => simp
  | coe r0 =>
    simp only [shiftedBound_coe, WithBot.coe_eq_coe]
    field_simp
    ring

def mul (x y : PElem) : PElem :=
  ⟨x.m + y.m, (2 : ℚ) ^ x.m * y.b + x.b, max y.r (shiftedBound x.r y.b ((2 : ℚ) ^ y.m))⟩

instance : Mul PElem := ⟨mul⟩

instance : One PElem := ⟨⟨0, 0, ⊥⟩⟩

theorem mul_def (x y : PElem) :
    x * y = ⟨x.m + y.m, (2 : ℚ) ^ x.m * y.b + x.b,
      max y.r (shiftedBound x.r y.b ((2 : ℚ) ^ y.m))⟩ := rfl

theorem one_def : (1 : PElem) = ⟨0, 0, ⊥⟩ := rfl

theorem two_pow_pos (n : ℤ) : (0 : ℚ) < (2 : ℚ) ^ n := by positivity

theorem two_pow_ne_zero (n : ℤ) : (2 : ℚ) ^ n ≠ 0 := (two_pow_pos n).ne'

theorem mul_one (x : PElem) : x * 1 = x := by
  obtain ⟨m, b, r⟩ := x
  simp only [mul_def, one_def, PElem.mk.injEq]
  refine ⟨by simp, by simp, ?_⟩
  show max (⊥ : WithBot ℚ) (shiftedBound r 0 1) = r
  simp

theorem one_mul (x : PElem) : 1 * x = x := by
  obtain ⟨m, b, r⟩ := x
  simp only [mul_def, one_def, PElem.mk.injEq]
  refine ⟨by simp, by simp, ?_⟩
  show max r (shiftedBound (⊥ : WithBot ℚ) b ((2 : ℚ) ^ m)) = r
  simp

theorem mul_assoc (x y z : PElem) : x * y * z = x * (y * z) := by
  obtain ⟨xm, xb, xr⟩ := x
  obtain ⟨ym, yb, yr⟩ := y
  obtain ⟨zm, zb, zr⟩ := z
  simp only [mul_def, PElem.mk.injEq]
  refine ⟨by ring, ?_, ?_⟩
  · show (2 : ℚ) ^ (xm + ym) * zb + ((2 : ℚ) ^ xm * yb + xb) =
      (2 : ℚ) ^ xm * ((2 : ℚ) ^ ym * zb + yb) + xb
    rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    ring
  · show max zr (shiftedBound (max yr (shiftedBound xr yb ((2 : ℚ) ^ ym))) zb ((2 : ℚ) ^ zm)) =
      max (max zr (shiftedBound yr zb ((2 : ℚ) ^ zm)))
        (shiftedBound xr ((2 : ℚ) ^ ym * zb + yb) ((2 : ℚ) ^ (ym + zm)))
    rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), shiftedBound_max (two_pow_pos zm),
      shiftedBound_shiftedBound xr yb ((2 : ℚ) ^ ym) zb ((2 : ℚ) ^ zm)
        (two_pow_ne_zero ym) (two_pow_ne_zero zm)]
    rw [← max_assoc, max_comm zr (shiftedBound yr zb ((2 : ℚ) ^ zm)), max_assoc]

noncomputable instance : Monoid PElem where
  mul := mul
  one := One.one
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one

/-- `u(x) = x/2`, a full affine bijection of `ℚ`. -/
def u : PElem := ⟨-1, 0, ⊥⟩

/-- `v(x) = (x+1)/2`, a full affine bijection of `ℚ`. -/
def v : PElem := ⟨-1, 1 / 2, ⊥⟩

/-- `e_a`, the partial identity on `[a, ∞) ∩ ℚ`. -/
def e (a : ℚ) : PElem := ⟨0, 0, (a : WithBot ℚ)⟩

/-- The inverse of a FULL affine map `(m, b, ⊥)` (an honest bijection of `ℚ`). -/
def fullInv (m : ℤ) (b : ℚ) : PElem := ⟨-m, -b * (2 : ℚ) ^ (-m), ⊥⟩

theorem mul_fullInv (m : ℤ) (b : ℚ) :
    (⟨m, b, ⊥⟩ : PElem) * fullInv m b = 1 := by
  have h2 : (2 : ℚ) ^ (-m) = ((2 : ℚ) ^ m)⁻¹ := zpow_neg 2 m
  simp only [mul_def, fullInv, one_def, PElem.mk.injEq, h2]
  refine ⟨by ring, ?_, by simp⟩
  have hm := two_pow_ne_zero m
  field_simp
  ring

theorem fullInv_mul (m : ℤ) (b : ℚ) :
    fullInv m b * (⟨m, b, ⊥⟩ : PElem) = 1 := by
  have h2 : (2 : ℚ) ^ (-m) = ((2 : ℚ) ^ m)⁻¹ := zpow_neg 2 m
  simp only [mul_def, fullInv, one_def, PElem.mk.injEq, h2]
  refine ⟨by ring, ?_, by simp⟩
  have hm := two_pow_ne_zero m
  field_simp
  ring

/-- Equation (27), first half: `e_a e_b = e_max(a,b)`. -/
theorem e_mul_e (a b : ℚ) : e a * e b = e (max a b) := by
  simp only [e, mul_def, PElem.mk.injEq]
  refine ⟨by norm_num, by norm_num, ?_⟩
  simp only [zpow_zero, shiftedBound_zero_one]
  rw [max_comm, WithBot.coe_max]

/-- Equation (27), second half, specialized to `w ∈ {u, v}`: `w e_a w⁻¹ = e_{w(a)}`. -/
theorem u_mul_e_mul_fullInv (a : ℚ) :
    u * e a * fullInv (-1) 0 = e (a / 2) := by
  simp only [u, e, fullInv, mul_def, PElem.mk.injEq]
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

theorem v_mul_e_mul_fullInv (a : ℚ) :
    v * e a * fullInv (-1) (1 / 2) = e ((a + 1) / 2) := by
  simp only [v, e, fullInv, mul_def, PElem.mk.injEq]
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

end PElem
end FiniteAlgebraicEnvelopes
end OAI


