-- Prove2me | Definitions.Def_BirkhoffGlobalSection_FiberGate
-- name    : BirkhoffGlobalSection_FiberGate
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-01T08:30:59.375533+00:00
-- url     : https://prove2.me/theorems/87e8e9eb-dee3-44fb-be9f-ccbeb0abff65
-- title:
--   The fiber gate inequality reduced to one branch-and-bound certificate
-- statement:
--   Reduces `fiber_gate_pos` to the acceptance of a single certificate by the verified checker. The gate quantities $G=$ `fibG` and $W=G^2-F(\beta_1^2+\beta_2^2)$ are computed over a box as order-2 Taylor models in the noise symbols of $(z_1,z_2,\mu)$ (`gateT`); the $c$-interval is folded into the errors and $1/r$ is a correlated Taylor model from one Newton step. `gateT_rep` proves the representation. The goal is $\min(G^+,W^+)$ with $X^+=X+16\max(0,-h_0)$, $h_0=3-2\mu-10|z|^2$ (equal to $X$ on the domain) and $r=\sqrt{D(z)}$; its enclosure is sound (`GQ.enc_sound`). `fiber_gate_pos_of_check`: if `check GQ.enc (gateCert t) = true` for a tree $t$, then $G>0$ and $F(\beta_1^2+\beta_2^2)<G^2$ on the whole window (via the reflections $z_i\mapsto -z_i$ and `check_sound`); the hypothesis $F\ge0$ is not needed.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_IntervalChecker_TM
import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber

/-!
# The fiber gate inequality: Taylor-model enclosure and reduction to a certificate

`fiber_gate_pos` asks for `fibG > 0` and `fibF (fibBeta1² + fibBeta2²) < fibG²` on the subcritical window
`μ ∈ [0, 1/2]`, `c ∈ [2.1, 2.1 + 10⁻⁶]`, `10 |z|² ≤ 3 - 2μ`, `r = √D(z)`. This module reduces it to the
acceptance of one branch-and-bound certificate by the verified checker `check_sound`.

* `Gate`: the ingredient polynomials of `fibF`, `fibL`, `fibV` in `(z₁, z₂, μ, c)` (exact dyadic data, each
  with its evaluation lemma), box helpers (`hw`, `noise_of_mem`), the checked reciprocal bracket
  (`invOK`, `inv_mem`, `invGuess`), and the reflection lemmas `gate_neg1`, `gate_neg2`.
* `GateTM`: the gate program over order-2 Taylor models in the noise symbols of `(z₁, z₂, μ)`
  (`gateT`): the `c`-interval is folded into the errors and `1/r` is a correlated Taylor model
  (one Newton step, error bound `TM.rep_invsqrt`). `gateT_rep`: it represents `fibG`,
  `W = fibG² - fibF (fibBeta1² + fibBeta2²)` and the cap `h₀ = 3 - 2μ - 10|z|²`.
  The goal is `min(G⁺, W⁺)` with `X⁺ = X + 16 max(0, -h₀)` (equal to `X` on the cap) and
  `r = √D(z)`; its enclosure `GQ.enc` is sound (`GQ.enc_sound`).
* `GateAsm`: `fiber_gate_pos_of_check`: if `check GQ.enc (gateCert t) = true` for a tree `t`, the gate
  inequality holds (the reflection to `z₁, z₂ ≥ 0` and `check_sound`). The hypothesis `0 ≤ fibF` is not
  needed.

The block-Hessian structure behind `fibG` and `fibBeta`: Grisa, arXiv 2026 (Thm 3.7(b)); see
`tHess_det_pos_of_fiber`.
-/

namespace BirkhoffGlobalSection.TangentialHessian.Checker

open CNum

namespace Gate

/-! ### Ingredient polynomials in `(z₁, z₂, μ, c)` (exact dyadic data) -/

def FpP : Poly Dy := [((⟨4, 0⟩ : Dy), [6, 0, 0, 0]), ((⟨12, 0⟩ : Dy), [4, 2, 0, 0]), ((⟨-4, 0⟩ : Dy), [4, 0, 1, 0]), ((⟨12, 0⟩ : Dy), [2, 4, 0, 0]), ((⟨1, 0⟩ : Dy), [2, 0, 2, 0]), ((⟨-2, 0⟩ : Dy), [2, 0, 0, 1]), ((⟨4, 0⟩ : Dy), [0, 6, 0, 0]), ((⟨4, 0⟩ : Dy), [0, 4, 1, 0]), ((⟨1, 0⟩ : Dy), [0, 2, 2, 0]), ((⟨-2, 0⟩ : Dy), [0, 2, 0, 1]), ((⟨-1, 0⟩ : Dy), [0, 0, 1, 0]), ((⟨1, 0⟩ : Dy), [0, 0, 0, 0])]
def Lp00P : Poly Dy := [((⟨-60, 0⟩ : Dy), [4, 0, 0, 0]), ((⟨-72, 0⟩ : Dy), [2, 2, 0, 0]), ((⟨24, 0⟩ : Dy), [2, 0, 1, 0]), ((⟨-12, 0⟩ : Dy), [0, 4, 0, 0]), ((⟨-1, 0⟩ : Dy), [0, 0, 2, 0]), ((⟨2, 0⟩ : Dy), [0, 0, 0, 1])]
def Lp01P : Poly Dy := [((⟨-48, 0⟩ : Dy), [3, 1, 0, 0]), ((⟨-48, 0⟩ : Dy), [1, 3, 0, 0])]
def Lp11P : Poly Dy := [((⟨-12, 0⟩ : Dy), [4, 0, 0, 0]), ((⟨-72, 0⟩ : Dy), [2, 2, 0, 0]), ((⟨-60, 0⟩ : Dy), [0, 4, 0, 0]), ((⟨-24, 0⟩ : Dy), [0, 2, 1, 0]), ((⟨-1, 0⟩ : Dy), [0, 0, 2, 0]), ((⟨2, 0⟩ : Dy), [0, 0, 0, 1])]
def vp0P : Poly Dy := [((⟨-12, 0⟩ : Dy), [5, 0, 0, 0]), ((⟨-24, 0⟩ : Dy), [3, 2, 0, 0]), ((⟨8, 0⟩ : Dy), [3, 0, 1, 0]), ((⟨-12, 0⟩ : Dy), [1, 4, 0, 0]), ((⟨-1, 0⟩ : Dy), [1, 0, 2, 0]), ((⟨2, 0⟩ : Dy), [1, 0, 0, 1])]
def vp1P : Poly Dy := [((⟨-12, 0⟩ : Dy), [4, 1, 0, 0]), ((⟨-24, 0⟩ : Dy), [2, 3, 0, 0]), ((⟨-12, 0⟩ : Dy), [0, 5, 0, 0]), ((⟨-8, 0⟩ : Dy), [0, 3, 1, 0]), ((⟨-1, 0⟩ : Dy), [0, 1, 2, 0]), ((⟨2, 0⟩ : Dy), [0, 1, 0, 1])]
def dD0P : Poly Dy := [((⟨16, 0⟩ : Dy), [3, 0, 0, 0]), ((⟨16, 0⟩ : Dy), [1, 2, 0, 0]), ((⟨-8, 0⟩ : Dy), [1, 0, 0, 0])]
def dD1P : Poly Dy := [((⟨16, 0⟩ : Dy), [2, 1, 0, 0]), ((⟨16, 0⟩ : Dy), [0, 3, 0, 0]), ((⟨8, 0⟩ : Dy), [0, 1, 0, 0])]
def hD00P : Poly Dy := [((⟨48, 0⟩ : Dy), [2, 0, 0, 0]), ((⟨16, 0⟩ : Dy), [0, 2, 0, 0]), ((⟨-8, 0⟩ : Dy), [0, 0, 0, 0])]
def hD01P : Poly Dy := [((⟨32, 0⟩ : Dy), [1, 1, 0, 0])]
def hD11P : Poly Dy := [((⟨16, 0⟩ : Dy), [2, 0, 0, 0]), ((⟨48, 0⟩ : Dy), [0, 2, 0, 0]), ((⟨8, 0⟩ : Dy), [0, 0, 0, 0])]
def ZqP : Poly Dy := [((⟨1, 0⟩ : Dy), [2, 0, 0, 0]), ((⟨1, 0⟩ : Dy), [0, 2, 0, 0])]

/-- The phase point with `z = (z₁, z₂)` (the gate data do not depend on `w`). -/
def sOf (z1 z2 : ℝ) : Phase := ![z1, z2, 0, 0]

@[simp] theorem sOf_zero (z1 z2 : ℝ) : sOf z1 z2 0 = z1 := rfl
@[simp] theorem sOf_one (z1 z2 : ℝ) : sOf z1 z2 1 = z2 := rfl

section evals

variable (z1 z2 μ c : ℝ)

theorem eval4 (p : Poly Dy) : NP.eval 4 (NP.ofFlat 4 p) [z1, z2, μ, c] = evalR p [z1, z2, μ, c] :=
  NP.eval_ofFlat 4 p _ rfl

theorem FpP_eval : NP.eval 4 (NP.ofFlat 4 FpP) [z1, z2, μ, c] =
    1 - μ - 2 * c * (z1 ^ 2 + z2 ^ 2) + (2 * (z1 ^ 2 + z2 ^ 2) - μ) ^ 2 * z1 ^ 2
      + (2 * (z1 ^ 2 + z2 ^ 2) + μ) ^ 2 * z2 ^ 2 := by rw [eval4]; simp [evalR, monoR, FpP]; ring
theorem Lp00P_eval : NP.eval 4 (NP.ofFlat 4 Lp00P) [z1, z2, μ, c] =
    2 * c - μ ^ 2 + 24 * μ * z1 ^ 2 - 60 * z1 ^ 4 - 72 * z1 ^ 2 * z2 ^ 2 - 12 * z2 ^ 4 := by rw [eval4]; simp [evalR, monoR, Lp00P]; ring
theorem Lp01P_eval : NP.eval 4 (NP.ofFlat 4 Lp01P) [z1, z2, μ, c] =
    -48 * z1 * z2 * (z1 ^ 2 + z2 ^ 2) := by rw [eval4]; simp [evalR, monoR, Lp01P]; ring
theorem Lp11P_eval : NP.eval 4 (NP.ofFlat 4 Lp11P) [z1, z2, μ, c] =
    2 * c - μ ^ 2 - 24 * μ * z2 ^ 2 - 12 * z1 ^ 4 - 72 * z1 ^ 2 * z2 ^ 2 - 60 * z2 ^ 4 := by rw [eval4]; simp [evalR, monoR, Lp11P]; ring
theorem vp0P_eval : NP.eval 4 (NP.ofFlat 4 vp0P) [z1, z2, μ, c] =
    z1 * (2 * c - μ ^ 2 + 8 * μ * z1 ^ 2 - 12 * (z1 ^ 2 + z2 ^ 2) ^ 2) := by rw [eval4]; simp [evalR, monoR, vp0P]; ring
theorem vp1P_eval : NP.eval 4 (NP.ofFlat 4 vp1P) [z1, z2, μ, c] =
    z2 * (2 * c - μ ^ 2 - 8 * μ * z2 ^ 2 - 12 * (z1 ^ 2 + z2 ^ 2) ^ 2) := by rw [eval4]; simp [evalR, monoR, vp1P]; ring
theorem dD0P_eval : NP.eval 4 (NP.ofFlat 4 dD0P) [z1, z2, μ, c] = dD (sOf z1 z2) 0 := by
  rw [eval4]; simp [evalR, monoR, dD0P, dD, sOf]; ring
theorem dD1P_eval : NP.eval 4 (NP.ofFlat 4 dD1P) [z1, z2, μ, c] = dD (sOf z1 z2) 1 := by
  rw [eval4]; simp [evalR, monoR, dD1P, dD, sOf]; ring
theorem hD00P_eval : NP.eval 4 (NP.ofFlat 4 hD00P) [z1, z2, μ, c] = hD (sOf z1 z2) 0 0 := by
  rw [eval4]; simp [evalR, monoR, hD00P, hD, sOf]; ring
theorem hD01P_eval : NP.eval 4 (NP.ofFlat 4 hD01P) [z1, z2, μ, c] = hD (sOf z1 z2) 0 1 := by
  rw [eval4]; simp [evalR, monoR, hD01P, hD, sOf]; ring
theorem hD11P_eval : NP.eval 4 (NP.ofFlat 4 hD11P) [z1, z2, μ, c] = hD (sOf z1 z2) 1 1 := by
  rw [eval4]; simp [evalR, monoR, hD11P, hD, sOf]; ring
theorem ZqP_eval : NP.eval 4 (NP.ofFlat 4 ZqP) [z1, z2, μ, c] = zNormSq (sOf z1 z2) := by
  rw [eval4]; simp [evalR, monoR, ZqP, zNormSq, sOf]

end evals

/-! ### Boxes: centre, half-width, noise; the checked reciprocal bracket -/

variable {α : Type} [CNum α]

/-- Half-width `(hi - lo)/2`. -/
def hw (I : Iv α) : α := half (sub I.2 I.1)

theorem noise_of_mem {x : ℝ} {I : Iv α} (hx : Mem x I) :
    ∃ t : ℝ, |t| ≤ 1 ∧ x = toReal (mid I) + toReal (hw I) * t := by
  unfold Mem at hx
  have hm : toReal (mid I) = (toReal I.1 + toReal I.2) / 2 := by simp [mid]
  have hw' : toReal (hw I) = (toReal I.2 - toReal I.1) / 2 := by simp [hw]
  by_cases h0 : toReal (hw I) = 0
  · refine ⟨0, by simp, ?_⟩
    rw [hm, h0]; rw [hw'] at h0; simp; linarith [hx.1, hx.2]
  · have hpos : 0 < toReal (hw I) := by
      rw [hw'] at h0 ⊢; rcases lt_or_eq_of_le (show toReal I.1 ≤ toReal I.2 by linarith [hx.1, hx.2]) with h | h
      · linarith
      · exact absurd (by rw [h]; ring) h0
    refine ⟨(x - toReal (mid I)) / toReal (hw I), ?_, by field_simp; ring⟩
    rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le, hm, hw']
    constructor <;> linarith [hx.1, hx.2]

/-- Check that `K` brackets `1 / r` for every `r ∈ J` (with `J` positive). -/
def invOK (J K : Iv α) : Bool :=
  blt zero J.1 && ble zero K.1 && ble (mul J.2 K.1) one && ble one (mul J.1 K.2)

theorem inv_mem {r : ℝ} {J K : Iv α} (hr : Mem r J) (h : invOK J K = true) :
    0 < r ∧ Mem r⁻¹ K := by
  simp only [invOK, Bool.and_eq_true, blt_iff, ble_iff, toReal_zero, toReal_mul, toReal_one] at h
  obtain ⟨⟨⟨ha, hk0⟩, hb⟩, hc⟩ := h
  unfold Mem at hr ⊢
  have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
  refine ⟨hr0, ?_, ?_⟩
  · -- r · K.1 ≤ J.2 · K.1 ≤ 1
    rw [inv_eq_one_div, le_div_iff₀ hr0]
    nlinarith [hr.2]
  · -- 1 ≤ J.1 · K.2 ≤ r · K.2
    have hK2 : 0 < toReal K.2 := by
      by_contra hneg
      push Not at hneg
      nlinarith
    rw [inv_eq_one_div, div_le_iff₀ hr0]
    nlinarith [hr.1]

/-- A dyadic bracket guess for `1 / r`, `r ∈ J`: `⌊2^(e+k)/m⌋ / 2^k` for `1/J.2` and one unit more for
`1/J.1`. Only positive divisions (so the rounding convention of `Int` division does not matter); only a
guess: soundness uses `invOK`. -/
def invGuess (J : Iv Dy) (k : ℕ) : Iv Dy :=
  (⟨Dy.two (J.2.e + k) / J.2.m, k⟩, ⟨Dy.two (J.1.e + k) / J.1.m + 1, k⟩)

/-! ### Constants and the `1/r` form of `kBr` -/

/-- The dyadic `m / 2^e`. -/
def cst (m : ℤ) (e : ℕ) : Dy := ⟨m, e⟩

@[simp] theorem cst_toReal (m : ℤ) (e : ℕ) : toReal (cst m e) = (m : ℝ) / 2 ^ e := rfl

/-- `kBr` with `1/r` powers written as products of `r⁻¹` (for linking to the affine program). -/
theorem kBr_eq (μ r : ℝ) (s : Phase) (i j : Fin 4) :
    kBr μ r s i j = μ * (hZ i j * r⁻¹
      - (1 / 2) * (dZ s i * dD s j + dZ s j * dD s i) * (r⁻¹ * (r⁻¹ * r⁻¹))
      - (1 / 2) * (zNormSq s * hD s i j) * (r⁻¹ * (r⁻¹ * r⁻¹))
      + (3 / 4) * (zNormSq s * (dD s i * dD s j)) * (r⁻¹ * (r⁻¹ * r⁻¹) * (r⁻¹ * r⁻¹))) := by
  unfold kBr; ring


/-- Precision (bits) of the `1/r` bracket guess. -/
def invBits : ℕ := 64

/-! ### Reduction to the quarter disk -/

section symmetry

variable (μ c r z1 z2 : ℝ)

theorem fibF_neg1 : fibF μ c r (sOf (-z1) z2) = fibF μ c r (sOf z1 z2) := by
  simp [fibF, zNormSq, sOf]
theorem fibF_neg2 : fibF μ c r (sOf z1 (-z2)) = fibF μ c r (sOf z1 z2) := by
  simp [fibF, zNormSq, sOf]
theorem fibL00_neg1 : fibL00 μ c r (sOf (-z1) z2) = fibL00 μ c r (sOf z1 z2) := by
  simp [fibL00, kBr, zNormSq, dZ, dD, hZ, hD, sOf]; ring
theorem fibL00_neg2 : fibL00 μ c r (sOf z1 (-z2)) = fibL00 μ c r (sOf z1 z2) := by
  simp [fibL00, kBr, zNormSq, dZ, dD, hZ, hD, sOf]; ring
theorem fibL11_neg1 : fibL11 μ c r (sOf (-z1) z2) = fibL11 μ c r (sOf z1 z2) := by
  simp [fibL11, kBr, zNormSq, dZ, dD, hZ, hD, sOf]; ring
theorem fibL11_neg2 : fibL11 μ c r (sOf z1 (-z2)) = fibL11 μ c r (sOf z1 z2) := by
  simp [fibL11, kBr, zNormSq, dZ, dD, hZ, hD, sOf]; ring
theorem fibL01_neg1 : fibL01 μ r (sOf (-z1) z2) = -fibL01 μ r (sOf z1 z2) := by
  simp [fibL01, kBr, zNormSq, dZ, dD, hZ, hD, sOf]; ring
theorem fibL01_neg2 : fibL01 μ r (sOf z1 (-z2)) = -fibL01 μ r (sOf z1 z2) := by
  simp [fibL01, kBr, zNormSq, dZ, dD, hZ, hD, sOf]; ring
theorem fibV0_neg1 : fibV0 μ c r (sOf (-z1) z2) = -fibV0 μ c r (sOf z1 z2) := by
  simp [fibV0, zNormSq, dZ, dD, sOf]; ring
theorem fibV0_neg2 : fibV0 μ c r (sOf z1 (-z2)) = fibV0 μ c r (sOf z1 z2) := by
  simp [fibV0, zNormSq, dZ, dD, sOf]
theorem fibV1_neg1 : fibV1 μ c r (sOf (-z1) z2) = fibV1 μ c r (sOf z1 z2) := by
  simp [fibV1, zNormSq, dZ, dD, sOf]
theorem fibV1_neg2 : fibV1 μ c r (sOf z1 (-z2)) = -fibV1 μ c r (sOf z1 z2) := by
  simp [fibV1, zNormSq, dZ, dD, sOf]; ring

theorem zNormSq_sOf : zNormSq (sOf z1 z2) = z1 ^ 2 + z2 ^ 2 := by simp [zNormSq, sOf]

/-- `G` and `W` are even in `z₁`. -/
theorem gate_neg1 :
    fibG μ c r (sOf (-z1) z2) = fibG μ c r (sOf z1 z2) ∧
      fibBeta1 μ c r (sOf (-z1) z2) ^ 2 + fibBeta2 μ c r (sOf (-z1) z2) ^ 2
        = fibBeta1 μ c r (sOf z1 z2) ^ 2 + fibBeta2 μ c r (sOf z1 z2) ^ 2 := by
  constructor
  · simp only [fibG, fibF_neg1, fibL00_neg1, fibL11_neg1, fibL01_neg1, fibV0_neg1, fibV1_neg1, zNormSq_sOf]
    ring
  · simp only [fibBeta1, fibBeta2, fibF_neg1, fibL00_neg1, fibL11_neg1, fibL01_neg1, fibV0_neg1,
      fibV1_neg1, sOf_zero, sOf_one]
    ring

/-- `G` and `W` are even in `z₂`. -/
theorem gate_neg2 :
    fibG μ c r (sOf z1 (-z2)) = fibG μ c r (sOf z1 z2) ∧
      fibBeta1 μ c r (sOf z1 (-z2)) ^ 2 + fibBeta2 μ c r (sOf z1 (-z2)) ^ 2
        = fibBeta1 μ c r (sOf z1 z2) ^ 2 + fibBeta2 μ c r (sOf z1 z2) ^ 2 := by
  constructor
  · simp only [fibG, fibF_neg2, fibL00_neg2, fibL11_neg2, fibL01_neg2, fibV0_neg2, fibV1_neg2, zNormSq_sOf]
    ring
  · simp only [fibBeta1, fibBeta2, fibF_neg2, fibL00_neg2, fibL11_neg2, fibL01_neg2, fibV0_neg2,
      fibV1_neg2, sOf_zero, sOf_one]
    ring

end symmetry

end Gate

namespace GateTM

open Gate

/-! ### Extra data: `D = secondCollisionDistanceSq` and the cap `h₀ = 3 - 2μ - 10 Z` -/

def DP : Poly Dy := [((⟨4, 0⟩ : Dy), [4, 0, 0, 0]), ((⟨8, 0⟩ : Dy), [2, 2, 0, 0]), ((⟨-4, 0⟩ : Dy), [2, 0, 0, 0]), ((⟨4, 0⟩ : Dy), [0, 4, 0, 0]), ((⟨4, 0⟩ : Dy), [0, 2, 0, 0]), ((⟨1, 0⟩ : Dy), [0, 0, 0, 0])]
def H0P : Poly Dy := [((⟨3, 0⟩ : Dy), [0, 0, 0, 0]), ((⟨-2, 0⟩ : Dy), [0, 0, 1, 0]), ((⟨-10, 0⟩ : Dy), [2, 0, 0, 0]), ((⟨-10, 0⟩ : Dy), [0, 2, 0, 0])]

theorem DP_eval (z1 z2 μ c : ℝ) :
    NP.eval 4 (NP.ofFlat 4 DP) [z1, z2, μ, c] = secondCollisionDistanceSq (sOf z1 z2) := by
  rw [eval4]; simp [evalR, monoR, DP, secondCollisionDistanceSq, sOf]; ring

theorem H0P_eval (z1 z2 μ c : ℝ) :
    NP.eval 4 (NP.ofFlat 4 H0P) [z1, z2, μ, c] = 3 - 2 * μ - 10 * zNormSq (sOf z1 z2) := by
  rw [eval4]; simp [evalR, monoR, H0P, zNormSq, sOf]; ring

/-! ### The Taylor-model program -/

/-- Truncation order. -/
def ord : ℕ := 2

abbrev T := TM Dy 3

noncomputable def pc (M H : List Dy) (p : Poly Dy) : T := TM.piece 3 ord M H (NP.ofFlat 4 p)

noncomputable def tm (A B : T) : T := TM.mul ord A B

def mapC : (n : ℕ) → (Dy → Dy) → NP Dy n → NP Dy n
  | 0, f, a => f a
  | n + 1, f, cs => (cs : List (NP Dy n)).map (mapC n f)

noncomputable def c0 : (n : ℕ) → NP Dy n → Dy
  | 0, a => a
  | _ + 1, [] => CNum.zero
  | n + 1, c :: _ => c0 n c

/-- Truncation to `2^-64` (only builds a candidate; soundness does not depend on it). -/
def rnd (x : Dy) : Dy := ⟨(x.m * Dy.two 64) / Dy.two x.e, 64⟩

/-- The interval `K` as a Taylor model with no dependence (fallback for `1/r`). -/
noncomputable def ofIv (K : Iv Dy) : T := ⟨NP.mono 3 (mid K) [], hw K⟩

/-- Candidate Taylor polynomial of `D^{-1/2}`: one Newton step from `mid K`, then the order-2
expansion in `d = D - D(centre)`, coefficients truncated. -/
noncomputable def yCand (Dt : T) (K : Iv Dy) : NP Dy 3 :=
  let D0 := c0 3 Dt.p
  let y0 := mid K
  let y := rnd (half (CNum.mul y0 (CNum.sub (CNum.natCast 3) (CNum.mul (CNum.mul y0 y0) D0))))
  let y2 := CNum.mul y y
  let d : T := ⟨NP.add 3 Dt.p (NP.mono 3 (CNum.neg D0) []), CNum.zero⟩
  let k1 := rnd (CNum.neg (half (CNum.mul y y2)))
  let k2 := rnd (CNum.mul (⟨3, 3⟩ : Dy) (CNum.mul y (CNum.mul y2 y2)))
  mapC 3 rnd (TM.add (TM.const 3 y) (TM.add (TM.scal k1 d) (TM.scal k2 (tm d d)))).p

/-- `1/r` as a Taylor model: the checked Newton form when the candidate is nonnegative, else `K`. -/
noncomputable def irT (M H : List Dy) (K : Iv Dy) : T :=
  let Dt := pc M H DP
  let Yp := yCand Dt K
  if ble CNum.zero (NP.ieval 3 Yp (NP.unitBox 3)).1 then TM.invsqrt ord Dt Yp K.2 else ofIv K

noncomputable def kbT (Vm IR ir3 ir5 Zq : T) (hz : Dy) (dZi dZj dDi dDj hDij : T) : T :=
  tm Vm (TM.add (TM.sub (TM.sub (TM.scal hz IR) (tm (TM.scal (cst 1 1) (TM.add (tm dZi dDj) (tm dZj dDi))) ir3))
      (tm (TM.scal (cst 1 1) (tm Zq hDij)) ir3))
    (tm (TM.scal (cst 3 2) (tm Zq (tm dDi dDj))) ir5))

/-- `(G, W, h₀)` on the box `[I₀, I₁, I₂, I₃]` (`z₁, z₂, μ, c`) with `1/r ∈ K`. -/
noncomputable def gateT (I0 I1 I2 I3 K : Iv Dy) : T × T × T :=
  let M : List Dy := [mid I0, mid I1, mid I2, mid I3]
  let H : List Dy := [hw I0, hw I1, hw I2, hw I3]
  let V0 : T := TM.var 3 0 (mid I0) (hw I0)
  let V1 : T := TM.var 3 1 (mid I1) (hw I1)
  let Vm : T := TM.var 3 2 (mid I2) (hw I2)
  let IR := irT M H K
  let ir2 := tm IR IR
  let ir3 := tm IR ir2
  let ir5 := tm ir3 ir2
  let Zq := pc M H ZqP
  let dZ0 := TM.scal (cst 2 0) V0
  let dZ1 := TM.scal (cst 2 0) V1
  let dD0 := pc M H dD0P
  let dD1 := pc M H dD1P
  let F := TM.add (pc M H FpP) (TM.scal (cst 2 0) (tm Vm (tm Zq IR)))
  let L00 := TM.sub (pc M H Lp00P) (kbT Vm IR ir3 ir5 Zq (cst 2 0) dZ0 dZ0 dD0 dD0 (pc M H hD00P))
  let L01 := TM.sub (pc M H Lp01P) (kbT Vm IR ir3 ir5 Zq (cst 0 0) dZ0 dZ1 dD0 dD1 (pc M H hD01P))
  let L11 := TM.sub (pc M H Lp11P) (kbT Vm IR ir3 ir5 Zq (cst 2 0) dZ1 dZ1 dD1 dD1 (pc M H hD11P))
  let v0 := TM.sub (pc M H vp0P) (tm Vm (TM.sub (tm dZ0 IR) (tm (TM.scal (cst 1 1) (tm Zq dD0)) ir3)))
  let v1 := TM.sub (pc M H vp1P) (tm Vm (TM.sub (tm dZ1 IR) (tm (TM.scal (cst 1 1) (tm Zq dD1)) ir3)))
  let v00 := tm v0 v0
  let v01 := tm v0 v1
  let v11 := tm v1 v1
  let G := TM.sub (TM.add (tm F (TM.sub (tm L00 L11) (tm L01 L01)))
      (TM.add (TM.sub (tm L11 v00) (TM.scal (cst 2 0) (tm L01 v01))) (tm L00 v11)))
    (TM.scal (cst 16 0) (tm (tm F F) Zq))
  let b1 := TM.add (tm F (TM.add (TM.sub (tm L11 (TM.scal (cst (-4) 0) V1))
        (TM.scal (cst 2 0) (tm L01 (TM.scal (cst (-4) 0) V0)))) (tm L00 (TM.scal (cst (-12) 0) V1))))
      (TM.add (TM.sub (tm (TM.scal (cst (-12) 0) V1) v00) (TM.scal (cst 2 0) (tm (TM.scal (cst (-4) 0) V0) v01)))
        (tm (TM.scal (cst (-4) 0) V1) v11))
  let b2 := TM.add (tm F (TM.add (TM.sub (tm L11 (TM.scal (cst 12 0) V0))
        (TM.scal (cst 2 0) (tm L01 (TM.scal (cst 4 0) V1)))) (tm L00 (TM.scal (cst 4 0) V0))))
      (TM.add (TM.sub (tm (TM.scal (cst 4 0) V0) v00) (TM.scal (cst 2 0) (tm (TM.scal (cst 4 0) V1) v01)))
        (tm (TM.scal (cst 12 0) V0) v11))
  (G, TM.sub (tm G G) (tm F (TM.add (tm b1 b1) (tm b2 b2))), pc M H H0P)

/-! ### Soundness -/

theorem trep_of_eq {d : List ℝ} {A : T} {x y : ℝ} (h : TM.Rep d A x) (e : x = y) : TM.Rep d A y :=
  e ▸ h

theorem rep_ofIv {d : List ℝ} (hl : d.length = 3) {x : ℝ} {K : Iv Dy} (hx : Mem x K) :
    TM.Rep d (ofIv K) x := by
  unfold TM.Rep ofIv
  rw [NP.eval_mono 3 _ [] d hl]
  unfold Mem at hx
  have hm : toReal (mid K) = (toReal K.1 + toReal K.2) / 2 := by simp [mid]
  have hw' : toReal (hw K) = (toReal K.2 - toReal K.1) / 2 := by simp [hw]
  simp only [monoR, mul_one]
  rw [hm, hw', abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem gateT_rep {z1 z2 μ c r : ℝ} {I0 I1 I2 I3 K : Iv Dy}
    (h0 : Mem z1 I0) (h1 : Mem z2 I1) (h2 : Mem μ I2) (h3 : Mem c I3)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq (sOf z1 z2)) (hK : Mem r⁻¹ K) :
    ∃ d : List ℝ, AF.Noise d ∧ d.length = 3 ∧
      TM.Rep d (gateT I0 I1 I2 I3 K).1 (fibG μ c r (sOf z1 z2)) ∧
      TM.Rep d (gateT I0 I1 I2 I3 K).2.1
        (fibG μ c r (sOf z1 z2) ^ 2 - fibF μ c r (sOf z1 z2) *
          (fibBeta1 μ c r (sOf z1 z2) ^ 2 + fibBeta2 μ c r (sOf z1 z2) ^ 2)) ∧
      TM.Rep d (gateT I0 I1 I2 I3 K).2.2 (3 - 2 * μ - 10 * zNormSq (sOf z1 z2)) := by
  obtain ⟨t0, ht0, e0⟩ := noise_of_mem h0
  obtain ⟨t1, ht1, e1⟩ := noise_of_mem h1
  obtain ⟨t2, ht2, e2⟩ := noise_of_mem h2
  obtain ⟨t3, ht3, e3⟩ := noise_of_mem h3
  set d : List ℝ := [t0, t1, t2] with hd_def
  have hd : AF.Noise d := by
    intro t ht; simp only [hd_def, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  have hl : d.length = 3 := rfl
  -- box variables
  have rV0 : TM.Rep d (TM.var 3 0 (mid I0) (hw I0) : T) z1 :=
    trep_of_eq (TM.rep_var hl 0 _ _) (by simp [hd_def, monoR, e0])
  have rV1 : TM.Rep d (TM.var 3 1 (mid I1) (hw I1) : T) z2 :=
    trep_of_eq (TM.rep_var hl 1 _ _) (by simp [hd_def, monoR, e1])
  have rVm : TM.Rep d (TM.var 3 2 (mid I2) (hw I2) : T) μ :=
    trep_of_eq (TM.rep_var hl 2 _ _) (by simp [hd_def, monoR, e2])
  -- polynomial pieces
  have hpt : NP.addPt [mid I0, mid I1, mid I2, mid I3] (NP.mulPt [hw I0, hw I1, hw I2, hw I3] (d ++ [t3]))
      = [z1, z2, μ, c] := by
    simp [hd_def, NP.addPt, NP.mulPt, e0, e1, e2, e3]
  have rpc : ∀ p : Poly Dy, TM.Rep d (pc [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] p)
      (NP.eval 4 (NP.ofFlat 4 p) [z1, z2, μ, c]) := fun p => by
    have := TM.rep_piece hd hl ht3 ord (M := [mid I0, mid I1, mid I2, mid I3])
      (H := [hw I0, hw I1, hw I2, hw I3]) rfl rfl (NP.ofFlat 4 p)
    rwa [hpt] at this
  -- 1/r
  have rIR : TM.Rep d (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K) r⁻¹ := by
    unfold irT
    simp only
    split
    · rename_i hY
      exact TM.rep_invsqrt hd hl ord hr (trep_of_eq (rpc DP) (by rw [DP_eval, hr2])) _ hY K.2 hK.2
    · exact rep_ofIv hl hK
  -- ingredients
  have rZq := trep_of_eq (rpc ZqP) (ZqP_eval z1 z2 μ c)
  have rdD0 := trep_of_eq (rpc dD0P) (dD0P_eval z1 z2 μ c)
  have rdD1 := trep_of_eq (rpc dD1P) (dD1P_eval z1 z2 μ c)
  have rhD00 := trep_of_eq (rpc hD00P) (hD00P_eval z1 z2 μ c)
  have rhD01 := trep_of_eq (rpc hD01P) (hD01P_eval z1 z2 μ c)
  have rhD11 := trep_of_eq (rpc hD11P) (hD11P_eval z1 z2 μ c)
  have rdZ0 : TM.Rep d _ (dZ (sOf z1 z2) 0) := trep_of_eq (TM.rep_scal (cst 2 0) rV0) (by simp [dZ])
  have rdZ1 : TM.Rep d _ (dZ (sOf z1 z2) 1) := trep_of_eq (TM.rep_scal (cst 2 0) rV1) (by simp [dZ])
  have rir2 := TM.rep_mul hd ord rIR rIR
  have rir3 := TM.rep_mul hd ord rIR rir2
  have rir5 := TM.rep_mul hd ord rir3 rir2
  have rkb : ∀ (hz : Dy) {Zi Zj Di Dj Hij : T} {xZi xZj xDi xDj xH : ℝ},
      TM.Rep d Zi xZi → TM.Rep d Zj xZj → TM.Rep d Di xDi → TM.Rep d Dj xDj → TM.Rep d Hij xH →
      TM.Rep d (kbT (TM.var 3 2 (mid I2) (hw I2))
          (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K)
          (tm (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K)
            (tm (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K)
              (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K)))
          (tm (tm (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K)
              (tm (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K)
                (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K)))
            (tm (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K)
              (irT [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] K)))
          (pc [mid I0, mid I1, mid I2, mid I3] [hw I0, hw I1, hw I2, hw I3] ZqP)
          hz Zi Zj Di Dj Hij)
        (μ * (toReal hz * r⁻¹ - (1 / 2) * (xZi * xDj + xZj * xDi) * (r⁻¹ * (r⁻¹ * r⁻¹))
          - (1 / 2) * (zNormSq (sOf z1 z2) * xH) * (r⁻¹ * (r⁻¹ * r⁻¹))
          + (3 / 4) * (zNormSq (sOf z1 z2) * (xDi * xDj)) * (r⁻¹ * (r⁻¹ * r⁻¹) * (r⁻¹ * r⁻¹)))) := by
    intro hz Zi Zj Di Dj Hij xZi xZj xDi xDj xH hZi hZj hDi hDj hH
    unfold kbT tm
    exact trep_of_eq
      (TM.rep_mul hd ord rVm (TM.rep_add (TM.rep_sub (TM.rep_sub (TM.rep_scal hz rIR)
        (TM.rep_mul hd ord (TM.rep_scal _ (TM.rep_add (TM.rep_mul hd ord hZi hDj) (TM.rep_mul hd ord hZj hDi))) rir3))
        (TM.rep_mul hd ord (TM.rep_scal _ (TM.rep_mul hd ord rZq hH)) rir3))
        (TM.rep_mul hd ord (TM.rep_scal _ (TM.rep_mul hd ord rZq (TM.rep_mul hd ord hDi hDj))) rir5)))
      (by simp only [cst_toReal]; push_cast; ring)
  -- the fiber data
  have rF : TM.Rep d _ (fibF μ c r (sOf z1 z2)) :=
    trep_of_eq (TM.rep_add (rpc FpP) (TM.rep_scal (cst 2 0) (TM.rep_mul hd ord rVm (TM.rep_mul hd ord rZq rIR))))
      (by rw [FpP_eval]; simp only [fibF, zNormSq, sOf_zero, sOf_one, cst_toReal]; field_simp; ring)
  have rL00 : TM.Rep d _ (fibL00 μ c r (sOf z1 z2)) :=
    trep_of_eq (TM.rep_sub (rpc Lp00P) (rkb (cst 2 0) rdZ0 rdZ0 rdD0 rdD0 rhD00))
      (by rw [Lp00P_eval, fibL00, kBr_eq]; simp [hZ, sOf_zero, sOf_one])
  have rL01 : TM.Rep d _ (fibL01 μ r (sOf z1 z2)) :=
    trep_of_eq (TM.rep_sub (rpc Lp01P) (rkb (cst 0 0) rdZ0 rdZ1 rdD0 rdD1 rhD01))
      (by rw [Lp01P_eval, fibL01, kBr_eq]; simp [hZ, sOf_zero, sOf_one])
  have rL11 : TM.Rep d _ (fibL11 μ c r (sOf z1 z2)) :=
    trep_of_eq (TM.rep_sub (rpc Lp11P) (rkb (cst 2 0) rdZ1 rdZ1 rdD1 rdD1 rhD11))
      (by rw [Lp11P_eval, fibL11, kBr_eq]; simp [hZ, sOf_zero, sOf_one])
  have rv0 : TM.Rep d _ (fibV0 μ c r (sOf z1 z2)) :=
    trep_of_eq (TM.rep_sub (rpc vp0P) (TM.rep_mul hd ord rVm (TM.rep_sub (TM.rep_mul hd ord rdZ0 rIR)
      (TM.rep_mul hd ord (TM.rep_scal (cst 1 1) (TM.rep_mul hd ord rZq rdD0)) rir3))))
      (by rw [vp0P_eval]; simp only [fibV0, zNormSq, sOf_zero, sOf_one, cst_toReal]; field_simp; ring)
  have rv1 : TM.Rep d _ (fibV1 μ c r (sOf z1 z2)) :=
    trep_of_eq (TM.rep_sub (rpc vp1P) (TM.rep_mul hd ord rVm (TM.rep_sub (TM.rep_mul hd ord rdZ1 rIR)
      (TM.rep_mul hd ord (TM.rep_scal (cst 1 1) (TM.rep_mul hd ord rZq rdD1)) rir3))))
      (by rw [vp1P_eval]; simp only [fibV1, zNormSq, sOf_zero, sOf_one, cst_toReal]; field_simp; ring)
  have rv00 := TM.rep_mul hd ord rv0 rv0
  have rv01 := TM.rep_mul hd ord rv0 rv1
  have rv11 := TM.rep_mul hd ord rv1 rv1
  -- the gate
  have rG : TM.Rep d _ (fibG μ c r (sOf z1 z2)) :=
    trep_of_eq (TM.rep_sub (TM.rep_add (TM.rep_mul hd ord rF (TM.rep_sub (TM.rep_mul hd ord rL00 rL11)
          (TM.rep_mul hd ord rL01 rL01)))
        (TM.rep_add (TM.rep_sub (TM.rep_mul hd ord rL11 rv00)
          (TM.rep_scal (cst 2 0) (TM.rep_mul hd ord rL01 rv01)))
          (TM.rep_mul hd ord rL00 rv11)))
      (TM.rep_scal (cst 16 0) (TM.rep_mul hd ord (TM.rep_mul hd ord rF rF) rZq)))
      (by simp only [fibG, cst_toReal]; norm_num; ring)
  have rb1 : TM.Rep d _ (fibBeta1 μ c r (sOf z1 z2)) :=
    trep_of_eq (TM.rep_add (TM.rep_mul hd ord rF (TM.rep_add (TM.rep_sub
          (TM.rep_mul hd ord rL11 (TM.rep_scal (cst (-4) 0) rV1))
          (TM.rep_scal (cst 2 0) (TM.rep_mul hd ord rL01 (TM.rep_scal (cst (-4) 0) rV0))))
          (TM.rep_mul hd ord rL00 (TM.rep_scal (cst (-12) 0) rV1))))
        (TM.rep_add (TM.rep_sub (TM.rep_mul hd ord (TM.rep_scal (cst (-12) 0) rV1) rv00)
          (TM.rep_scal (cst 2 0) (TM.rep_mul hd ord (TM.rep_scal (cst (-4) 0) rV0) rv01)))
          (TM.rep_mul hd ord (TM.rep_scal (cst (-4) 0) rV1) rv11)))
      (by simp only [fibBeta1, cst_toReal, sOf_zero, sOf_one]; norm_num; ring)
  have rb2 : TM.Rep d _ (fibBeta2 μ c r (sOf z1 z2)) :=
    trep_of_eq (TM.rep_add (TM.rep_mul hd ord rF (TM.rep_add (TM.rep_sub
          (TM.rep_mul hd ord rL11 (TM.rep_scal (cst 12 0) rV0))
          (TM.rep_scal (cst 2 0) (TM.rep_mul hd ord rL01 (TM.rep_scal (cst 4 0) rV1))))
          (TM.rep_mul hd ord rL00 (TM.rep_scal (cst 4 0) rV0))))
        (TM.rep_add (TM.rep_sub (TM.rep_mul hd ord (TM.rep_scal (cst 4 0) rV0) rv00)
          (TM.rep_scal (cst 2 0) (TM.rep_mul hd ord (TM.rep_scal (cst 4 0) rV1) rv01)))
          (TM.rep_mul hd ord (TM.rep_scal (cst 12 0) rV0) rv11)))
      (by simp only [fibBeta2, cst_toReal, sOf_zero, sOf_one]; norm_num; ring)
  have rW := TM.rep_sub (TM.rep_mul hd ord rG rG)
    (TM.rep_mul hd ord rF (TM.rep_add (TM.rep_mul hd ord rb1 rb1) (TM.rep_mul hd ord rb2 rb2)))
  exact ⟨d, hd, hl, rG, trep_of_eq rW (by ring), trep_of_eq (rpc H0P) (H0P_eval z1 z2 μ c)⟩

/-! ### The goal: `min(G⁺, W⁺)` with the cap penalty -/

/-- `r = √D(z)` (the leaf's own `r`-coordinate is not used by the goal). -/
noncomputable def rOf (z1 z2 : ℝ) : ℝ := Real.sqrt (secondCollisionDistanceSq (sOf z1 z2))

/-- `16 · max(0, -h₀)`; zero on the cap `h₀ ≥ 0`. -/
noncomputable def capPen (μ z1 z2 : ℝ) : ℝ := 16 * max 0 (-(3 - 2 * μ - 10 * zNormSq (sOf z1 z2)))

/-- Hypotheses and goals of the leaf: explicit polynomials (centred form), or the gate goal. -/
inductive GQ
  | poly (q : NP.DPoly Dy)
  | gate

noncomputable def gateVal (μ c z1 z2 : ℝ) : ℝ :=
  min (fibG μ c (rOf z1 z2) (sOf z1 z2) + capPen μ z1 z2)
    (fibG μ c (rOf z1 z2) (sOf z1 z2) ^ 2 - fibF μ c (rOf z1 z2) (sOf z1 z2) *
        (fibBeta1 μ c (rOf z1 z2) (sOf z1 z2) ^ 2 + fibBeta2 μ c (rOf z1 z2) (sOf z1 z2) ^ 2)
      + capPen μ z1 z2)

/-- Real meaning at `[z₁, z₂, μ, c, r]`. -/
noncomputable def GQ.eval : GQ → List ℝ → ℝ
  | .poly q, x => q.eval x
  | .gate, [z1, z2, μ, c, _] => gateVal μ c z1 z2
  | _, _ => 0

/-- Penalty weights tried by the lower bound (each `≤ 16`). -/
def kset : List Dy := [⟨1, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨8, 0⟩, ⟨16, 0⟩]

/-- Enclosure of `X + 16 max(0, -h)`: lower bound `max(lo X, maxₖ lo(X - k h))`. -/
noncomputable def penEnc (A h : T) : Iv Dy :=
  (kset.foldl (fun acc k => amax acc (TM.range (TM.sub A (TM.scal k h))).1) (TM.range A).1,
   CNum.add (TM.range A).2 (CNum.mul (⟨16, 0⟩ : Dy) (amax CNum.zero (CNum.neg (TM.range h).1))))

noncomputable def DQ4 : NP.DPoly Dy := ⟨4, NP.ofFlat 4 DP⟩

/-- `J` brackets `√D` on the box `B` (from the centred form of `D`). -/
noncomputable def rbChk (B : List (Iv Dy)) (J : Iv Dy) : Bool :=
  match NP.centredEnc DQ4 B with
  | some R => blt CNum.zero J.1 && ble CNum.zero J.2 && ble (CNum.mul J.1 J.1) R.1 && ble R.2 (CNum.mul J.2 J.2)
  | none => false

noncomputable def GQ.enc : GQ → List (Iv Dy) → Option (Iv Dy)
  | .poly q, B => NP.centredEnc q B
  | .gate, [I0, I1, I2, I3, J] =>
      if rbChk [I0, I1, I2, I3] J && invOK J (invGuess J invBits) then
        let g := gateT I0 I1 I2 I3 (invGuess J invBits)
        let EG := penEnc g.1 g.2.2
        let EW := penEnc g.2.1 g.2.2
        some (amin EG.1 EW.1, amin EG.2 EW.2)
      else none
  | _, _ => none

theorem foldl_amax_le {v : ℝ} (f : Dy → Dy) :
    ∀ (l : List Dy) (acc : Dy), toReal acc ≤ v → (∀ k ∈ l, toReal (f k) ≤ v) →
      toReal (l.foldl (fun a k => amax a (f k)) acc) ≤ v
  | [], _, h, _ => h
  | k :: l, acc, h, hl => by
    simp only [List.foldl_cons]
    refine foldl_amax_le f l _ ?_ (fun k' hk' => hl k' (by simp [hk']))
    rw [toReal_amax]; exact max_le h (hl k (by simp))

/-- Real core of `mem_penEnc`: `X - k h ≤ X + 16 max(0, -h)` for `0 ≤ k ≤ 16`. -/
theorem pen_ge {x y κ : ℝ} (h0 : 0 ≤ κ) (h16 : κ ≤ 16) : x - κ * y ≤ x + 16 * max 0 (-y) := by
  rcases le_or_gt 0 y with hy | hy
  · nlinarith [le_max_left 0 (-y)]
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ -y)]; nlinarith

theorem mem_penEnc {d : List ℝ} (hd : AF.Noise d) (hl : d.length = 3) {A h : T} {x y : ℝ}
    (hA : TM.Rep d A x) (hh : TM.Rep d h y) : Mem (x + 16 * max 0 (-y)) (penEnc A h) := by
  have key : ∀ k ∈ kset, toReal ((TM.range (TM.sub A (TM.scal k h))).1) ≤ x + 16 * max 0 (-y) := by
    intro k hk
    have hk' : 0 ≤ toReal k ∧ toReal k ≤ 16 := by
      simp only [kset, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> norm_num [Dy.cnum_toReal_mk]
    have mk := (TM.mem_range hd hl (TM.rep_sub hA (TM.rep_scal k hh))).1
    generalize toReal ((TM.range (TM.sub A (TM.scal k h))).1) = L at mk ⊢
    exact mk.trans (pen_ge hk'.1 hk'.2)
  have mA := TM.mem_range hd hl hA
  have mh := (TM.mem_range hd hl hh).1
  unfold Mem at mA
  show toReal (kset.foldl (fun acc k => amax acc (TM.range (TM.sub A (TM.scal k h))).1) (TM.range A).1)
      ≤ x + 16 * max 0 (-y) ∧
    x + 16 * max 0 (-y) ≤ toReal (CNum.add (TM.range A).2
      (CNum.mul (⟨16, 0⟩ : Dy) (amax CNum.zero (CNum.neg (TM.range h).1))))
  have hm16 : toReal (⟨16, 0⟩ : Dy) = 16 := by rw [Dy.cnum_toReal_mk]; norm_num
  constructor
  · refine foldl_amax_le (fun k => (TM.range (TM.sub A (TM.scal k h))).1) kset _ ?_ key
    have := le_max_left 0 (-y)
    generalize toReal (TM.range A).1 = a1 at mA ⊢
    linarith [mA.1]
  · rw [toReal_add, toReal_mul, toReal_amax, toReal_zero, toReal_neg, hm16]
    generalize toReal (TM.range h).1 = h1 at mh ⊢
    generalize toReal (TM.range A).2 = a2 at mA ⊢
    have : max 0 (-y) ≤ max 0 (-h1) := max_le_max le_rfl (by linarith)
    linarith [mA.2]

theorem rOf_mem {z1 z2 μ c : ℝ} {I0 I1 I2 I3 J : Iv Dy}
    (hx : InBox [z1, z2, μ, c] [I0, I1, I2, I3]) (h : rbChk [I0, I1, I2, I3] J = true) :
    0 < rOf z1 z2 ∧ rOf z1 z2 ^ 2 = secondCollisionDistanceSq (sOf z1 z2) ∧ Mem (rOf z1 z2) J := by
  unfold rbChk at h
  split at h
  · rename_i R hR
    simp only [Bool.and_eq_true, blt_iff, ble_iff, toReal_zero, toReal_mul] at h
    obtain ⟨⟨⟨ha, hb⟩, hlo⟩, hhi⟩ := h
    have hm := NP.centredEnc_sound DQ4 _ _ R hx hR
    have hD : NP.DPoly.eval DQ4 [z1, z2, μ, c] = secondCollisionDistanceSq (sOf z1 z2) :=
      DP_eval z1 z2 μ c
    rw [hD] at hm
    unfold Mem at hm
    set D := secondCollisionDistanceSq (sOf z1 z2)
    have hDpos : 0 < D := by nlinarith [hm.1]
    refine ⟨Real.sqrt_pos.2 hDpos, Real.sq_sqrt hDpos.le, ?_, ?_⟩
    · calc toReal J.1 = Real.sqrt (toReal J.1 ^ 2) := (Real.sqrt_sq ha.le).symm
        _ ≤ Real.sqrt D := Real.sqrt_le_sqrt (by nlinarith [hm.1])
    · calc Real.sqrt D ≤ Real.sqrt (toReal J.2 ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hm.2])
        _ = toReal J.2 := Real.sqrt_sq hb
  · simp at h

theorem GQ.enc_sound : EnclSound GQ.eval GQ.enc := by
  intro p x B I hx h
  cases p with
  | poly q => exact NP.centredEnc_sound q x B I hx h
  | gate =>
    match B, x, hx with
    | [I0, I1, I2, I3, J], [z1, z2, μ, c, r], .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons _ .nil)))) =>
      simp only [GQ.enc] at h
      split at h
      · rename_i hok
        simp only [Bool.and_eq_true] at hok
        obtain ⟨hrb, hinv⟩ := hok
        obtain ⟨hr0, hr2, hrJ⟩ := rOf_mem (.cons h0 (.cons h1 (.cons h2 (.cons h3 .nil)))) hrb
        obtain ⟨-, hK⟩ := inv_mem hrJ hinv
        obtain ⟨d, hd, hl, hG, hW, hh⟩ := gateT_rep h0 h1 h2 h3 hr0 hr2 hK
        have mG := mem_penEnc hd hl hG hh
        have mW := mem_penEnc hd hl hW hh
        simp only [Option.some.injEq] at h
        subst h
        unfold Mem at mG mW ⊢
        simp only [GQ.eval, gateVal, capPen, toReal_amin]
        constructor
        · exact min_le_min mG.1 mW.1
        · exact min_le_min mG.2 mW.2
      · simp at h

end GateTM


namespace GateAsm

open Gate GateTM

/-- The cap `h₀ = 3 - 2μ - 10(z₁² + z₂²)` in the variables `[z₁, z₂, μ, c, r]`. -/
def H0P5 : Poly Dy := [((⟨-10, 0⟩ : Dy), [2, 0, 0, 0, 0]), ((⟨-10, 0⟩ : Dy), [0, 2, 0, 0, 0]),
  ((⟨-2, 0⟩ : Dy), [0, 0, 1, 0, 0]), ((⟨3, 0⟩ : Dy), [0, 0, 0, 0, 0])]

/-- Root box: `z₁, z₂ ∈ [0, 9/16]`, `μ ∈ [0, 1/2]`, `c` in a dyadic outer bound of `[2.1, 2.1 + 10⁻⁶]`. -/
noncomputable def rootBox : List (Iv Dy) :=
  [((⟨0, 0⟩ : Dy), (⟨9, 4⟩ : Dy)), ((⟨0, 0⟩ : Dy), (⟨9, 4⟩ : Dy)), ((⟨0, 0⟩ : Dy), (⟨1, 1⟩ : Dy)),
   ((⟨2308974418329, 40⟩ : Dy), (⟨1154487758921, 39⟩ : Dy))]

/-- The certificate: box, `r² = D`, hypothesis `h₀ ≥ 0`, goal `min(G⁺, W⁺) > 0`, tree `t`. -/
noncomputable def gateCert (t : Tree Dy) : Cert Dy GQ :=
  ⟨rootBox, .poly DQ4, [.poly ⟨5, NP.ofFlat 5 H0P5⟩], [.gate], t⟩

/-! ### The gate data depend on `z = (s 0, s 1)` only -/

section dep

variable (μ c r : ℝ) (s : Phase)

theorem dZ_sOf : dZ s = dZ (sOf (s 0) (s 1)) := by
  funext i; fin_cases i <;> simp [dZ, sOf]
theorem dD_sOf : dD s = dD (sOf (s 0) (s 1)) := by
  funext i; fin_cases i <;> simp [dD, sOf]
theorem hD_sOf : hD s = hD (sOf (s 0) (s 1)) := by
  funext i j; fin_cases i <;> fin_cases j <;> simp [hD, sOf]
theorem zNormSq_sOf' : zNormSq s = zNormSq (sOf (s 0) (s 1)) := by simp [zNormSq, sOf]
theorem D_sOf : secondCollisionDistanceSq s = secondCollisionDistanceSq (sOf (s 0) (s 1)) := by
  simp [secondCollisionDistanceSq, sOf]

theorem kBr_sOf (i j : Fin 4) : kBr μ r s i j = kBr μ r (sOf (s 0) (s 1)) i j := by
  unfold kBr; rw [dZ_sOf, dD_sOf, hD_sOf, zNormSq_sOf']

theorem fibF_sOf : fibF μ c r s = fibF μ c r (sOf (s 0) (s 1)) := by
  unfold fibF; rw [zNormSq_sOf']; simp [sOf]
theorem fibL00_sOf : fibL00 μ c r s = fibL00 μ c r (sOf (s 0) (s 1)) := by
  unfold fibL00; rw [kBr_sOf]; simp [sOf]
theorem fibL01_sOf : fibL01 μ r s = fibL01 μ r (sOf (s 0) (s 1)) := by
  unfold fibL01; rw [kBr_sOf]; simp [sOf]
theorem fibL11_sOf : fibL11 μ c r s = fibL11 μ c r (sOf (s 0) (s 1)) := by
  unfold fibL11; rw [kBr_sOf]; simp [sOf]
theorem fibV0_sOf : fibV0 μ c r s = fibV0 μ c r (sOf (s 0) (s 1)) := by
  unfold fibV0; rw [dZ_sOf, dD_sOf, zNormSq_sOf']; simp [sOf]
theorem fibV1_sOf : fibV1 μ c r s = fibV1 μ c r (sOf (s 0) (s 1)) := by
  unfold fibV1; rw [dZ_sOf, dD_sOf, zNormSq_sOf']; simp [sOf]

theorem fibG_sOf : fibG μ c r s = fibG μ c r (sOf (s 0) (s 1)) := by
  unfold fibG
  rw [fibF_sOf, fibL00_sOf, fibL01_sOf, fibL11_sOf, fibV0_sOf, fibV1_sOf, zNormSq_sOf']
theorem fibBeta1_sOf : fibBeta1 μ c r s = fibBeta1 μ c r (sOf (s 0) (s 1)) := by
  unfold fibBeta1
  rw [fibF_sOf, fibL00_sOf, fibL01_sOf, fibL11_sOf, fibV0_sOf, fibV1_sOf]; simp [sOf]
theorem fibBeta2_sOf : fibBeta2 μ c r s = fibBeta2 μ c r (sOf (s 0) (s 1)) := by
  unfold fibBeta2
  rw [fibF_sOf, fibL00_sOf, fibL01_sOf, fibL11_sOf, fibV0_sOf, fibV1_sOf]; simp [sOf]

end dep

/-! ### Reflection to `z₁, z₂ ≥ 0` -/

section abs

variable (μ c r : ℝ)

/-- `G`, `F` and `β₁² + β₂²` at `(z₁, z₂)` equal their values at `(|z₁|, |z₂|)`. -/
theorem gate_abs (z1 z2 : ℝ) :
    fibG μ c r (sOf z1 z2) = fibG μ c r (sOf |z1| |z2|) ∧
      fibF μ c r (sOf z1 z2) = fibF μ c r (sOf |z1| |z2|) ∧
      fibBeta1 μ c r (sOf z1 z2) ^ 2 + fibBeta2 μ c r (sOf z1 z2) ^ 2
        = fibBeta1 μ c r (sOf |z1| |z2|) ^ 2 + fibBeta2 μ c r (sOf |z1| |z2|) ^ 2 := by
  have step1 : fibG μ c r (sOf z1 z2) = fibG μ c r (sOf |z1| z2) ∧
      fibF μ c r (sOf z1 z2) = fibF μ c r (sOf |z1| z2) ∧
      fibBeta1 μ c r (sOf z1 z2) ^ 2 + fibBeta2 μ c r (sOf z1 z2) ^ 2
        = fibBeta1 μ c r (sOf |z1| z2) ^ 2 + fibBeta2 μ c r (sOf |z1| z2) ^ 2 := by
    rcases abs_choice z1 with h | h
    · rw [h]; exact ⟨rfl, rfl, rfl⟩
    · have e : z1 = -|z1| := by rw [h]; ring
      rw [e, abs_neg, abs_abs]
      obtain ⟨hG, hB⟩ := gate_neg1 μ c r |z1| z2
      exact ⟨hG, fibF_neg1 μ c r |z1| z2, hB⟩
  have step2 : fibG μ c r (sOf |z1| z2) = fibG μ c r (sOf |z1| |z2|) ∧
      fibF μ c r (sOf |z1| z2) = fibF μ c r (sOf |z1| |z2|) ∧
      fibBeta1 μ c r (sOf |z1| z2) ^ 2 + fibBeta2 μ c r (sOf |z1| z2) ^ 2
        = fibBeta1 μ c r (sOf |z1| |z2|) ^ 2 + fibBeta2 μ c r (sOf |z1| |z2|) ^ 2 := by
    rcases abs_choice z2 with h | h
    · rw [h]; exact ⟨rfl, rfl, rfl⟩
    · have e : z2 = -|z2| := by rw [h]; ring
      rw [e, abs_neg, abs_abs]
      obtain ⟨hG, hB⟩ := gate_neg2 μ c r |z1| |z2|
      exact ⟨hG, fibF_neg2 μ c r |z1| |z2|, hB⟩
  exact ⟨step1.1.trans step2.1, step1.2.1.trans step2.2.1, step1.2.2.trans step2.2.2⟩

end abs

/-! ### From the certificate to the gate inequality -/

theorem fiber_gate_pos_of_check {t : Tree Dy} (hC : check GQ.enc (gateCert t) = true)
    (μ c r : ℝ) (s : Phase)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq s)
    (hz : 2 * zNormSq s ≤ (3 - 2 * μ) / 5) :
    0 < fibG μ c r s ∧
      fibF μ c r s * (fibBeta1 μ c r s ^ 2 + fibBeta2 μ c r s ^ 2) < fibG μ c r s ^ 2 := by
  set a := |s 0| with ha_def
  set b := |s 1| with hb_def
  have ha0 : 0 ≤ a := abs_nonneg _
  have hb0 : 0 ≤ b := abs_nonneg _
  have hZ : zNormSq s = a ^ 2 + b ^ 2 := by simp [zNormSq, ha_def, hb_def, sq_abs]
  have hD : secondCollisionDistanceSq s = secondCollisionDistanceSq (sOf a b) := by
    simp only [secondCollisionDistanceSq, sOf, ha_def, hb_def]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : |s 0| ^ 2 = s 0 ^ 2 := sq_abs _
    have h1 : |s 1| ^ 2 = s 1 ^ 2 := sq_abs _
    have h2 : (4 * |s 0| * |s 1|) ^ 2 = (4 * s 0 * s 1) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs, sq_abs, mul_pow, mul_pow]
    rw [h0, h1, h2]
  -- the certificate at x = [a, b, μ, c]
  have hx : InBox [a, b, μ, c] rootBox := by
    have ha1 : a ≤ 9 / 16 := by nlinarith [sq_nonneg b]
    have hb1 : b ≤ 9 / 16 := by nlinarith [sq_nonneg a]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))) <;>
      simp only [Mem, Dy.cnum_toReal_mk] <;> norm_num <;> constructor <;> linarith
  have hr2' : r ^ 2 = GQ.eval (gateCert t).rSq [a, b, μ, c] := by
    show r ^ 2 = NP.DPoly.eval DQ4 [a, b, μ, c]
    rw [show NP.DPoly.eval DQ4 [a, b, μ, c] = secondCollisionDistanceSq (sOf a b) from DP_eval a b μ c,
      ← hD, hr2]
  have hh0 : 0 ≤ 3 - 2 * μ - 10 * (a ^ 2 + b ^ 2) := by rw [← hZ]; linarith
  have hhyp : ∀ p ∈ (gateCert t).hyps, 0 ≤ GQ.eval p ([a, b, μ, c] ++ [r]) := by
    intro p hp
    simp only [gateCert, List.mem_singleton] at hp
    subst hp
    show 0 ≤ NP.eval 5 (NP.ofFlat 5 H0P5) [a, b, μ, c, r]
    rw [NP.eval_ofFlat 5 H0P5 _ rfl]
    simp only [evalR, monoR, H0P5, Dy.cnum_toReal_mk]
    norm_num
    linarith
  have hg := check_sound GQ.enc_sound (gateCert t) hC [a, b, μ, c] hx r hr hr2' hhyp .gate
    (by simp [gateCert])
  -- read the goal: r = √D and the penalty vanishes
  have hrOf : rOf a b = r := by
    unfold rOf
    rw [← hD, ← hr2, Real.sqrt_sq hr.le]
  have hpen : capPen μ a b = 0 := by
    unfold capPen
    rw [zNormSq_sOf]
    simp only [max_eq_left (by linarith : -(3 - 2 * μ - 10 * (a ^ 2 + b ^ 2)) ≤ 0), mul_zero]
  simp only [List.cons_append, List.nil_append, GQ.eval, gateVal, hrOf, hpen, add_zero,
    lt_min_iff] at hg
  obtain ⟨hG, hW⟩ := hg
  -- back to s
  obtain ⟨eG, eF, eB⟩ := gate_abs μ c r (s 0) (s 1)
  rw [fibG_sOf, fibF_sOf, fibBeta1_sOf, fibBeta2_sOf, eG, eF, eB]
  exact ⟨hG, by linarith⟩

end GateAsm


end BirkhoffGlobalSection.TangentialHessian.Checker


