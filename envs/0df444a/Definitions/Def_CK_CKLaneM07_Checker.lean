-- Prove2me | Definitions.Def_CK_CKLaneM07_Checker
-- name    : CK_CKLaneM07_Checker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T13:00:01.906989+00:00
-- url     : https://prove2.me/theorems/0c063639-8fb3-4d8b-bf2a-1dff308b455e
-- title:
--   Courtade–Kumar proof module `CKLaneM07.Checker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.Checker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.Checker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.Checker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/Checker.lean)

import Definitions.Def_CK_CKLaneM07_Analytic
import Definitions.Def_CK_CKLaneM07_KappaLogSum

-- ===== source module CKLaneM07.Checker =====
section

/-!
# Lane M07: reflective Boolean checker for the archived same-side `derivative` method

A leaf is an exact archived same-side box `B = (x1,x2,b1,b2,t1,t2)` in the coordinates
`x = log₂(b/a)`, `b`, `t = E / ((H a + H b)/2)` (root `[0,32] × [1/32,1/2] × [0,1]`, path digits
`axis = d / 2`, `side = d % 2`, exact halving).  The witness `w` only proposes rationals
(`r1 ≤ 2^-x2`, `2^-x1 ≤ r2`, a point `zr ≥ ρ_hi` and a curvature anchor `v`); `check B w`
recomputes every enclosure in exact `ℚ`:

* the image of the box: `r1 ≤ a/b ≤ r2` (exact `Nat` powers), `a, m, d` ranges;
* `H` enclosures at `aLo, aHi, b1, b2, mHi` (`CKLaneE.FP`, fixed point `2^-48`);
* `K ≥ Δ/d²` from the exact identity `Δ/d² = C(ρ)/ρ²/(4m) + C(κ)/κ²/(4(1-m))`, monotonicity of
  `C(z)/z²` (evaluated at `zr`) and the polynomial bound (at `ρ_hi`, `κ_hi`);
* `I_hi ≥ H(m) - E` from `E ≥ t1 C` and from `Δ + s ≤ K d_hi² + (1-t1) C_hi`;
* `P''(y) ≤ P2up v` for all `y ≤ I_hi` (closed form of `etaCurvature (H v)`, monotone transfer);
* `kap_lo`: interval lower bound of the archive factor `min(kap(a),kap(b))` (used only if `> 1`);
* final inequality `K · P2up v ≤ kap / (2 b2 (1 - aLo))` (archive: `beta_lo ≥ K P''(I_hi)`).

`check_sound`: `check B w = true` ⇒ every finite interior law with `a ≤ b` in the exact box and
`phi ≤ psi` at the parent satisfies `μ.gap ≤ μ.cost`.  No real-variable enclosure, stored margin or
entropy-split parametrization is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM07

open GeneralCK GeneralCK.Scalar CKLaneE.FP

/-! ## Archived same-side leaf boxes and the semantic statement -/

structure SBox where
  x1 : ℚ
  x2 : ℚ
  b1 : ℚ
  b2 : ℚ
  t1 : ℚ
  t2 : ℚ
  deriving Repr, DecidableEq

/-- Root of the archived same-side cover (`ADAPT_RESULT.json`). -/
def ssRoot : SBox := ⟨0, 32, 1 / 32, 1 / 2, 0, 1⟩

/-- One exact halving step (`COVER.reconstruct`: `axis, side = divmod(d, 2)`). -/
def ssStep (B : SBox) (d : ℕ) : SBox :=
  match d with
  | 0 => { B with x2 := (B.x1 + B.x2) / 2 }
  | 1 => { B with x1 := (B.x1 + B.x2) / 2 }
  | 2 => { B with b2 := (B.b1 + B.b2) / 2 }
  | 3 => { B with b1 := (B.b1 + B.b2) / 2 }
  | 4 => { B with t2 := (B.t1 + B.t2) / 2 }
  | 5 => { B with t1 := (B.t1 + B.t2) / 2 }
  | _ => B

/-- The exact leaf box of an archived path. -/
def ssBox (p : List ℕ) : SBox := p.foldl ssStep ssRoot

/-- Law-level membership in the exact leaf box: `x = log₂(b/a) ∈ [x1,x2]`, `b ∈ [b1,b2]`,
`t = E/((H a + H b)/2) ∈ [t1,t2]`. -/
def InSBox (B : SBox) (a b E : ℝ) : Prop :=
  (2 : ℝ) ^ (-(B.x2 : ℝ)) ≤ a / b ∧ a / b ≤ (2 : ℝ) ^ (-(B.x1 : ℝ)) ∧
    (B.b1 : ℝ) ≤ b ∧ b ≤ (B.b2 : ℝ) ∧
    (B.t1 : ℝ) * ((H a + H b) / 2) ≤ E ∧ E ≤ (B.t2 : ℝ) * ((H a + H b) / 2)

/-- Semantic owner statement for a leaf (active-psi branch). -/
def SemSBox (B : SBox) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → InSBox B μ.a μ.b μ.meanEntropy →
    phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy → μ.gap ≤ μ.cost

/-! ## Exact comparisons of `2^-u` with rationals (pattern of `CKLaneD.pow2LowerOK`) -/

/-- `r ≤ 2^-u`, certified by `num(r)^den(u) * 2^num(u) ≤ den(r)^den(u)`. -/
def pow2LowerOK (r u : ℚ) : Bool :=
  decide (0 < r) && decide (0 ≤ u) &&
    Nat.ble (r.num.toNat ^ u.den * 2 ^ u.num.toNat) (r.den ^ u.den)

/-- `2^-u ≤ r`, certified by `den(r)^den(u) ≤ num(r)^den(u) * 2^num(u)`. -/
def pow2UpperOK (r u : ℚ) : Bool :=
  decide (0 < r) && decide (0 ≤ u) &&
    Nat.ble (r.den ^ u.den) (r.num.toNat ^ u.den * 2 ^ u.num.toNat)

theorem rpow_neg_pow_den (u : ℚ) (hu : 0 ≤ u) :
    ((2 : ℝ) ^ (-(u : ℝ))) ^ u.den = ((2 : ℝ) ^ u.num.toNat)⁻¹ := by
  have hnum : (0 : ℤ) ≤ u.num := Rat.num_nonneg.mpr hu
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hu' : (u : ℝ) = (u.num : ℝ) / (u.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have htn : ((u.num.toNat : ℕ) : ℝ) = (u.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hden : (u.den : ℝ) ≠ 0 := by exact_mod_cast u.den_nz
  rw [hu', show -((u.num : ℝ) / (u.den : ℝ)) * (u.den : ℝ) = -(u.num : ℝ) by field_simp,
    Real.rpow_neg (by norm_num), ← htn, Real.rpow_natCast]

theorem rat_cast_eq_num_div_den (r : ℚ) (hr : 0 < r) :
    (r : ℝ) = (r.num.toNat : ℝ) / (r.den : ℝ) := by
  have hnum : (0 : ℤ) < r.num := Rat.num_pos.mpr hr
  have htn : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  rw [htn, ← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]

theorem pow2LowerOK_sound {r u : ℚ} (h : pow2LowerOK r u = true) :
    (r : ℝ) ≤ (2 : ℝ) ^ (-(u : ℝ)) := by
  unfold pow2LowerOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq] at h
  obtain ⟨⟨hr, hu⟩, hle⟩ := h
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(u : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hM : u.den ≠ 0 := u.den_nz
  rw [← pow_le_pow_iff_left₀ hr'.le hpos.le hM, rpow_neg_pow_den u hu,
    rat_cast_eq_num_div_den r hr, div_pow]
  have hD : (0 : ℝ) < (r.den : ℝ) ^ u.den := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ u.num.toNat := by positivity
  rw [div_le_iff₀ hD, inv_mul_eq_div, le_div_iff₀ h2]
  exact_mod_cast hle

theorem pow2UpperOK_sound {r u : ℚ} (h : pow2UpperOK r u = true) :
    (2 : ℝ) ^ (-(u : ℝ)) ≤ (r : ℝ) := by
  unfold pow2UpperOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.ble_eq] at h
  obtain ⟨⟨hr, hu⟩, hle⟩ := h
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(u : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hM : u.den ≠ 0 := u.den_nz
  rw [← pow_le_pow_iff_left₀ hpos.le hr'.le hM, rpow_neg_pow_den u hu,
    rat_cast_eq_num_div_den r hr, div_pow]
  have hD : (0 : ℝ) < (r.den : ℝ) ^ u.den := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ u.num.toNat := by positivity
  rw [le_div_iff₀ hD, inv_mul_eq_div, div_le_iff₀ h2]
  exact_mod_cast hle

/-! ## Witness and the Boolean checker -/

structure Wit where
  r1 : ℚ
  r2 : ℚ
  zr : ℚ
  v : ℚ
  deriving Repr, DecidableEq

/-- Compact dyadic literal `n / 2^e` used to encode witness data. -/
def dy (n : ℤ) (e : ℕ) : ℚ := (n : ℚ) / ((2 ^ e : ℕ) : ℚ)

def aLo (B : SBox) (w : Wit) : ℚ := w.r1 * B.b1
def aHi (B : SBox) (w : Wit) : ℚ := w.r2 * B.b2
def mLo (B : SBox) (w : Wit) : ℚ := B.b1 * (1 + w.r1) / 2
def mHi (B : SBox) (w : Wit) : ℚ := B.b2 * (1 + w.r2) / 2
def dHi (B : SBox) (w : Wit) : ℚ := B.b2 * (1 - w.r1)
def CLo (B : SBox) (w : Wit) : ℚ := (Hlo (aLo B w) + Hlo B.b1) / 2
def CHi (B : SBox) (w : Wit) : ℚ := (Hhi (aHi B w) + Hhi B.b2) / 2
def rhoHi (w : Wit) : ℚ := (1 - w.r1) / (1 + w.r1)
def kapHi (B : SBox) (w : Wit) : ℚ := dHi B w / (2 * (1 - mHi B w))
def crPoly (z : ℚ) : ℚ := (1 + z * z / 6 + 2 / 5 * (z * z) * (z * z)) / (2 * LqLo)
def crLog (z : ℚ) : ℚ := (1 - Hlo ((1 - z) / 2)) / (z * z)
def cr1 (w : Wit) : ℚ :=
  if 0 < w.zr then min (crLog w.zr) (crPoly (rhoHi w)) else crPoly (rhoHi w)
def cr2 (B : SBox) (w : Wit) : ℚ := crPoly (kapHi B w)
def Kq (B : SBox) (w : Wit) : ℚ := cr1 w / (4 * mLo B w) + cr2 B w / (4 * (1 - mHi B w))
def I1 (B : SBox) (w : Wit) : ℚ := Hhi (mHi B w) - B.t1 * CLo B w
def I2 (B : SBox) (w : Wit) : ℚ := CHi B w * (1 - B.t1) + Kq B w * (dHi B w * dHi B w)
def IHi (B : SBox) (w : Wit) : ℚ := min (I1 B w) (I2 B w)
def P2up (v : ℚ) : ℚ :=
  LqHi * ((v * v + (1 - v) * (1 - v)) * lamHi v - (1 - 2 * v)) /
    (v * v * ((1 - v) * (1 - v)) * (lamLo v * lamLo v * lamLo v))
def kA1 (B : SBox) (w : Wit) : ℚ := aLo B w / ((1 - aLo B w) * (-l1Lo (aHi B w)))
def kA2 (B : SBox) (w : Wit) : ℚ := (1 - aHi B w) / (aHi B w * (-lLo (aLo B w)))
def kB1 (B : SBox) : ℚ := B.b1 / ((1 - B.b1) * (-l1Lo B.b2))
def kB2 (B : SBox) : ℚ := (1 - B.b2) / (B.b2 * (-lLo B.b1))
def kapInt (B : SBox) (w : Wit) : ℚ := min (min (kA1 B w) (kA2 B w)) (min (kB1 B) (kB2 B))
def kapEff (B : SBox) (w : Wit) : ℚ := if 1 < kapInt B w then min (kapInt B w) 2 else 1
def betaLo (B : SBox) (w : Wit) : ℚ := kapEff B w / (2 * B.b2 * (1 - aLo B w))

def boxOk (B : SBox) (w : Wit) : Bool :=
  decide (0 ≤ B.x1 ∧ B.x1 ≤ B.x2 ∧ 0 < B.b1 ∧ B.b1 ≤ B.b2 ∧ B.b2 ≤ 1 / 2 ∧ 0 ≤ B.t1 ∧ B.t1 ≤ 1 ∧
    0 < w.r1 ∧ w.r1 ≤ w.r2 ∧ w.r2 ≤ 1)
def pow2Ok (B : SBox) (w : Wit) : Bool := pow2LowerOK w.r1 B.x2 && pow2UpperOK w.r2 B.x1
def ptsOk (B : SBox) (w : Wit) : Bool :=
  ptOk (aLo B w) && ptOk (aHi B w) && ptOk B.b1 && ptOk B.b2 && ptOk (mHi B w)
def zrOk (w : Wit) : Bool :=
  if 0 < w.zr then decide (rhoHi w ≤ w.zr ∧ w.zr < 1) && ptOk ((1 - w.zr) / 2) else true
def anchorOk (B : SBox) (w : Wit) : Bool :=
  ptOk w.v && decide (w.v < 1 / 2 ∧ 0 < lamLo w.v ∧ Hhi w.v ≤ 1 - IHi B w)
def finalOk (B : SBox) (w : Wit) : Bool :=
  decide (IHi B w < 1 ∧ 0 ≤ Kq B w ∧ Kq B w * P2up w.v ≤ betaLo B w)

/-- The reflective checker. -/
def check (B : SBox) (w : Wit) : Bool :=
  boxOk B w && pow2Ok B w && ptsOk B w && zrOk w && anchorOk B w && finalOk B w

/-- Per-leaf acceptance bound to the archived path. -/
def checkLeaf (p : List ℕ) (w : Wit) : Bool := check (ssBox p) w

/-! ## Real-variable lemmas used by the soundness proof -/

theorem cast_crPoly (z : ℚ) : ((crPoly z : ℚ) : ℝ) =
    (1 + (z : ℝ) ^ 2 / 6 + 2 / 5 * (z : ℝ) ^ 4) / (2 * ((LqLo : ℚ) : ℝ)) := by
  simp only [crPoly]; push_cast; ring

theorem crR_le_crPoly {z : ℝ} {zh : ℚ} (hz : 0 < z) (hzz : z ≤ zh) (hz1 : z < 1) :
    crR z ≤ ((crPoly zh : ℚ) : ℝ) := by
  rw [cast_crPoly]
  obtain ⟨hL1, _⟩ := log_two_mem
  exact crR_le_poly hz hzz hz1 LqLo_pos hL1

theorem crR_le_crLog {z : ℝ} {zr : ℚ} (hz : 0 < z) (hzz : z ≤ zr) (hzr1 : (zr : ℝ) < 1)
    (hpt : ptOk ((1 - zr) / 2) = true) : crR z ≤ ((crLog zr : ℚ) : ℝ) := by
  have hm := crR_mono hz hzz hzr1
  have hzr0 : (0 : ℝ) < zr := lt_of_lt_of_le hz hzz
  obtain ⟨hHlo, _⟩ := H_bounds hpt
  have hcast : (((1 - zr) / 2 : ℚ) : ℝ) = (1 - (zr : ℝ)) / 2 := by push_cast; ring
  rw [hcast] at hHlo
  have e : ((crLog zr : ℚ) : ℝ) = (1 - ((Hlo ((1 - zr) / 2) : ℚ) : ℝ)) / ((zr : ℝ) ^ 2) := by
    simp only [crLog]; push_cast; ring
  rw [e]
  refine hm.trans ?_
  unfold crR
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

theorem cr1_bound {w : Wit} (hzr : zrOk w = true) {z : ℝ} (hz : 0 < z) (hzz : z ≤ rhoHi w)
    (hz1 : z < 1) : crR z ≤ ((cr1 w : ℚ) : ℝ) := by
  unfold cr1
  unfold zrOk at hzr
  split_ifs with h
  · simp only [h, if_true, Bool.and_eq_true, decide_eq_true_eq] at hzr
    obtain ⟨⟨hle, hlt⟩, hpt⟩ := hzr
    have hle' : ((rhoHi w : ℚ) : ℝ) ≤ (w.zr : ℝ) := by exact_mod_cast hle
    have hlt' : (w.zr : ℝ) < 1 := by exact_mod_cast hlt
    have h1 := crR_le_crLog hz (hzz.trans hle') hlt' hpt
    have h2 := crR_le_crPoly hz hzz hz1
    rw [Rat.cast_min]
    exact le_min h1 h2
  · exact crR_le_crPoly hz hzz hz1

/-- Kappa conditions, low-side form: `κ (-log(1-z)) ≤ z/(1-z)` on `[zlo, zhi]`. -/
theorem kapA {κ z zlo zhi ℓ : ℝ} (hκ : 0 ≤ κ) (hzlo : 0 < zlo) (hz1 : zlo ≤ z) (hz2 : z ≤ zhi)
    (hzhi : zhi < 1) (hℓ : ℓ ≤ Real.log (1 - zhi)) (hk : κ ≤ zlo / ((1 - zlo) * (-ℓ))) :
    κ * (-Real.log (1 - z)) ≤ z / (1 - z) := by
  have hlog1 : Real.log (1 - zhi) < 0 := Real.log_neg (by linarith) (by linarith)
  have hℓneg : 0 < -ℓ := by linarith
  have hD : 0 < (1 - zlo) * (-ℓ) := mul_pos (by linarith) hℓneg
  have hk' : κ * ((1 - zlo) * (-ℓ)) ≤ zlo := by rwa [le_div_iff₀ hD] at hk
  have hlz : Real.log (1 - zhi) ≤ Real.log (1 - z) := Real.log_le_log (by linarith) (by linarith)
  have h1 : κ * (-Real.log (1 - z)) ≤ κ * (-ℓ) := mul_le_mul_of_nonneg_left (by linarith) hκ
  have h2 : κ * (-ℓ) ≤ zlo / (1 - zlo) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have h3 : zlo / (1 - zlo) ≤ z / (1 - z) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  linarith

/-- Kappa conditions, high-side form: `κ (-log z) ≤ (1-z)/z` on `[zlo, zhi]`. -/
theorem kapB {κ z zlo zhi ℓ : ℝ} (hκ : 0 ≤ κ) (hzlo : 0 < zlo) (hz1 : zlo ≤ z) (hz2 : z ≤ zhi)
    (hzhi : zhi < 1) (hℓ : ℓ ≤ Real.log zlo) (hk : κ ≤ (1 - zhi) / (zhi * (-ℓ))) :
    κ * (-Real.log z) ≤ (1 - z) / z := by
  have hlog1 : Real.log zlo < 0 := Real.log_neg hzlo (by linarith)
  have hℓneg : 0 < -ℓ := by linarith
  have hzhi0 : 0 < zhi := by linarith
  have hD : 0 < zhi * (-ℓ) := mul_pos hzhi0 hℓneg
  have hk' : κ * (zhi * (-ℓ)) ≤ 1 - zhi := by rwa [le_div_iff₀ hD] at hk
  have hlz : Real.log zlo ≤ Real.log z := Real.log_le_log hzlo hz1
  have h1 : κ * (-Real.log z) ≤ κ * (-ℓ) := mul_le_mul_of_nonneg_left (by linarith) hκ
  have h2 : κ * (-ℓ) ≤ (1 - zhi) / zhi := by
    rw [le_div_iff₀ hzhi0]; nlinarith
  have h3 : (1 - zhi) / zhi ≤ (1 - z) / z := by
    rw [div_le_div_iff₀ hzhi0 (by linarith)]; nlinarith
  linarith

/-- The (kappa-enhanced or plain) log-sum cost floor in the form used by the criterion. -/
theorem floor_of_kap {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) (hab : μ.a < μ.b) {κ : ℝ}
    (hκ : κ = 1 ∨ (0 ≤ κ ∧ κ ≤ 2 ∧
      κ * (-Real.log (1 - μ.a)) ≤ μ.a / (1 - μ.a) ∧ κ * (-Real.log μ.a) ≤ (1 - μ.a) / μ.a ∧
      κ * (-Real.log (1 - μ.b)) ≤ μ.b / (1 - μ.b) ∧ κ * (-Real.log μ.b) ≤ (1 - μ.b) / μ.b)) :
    interiorCost μ.a μ.b + κ * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))) * μ.meanDeficit ≤
      μ.cost := by
  have hV : LogSum.V μ.a μ.b = μ.b * (1 - μ.a) := by
    simp only [LogSum.V, max_eq_right hab.le, min_eq_left hab.le]
  have hsd : (H μ.a - μ.e) + (H μ.b - μ.f) = 2 * μ.meanDeficit := by
    unfold InteriorLaw.meanDeficit; ring
  have hpos : 0 < μ.b * (1 - μ.a) := mul_pos μ.b_interior.1 (by linarith [μ.a_interior.2])
  rcases hκ with h1 | ⟨h0, h2, ha0, ha1, hb0, hb1⟩
  · have hf := μ.psiLogSumCostFloor_le_cost
    unfold InteriorLaw.psiLogSumCostFloor at hf
    rw [hV, hsd] at hf
    rw [h1]
    have e : (μ.a - μ.b) ^ 2 / (4 * (μ.b * (1 - μ.a))) * (2 * μ.meanDeficit) =
        1 * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))) * μ.meanDeficit := by
      field_simp; ring
    linarith
  · have hf := kappa_cost_lower_bound μ h0 h2 ha0 ha1 hb0 hb1
    rw [hV, hsd] at hf
    have e : κ * ((μ.a - μ.b) ^ 2 / (4 * (μ.b * (1 - μ.a)))) * (2 * μ.meanDeficit) =
        κ * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))) * μ.meanDeficit := by
      field_simp; ring
    linarith

/-- From the checked rational data, the effective kappa satisfies the floor hypotheses. -/
theorem kapEff_ok (B : SBox) (w : Wit) {a b : ℝ}
    (hpaL : ptOk (aLo B w) = true) (hpaH : ptOk (aHi B w) = true)
    (hpb1 : ptOk B.b1 = true) (hpb2 : ptOk B.b2 = true)
    (haL : ((aLo B w : ℚ) : ℝ) ≤ a) (haH : a ≤ ((aHi B w : ℚ) : ℝ))
    (hbL : ((B.b1 : ℚ) : ℝ) ≤ b) (hbH : b ≤ ((B.b2 : ℚ) : ℝ)) :
    ((kapEff B w : ℚ) : ℝ) = 1 ∨ (0 ≤ ((kapEff B w : ℚ) : ℝ) ∧ ((kapEff B w : ℚ) : ℝ) ≤ 2 ∧
      ((kapEff B w : ℚ) : ℝ) * (-Real.log (1 - a)) ≤ a / (1 - a) ∧
      ((kapEff B w : ℚ) : ℝ) * (-Real.log a) ≤ (1 - a) / a ∧
      ((kapEff B w : ℚ) : ℝ) * (-Real.log (1 - b)) ≤ b / (1 - b) ∧
      ((kapEff B w : ℚ) : ℝ) * (-Real.log b) ≤ (1 - b) / b) := by
  unfold kapEff
  split_ifs with hk
  · right
    set κq : ℚ := min (kapInt B w) 2 with hκq
    have hκ1 : (1 : ℚ) ≤ κq := le_min hk.le (by norm_num)
    have hκ2 : κq ≤ 2 := min_le_right _ _
    have hκI : κq ≤ kapInt B w := min_le_left _ _
    have hA1 : κq ≤ kA1 B w := hκI.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hA2 : κq ≤ kA2 B w := hκI.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hB1 : κq ≤ kB1 B := hκI.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hB2 : κq ≤ kB2 B := hκI.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hκ0R : (0 : ℝ) ≤ (κq : ℝ) := by exact_mod_cast (show (0 : ℚ) ≤ κq by linarith)
    have hκ2R : (κq : ℝ) ≤ 2 := by exact_mod_cast hκ2
    obtain ⟨hpa1, hpa2⟩ := ptOk_pos hpaL
    obtain ⟨hpA1, hpA2⟩ := ptOk_pos hpaH
    obtain ⟨hpb11, hpb12⟩ := ptOk_pos hpb1
    obtain ⟨hpb21, hpb22⟩ := ptOk_pos hpb2
    obtain ⟨la1, _, _, _⟩ := ptOk_sound hpaL
    obtain ⟨_, _, lA3, _⟩ := ptOk_sound hpaH
    obtain ⟨lb1, _, _, _⟩ := ptOk_sound hpb1
    obtain ⟨_, _, lB3, _⟩ := ptOk_sound hpb2
    have c1 : ((kA1 B w : ℚ) : ℝ) = ((aLo B w : ℚ) : ℝ) /
        ((1 - ((aLo B w : ℚ) : ℝ)) * (-((l1Lo (aHi B w) : ℚ) : ℝ))) := by
      simp only [kA1]; push_cast; ring
    have c2 : ((kA2 B w : ℚ) : ℝ) = (1 - ((aHi B w : ℚ) : ℝ)) /
        (((aHi B w : ℚ) : ℝ) * (-((lLo (aLo B w) : ℚ) : ℝ))) := by
      simp only [kA2]; push_cast; ring
    have c3 : ((kB1 B : ℚ) : ℝ) = ((B.b1 : ℚ) : ℝ) /
        ((1 - ((B.b1 : ℚ) : ℝ)) * (-((l1Lo B.b2 : ℚ) : ℝ))) := by
      simp only [kB1]; push_cast; ring
    have c4 : ((kB2 B : ℚ) : ℝ) = (1 - ((B.b2 : ℚ) : ℝ)) /
        (((B.b2 : ℚ) : ℝ) * (-((lLo B.b1 : ℚ) : ℝ))) := by
      simp only [kB2]; push_cast; ring
    have hA1R : (κq : ℝ) ≤ ((kA1 B w : ℚ) : ℝ) := by exact_mod_cast hA1
    have hA2R : (κq : ℝ) ≤ ((kA2 B w : ℚ) : ℝ) := by exact_mod_cast hA2
    have hB1R : (κq : ℝ) ≤ ((kB1 B : ℚ) : ℝ) := by exact_mod_cast hB1
    have hB2R : (κq : ℝ) ≤ ((kB2 B : ℚ) : ℝ) := by exact_mod_cast hB2
    rw [c1] at hA1R
    rw [c2] at hA2R
    rw [c3] at hB1R
    rw [c4] at hB2R
    have hpa1R : (0 : ℝ) < ((aLo B w : ℚ) : ℝ) := by exact_mod_cast hpa1
    have hpA2R : ((aHi B w : ℚ) : ℝ) < 1 := by exact_mod_cast hpA2
    have hpb11R : (0 : ℝ) < ((B.b1 : ℚ) : ℝ) := by exact_mod_cast hpb11
    have hpb22R : ((B.b2 : ℚ) : ℝ) < 1 := by exact_mod_cast hpb22
    refine ⟨hκ0R, hκ2R, ?_, ?_, ?_, ?_⟩
    · exact kapA hκ0R hpa1R haL haH hpA2R lA3 hA1R
    · exact kapB hκ0R hpa1R haL haH hpA2R la1 hA2R
    · exact kapA hκ0R hpb11R hbL hbH hpb22R lB3 hB1R
    · exact kapB hκ0R hpb11R hbL hbH hpb22R lb1 hB2R
  · left; norm_num

/-- Curvature anchor: `etaCurvature (H v) ≤ P2up v`. -/
theorem P2up_bound {v : ℚ} (hpt : ptOk v = true) (hv2 : v < 1 / 2) (hlam : 0 < lamLo v) :
    etaCurvature (H (v : ℝ)) ≤ ((P2up v : ℚ) : ℝ) := by
  have hv := ptOk_pos hpt
  have hv0 : (0 : ℝ) < v := by exact_mod_cast hv.1
  have hv12 : (v : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hv2
    push_cast at h
    exact h
  obtain ⟨hl1, hl2⟩ := lam_bounds hpt
  obtain ⟨_, hL2⟩ := log_two_mem
  have hlamR : (0 : ℝ) < ((lamLo v : ℚ) : ℝ) := by exact_mod_cast hlam
  have h := etaCurvature_H_le hv0 hv12 hL2 hl1 hl2 hlamR
  have e : ((P2up v : ℚ) : ℝ) = ((LqHi : ℚ) : ℝ) *
      (((v : ℝ) * v + (1 - v) * (1 - v)) * ((lamHi v : ℚ) : ℝ) - (1 - 2 * (v : ℝ))) /
      ((v : ℝ) * v * ((1 - v) * (1 - v)) *
        (((lamLo v : ℚ) : ℝ) * ((lamLo v : ℚ) : ℝ) * ((lamLo v : ℚ) : ℝ))) := by
    simp only [P2up]; push_cast; ring
  rw [e]
  exact h

/-! ## Soundness -/

/-- Scalar assembly at law level: derivative criterion plus the (kappa) log-sum floor. -/
theorem assemble {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) (hlt : μ.a < μ.b)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy)
    {K P2 β κ IH : ℝ}
    (hΔK : μ.entropyDrop ≤ K * (μ.b - μ.a) ^ 2)
    (hI : μ.entropyDrop + μ.meanDeficit ≤ IH) (hIH1 : IH < 1)
    (hcurv : ∀ y : ℝ, 0 < y → y ≤ IH → etaCurvature (1 - y) ≤ P2)
    (hP2 : 0 ≤ P2) (hfin : K * P2 ≤ β) (hβ : β ≤ κ / (2 * (μ.b * (1 - μ.a))))
    (hκ : κ = 1 ∨ (0 ≤ κ ∧ κ ≤ 2 ∧
      κ * (-Real.log (1 - μ.a)) ≤ μ.a / (1 - μ.a) ∧ κ * (-Real.log μ.a) ≤ (1 - μ.a) / μ.a ∧
      κ * (-Real.log (1 - μ.b)) ≤ μ.b / (1 - μ.b) ∧ κ * (-Real.log μ.b) ≤ (1 - μ.b) / μ.b)) :
    μ.gap ≤ μ.cost := by
  have hΔ0 : 0 ≤ μ.entropyDrop := μ.entropyDrop_nonneg
  have hs0 : 0 ≤ μ.meanDeficit := μ.meanDeficit_mem.1
  have hcap : μ.entropyDrop + μ.meanDeficit < 1 := lt_of_le_of_lt hI hIH1
  have hfloor := floor_of_kap μ hlt hκ
  have ha0 : 0 < μ.a := μ.a_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb0 : 0 < μ.b := μ.b_interior.1
  have hb1 : μ.b < 1 := μ.b_interior.2
  have hzero : P μ.entropyDrop ≤ interiorCost μ.a μ.b :=
    deterministic_cap_bound ha0 ha1 hb0 hb1
  have hcurv' : ∀ y : ℝ, 0 < y → y ≤ μ.entropyDrop + μ.meanDeficit →
      μ.entropyDrop * etaCurvature (1 - y) ≤ κ * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))) := by
    intro y hy0 hy
    have hE := hcurv y hy0 (hy.trans hI)
    have h1 : μ.entropyDrop * etaCurvature (1 - y) ≤ μ.entropyDrop * P2 :=
      mul_le_mul_of_nonneg_left hE hΔ0
    have h2 : μ.entropyDrop * P2 ≤ (K * (μ.b - μ.a) ^ 2) * P2 := mul_le_mul_of_nonneg_right hΔK hP2
    have h3 : (K * (μ.b - μ.a) ^ 2) * P2 ≤ (μ.b - μ.a) ^ 2 * β := by
      have := mul_le_mul_of_nonneg_left hfin (sq_nonneg (μ.b - μ.a))
      linarith
    have h4 : (μ.b - μ.a) ^ 2 * β ≤ (μ.b - μ.a) ^ 2 * (κ / (2 * (μ.b * (1 - μ.a)))) :=
      mul_le_mul_of_nonneg_left hβ (sq_nonneg _)
    have h5 : (μ.b - μ.a) ^ 2 * (κ / (2 * (μ.b * (1 - μ.a)))) =
        κ * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))) := by ring
    linarith
  have hcrit := derivative_criterion hΔ0 hs0 hcap hzero hcurv'
  have hmain : μ.splitBound ≤ μ.cost := by
    have e : μ.splitBound = P (μ.entropyDrop + μ.meanDeficit) - P μ.meanDeficit := rfl
    rw [e]
    linarith
  exact μ.gap_le_of_splitBound hactive hmain

/-- Real entropy enclosures of the law's means from the checked rational points. -/
theorem law_H_bounds (B : SBox) (w : Wit) {a b : ℝ} (ha0 : 0 < a) (hb0 : 0 < b)
    (R1 : (0 : ℝ) < w.r1) (R2 : (w.r2 : ℝ) ≤ 1) (Rb1 : (0 : ℝ) < B.b1) (Rb2 : (B.b2 : ℝ) ≤ 1 / 2)
    (hpaL : ptOk (aLo B w) = true) (hpaH : ptOk (aHi B w) = true)
    (hpb1 : ptOk B.b1 = true) (hpb2 : ptOk B.b2 = true) (hpmH : ptOk (mHi B w) = true)
    (hb1 : (B.b1 : ℝ) ≤ b) (hb2 : b ≤ (B.b2 : ℝ))
    (gaL : (w.r1 : ℝ) * B.b1 ≤ a) (gaH : a ≤ (w.r2 : ℝ) * B.b2)
    (gmH : (a + b) / 2 ≤ (B.b2 : ℝ) * (1 + w.r2) / 2) :
    ((Hlo (aLo B w) : ℚ) : ℝ) ≤ H a ∧ H a ≤ ((Hhi (aHi B w) : ℚ) : ℝ) ∧
      ((Hlo B.b1 : ℚ) : ℝ) ≤ H b ∧ H b ≤ ((Hhi B.b2 : ℚ) : ℝ) ∧
      H ((a + b) / 2) ≤ ((Hhi (mHi B w) : ℚ) : ℝ) := by
  have caLo : ((aLo B w : ℚ) : ℝ) = (w.r1 : ℝ) * B.b1 := by simp only [aLo]; push_cast; ring
  have caHi : ((aHi B w : ℚ) : ℝ) = (w.r2 : ℝ) * B.b2 := by simp only [aHi]; push_cast; ring
  have cmHi : ((mHi B w : ℚ) : ℝ) = (B.b2 : ℝ) * (1 + w.r2) / 2 := by
    simp only [mHi]; push_cast; ring
  have hb2pos : (0 : ℝ) < B.b2 := lt_of_lt_of_le hb0 hb2
  have haHi_half : (w.r2 : ℝ) * B.b2 ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right R2 hb2pos.le
    linarith
  have hmHi_half : (B.b2 : ℝ) * (1 + w.r2) / 2 ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left R2 hb2pos.le
    linarith
  have hb_half : b ≤ 1 / 2 := hb2.trans Rb2
  have ha_half : a ≤ 1 / 2 := gaH.trans haHi_half
  obtain ⟨HaLo, _⟩ := H_bounds hpaL
  obtain ⟨_, HaHi⟩ := H_bounds hpaH
  obtain ⟨Hb1L, _⟩ := H_bounds hpb1
  obtain ⟨_, Hb2H⟩ := H_bounds hpb2
  obtain ⟨_, HmH⟩ := H_bounds hpmH
  rw [caLo] at HaLo
  rw [caHi] at HaHi
  rw [cmHi] at HmH
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact HaLo.trans (CKLaneE.NLS.H_le_H (mul_pos R1 Rb1).le gaL ha_half)
  · exact (CKLaneE.NLS.H_le_H ha0.le gaH haHi_half).trans HaHi
  · exact Hb1L.trans (CKLaneE.NLS.H_le_H Rb1.le hb1 hb_half)
  · exact (CKLaneE.NLS.H_le_H hb0.le hb2 Rb2).trans Hb2H
  · exact (CKLaneE.NLS.H_le_H (by linarith) gmH hmHi_half).trans HmH

/-- `Δ ≤ K d²` from the checked data. -/
theorem law_K_bound (B : SBox) (w : Wit) (hzr : zrOk w = true) {a b : ℝ} (ha0 : 0 < a)
    (hab : a < b) (hb1 : b < 1)
    (hmL : (0 : ℝ) < ((mLo B w : ℚ) : ℝ)) (hmL' : ((mLo B w : ℚ) : ℝ) ≤ (a + b) / 2)
    (hmH : (a + b) / 2 ≤ ((mHi B w : ℚ) : ℝ)) (hmH1 : ((mHi B w : ℚ) : ℝ) < 1)
    (hrho : (b - a) / (a + b) ≤ ((rhoHi w : ℚ) : ℝ)) (hdH : b - a ≤ ((dHi B w : ℚ) : ℝ)) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ ((Kq B w : ℚ) : ℝ) * (b - a) ^ 2 := by
  have hs2 : 0 < a + b := by linarith
  have ht2 : 0 < 2 - a - b := by linarith
  have hρ0 : 0 < (b - a) / (a + b) := div_pos (by linarith) hs2
  have hρ1 : (b - a) / (a + b) < 1 := (div_lt_one hs2).mpr (by linarith)
  have hκ0 : 0 < (b - a) / (2 - a - b) := div_pos (by linarith) ht2
  have hκ1 : (b - a) / (2 - a - b) < 1 := (div_lt_one ht2).mpr (by linarith)
  have hU1 : crR ((b - a) / (a + b)) ≤ ((cr1 w : ℚ) : ℝ) := cr1_bound hzr hρ0 hrho hρ1
  have hκle : (b - a) / (2 - a - b) ≤ ((kapHi B w : ℚ) : ℝ) := by
    have ck : ((kapHi B w : ℚ) : ℝ) = ((dHi B w : ℚ) : ℝ) / (2 * (1 - ((mHi B w : ℚ) : ℝ))) := by
      simp only [kapHi]; push_cast; ring
    rw [ck, div_le_div_iff₀ ht2 (by linarith)]
    have hd0 : 0 ≤ b - a := by linarith
    have h1 : 2 * (1 - ((mHi B w : ℚ) : ℝ)) ≤ 2 - a - b := by linarith
    calc (b - a) * (2 * (1 - ((mHi B w : ℚ) : ℝ))) ≤ (b - a) * (2 - a - b) :=
          mul_le_mul_of_nonneg_left h1 hd0
      _ ≤ ((dHi B w : ℚ) : ℝ) * (2 - a - b) := mul_le_mul_of_nonneg_right hdH ht2.le
  have hU2 : crR ((b - a) / (2 - a - b)) ≤ ((cr2 B w : ℚ) : ℝ) := crR_le_crPoly hκ0 hκle hκ1
  have hΔK := entropyDrop_le_K ha0 hab hb1 hU1 hU2 hmL hmL' hmH hmH1
  have cK : ((Kq B w : ℚ) : ℝ) = ((cr1 w : ℚ) : ℝ) / (4 * ((mLo B w : ℚ) : ℝ)) +
      ((cr2 B w : ℚ) : ℝ) / (4 * (1 - ((mHi B w : ℚ) : ℝ))) := by
    simp only [Kq]; push_cast; ring
  rw [cK]
  linarith

/-- `H(m) - E ≤ IHi` from the checked data. -/
theorem law_I_bound (B : SBox) (w : Wit) {a b E Δ : ℝ}
    (hΔ : Δ = H ((a + b) / 2) - (H a + H b) / 2)
    (hHaL : ((Hlo (aLo B w) : ℚ) : ℝ) ≤ H a) (hHaH : H a ≤ ((Hhi (aHi B w) : ℚ) : ℝ))
    (hHbL : ((Hlo B.b1 : ℚ) : ℝ) ≤ H b) (hHbH : H b ≤ ((Hhi B.b2 : ℚ) : ℝ))
    (hHmH : H ((a + b) / 2) ≤ ((Hhi (mHi B w) : ℚ) : ℝ))
    (Rt1 : (0 : ℝ) ≤ B.t1) (Rt11 : (B.t1 : ℝ) ≤ 1) (hE : (B.t1 : ℝ) * ((H a + H b) / 2) ≤ E)
    (hΔK : Δ ≤ ((Kq B w : ℚ) : ℝ) * (b - a) ^ 2) (hK0 : (0 : ℝ) ≤ ((Kq B w : ℚ) : ℝ))
    (hd0 : 0 ≤ b - a) (hdH : b - a ≤ ((dHi B w : ℚ) : ℝ)) :
    Δ + ((H a + H b) / 2 - E) ≤ ((IHi B w : ℚ) : ℝ) := by
  have cCLo : ((CLo B w : ℚ) : ℝ) = (((Hlo (aLo B w) : ℚ) : ℝ) + ((Hlo B.b1 : ℚ) : ℝ)) / 2 := by
    simp only [CLo]; push_cast; ring
  have cCHi : ((CHi B w : ℚ) : ℝ) = (((Hhi (aHi B w) : ℚ) : ℝ) + ((Hhi B.b2 : ℚ) : ℝ)) / 2 := by
    simp only [CHi]; push_cast; ring
  have hCLo : ((CLo B w : ℚ) : ℝ) ≤ (H a + H b) / 2 := by rw [cCLo]; linarith
  have hCHi : (H a + H b) / 2 ≤ ((CHi B w : ℚ) : ℝ) := by rw [cCHi]; linarith
  have hI1 : Δ + ((H a + H b) / 2 - E) ≤ ((I1 B w : ℚ) : ℝ) := by
    have c : ((I1 B w : ℚ) : ℝ) = ((Hhi (mHi B w) : ℚ) : ℝ) - (B.t1 : ℝ) * ((CLo B w : ℚ) : ℝ) := by
      simp only [I1]; push_cast; ring
    rw [c, hΔ]
    have : (B.t1 : ℝ) * ((CLo B w : ℚ) : ℝ) ≤ (B.t1 : ℝ) * ((H a + H b) / 2) :=
      mul_le_mul_of_nonneg_left hCLo Rt1
    linarith
  have hI2 : Δ + ((H a + H b) / 2 - E) ≤ ((I2 B w : ℚ) : ℝ) := by
    have c : ((I2 B w : ℚ) : ℝ) = ((CHi B w : ℚ) : ℝ) * (1 - (B.t1 : ℝ)) +
        ((Kq B w : ℚ) : ℝ) * (((dHi B w : ℚ) : ℝ) * ((dHi B w : ℚ) : ℝ)) := by
      simp only [I2]; push_cast; ring
    rw [c]
    have hdd : (b - a) ^ 2 ≤ ((dHi B w : ℚ) : ℝ) * ((dHi B w : ℚ) : ℝ) := by
      have := mul_le_mul hdH hdH hd0 (hd0.trans hdH)
      calc (b - a) ^ 2 = (b - a) * (b - a) := by ring
        _ ≤ _ := this
    have h1 : Δ ≤ ((Kq B w : ℚ) : ℝ) * (((dHi B w : ℚ) : ℝ) * ((dHi B w : ℚ) : ℝ)) :=
      hΔK.trans (mul_le_mul_of_nonneg_left hdd hK0)
    have h3 : (H a + H b) / 2 * (1 - (B.t1 : ℝ)) ≤ ((CHi B w : ℚ) : ℝ) * (1 - (B.t1 : ℝ)) :=
      mul_le_mul_of_nonneg_right hCHi (by linarith)
    have h4 : (H a + H b) / 2 - E ≤ (H a + H b) / 2 * (1 - (B.t1 : ℝ)) := by
      have e : (H a + H b) / 2 * (1 - (B.t1 : ℝ)) = (H a + H b) / 2 - (B.t1 : ℝ) * ((H a + H b) / 2) := by
        ring
      rw [e]
      linarith
    linarith
  simp only [IHi]
  rw [Rat.cast_min]
  exact le_min hI1 hI2

/-- `P''(y) ≤ P2up v` for all `0 < y ≤ IHi`, and `P2up v ≥ 0`. -/
theorem law_curv_bound (B : SBox) (w : Wit) (hptv : ptOk w.v = true) (hv2 : w.v < 1 / 2)
    (hlam : 0 < lamLo w.v) (hHv : Hhi w.v ≤ 1 - IHi B w) (hIH1 : IHi B w < 1) :
    (∀ y : ℝ, 0 < y → y ≤ ((IHi B w : ℚ) : ℝ) → etaCurvature (1 - y) ≤ ((P2up w.v : ℚ) : ℝ)) ∧
      (0 : ℝ) ≤ ((P2up w.v : ℚ) : ℝ) := by
  have hv := ptOk_pos hptv
  have hv0 : (0 : ℝ) < w.v := by exact_mod_cast hv.1
  have hv12 : (w.v : ℝ) < 1 / 2 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hv2
    push_cast at h
    exact h
  obtain ⟨_, hHvH⟩ := H_bounds hptv
  have hHvI : ((Hhi w.v : ℚ) : ℝ) ≤ 1 - ((IHi B w : ℚ) : ℝ) := by exact_mod_cast hHv
  have hIH1R : ((IHi B w : ℚ) : ℝ) < 1 := by exact_mod_cast hIH1
  have hP2 := P2up_bound hptv hv2 hlam
  refine ⟨?_, ?_⟩
  · intro y hy0 hy
    have hy1 : y < 1 := lt_of_le_of_lt hy hIH1R
    have hHy : H (w.v : ℝ) ≤ 1 - y := by linarith
    exact (etaCurvature_le_anchor hv0 hv12 hy0 hy1 hHy).trans hP2
  · have hH0 : 0 < H (w.v : ℝ) := H_pos hv0 (by linarith)
    have hH1 : H (w.v : ℝ) < 1 := CKLaneE.H_lt_one_of_lt_half hv0.le hv12
    exact (etaCurvature_nonneg hH0 hH1).trans hP2

/-- `betaLo ≤ κ / (2 b (1-a))`. -/
theorem law_beta_bound (B : SBox) (w : Wit) {a b : ℝ} (hκ : (0 : ℝ) ≤ ((kapEff B w : ℚ) : ℝ))
    (ha1 : a < 1) (hb0 : 0 < b) (hb2 : b ≤ (B.b2 : ℝ)) (gaL : (w.r1 : ℝ) * B.b1 ≤ a) :
    ((betaLo B w : ℚ) : ℝ) ≤ ((kapEff B w : ℚ) : ℝ) / (2 * (b * (1 - a))) := by
  have cbeta : ((betaLo B w : ℚ) : ℝ) =
      ((kapEff B w : ℚ) : ℝ) / (2 * (B.b2 : ℝ) * (1 - (w.r1 : ℝ) * B.b1)) := by
    simp only [betaLo, aLo]; push_cast; ring
  rw [cbeta]
  have hbpos : 0 < b * (1 - a) := mul_pos hb0 (by linarith)
  apply div_le_div_of_nonneg_left hκ (by linarith)
  have h1 : 1 - a ≤ 1 - (w.r1 : ℝ) * B.b1 := by linarith
  have h3 : 2 * b * (1 - a) ≤ 2 * (B.b2 : ℝ) * (1 - a) := by
    have := mul_le_mul_of_nonneg_right hb2 (show (0 : ℝ) ≤ 2 * (1 - a) by linarith)
    linarith
  have h4 : 2 * (B.b2 : ℝ) * (1 - a) ≤ 2 * (B.b2 : ℝ) * (1 - (w.r1 : ℝ) * B.b1) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  calc 2 * (b * (1 - a)) = 2 * b * (1 - a) := by ring
    _ ≤ _ := h3.trans h4

/-- **Soundness of the derivative checker.** -/
theorem check_sound {B : SBox} {w : Wit} (hw : check B w = true) {ι : Type*} [Fintype ι]
    (μ : InteriorLaw ι) (hab : μ.a ≤ μ.b) (hin : InSBox B μ.a μ.b μ.meanEntropy)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  rcases hab.eq_or_lt with heq | hlt
  · exact gap_le_cost_of_eq μ heq hactive
  simp only [check, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨hbox, hpow⟩, hpts⟩, hzr⟩, hanc⟩, hfin⟩ := hw
  simp only [boxOk, decide_eq_true_eq] at hbox
  obtain ⟨_, _, qb1, _, qb2, qt1, qt11, qr1, _, qr2⟩ := hbox
  simp only [pow2Ok, Bool.and_eq_true] at hpow
  obtain ⟨hpl, hpu⟩ := hpow
  simp only [ptsOk, Bool.and_eq_true] at hpts
  obtain ⟨⟨⟨⟨hpaL, hpaH⟩, hpb1⟩, hpb2⟩, hpmH⟩ := hpts
  simp only [anchorOk, Bool.and_eq_true, decide_eq_true_eq] at hanc
  obtain ⟨hptv, hv2, hlam, hHv⟩ := hanc
  simp only [finalOk, decide_eq_true_eq] at hfin
  obtain ⟨qI1, qK0, qfin⟩ := hfin
  unfold InSBox at hin
  obtain ⟨hin1, hin2, hin3, hin4, hin5, _⟩ := hin
  have ha0 : 0 < μ.a := μ.a_interior.1
  have hb0 : 0 < μ.b := μ.b_interior.1
  have ha1 : μ.a < 1 := μ.a_interior.2
  have hb1 : μ.b < 1 := μ.b_interior.2
  have R1 : (0 : ℝ) < w.r1 := by exact_mod_cast qr1
  have R2 : (w.r2 : ℝ) ≤ 1 := by exact_mod_cast qr2
  have Rb1 : (0 : ℝ) < B.b1 := by exact_mod_cast qb1
  have Rb2 : (B.b2 : ℝ) ≤ 1 / 2 := by
    have h : ((B.b2 : ℚ) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast qb2
    simpa using h
  have Rt1 : (0 : ℝ) ≤ B.t1 := by exact_mod_cast qt1
  have Rt11 : (B.t1 : ℝ) ≤ 1 := by exact_mod_cast qt11
  have hr1 : (w.r1 : ℝ) ≤ μ.a / μ.b := (pow2LowerOK_sound hpl).trans hin1
  have hr2 : μ.a / μ.b ≤ (w.r2 : ℝ) := hin2.trans (pow2UpperOK_sound hpu)
  obtain ⟨gaL, gaH, gmL, gmH, _, gdH, grho⟩ :=
    CKLaneE.NLS.box_geometry R1 R2 Rb1 hb0 hr1 hr2 hin3 hin4
  have caLo : ((aLo B w : ℚ) : ℝ) = (w.r1 : ℝ) * B.b1 := by simp only [aLo]; push_cast; ring
  have caHi : ((aHi B w : ℚ) : ℝ) = (w.r2 : ℝ) * B.b2 := by simp only [aHi]; push_cast; ring
  have cmLo : ((mLo B w : ℚ) : ℝ) = (B.b1 : ℝ) * (1 + w.r1) / 2 := by
    simp only [mLo]; push_cast; ring
  have cmHi : ((mHi B w : ℚ) : ℝ) = (B.b2 : ℝ) * (1 + w.r2) / 2 := by
    simp only [mHi]; push_cast; ring
  have cdHi : ((dHi B w : ℚ) : ℝ) = (B.b2 : ℝ) * (1 - w.r1) := by
    simp only [dHi]; push_cast; ring
  have crho : ((rhoHi w : ℚ) : ℝ) = (1 - (w.r1 : ℝ)) / (1 + w.r1) := by
    simp only [rhoHi]; push_cast; ring
  obtain ⟨hHaL, hHaH, hHbL, hHbH, hHmH⟩ :=
    law_H_bounds B w ha0 hb0 R1 R2 Rb1 Rb2 hpaL hpaH hpb1 hpb2 hpmH hin3 hin4 gaL gaH gmH
  have hb2pos : (0 : ℝ) < B.b2 := lt_of_lt_of_le hb0 hin4
  have hmLpos : (0 : ℝ) < ((mLo B w : ℚ) : ℝ) := by
    rw [cmLo]
    have := mul_pos Rb1 (show (0 : ℝ) < 1 + w.r1 by linarith)
    linarith
  have hmHlt : ((mHi B w : ℚ) : ℝ) < 1 := by
    rw [cmHi]
    have := mul_le_mul_of_nonneg_left R2 hb2pos.le
    linarith
  have hΔK := law_K_bound B w hzr ha0 hlt hb1 hmLpos (by rw [cmLo]; exact gmL)
    (by rw [cmHi]; exact gmH) hmHlt (by rw [crho]; exact grho) (by rw [cdHi]; exact gdH)
  have hK0 : (0 : ℝ) ≤ ((Kq B w : ℚ) : ℝ) := by exact_mod_cast qK0
  have hΔdef : μ.entropyDrop = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl
  have hsdef : μ.meanDeficit = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy; ring
  have hI := law_I_bound B w hΔdef hHaL hHaH hHbL hHbH hHmH Rt1 Rt11 hin5
    (by rw [hΔdef]; exact hΔK) hK0 (by linarith) (by rw [cdHi]; exact gdH)
  rw [← hsdef] at hI
  obtain ⟨hcurv, hP2⟩ := law_curv_bound B w hptv hv2 hlam hHv qI1
  have hkap := kapEff_ok B w (a := μ.a) (b := μ.b) hpaL hpaH hpb1 hpb2 (by rw [caLo]; exact gaL)
    (by rw [caHi]; exact gaH) hin3 hin4
  have hκnn : (0 : ℝ) ≤ ((kapEff B w : ℚ) : ℝ) := by
    rcases hkap with h | h
    · rw [h]; norm_num
    · exact h.1
  have hβ := law_beta_bound B w hκnn ha1 hb0 hin4 gaL
  have hfinR : ((Kq B w : ℚ) : ℝ) * ((P2up w.v : ℚ) : ℝ) ≤ ((betaLo B w : ℚ) : ℝ) := by
    exact_mod_cast qfin
  have hIH1R : ((IHi B w : ℚ) : ℝ) < 1 := by exact_mod_cast qI1
  exact assemble μ hlt hactive (by rw [hΔdef]; exact hΔK) hI hIH1R hcurv hP2 hfinR hβ hkap

/-- Leaf form: a checked witness proves the semantic owner statement on the exact leaf box. -/
theorem check_sem {B : SBox} {w : Wit} (hw : check B w = true) : SemSBox B := by
  intro k μ hab hin hactive
  exact check_sound hw μ hab hin hactive

theorem checkLeaf_sound {p : List ℕ} {w : Wit} (h : checkLeaf p w = true) : SemSBox (ssBox p) :=
  check_sem h

theorem checkLeaves_sound (L : List (List ℕ × Wit))
    (h : (L.all fun x => checkLeaf x.1 x.2) = true) :
    ∀ x ∈ L, SemSBox (ssBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkLeaf_sound (h x hx)

end CKLaneM07

#check @CKLaneM07.check_sound
#check @CKLaneM07.check_sem
#check @CKLaneM07.checkLeaves_sound
#print axioms CKLaneM07.check_sound
#print axioms CKLaneM07.checkLeaves_sound

end


