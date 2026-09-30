-- Prove2me | Definitions.Def_CK_CKLaneD_FleetBase
-- name    : CK_CKLaneD_FleetBase
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:40:51.566347+00:00
-- url     : https://prove2.me/theorems/1e29bb51-9b14-45d6-8037-1dbb28368630
-- title:
--   Courtade–Kumar proof module `CKLaneD.FleetBase` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneD.FleetBase` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneD.FleetBase` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneD.FleetBase (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneD/FleetBase.lean)

import Definitions.Def_CK_CKLaneD_Endpoint

-- ===== source module CKLaneD.FleetBase =====
section

/-!
# Lane D: binding endpoint witnesses to archived (u,v,t) leaves

The archived outer-opposite partition lives in `(u, v, t) ∈ [3,28] × [1,28] × [0,1]` with
`a = 2^-u`, `b = 1 - 2^-v`, `E = EMIN + t (C0 - EMIN)`.  A leaf is identified by its path
(digits `0..5`: axis = digit / 2, side = digit % 2, exact halving).  `uvtBox` recomputes the exact
dyadic leaf box from the path; `imageCheck` certifies (with exact `Nat` powers) that the physical
image of that leaf, clipped by `a ≤ 1/10` and `a + b ≤ 1`, lies in the rational witness box.
-/

namespace CKLaneD

open GeneralCK

/-- Compact dyadic literal `n / 2^e` used to encode witness data. -/
def dy (n : ℤ) (e : ℕ) : ℚ := (n : ℚ) / ((2 ^ e : ℕ) : ℚ)

/-- A leaf box in archived `(u, v, t)` coordinates. -/
structure UVT where
  u0 : ℚ
  u1 : ℚ
  v0 : ℚ
  v1 : ℚ
  t0 : ℚ
  t1 : ℚ
  deriving Repr, DecidableEq

def uvtRoot : UVT := ⟨3, 28, 1, 28, 0, 1⟩

/-- One exact halving step of the archived partition (`OUTER_OPPOSITE.reconstruct`). -/
def uvtStep (B : UVT) (d : ℕ) : UVT :=
  match d with
  | 0 => { B with u1 := (B.u0 + B.u1) / 2 }
  | 1 => { B with u0 := (B.u0 + B.u1) / 2 }
  | 2 => { B with v1 := (B.v0 + B.v1) / 2 }
  | 3 => { B with v0 := (B.v0 + B.v1) / 2 }
  | 4 => { B with t1 := (B.t0 + B.t1) / 2 }
  | 5 => { B with t0 := (B.t0 + B.t1) / 2 }
  | _ => B

/-- The exact leaf box of an archived path. -/
def uvtBox (p : List ℕ) : UVT := p.foldl uvtStep uvtRoot

/-- The physical (clipped) image of a `(u,v,t)` leaf, at law level. -/
def InUVT (U : UVT) (a b E : ℝ) : Prop :=
  (2 : ℝ) ^ (-(U.u1 : ℝ)) ≤ a ∧ a ≤ (2 : ℝ) ^ (-(U.u0 : ℝ)) ∧
    1 - (2 : ℝ) ^ (-(U.v0 : ℝ)) ≤ b ∧ b ≤ 1 - (2 : ℝ) ^ (-(U.v1 : ℝ)) ∧
    a ≤ 1 / 10 ∧ a + b ≤ 1 ∧
    (EMIN : ℝ) + (U.t0 : ℝ) * ((H a + H b) / 2 - (EMIN : ℝ)) ≤ E ∧
    E ≤ (EMIN : ℝ) + (U.t1 : ℝ) * ((H a + H b) / 2 - (EMIN : ℝ))

/-- Semantic Bellman statement (psi candidate) on the exact physical image of an archived leaf. -/
def SemUVT (U : UVT) : Prop :=
  ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), InUVT U μ.a μ.b μ.meanEntropy →
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost

/-! ## Exact comparisons of `2^-u` with rationals via `Nat` powers -/

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
  have hden : (u.den : ℝ) ≠ 0 := by exact_mod_cast u.den_nz
  have hnum : (0 : ℤ) ≤ u.num := Rat.num_nonneg.mpr hu
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have hu' : (u : ℝ) = (u.num : ℝ) / (u.den : ℝ) := by
    rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
  have htn : ((u.num.toNat : ℕ) : ℝ) = (u.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
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

/-- The clipped physical image of the leaf `U` lies in the rational box `B`. -/
def imageCheck (U : UVT) (B : Box) : Bool :=
  decide (B.t0 = U.t0 ∧ B.t1 = U.t1) &&
  pow2LowerOK B.alo U.u1 &&
  (pow2UpperOK B.ahi U.u0 || decide (1 / 10 ≤ B.ahi)) &&
  pow2UpperOK (1 - B.blo) U.v0 &&
  (pow2LowerOK (1 - B.bhi) U.v1 || decide (1 - B.alo ≤ B.bhi))

theorem imageCheck_sound {U : UVT} {B : Box} (h : imageCheck U B = true) (hB : Sem B) :
    SemUVT U := by
  unfold imageCheck at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨ht0, ht1⟩, hal⟩, hah⟩, hbl⟩, hbh⟩ := h
  intro k μ hin
  unfold InUVT at hin
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hin
  apply hB k μ
  have hal' := pow2LowerOK_sound hal
  have hbl' := pow2UpperOK_sound hbl
  push_cast at hbl'
  refine ⟨hal'.trans h1, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hah with hah | hah
    · exact h2.trans (pow2UpperOK_sound hah)
    · have hq : ((1 / 10 : ℚ) : ℝ) ≤ (B.ahi : ℝ) := Rat.cast_le.mpr hah
      have h10 : ((1 / 10 : ℚ) : ℝ) = 1 / 10 := by norm_num
      rw [h10] at hq
      linarith
  · linarith
  · rcases hbh with hbh | hbh
    · have := pow2LowerOK_sound hbh
      push_cast at this
      linarith
    · have : (1 : ℝ) - (B.alo : ℝ) ≤ (B.bhi : ℝ) := by exact_mod_cast hbh
      linarith [hal'.trans h1]
  · rw [ht0]; exact h7
  · rw [ht1]; exact h8

/-- Per-leaf acceptance: certificate valid and bound to the archived path. -/
def checkLeaf (p : List ℕ) (w : EndpointWitness) : Bool :=
  imageCheck (uvtBox p) w.box && checkEndpoint w

theorem checkLeaf_sound {p : List ℕ} {w : EndpointWitness} (h : checkLeaf p w = true) :
    SemUVT (uvtBox p) := by
  unfold checkLeaf at h
  rw [Bool.and_eq_true] at h
  exact imageCheck_sound h.1 (endpoint_check_sound w h.2)

theorem checkLeaves_sound (L : List (List ℕ × EndpointWitness))
    (h : (L.all fun x => checkLeaf x.1 x.2) = true) :
    ∀ x ∈ L, SemUVT (uvtBox x.1) := by
  intro x hx
  rw [List.all_eq_true] at h
  exact checkLeaf_sound (h x hx)

end CKLaneD

end


