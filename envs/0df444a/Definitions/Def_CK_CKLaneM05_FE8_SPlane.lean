-- Prove2me | Definitions.Def_CK_CKLaneM05_FE8_SPlane
-- name    : CK_CKLaneM05_FE8_SPlane
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T00:42:21.06663+00:00
-- url     : https://prove2.me/theorems/e3ddd684-6e35-4df7-811c-6a65ea49a177
-- title:
--   Courtade–Kumar proof module `CKLaneM05.FE8.SPlane` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM05.FE8.SPlane` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM05.FE8.SPlane` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM05.FE8.SPlane (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM05/FE8/SPlane.lean)

import Definitions.Def_CK_CKLaneM05_FE8_Plane
import Definitions.Def_CK_CKLaneM2_SLChecker
import Definitions.Def_CK_CKLaneM07_KappaLogSum

-- ===== source module CKLaneM05.FE8.SPlane =====
section

/-!
# Lane M05 / FE8: same-side SHIFTED plane checker (`splaneCheck`)

Same relaxation as `FE8/Plane.lean` (same-side port of Lane D `checkCell`, `CKLaneE.FP` enclosures), with

* a general affine cost minorant `cost ≥ sK + sU a + sV b - 2 sA E`, one of
  - `pm = 0`: the θ-shifted log-sum plane at a rational anchor `(al, be)` (`CKLaneM2.slplane_cost_lower`),
  - `pm = 1`: the κ-shifted log-sum plane at `(al, be)` (NEW `kslplane_cost_lower`, from
    `CKLaneM07.kappa_tangentGap` / `CKLaneM07.kappa_klN`: `κ ≤ κ(al), κ(be)` checked by log bounds),
  - `pm = 2`: the symmetric contact plane at `v` (`CKLaneD.plane_cost_lower`);
  the anchored planes are put in closed form by `plane_lower_gen` (proof as `CKLaneM2.plane_lower_real`);
* the deficit-side slope `slam = 4` (`Scalar.P_increment_lower`) or the secant slope of the convex `P`
  on `[sL - hs, sL]` (`CKLaneM2.P_secant_lower`).

`splaneCheck_sound : splaneCheck B c = true → SemD B`, no other hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM05.FE8

open GeneralCK CKLaneE.FP

/-! ## Planes at an arbitrary anchor (law level) -/

/-- NEW: the κ-shifted log-sum plane at an arbitrary anchor `(α, β)`, averaged over the law. -/
theorem kslplane_cost_lower {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {α β κ : ℝ}
    (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (ha0 : κ * (-Real.log (1 - α)) ≤ α / (1 - α)) (ha1 : κ * (-Real.log α) ≤ (1 - α) / α)
    (hb0 : κ * (-Real.log (1 - β)) ≤ β / (1 - β)) (hb1 : κ * (-Real.log β) ≤ (1 - β) / β) :
    interiorCost α β + LogSum.gradLeft α β * (μ.a - α) + LogSum.gradRight α β * (μ.b - β) +
      κ * ((α - β) ^ 2 / (4 * LogSum.V α β)) *
        ((H α + (μ.a - α) * J α - μ.e) + (H β + (μ.b - β) * J β - μ.f)) ≤ μ.cost := by
  have h := μ.avg_mono (fun i => CKLaneM07.kappa_tangentGap hα hβ
    (μ.left_interior i) (μ.right_interior i)
    (CKLaneM07.kappa_klN hα.1 hα.2 hκ0 hκ2 ha0 ha1 (μ.left_interior i).1 (μ.left_interior i).2)
    (CKLaneM07.kappa_klN hβ.1 hβ.2 hκ0 hκ2 hb0 hb1 (μ.right_interior i).1 (μ.right_interior i).2))
  rw [LogSum.avg_const_mul, μ.avg_add, CKLaneM2.avg_bernD_anchor μ μ.left_interior hα,
    CKLaneM2.avg_bernD_anchor μ μ.right_interior hβ] at h
  have ht : μ.avg (fun i => LogSum.tangentGap α β (μ.left i) (μ.right i)) =
      μ.cost - interiorCost α β - LogSum.gradLeft α β * (μ.a - α) -
        LogSum.gradRight α β * (μ.b - β) := by
    unfold LogSum.tangentGap
    rw [μ.avg_sub, μ.avg_sub, μ.avg_sub, μ.avg_const,
      LogSum.avg_const_mul, LogSum.avg_const_mul, μ.avg_sub, μ.avg_sub, μ.avg_const, μ.avg_const]
    rfl
  rw [ht] at h
  have he : μ.avg (fun i => H (μ.left i)) = μ.e := rfl
  have hf : μ.avg (fun i => H (μ.right i)) = μ.f := rfl
  have ha : μ.avg μ.left = μ.a := rfl
  have hb : μ.avg μ.right = μ.b := rfl
  rw [he, hf, ha, hb] at h
  linarith

/-- Closed form of an anchored plane with enclosed coefficients (proof as `CKLaneM2.plane_lower_real`,
for an arbitrary nonnegative entropy coefficient `A`). -/
theorem plane_lower_gen {ι : Type*} [Fintype ι] (μ : InteriorLaw ι)
    {α β A Hal Jal Jau Hbl Jbl Jbu i0 i1 : ℝ}
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) (hA0 : 0 ≤ A)
    (hpl : interiorCost α β + LogSum.gradLeft α β * (μ.a - α) + LogSum.gradRight α β * (μ.b - β) +
      A * ((H α + (μ.a - α) * J α - μ.e) + (H β + (μ.b - β) * J β - μ.f)) ≤ μ.cost)
    (hHa : Hal ≤ H α) (hJa0 : Jal ≤ J α) (hJa1 : J α ≤ Jau)
    (hHb : Hbl ≤ H β) (hJb0 : Jbl ≤ J β) (hJb1 : J β ≤ Jbu)
    (hi0 : i0 ≤ (Real.log 2)⁻¹) (hi1 : (Real.log 2)⁻¹ ≤ i1) :
    A * (Hal - α * Jau) + A * (Hbl - β * Jbu) - (β - α) ^ 2 / (2 * (1 - α) * (1 - β)) * i1 +
      (Jbl / 2 + min ((A - 1 / 2) * Jal) ((A - 1 / 2) * Jau) +
        (α - β) / (2 * α * (1 - α)) * i1) * μ.a +
      (Jal / 2 + min ((A - 1 / 2) * Jbl) ((A - 1 / 2) * Jbu) +
        (β - α) / (2 * β * (1 - β)) * i0) * μ.b -
      2 * A * μ.meanEntropy ≤ μ.cost := by
  have hα' : 0 < α ∧ α < 1 := ⟨hα, by linarith⟩
  have hβ' : 0 < β ∧ β < 1 := ⟨by linarith, hβ⟩
  rw [CKLaneM2.slplane_expand hα' hβ'] at hpl
  have ha := μ.a_interior
  have hb := μ.b_interior
  have hE : μ.meanEntropy = (μ.e + μ.f) / 2 := rfl
  have hK1 : A * (Hal - α * Jau) ≤ A * (H α - α * J α) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hA0
  have hK2 : A * (Hbl - β * Jbu) ≤ A * (H β - β * J β) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hA0
  have hkK : 0 ≤ (β - α) ^ 2 / (2 * (1 - α) * (1 - β)) := by
    have : 0 < 2 * (1 - α) * (1 - β) := by
      have : 0 < 1 - α := by linarith
      have : 0 < 1 - β := by linarith
      positivity
    positivity
  have hK3 : (β - α) ^ 2 / (2 * (1 - α) * (1 - β)) * (Real.log 2)⁻¹ ≤
      (β - α) ^ 2 / (2 * (1 - α) * (1 - β)) * i1 := mul_le_mul_of_nonneg_left hi1 hkK
  have hrA : (α - β) / (2 * α * (1 - α)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg (by linarith)
    have : 0 < 1 - α := by linarith
    positivity
  have hU1 : (α - β) / (2 * α * (1 - α)) * i1 ≤ (α - β) / (2 * α * (1 - α)) * (Real.log 2)⁻¹ :=
    mul_le_mul_of_nonpos_left hi1 hrA
  have hU2 : min ((A - 1 / 2) * Jal) ((A - 1 / 2) * Jau) ≤ (A - 1 / 2) * J α := by
    rcases le_total 0 (A - 1 / 2) with hs | hs
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hJa0 hs)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hJa1 hs)
  have hUa : Jbl / 2 + min ((A - 1 / 2) * Jal) ((A - 1 / 2) * Jau) +
      (α - β) / (2 * α * (1 - α)) * i1 ≤
      J β / 2 + (A - 1 / 2) * J α + (α - β) / (2 * α * (1 - α)) * (Real.log 2)⁻¹ := by
    linarith
  have hrB : 0 ≤ (β - α) / (2 * β * (1 - β)) := by
    apply div_nonneg (by linarith)
    have : 0 < 1 - β := by linarith
    have : 0 < β := by linarith
    positivity
  have hV1 : (β - α) / (2 * β * (1 - β)) * i0 ≤ (β - α) / (2 * β * (1 - β)) * (Real.log 2)⁻¹ :=
    mul_le_mul_of_nonneg_left hi0 hrB
  have hV2 : min ((A - 1 / 2) * Jbl) ((A - 1 / 2) * Jbu) ≤ (A - 1 / 2) * J β := by
    rcases le_total 0 (A - 1 / 2) with hs | hs
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hJb0 hs)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hJb1 hs)
  have hVb : Jal / 2 + min ((A - 1 / 2) * Jbl) ((A - 1 / 2) * Jbu) +
      (β - α) / (2 * β * (1 - β)) * i0 ≤
      J α / 2 + (A - 1 / 2) * J β + (β - α) / (2 * β * (1 - β)) * (Real.log 2)⁻¹ := by
    linarith
  have hUam := mul_le_mul_of_nonneg_right hUa ha.1.le
  have hVbm := mul_le_mul_of_nonneg_right hVb hb.1.le
  rw [hE]
  linarith

/-- Rational bounds on `1 / log 2` from the FastPoint constants. -/
def iLoF : ℚ := 1 / LqHi
def iHiF : ℚ := 1 / LqLo

theorem inv_log2_mem : ((iLoF : ℚ) : ℝ) ≤ (Real.log 2)⁻¹ ∧ (Real.log 2)⁻¹ ≤ ((iHiF : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := log_two_mem
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 := LqLo_pos
  have e1 : ((iLoF : ℚ) : ℝ) = 1 / ((LqHi : ℚ) : ℝ) := by unfold iLoF; push_cast; ring
  have e2 : ((iHiF : ℚ) : ℝ) = 1 / ((LqLo : ℚ) : ℝ) := by unfold iHiF; push_cast; ring
  rw [e1, e2, ← one_div]
  exact ⟨one_div_le_one_div_of_le hl2 h2, one_div_le_one_div_of_le hL0 h1⟩

/-! ## Certificate and checker -/

/-- Shifted-plane certificate (untrusted data). -/
structure SC where
  pm : ℕ
  al : ℚ
  be : ℚ
  th : ℚ
  ka : ℚ
  v : ℚ
  hm : ℚ
  pLo : ℚ
  pHi : ℚ
  xa : ℚ
  xb : ℚ
  sL : ℚ
  useXc : Bool
  xc : ℚ
  useSec : Bool
  hs : ℚ
  xs : ℚ
  deriving Repr

section defs
variable (B : CKLaneD.Box) (c : SC)

/-- Contact-plane constants at `v` (as in `FE8/Plane.lean`). -/
def cnLo : ℚ := -(lHi c.v + l1Hi c.v)
def cnHi : ℚ := -(lLo c.v + l1Lo c.v)
def cbase : ℚ := (1 - 2 * c.v) ^ 2 / (2 * c.v * (1 - c.v))
def cKlo : ℚ := cbase c / cnHi c
def cKhi : ℚ := cbase c / cnLo c
def cccLo : ℚ := Jl c.v + 2 * cKlo c * Hlo c.v / (1 - 2 * c.v)

/-- Entropy coefficient of the plane. -/
def sA : ℚ :=
  if c.pm = 2 then cKhi c
  else if c.pm = 0 then (c.be - c.al) ^ 2 / (4 * (c.be * (1 - c.al)) * c.th)
  else c.ka * ((c.be - c.al) ^ 2 / (4 * (c.be * (1 - c.al))))

/-- Constant, `a` and `b` coefficients of the plane. -/
def sK : ℚ :=
  if c.pm = 2 then 0
  else sA c * (Hlo c.al - c.al * Jh c.al) + sA c * (Hlo c.be - c.be * Jh c.be) -
    (c.be - c.al) ^ 2 / (2 * (1 - c.al) * (1 - c.be)) * iHiF
def sU : ℚ :=
  if c.pm = 2 then -cccLo c
  else Jl c.be / 2 + min ((sA c - 1 / 2) * Jl c.al) ((sA c - 1 / 2) * Jh c.al) +
    (c.al - c.be) / (2 * c.al * (1 - c.al)) * iHiF
def sV : ℚ :=
  if c.pm = 2 then cccLo c
  else Jl c.al / 2 + min ((sA c - 1 / 2) * Jl c.be) ((sA c - 1 / 2) * Jh c.be) +
    (c.be - c.al) / (2 * c.be * (1 - c.be)) * iLoF

/-- Validity of the plane data. -/
def planeOK : Bool :=
  if c.pm = 2 then
    ptOk c.v && decide (0 < c.v ∧ 2 * c.v < 1) && decide (0 < cnLo c) &&
      decide (0 ≤ Hlo c.v ∧ 0 ≤ lamLo c.v)
  else
    decide (0 < c.al ∧ c.al < c.be ∧ 2 * c.be ≤ 1) && ptOk c.al && ptOk c.be &&
      decide (0 ≤ lamLo c.al ∧ 0 ≤ lamLo c.be) &&
      (if c.pm = 0 then
        decide (1 + c.al ≤ 2 * c.th ∧ 2 - c.al ≤ 2 * c.th ∧ 1 + c.be ≤ 2 * c.th ∧ 2 - c.be ≤ 2 * c.th)
      else
        decide (0 ≤ c.ka ∧ c.ka ≤ 2 ∧ c.ka * (-l1Lo c.al) ≤ c.al / (1 - c.al) ∧
          c.ka * (-lLo c.al) ≤ (1 - c.al) / c.al ∧ c.ka * (-l1Lo c.be) ≤ c.be / (1 - c.be) ∧
          c.ka * (-lLo c.be) ≤ (1 - c.be) / c.be))

/-- Relaxation quantities (as `FE8/Plane.lean`, with the general plane and slope). -/
def qnumM : ℚ := (Hhi (mLo B) - Hlo (mLo B - c.hm)) / c.hm
def qHmHi : ℚ := Hhi (mLo B) + max 0 (qnumM B c * (mHi B - mLo B))
def qPuLo : ℚ := (1 - 2 * c.xa) * Jh c.xa
def qPuHi : ℚ := (1 - 2 * c.xb) * Jh c.xb
def qPlS : ℚ := if c.useXc then (1 - 2 * c.xc) * Jl c.xc else 4 * c.sL
def qPu0 : ℚ := (1 - 2 * c.xs) * Jh c.xs
def qslam : ℚ := if c.useSec then (qPlS c - qPu0 c) / c.hs else 4
def qsig : ℚ := (qPuHi c - qPuLo c) / (c.pHi - c.pLo)
def qkap : ℚ := qsig c - 2 * sA c - qslam c
def qts : ℚ := if 0 ≤ qkap c then B.t0 else B.t1
def qgam : ℚ := (qkap c * qts B c + qslam c) / 2
def qconst : ℚ := -qPuLo c + qsig c * c.pLo + qPlS c - qslam c * c.sL
def qca : ℚ := sU c + qgam B c * mua B - qsig c * qnumM B c / 2
def qcb : ℚ := sV c + qgam B c * mub B - qsig c * qnumM B c / 2
def qc0 : ℚ :=
  sK c + qkap c * CKLaneD.EMIN * (1 - qts B c) +
    qgam B c * (Hlo B.alo - mua B * B.alo + Hlo B.blo - mub B * B.blo) -
    qsig c * (Hhi (mLo B) - qnumM B c * mLo B) + qconst c
def qfinal : ℚ :=
  qc0 B c + min (qca B c * B.alo) (qca B c * B.ahi) + min (qcb B c * B.blo) (qcb B c * B.bhi)

def qxcOK : Bool :=
  !c.useXc || (ptOk c.xc && decide (2 * c.xc ≤ 1 ∧ 1 - c.sL ≤ Hlo c.xc ∧ 0 ≤ lamLo c.xc))

def qsecOK : Bool :=
  !c.useSec || (ptOk c.xs && decide (0 < c.hs ∧ c.hs ≤ c.sL ∧ 2 * c.xs ≤ 1 ∧
    Hhi c.xs ≤ 1 - (c.sL - c.hs)))

/-- The Boolean shifted-plane cell checker (binds the box and every enclosure). -/
def splaneCheck : Bool :=
  boxSane B && boxPts B && decide (0 < c.hm ∧ c.hm < mLo B) &&
    ptOk (mLo B - c.hm) && ptOk c.xa && ptOk c.xb && planeOK c && qxcOK c && qsecOK c &&
    decide (CKLaneD.EMIN < C0lo B) &&
    decide (0 ≤ c.pLo ∧ c.pLo ≤ HmLo2 B - Eup B ∧ qHmHi B c - Elo B ≤ c.pHi ∧
      c.pLo < c.pHi ∧ c.pHi < 1) &&
    decide (2 * c.xa ≤ 1 ∧ Hhi c.xa ≤ 1 - c.pLo) &&
    decide (2 * c.xb ≤ 1 ∧ Hhi c.xb ≤ 1 - c.pHi) &&
    decide (0 ≤ c.sL ∧ c.sL ≤ (C0lo B - CKLaneD.EMIN) * (1 - B.t1)) &&
    decide (0 ≤ qsig c) && decide (0 ≤ qgam B c) && decide (0 ≤ qfinal B c)

end defs

/-! ## Soundness -/

/-- The contact plane at `v` (extracted from `FE8/Plane.lean`). -/
theorem contact_plane_lower {c : SC} (pv : ptOk c.v = true) (hv0q : 0 < c.v) (hv2 : 2 * c.v < 1)
    (hnLo : 0 < cnLo c) (hHv : 0 ≤ Hlo c.v) (hlamv : 0 ≤ lamLo c.v)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hd0 : 0 ≤ μ.b - μ.a) (hE0 : 0 < μ.meanEntropy) :
    ((cccLo c : ℚ) : ℝ) * (μ.b - μ.a) - 2 * ((cKhi c : ℚ) : ℝ) * μ.meanEntropy ≤ μ.cost := by
  have rv0 : (0 : ℝ) < (c.v : ℝ) := by exact_mod_cast hv0q
  have rv2 : 2 * (c.v : ℝ) < 1 := by exact_mod_cast hv2
  have hplane := CKLaneD.plane_cost_lower μ rv0 (by linarith : (c.v : ℝ) < 1 / 2)
  have hv1' : (0 : ℝ) < 1 - (c.v : ℝ) := by linarith
  obtain ⟨hl1, hl2, hl3, hl4⟩ := ptOk_sound pv
  have hlogm : Real.log ((c.v : ℝ) * (1 - (c.v : ℝ))) =
      Real.log (c.v : ℝ) + Real.log (1 - (c.v : ℝ)) := Real.log_mul rv0.ne' hv1'.ne'
  have rnLo : (0 : ℝ) < ((cnLo c : ℚ) : ℝ) := by exact_mod_cast hnLo
  have hnlo : ((cnLo c : ℚ) : ℝ) ≤ -Real.log ((c.v : ℝ) * (1 - (c.v : ℝ))) := by
    have e : ((cnLo c : ℚ) : ℝ) = -(((lHi c.v : ℚ) : ℝ) + ((l1Hi c.v : ℚ) : ℝ)) := by
      unfold cnLo; push_cast; ring
    rw [e, hlogm]; linarith
  have hnhi : -Real.log ((c.v : ℝ) * (1 - (c.v : ℝ))) ≤ ((cnHi c : ℚ) : ℝ) := by
    have e : ((cnHi c : ℚ) : ℝ) = -(((lLo c.v : ℚ) : ℝ) + ((l1Lo c.v : ℚ) : ℝ)) := by
      unfold cnHi; push_cast; ring
    rw [e, hlogm]; linarith
  have ebase : ((cbase c : ℚ) : ℝ) =
      (1 - 2 * (c.v : ℝ)) ^ 2 / (2 * (c.v : ℝ) * (1 - (c.v : ℝ))) := by
    unfold cbase; push_cast; ring
  have hbase : (0 : ℝ) < ((cbase c : ℚ) : ℝ) := by
    rw [ebase]
    have : (0 : ℝ) < 1 - 2 * (c.v : ℝ) := by linarith
    positivity
  have hnpos : 0 < -Real.log ((c.v : ℝ) * (1 - (c.v : ℝ))) := rnLo.trans_le hnlo
  have hK_eq : CKLaneD.planeK (c.v : ℝ) =
      ((cbase c : ℚ) : ℝ) / (-Real.log ((c.v : ℝ) * (1 - (c.v : ℝ)))) := by
    unfold CKLaneD.planeK; rw [ebase, div_div]
  have eKhi : ((cKhi c : ℚ) : ℝ) = ((cbase c : ℚ) : ℝ) / ((cnLo c : ℚ) : ℝ) := by
    unfold cKhi; push_cast; ring
  have eKlo : ((cKlo c : ℚ) : ℝ) = ((cbase c : ℚ) : ℝ) / ((cnHi c : ℚ) : ℝ) := by
    unfold cKlo; push_cast; ring
  have rnHi : (0 : ℝ) < ((cnHi c : ℚ) : ℝ) := hnpos.trans_le hnhi
  have hKhi : CKLaneD.planeK (c.v : ℝ) ≤ ((cKhi c : ℚ) : ℝ) := by
    rw [hK_eq, eKhi, div_le_div_iff₀ hnpos rnLo]
    exact mul_le_mul_of_nonneg_left hnlo hbase.le
  have hKlo : ((cKlo c : ℚ) : ℝ) ≤ CKLaneD.planeK (c.v : ℝ) := by
    rw [hK_eq, eKlo, div_le_div_iff₀ rnHi hnpos]
    exact mul_le_mul_of_nonneg_left hnhi hbase.le
  have hKlo0 : (0 : ℝ) ≤ ((cKlo c : ℚ) : ℝ) := by rw [eKlo]; exact div_nonneg hbase.le rnHi.le
  have rHv : (0 : ℝ) ≤ ((Hlo c.v : ℚ) : ℝ) := by exact_mod_cast hHv
  obtain ⟨hvHl, _⟩ := H_bounds pv
  have hvJl := Jl_le pv hlamv
  have hcc : ((cccLo c : ℚ) : ℝ) ≤
      J (c.v : ℝ) + 2 * CKLaneD.planeK (c.v : ℝ) * H (c.v : ℝ) / (1 - 2 * (c.v : ℝ)) := by
    have e : ((cccLo c : ℚ) : ℝ) = ((Jl c.v : ℚ) : ℝ) +
        2 * ((cKlo c : ℚ) : ℝ) * ((Hlo c.v : ℚ) : ℝ) / (1 - 2 * (c.v : ℝ)) := by
      unfold cccLo; push_cast; ring
    rw [e]
    have hr : (0 : ℝ) < 1 - 2 * (c.v : ℝ) := by linarith
    have hprod : ((cKlo c : ℚ) : ℝ) * ((Hlo c.v : ℚ) : ℝ) ≤ CKLaneD.planeK (c.v : ℝ) * H (c.v : ℝ) :=
      mul_le_mul hKlo hvHl rHv (hKlo0.trans hKlo)
    have hdiv : 2 * ((cKlo c : ℚ) : ℝ) * ((Hlo c.v : ℚ) : ℝ) / (1 - 2 * (c.v : ℝ)) ≤
        2 * CKLaneD.planeK (c.v : ℝ) * H (c.v : ℝ) / (1 - 2 * (c.v : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hr.le
      linarith
    linarith
  have h1 := mul_le_mul_of_nonneg_right hcc hd0
  have h2 := mul_le_mul_of_nonneg_right hKhi hE0.le
  linarith

/-- The plane of a valid certificate. -/
theorem splane_cost {c : SC} (h : planeOK c = true) {k : ℕ} (μ : InteriorLaw (Fin k))
    (hd0 : 0 ≤ μ.b - μ.a) (hE0 : 0 < μ.meanEntropy) :
    ((sK c : ℚ) : ℝ) + ((sU c : ℚ) : ℝ) * μ.a + ((sV c : ℚ) : ℝ) * μ.b -
      2 * ((sA c : ℚ) : ℝ) * μ.meanEntropy ≤ μ.cost := by
  unfold planeOK at h
  by_cases h2 : c.pm = 2
  · rw [if_pos h2] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨pv, hv0, hv2⟩, hnLo⟩, hHv, hlamv⟩ := h
    have hc := contact_plane_lower pv hv0 hv2 hnLo hHv hlamv μ hd0 hE0
    have eK : sK c = 0 := by unfold sK; rw [if_pos h2]
    have eU : sU c = -cccLo c := by unfold sU; rw [if_pos h2]
    have eV : sV c = cccLo c := by unfold sV; rw [if_pos h2]
    have eA : sA c = cKhi c := by unfold sA; rw [if_pos h2]
    rw [eK, eU, eV, eA]
    push_cast
    linarith
  · rw [if_neg h2] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨hal0, halbe, hbe2⟩, pal⟩, pbe⟩, hlal, hlbe⟩, hmode⟩ := h
    have ral0 : (0 : ℝ) < (c.al : ℝ) := by exact_mod_cast hal0
    have ralbe : (c.al : ℝ) < (c.be : ℝ) := by exact_mod_cast halbe
    have rbe2 : 2 * (c.be : ℝ) ≤ 1 := by exact_mod_cast hbe2
    have rbe1 : (c.be : ℝ) < 1 := by linarith
    have hα' : 0 < (c.al : ℝ) ∧ (c.al : ℝ) < 1 := ⟨ral0, by linarith⟩
    have hβ' : 0 < (c.be : ℝ) ∧ (c.be : ℝ) < 1 := ⟨by linarith, rbe1⟩
    have hV : LogSum.V (c.al : ℝ) (c.be : ℝ) = (c.be : ℝ) * (1 - (c.al : ℝ)) := by
      unfold LogSum.V; rw [max_eq_right ralbe.le, min_eq_left ralbe.le]
    have hVpos : (0 : ℝ) < (c.be : ℝ) * (1 - (c.al : ℝ)) := mul_pos (by linarith) (by linarith)
    -- the plane with an exact entropy coefficient `sA`
    have hpl : interiorCost (c.al : ℝ) (c.be : ℝ) +
        LogSum.gradLeft (c.al : ℝ) (c.be : ℝ) * (μ.a - (c.al : ℝ)) +
        LogSum.gradRight (c.al : ℝ) (c.be : ℝ) * (μ.b - (c.be : ℝ)) +
        ((sA c : ℚ) : ℝ) * ((H (c.al : ℝ) + (μ.a - (c.al : ℝ)) * J (c.al : ℝ) - μ.e) +
          (H (c.be : ℝ) + (μ.b - (c.be : ℝ)) * J (c.be : ℝ) - μ.f)) ≤ μ.cost ∧
        (0 : ℝ) ≤ ((sA c : ℚ) : ℝ) := by
      by_cases h0 : c.pm = 0
      · rw [if_pos h0] at hmode
        simp only [decide_eq_true_eq] at hmode
        obtain ⟨t1, t2, t3, t4⟩ := hmode
        have r1 : 1 + (c.al : ℝ) ≤ 2 * (c.th : ℝ) := by exact_mod_cast t1
        have r2 : 2 - (c.al : ℝ) ≤ 2 * (c.th : ℝ) := by exact_mod_cast t2
        have r3 : 1 + (c.be : ℝ) ≤ 2 * (c.th : ℝ) := by exact_mod_cast t3
        have r4 : 2 - (c.be : ℝ) ≤ 2 * (c.th : ℝ) := by exact_mod_cast t4
        have hθa : CKLaneM2.theta (c.al : ℝ) ≤ (c.th : ℝ) := by
          unfold CKLaneM2.theta; have := max_le r1 r2; linarith
        have hθb : CKLaneM2.theta (c.be : ℝ) ≤ (c.th : ℝ) := by
          unfold CKLaneM2.theta; have := max_le r3 r4; linarith
        have hth : (0 : ℝ) < (c.th : ℝ) := by linarith
        have hs := CKLaneM2.slplane_cost_lower μ hα' hβ' hθa hθb
        have eA : ((sA c : ℚ) : ℝ) =
            ((c.al : ℝ) - (c.be : ℝ)) ^ 2 / (4 * LogSum.V (c.al : ℝ) (c.be : ℝ) * (c.th : ℝ)) := by
          unfold sA; rw [if_neg h2, if_pos h0, hV]; push_cast; ring
        refine ⟨?_, ?_⟩
        · rw [eA]; exact hs
        · rw [eA, hV]
          apply div_nonneg (sq_nonneg _)
          exact (mul_pos (mul_pos (by norm_num) hVpos) hth).le
      · rw [if_neg h0] at hmode
        simp only [decide_eq_true_eq] at hmode
        obtain ⟨k0, k2, ka0, ka1, kb0, kb1⟩ := hmode
        have rk0 : (0 : ℝ) ≤ (c.ka : ℝ) := by exact_mod_cast k0
        have rk2 : (c.ka : ℝ) ≤ 2 := by exact_mod_cast k2
        obtain ⟨la1, _, la3, _⟩ := ptOk_sound pal
        obtain ⟨lb1, _, lb3, _⟩ := ptOk_sound pbe
        have cka0 : (c.ka : ℝ) * (-Real.log (1 - (c.al : ℝ))) ≤ (c.al : ℝ) / (1 - (c.al : ℝ)) := by
          have h' : (c.ka : ℝ) * (-((l1Lo c.al : ℚ) : ℝ)) ≤ (c.al : ℝ) / (1 - (c.al : ℝ)) := by
            have := (Rat.cast_le (K := ℝ)).mpr ka0; push_cast at this; exact this
          have := mul_le_mul_of_nonneg_left (show -Real.log (1 - (c.al : ℝ)) ≤
            -((l1Lo c.al : ℚ) : ℝ) by linarith) rk0
          linarith
        have cka1 : (c.ka : ℝ) * (-Real.log (c.al : ℝ)) ≤ (1 - (c.al : ℝ)) / (c.al : ℝ) := by
          have h' : (c.ka : ℝ) * (-((lLo c.al : ℚ) : ℝ)) ≤ (1 - (c.al : ℝ)) / (c.al : ℝ) := by
            have := (Rat.cast_le (K := ℝ)).mpr ka1; push_cast at this; exact this
          have := mul_le_mul_of_nonneg_left (show -Real.log (c.al : ℝ) ≤
            -((lLo c.al : ℚ) : ℝ) by linarith) rk0
          linarith
        have ckb0 : (c.ka : ℝ) * (-Real.log (1 - (c.be : ℝ))) ≤ (c.be : ℝ) / (1 - (c.be : ℝ)) := by
          have h' : (c.ka : ℝ) * (-((l1Lo c.be : ℚ) : ℝ)) ≤ (c.be : ℝ) / (1 - (c.be : ℝ)) := by
            have := (Rat.cast_le (K := ℝ)).mpr kb0; push_cast at this; exact this
          have := mul_le_mul_of_nonneg_left (show -Real.log (1 - (c.be : ℝ)) ≤
            -((l1Lo c.be : ℚ) : ℝ) by linarith) rk0
          linarith
        have ckb1 : (c.ka : ℝ) * (-Real.log (c.be : ℝ)) ≤ (1 - (c.be : ℝ)) / (c.be : ℝ) := by
          have h' : (c.ka : ℝ) * (-((lLo c.be : ℚ) : ℝ)) ≤ (1 - (c.be : ℝ)) / (c.be : ℝ) := by
            have := (Rat.cast_le (K := ℝ)).mpr kb1; push_cast at this; exact this
          have := mul_le_mul_of_nonneg_left (show -Real.log (c.be : ℝ) ≤
            -((lLo c.be : ℚ) : ℝ) by linarith) rk0
          linarith
        have hs := kslplane_cost_lower μ hα' hβ' rk0 rk2 cka0 cka1 ckb0 ckb1
        have eA : ((sA c : ℚ) : ℝ) =
            (c.ka : ℝ) * (((c.al : ℝ) - (c.be : ℝ)) ^ 2 / (4 * LogSum.V (c.al : ℝ) (c.be : ℝ))) := by
          unfold sA; rw [if_neg h2, if_neg h0, hV]; push_cast; ring
        refine ⟨?_, ?_⟩
        · rw [eA]; exact hs
        · rw [eA, hV]
          exact mul_nonneg rk0 (div_nonneg (sq_nonneg _) (mul_pos (by norm_num) hVpos).le)
    obtain ⟨hpl, hA0⟩ := hpl
    obtain ⟨hHal, _⟩ := H_bounds pal
    obtain ⟨hHbe, _⟩ := H_bounds pbe
    have hJal := Jl_le pal hlal
    have hJau := le_Jh pal (by linarith)
    have hJbl := Jl_le pbe hlbe
    have hJbu := le_Jh pbe (by linarith)
    obtain ⟨hi0, hi1⟩ := inv_log2_mem
    have key := plane_lower_gen μ ral0 ralbe rbe1 hA0 hpl hHal hJal hJau hHbe hJbl hJbu hi0 hi1
    have eK : ((sK c : ℚ) : ℝ) = ((sA c : ℚ) : ℝ) * (((Hlo c.al : ℚ) : ℝ) - (c.al : ℝ) * ((Jh c.al : ℚ) : ℝ)) +
        ((sA c : ℚ) : ℝ) * (((Hlo c.be : ℚ) : ℝ) - (c.be : ℝ) * ((Jh c.be : ℚ) : ℝ)) -
        ((c.be : ℝ) - (c.al : ℝ)) ^ 2 / (2 * (1 - (c.al : ℝ)) * (1 - (c.be : ℝ))) *
          ((iHiF : ℚ) : ℝ) := by
      unfold sK; rw [if_neg h2]; push_cast; ring
    have eU : ((sU c : ℚ) : ℝ) = ((Jl c.be : ℚ) : ℝ) / 2 +
        min ((((sA c : ℚ) : ℝ) - 1 / 2) * ((Jl c.al : ℚ) : ℝ))
          ((((sA c : ℚ) : ℝ) - 1 / 2) * ((Jh c.al : ℚ) : ℝ)) +
        ((c.al : ℝ) - (c.be : ℝ)) / (2 * (c.al : ℝ) * (1 - (c.al : ℝ))) * ((iHiF : ℚ) : ℝ) := by
      unfold sU; rw [if_neg h2]; push_cast; ring
    have eV : ((sV c : ℚ) : ℝ) = ((Jl c.al : ℚ) : ℝ) / 2 +
        min ((((sA c : ℚ) : ℝ) - 1 / 2) * ((Jl c.be : ℚ) : ℝ))
          ((((sA c : ℚ) : ℝ) - 1 / 2) * ((Jh c.be : ℚ) : ℝ)) +
        ((c.be : ℝ) - (c.al : ℝ)) / (2 * (c.be : ℝ) * (1 - (c.be : ℝ))) * ((iLoF : ℚ) : ℝ) := by
      unfold sV; rw [if_neg h2]; push_cast; ring
    rw [eK, eU, eV]
    exact key

theorem qPlS_le {c : SC} (hx : qxcOK c = true) (hs0 : 0 ≤ (c.sL : ℝ)) (hs1 : (c.sL : ℝ) < 1) :
    ((qPlS c : ℚ) : ℝ) ≤ Scalar.P (c.sL : ℝ) := by
  unfold qxcOK at hx
  unfold qPlS
  cases hu : c.useXc with
  | false =>
    rw [if_neg Bool.false_ne_true]
    push_cast
    exact Scalar.four_mul_le_P hs0 hs1
  | true =>
    rw [hu] at hx
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨hp, h2, h3, hlam⟩ := hx
    rw [if_pos rfl]
    have hx0 : (0 : ℝ) < c.xc := by exact_mod_cast (ptOk_pos hp).1
    have h2' : 2 * (c.xc : ℝ) ≤ 1 := by exact_mod_cast h2
    obtain ⟨hHl, _⟩ := H_bounds hp
    have h3' : 1 - (c.sL : ℝ) ≤ ((Hlo c.xc : ℚ) : ℝ) := by
      have h := (Rat.cast_le (K := ℝ)).mpr h3; push_cast at h; exact h
    have hb := CKLaneD.P_ge_bracket hs0 hs1 hx0 (by linarith) (h3'.trans hHl)
    have hJl := Jl_le hp hlam
    push_cast
    have := mul_le_mul_of_nonneg_left hJl (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xc : ℝ))
    linarith

/-- Affine lower bound of `P` on the deficit side with slope `qslam`. -/
theorem qslam_lower {c : SC} (hx : qxcOK c = true) (hsec : qsecOK c = true)
    (hs0 : 0 ≤ (c.sL : ℝ)) {s : ℝ} (hss : (c.sL : ℝ) ≤ s) (hs1 : s < 1) :
    ((qPlS c : ℚ) : ℝ) + ((qslam c : ℚ) : ℝ) * (s - c.sL) ≤ Scalar.P s := by
  have hPl := qPlS_le hx hs0 (by linarith)
  unfold qslam
  unfold qsecOK at hsec
  cases hu : c.useSec with
  | false =>
    rw [if_neg Bool.false_ne_true]
    have hinc := Scalar.P_increment_lower hs0 hs1 hss
    push_cast
    linarith
  | true =>
    rw [hu] at hsec
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hsec
    obtain ⟨hp, hh0, hh1, hx2, hxH⟩ := hsec
    rw [if_pos rfl]
    have rh0 : (0 : ℝ) < (c.hs : ℝ) := by exact_mod_cast hh0
    have rh1 : (c.hs : ℝ) ≤ (c.sL : ℝ) := by exact_mod_cast hh1
    have rx2 : 2 * (c.xs : ℝ) ≤ 1 := by exact_mod_cast hx2
    have rxH : ((Hhi c.xs : ℚ) : ℝ) ≤ 1 - ((c.sL : ℝ) - c.hs) := by
      have h := (Rat.cast_le (K := ℝ)).mpr hxH; push_cast at h; exact h
    have hxs0 : (0 : ℝ) < (c.xs : ℝ) := by exact_mod_cast (ptOk_pos hp).1
    obtain ⟨_, hxsHu⟩ := H_bounds hp
    have hPu0 : Scalar.P ((c.sL : ℝ) - c.hs) ≤ ((qPu0 c : ℚ) : ℝ) := by
      have hb := CKLaneD.P_le_bracket (p := (c.sL : ℝ) - c.hs) (xa := (c.xs : ℝ)) (by linarith)
        (by linarith) hxs0 (by linarith) (hxsHu.trans rxH)
      have hJ := le_Jh hp (by linarith)
      have e : ((qPu0 c : ℚ) : ℝ) = (1 - 2 * (c.xs : ℝ)) * ((Jh c.xs : ℚ) : ℝ) := by
        unfold qPu0; push_cast; ring
      have := mul_le_mul_of_nonneg_left hJ (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xs : ℝ))
      rw [e]; linarith
    have hsecl := CKLaneM2.P_secant_lower (s0 := (c.sL : ℝ) - c.hs) (s1 := (c.sL : ℝ)) (s := s)
      (by linarith) (by linarith) hss hs1
    have hslope : (((qPlS c : ℚ) : ℝ) - ((qPu0 c : ℚ) : ℝ)) / (c.hs : ℝ) ≤
        (Scalar.P (c.sL : ℝ) - Scalar.P ((c.sL : ℝ) - c.hs)) / ((c.sL : ℝ) - ((c.sL : ℝ) - c.hs)) := by
      have e2 : (c.sL : ℝ) - ((c.sL : ℝ) - c.hs) = (c.hs : ℝ) := by ring
      rw [e2]
      exact div_le_div_of_nonneg_right (by linarith) rh0.le
    have hmul := mul_le_mul_of_nonneg_right hslope (by linarith : (0 : ℝ) ≤ s - c.sL)
    push_cast
    linarith

set_option maxHeartbeats 4000000 in
theorem splaneCheck_sound {B : CKLaneD.Box} {c : SC} (h : splaneCheck B c = true) : SemD B := by
  intro k μ hbox hd
  simp only [splaneCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hs, hp, hhm0, hhm1, pMh, pxa, pxb, hplane, hxc, hsec, hC0, hpL0, hpL1, hpH1, hpLH, hpH2,
    hxa1, hxa2, hxb1, hxb2, hsL0, hsL1, hsig, hgam, hfin⟩ := h
  -- box facts
  obtain ⟨hmLo, hmHi, hmHh, hm0, hHmL, hHmH, hElo, hEup, hEm, hE0, _⟩ := box_facts hs hp μ hbox
  have hs' := hs
  simp only [boxSane, decide_eq_true_eq] at hs'
  obtain ⟨sa0, sa1, sa2, sb0, sb1, sb2, st0, st1, st2⟩ := hs'
  have hp' := hp
  simp only [boxPts, Bool.and_eq_true] at hp'
  obtain ⟨⟨⟨⟨⟨pa0, pa1⟩, pb0⟩, pb1⟩, pm0⟩, pm1⟩ := hp'
  obtain ⟨ha0, ha1, hb0, hb1, hE0', hE1'⟩ := hbox
  have hjen := CKLaneD.law_gap_le_P μ
  have hm_def : μ.midpoint = (μ.a + μ.b) / 2 := rfl
  rw [← hm_def] at hjen
  -- casts
  have rA0 : (0 : ℝ) < ((B.alo : ℚ) : ℝ) := by exact_mod_cast sa0
  have rA2 : ((B.ahi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr sa2; push_cast at h; exact h
  have rB0 : (0 : ℝ) < ((B.blo : ℚ) : ℝ) := by exact_mod_cast sb0
  have rB2 : ((B.bhi : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr sb2; push_cast at h; exact h
  have rt0 : (0 : ℝ) ≤ ((B.t0 : ℚ) : ℝ) := by exact_mod_cast st0
  have rt01 : ((B.t0 : ℚ) : ℝ) ≤ ((B.t1 : ℚ) : ℝ) := by exact_mod_cast st1
  have rt1 : ((B.t1 : ℚ) : ℝ) ≤ 1 := by exact_mod_cast st2
  -- entropy enclosures at the corners
  obtain ⟨HA0l, _⟩ := H_bounds pa0
  obtain ⟨HA1l, HA1u⟩ := H_bounds pa1
  obtain ⟨HB0l, _⟩ := H_bounds pb0
  obtain ⟨HB1l, HB1u⟩ := H_bounds pb1
  obtain ⟨HM0l, HM0u⟩ := H_bounds pm0
  obtain ⟨HM1l, _⟩ := H_bounds pm1
  obtain ⟨HMhl, _⟩ := H_bounds pMh
  have ha2 : μ.a ≤ 1 / 2 := ha1.trans rA2
  have hb2 : μ.b ≤ 1 / 2 := hb1.trans rB2
  have hHa_lo : ((Hlo B.alo : ℚ) : ℝ) ≤ H μ.a := HA0l.trans (H_le_H rA0.le ha0 ha2)
  have hHb_lo : ((Hlo B.blo : ℚ) : ℝ) ≤ H μ.b := HB0l.trans (H_le_H rB0.le hb0 hb2)
  have hC0lo : ((C0lo B : ℚ) : ℝ) ≤ (H μ.a + H μ.b) / 2 := by
    have e : ((C0lo B : ℚ) : ℝ) = (((Hlo B.alo : ℚ) : ℝ) + ((Hlo B.blo : ℚ) : ℝ)) / 2 := by
      unfold C0lo; push_cast; ring
    rw [e]; linarith
  -- parent mean enclosures
  have c_mLo : ((mLo B : ℚ) : ℝ) = ((B.alo : ℚ) : ℝ) / 2 + ((B.blo : ℚ) : ℝ) / 2 := by
    unfold mLo; push_cast; ring
  have c_mHi : ((mHi B : ℚ) : ℝ) = ((B.ahi : ℚ) : ℝ) / 2 + ((B.bhi : ℚ) : ℝ) / 2 := by
    unfold mHi; push_cast; ring
  have rhm0 : (0 : ℝ) < (c.hm : ℝ) := by exact_mod_cast hhm0
  have rhm1 : (c.hm : ℝ) < ((mLo B : ℚ) : ℝ) := by exact_mod_cast hhm1
  have rmLo0 : (0 : ℝ) ≤ ((mLo B : ℚ) : ℝ) := by linarith
  have rmHi1 : ((mHi B : ℚ) : ℝ) ≤ 1 := by linarith
  have hHm_lo : ((HmLo2 B : ℚ) : ℝ) ≤ H μ.midpoint := by
    have hc := CKLaneD.H_chord_lower (lo := ((mLo B : ℚ) : ℝ)) (hi := ((mHi B : ℚ) : ℝ))
      (x := μ.midpoint) (HL0 := ((HmLo2 B : ℚ) : ℝ)) (HL1 := ((HmLo2 B : ℚ) : ℝ)) rmLo0 hmLo hmHi
      rmHi1 (by unfold HmLo2; rw [Rat.cast_min]; exact (min_le_left _ _).trans HM0l)
      (by unfold HmLo2; rw [Rat.cast_min]; exact (min_le_right _ _).trans HM1l)
    calc ((HmLo2 B : ℚ) : ℝ) = ((HmLo2 B : ℚ) : ℝ) + (((HmLo2 B : ℚ) : ℝ) - ((HmLo2 B : ℚ) : ℝ)) /
          (((mHi B : ℚ) : ℝ) - ((mLo B : ℚ) : ℝ)) * (μ.midpoint - ((mLo B : ℚ) : ℝ)) := by ring
      _ ≤ H μ.midpoint := hc
  have hMhl' : ((Hlo (mLo B - c.hm) : ℚ) : ℝ) ≤ H (((mLo B : ℚ) : ℝ) - (c.hm : ℝ)) := by
    have := HMhl; push_cast at this; exact this
  have enum : ((qnumM B c : ℚ) : ℝ) =
      (((Hhi (mLo B) : ℚ) : ℝ) - ((Hlo (mLo B - c.hm) : ℚ) : ℝ)) / (c.hm : ℝ) := by
    unfold qnumM; push_cast; ring
  have hHm_tan : H μ.midpoint ≤
      ((Hhi (mLo B) : ℚ) : ℝ) + ((qnumM B c : ℚ) : ℝ) * (μ.midpoint - ((mLo B : ℚ) : ℝ)) := by
    have hc := CKLaneD.H_leftslope_upper (lo := ((mLo B : ℚ) : ℝ)) (h := (c.hm : ℝ))
      (x := μ.midpoint) (HU0 := ((Hhi (mLo B) : ℚ) : ℝ))
      (HLh := ((Hlo (mLo B - c.hm) : ℚ) : ℝ)) rhm0 (by linarith) hmLo (by linarith) HM0u hMhl'
    rw [enum]; exact hc
  have hHm_hi : H μ.midpoint ≤ ((qHmHi B c : ℚ) : ℝ) := by
    have hmm : 0 ≤ μ.midpoint - ((mLo B : ℚ) : ℝ) := by linarith
    have hmm2 : μ.midpoint - ((mLo B : ℚ) : ℝ) ≤ ((mHi B : ℚ) : ℝ) - ((mLo B : ℚ) : ℝ) := by
      linarith
    have hmax : ((qnumM B c : ℚ) : ℝ) * (μ.midpoint - ((mLo B : ℚ) : ℝ)) ≤
        max 0 (((qnumM B c : ℚ) : ℝ) * (((mHi B : ℚ) : ℝ) - ((mLo B : ℚ) : ℝ))) := by
      rcases le_total 0 ((qnumM B c : ℚ) : ℝ) with hn | hn
      · exact (mul_le_mul_of_nonneg_left hmm2 hn).trans (le_max_right _ _)
      · exact (mul_nonpos_iff.mpr (Or.inr ⟨hn, hmm⟩)).trans (le_max_left _ _)
    have e : ((qHmHi B c : ℚ) : ℝ) = ((Hhi (mLo B) : ℚ) : ℝ) +
        max 0 (((qnumM B c : ℚ) : ℝ) * (((mHi B : ℚ) : ℝ) - ((mLo B : ℚ) : ℝ))) := by
      unfold qHmHi; push_cast; ring
    rw [e]; linarith
  -- information range
  have rpL0 : (0 : ℝ) ≤ (c.pLo : ℝ) := by exact_mod_cast hpL0
  have rpL1 : (c.pLo : ℝ) ≤ ((HmLo2 B : ℚ) : ℝ) - ((Eup B : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hpL1; push_cast at h; exact h
  have rpH1 : ((qHmHi B c : ℚ) : ℝ) - ((Elo B : ℚ) : ℝ) ≤ (c.pHi : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hpH1; push_cast at h; exact h
  have rpLH : (c.pLo : ℝ) < (c.pHi : ℝ) := by exact_mod_cast hpLH
  have rpH2 : (c.pHi : ℝ) < 1 := by exact_mod_cast hpH2
  have hIlo : (c.pLo : ℝ) ≤ H μ.midpoint - μ.meanEntropy := by linarith
  have hIhi : H μ.midpoint - μ.meanEntropy ≤ (c.pHi : ℝ) := by linarith
  -- deficit range
  have hdef := CKLaneD.law_deficit_mem μ
  have rsL0 : (0 : ℝ) ≤ (c.sL : ℝ) := by exact_mod_cast hsL0
  have rsL1 : (c.sL : ℝ) ≤ (((C0lo B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) * (1 - ((B.t1 : ℚ) : ℝ)) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsL1; push_cast at h; exact h
  have hsL : (c.sL : ℝ) ≤ (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
    have h1 : (((C0lo B : ℚ) : ℝ) - (CKLaneD.EMIN : ℝ)) * (1 - ((B.t1 : ℚ) : ℝ)) ≤
        ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) * (1 - ((B.t1 : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) * (1 - ((B.t1 : ℚ) : ℝ)) =
        (H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ) -
          ((B.t1 : ℚ) : ℝ) * ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ)) := by ring
    linarith
  -- P upper bound on the information side
  have rxa1 : 2 * (c.xa : ℝ) ≤ 1 := by exact_mod_cast hxa1
  have rxb1 : 2 * (c.xb : ℝ) ≤ 1 := by exact_mod_cast hxb1
  obtain ⟨_, HXa⟩ := H_bounds pxa
  obtain ⟨_, HXb⟩ := H_bounds pxb
  have rxa2 : ((Hhi c.xa : ℚ) : ℝ) ≤ 1 - (c.pLo : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hxa2; push_cast at h; exact h
  have rxb2 : ((Hhi c.xb : ℚ) : ℝ) ≤ 1 - (c.pHi : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hxb2; push_cast at h; exact h
  have hxa0 : (0 : ℝ) < c.xa := by exact_mod_cast (ptOk_pos pxa).1
  have hxb0 : (0 : ℝ) < c.xb := by exact_mod_cast (ptOk_pos pxb).1
  have hPLo : Scalar.P (c.pLo : ℝ) ≤ ((qPuLo c : ℚ) : ℝ) := by
    have hb := CKLaneD.P_le_bracket rpL0 (by linarith) hxa0 (by linarith) (HXa.trans rxa2)
    have hJ := le_Jh pxa (by linarith)
    have e : ((qPuLo c : ℚ) : ℝ) = (1 - 2 * (c.xa : ℝ)) * ((Jh c.xa : ℚ) : ℝ) := by
      unfold qPuLo; push_cast; ring
    have := mul_le_mul_of_nonneg_left hJ (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xa : ℝ))
    rw [e]; linarith
  have hPHi : Scalar.P (c.pHi : ℝ) ≤ ((qPuHi c : ℚ) : ℝ) := by
    have hb := CKLaneD.P_le_bracket (by linarith) rpH2 hxb0 (by linarith) (HXb.trans rxb2)
    have hJ := le_Jh pxb (by linarith)
    have e : ((qPuHi c : ℚ) : ℝ) = (1 - 2 * (c.xb : ℝ)) * ((Jh c.xb : ℚ) : ℝ) := by
      unfold qPuHi; push_cast; ring
    have := mul_le_mul_of_nonneg_left hJ (by linarith : (0 : ℝ) ≤ 1 - 2 * (c.xb : ℝ))
    rw [e]; linarith
  have esig : ((qsig c : ℚ) : ℝ) =
      (((qPuHi c : ℚ) : ℝ) - ((qPuLo c : ℚ) : ℝ)) / ((c.pHi : ℝ) - (c.pLo : ℝ)) := by
    unfold qsig; push_cast; ring
  have hPI : Scalar.P (H μ.midpoint - μ.meanEntropy) ≤
      ((qPuLo c : ℚ) : ℝ) + ((qsig c : ℚ) : ℝ) * (H μ.midpoint - μ.meanEntropy - (c.pLo : ℝ)) := by
    have hch := CKLaneD.P_chord rpL0 hIlo hIhi rpH2 rpLH
    have hm2 := CKLaneD.chord_mono (f0 := Scalar.P (c.pLo : ℝ)) (f1 := Scalar.P (c.pHi : ℝ))
      (g0 := ((qPuLo c : ℚ) : ℝ)) (g1 := ((qPuHi c : ℚ) : ℝ)) (Δ := (c.pHi : ℝ) - (c.pLo : ℝ))
      (x := H μ.midpoint - μ.meanEntropy - (c.pLo : ℝ))
      (by linarith) (by linarith) (by linarith) hPLo hPHi
    rw [esig]; exact hch.trans hm2
  -- P lower bound on the deficit side
  have hPs : ((qPlS c : ℚ) : ℝ) + ((qslam c : ℚ) : ℝ) *
      ((H μ.a + H μ.b) / 2 - μ.meanEntropy - (c.sL : ℝ)) ≤
      Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) :=
    qslam_lower hxc hsec rsL0 hsL hdef.2
  -- the plane
  have hd0 : 0 ≤ μ.b - μ.a := by linarith
  have hcost := splane_cost hplane μ hd0 hE0
  -- relaxation algebra
  have rsig : (0 : ℝ) ≤ ((qsig c : ℚ) : ℝ) := by exact_mod_cast hsig
  have rgam : (0 : ℝ) ≤ ((qgam B c : ℚ) : ℝ) := by exact_mod_cast hgam
  have rfin : (0 : ℝ) ≤ ((qfinal B c : ℚ) : ℝ) := by exact_mod_cast hfin
  have hkapE : ((qkap c : ℚ) : ℝ) * ((CKLaneD.EMIN : ℝ) + ((qts B c : ℚ) : ℝ) *
      ((H μ.a + H μ.b) / 2 - (CKLaneD.EMIN : ℝ))) ≤ ((qkap c : ℚ) : ℝ) * μ.meanEntropy := by
    unfold qts
    split_ifs with hk
    · have rk : (0 : ℝ) ≤ ((qkap c : ℚ) : ℝ) := by exact_mod_cast hk
      exact mul_le_mul_of_nonneg_left hE0' rk
    · have rk : ((qkap c : ℚ) : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hk))
      exact mul_le_mul_of_nonpos_left hE1' rk
  have hchA : ((Hlo B.alo : ℚ) : ℝ) + ((mua B : ℚ) : ℝ) * (μ.a - ((B.alo : ℚ) : ℝ)) ≤ H μ.a := by
    have hc := CKLaneD.H_chord_lower (lo := ((B.alo : ℚ) : ℝ)) (hi := ((B.ahi : ℚ) : ℝ)) (x := μ.a)
      (HL0 := ((Hlo B.alo : ℚ) : ℝ)) (HL1 := ((Hlo B.ahi : ℚ) : ℝ)) rA0.le ha0 ha1
      (by linarith) HA0l HA1l
    have e : ((mua B : ℚ) : ℝ) =
        (((Hlo B.ahi : ℚ) : ℝ) - ((Hlo B.alo : ℚ) : ℝ)) / (((B.ahi : ℚ) : ℝ) - ((B.alo : ℚ) : ℝ)) := by
      unfold mua; push_cast; ring
    rw [e]; exact hc
  have hchB : ((Hlo B.blo : ℚ) : ℝ) + ((mub B : ℚ) : ℝ) * (μ.b - ((B.blo : ℚ) : ℝ)) ≤ H μ.b := by
    have hc := CKLaneD.H_chord_lower (lo := ((B.blo : ℚ) : ℝ)) (hi := ((B.bhi : ℚ) : ℝ)) (x := μ.b)
      (HL0 := ((Hlo B.blo : ℚ) : ℝ)) (HL1 := ((Hlo B.bhi : ℚ) : ℝ)) rB0.le hb0 hb1
      (by linarith) HB0l HB1l
    have e : ((mub B : ℚ) : ℝ) =
        (((Hlo B.bhi : ℚ) : ℝ) - ((Hlo B.blo : ℚ) : ℝ)) / (((B.bhi : ℚ) : ℝ) - ((B.blo : ℚ) : ℝ)) := by
      unfold mub; push_cast; ring
    rw [e]; exact hc
  have hgamH := mul_le_mul_of_nonneg_left (add_le_add hchA hchB) rgam
  have hsigH := mul_le_mul_of_nonneg_left hHm_tan rsig
  have hcorner : (0 : ℝ) ≤ ((qc0 B c : ℚ) : ℝ) + ((qca B c : ℚ) : ℝ) * μ.a +
      ((qcb B c : ℚ) : ℝ) * μ.b := by
    have e1 := CKLaneD.min_mul_le (q := qca B c) ha0 ha1
    have e2 := CKLaneD.min_mul_le (q := qcb B c) hb0 hb1
    have e : ((qfinal B c : ℚ) : ℝ) = ((qc0 B c : ℚ) : ℝ) +
        ((min (qca B c * B.alo) (qca B c * B.ahi) : ℚ) : ℝ) +
        ((min (qcb B c * B.blo) (qcb B c * B.bhi) : ℚ) : ℝ) := by
      unfold qfinal; push_cast; ring
    linarith
  have egam : ((qgam B c : ℚ) : ℝ) = (((qkap c : ℚ) : ℝ) * ((qts B c : ℚ) : ℝ) +
      ((qslam c : ℚ) : ℝ)) / 2 := by
    unfold qgam; push_cast; ring
  have ekap : ((qkap c : ℚ) : ℝ) = ((qsig c : ℚ) : ℝ) - 2 * ((sA c : ℚ) : ℝ) -
      ((qslam c : ℚ) : ℝ) := by
    unfold qkap; push_cast; ring
  have econst : ((qconst c : ℚ) : ℝ) = -((qPuLo c : ℚ) : ℝ) + ((qsig c : ℚ) : ℝ) * (c.pLo : ℝ) +
      ((qPlS c : ℚ) : ℝ) - ((qslam c : ℚ) : ℝ) * (c.sL : ℝ) := by
    unfold qconst; push_cast; ring
  have ec0 : ((qc0 B c : ℚ) : ℝ) = ((sK c : ℚ) : ℝ) + ((qkap c : ℚ) : ℝ) * (CKLaneD.EMIN : ℝ) *
      (1 - ((qts B c : ℚ) : ℝ)) +
      ((qgam B c : ℚ) : ℝ) * (((Hlo B.alo : ℚ) : ℝ) - ((mua B : ℚ) : ℝ) * ((B.alo : ℚ) : ℝ) +
        ((Hlo B.blo : ℚ) : ℝ) - ((mub B : ℚ) : ℝ) * ((B.blo : ℚ) : ℝ)) -
      ((qsig c : ℚ) : ℝ) * (((Hhi (mLo B) : ℚ) : ℝ) - ((qnumM B c : ℚ) : ℝ) * ((mLo B : ℚ) : ℝ)) +
      ((qconst c : ℚ) : ℝ) := by
    unfold qc0; push_cast; ring
  have eca : ((qca B c : ℚ) : ℝ) = ((sU c : ℚ) : ℝ) + ((qgam B c : ℚ) : ℝ) * ((mua B : ℚ) : ℝ) -
      ((qsig c : ℚ) : ℝ) * ((qnumM B c : ℚ) : ℝ) / 2 := by
    unfold qca; push_cast; ring
  have ecb : ((qcb B c : ℚ) : ℝ) = ((sV c : ℚ) : ℝ) + ((qgam B c : ℚ) : ℝ) * ((mub B : ℚ) : ℝ) -
      ((qsig c : ℚ) : ℝ) * ((qnumM B c : ℚ) : ℝ) / 2 := by
    unfold qcb; push_cast; ring
  rw [ec0, eca, ecb, econst, egam, ekap] at hcorner
  rw [egam, ekap] at hgamH
  rw [ekap] at hkapE
  rw [hm_def] at hsigH hPI hjen
  generalize Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) = PI at hjen hPI
  generalize Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) = PS at hjen hPs
  rw [c_mLo] at hsigH hcorner
  linarith only [hjen, hPI, hPs, hkapE, hgamH, hsigH, hcorner, hcost]

theorem leafOK_of_splaneCheck {B : CKLaneD.Box} {c : SC} (h : splaneCheck B c = true) : LeafOK B :=
  leafOK_of_semD (splaneCheck_sound h)

end CKLaneM05.FE8

#check @CKLaneM05.FE8.splaneCheck_sound
#print axioms CKLaneM05.FE8.kslplane_cost_lower
#print axioms CKLaneM05.FE8.plane_lower_gen
#print axioms CKLaneM05.FE8.splane_cost
#print axioms CKLaneM05.FE8.splaneCheck_sound
#print axioms CKLaneM05.FE8.leafOK_of_splaneCheck

end


