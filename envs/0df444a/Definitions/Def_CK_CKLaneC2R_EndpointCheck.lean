-- Prove2me | Definitions.Def_CK_CKLaneC2R_EndpointCheck
-- name    : CK_CKLaneC2R_EndpointCheck
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T13:51:12.301846+00:00
-- url     : https://prove2.me/theorems/c65bd4c2-e5b6-408b-9642-775e78d32fa0
-- title:
--   Courtade–Kumar proof module `CKLaneC2R.EndpointCheck` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2R.EndpointCheck` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2R.EndpointCheck` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2R.EndpointCheck (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2R/EndpointCheck.lean)

import Definitions.Def_CK_CKLaneC2R_CompactCheck
import Definitions.Def_CK_GeneralCK_Certificates_RegularContactBounds
import Definitions.Def_CK_GeneralCK_ReflectionEndpointBridge

-- ===== source module CKLaneC2R.EndpointCheck =====
section

/-!
# Lane C2 (reflection compact): reflective checker for endpoint cells (`z` up to `1`)

The compact program divides by `1 - z`.  Near `z = 1` we evaluate the endpoint-safe
`RegularReflectionExpression.normalizedValue` instead (its regular contact is analytic at the
zero-radius endpoint) with plain dyadic interval arithmetic:

* entropy enclosures are monotone (`biasE` is antitone on `[0,1]`), from executable point witnesses
  at the interval endpoints;
* regular contacts are bracketed with `RegularContactBounds.contact_contains`;
* `biasB` and `log` enclosures use the executable witnesses of `ReflectionFastTranscendental`.

`ecellOk c = true` (discharged per cell by `decide +kernel`) implies
`0 < Reflection.curvature a (a*z)` on the box, for `z < 1`.
-/

namespace CKLaneC2R.Endpoint

open GeneralCK GeneralCK.Certificates
open ReflectionFastTranscendental

abbrev DI := DyadicInterval 40
abbrev one : DI := DyadicInterval.ofInt 40 1
abbrev two : DI := DyadicInterval.ofInt 40 2
abbrev half : DI := DyadicEntropy.half 40
abbrev S40 : ℤ := DyadicInterval.scale 40

structure ECell where
  al : ℚ
  au : ℚ
  zl : ℚ
  zu : ℚ
  A : DI
  Z : DI
  eAl : EntropyWitness
  eAh : EntropyWitness
  eBl : EntropyWitness
  eBh : EntropyWitness
  cm : DI
  ecmL : EntropyWitness
  ecmH : EntropyWitness
  bcm : BWitness
  cp : DI
  ecpL : EntropyWitness
  ecpH : EntropyWitness
  bcp : BWitness
  lp : DI
  lpw : LogWitness
  lm : DI
  lmw : LogWitness

/-- Monotone entropy enclosure on `[lo,hi] ⊆ [0,1]`: lower from the witness at `hi`,
upper from the witness at `lo`. -/
def emono (wl wh : EntropyWitness) : DI := ⟨wh.output.lo, wl.output.hi⟩

def pointOk (x : ℤ) (w : EntropyWitness) : Bool := w.check (DyadicContact.point x)

def contactOk (Y c : DI) (wl wh : EntropyWitness) : Bool :=
  decide (0 ≤ Y.lo) && decide (0 ≤ c.lo) && decide (c.lo ≤ c.hi) && decide (c.hi ≤ S40) &&
    pointOk c.lo wl && pointOk c.hi wh &&
    decide (c.lo * S40 ≤ Y.lo * wl.output.lo) && decide (Y.hi * wh.output.hi ≤ c.hi * S40)

def gapI (C : DI) : DI := one.sub (C.mul C)

def secNum (C Ec Bc L : DI) : DI :=
  (Ec.mul ((Bc.add Bc).sub (C.mul C))).mul ((Ec.add (C.mul L)).mul (Ec.add (C.mul L)))

def secDen (C Bc E : DI) : DI :=
  ((E.add E).mul ((gapI C).mul (gapI C))).mul (Bc.mul (Bc.mul Bc))

def secDen2 (C Bc A : DI) : DI := ((one.sub (A.mul A)).mul (gapI C)).mul Bc

def secI (C Ec Bc A L E : DI) : DI :=
  ((secNum C Ec Bc L).mul (secDen C Bc E).recip).add ((C.mul C).mul (secDen2 C Bc A).recip)

def secOk (C Bc A E : DI) : Bool :=
  decide (0 < (secDen C Bc E).lo) && decide (0 < (secDen2 C Bc A).lo)

namespace ECell

def B (c : ECell) : DI := c.A.mul c.Z
def EA (c : ECell) : DI := emono c.eAl c.eAh
def EB (c : ECell) : DI := emono c.eBl c.eBh
def E (c : ECell) : DI := (c.EA.add c.EB).mul half
def RM (c : ECell) : DI := ((c.A.mul (one.sub c.Z)).mul half).mul c.E.recip
def RP (c : ECell) : DI := ((c.A.mul (one.add c.Z)).mul half).mul c.E.recip
def L (c : ECell) : DI := (c.lp.sub c.lm).mul half
def oma2 (c : ECell) : DI := (one.sub (c.A.mul c.A)).mul (one.sub (c.A.mul c.A))
def base (c : ECell) : DI := ((two.mul c.A).mul c.B).mul c.oma2.recip
def SM (c : ECell) : DI := secI c.cm (emono c.ecmL c.ecmH) c.bcm.output c.A c.L c.E
def SP (c : ECell) : DI := secI c.cp (emono c.ecpL c.ecpH) c.bcp.output c.A c.L c.E
def N (c : ECell) : DI := (c.base.add c.SM).sub c.SP

end ECell

def boxE (c : ECell) : Bool :=
  decide (0 < c.al) && decide (c.al < c.au) && decide (c.au < 1) &&
  decide (0 < c.zl) && decide (c.zl < c.zu) && decide (c.zu ≤ 1) &&
  memQ c.A c.al && memQ c.A c.au && memQ c.Z c.zl && memQ c.Z c.zu

def entE (c : ECell) : Bool :=
  decide (0 ≤ c.A.lo) && decide (c.A.hi ≤ S40) && decide (0 ≤ c.B.lo) && decide (c.B.hi ≤ S40) &&
  pointOk c.A.lo c.eAl && pointOk c.A.hi c.eAh && pointOk c.B.lo c.eBl && pointOk c.B.hi c.eBh &&
  decide (0 < c.E.lo)

def conE (c : ECell) : Bool :=
  contactOk c.RM c.cm c.ecmL c.ecmH && contactOk c.RP c.cp c.ecpL c.ecpH &&
  c.bcm.check c.cm && c.bcp.check c.cp &&
  c.lpw.check (one.add c.A) c.lp && c.lmw.check (one.sub c.A) c.lm

def finE (c : ECell) : Bool :=
  decide (0 < c.oma2.lo) && secOk c.cm c.bcm.output c.A c.E && secOk c.cp c.bcp.output c.A c.E &&
  decide (0 < c.N.lo)

/-- The reflective endpoint cell checker. -/
def ecellOk (c : ECell) : Bool := boxE c && entE c && conE c && finE c

/-! ## Soundness -/

theorem scale_pos' : (0 : ℝ) < ((S40 : ℤ) : ℝ) := DyadicInterval.scale_cast_pos 40

theorem one_contains : one.Contains (1 : ℝ) := by
  simpa using DyadicInterval.ofInt_sound 40 1

theorem two_contains : two.Contains (2 : ℝ) := by
  simpa using DyadicInterval.ofInt_sound 40 2

theorem pos_of_contains {d : DI} {x : ℝ} (hd : 0 < d.lo) (hx : d.Contains x) : 0 < x := by
  have h : (0 : ℝ) < d.lo := by exact_mod_cast hd
  exact pos_of_mul_pos_right (h.trans_le hx.1) scale_pos'.le

theorem point_entropy {x : ℤ} {w : EntropyWitness} (h : pointOk x w = true) :
    w.output.Contains (Reflection.biasE ((x : ℝ) / ((S40 : ℤ) : ℝ))) :=
  EntropyWitness.sound h (DyadicContact.point_contains 40 x)

theorem emono_contains {d : DI} {wl wh : EntropyWitness}
    (hl : pointOk d.lo wl = true) (hh : pointOk d.hi wh = true)
    (h0 : 0 ≤ d.lo) (h1 : d.hi ≤ S40) {x : ℝ} (hx : d.Contains x) :
    (emono wl wh).Contains (Reflection.biasE x) := by
  have hs := scale_pos'
  have el := point_entropy hl
  have eh := point_entropy hh
  have hxl : (d.lo : ℝ) / ((S40 : ℤ) : ℝ) ≤ x := by
    rw [div_le_iff₀ hs]; linarith [hx.1]
  have hxh : x ≤ (d.hi : ℝ) / ((S40 : ℤ) : ℝ) := by
    rw [le_div_iff₀ hs]; linarith [hx.2]
  have hlo0 : (0 : ℝ) ≤ (d.lo : ℝ) / ((S40 : ℤ) : ℝ) := div_nonneg (by exact_mod_cast h0) hs.le
  have hhi1 : (d.hi : ℝ) / ((S40 : ℤ) : ℝ) ≤ 1 := (div_le_one hs).mpr (by exact_mod_cast h1)
  have hx0 : 0 ≤ x := le_trans hlo0 hxl
  have hx1 : x ≤ 1 := le_trans hxh hhi1
  have m1 : Reflection.biasE ((d.hi : ℝ) / ((S40 : ℤ) : ℝ)) ≤ Reflection.biasE x :=
    Reflection.biasE_antitone ⟨hx0, hx1⟩ ⟨le_trans hx0 hxh, hhi1⟩ hxh
  have m2 : Reflection.biasE x ≤ Reflection.biasE ((d.lo : ℝ) / ((S40 : ℤ) : ℝ)) :=
    Reflection.biasE_antitone ⟨hlo0, le_trans hxl hx1⟩ ⟨hx0, hx1⟩ hxl
  have k1 := mul_le_mul_of_nonneg_left m1 hs.le
  have k2 := mul_le_mul_of_nonneg_left m2 hs.le
  constructor
  · show ((wh.output.lo : ℤ) : ℝ) ≤ ((S40 : ℤ) : ℝ) * Reflection.biasE x
    linarith [eh.1]
  · show ((S40 : ℤ) : ℝ) * Reflection.biasE x ≤ ((wl.output.hi : ℤ) : ℝ)
    linarith [el.2]

theorem contact_sound {Y cI : DI} {wl wh : EntropyWitness} (hok : contactOk Y cI wl wh = true)
    {y : ℝ} (hy : Y.Contains y) : cI.Contains (Reflection.regularContact y) := by
  simp only [contactOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hY0, hc0⟩, hord⟩, hc1⟩, hpl⟩, hph⟩, hlo⟩, hhi⟩ := hok
  have hs := scale_pos'
  have el := point_entropy hpl
  have eh := point_entropy hph
  have hlo' : (cI.lo : ℝ) * ((S40 : ℤ) : ℝ) ≤ (Y.lo : ℝ) * (wl.output.lo : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (Y.hi : ℝ) * (wh.output.hi : ℝ) ≤ (cI.hi : ℝ) * ((S40 : ℤ) : ℝ) := by
    exact_mod_cast hhi
  have hY0' : (0 : ℝ) ≤ Y.lo := by exact_mod_cast hY0
  have hYh0 : (0 : ℝ) ≤ Y.hi := by
    have h1 := hy.1
    have h2 := hy.2
    linarith
  apply DyadicInterval.contains_toReal_iff.mp
  apply RegularContactBounds.contact_contains (Y := Y.toReal) (DyadicInterval.contains_toReal_iff.mpr hy)
  · show (0 : ℝ) ≤ (Y.lo : ℝ) / ((S40 : ℤ) : ℝ)
    exact div_nonneg hY0' hs.le
  · show (0 : ℝ) ≤ (cI.lo : ℝ) / ((S40 : ℤ) : ℝ)
    exact div_nonneg (by exact_mod_cast hc0) hs.le
  · show (cI.hi : ℝ) / ((S40 : ℤ) : ℝ) ≤ 1
    exact (div_le_one hs).mpr (by exact_mod_cast hc1)
  · show (cI.lo : ℝ) / ((S40 : ℤ) : ℝ) ≤ (cI.hi : ℝ) / ((S40 : ℤ) : ℝ)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hord) hs.le
  · show (cI.lo : ℝ) / ((S40 : ℤ) : ℝ) ≤
      (Y.lo : ℝ) / ((S40 : ℤ) : ℝ) * Reflection.biasE ((cI.lo : ℝ) / ((S40 : ℤ) : ℝ))
    have k := mul_le_mul_of_nonneg_left el.1 hY0'
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs]
    have k2 : (cI.lo : ℝ) * ((S40 : ℤ) : ℝ) ≤
        ((Y.lo : ℝ) * Reflection.biasE ((cI.lo : ℝ) / ((S40 : ℤ) : ℝ))) * ((S40 : ℤ) : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right k2 hs
  · show (Y.hi : ℝ) / ((S40 : ℤ) : ℝ) * Reflection.biasE ((cI.hi : ℝ) / ((S40 : ℤ) : ℝ)) ≤
      (cI.hi : ℝ) / ((S40 : ℤ) : ℝ)
    have k := mul_le_mul_of_nonneg_left eh.2 hYh0
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hs]
    have k2 : ((Y.hi : ℝ) * Reflection.biasE ((cI.hi : ℝ) / ((S40 : ℤ) : ℝ))) * ((S40 : ℤ) : ℝ) ≤
        (cI.hi : ℝ) * ((S40 : ℤ) : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right k2 hs

theorem secI_contains {C Ec Bc A L E : DI} {c a e : ℝ}
    (hC : C.Contains c) (hEc : Ec.Contains (Reflection.biasE c))
    (hBc : Bc.Contains (Reflection.biasB c)) (hA : A.Contains a)
    (hL : L.Contains (Real.log ((1 + a) / (1 - a)) / 2)) (hE : E.Contains e)
    (hok : secOk C Bc A E = true) :
    (secI C Ec Bc A L E).Contains (Reflection.biasS c a e) := by
  simp only [secOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hc2 := DyadicInterval.mul_sound hC hC
  have hgap : (gapI C).Contains (1 - c * c) := DyadicInterval.sub_sound one_contains hc2
  have ht := DyadicInterval.add_sound hEc (DyadicInterval.mul_sound hC hL)
  have hnum : (secNum C Ec Bc L).Contains (Reflection.biasE c *
      (Reflection.biasB c + Reflection.biasB c - c * c) *
      ((Reflection.biasE c + c * (Real.log ((1 + a) / (1 - a)) / 2)) *
        (Reflection.biasE c + c * (Real.log ((1 + a) / (1 - a)) / 2)))) :=
    DyadicInterval.mul_sound (DyadicInterval.mul_sound hEc
      (DyadicInterval.sub_sound (DyadicInterval.add_sound hBc hBc) hc2))
      (DyadicInterval.mul_sound ht ht)
  have hden : (secDen C Bc E).Contains ((e + e) * ((1 - c * c) * (1 - c * c)) *
      (Reflection.biasB c * (Reflection.biasB c * Reflection.biasB c))) :=
    DyadicInterval.mul_sound (DyadicInterval.mul_sound (DyadicInterval.add_sound hE hE)
      (DyadicInterval.mul_sound hgap hgap))
      (DyadicInterval.mul_sound hBc (DyadicInterval.mul_sound hBc hBc))
  have hden2 : (secDen2 C Bc A).Contains ((1 - a * a) * (1 - c * c) * Reflection.biasB c) :=
    DyadicInterval.mul_sound (DyadicInterval.mul_sound
      (DyadicInterval.sub_sound one_contains (DyadicInterval.mul_sound hA hA)) hgap) hBc
  have h := DyadicInterval.add_sound
    (DyadicInterval.mul_sound hnum (DyadicInterval.recip_sound hok.1 hden))
    (DyadicInterval.mul_sound hc2 (DyadicInterval.recip_sound hok.2 hden2))
  have e1 : 2 * e * (1 - c * c) ^ 2 * Reflection.biasB c ^ 3 =
      (e + e) * ((1 - c * c) * (1 - c * c)) *
        (Reflection.biasB c * (Reflection.biasB c * Reflection.biasB c)) := by ring
  have e2 : Reflection.biasE c * (2 * Reflection.biasB c - c * c) *
      (Reflection.biasE c + c * (Real.log ((1 + a) / (1 - a)) / 2)) ^ 2 =
      Reflection.biasE c * (Reflection.biasB c + Reflection.biasB c - c * c) *
        ((Reflection.biasE c + c * (Real.log ((1 + a) / (1 - a)) / 2)) *
          (Reflection.biasE c + c * (Real.log ((1 + a) / (1 - a)) / 2))) := by ring
  have key : Reflection.biasS c a e =
      Reflection.biasE c * (Reflection.biasB c + Reflection.biasB c - c * c) *
        ((Reflection.biasE c + c * (Real.log ((1 + a) / (1 - a)) / 2)) *
          (Reflection.biasE c + c * (Real.log ((1 + a) / (1 - a)) / 2))) *
        ((e + e) * ((1 - c * c) * (1 - c * c)) *
          (Reflection.biasB c * (Reflection.biasB c * Reflection.biasB c)))⁻¹ +
      c * c * ((1 - a * a) * (1 - c * c) * Reflection.biasB c)⁻¹ := by
    unfold Reflection.biasS
    rw [e1, e2]
    all_goals simp only [div_eq_mul_inv]
  rw [key]
  exact h

theorem ecellOk_sound (c : ECell) (h : ecellOk c = true) {a z : ℝ}
    (ha1 : (c.al : ℝ) ≤ a) (ha2 : a ≤ (c.au : ℝ)) (hz1 : (c.zl : ℝ) ≤ z) (hz2 : z ≤ (c.zu : ℝ))
    (hz : z < 1) : 0 < Reflection.curvature a (a * z) := by
  simp only [ecellOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hbox, hent⟩, hcon⟩, hfin⟩ := h
  simp only [boxE, Bool.and_eq_true, decide_eq_true_eq] at hbox
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hal, halu⟩, hau⟩, hzl⟩, hzlu⟩, hzu⟩, hA1⟩, hA2⟩, hZ1⟩, hZ2⟩ := hbox
  simp only [entE, Bool.and_eq_true, decide_eq_true_eq] at hent
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hA0, hAS⟩, hB0⟩, hBS⟩, hpAl⟩, hpAh⟩, hpBl⟩, hpBh⟩, hEpos⟩ := hent
  simp only [conE, Bool.and_eq_true] at hcon
  obtain ⟨⟨⟨⟨⟨hcm, hcp⟩, hbm⟩, hbp⟩, hlpw⟩, hlmw⟩ := hcon
  simp only [finE, Bool.and_eq_true, decide_eq_true_eq] at hfin
  obtain ⟨⟨⟨homa, hsm⟩, hsp⟩, hNpos⟩ := hfin
  -- the point
  have hal' : (0 : ℝ) < c.al := by exact_mod_cast hal
  have hau' : (c.au : ℝ) < 1 := by exact_mod_cast hau
  have hzl' : (0 : ℝ) < c.zl := by exact_mod_cast hzl
  have ha0 : 0 < a := lt_of_lt_of_le hal' ha1
  have ha1' : a < 1 := lt_of_le_of_lt ha2 hau'
  have hz0 : 0 < z := lt_of_lt_of_le hzl' hz1
  have hA : c.A.Contains a := contains_of_memQ hA1 hA2 ha1 ha2
  have hZ : c.Z.Contains z := contains_of_memQ hZ1 hZ2 hz1 hz2
  have hB : c.B.Contains (a * z) := DyadicInterval.mul_sound hA hZ
  -- entropies and mean entropy
  have hEa : c.EA.Contains (Reflection.biasE a) := emono_contains hpAl hpAh hA0 hAS hA
  have hEb : c.EB.Contains (Reflection.biasE (a * z)) := emono_contains hpBl hpBh hB0 hBS hB
  set e : ℝ := (Reflection.biasE a + Reflection.biasE (a * z)) / 2 with he_def
  have hE : c.E.Contains e := by
    have h0 := DyadicInterval.mul_sound (DyadicInterval.add_sound hEa hEb)
      (DyadicEntropy.half_contains 40)
    rw [he_def, div_eq_mul_inv]
    exact h0
  have he0 : 0 < e := pos_of_contains hEpos hE
  have hEi : c.E.recip.Contains e⁻¹ := DyadicInterval.recip_sound hEpos hE
  -- contact arguments
  have hRM : c.RM.Contains (a * (1 - z) / 2 / e) := by
    have h0 := DyadicInterval.mul_sound (DyadicInterval.mul_sound
      (DyadicInterval.mul_sound hA (DyadicInterval.sub_sound one_contains hZ))
      (DyadicEntropy.half_contains 40)) hEi
    simp only [div_eq_mul_inv]
    exact h0
  have hRP : c.RP.Contains (a * (1 + z) / 2 / e) := by
    have h0 := DyadicInterval.mul_sound (DyadicInterval.mul_sound
      (DyadicInterval.mul_sound hA (DyadicInterval.add_sound one_contains hZ))
      (DyadicEntropy.half_contains 40)) hEi
    simp only [div_eq_mul_inv]
    exact h0
  set cmv : ℝ := Reflection.regularContact (a * (1 - z) / 2 / e) with hcmv
  set cpv : ℝ := Reflection.regularContact (a * (1 + z) / 2 / e) with hcpv
  have hCm : c.cm.Contains cmv := contact_sound hcm hRM
  have hCp : c.cp.Contains cpv := contact_sound hcp hRP
  -- contact-side enclosures
  have hcmok := hcm
  have hcpok := hcp
  simp only [contactOk, Bool.and_eq_true, decide_eq_true_eq] at hcmok hcpok
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hcm0⟩, _⟩, hcm1⟩, hcmL⟩, hcmH⟩, _⟩, _⟩ := hcmok
  obtain ⟨⟨⟨⟨⟨⟨⟨_, hcp0⟩, _⟩, hcp1⟩, hcpL⟩, hcpH⟩, _⟩, _⟩ := hcpok
  have hEcm : (emono c.ecmL c.ecmH).Contains (Reflection.biasE cmv) :=
    emono_contains hcmL hcmH hcm0 hcm1 hCm
  have hEcp : (emono c.ecpL c.ecpH).Contains (Reflection.biasE cpv) :=
    emono_contains hcpL hcpH hcp0 hcp1 hCp
  have hBcm : c.bcm.output.Contains (Reflection.biasB cmv) := BWitness.sound hbm hCm
  have hBcp : c.bcp.output.Contains (Reflection.biasB cpv) := BWitness.sound hbp hCp
  -- artanh
  have hlp : c.lp.Contains (Real.log (1 + a)) :=
    LogWitness.sound hlpw (1 + a) (DyadicInterval.add_sound one_contains hA)
  have hlm : c.lm.Contains (Real.log (1 - a)) :=
    LogWitness.sound hlmw (1 - a) (DyadicInterval.sub_sound one_contains hA)
  have hL : c.L.Contains (Real.log ((1 + a) / (1 - a)) / 2) := by
    rw [Real.log_div (by linarith) (by linarith), div_eq_mul_inv]
    exact DyadicInterval.mul_sound (DyadicInterval.sub_sound hlp hlm)
      (DyadicEntropy.half_contains 40)
  -- secants and base
  have hSM : c.SM.Contains (Reflection.biasS cmv a e) :=
    secI_contains hCm hEcm hBcm hA hL hE hsm
  have hSP : c.SP.Contains (Reflection.biasS cpv a e) :=
    secI_contains hCp hEcp hBcp hA hL hE hsp
  have hOma : (one.sub (c.A.mul c.A)).Contains (1 - a * a) :=
    DyadicInterval.sub_sound one_contains (DyadicInterval.mul_sound hA hA)
  have hbase : c.base.Contains (2 * a * (a * z) * ((1 - a * a) * (1 - a * a))⁻¹) :=
    DyadicInterval.mul_sound (DyadicInterval.mul_sound (DyadicInterval.mul_sound two_contains hA) hB)
      (DyadicInterval.recip_sound homa (DyadicInterval.mul_sound hOma hOma))
  have hN : c.N.Contains (2 * a * (a * z) * ((1 - a * a) * (1 - a * a))⁻¹ +
      Reflection.biasS cmv a e - Reflection.biasS cpv a e) :=
    DyadicInterval.sub_sound (DyadicInterval.add_sound hbase hSM) hSP
  have hnum := pos_of_contains hNpos hN
  -- the regular normalized value
  have hval : 0 < RegularReflectionExpression.normalizedValue a z := by
    have hsq : (1 - a ^ 2) ^ 2 = (1 - a * a) * (1 - a * a) := by ring
    have hnum' : 0 < 2 * a * (a * z) / (1 - a ^ 2) ^ 2 + Reflection.biasS cmv a e -
        Reflection.biasS cpv a e := by
      rw [hsq, div_eq_mul_inv]
      exact hnum
    have hden : 0 < a ^ 3 * (a * z) := by positivity
    simp only [RegularReflectionExpression.normalizedValue]
    exact div_pos hnum' hden
  exact Reflection.curvature_pos_of_regular_normalizedValue_pos ha0 ha1' hz0 hz hval

end CKLaneC2R.Endpoint

end


