-- Prove2me | Definitions.Def_DetDLP_S8K_ECAddArithmetic
-- name    : DetDLP_S8K_ECAddArithmetic
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:30:04.67628+00:00
-- url     : https://prove2.me/theorems/22373d2c-d475-41f0-9860-2218fcb921ba
-- title:
--   Deterministic short-Weierstrass elliptic-curve addition arithmetic
-- statement:
--   Defines arithmetic certificates for the zero-inverse cases, point addition on the short Weierstrass model, and the coordinate map from an elliptic curve to that model. The certificates use uniquely determined multiply-add gate transcripts, and their outputs agree with the corresponding affine point operations.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Lemma 2.4 (pp. 9–10)

import Definitions.Def_DetDLP_S8K_ShortWeierstrassEquiv
import Definitions.Def_DetDLP_S8H_ECPointArithmetic

set_option autoImplicit false
namespace DetDLP.S8K.ECAddArithmetic
open S8H.ECPointArithmetic WeierstrassCurve WeierstrassCurve.Affine
variable {p : ℕ} [Fact p.Prime]
abbrev Coords (p : ℕ) := Bool × ZMod p × ZMod p
abbrev swCoords {E : WeierstrassCurve (ZMod p)} (P : E.toAffine.Point) := coords P
abbrev ZeroInvCert (p : ℕ) := Bool × ZMod p × ZMod p × Cert p
def zeroInvOK (u : ZMod p) (z : ZeroInvCert p) :=
  gate u z.2.1 0 z.2.2.1 z.2.2.2 ∧ (if z.1 then u = 0 ∧ z.2.1 = 0 else z.2.2.1 = 1)

theorem zeroInv_sound (mul : w3_modMulInterface) (u : ZMod p) {z : ZeroInvCert p}
    (h : zeroInvOK u z) : z.1 = decide (u = 0) ∧ z.2.1 = u⁻¹ := by
  obtain ⟨b,v,m,c⟩ := z
  obtain ⟨hg,hb⟩ := h
  have hm := gate_sound mul hg
  cases b <;> simp_all only [Bool.false_eq_true, if_false, if_true, add_zero]
  · have hu : u ≠ 0 := by intro e; simp_all
    exact ⟨by simp [hu], by apply mul_left_cancel₀ hu; simp_all⟩
  · simp_all

theorem zeroInv_unique (mul : w3_modMulInterface) (u : ZMod p) : ∃! z, zeroInvOK u z := by
  obtain ⟨c,hc,uc⟩ := gate_unique mul u u⁻¹ 0
  refine ⟨(decide (u = 0),u⁻¹,u*u⁻¹+0,c),⟨hc,?_⟩,?_⟩
  · by_cases h : u = 0 <;> simp [h]
  · rintro ⟨b,v,m,d⟩ hd
    obtain ⟨rfl,rfl⟩ := (zeroInv_sound mul u hd : b = _ ∧ v = _)
    obtain rfl : m = u*u⁻¹+0 := gate_sound mul hd.1
    rw [uc d hd.1]

/-- A block separates replay on actual wires from its field-valued specification. -/
structure Block (C A : Type) where
  ok : C → Prop
  read : C → A
  value : A
  unique : w3_modMulInterface → ∃! c, ok c
  sound : ∀ (_mul : w3_modMulInterface) c, ok c → read c = value

private def wire (a x b : ZMod p) : Block (Run p) (ZMod p) :=
  ⟨validRun (a,x,b), Prod.fst, a*x+b, fun m => run_unique m _, fun m _ h => gate_sound m h⟩
private def invWire (u : ZMod p) : Block (ZeroInvCert p) (Bool × ZMod p) :=
  ⟨zeroInvOK u, fun z => (z.1,z.2.1), (decide (u=0),u⁻¹), fun m => zeroInv_unique m u,
   fun m _ h => Prod.ext (zeroInv_sound m u h).1 (zeroInv_sound m u h).2⟩
private def done {A : Type} (v : A) : Block Unit A :=
  ⟨fun _ => True, fun _ => v, v, fun _ => ⟨(),trivial,fun _ _ => rfl⟩, fun _ _ _ => rfl⟩
private def seqB {C D A B : Type} (s : Block C A) (k : A → Block D B) : Block (C × D) B where
  ok c := s.ok c.1 ∧ (k (s.read c.1)).ok c.2
  read c := (k (s.read c.1)).read c.2
  value := (k s.value).value
  unique m := by
    obtain ⟨a,ha,ua⟩ := s.unique m
    obtain ⟨b,hb,ub⟩ := (k (s.read a)).unique m
    refine ⟨(a,b),⟨ha,hb⟩,?_⟩
    rintro ⟨c,d⟩ ⟨hc,hd⟩; obtain rfl := ua c hc; exact Prod.ext rfl (ub d hd)
  sound m c h := ((k _).sound m c.2 h.2).trans (congrArg (fun a => (k a).value) (s.sound m _ h.1))
private theorem seq_value {C D A B : Type} (s : Block C A) (k : A → Block D B) :
    (seqB s k).value = (k s.value).value := rfl
private theorem wire_value (a x b : ZMod p) : (wire a x b).value = a*x+b := rfl
private theorem inv_value (u : ZMod p) : (invWire u).value = (decide (u=0),u⁻¹) := rfl
private theorem done_value {A : Type} (v : A) : (done v).value = v := rfl
private def accepts {C A : Type} (s : Block C A) (out : A) (c : C) := s.ok c ∧ out = s.read c
private theorem complete {C A : Type} (s : Block C A) (m : w3_modMulInterface) : ∃! c, accepts s s.value c := by
  obtain ⟨c,h,u⟩ := s.unique m; exact ⟨c,⟨h,(s.sound m _ h).symm⟩,fun d hd => u d hd.1⟩
private theorem correct {C A : Type} (s : Block C A) (m : w3_modMulInterface) {o c} (h : accepts s o c) :
    o = s.value := h.2.trans (s.sound m c h.1)

variable (E : WeierstrassCurve (ZMod p))
private def addition (P Q : Coords p) :=
  let (i,x,y) := P; let (j,z,w) := Q
  seqB (wire (-1) x z) fun ux => seqB (invWire ux) fun bx =>
  seqB (wire 1 y w) fun uy => seqB (invWire uy) fun by' =>
  seqB (wire (-1) y w) fun dy => seqB (wire dy bx.2 0) fun chord =>
  seqB (wire x x 0) fun sq => seqB (wire 3 sq (-27 * E.c₄)) fun num =>
  seqB (wire num by'.2 0) fun tangent =>
  let l := if !i && !j && !bx.1 then chord else if !i && !j && bx.1 && !by'.1 then tangent else 0
  seqB (wire l l 0) fun lsq => seqB (wire (-1) x lsq) fun tx => seqB (wire (-1) z tx) fun X =>
  seqB (wire (-1) X x) fun dx => seqB (wire l dx 0) fun ty => seqB (wire (-1) y ty) fun Y =>
  done (if i then Q else if j then (false,x,y) else if bx.1 && by'.1 then (true,0,0) else (false,X,Y))

abbrev AddCert (p : ℕ) := Run p × ZeroInvCert p × Run p × ZeroInvCert p × Run p × Run p × Run p × Run p × Run p × Run p × Run p × Run p × Run p × Run p × Run p × Unit
def swAddOK (P Q out : Coords p) (c : AddCert p) := accepts (addition E P Q) out c
private abbrev W := (SWEquiv.short E).toAffine
private theorem addition_value (P Q : (W E).Point) :
    (addition E (coords P) (coords Q)).value = coords (P+Q) := by
  cases P with
  | zero => cases Q <;> rfl
  | some x y hp =>
    cases Q with
    | zero => rfl
    | some z w hq =>
      have neg (a b : ZMod p) : (W E).negY a b = -b := by simp [W, SWEquiv.short, toAffine, negY]
      by_cases hx : x = z
      · subst z
        by_cases hy : y = (W E).negY x w
        · rw [Point.add_of_Y_eq rfl hy]; rw [neg] at hy; subst y
          simp [addition, coords, seq_value, wire_value, inv_value, done_value]
        · obtain rfl := Y_eq_of_Y_ne hp.1 hq.1 rfl hy
          have hn : y+y ≠ 0 := fun h => hy (by rw [neg]; exact eq_neg_of_add_eq_zero_left h)
          rw [Point.add_some (fun h => hy h.2)]
          simp only [coords, slope_of_Y_ne rfl hy]
          simp [addition, seq_value, wire_value, inv_value, done_value, hn,
            W, SWEquiv.short, toAffine, addX, addY, negAddY, negY, div_eq_mul_inv] <;> constructor <;> ring
      · have hn : -x+z ≠ 0 := by intro h; apply hx; linear_combination -h
        rw [Point.add_some (fun h => hx h.1)]
        have sl : (W E).slope x z y w = (-y+w) * (-x+z)⁻¹ := by
          rw [slope_of_X_ne hx, ← neg_div_neg_eq, div_eq_mul_inv]; congr 1 <;> first | ring | congr 1 <;> ring
        simp only [coords, sl]
        simp [addition, seq_value, wire_value, inv_value, done_value, hn, W, SWEquiv.short, toAffine,
          addX, addY, negAddY, negY] <;> constructor <;> ring

theorem swAdd_unique (mul : w3_modMulInterface) (P Q : (SWEquiv.short E).toAffine.Point) :
    ∃! c, swAddOK E (swCoords P) (swCoords Q) (swCoords (P+Q)) c := by
  change ∃! c, accepts (addition E (coords P) (coords Q)) (coords (P+Q)) c
  rw [← addition_value E]; exact complete _ mul
theorem swAdd_sound (mul : w3_modMulInterface) (P Q : (SWEquiv.short E).toAffine.Point) (out : Coords p) (c : AddCert p)
    (h : swAddOK E (swCoords P) (swCoords Q) out c) : out = swCoords (P+Q) :=
  (correct _ mul h).trans (addition_value E P Q)

private def convertPoint (P : Coords p) :=
  let (i,x,y) := P
  seqB (wire 36 x (3*E.b₂)) fun X => seqB (wire E.a₁ x E.a₃) fun t =>
  seqB (wire 2 y t) fun u => seqB (wire 108 u 0) fun Y => done (if i then (true,0,0) else (false,X,Y))
abbrev MapCert (p : ℕ) := Run p × Run p × Run p × Run p × Unit
def ecToSWOK (P out : Coords p) (c : MapCert p) := accepts (convertPoint E P) out c
variable [E.IsElliptic] (hp : 3 < p)
private theorem convert_value (P : E.toAffine.Point) : (convertPoint E (coords P)).value =
    coords (SWEquiv.equiv E (SWEquiv.six_ne_zero hp) P) := by
  change _ = coords (SWEquiv.point E (SWEquiv.six_ne_zero hp) P)
  cases P <;> simp [coords, convertPoint, seqB, wire, done, SWEquiv.point, SWEquiv.X, SWEquiv.Y, add_assoc]
theorem ecToSW_unique (mul : w3_modMulInterface) (P : E.toAffine.Point) :
    ∃! c, ecToSWOK E (coords P) (swCoords (SWEquiv.equiv E (SWEquiv.six_ne_zero hp) P)) c := by
  change ∃! c, accepts (convertPoint E (coords P)) (coords (SWEquiv.equiv E (SWEquiv.six_ne_zero hp) P)) c
  rw [← convert_value E hp]; exact complete _ mul
theorem ecToSW_sound (mul : w3_modMulInterface) (P : E.toAffine.Point) (out : Coords p) (c : MapCert p)
    (h : ecToSWOK E (coords P) out c) : out = swCoords (SWEquiv.equiv E (SWEquiv.six_ne_zero hp) P) :=
  (correct _ mul h).trans (convert_value E hp P)
end DetDLP.S8K.ECAddArithmetic


