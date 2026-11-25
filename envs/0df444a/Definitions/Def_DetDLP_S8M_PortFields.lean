-- Prove2me | Definitions.Def_DetDLP_S8M_PortFields
-- name    : DetDLP_S8M_PortFields
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:19:42.386625+00:00
-- url     : https://prove2.me/theorems/60252d77-160b-52bd-922a-d49e1eb89430
-- title:
--   Tag 6 port field decoding
-- statement:
--   Proves that the encoded curve coefficients, point coordinates, and target fields agree with the Tag 6 semantics.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_Semantics
import Definitions.Def_DetDLP_S8H4_ElemDecoder
import Definitions.Def_DetDLP_S8M_PortPoly
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
namespace DetDLP.S8M.PortEval
open PortPoly S8H0 Groundwork M89S1 DetDLP_W1_Queries
variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (T : ℕ) (S : ECSeed p m) (X : E.toAffine.Point) (η : List Bool)
local notation "w" => ECPair.word E T S X η
include E T X η in
theorem coeff_eq : coeff w = GateSemantics.coeff E := by
  simp [coeff,ECPair.word,queryWord,second,encodeCurveInput,w5_M6Sort.decode_encode,GateSemantics.coeff]
include E T S X η in
omit E T S X η in
private theorem subVal (a b : ZMod p) : (a.val+p-b.val)%p = (a-b).val := by
  rw [←ZMod.val_natCast]; congr 1; rw [Nat.cast_sub (by have := b.val_lt; omega),Nat.cast_add]; simp
include E T S X η in
omit E T S X η in
private theorem negVal (a : ZMod p) : (p-a.val)%p = (-a).val := by simpa using subVal (a:=(0 : ZMod p)) (b:=a)
include E T S X η in
theorem bTwo_eq : bTwo w = E.b₂.val := by
  have hp : prime w = p := (ECPair.Packet.fields E T S X η).1
  rw [bTwo,coeff_eq,hp,←ZMod.val_natCast]; congr 1; simp [GateSemantics.coeff,WeierstrassCurve.b₂,pow_two]
include E T S X η in
theorem cTerm_eq : cTerm w = (-27*E.c₄).val := by
  have hp : prime w = p := (ECPair.Packet.fields E T S X η).1
  have hsq : E.b₂.val*E.b₂.val%p = (E.b₂^2).val := by rw [←ZMod.val_natCast]; simp [pow_two]
  have h4 : (24*(2*E.a₄.val+E.a₁.val*E.a₃.val))%p = (24*E.b₄).val := by rw [←ZMod.val_natCast]; simp [WeierstrassCurve.b₄]
  have h27 : 27*E.c₄.val%p = (27*E.c₄).val := by rw [←ZMod.val_natCast]; simp
  have hc : (E.b₂ ^ 2 - 24*E.b₄ : ZMod p) = E.c₄ := by simp [WeierstrassCurve.c₄]
  have hcv : ((E.b₂ ^ 2).val+p-(24*E.b₄).val)%p = E.c₄.val := by
    have hh := congrArg ZMod.val hc
    rw [←subVal (E.b₂^2) (24*E.b₄)] at hh
    exact hh
  simp only [cTerm,coeff_eq,bTwo_eq,hp,GateSemantics.coeff,hsq,h4,hcv,h27]; rw [negVal (27*E.c₄),neg_mul]
include E T η in
theorem coord_eq (i : Fin m) (k : Fin 4) : coord (List.ofFn (ecBits S)) (bitLen p) (i.val*4+k.val) = ecWords S i k := by
  have h := S8H4.ElemDecoder.seedEntry_eq E T S i η k
  obtain ⟨hp,_,hs,hi,_,_⟩ := S8H4.ElemDecoder.fields E T S i η
  change m89_enum_words.coord _ _ _ = _
  simpa only [S8H4.ElemDecoder.seedEntry,S8H4.ElemDecoder.width,hp,hs,hi,S8G.FpMoment.Code.width_eq] using h
variable [E.IsElliptic]
theorem target_eq (hp : 3<p) : let t := pointCoords X
    (decide (t.getD 0 0 = 1), (if t.getD 0 0 = 1 then 0 else (36*t.getD 1 0+3*E.b₂.val)%p), (if t.getD 0 0 = 1 then 0 else (108*(2*t.getD 2 0+E.a₁.val*t.getD 1 0+E.a₃.val))%p)) = Semantics.target E hp X := by
  cases X with
  | zero => exact (Semantics.target_zero E hp).symm
  | some x y h =>
    change (false,(36*x.val+3*E.b₂.val)%p,(108*(2*y.val+E.a₁.val*x.val+E.a₃.val))%p) = (false,(S8K.SWEquiv.X E x).val,(S8K.SWEquiv.Y E x y).val)
    rw [←ZMod.val_natCast,←ZMod.val_natCast]; simp [S8K.SWEquiv.X,S8K.SWEquiv.Y]
end DetDLP.S8M.PortEval


