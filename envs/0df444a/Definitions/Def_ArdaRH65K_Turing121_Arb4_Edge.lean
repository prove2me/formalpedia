-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
-- name    : ArdaRH65K_Turing121_Arb4_Edge
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:13:16.177574+00:00
-- url     : https://prove2.me/theorems/59e4080c-4910-4acb-93ae-ce248281999f
-- title:
--   Arb4 Edge certificate definitions
-- statement:
--   This bundle defines the horizontal-edge certificate and its finite rational checks. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{Arb4.eqB},\;\mathtt{Arb4.inRad},\;\mathtt{Arb4.cornerOK},\;\mathtt{Arb4.boxOK}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Arb4_Edge.lean

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
/-  Arb4_Edge.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per horizontal edge.

    `ArgHoriz.hAH_of_octCert_boxes` (brick K6c) reduces `argChangeHoriz ζ T 2 (-1) ∈ [Lo, Hi]` to an
    octant certificate (breakpoints `2 = x 0 > … > x m = -1`, labels, no crossing on every piece),
    two endpoint point enclosures with their corner slopes, and two final inequalities with `π` and
    `arctan`.  The generated edge modules `H1000Edge_*` prove these by `norm_num` per piece and per
    edge.  Here the WHOLE edge is one Boolean `edgeOK`, run by ONE `decide +kernel`:

      * `EdgeD`         -- the certificate data of an edge: height `t = tn / 2^tq`, EM cut `N`, log
                           bound `L`, breakpoints `x`, pieces `pc` (`Arb4_Side.PieceD`), endpoint
                           boxes (`ArbEcon.Off.checkG` data), corner slopes, the final `[Lo, Hi]`;
      * `boxOK`, `boxOK_sound` -- an endpoint enclosure (evaluator run at the piece center, recomputed)
                           and its four corner conditions;
      * `atanLoQ atanHiQ piL piH`, `finalLo_sound`, `finalHi_sound` -- the two final inequalities
                           (`3.141592 < π < 3.141593`, `ArgHoriz.atanLo_le`, `ArgHoriz.le_atanHi`);
      * `edgeOK`, `edgeOK_sound` -- THE EDGE: `edgeOK E = true` gives
                           `argChangeHoriz riemannZeta (tn / 2^tq) 2 (-1) ∈ [Lo, Hi]`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  One edge of a finite
    zero count; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. Small Boolean helpers -/

/-- `a = b` as rationals (both inequalities). -/
def eqB (a b : Q) : Bool := le a b && le b a



/-- `|x - σ| ≤ r`. -/
def inRad (x : Q) (P : PieceD) : Bool := le (qabs (sub x P.σQ)) P.rQ



/-! ## B. The evaluator invariants of a piece center -/



/-! ## C. Endpoint enclosures and their corner slopes -/

/-- One corner `(a, b)` of an endpoint box in octant `(α, β)`: `X = α a + β b > 0` and
    `qlo X ≤ Y ≤ qhi X` for `Y = α b - β a`. -/
def cornerOK (al be : ℤ) (a b qlo qhi : Q) : Bool :=
  lt (ofInt 0) (add (mul (ofInt al) a) (mul (ofInt be) b)) &&
    le (mul qlo (add (mul (ofInt al) a) (mul (ofInt be) b))) (sub (mul (ofInt al) b) (mul (ofInt be) a)) &&
    le (sub (mul (ofInt al) b) (mul (ofInt be) a)) (mul qhi (add (mul (ofInt al) a) (mul (ofInt be) b)))



/-- An endpoint enclosure at the center of piece `P` (the evaluator run recomputed): the point box
    `[reLo, reHi] × [imLo, imHi] / D` by `ArbEcon.Off.checkG`, and its four corners in the octant of
    `P` with slopes in `[qlo, qhi]`. -/
noncomputable def boxOK (tn tq N : ℕ) (P : PieceD) (D : ℕ) (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (qlo qhi : Q) : Bool :=
  let c := ArbEcon.OrderK.cfg64 tn tq
  let s1 := ArbEcon.Off.runO c P.oc (N - 2) (ArbEcon.Off.StO.init c 5)
  let sN := ArbEcon.Off.runO c P.oc 1 s1
  Nat.ble 2 N && Nat.ble 1 P.q && Nat.ble 1 D && !s1.acc.isEmpty && !sN.acc.isEmpty &&
    ArbEcon.Off.checkG c P.oc 6 N (s1.acc.headD ArbEcon.Off.Acc.zero)
      (sN.acc.headD ArbEcon.Off.Acc.zero) D reLo reHi imLo imHi Qp Rn Rd &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reLo D) (frac imLo D) qlo qhi &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reLo D) (frac imHi D) qlo qhi &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reHi D) (frac imLo D) qlo qhi &&
    cornerOK (ArgHoriz.octA P.kk) (ArgHoriz.octB P.kk) (frac reHi D) (frac imHi D) qlo qhi



/-! ## D. The two final inequalities -/

/-- Rational lower bound of `arctan q` (`ArgHoriz.atanLo`). -/
def atanLoQ (q : Q) : Q := if 0 ≤ q.n then sub q (div (npow q 3) (ofNat 3)) else q

/-- Rational upper bound of `arctan q` (`ArgHoriz.atanHi`). -/
def atanHiQ (q : Q) : Q := if 0 ≤ q.n then q else sub q (div (npow q 3) (ofNat 3))







/-- The `π` bound that makes `dk · π` smallest (`3.141592 < π < 3.141593`). -/
def piL (dk : ℤ) : Q := if 0 ≤ dk then frac 3141592 1000000 else frac 3141593 1000000

/-- The `π` bound that makes `dk · π` largest. -/
def piH (dk : ℤ) : Q := if 0 ≤ dk then frac 3141593 1000000 else frac 3141592 1000000





/-- `Lo ≤ dk π/4 + atanLo qlo1 - atanHi qhi0` with `π` replaced by its safe rational bound. -/
def finalLoOK (dk : ℤ) (qhi0 qlo1 Lo : Q) : Bool :=
  le Lo (sub (add (div (mul (ofInt dk) (piL dk)) (ofNat 4)) (atanLoQ qlo1)) (atanHiQ qhi0))

/-- `dk π/4 + atanHi qhi1 - atanLo qlo0 ≤ Hi` with `π` replaced by its safe rational bound. -/
def finalHiOK (dk : ℤ) (qlo0 qhi1 Hi : Q) : Bool :=
  le (sub (add (div (mul (ofInt dk) (piH dk)) (ofNat 4)) (atanHiQ qhi1)) (atanLoQ qlo0)) Hi





/-! ## E. THE EDGE -/

/-- The certificate data of one horizontal edge `[2, -1] + i t`, `t = tn / 2^tq`. -/
structure EdgeD where
  tn : ℕ
  tq : ℕ
  /-- EM cut and log bound `L ≥ log N` of every piece -/
  N : ℕ
  L : Q
  /-- `m` pieces; piece `j` (`pc j`) covers `[x (j+1), x j]`; `x 0 = 2`, `x m = -1` -/
  m : ℕ
  x : ℕ → Q
  pc : ℕ → PieceD
  /-- the endpoint box at `x = 2` (center of piece 0) and its corner slopes -/
  D0 : ℕ
  reLo0 : ℤ
  reHi0 : ℤ
  imLo0 : ℤ
  imHi0 : ℤ
  Qp0 : ℕ
  Rn0 : ℕ
  Rd0 : ℕ
  qlo0 : Q
  qhi0 : Q
  /-- the endpoint box at `x = -1` (center of piece `m - 1`) and its corner slopes -/
  D1 : ℕ
  reLo1 : ℤ
  reHi1 : ℤ
  imLo1 : ℤ
  imHi1 : ℤ
  Qp1 : ℕ
  Rn1 : ℕ
  Rd1 : ℕ
  qlo1 : Q
  qhi1 : Q
  /-- the certified enclosure of the argument change -/
  Lo : Q
  Hi : Q

namespace EdgeD

/-- The height `t = tn / 2^tq`. -/
noncomputable def T (E : EdgeD) : ℝ := (E.tn : ℝ) / 2 ^ E.tq

/-- The octant certificate of the edge. -/
noncomputable def cert (E : EdgeD) : ArgHoriz.OctCert := ⟨E.m, fun j => (E.x j).val, fun j => (E.pc j).kk⟩

end EdgeD

/-- **The edge checker**: every piece (`pieceOK`, with both breakpoints inside its radius), the
    label steps, the two endpoint boxes with their corners, and the final enclosure. -/
noncomputable def edgeOK (E : EdgeD) : Bool :=
  Nat.ble 1 E.m && Nat.ble 1 E.tn && eqB (E.x 0) (ofNat 2) && eqB (E.x E.m) (ofInt (-1)) &&
    (List.range E.m).all (fun j => pieceOK E.tn E.tq E.N E.L (E.pc j) &&
      inRad (E.x j) (E.pc j) && inRad (E.x (j + 1)) (E.pc j)) &&
    (List.range (E.m - 1)).all (fun j => decide (|(E.pc (j + 1)).kk - (E.pc j).kk| ≤ 3)) &&
    eqB (E.pc 0).σQ (ofNat 2) && eqB (E.pc (E.m - 1)).σQ (ofInt (-1)) &&
    boxOK E.tn E.tq E.N (E.pc 0) E.D0 E.reLo0 E.reHi0 E.imLo0 E.imHi0 E.Qp0 E.Rn0 E.Rd0 E.qlo0 E.qhi0 &&
    boxOK E.tn E.tq E.N (E.pc (E.m - 1)) E.D1 E.reLo1 E.reHi1 E.imLo1 E.imHi1 E.Qp1 E.Rn1 E.Rd1
      E.qlo1 E.qhi1 &&
    finalLoOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qhi0 E.qlo1 E.Lo &&
    finalHiOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qlo0 E.qhi1 E.Hi



end Arb4


def ArdaRH65K_Turing121_Arb4_Edge : Nat := 0


