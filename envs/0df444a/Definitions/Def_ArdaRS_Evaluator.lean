-- Prove2me | Definitions.Def_ArdaRS_Evaluator
-- name    : ArdaRS_Evaluator
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:46:41.971368+00:00
-- url     : https://prove2.me/theorems/deaf6e21-ee42-419a-be9d-13723d8b1e03
-- title:
--   Riemann–Siegel interval evaluator
-- statement:
--   A finite integer certificate and Boolean checks for an interval evaluation of the Riemann–Siegel main term at a dyadic height. The Boolean checks are computational definitions; their soundness is separate.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS4_Eval.lean

/- Source: Arda, commit af4fde897, RS4_Eval.lean; Apache-2.0. -/
/-  RS4_Eval.lean -- lane B4: the kernel-decidable interval evaluator for the Riemann-Siegel
    main term (computable side only; soundness is `RS4_Sound`).

    ## What is evaluated

    For a height `t = tn / 2^tq` (the `t` of an `ArbEcon.Cfg`, precision `P`, `o = 2^P`) the checker
    `RS4.check c z` decides, in the kernel, a list of integer inequalities about a certificate `z`
    (candidate brackets emitted by an UNTRUSTED pipeline) and then assembles a dyadic box (`DIntv`,
    exponent `-2P`) for the Riemann-Siegel main term

        Zmain t phi = 2 sum_{n <= N} n^(-1/2) cos(phi - t log n)
                        + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p),

    `N = floor a`, `p = a - N`, `a = sqrt(t/2pi)`, `Psi(p) = cos(2pi(p^2-p-1/16)) / cos(2pi p)`,
    simultaneously for EVERY phase `phi` with `|phi - thetaMain t| <= 1/t` (the ball delivered by
    `RSDesignTheta.theta_sub_thetaMain` and used in `RSInt.rs_Z_C0`).

    ## Reused machinery (nothing duplicated)

      * `ArbEcon.run` / `ArbEcon.St.init` (Probes/ArbEconomics_Eval): the Nat-only Dirichlet loop.
        After `N - 1` steps its state encloses `psum t N = sum_{n<=N} n^(-1/2 - it)` (Re and Im
        signed balls) AND `log N` (the log bracket it carries for the phase reduction).
      * `ArbEcon.trig`: cos/sin balls of an angle given by a Nat bracket (pi/2 reduction + Horner).
        It is applied to the whole phase ball at once (its radius absorbs the bracket width), to
        `2 pi p` and to `2 pi (p - p^2 + 1/16)`.
      * `DIntvProd.DIntv` `mul` / `add` / `sub` / `neg` (DIntvDef, DIntvCorrect): the final assembly.

    ## The certificate (all candidates are RE-VERIFIED here; nothing is trusted)

      A0 A1   : A0 <= a o <= A1            (checked by squaring against t / (4 (pi/2)))
      N       : N o < A0, A1 < (N+1) o     (so N = floor a and p > 0)
      Y0 Y1   : Y0 <= (p/N) o <= Y1        (y = p / N, a = N (1 + y))
      LG0 LG1 : LG0 <= log(1+y) o <= LG1   (degree-8 alternating log series, exact integer check,
                                             tail 2 y^9 from Mathlib's `abs_log_sub_add_sum_range_le`)
      TH0 TH1 : TH0 <= phi o <= TH1 for every phi in the ball (thetaMain = t log a - t/2 - pi/8,
                                             log a = log N + log(1+y), log N from the Dirichlet state)
      Q0 Q1   : Q0 <= a^(-1/2) o <= Q1     (= (t/2pi)^(-1/4))
      U0 U1   : bracket of 2 pi p o;  V0 V1 : bracket of 2 pi (p - p^2 + 1/16) o
      F0 F1   : F0 <= Psi(p) o <= F1       (quotient check against the two cos balls; requires the
                                             cos(2 pi p) ball to exclude 0 -- FAILURE otherwise)
      zlo zhi : the claimed output box, exponent -2P (checked to contain the assembled box)

    conjecture1_proved = False.  Finite interval arithmetic at one height; nothing about RH.
-/
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_DyadicOps

namespace RS4

open ArbEcon DIntvProd

noncomputable section

/-- The certificate for one height (emitted untrusted, verified by `Checks`). -/
structure Cert where
  N : Nat
  A0 : Nat
  A1 : Nat
  Y0 : Nat
  Y1 : Nat
  LG0 : Nat
  LG1 : Nat
  TH0 : Nat
  TH1 : Nat
  Q0 : Nat
  Q1 : Nat
  U0 : Nat
  U1 : Nat
  V0 : Nat
  V1 : Nat
  F0 : Int
  F1 : Int
  zlo : Int
  zhi : Int

/-- Positive part of `840 o^9 L(Y/o)`, `L(y) = y - y^2/2 + ... - y^8/8`. -/
def lpPos (Y o : Nat) : Nat :=
  840 * Y * o ^ 8 + 280 * Y ^ 3 * o ^ 6 + 168 * Y ^ 5 * o ^ 4 + 120 * Y ^ 7 * o ^ 2

/-- Negative part of `840 o^9 L(Y/o)`. -/
def lpNeg (Y o : Nat) : Nat :=
  420 * Y ^ 2 * o ^ 7 + 210 * Y ^ 4 * o ^ 5 + 140 * Y ^ 6 * o ^ 3 + 105 * Y ^ 8 * o

/-- Signed integer `sgn b * m`. -/
def sgnI (b : Bool) (m : Nat) : Int := if b then (m : Int) else -(m : Int)

/-- The DIntv of a signed ball `|x o - m| <= r` (exponent `-P`). -/
def ballD (P : Nat) (m : Int) (r : Nat) : DIntv := ⟨m - r, m + r, -(P : Int)⟩

/-- Conditional negation (keeps the exponent syntactically). -/
def negIf (b : Bool) (I : DIntv) : DIntv :=
  ⟨if b then I.lo else -I.hi, if b then I.hi else -I.lo, I.e⟩

/-- The Dirichlet state after `N` terms. -/
def dstate (c : Cfg) (z : Cert) : St := run c (z.N - 1) (St.init c)

/-- The cos/sin balls of the phase ball. -/
def phTrig (c : Cfg) (z : Cert) : Trig := trig c z.TH0 z.TH1

/-- The main-sum box `2 (cos phi Re S - sin phi Im S)`, exponent `-2P`. -/
def mainBox (c : Cfg) (z : Cert) : DIntv :=
  let s := dstate c z
  let tr := phTrig c z
  let reS := ballD c.P ((s.reP : Int) - s.reN) s.reR
  let imS := ballD c.P ((s.imP : Int) - s.imN) s.imR
  let cph := ballD c.P (sgnI tr.cs tr.cm) tr.cr
  let sph := ballD c.P (sgnI tr.ss tr.sm) tr.sr
  let m1 := DIntv.sub (DIntv.mul cph reS) (DIntv.mul sph imS) rfl
  DIntv.add m1 m1 rfl

/-- The C0 box `(-1)^(N+1) a^(-1/2) Psi(p)`, exponent `-2P`. -/
def c0Box (c : Cfg) (z : Cert) : DIntv :=
  negIf (z.N % 2 == 1) (DIntv.mul ⟨z.Q0, z.Q1, -(c.P : Int)⟩ ⟨z.F0, z.F1, -(c.P : Int)⟩)

/-- The assembled box for `Zmain`, exponent `-2P`. -/
def zBox (c : Cfg) (z : Cert) : DIntv := DIntv.add (mainBox c z) (c0Box c z) rfl

/-- The quotient condition `F0 <= X / Yd * o <= F1` for `X in [Nm -+ rN]`, `Yd in [D -+ rD]`,
    with the denominator ball sign-definite (this is where `|cos 2 pi p|` is bounded below). -/
def QuotOK (o : Nat) (Nm : Int) (rN : Nat) (D : Int) (rD : Nat) (F0 F1 : Int) : Prop :=
  ((rD : Int) < D ∧
    F0 * (D - rD) ≤ (Nm - rN) * o ∧ F0 * (D + rD) ≤ (Nm - rN) * o ∧
    (Nm + rN) * o ≤ F1 * (D - rD) ∧ (Nm + rN) * o ≤ F1 * (D + rD)) ∨
  (D + rD < 0 ∧
    (Nm + rN) * o ≤ F0 * (D - rD) ∧ (Nm + rN) * o ≤ F0 * (D + rD) ∧
    F1 * (D - rD) ≤ (Nm - rN) * o ∧ F1 * (D + rD) ≤ (Nm - rN) * o)

instance (o : Nat) (Nm : Int) (rN : Nat) (D : Int) (rD : Nat) (F0 F1 : Int) :
    Decidable (QuotOK o Nm rN D rD F0 F1) := by unfold QuotOK; infer_instance

/-- **All the kernel checks.**  Every conjunct is an integer inequality. -/
structure Checks (c : Cfg) (z : Cert) : Prop where
  hN : 1 ≤ z.N
  ht : 10000 * 2 ^ c.tq ≤ c.tn
  hrp : c.rp ≤ c.hp
  hA0 : z.A0 * z.A0 * 2 ^ c.tq * 4 * (c.hp + c.rp) ≤ c.tn * (c.one * c.one * c.one)
  hA1 : c.tn * (c.one * c.one * c.one) ≤ z.A1 * z.A1 * 2 ^ c.tq * 4 * (c.hp - c.rp)
  hNlo : z.N * c.one < z.A0
  hNhi : z.A1 < (z.N + 1) * c.one
  hY0 : z.Y0 * z.N ≤ z.A0 - z.N * c.one
  hY1 : z.A1 - z.N * c.one ≤ z.Y1 * z.N
  hYhalf : 2 * z.Y1 ≤ c.one
  hLG0 : z.LG0 * 840 * c.one ^ 8 + 1680 * z.Y0 ^ 9 + lpNeg z.Y0 c.one ≤ lpPos z.Y0 c.one
  hLG1 : lpPos z.Y1 c.one + 1680 * z.Y1 ^ 9 ≤ z.LG1 * 840 * c.one ^ 8 + lpNeg z.Y1 c.one
  hTH0 : z.TH0 * (4 * c.tn * 2 ^ c.tq) + 2 * c.tn * c.tn * c.one + c.tn * 2 ^ c.tq * (c.hp + c.rp)
      + 4 * c.one * 2 ^ c.tq * 2 ^ c.tq ≤ 4 * c.tn * c.tn * ((dstate c z).llo + z.LG0)
  hTH1 : 4 * c.tn * c.tn * ((dstate c z).lhi + z.LG1) + 4 * c.one * 2 ^ c.tq * 2 ^ c.tq
      ≤ z.TH1 * (4 * c.tn * 2 ^ c.tq) + 2 * c.tn * c.tn * c.one + c.tn * 2 ^ c.tq * (c.hp - c.rp)
  hQ0 : z.Q0 * z.Q0 * z.A1 ≤ c.one * c.one * c.one
  hQ1 : c.one * c.one * c.one ≤ z.Q1 * z.Q1 * z.A0
  hU0 : z.U0 * c.one ≤ 4 * (c.hp - c.rp) * (z.A0 - z.N * c.one)
  hU1 : 4 * (c.hp + c.rp) * (z.A1 - z.N * c.one) ≤ z.U1 * c.one
  hG0 : 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one)
      ≤ 16 * (z.A0 - z.N * c.one) * c.one + c.one * c.one
  hV0 : z.V0 * (4 * c.one * c.one) ≤ (c.hp - c.rp) * (16 * (z.A0 - z.N * c.one) * c.one
      + c.one * c.one - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one))
  hV1 : (c.hp + c.rp) * (16 * (z.A1 - z.N * c.one) * c.one + c.one * c.one)
      ≤ z.V1 * (4 * c.one * c.one) + (c.hp + c.rp) * (16 * (z.A0 - z.N * c.one) * (z.A0 - z.N * c.one))
  hPsi : QuotOK c.one (sgnI (trig c z.V0 z.V1).cs (trig c z.V0 z.V1).cm) (trig c z.V0 z.V1).cr
      (sgnI (trig c z.U0 z.U1).cs (trig c z.U0 z.U1).cm) (trig c z.U0 z.U1).cr z.F0 z.F1
  hzlo : z.zlo ≤ (zBox c z).lo
  hzhi : (zBox c z).hi ≤ z.zhi

/-- The checks as one conjunction (the decidable form). -/
def ChecksP (c : Cfg) (z : Cert) : Prop :=
    1 ≤ z.N ∧ 10000 * 2 ^ c.tq ≤ c.tn ∧ c.rp ≤ c.hp ∧
      z.A0 * z.A0 * 2 ^ c.tq * 4 * (c.hp + c.rp) ≤ c.tn * (c.one * c.one * c.one) ∧
      c.tn * (c.one * c.one * c.one) ≤ z.A1 * z.A1 * 2 ^ c.tq * 4 * (c.hp - c.rp) ∧
      z.N * c.one < z.A0 ∧ z.A1 < (z.N + 1) * c.one ∧
      z.Y0 * z.N ≤ z.A0 - z.N * c.one ∧ z.A1 - z.N * c.one ≤ z.Y1 * z.N ∧ 2 * z.Y1 ≤ c.one ∧
      z.LG0 * 840 * c.one ^ 8 + 1680 * z.Y0 ^ 9 + lpNeg z.Y0 c.one ≤ lpPos z.Y0 c.one ∧
      lpPos z.Y1 c.one + 1680 * z.Y1 ^ 9 ≤ z.LG1 * 840 * c.one ^ 8 + lpNeg z.Y1 c.one ∧
      z.TH0 * (4 * c.tn * 2 ^ c.tq) + 2 * c.tn * c.tn * c.one + c.tn * 2 ^ c.tq * (c.hp + c.rp)
        + 4 * c.one * 2 ^ c.tq * 2 ^ c.tq ≤ 4 * c.tn * c.tn * ((dstate c z).llo + z.LG0) ∧
      4 * c.tn * c.tn * ((dstate c z).lhi + z.LG1) + 4 * c.one * 2 ^ c.tq * 2 ^ c.tq
        ≤ z.TH1 * (4 * c.tn * 2 ^ c.tq) + 2 * c.tn * c.tn * c.one + c.tn * 2 ^ c.tq * (c.hp - c.rp) ∧
      z.Q0 * z.Q0 * z.A1 ≤ c.one * c.one * c.one ∧ c.one * c.one * c.one ≤ z.Q1 * z.Q1 * z.A0 ∧
      z.U0 * c.one ≤ 4 * (c.hp - c.rp) * (z.A0 - z.N * c.one) ∧
      4 * (c.hp + c.rp) * (z.A1 - z.N * c.one) ≤ z.U1 * c.one ∧
      16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one)
        ≤ 16 * (z.A0 - z.N * c.one) * c.one + c.one * c.one ∧
      z.V0 * (4 * c.one * c.one) ≤ (c.hp - c.rp) * (16 * (z.A0 - z.N * c.one) * c.one
        + c.one * c.one - 16 * (z.A1 - z.N * c.one) * (z.A1 - z.N * c.one)) ∧
      (c.hp + c.rp) * (16 * (z.A1 - z.N * c.one) * c.one + c.one * c.one)
        ≤ z.V1 * (4 * c.one * c.one) + (c.hp + c.rp) * (16 * (z.A0 - z.N * c.one) * (z.A0 - z.N * c.one)) ∧
      QuotOK c.one (sgnI (trig c z.V0 z.V1).cs (trig c z.V0 z.V1).cm) (trig c z.V0 z.V1).cr
        (sgnI (trig c z.U0 z.U1).cs (trig c z.U0 z.U1).cm) (trig c z.U0 z.U1).cr z.F0 z.F1 ∧
      z.zlo ≤ (zBox c z).lo ∧ (zBox c z).hi ≤ z.zhi

instance (c : Cfg) (z : Cert) : Decidable (ChecksP c z) := by unfold ChecksP; infer_instance



/-- **The kernel checker.**  `check c z = true` is what an instance proves by `decide +kernel`. -/
def check (c : Cfg) (z : Cert) : Bool := decide (ChecksP c z)

end

end RS4

def ArdaRS_Evaluator : Nat := 0


