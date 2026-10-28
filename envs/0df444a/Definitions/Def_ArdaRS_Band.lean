-- Prove2me | Definitions.Def_ArdaRS_Band
-- name    : ArdaRS_Band
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:47:08.967965+00:00
-- url     : https://prove2.me/theorems/f33d8686-f588-4a1a-81dc-cd9b52b1088f
-- title:
--   Dyadic Riemann–Siegel sign bands
-- statement:
--   Dyadic samples, a finite sign-band predicate, and an adjacent-sign-change count. The sample predicate uses the error budget intended for heights at least $509$.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_Eval.lean

/- Source: Arda, commit af4fde897, RS5_Eval.lean; Apache-2.0. -/
/-  RS5_Eval.lean -- lane B5: the t >= 509 variant of the RS4 kernel checker, the margin check,
    and the BAND checker over a list of dyadic sample heights (computable side only; soundness is
    `RS5_Sound`, `RS5_Z`, `RS5_Band`).

    ## Why a variant (and not an edit of RS4)

    `RS4.Checks` hard-codes the height floor `10000 * 2^tq <= tn` (it feeds `RSInt.rs_Z_C0`, t >= 10000).
    The seam bound `RSSeam.rs_Z_C0_seam` holds from t >= 509.  `RS5.Checks5` / `RS5.check5` are
    `RS4.Checks` / `RS4.check` VERBATIM with the floor `509` instead of `10000`; every computable
    ingredient (`RS4.Cert`, `RS4.zBox`, `RS4.mainBox`, `RS4.c0Box`, `RS4.QuotOK`, `RS4.lpPos`, ...) is
    REUSED from `RS4_Eval`, unchanged.  The RS4 files are not edited.

    ## The margin

    The seam remainder is `(13/5) t^(-3/4)`.  A sample carries a Nat `E`; `MarginOK c E` is the integer
    inequality `one^4 (2^tq)^3 <= E^4 tn^3`, i.e. `(E / 2^P)^4 t^3 >= 1`, i.e. `E / 2^P >= t^(-3/4)`.
    `PosOK` / `NegOK` compare the certified box against `(13/5) E / 2^P` (exact integer inequalities).

    ## The band checker

    A `Sample` is a dyadic height `t = tn / 2^tq`, a margin `E` and an RS4 certificate `z` for the P = 64
    configuration `ArbEcon.OrderK.cfg64 tn tq` (valid at every height, `ArbEcon.OrderK.valid64`).
    Its claimed sign is `pos = (0 < zlo)`.  `bandOK l` checks every sample (`sampleOK`) and that the
    heights are STRICTLY increasing; `chgBy Sample.pos l` counts adjacent sign changes.

    conjecture1_proved = False.  Finite interval arithmetic at finitely many heights; nothing about RH.
-/
import Definitions.Def_ArdaRS_Evaluator
import Definitions.Def_ArdaRS_Config64

namespace RS5

open ArbEcon DIntvProd RS4

noncomputable section

/-- **All the kernel checks** of `RS4.Checks`, VERBATIM except the height floor `509` (was `10000`).
    Every conjunct is an integer inequality. -/
structure Checks5 (c : Cfg) (z : Cert) : Prop where
  hN : 1 ≤ z.N
  ht : 509 * 2 ^ c.tq ≤ c.tn
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
def ChecksP5 (c : Cfg) (z : Cert) : Prop :=
    1 ≤ z.N ∧ 509 * 2 ^ c.tq ≤ c.tn ∧ c.rp ≤ c.hp ∧
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

instance (c : Cfg) (z : Cert) : Decidable (ChecksP5 c z) := by unfold ChecksP5; infer_instance



/-- **The t >= 509 kernel checker.**  `check5 c z = true` is what an instance proves by `decide +kernel`. -/
def check5 (c : Cfg) (z : Cert) : Bool := decide (ChecksP5 c z)

/-! ## the margin `E / 2^P >= t^(-3/4)` and the two sign conditions -/

/-- `one^4 (2^tq)^3 <= E^4 tn^3`, i.e. `E / 2^P >= t^(-3/4)` for `t = tn / 2^tq`. -/
def MarginOK (c : Cfg) (E : Nat) : Prop := c.one ^ 4 * (2 ^ c.tq) ^ 3 ≤ E ^ 4 * c.tn ^ 3

/-- `zlo / 2^(2P) > (13/5) E / 2^P`. -/
def PosOK (c : Cfg) (z : Cert) (E : Nat) : Prop := 13 * (E : Int) * (c.one : Int) < 5 * z.zlo

/-- `zhi / 2^(2P) < -(13/5) E / 2^P`. -/
def NegOK (c : Cfg) (z : Cert) (E : Nat) : Prop := 5 * z.zhi < -(13 * (E : Int) * (c.one : Int))

instance (c : Cfg) (E : Nat) : Decidable (MarginOK c E) := by unfold MarginOK; infer_instance
instance (c : Cfg) (z : Cert) (E : Nat) : Decidable (PosOK c z E) := by unfold PosOK; infer_instance
instance (c : Cfg) (z : Cert) (E : Nat) : Decidable (NegOK c z E) := by unfold NegOK; infer_instance

/-! ## samples and the band checker -/

/-- One sample height `t = tn / 2^tq` with its margin numerator `E` and its RS4 certificate. -/
structure Sample where
  tn : Nat
  tq : Nat
  E : Nat
  z : Cert

/-- The P = 64 configuration at the sample height. -/
def Sample.cfg (s : Sample) : Cfg := ArbEcon.OrderK.cfg64 s.tn s.tq

/-- The claimed sign of the sample: `true` = positive. -/
def Sample.pos (s : Sample) : Bool := decide (0 < s.z.zlo)

/-- One sample is certified: the t >= 509 checker accepts, the margin is valid, and the box clears
    `(13/5) E / 2^P` on the claimed side. -/
def sampleOK (s : Sample) : Bool :=
  check5 s.cfg s.z && decide (MarginOK s.cfg s.E) &&
    (if s.pos then decide (PosOK s.cfg s.z s.E) else decide (NegOK s.cfg s.z s.E))

/-- Strict order of dyadic heights: `tn / 2^tq < tn' / 2^tq'`. -/
def ltH (s s' : Sample) : Bool := decide (s.tn * 2 ^ s'.tq < s'.tn * 2 ^ s.tq)

/-- The band loop (raw `List.rec`, so the kernel evaluates it in one linear pass): the head sample `s`
    is certified, strictly below the next one, and so on. -/
def bandAux : List Sample → Sample → Bool :=
  List.rec (motive := fun _ => Sample → Bool) (fun s => sampleOK s)
    (fun s' _ ih s => sampleOK s && ltH s s' && ih s')

/-- **The band checker**: every sample certified, heights strictly increasing. -/
def bandOK : List Sample → Bool
  | [] => true
  | s :: l => bandAux l s

/-- Adjacent sign changes after a head `a` (raw `List.rec`). -/
def chgAux {α : Type} (sg : α → Bool) : List α → α → Nat :=
  List.rec (motive := fun _ => α → Nat) (fun _ => 0)
    (fun b _ ih a => (if sg a == sg b then 0 else 1) + ih b)

/-- Number of adjacent sign changes of `sg` along a list (generic; used with `Sample.pos`). -/
def chgBy {α : Type} (sg : α → Bool) : List α → Nat
  | [] => 0
  | a :: l => chgAux sg l a

/-- The last element of `a :: l` (generic; raw `List.rec`). -/
def lastOf {α : Type} (a : α) (l : List α) : α :=
  List.rec (motive := fun _ => α → α) (fun a => a) (fun b _ ih _ => ih b) l a

end

end RS5

def ArdaRS_Band : Nat := 0


