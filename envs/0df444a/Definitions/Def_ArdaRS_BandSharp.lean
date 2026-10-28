-- Prove2me | Definitions.Def_ArdaRS_BandSharp
-- name    : ArdaRS_BandSharp
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:47:28.592423+00:00
-- url     : https://prove2.me/theorems/5be34b8a-15e8-402a-b311-6ba1091d9c2e
-- title:
--   Sharp Riemann–Siegel sign-band predicate
-- statement:
--   A sign-band predicate for dyadic samples at height at least $4250$, using the sharper $3t^{-3/4}/5$ error margin. Its correctness is a separate theorem.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/RS5_EvalSharp.lean

/- Source: Arda, commit af4fde897, RS5_EvalSharp.lean; Apache-2.0. -/
/-  RS5_EvalSharp.lean -- lane B5, RSC0 Phase 3 (Tier 0 mechanics): the band checker with the SHARPENED
    margin (3/5) t^(-3/4) of `RSInt.rs_Z_C0'` (RS_BridgeSharp), valid from t >= 4250.  Computable side only;
    soundness is `RS5_ZSharp` / `RS5_BandSharp`.  New definitions BESIDE the old ones in `RS5_Eval`
    (imported read-only); no existing definition is changed and every committed certificate keeps its
    `RS5.bandOK` proof.

    ## The new predicates

      * `HeightOK s` : `4250 * 2^tq <= tn`, i.e. `t >= 4250`, the range of `rs_Z_C0'` (decided per sample);
      * `PosOK'` / `NegOK'` : the box clears `(3/5) E / 2^P` (was `(13/5) E / 2^P` in `PosOK` / `NegOK`):
            3 E one < 5 zlo,     5 zhi < -(3 E one);
      * `sampleOK' s` : `HeightOK s`, `check5` (the unchanged t >= 509 RS4 checker), `MarginOK` (unchanged),
        and `PosOK'` / `NegOK'` on the claimed side;
      * `bandOK'` : `bandOK` with `sampleOK'` in place of `sampleOK` (same raw `List.rec` loop, same `ltH`).

    A sample below t = 4250 is REFUSED by `HeightOK` (it must use the old `bandOK`, margin 13/5).

    conjecture1_proved = False.  Finite interval arithmetic at finitely many heights; nothing about RH.
-/
import Definitions.Def_ArdaRS_Band

namespace RS5

open ArbEcon DIntvProd RS4

noncomputable section

/-- The sharpened bound's range, decided per sample: `t = tn / 2^tq >= 4250`. -/
def HeightOK (s : Sample) : Prop := 4250 * 2 ^ s.tq ≤ s.tn

/-- `zlo / 2^(2P) > (3/5) E / 2^P`. -/
def PosOK' (c : Cfg) (z : Cert) (E : Nat) : Prop := 3 * (E : Int) * (c.one : Int) < 5 * z.zlo

/-- `zhi / 2^(2P) < -(3/5) E / 2^P`. -/
def NegOK' (c : Cfg) (z : Cert) (E : Nat) : Prop := 5 * z.zhi < -(3 * (E : Int) * (c.one : Int))

instance (s : Sample) : Decidable (HeightOK s) := by unfold HeightOK; infer_instance
instance (c : Cfg) (z : Cert) (E : Nat) : Decidable (PosOK' c z E) := by unfold PosOK'; infer_instance
instance (c : Cfg) (z : Cert) (E : Nat) : Decidable (NegOK' c z E) := by unfold NegOK'; infer_instance

/-- One sample is certified with the sharpened margin: `t >= 4250`, the t >= 509 checker accepts, the
    margin is valid, and the box clears `(3/5) E / 2^P` on the claimed side. -/
def sampleOK' (s : Sample) : Bool :=
  decide (HeightOK s) && check5 s.cfg s.z && decide (MarginOK s.cfg s.E) &&
    (if s.pos then decide (PosOK' s.cfg s.z s.E) else decide (NegOK' s.cfg s.z s.E))

/-- The band loop with `sampleOK'` (raw `List.rec`, as `bandAux`). -/
def bandAux' : List Sample → Sample → Bool :=
  List.rec (motive := fun _ => Sample → Bool) (fun s => sampleOK' s)
    (fun s' _ ih s => sampleOK' s && ltH s s' && ih s')

/-- **The band checker, sharpened margin**: every sample certified by `sampleOK'`, heights strictly
    increasing. -/
def bandOK' : List Sample → Bool
  | [] => true
  | s :: l => bandAux' l s

end

end RS5

def ArdaRS_BandSharp : Nat := 0


