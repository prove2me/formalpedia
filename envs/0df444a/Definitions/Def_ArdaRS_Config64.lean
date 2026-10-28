-- Prove2me | Definitions.Def_ArdaRS_Config64
-- name    : ArdaRS_Config64
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T01:46:18.405926+00:00
-- url     : https://prove2.me/theorems/9c9a0ab5-ad65-4e32-a46b-53c519fdd4d8
-- title:
--   Fixed-point configuration at a dyadic height
-- statement:
--   The 64-bit fixed-point arithmetic configuration used at a height $t=n/2^q$, including the unrolled logarithm and trigonometric kernels.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde897/telperion/examples/zeta_reflection/lean/EMZetaHighCfg64.lean

/- Source: Arda, commit af4fde897, EMZetaHighCfg64.lean; Apache-2.0. -/
/-  EMZetaHighCfg64.lean -- the P = 64 Nat-only evaluator configuration of the order-(2K+1)
    Euler-Maclaurin instances (lane emhigh), as a FUNCTION of the height `t = tn / 2^tq`.

    Same evaluator as `Probes/ArbEconomics_Eval` (unchanged); the unrolled Horner (length 9) and
    log (length 7, fast path from `n = 256`) kernels are shared by every height, so an instance
    file carries only its chunk-boundary states.  Validated once for all heights by
    `EMZetaHighCheck.valid64`.  Imports only the evaluator, so chunk modules stay light.

    conjecture1_proved = False.
-/
import Definitions.Def_ArdaRS_Arithmetic

namespace ArbEcon

namespace OrderK

noncomputable section

def hc64 (w : Nat) : Nat :=
  Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (18446744073709551616)) 5644703686555122794496))) 4427218577690292387840))) 3357307421415138394112))) 2434970217729660813312))) 1660206966633859645440))) 1033017668127734890496))) 553402322211286548480))) 221360928884514619392))) 36893488147419103232)

def hs64 (w : Nat) : Nat :=
  Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (Nat.sub 18446744073709551616 (Nat.div (Nat.mul w (18446744073709551616)) 6308786473208666652672))) 5017514388048998039552))) 3873816255479005839360))) 2877692075498690052096))) 2029141848108050677760))) 1328165573307087716352))) 774763251095801167872))) 368934881474191032320))) 110680464442257309696)

def lnf64 (m : Nat) : Nat × Nat × Nat :=
  let p1 := m
  let p2 := Nat.mul p1 m
  let p3 := Nat.mul p2 m
  let p4 := Nat.mul p3 m
  let p5 := Nat.mul p4 m
  let p6 := Nat.mul p5 m
  let p7 := Nat.mul p6 m
  let p8 := Nat.mul p7 m
  (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (0) (Nat.div 18446744073709551616 (Nat.mul p1 1))) (Nat.div 18446744073709551616 (Nat.mul p2 2))) (Nat.div 18446744073709551616 (Nat.mul p3 3))) (Nat.div 18446744073709551616 (Nat.mul p4 4))) (Nat.div 18446744073709551616 (Nat.mul p5 5))) (Nat.div 18446744073709551616 (Nat.mul p6 6))) (Nat.div 18446744073709551616 (Nat.mul p7 7)), 7, p8)

/-- The P = 64 evaluator configuration at height `t = tn / 2^tq` (Horner length 9, log fast path
    of length 7 and two-step Newton square root from `n = 256` on). -/
def cfg64 (tn tq : Nat) : Cfg :=
  ⟨64, 18446744073709551616, 36893488147419103232, 340282366920938463463374607431768211456, tn, tq,
   28976077832308491369, 14488038916154245684, 2, 14987979559889010688, 1,
   [5644703686555122794496, 4427218577690292387840, 3357307421415138394112, 2434970217729660813312,
    1660206966633859645440, 1033017668127734890496, 553402322211286548480, 221360928884514619392,
    36893488147419103232],
   [6308786473208666652672, 5017514388048998039552, 3873816255479005839360, 2877692075498690052096,
    2029141848108050677760, 1328165573307087716352, 774763251095801167872, 368934881474191032320,
    110680464442257309696], hc64, hs64, 65, 256, 7, lnf64, 12, 256⟩

end

end OrderK

end ArbEcon

def ArdaRS_Config64 : Nat := 0


