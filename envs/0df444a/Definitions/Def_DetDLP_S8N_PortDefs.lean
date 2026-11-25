-- Prove2me | Definitions.Def_DetDLP_S8N_PortDefs
-- name    : DetDLP_S8N_PortDefs
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T04:46:26.880621+00:00
-- url     : https://prove2.me/theorems/4f65c678-45c4-45f4-823d-40bf3af703a8

import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8M_PortDefs
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace DetDLP.S8N.PortPoly
open Groundwork S8H0 S8H.PortCombinators RegisterMap DetDLP_W1_Queries
open DetDLP.S8M.PortPoly (bit tab tile rd hash atomFixed mapG addStepG prime coeff bTwo cTerm width slots prefixG)

def idx (w : List Bool) := PolyT.bval (third w)
def threshold (w : List Bool) := PolyT.bval (third (more w))
def prefixBits (w : List Bool) := third (more (more w))

def seedSlotG (d p : ℕ) : GC :=
  catG (rangeG d (p - 1)) (catG (rangeG d p) (addG (d + 1) false (regR d) (pinR 1) (regR d)))

def ecSeedG (m b d p : ℕ) (η : List Bool) : GC :=
  catG (tile m (catG (seedSlotG d p) (seedSlotG d p))) (prefixG (m * 4 * b) η)

def atomSlotG (q : List Unit) (d p T : ℕ) (c : GateRoutes.Coeff) : GC :=
  catG (atomFixed q d p T c)
    (d, fun _ w => decide (bit w 1 = (if bit w 0 then bit w 5 else bit w 3) ∧
      bit w 2 = (if bit w 0 then bit w 6 else bit w 4)))

def targetG (d p : ℕ) : GC :=
  catG (rangeG d p) (catG (rangeG d p)
    (d, fun _ r => decide (!bit r 0 || (bit r 1 = false ∧ bit r 2 = false))))

def foldChainG (n d : ℕ) (g : GC) : GC :=
  let eqr (len : ℕ) : GC := (len, fun _ h => decide (bit h 0 = bit h 1))
  catG (eqr 1) (catG (eqr d) (catG (eqr d) (tile n g)))

def anchorCount (c o m d e : ℕ) : ℕ :=
  m * (16 * d + 6) +
    (c * (m * (122 * d + 14 * e + 46)) +
      o * ((6 * d + 3) + (2 * m * (70 * d + 8 * e + 27) + 2 * ((m - 1) * (253 * d + 30 * e + 97))))) + 1

def tree (q : List Unit) (b m p T c o e b2 c4 : ℕ) (cf : GateRoutes.Coeff) (η : List Bool) : GC :=
  let d := b + 1
  let prod := catG (targetG d p)
    (catG (tile (2 * m) (mapG q d p b2 cf.a1 cf.a3))
      (tile 2 (foldChainG (m - 1) d (addStepG q d p c4))))
  catG (anchorsG (anchorCount c o m d e))
    (catG zeroLastG
      (catG (ecSeedG m b d p η)
        (catG (tile c (tile m (atomSlotG q d p T cf))) (tile o prod))))

def decoded (w : List Bool) : GC :=
  let p := prime w; let b := width p; let d := b + 1; let m := slots b; let j := idx w
  let cf := coeff w
  tree (CoreCheck.pad p) b m p (threshold w) (min j 2) (if j = 3 then 1 else 0)
    (S8H.PointAddresses.wires d) (bTwo w) (cTerm w) cf (prefixBits w)

def port : List Bool → List Bool := fullPort decoded

end DetDLP.S8N.PortPoly


