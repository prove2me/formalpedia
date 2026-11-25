-- Prove2me | Definitions.Def_DetDLP_S8M_FoldModel
-- name    : DetDLP_S8M_FoldModel
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T23:43:19.010618+00:00
-- url     : https://prove2.me/theorems/2f5b2421-6ec6-4a97-a52e-086c119b4792
-- title:
--   EC pair accumulator fold model
-- statement:
--   Fits the short-Weierstrass addition steps, fold and prefix blocks, and proves the anchored copy-cycle code models the semantic elliptic-curve pair-query layout.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_AtomMapModel_v2
import Definitions.Def_DetDLP_S8M_Semantics

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8M.FoldModel

open S8H0.RegisterMap S8H0.NamedBlocks S8H0.GateRoutes
open S8H.PointAddresses (Models)
open S8H0.HashRows (Word)
open DetDLP.S8M.Routes DetDLP.S8M.MakePacket
open DetDLP.S8N.ECAddRoutes

variable {m d e : ℕ}

/-- A single short-Weierstrass addition step uses the canonical routed
register-name model. The edge-count parameter remains abstract. -/
theorem step_spec (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (flag0 : Ref (Routes.bank m d e)) (x0 y0 : Word (Routes.bank m d e))
    (flag1 : Ref (Routes.bank m d e)) (x1 y1 : Word (Routes.bank m d e))
    (path : Path (addShape d e) (Routes.bank m d e)) :
    Fits (addStepN hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path)
      (addBlock hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path) := by
  exact addStepN_Fits hd p neg1 three c4 flag0 x0 y0 flag1 x1 y1 path

/-- The `(2*m-1)` addition blocks and their final equality rows are fitted by
the canonical model for the complete accumulator fold. -/
theorem fold_spec (hd : 1 ≤ d) (hm : 1 ≤ m)
    (p neg1 three c4 : ℕ) (t : Routes.Target) :
    Fits (foldN hd hm p neg1 three c4 t)
      (foldRows hd hm p neg1 three c4 t) := by
  exact foldN_Fits hd hm p neg1 three c4 t

/-- Prefix constraints are represented by a canonical code/name model. -/
theorem prefix_spec (b : ℕ) (η : List Bool) :
    Fits (codeOf (Routes.prefixRows (m := m) (d := d) (e := e) b η))
      (Routes.prefixRows (m := m) (d := d) (e := e) b η) := by
  exact codeOf_spec _

variable (hd : 1 ≤ d) (hm : 1 ≤ m) (p T : ℕ) (c : Coeff)
  (S : Routes.SeedData m) (b2 neg1 three c4 : ℕ) (η : List Bool)

/-- The assembled atom, conversion, fold, and prefix network has a fitting
model. Its component register arithmetic is parameterized by abstract `d` and
`e`, rather than by an unfolded graph edge-count expression. -/
theorem base_spec (t : Routes.Target) :
    Fits (MakePacket.base hd hm p T c S b2 neg1 three c4 η t)
      (Routes.networkAt hd hm p T c S b2 neg1 three c4 η t) := by
  exact MakePacket.base_Fits hd hm p T c S b2 neg1 three c4 η t

end DetDLP.S8M.FoldModel

namespace DetDLP.S8M.FoldModel

open S8H0.RegisterMap S8H0.NamedBlocks S8H0.GateRoutes
open S8H.PointAddresses (Models)
open DetDLP.S8M.MakePacket

/-- The anchored copy-cycle code for the semantic EC-pair layout models that
layout. Names are taken from the same canonical net model used by the packet
builder. -/
theorem cycle_spec {p m T : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hp : 3 < p) (hm : 1 ≤ m) (S : ECSeed p m) (hT : T ≤ p)
    (X : E.toAffine.Point) (η : List Bool) :
    Models
      (DetDLP.S8H0.CycleCode.code
        (DetDLP.S8H0.AnchoredLayout.withAnchors ((Semantics.shape p m).size + 1)
          (MakePacket.codeOf (Semantics.net E hp hm S X η T)).1)
        (DetDLP.S8H0.AnchoredLayout.signalNat ((Semantics.shape p m).size + 1)
          (MakePacket.codeOf (Semantics.net E hp hm S X η T)).2))
      (Semantics.layout E hp hm S X η T) := by
  let b := Semantics.net E hp hm S X η T
  let k := (Semantics.shape p m).size + 1
  have h := MakePacket.codeOf_spec b
  change Models (DetDLP.S8H0.AnchoredLayout.code k (MakePacket.codeOf b).1 (MakePacket.codeOf b).2)
    (S8J.CircuitRealizes.circuit (DetDLP.S8H0.AnchoredLayout.block b.core k)
      (DetDLP.S8H0.AnchoredLayout.wiring b.core b.name))
  exact DetDLP.S8H0.AnchoredLayout.code_spec (b := b.core) (k := k) (name := b.name)
    h.1 (MakePacket.codeOf b).2 h.2

end DetDLP.S8M.FoldModel


