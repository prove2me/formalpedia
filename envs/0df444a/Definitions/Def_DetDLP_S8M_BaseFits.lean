-- Prove2me | Definitions.Def_DetDLP_S8M_BaseFits
-- name    : DetDLP_S8M_BaseFits
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T03:21:38.376383+00:00
-- url     : https://prove2.me/theorems/9a662939-6f7e-5f3e-86ba-2b603d860bef
-- title:
--   Fitting code for EC pair routed base network
-- statement:
--   Fitting lemmas for the routed fold, prefix, assembled base network and anchored cycle semantics.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8M_FoldModel
import Definitions.Def_DetDLP_S8M_StepFits

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace DetDLP.S8M.BaseFits

open S8H0.RegisterMap S8H0.GateRoutes S8H.PointAddresses
open DetDLP.S8M.Routes DetDLP.S8M.MakePacket

variable {m d e : ℕ}

/-- The complete routed accumulator block is fitted by its canonical natural
code. The fold includes all `2*m-1` stage additions and its output rows. -/
theorem fold_fits (hd : 1 ≤ d) (hm : 1 ≤ m)
    (p neg1 three c4 : ℕ) (t : Routes.Target) :
    Fits (foldN hd hm p neg1 three c4 t)
      (foldRows hd hm p neg1 three c4 t) := by
  exact DetDLP.S8M.FoldModel.fold_spec hd hm p neg1 three c4 t

/-- Prefix rows are fitted by their canonical flattened code. -/
theorem prefix_fits (b : ℕ) (η : List Bool) :
    Fits (codeOf (Routes.prefixRows (m := m) (d := d) (e := e) b η))
      (Routes.prefixRows (m := m) (d := d) (e := e) b η) := by
  exact codeOf_spec _

variable (hd : 1 ≤ d) (hm : 1 ≤ m) (p T : ℕ) (c : S8H0.GateRoutes.Coeff)
  (S : Routes.SeedData m) (b2 neg1 three c4 : ℕ) (η : List Bool)

/-- The joined network of atom constraints, conversion constraints, fold, and
prefix fits the canonical natural-address model. The bank edge dimension stays
abstract. -/
theorem base_fits (t : Routes.Target) :
    Fits (MakePacket.base hd hm p T c S b2 neg1 three c4 η t)
      (Routes.networkAt hd hm p T c S b2 neg1 three c4 η t) := by
  exact DetDLP.S8M.FoldModel.base_spec hd hm p T c S b2 neg1 three c4 η t

end DetDLP.S8M.BaseFits

namespace DetDLP.S8M.BaseFits

open S8H0.CycleCode S8H0.AnchoredLayout
open S8H.PointAddresses (Models)
open DetDLP.S8M.Semantics DetDLP.S8M.MakePacket

/-- The anchored copy-cycle encoding of the semantic EC-pair layout is modeled
by the canonical code/name model of its routed network. -/
theorem cycle_spec {p m T : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (hp : 3 < p) (hm : 1 ≤ m) (S : ECSeed p m) (hT : T ≤ p)
    (X : E.toAffine.Point) (η : List Bool) :
    Models
      (S8H0.CycleCode.code
        (S8H0.AnchoredLayout.withAnchors ((Semantics.shape p m).size + 1)
          (MakePacket.codeOf (Semantics.net E hp hm S X η T)).1)
        (S8H0.AnchoredLayout.signalNat ((Semantics.shape p m).size + 1)
          (MakePacket.codeOf (Semantics.net E hp hm S X η T)).2))
      (Semantics.layout E hp hm S X η T) := by
  exact DetDLP.S8M.FoldModel.cycle_spec E hp hm S hT X η

end DetDLP.S8M.BaseFits


