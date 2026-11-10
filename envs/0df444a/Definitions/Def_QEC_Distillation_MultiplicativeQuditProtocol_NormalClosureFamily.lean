-- Prove2me | Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
-- name    : QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:34:31.013238+00:00
-- url     : https://prove2.me/theorems/928b5afb-f274-4000-9387-d1f34d922e5e
-- title:
--   Normal Closure Family
-- statement:
--   Definitions and structural lemmas for Normal Closure Family, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/NormalClosureFamily.lean

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureDistance
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
set_option autoImplicit false
noncomputable section
namespace QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Coding.AlgebraicGeometry.F256GarciaStichtenoth Semantics
open Ngu24MultiplicativeCCZ
open Filter
open scoped BigOperators Topology
section Native
local instance _p2m_local_instance_a61e848631_24 {J : Type} [Fintype J] : Fintype (Word F256 J) := Fintype.ofFinite _
def f256QuditLength (i : ℕ) : ℕ :=
  f256GarciaStichtenothLength i - f256MultiplicationLogicalCount i
def f256QuditDistanceBound (i : ℕ) : ℕ :=
  (f256GarciaStichtenothLength i + 4) / 5 - f256MultiplicationLogicalCount i
def f256QuditEncodedCode (i : ℕ) :
    EncodedCode (ComputationalBasisRegister F256 (Fin (f256MultiplicationLogicalCount i)))
      (ComputationalBasisRegister F256 (f256SourceInput i).PivotComplement) :=
  (f256SourceInput i).encodedCode
end Native
local instance _p2m_local_instance_a61e848631_111 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
local instance _p2m_local_instance_a61e848631_112 : CharP F256 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F256).injective 2
end QEC.Distillation.Ngu24MultiplicativeCSS


