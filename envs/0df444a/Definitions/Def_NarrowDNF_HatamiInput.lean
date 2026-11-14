-- Prove2me | Definitions.Def_NarrowDNF_HatamiInput
-- name    : NarrowDNF_HatamiInput
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:41.900244+00:00
-- url     : https://prove2.me/theorems/71e0b674-2bfe-489c-9cde-f5485e2a8399
-- title:
--   The local activation family that never fires
-- statement:
--   For a coordinate type $\iota$, the empty activation family assigns the false predicate to every finite index set $T$ and every Boolean input $x$:
--   $$J_T(x)=\mathrm{false}.$$
--   Its locality condition holds because changing the input cannot change this value. No coordinate set fires, including the empty set, so the associated active union is empty on every input. This is an explicit object of the same activation type used by the nontrivial Fourier construction, rather than an assumed approximation theorem.
--
--   The construction supplies the activation-family choice used in the zero-influence branch of the quantitative argument. The required approximation, measurability, arity, and load conclusions for that branch are separate propositions and proofs.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiInput.lean#L96-L99

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive

namespace NarrowDNF.HatamiInput
end NarrowDNF.HatamiInput


/-!
# Hatami's quantitative activation input

Assembly of the actual Fourier truncation, the reconstructed Bourgain estimate,
the repaired adaptive residual proof, and threshold decoding for Lemma 2.1.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.HatamiInput
variable {ι : Type*} [Fintype ι] [DecidableEq ι]











/-- The empty activation family used for the zero-influence case. -/
def emptyActivation : Activation ι where
  fires _ _ := False
  locality _ _ _ _ := Iff.rfl



















end NarrowDNF.HatamiInput


