-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Supplement_Layering
-- name    : ParityBarrier563_Trilinear_Supplement_Layering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:39:56.326203+00:00
-- url     : https://prove2.me/theorems/a87a3bb0-70bb-4e75-a551-0289226a8899
-- title:
--   Layerings and fan-in over the published circuit DAG
-- statement:
--   A layering assigns every gate of the published circuit DAG to one of d alternating layers. Layer one reads literals and constants; later layers read previous-layer gates and constants; the output is the unique top-layer gate. Evaluation and gate count are those of the published circuit. Define
--   $$\operatorname{BottomBound}(C,\tau,k)\iff\text{each bottom gate reads at most }k\text{ live literal wires}.$$
--   The full bottom bound leaves all variables live. The top bound counts gate wires entering the output. Unary gates count as gates, constants do not count as live literals, and restrictions leave the DAG and its size intact. Repeated wires may be deleted without changing evaluation or increasing any size or fan-in bound. Either output kind is allowed.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), §2, printed pp.10–11 / PDF 12–13; Lemma 6.3 preamble, printed p.27 / PDF 29

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Circuit
import Definitions.Def_ParityBarrier563_Trilinear_Supplement_FiniteAverages

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- A layering of the published DAG: all actual gates remain counted, constants may enter
any layer, unary gates are actual gates, and the top layer consists of the output alone. -/
structure Layering {V : Type} (C : Circuit V) (d : ℕ) where
  level : Fin C.size → Fin d
  layerKind : Fin d → GateKind
  gateKind : ∀ i, C.kind i = layerKind (level i)
  alternating : ∀ i j, i.val + 1 = j.val → layerKind i ≠ layerKind j
  outputGate : Fin C.size
  output_eq : C.output = .gate outputGate
  outputLevel : (level outputGate).val + 1 = d
  top_unique : ∀ i, (level i).val + 1 = d → i = outputGate
  wires : ∀ i, ∀ a ∈ C.inputs i, match a with
    | .lit _ _ => (level i).val = 0
    | .const _ => True
    | .gate j => (level ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).val + 1 = (level i).val

/-- Fan-in counts literal wires. Under restriction, only live literals count; constants
and wires from previous gates do not. No simplifying or deleting gates takes place. -/
def BottomBound {V : Type} {C : Circuit V} {d : ℕ} (L : Layering C d)
    (τ : Restriction V) (k : ℝ) : Prop :=
  ∀ i, (L.level i).val = 0 →
    (((C.inputs i).countP (fun a => match a with
      | .lit v _ => (τ v).isNone
      | _ => false) : ℕ) : ℝ) ≤ k

/-- Unrestricted bottom fan-in bound. -/
def BottomBoundFull {V : Type} {C : Circuit V} {d : ℕ} (L : Layering C d)
    (k : ℝ) : Prop := BottomBound L (fun _ => none) k

/-- The top fan-in counts the preceding-layer gate wires read by the output. -/
def TopBound {V : Type} {C : Circuit V} {d : ℕ} (L : Layering C d) (t : ℝ) : Prop :=
  (((C.inputs L.outputGate).countP (fun a => match a with
    | .gate _ => true
    | _ => false) : ℕ) : ℝ) ≤ t

end ParityBarrier563.Trilinear.Supplement


