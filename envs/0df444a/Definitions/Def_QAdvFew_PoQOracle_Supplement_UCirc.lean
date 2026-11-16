-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_UCirc
-- name    : QAdvFew_PoQOracle_Supplement_UCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:11:50.526581+00:00
-- url     : https://prove2.me/theorems/21497f19-9d46-46d8-a563-9a29634c7b1d
-- title:
--   Unitary oracles and oracle quantum circuits
-- statement:
--   A **quantum (unitary) oracle** is a family of operators $O_{i,t}$ indexed by a component $i$ and a level $t$, each acting on $\mathrm{ar}(i,t)$ qubits; being unitary is a separate property. An **oracle quantum circuit** on $m$ wires is a list of instructions, each of which is
--
--   1. a Clifford+T gate ($H,S,T,X,\mathrm{CNOT}$) or a query to a classical oracle $f$ through $|x,z\rangle\mapsto|x,z\oplus f(x)\rangle$ (the published `OInstr`), or
--   2. a query to $O_{i,t}$ or to its inverse $O_{i,t}^\dagger$ on a list of distinct wires, possibly controlled on a further wire.
--
--   The **size** of a circuit is its description length in bits, with every field written in binary, plus $t$ for every query to level $t$; the circuit's run applies the instructions left to right to an amplitude vector.
--
--   This is the model of the paper's quantum oracle algorithms: "We allow controlled queries and queries to both a unitary and its inverse", "A query to level $t$ takes at least $t$ time", and "We measure the size of a circuit by its description length in bits".
--
--   **Formalization Note** A query to components and levels in superposition is obtained from controlled queries, one per component and level, at polynomial cost.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.1–§3.2.2, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OInstr
import Definitions.Def_QAdvFew_PoQOracle_Supplement_Layout

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- A **quantum (unitary) oracle** with arity `ar` (Goldin, Lombardi, Morimae, *Quantum Advantage
has Few Complexity Implications*, arXiv:2611.05303v1, §3.2.2, p. 12 (PDF p. 14): "A quantum oracle
is a family of unitary operators"): for each component `i` and level `t` an operator `O i t` on
`ar i t` qubits.

**Formalization Note** The operators are stored as matrices; that they are unitary is the separate
predicate `UOracle.IsUnitary`, asserted wherever an oracle is quantified existentially. Components
are indexed by `ℕ`; an oracle with finitely many components gives the others arity `0`. -/
def UOracle (ar : ℕ → ℕ → ℕ) : Type := (i t : ℕ) → Matrix (Bits (ar i t)) (Bits (ar i t)) ℂ

/-- Every operator of the oracle is unitary. -/
def UOracle.IsUnitary {ar : ℕ → ℕ → ℕ} (O : UOracle ar) : Prop :=
  ∀ i t, O i t ∈ Matrix.unitaryGroup (Bits (ar i t)) ℂ

/-- Apply the operator `M` on `k` qubits to the wires `ws` (in order) of an `m`-qubit amplitude
vector, controlled on the wire `c` when `ctrl = some c` (identity on the basis states with `c = 0`):
`(Mψ)(y) = Σ_z M(y|_ws, z) ψ(y[ws ↦ z])`. -/
noncomputable def applyOn {m k : ℕ} (M : Matrix (Bits k) (Bits k) ℂ) (ctrl : Option (Fin m))
    (ws : Fin k → Fin m) (ψ : QState m) : QState m :=
  fun y =>
    let act := ∑ z : Bits k, M (y ∘ ws) z * ψ (Function.extend ws z y)
    match ctrl with
    | none => act
    | some c => if y c then act else ψ y

/-- An instruction of an **oracle quantum circuit** with a unitary oracle of arity `ar` and a
classical oracle (§3.2.1–§3.2.2, p. 12 (PDF p. 14): "We allow controlled queries and queries to
both a unitary and its inverse"; "A classical function `f` is accessed quantumly through the map
`|x, z⟩ ↦ |x, z ⊕ f(x)⟩`"; "multiple oracles may be listed in a superscript", §3.2.3):

* `gate g` — a Clifford+T gate or a classical-oracle query (`QAdvFew.PoQOracle.OInstr`);
* `uq i t inv ctrl ws` — a query to component `i` at level `t` (its inverse if `inv`), on the
  distinct wires `ws`, controlled on the wire `c` if `ctrl = some c` (`c ∉ ws`).

**Formalization Note** "Components and levels may be queried in superposition, using zero padding"
(p. 12) is obtained from controlled queries, one per component and level, with the Toffoli gate
(exactly expressible in Clifford+T) computing the control; since a level-`t` query is charged `t`
(`UInstr.levelCost`), this costs a polynomial overhead. -/
inductive UInstr (ar : ℕ → ℕ → ℕ) (m : ℕ) where
  | gate (g : OInstr m)
  | uq (i t : ℕ) (inv : Bool) (ctrl : Option (Fin m)) (ws : Fin (ar i t) → Fin m)
      (hws : Function.Injective ws) (hc : ∀ c, ctrl = some c → ∀ j, ws j ≠ c)

namespace UInstr

variable {ar : ℕ → ℕ → ℕ} {m : ℕ}

/-- The action of an instruction, with unitary oracle `O` and classical oracle `C`; an inverse
query applies the conjugate transpose `(O i t)†`. -/
noncomputable def apply (O : UOracle ar) (C : Oracle) : UInstr ar m → QState m → QState m
  | .gate g => g.apply C
  | .uq i t inv ctrl ws _ _ => applyOn (if inv then (O i t).conjTranspose else O i t) ctrl ws

/-- The binary description of a Clifford+T gate: a tag and its wires (`bnat`). -/
def instrDesc : Instr m → Str
  | .h i => bnat 0 ++ bnat i
  | .s i => bnat 1 ++ bnat i
  | .t i => bnat 2 ++ bnat i
  | .x i => bnat 3 ++ bnat i
  | .cnot i j _ => bnat 4 ++ bnat i ++ bnat j

/-- The binary description of an instruction (§3.2.1, p. 12: "We measure the size of a circuit by
its description length in bits"): a tag, then every field in the self-delimiting binary code
`bnat`. -/
def desc : UInstr ar m → Str
  | .gate (.gate g) => instrDesc g
  | .gate (.query ws a _) =>
      bnat 5 ++ bnat ws.length ++ (ws.map (fun w => bnat (w : ℕ))).flatten ++ bnat (a : ℕ)
  | .uq i t inv ctrl ws _ _ =>
      bnat 6 ++ bnat i ++ bnat t ++ [inv] ++
        (match ctrl with
          | none => [false]
          | some c => true :: bnat (c : ℕ)) ++
        (List.ofFn (fun j => bnat (ws j : ℕ))).flatten

/-- The extra charge of an instruction: `t` for a query to level `t` (§3.2.2, p. 12: "A query to
level `t` takes at least `t` time"), `0` otherwise. -/
def levelCost : UInstr ar m → ℕ
  | .uq _ t _ _ _ _ _ => t
  | .gate _ => 0

/-- The level of a unitary-oracle query (`none` for other instructions). -/
def level? : UInstr ar m → Option ℕ
  | .uq _ t _ _ _ _ _ => some t
  | .gate _ => none

/-- The component of a unitary-oracle query (`none` for other instructions). -/
def comp? : UInstr ar m → Option ℕ
  | .uq i _ _ _ _ _ _ => some i
  | .gate _ => none

end UInstr

/-- An oracle quantum circuit on `m` wires: a list of instructions applied left to right. -/
abbrev UCirc (ar : ℕ → ℕ → ℕ) (m : ℕ) := List (UInstr ar m)

namespace UCirc

variable {ar : ℕ → ℕ → ℕ} {m : ℕ}

/-- Running a circuit with unitary oracle `O` and classical oracle `C`. -/
noncomputable def run (O : UOracle ar) (C : Oracle) (c : UCirc ar m) (ψ : QState m) : QState m :=
  c.foldl (fun st g => g.apply O C st) ψ

/-- The description of a circuit: the concatenated instruction descriptions. -/
def desc (c : UCirc ar m) : Str := (c.map UInstr.desc).flatten

/-- The **size** of a circuit (§3.2.1, p. 12: "We measure the size of a circuit by its description
length in bits"; §3.2.2: "A query to level `t` takes at least `t` time"): its description length
plus `t` for every query to level `t`. -/
def size (c : UCirc ar m) : ℕ := c.desc.length + (c.map UInstr.levelCost).sum

end UCirc

/-- The probability that measuring wire `w` of the (unnormalized) state `ψ` in the computational
basis gives `1`, i.e. `‖Π_{w=1} ψ‖²`. -/
noncomputable def probOne {m : ℕ} (ψ : QState m) (w : Fin m) : ℝ :=
  ∑ y : Bits m, if y w then ‖ψ y‖ ^ 2 else 0

end QAdvFew.PoQOracle.Supplement


