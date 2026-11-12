-- Prove2me | Definitions.Def_FourMsgQMA_PolicyCircuit
-- name    : FourMsgQMA_PolicyCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:13.998065+00:00
-- url     : https://prove2.me/theorems/95c65128-1d28-4214-81d0-a0423c1a123f
-- title:
--   Canonically encoded Boolean circuit policies $C:\{0,1\}^k\to\{0,1\}$
-- statement:
--   A **circuit policy** on $k$ bits with $s$ gates is given by its canonical table (Figure 4): inputs have indices $1,\dots,k$, internal gates $k+1,\dots,k+s$; gate $t$ has a type in $\{\mathrm{AND},\mathrm{OR},\mathrm{NOT},0,1\}$ and two child identifiers $u_t,v_t$; there is an output index $\mathrm{out}$.
--
--   The table is **canonical** when $1\le u_t,v_t<t$ for every gate, $v_t=u_t$ for a NOT gate, $u_t=v_t=1$ for a constant gate, and $\mathrm{out}\in[k+s]$.
--
--   The wire values on $y\in\{0,1\}^k$ are
--   $$
--   a_i=y_i\ (i\in[k]),\qquad a_t=\mathrm{gate}_t(a_{u_t},a_{v_t})\ (k<t\le k+s),
--   $$
--   and $C(y)=a_{\mathrm{out}}$. A string $y$ is **authorized** when $C(y)=1$. The module also fixes the wire-value array $a=(a_1,\dots,a_{k+s})$ and an injective bit-string encoding of the table.
--
--   Policies are the first half of an NP ∘ batchQMA instance; the wire values are part of the honest prover's classical witness (Figure 4, check 3).
--
--   **Formalization Note** Indices are the paper's 1-based ones; $y_i$ is `y ⟨i-1, _⟩`. A child identifier that is not smaller than its gate, which a canonical table excludes, reads `false`.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Definition 3.1, p.10 (PDF 12); Figure 4, p.34 (PDF 36)

import Mathlib
import Definitions.Def_FourMsgQMA_ComputedOn

namespace FourMsgQMA

/-!
Goyal, Koppula, STOC 2027 submission (sha256 6c523d45…), Definition 3.1 (p.10, PDF 12) and
Figure 4 (p.34, PDF 36): canonically encoded Boolean circuit policies.
-/

open QAlgorithms.Complexity

/-- The gate types of a policy circuit: AND, OR, NOT and the constants 0 and 1 (Definition 3.1). -/
inductive GateType where
  | and | or | not | zero | one
  deriving DecidableEq

/-- The output of a gate of type `g` on the child values `a, b` (Figure 4: `gate_t(a_{u_t}, a_{v_t})`;
a NOT gate ignores its second input, a constant gate both). -/
def GateType.apply : GateType → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .not, a, _ => !a
  | .zero, _, _ => false
  | .one, _, _ => true

/-- A circuit `C : {0,1}^k → {0,1}` with `s` gates, in the canonical encoding of Figure 4 (p.34):
inputs have indices `1, …, k`, internal gates `k + 1, …, k + s`; internal gate number
`t = k + 1 + j` (for `j : Fin s`) has a type and two child identifiers `(u_t, v_t)`; `out` is the
output index. Indices are the paper's 1-based ones. -/
structure PolicyCircuit (k s : ℕ) where
  /-- Gate `t = k + 1 + j`: its type and its two child identifiers `u_t, v_t`. -/
  gate : Fin s → GateType × ℕ × ℕ
  /-- The output index `out`. -/
  out : ℕ

/-- The canonical-encoding checks of Figure 4 (p.34): `1 ≤ u_t, v_t < t` for every gate `t`
(topological order, fan-in at most two), `v_t = u_t` for a NOT gate, `u_t = v_t = 1` for a constant
gate, and `out ∈ [k + s]`. -/
def PolicyCircuit.IsCanonical {k s : ℕ} (C : PolicyCircuit k s) : Prop :=
  (∀ j : Fin s,
    1 ≤ (C.gate j).2.1 ∧ (C.gate j).2.1 < k + 1 + j ∧
    1 ≤ (C.gate j).2.2 ∧ (C.gate j).2.2 < k + 1 + j ∧
    ((C.gate j).1 = .not → (C.gate j).2.2 = (C.gate j).2.1) ∧
    ((C.gate j).1 = .zero ∨ (C.gate j).1 = .one → (C.gate j).2.1 = 1 ∧ (C.gate j).2.2 = 1)) ∧
  1 ≤ C.out ∧ C.out ≤ k + s

/-- The wire values `a_w` of `C` on the input `y ∈ {0,1}^k` (Figure 4: `a_i = y_i` for `i ∈ [k]`,
`a_t = gate_t(a_{u_t}, a_{v_t})` for `k < t ≤ k + s`). The paper's `y_i` is `y ⟨i - 1, _⟩`.
A child identifier that is not smaller than its gate (excluded by `IsCanonical`) and an index
outside `[k + s]` read `false`. -/
def PolicyCircuit.wire {k s : ℕ} (C : PolicyCircuit k s) (y : Fin k → Bool) (w : ℕ) : Bool :=
  if h : 1 ≤ w ∧ w ≤ k then y ⟨w - 1, by omega⟩
  else if h' : k < w ∧ w ≤ k + s then
    (C.gate ⟨w - k - 1, by omega⟩).1.apply
      (if (C.gate ⟨w - k - 1, by omega⟩).2.1 < w then C.wire y (C.gate ⟨w - k - 1, by omega⟩).2.1
        else false)
      (if (C.gate ⟨w - k - 1, by omega⟩).2.2 < w then C.wire y (C.gate ⟨w - k - 1, by omega⟩).2.2
        else false)
  else false
termination_by w
decreasing_by all_goals assumption

/-- `C(y)`, the value of the output wire. `y` is **authorized** when `C(y) = 1` (Definition 3.1). -/
def PolicyCircuit.eval {k s : ℕ} (C : PolicyCircuit k s) (y : Fin k → Bool) : Bool :=
  C.wire y C.out

/-- The wire-value array `a ∈ {0,1}^{k+s}` of Figure 4, `a = (a_1, …, a_{k+s})`. -/
def PolicyCircuit.wireValues {k s : ℕ} (C : PolicyCircuit k s) (y : Fin k → Bool) : List Bool :=
  List.ofFn fun t : Fin (k + s) => C.wire y (t + 1)

/-- The numeric code of a gate type. -/
def GateType.code : GateType → ℕ
  | .and => 0 | .or => 1 | .not => 2 | .zero => 3 | .one => 4

/-- The canonical encoding of a circuit table as a bit string: `k`, `s`, every gate record
(type, `u_t`, `v_t`) in topological order, and `out`, each number self-delimiting (`encNat`). -/
def PolicyCircuit.encode {k s : ℕ} (C : PolicyCircuit k s) : Str :=
  encNat k ++ encNat s ++
    (List.ofFn fun j : Fin s =>
      encNat (C.gate j).1.code ++ encNat (C.gate j).2.1 ++ encNat (C.gate j).2.2).flatten ++
    encNat C.out

end FourMsgQMA


