-- Prove2me | Definitions.Def_QuantumHMMR_GateCode
-- name    : QuantumHMMR_GateCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:54.483876+00:00
-- url     : https://prove2.me/theorems/bd2a84e8-b557-4c58-b18e-191b7d8c0557
-- title:
--   Gate descriptions: $H$, $T$, CNOT and controlled rational rotations
-- statement:
--   A test circuit is described gate by gate. A **gate code** is one of
--
--   1. $H\,i$, the Hadamard gate on wire $i$;
--   2. $T\,i$, the gate $\mathrm{diag}(1, e^{i\pi/4})$ on wire $i$;
--   3. $\mathrm{CNOT}\,c\,t$, control $c$, target $t$;
--   4. $\mathrm{CRot}\,p\,q\,c\,t$, the rotation
--   $$
--   R_{p/q} = \begin{pmatrix} \sqrt{p/q} & -\sqrt{1 - p/q} \\ \sqrt{1 - p/q} & \sqrt{p/q} \end{pmatrix}
--   $$
--   on wire $t$, controlled by wire $c$, for integers $0 \le p \le q$, $q > 0$ written in binary.
--
--   A code is valid on $N$ wires when its wires are less than $N$ and distinct and, for $\mathrm{CRot}$, $0 < q$ and $p \le q$. Each valid code denotes the corresponding unitary on $N$ qubits.
--
--   **Formalization Note** The QPT model of p.11 fixes no gate set. $\mathrm{CRot}$ is included because the test of Lemma 4.4 selects a uniformly random nonidentity Pauli from a subspace, an exact uniform choice among $2^r - 1$ elements, which no circuit over $\{H, T, \mathrm{CNOT}\}$ produces exactly. Gates are placed with the published `embedOp`; an invalid code denotes the identity and never occurs in a `CopyTest`.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 3, p.11 (QPT model) and Lemma 4.4, p.14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45

namespace QuantumHMMR

/-- The classical description of one elementary gate of a test circuit (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §3, p.11, the QPT
model, which fixes no gate set): a Hadamard `H i`, a `T` gate `T i`, a `CNOT c tgt`, or a
controlled rational rotation `CRot p q c tgt`, whose target block is
`[[√(p/q), -√(1-p/q)], [√(1-p/q), √(p/q)]]` (exact amplitudes `√(p/q)`, `p ≤ q`, written in binary).
Wires are natural numbers; `GateCode.Valid N` says the wires are `< N` and distinct and `0 < q`,
`p ≤ q`.

**Formalization Note** The model includes `CRot` because the test of Lemma 4.4 selects a uniformly
random nonidentity Pauli from a subspace, an exact uniform choice among `2^r - 1` elements, which no
circuit over `{H, T, CNOT}` produces exactly. An invalid code denotes the identity (it never occurs
in a `CopyTest`, whose gates are valid). -/
inductive GateCode where
  | H (i : ℕ)
  | T (i : ℕ)
  | CNOT (c tgt : ℕ)
  | CRot (p q c tgt : ℕ)
  deriving DecidableEq

namespace GateCode

/-- A gate code is valid on `N` wires: its wires are `< N` and pairwise distinct, and a `CRot p q`
has `0 < q` and `p ≤ q`. -/
def Valid (N : ℕ) : GateCode → Prop
  | H i => i < N
  | T i => i < N
  | CNOT c tgt => c < N ∧ tgt < N ∧ c ≠ tgt
  | CRot p q c tgt => c < N ∧ tgt < N ∧ c ≠ tgt ∧ 0 < q ∧ p ≤ q

/-- The ordered pair of distinct wires `(c, tgt)` as an embedding `Fin 2 ↪ Fin N`. -/
def wirePair {N : ℕ} (c tgt : Fin N) (h : c ≠ tgt) : Fin 2 ↪ Fin N :=
  ⟨![c, tgt], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]⟩

/-- The `N`-qubit matrix of a gate code: the published `hadamard`, `gateT`, `cnot` and
`controlled` gates (control = first listed wire) placed on the listed wires by the published
`embedOp`; the `CRot p q` target block is `[[√(p/q), -√(1-p/q)], [√(1-p/q), √(p/q)]]` (row and
column `false` first). An invalid code denotes the identity. -/
noncomputable def op (N : ℕ) : GateCode → QMat N
  | H i => if h : i < N then
      embedOp (k := 1) (Gate.ofMatrix1 hadamard).mat ⟨fun _ => ⟨i, h⟩, fun a b _ => Subsingleton.elim a b⟩
    else 1
  | T i => if h : i < N then
      embedOp (k := 1) (Gate.ofMatrix1 gateT).mat ⟨fun _ => ⟨i, h⟩, fun a b _ => Subsingleton.elim a b⟩
    else 1
  | CNOT c tgt => if h : c < N ∧ tgt < N ∧ c ≠ tgt then
      embedOp (k := 2) (Gate.ofMatrix2 cnot).mat
        (wirePair ⟨c, h.1⟩ ⟨tgt, h.2.1⟩ (fun e => h.2.2 (congrArg Fin.val e)))
    else 1
  | CRot p q c tgt => if h : c < N ∧ tgt < N ∧ c ≠ tgt then
      embedOp (k := 2) (Gate.ofMatrix2 (controlled (Matrix.of fun a b : Bool =>
          match a, b with
          | false, false => ((Real.sqrt ((p : ℝ) / q) : ℝ) : ℂ)
          | false, true => -((Real.sqrt (1 - (p : ℝ) / q) : ℝ) : ℂ)
          | true, false => ((Real.sqrt (1 - (p : ℝ) / q) : ℝ) : ℂ)
          | true, true => ((Real.sqrt ((p : ℝ) / q) : ℝ) : ℂ)))).mat
        (wirePair ⟨c, h.1⟩ ⟨tgt, h.2.1⟩ (fun e => h.2.2 (congrArg Fin.val e)))
    else 1

/-- The list of numbers describing a gate code: a tag (`0` H, `1` T, `2` CNOT, `3` CRot) followed by
its arguments. -/
def toNats : GateCode → List ℕ
  | H i => [0, i]
  | T i => [1, i]
  | CNOT c tgt => [2, c, tgt]
  | CRot p q c tgt => [3, p, q, c, tgt]

end GateCode

end QuantumHMMR


