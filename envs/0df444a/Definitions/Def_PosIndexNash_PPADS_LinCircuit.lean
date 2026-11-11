-- Prove2me | Definitions.Def_PosIndexNash_PPADS_LinCircuit
-- name    : PosIndexNash_PPADS_LinCircuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:31:39.952591+00:00
-- url     : https://prove2.me/theorems/90d56921-0e49-4453-bed7-b660c40c487c
-- title:
--   Rational Linear-FIXP circuits: evaluation, strictness and binary code (p. 13)
-- statement:
--   A **rational Linear-FIXP circuit** is a straight-line program over the reals using rational affine operations together with $\max$. It has $d_{\mathrm{in}}$ input wires; each gate appends one wire whose value is either an affine combination $c + \sum_k a_k w_k$ of earlier wires with rational $c, a_k$, or $\max(w_i, w_j)$ of two earlier wires; some wires are designated outputs. On $d_{\mathrm{in}} = d$ inputs and $d$ outputs it computes a piecewise-affine map $\Phi : \mathbb{R}^d \to \mathbb{R}^d$.
--
--   The circuit is **strict** at a point $p$ if the two inputs of every max gate have different values when the circuit is evaluated at $p$ (no max gate has a tie). At such a point the branch selected by each max gate is locally constant, and replacing each max gate by it gives the active affine piece of $\Phi$ at $p$.
--
--   **Formalization Note** `LinCircuit.WF` requires every gate to read earlier wires only. `LinCircuit.toMap C d` is the map $\mathbb{R}^d\to\mathbb{R}^d$ (input wire $i$ reads $x_i$, coordinate $\ell$ is the $\ell$-th output wire); it is used with $d_{\mathrm{in}} = |\mathrm{outs}| = d$. `LinCircuit.enc` is a self-delimiting binary code of the circuit built from the platform's `encBin`/`encRat`.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 13, 'Linear fixed point maps and their index'

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace PosIndexNash.PPADS

open QAlgorithms.LocalHamiltonian

/-- **A gate of a rational Linear-FIXP circuit** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a
Positive Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 13: "a straight-line
program using rational affine operations together with max").

`affine c ts` computes `c + Σ_{(k, a) ∈ ts} a · w_k` from earlier wires `w_k` (rational
coefficients); `max i j` computes `max(w_i, w_j)`. -/
inductive LGate where
  | affine (c : ℚ) (ts : List (ℕ × ℚ))
  | max (i j : ℕ)

/-- **A rational Linear-FIXP circuit** (arXiv:2609.23879, p. 13). `dIn` input wires
`0, …, dIn − 1`; the `k`-th gate writes wire `dIn + k`; `outs` lists the output wires. -/
structure LinCircuit where
  dIn : ℕ
  gates : List LGate
  outs : List ℕ

/-- **Well-formed Linear-FIXP circuit**: the `k`-th gate reads only wires `< dIn + k`
(straight-line, acyclic) and every output wire exists. -/
def LinCircuit.WF (C : LinCircuit) : Prop :=
  (∀ k (hk : k < C.gates.length),
    match C.gates[k] with
    | LGate.affine _ ts => ∀ t ∈ ts, t.1 < C.dIn + k
    | LGate.max i j => i < C.dIn + k ∧ j < C.dIn + k) ∧
  ∀ o ∈ C.outs, o < C.dIn + C.gates.length

/-- Value of one gate given the list `ws` of the values of the earlier wires (over `ℝ`). -/
noncomputable def LGate.value (ws : List ℝ) : LGate → ℝ
  | LGate.affine c ts => (c : ℝ) + (ts.map (fun t => (t.2 : ℝ) * ws.getD t.1 0)).sum
  | LGate.max i j => Max.max (ws.getD i 0) (ws.getD j 0)

/-- **Wire values** of the circuit on the input `x ∈ ℝ^{dIn}`: the inputs, then each gate in
order appends its value. -/
noncomputable def LinCircuit.wires (C : LinCircuit) (x : Fin C.dIn → ℝ) : List ℝ :=
  C.gates.foldl (fun ws g => ws ++ [g.value ws]) (List.ofFn x)

/-- The circuit input fed from a point `x ∈ ℝ^d`: input wire `i` reads `x_i` (and `0` if
`i ≥ d`, which does not occur when `dIn = d`). -/
noncomputable def LinCircuit.inputOf (C : LinCircuit) {d : ℕ} (x : Fin d → ℝ) : Fin C.dIn → ℝ :=
  fun i => if h : i.val < d then x ⟨i.val, h⟩ else 0

/-- **The map `Φ : ℝ^d → ℝ^d` computed by the circuit** (p. 13): coordinate `l` is the value of
the `l`-th output wire on the input `x`.

**Formalization Note** Used with `dIn = |outs| = d`, where it is exactly the computed map; the
defaults (`0` for a missing wire) are never read on well-formed circuits of that shape. -/
noncomputable def LinCircuit.toMap (C : LinCircuit) (d : ℕ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun l => (C.wires (C.inputOf x)).getD (C.outs.getD l.val 0) 0

/-- **Strictness at a point** (arXiv:2609.23879, p. 13: "the circuit is strict at p if the two
inputs of every max gate have different values when the circuit is evaluated at p, i.e., no max
gate has a tie"). -/
def LinCircuit.StrictAt (C : LinCircuit) {d : ℕ} (x : Fin d → ℝ) : Prop :=
  ∀ k (hk : k < C.gates.length) (i j : ℕ), C.gates[k] = LGate.max i j →
    (C.wires (C.inputOf x)).getD i 0 ≠ (C.wires (C.inputOf x)).getD j 0

/-- Binary code of a gate: a tag bit, then `c`, the number of terms and the terms
`(k, a)` (`affine`), or the two wire indices (`max`). Numbers are self-delimiting binary
(`encBin`), rationals `encRat`. -/
def LGate.enc : LGate → List Bool
  | LGate.affine c ts => false :: (encRat c ++ encBin ts.length ++
      ts.flatMap (fun t => encBin t.1 ++ encRat t.2))
  | LGate.max i j => true :: (encBin i ++ encBin j)

/-- **Binary code of a Linear-FIXP circuit**: `dIn`, the number of gates, the gate codes, the
number of outputs and the output wires. Every part is self-delimiting, so a code determines the
circuit; its length is polynomial in the size of the circuit and the bit lengths of its
coefficients. -/
def LinCircuit.enc (C : LinCircuit) : List Bool :=
  encBin C.dIn ++ encBin C.gates.length ++ C.gates.flatMap LGate.enc ++
    encBin C.outs.length ++ C.outs.flatMap encBin

end PosIndexNash.PPADS


