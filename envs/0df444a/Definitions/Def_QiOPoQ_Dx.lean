-- Prove2me | Definitions.Def_QiOPoQ_Dx
-- name    : QiOPoQ_Dx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:17.86752+00:00
-- url     : https://prove2.me/theorems/b96d0e94-09c0-4b9e-b3ff-99e629dc6117
-- title:
--   The circuit $D_x$ of the proof of Lemma 4.4 (Figure 5)
-- statement:
--   For $x\in\{0,1\}^\lambda$, the circuit $D_x$ has one logical input qubit $Q$ and uses the output, instance and workspace registers of $V_\lambda$ as clean ancillas. It applies, in order:
--
--   1. $X^x$ on the instance register, with one gate (possibly an identity gate) for each bit;
--   2. $V_\lambda$;
--   3. a CNOT controlled on the output qubit of $V_\lambda$ with target $Q$;
--   4. $V_\lambda^\dagger$, the adjoint gates in reverse order;
--   5. $X^x$ again.
--
--   Its output is $Q$. It has $2|V_\lambda|+2\lambda+1$ gates, $1$ input and $\lambda+n_{\mathrm{anc}}$ ancillas. It is the bridge between the hardness of $L$ and the two padded circuits: it implements $X^{L(x)}(\cdot)$ up to negligible error.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Lemma 4.4, p.18; Figure 5, p.19

import Mathlib
import Definitions.Def_QiOPoQ_Circ

set_option autoImplicit false

namespace QiOPoQ

variable {G : GateSet}

/-- A one-qubit gate `i` placed on wire `a`. -/
def oneWire {W : ℕ} (i : Fin G.k) (h : G.arity i = 1) (a : Fin W) : Fin (G.arity i) ↪ Fin W :=
  ⟨fun _ => a, fun j₁ j₂ _ => Fin.ext (by have := j₁.isLt; have := j₂.isLt; omega)⟩

/-- `CNOT` placed with control on wire `c` and target on wire `tg` (gate wire `0` ↦ `c`, gate
wire `1` ↦ `tg`). -/
def twoWires {W : ℕ} (c tg : Fin W) (h : c ≠ tg) : Fin (G.arity G.gCNOT) ↪ Fin W :=
  ⟨fun j => if j.val = 0 then c else tg, by
    intro j₁ j₂ hj
    have h₁ := j₁.isLt
    have h₂ := j₂.isLt
    have ha := G.arity_gCNOT
    apply Fin.ext
    by_cases p : j₁.val = 0 <;> by_cases q : j₂.val = 0 <;> simp only [p, q, if_true, if_false] at hj
    · omega
    · exact absurd hj h
    · exact absurd hj.symm h
    · omega⟩

/-- The wire shift `w ↦ w + 1` from the wires of `V_λ` to the wires of `D_x` (wire `0` of `D_x`
is the logical qubit `Q`). -/
def shiftEmb (W : ℕ) : Fin W ↪ Fin (1 + W) :=
  ⟨Fin.natAdd 1, fun a b h => by simpa using h⟩

/-- The layer `X^x` of `D_x`: on wire `1 + j` of the instance register, the gate `X` if `x_j = 1`
and the gate `I` if `x_j = 0` ("using one gate (possibly an identity gate) for each bit of x"). -/
def xLayer (C : Circ G) (x : List Bool) :
    List (Σ i : Fin G.k, Fin (G.arity i) ↪ Fin (1 + (C.nin + C.nanc))) :=
  List.ofFn fun j : Fin C.nin =>
    if x.getD j.val false then
      ⟨G.gX, oneWire G.gX G.arity_gX (shiftEmb _ (Fin.castAdd C.nanc j))⟩
    else ⟨G.gI, oneWire G.gI G.arity_gI (shiftEmb _ (Fin.castAdd C.nanc j))⟩

/-- **The circuit `D_x` of the proof of Lemma 4.4 (Figure 5).** Gheorghiu, Gupte, Havlíček, Liu,
*Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289
(sha256 fe2f9210…), proof of Lemma 4.4, p.18: "Define a circuit D_x with one logical input
qubit Q and clean workspace as follows: • apply X^x to prepare x in the instance register, using
one gate (possibly an identity gate) for each bit of x; • apply V_λ and, controlled on its output
qubit, apply X to Q; • apply V_λ† and then X^x again to restore the instance register to zero."
(Figure 5, p.19.)

For a circuit `C = V_λ` and a string `x`: wire `0` is the input `Q`; wires `1, …, n_in + n_anc`
carry the wires of `C` shifted by one (instance register `1, …, n_in`, then the ancillas of `C`,
including its output wire), all ancillas of `D_x`. The gates are `X^x`, the gates of `C`, one
`CNOT` from each output wire of `C` (one wire for `V_λ`) onto `Q`, the adjoint gates of `C` in
reverse order (`V_λ†`), and `X^x` again. The output register is `Q`.

**Formalization Note.** `V_λ†` uses the adjoint gate of the gate set for each gate, so it has
`|V_λ|` gates; hence `D_x` has `2|V_λ| + 2λ + 1` gates when `V_λ` has `λ` inputs and one output. -/
def Dx (C : Circ G) (x : List Bool) : Circ G where
  nin := 1
  nanc := C.nin + C.nanc
  gates :=
    xLayer C x ++
    C.gates.map (fun g => ⟨g.1, g.2.trans (shiftEmb _)⟩) ++
    C.out.map (fun w => ⟨G.gCNOT, twoWires (shiftEmb _ w) ⟨0, by omega⟩
      (by
        intro h
        have h' := congrArg Fin.val h
        change 1 + w.val = 0 at h'
        omega)⟩) ++
    C.gates.reverse.map (fun g =>
      ⟨G.adj g.1, ((finCongr (G.arity_adj g.1)).toEmbedding.trans g.2).trans (shiftEmb _)⟩) ++
    xLayer C x
  out := [⟨0, by omega⟩]
  out_nodup := List.nodup_singleton _

end QiOPoQ


