-- Prove2me | Definitions.Def_QiOPoQ_Supplement_postX
-- name    : QiOPoQ_Supplement_postX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:50:35.997353+00:00
-- url     : https://prove2.me/theorems/a4603fd8-c560-48bb-a446-71fc2c994d22
-- title:
--   The circuit $X^b\circ C$: $C$ followed by an $X$ or $I$ gate on its output wire
-- statement:
--   For a circuit $C$ with one output wire, $X^b\circ C$ is $C$ followed by one gate on that wire: the designated $X$ gate for $b=1$ and the designated identity gate for $b=0$. Thus $X\circ C$ and $I\circ C$ have the same shape $(|C|+1,n_{\mathrm{in}},n_{\mathrm{anc}},1)$ and implement $X^b(C(\cdot))$. Figures 7 and 9 obfuscate these circuits at the planted positions.
--
--   **Formalization Note** A circuit with more or fewer output wires is returned unchanged; the protocols apply it only to circuits of $\mathcal C_{\mathsf{BQP}}$.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Notation 5.1, p.22; Figure 7, p.23; Figure 9, p.28

import Mathlib
import Definitions.Def_QiOPoQ_Circ

set_option autoImplicit false

namespace QiOPoQ.Supplement

variable {G : GateSet}

/-- The placement of a one-qubit gate `g` on the wire `w`. -/
def oneWire {W : ℕ} (g : Fin G.k) (h : G.arity g = 1) (w : Fin W) : Fin (G.arity g) ↪ Fin W :=
  ⟨fun _ => w, fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩

/-- **`X^b ∘ C`** (Gheorghiu, Gupte, Havlíček, Liu, arXiv:2609.40289, sha256 fe2f9210…,
Notation 5.1, p.22: "the same gate count as X ∘ C and I ∘ C"; Figure 7, p.23, and Figure 9, p.28:
"qiO(1^λ, X_{b_{i,j}} ∘ C)"): the circuit `C` followed by one gate on its output wire, the
designated `X` gate for `b = 1` and the designated identity gate `I` for `b = 0`. So `X ∘ C` and
`I ∘ C` have the same shape `(|C| + 1, n_in, n_anc, n_out)` and implement `X^b(C(·))`.

**Formalization Note.** Defined for circuits with one output wire (every circuit of `C_BQP`);
any other circuit is returned unchanged. -/
def postX (b : Bool) (C : Circ G) : Circ G :=
  match C.out with
  | [w] =>
    { C with
      gates := C.gates ++
        [if b then ⟨G.gX, oneWire G.gX G.arity_gX w⟩ else ⟨G.gI, oneWire G.gI G.arity_gI w⟩] }
  | _ => C

end QiOPoQ.Supplement


