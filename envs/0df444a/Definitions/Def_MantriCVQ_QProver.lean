-- Prove2me | Definitions.Def_MantriCVQ_QProver
-- name    : MantriCVQ_QProver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:56.233196+00:00
-- url     : https://prove2.me/theorems/48a6778d-9d46-4fd9-8d4b-e56474c1688e
-- title:
--   Efficient quantum honest provers
-- statement:
--   An **efficient quantum prover** over a gate set $G$ produces each message by one circuit with oracle gates, applied to the basis encoding of the input $w$ and the history with fresh ancillas, followed by a measurement of a list of distinct wires (the Born rule). The circuit and the wires are determined by $w$, the slot number and the length of the encoding. A classical polynomial-time machine with no oracle generates them, and their size and ancilla count are polynomial in the length of that whole input.
--
--   **Formalization Note** The prover keeps no quantum memory between slots. This restricts the honest prover, so its existence is the stronger statement; the paper's prover recomputes every secret afresh and has this form. The circuit may depend on the public input classically: a circuit keyed by $|w|$ alone could not meet the exact query count of Theorem 5.5 (iv), since claims of different heights can have encodings of one length. For the unary inputs of Theorem 1.1, $w=1^n$ and $n$ carry the same information. If the masses of the measured wires do not sum to one, which does not happen for a unitary circuit, a list of $\ell$ distinct wires and a normalized input, the definition returns the point mass at the zero string.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16); §5.2, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_MantriCVQ_Circ
import Definitions.Def_MantriCVQ_ket
import Definitions.Def_MantriCVQ_Strategy
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

open Classical in
/-- The law of the measured wires `ws` of the state `ψ`, as a distribution on strings of length `ℓ`
(the Born rule).

**Formalization Note** For a state of norm one and a list of `ℓ` distinct wires the masses sum to
one, and this is the Born distribution. In any other case the definition returns the point mass at
the all-zero string, a value that a unitary circuit over an admissible gate set never reaches when
`ws` has length `ℓ`. -/
noncomputable def bornPMF {N : ℕ} (ψ : QState N) (ws : List (Fin N)) (ℓ : ℕ) : PMF (Bits ℓ) :=
  let p : Bits ℓ → ENNReal := fun b =>
    ENNReal.ofReal (∑ y : Bits N, if ws.map y = List.ofFn b then ‖ψ y‖ ^ 2 else 0)
  if h : ∑ b, p b = 1 then PMF.ofFintype p h else PMF.pure fun _ => false

/-- An efficient quantum honest prover over the gate set `G` (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), §3.1, p. 14 (PDF p. 16): "The honest prover is efficient if it is a uniform
polynomial-time quantum algorithm with query access to O"). For a public input `w`, a slot `i` and a
length `inLen` of the encoded pair of input and history, it has an ancilla count, a circuit with
oracle gates on `inLen + anc` wires, and a list of distinct wires to measure.

**Formalization Note** The prover is memoryless: each message is produced by one circuit from the
input and the transcript. This restricts the honest prover, so its existence is the stronger
statement. The circuit may depend on the public input `w` classically, because the input is known to
both parties (§5.2, p. 19). A circuit keyed by `|w|` alone could not meet the exact query count of
Theorem 5.5 (iv), since claims of different heights can have encodings of one length. For the unary
inputs `w = 1^n` of Theorem 1.1, `w` and `n` carry the same information. -/
structure QProver (G : List Gate) where
  /-- the ancilla count -/
  anc : Str → ℕ → ℕ → ℕ
  /-- the circuit for one message -/
  circ : (w : Str) → (i inLen : ℕ) → Circ G (inLen + anc w i inLen)
  /-- the measured wires -/
  outW : (w : Str) → (i inLen : ℕ) → List (Fin (inLen + anc w i inLen))
  outW_nodup : ∀ w i inLen, (outW w i inLen).Nodup

/-- Uniformity: a classical polynomial-time machine, with no oracle, maps `(w, 1^i, 1^inLen)` to the
description of the circuit and of its measured wires. -/
def QProver.Uniform {G : List Gate} (P : QProver G) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ (w : Str) (i inLen : ℕ),
    f (tup [w, unary i, unary inLen]) =
      encNat (P.anc w i inLen) ++
        encStr ((P.outW w i inLen).map fun j => encNat (j : ℕ)) ++ (P.circ w i inLen).enc

/-- Polynomial size, in the length of the prover's whole input: on a transcript of a polynomially
bounded schedule, `i` and `inLen` are polynomial in `|w|`, so this is polynomial in `|w|`. -/
def QProver.PolyBounded {G : List Gate} (P : QProver G) : Prop :=
  ∃ q : Polynomial ℕ, ∀ (w : Str) (i inLen : ℕ),
    (P.circ w i inLen).size ≤ q.eval (w.length + i + inLen) ∧
      P.anc w i inLen ≤ q.eval (w.length + i + inLen)

/-- The strategy of a quantum prover with the oracle `O`: on input `w` and history `hist`, run the
circuit on `|tup (w, hist), 0…0⟩` and measure the output wires. -/
noncomputable def QProver.toStrategy {G : List Gate} (P : QProver G) (O : Oracle) : Strategy :=
  fun w hist ℓ =>
    let x := tup (w :: hist)
    bornPMF ((P.circ w hist.length x.length).run O
        (ket _ (x ++ List.replicate (P.anc w hist.length x.length) false)))
      (P.outW w hist.length x.length) ℓ

end MantriCVQ


