-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsAFCorrect
-- name    : QiOPoQ_Supplement_IsAFCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:07:02.716386+00:00
-- url     : https://prove2.me/theorems/6fce03d4-b7aa-4bcf-95c7-14aac8aad857
-- title:
--   Correctness of a transformation of ancilla-free circuits (as in Definition 3.1)
-- statement:
--   A classical PPT transformation $T$ of ancilla-free circuits satisfies the correctness guarantee of Definition 3.1 if for every polynomially bounded width $n(\lambda)$ and every polynomial-size family of ancilla-free $n(\lambda)$-qubit circuits $C_\lambda$ there is a negligible $\mu$ such that, with probability at least $1-\mu(\lambda)$, $T(1^\lambda,C_\lambda)$ describes an ancilla-free $n(\lambda)$-qubit circuit within diamond distance $\mu(\lambda)$ of $C_\lambda$.
--
--   **Formalization Note** Outputs are read as circuits of the same width, since Definition 6.4 and the obfuscator of Theorem 6.6 concatenate them.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Assumption 6.3, p.31; Definition 3.1, p.14

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_diamond
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_Supplement_Placement
import Definitions.Def_QMAvsQCMAH_PolyBounded
import Definitions.Def_QiOPoQ_Supplement_PolyBounded2

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

open Classical in
/-- **Correctness of a transformation of ancilla-free circuits** (Gheorghiu, Gupte, Havlíček,
Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289, sha256 fe2f9210…, Assumption 6.3, p.31: "classical probabilistic
polynomial-time transformations RIO, Encode of ancilla-free quantum circuits, each satisfying the
negligible diamond-distance correctness guarantee of Definition 3.1").

`T` is a classical PPT algorithm run on `(1^λ, C)`; for every polynomially bounded width `n(λ)`
and every polynomial-size family of ancilla-free `n(λ)`-qubit circuits `C_λ`, one negligible `μ`
satisfies: with probability at least `1 − μ(λ)` the output describes an ancilla-free
`n(λ)`-qubit circuit `D` with `∥D − C_λ∥⋄ ≤ μ(λ)`.

**Formalization Note.** The outputs are read as ancilla-free circuits of the same width, since
Definition 6.4 and the proof of Theorem 6.6 concatenate them with each other and with the masks. -/
def IsAFCorrect (G : GateSet) (T : UPPT) : Prop :=
  ∀ nw : ℕ → ℕ, QMAvsQCMAH.PolyBounded nw → ∀ Cf : (l : ℕ) → List (Placement G (nw l)),
    QMAvsQCMAH.PolyBounded (fun l => (Cf l).length) → ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ l,
      1 - μ l ≤ T.expect (pair (unary l) (encCirc (afCirc (nw l) (Cf l)))) fun s =>
        if ∃ D : List (Placement G (nw l)), decAC (nw l) s = some D ∧
            diamond (chan (afCirc (nw l) D)) (chan (afCirc (nw l) (Cf l))) ≤ μ l then 1 else 0

end QiOPoQ.Supplement


