-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_PredHolds
-- name    : DoublyEffIP_Supplement_PredHolds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:31:50.007786+00:00
-- url     : https://prove2.me/theorems/d6ec04c7-d77f-42a5-8648-9fcce41227da
-- title:
--   A described predicate holds: $C(x,\langle\Psi\rangle)=1$
-- statement:
--   Let $T$ be a generator of implementation circuits, $\alpha$ the field generator, $x\in R^n$ and $\langle\Psi\rangle\in\{0,1\}^B$. Then $\Psi(x)=1$ holds if the circuit $C$ that $T$ generates on the shape $(1^n,1^B)$ satisfies
--
--   $$
--   C\big(x,\langle\Psi\rangle\big)=1 ,
--   $$
--
--   the single output value being $1$.
--
--   This is Definition 5 read for predicates: $\langle\Psi\rangle$ describes $\Psi$ when its log-space uniform implementation circuit computes $\Psi(x)=C(x,\langle\Psi\rangle)$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definition 5

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit
import Definitions.Def_DoublyEffIP_Supplement_evalCircuit
import Definitions.Def_DoublyEffIP_Supplement_IsImpl
import Definitions.Def_DoublyEffIP_Supplement_implShape
import Definitions.Def_DoublyEffIP_Supplement_bitsIn
import Definitions.Def_TreeEdgeRankPC_Transducer

set_option autoImplicit false

open TreeEdgeRankPC

namespace DoublyEffIP.Supplement

/-- **A described predicate holds** — Definition 5 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9: "⟨Φ⟩ ∈ {0,1}^B is
a description of a function Φ : F^n → F^m if there exists a log-space uniform circuit
C : F^{n+B} → F^m … such that C(x, ⟨Φ⟩) = Φ(x)", read for a predicate (`m = 1`).

`PredHolds α T x desc`: the implementation circuit `C` that `T` outputs on the shape
`(|x|, |desc|)` satisfies `C(x, desc) = 1` over the ring of `α`, i.e. `Ψ(x) = 1`.

**Formalization Note.** `C` is evaluated with the field generator `α` (`evalCircuit`); the output
must be the single value `1`. -/
def PredHolds {R : Type*} [CommRing R] (α : R) (T : Transducer) (x : List R)
    (desc : List Bool) : Prop :=
  ∃ C : Circuit, IsImpl T (implShape x.length desc.length) C ∧
    evalCircuit α C (x ++ bitsIn R desc) = [1]

end DoublyEffIP.Supplement


