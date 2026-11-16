-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsPubVerCVQC
-- name    : QiOPoQ_Supplement_IsPubVerCVQC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:49:45.527293+00:00
-- url     : https://prove2.me/theorems/5b16fb22-005c-426d-b79c-82a6ce93dd91
-- title:
--   Definition 3.6: publicly verifiable classical verification of quantum computation
-- statement:
--   A protocol as in Definition 3.5 is publicly verifiable if a deterministic classical polynomial-time PublicVerify satisfies
--
--   $$\mathrm{Verify}(1^\lambda,C,\mathsf{chall},\mathsf{state},\mathsf{resp})=\mathrm{PublicVerify}(1^\lambda,\mathsf{chall},\mathsf{resp})$$
--
--   for every $\lambda$, every $C\in\mathcal C_{\mathsf{BQP}}$, every $(\mathsf{chall},\mathsf{state})$ in the support of $\mathrm{Gen}(1^\lambda,C)$ and every response.
--
--   **Formalization Note** $\mathcal C_{\mathsf{BQP}}$ is a class of families, so "every $C$" ranges over every member of every family in the class, at every security parameter.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.6, p.16

import Mathlib
import Definitions.Def_QiOPoQ_Supplement_IsCVQC

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- **Definition 3.6 (Publicly verifiable classical verification of quantum computation).**
Gheorghiu, Gupte, Havlíček, Liu, arXiv:2609.40289 (sha256 fe2f9210…), Definition 3.6, p.16: "A
two-message protocol Π = (Gen, Prove, Verify) as in Definition 3.5 is publicly verifiable if there
is a deterministic classical polynomial-time algorithm PublicVerify such that, for every λ, every
C ∈ C_BQP, every (chall, state) in the support of Gen(1^λ, C), and every response resp,
Verify(1^λ, C, chall, state, resp) = PublicVerify(1^λ, chall, resp)."

**Formalization Note.** `C_BQP` is a class of families (`InCBQP`), so "every C ∈ C_BQP" is every
member `C_m` of every family in `C_BQP`, at every security parameter `λ`; the support of Gen is
every admissible draw `ω`. -/
def IsPubVerCVQC (G : GateSet) (rad : ℕ → Circ G → List ℕ) (gen : ℕ → Circ G → List ℕ → Str × Str)
    (verify : ℕ → Circ G → Str → Str → Str → Option Bool) : Prop :=
  ∃ pv : ℕ → Str → Str → Option Bool,
    (∃ g : Str → Str, PolyTimeComputable g ∧
      ∀ n (c resp : Str), g (tup [unary n, c, resp]) = encOptBool (pv n c resp)) ∧
    ∀ Cf : ℕ → Circ G, InCBQP Cf → ∀ m n (ω : List ℕ), List.Forall₂ (· < ·) ω (rad n (Cf m)) →
      ∀ resp : Str, verify n (Cf m) (gen n (Cf m) ω).1 (gen n (Cf m) ω).2 resp =
        pv n (gen n (Cf m) ω).1 resp

end QiOPoQ.Supplement


