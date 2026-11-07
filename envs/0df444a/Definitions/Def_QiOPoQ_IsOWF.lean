-- Prove2me | Definitions.Def_QiOPoQ_IsOWF
-- name    : QiOPoQ_IsOWF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:50.368091+00:00
-- url     : https://prove2.me/theorems/afb91f54-9e0d-4cd5-86da-4ee4c4644b68
-- title:
--   One-way functions secure against non-uniform classical PPT algorithms
-- statement:
--   A function $f$ on bit strings is **one-way against classical PPT algorithms** if it is computable in polynomial time and for every non-uniform classical PPT $A$ the inversion probability
--
--   $$
--   m\mapsto\Pr_{x\in\{0,1\}^m,\ \text{coins of }A}\big[f(A(1^m,f(x)))=f(x)\big]
--   $$
--
--   is negligible. The paper's family $\{f_\lambda\}$ with $f_\lambda$ of input length $\lambda$ is the restriction of the one map $f$ to length $\lambda$.
--
--   **Formalization Note** Any preimage counts as a success, of any length. The published uniform-adversary notions of one-way functions on the platform are weaker and are not used.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Lemma 4.5 and p.20; §3, p.13

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_NUPPT

set_option autoImplicit false

namespace QiOPoQ

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- **One-way functions secure against classical PPT algorithms.** Gheorghiu, Gupte, Havlíček,
Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…), Lemma 4.5, p.20 ("there exist one-way functions that are
secure against classical PPT algorithms") and p.20 ("Let {f_λ}λ∈N be a one-way function family
secure against classical PPT algorithms, where f_λ has input length λ"); §3, p.13: adversaries
are non-uniform.

`f` is polynomial-time computable, and for every non-uniform classical PPT inverter `A` the
probability over a uniform `x ∈ {0,1}^m` and the coins of `A` that `A(1^m, f(x))` outputs some
preimage of `f(x)` is negligible in `m`.

**Formalization Note.** The family `{f_λ}` is one map on all strings (`f_λ` = `f` on length `λ`).
Any preimage, of any length, counts as a success. -/
def IsOWF (f : Str → Str) : Prop :=
  PolyTimeComputable f ∧ ∀ A : NUPPT, Negligible fun m =>
    avgCoins m fun x => A.expect m (f x) fun x' => if f x' = f x then 1 else 0

end QiOPoQ


