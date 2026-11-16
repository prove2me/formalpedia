-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsOWFQuantum
-- name    : QiOPoQ_Supplement_IsOWFQuantum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:53:48.454567+00:00
-- url     : https://prove2.me/theorems/e01df200-d2f4-4ea3-8607-98f995dc8c53
-- title:
--   One-way functions secure against non-uniform QPT inverters
-- statement:
--   A function $g$ is a quantum-secure one-way function if it is polynomial-time computable and for every non-uniform QPT inverter $A$
--
--   $$\Pr_{x\leftarrow\{0,1\}^m}\big[g(A(1^m,g(x)))=g(x)\big]\le\mathrm{negl}(m).$$
--
--   This is the published `QiOPoQ.IsOWF` with quantum inverters; it is the second hypothesis of Theorem 5.9.
--
--   **Formalization Note** The family $\{g_\lambda\}$ is one map on all strings ($g_\lambda$ is $g$ on length $\lambda$); any preimage counts as a success.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Notation 5.1, p.22; Theorem 5.9, p.29

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_Supplement_NUQPT

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- **One-way functions secure against non-uniform QPT algorithms.** Gheorghiu, Gupte, Havlíček,
Liu, arXiv:2609.40289 (sha256 fe2f9210…), Notation 5.1, p.22: "Define {g_λ}λ∈N to be a family of
quantum-secure one-way functions"; Theorem 5.9, p.29: "g_λ is a one-way function secure against
such adversaries" (non-uniform QPT).

`g` is polynomial-time computable, and for every non-uniform QPT inverter `A` (`NUQPT`) the
probability over a uniform `x ∈ {0,1}^m` and the randomness of `A` that `A(1^m, g(x))` outputs a
preimage of `g(x)` is negligible in `m`. **Formalization Note.** The published `QiOPoQ.IsOWF`
with `NUQPT` in place of `NUPPT`: the family `{g_λ}` is one map (`g_λ` = `g` on length `λ`), any
preimage counts. -/
def IsOWFQuantum (G : GateSet) (g : Str → Str) : Prop :=
  PolyTimeComputable g ∧ ∀ A : NUQPT, Negligible fun m =>
    avgCoins m fun x => A.expect G m (g x) fun x' => if g x' = g x then 1 else 0

end QiOPoQ.Supplement


