-- Prove2me | Definitions.Def_NKtLB_Supplement_IsPolySampler
-- name    : NKtLB_Supplement_IsPolySampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:35:53.177507+00:00
-- url     : https://prove2.me/theorems/ac3f30d1-67fa-44bb-bd26-2906ce7c01e5
-- title:
--   Polynomial-time samplers of distributions over $\{0,1\}^n\times\{0,1\}^n$
-- statement:
--   A **polynomial-time samplable distribution family** $\{D_n\}$ supported over $\{0,1\}^n\times\{0,1\}^n$ is given by a machine $A$ and an exponent $q$. On input $1^n$ and any random string $r\in\{0,1\}^{n^q+q}$, $A$ halts within $n^q+q$ steps and outputs a pair $(x,y)$ with $x,y\in\{0,1\}^n$. $D_n$ is the output distribution for uniform $r$.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`. The pair is output in the base tuple encoding. Not defined in the paper.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorems 56 and 58, pp.37–38 (standard)

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB.Supplement

/-- **Polynomial-time samplable distribution families over `{0,1}^n × {0,1}^n`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorems 56
and 58, pp.37–38: "every polynomial-time samplable distribution family `{D_n}_{n∈ℕ}` supported over
`{0,1}^n × {0,1}^n`"; standard, not defined in the paper). `IsPolySampler A q`: on input `1^n` and any
random string `r ∈ {0,1}^{n^q + q}` (randomness tape), the machine `A` halts within `n^q + q` steps and
outputs the encoded pair `tupleEnc [x, y]` of two strings `x, y ∈ {0,1}^n`. The family `D_n` is the
distribution of this output for uniform `r` (`sampProb`). -/
def IsPolySampler (A : Machine) (q : ℕ) : Prop :=
  ∀ (n : ℕ) (r : List Bool), r.length = n ^ q + q → ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
    A.HaltsWith ∅ ⟨List.replicate n true, [], [], r⟩ (n ^ q + q) (bitsSym (tupleEnc [x, y]))

end NKtLB.Supplement


