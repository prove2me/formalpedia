-- Prove2me | Definitions.Def_QuantumHMMR_IsUniformFamily
-- name    : QuantumHMMR_IsUniformFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:32.992335+00:00
-- url     : https://prove2.me/theorems/7c3fb316-218a-4f93-992e-9d8e713f0347
-- title:
--   Uniform polynomial-time family of copy tests
-- statement:
--   A family $\{D_i\}_{i \in I}$ of copy tests is **uniform polynomial-time** when there is a polynomial-time classical algorithm (a Turing machine) which, on the word encoding the index $i$ (for example $1^n$), outputs the classical description of $D_i$. Its circuit size is then at most the machine's running time, hence polynomial.
--
--   **Formalization Note** Polynomial time is the published `CookPvsNP.PolyTimeComputable`: a one-tape machine halting within $|x|^k + k$ steps on every input $x$. Numbers in the description are written in binary with an injective self-delimiting code.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 3, p.11

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumHMMR_CopyTest

namespace QuantumHMMR

/-- A uniform polynomial-time family of copy tests (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §3, p.11: "a uniform family of circuits
`{A_n}` … uniform means that there exists a polynomial-time classical algorithm which, on input
`1ⁿ`, outputs a classical description of `A_n`"). The family `D` is indexed by `ι`; the index `i`
is given to the machine as the word `inp i` (for instance `1ⁿ`), and the machine outputs the
binary description `(D i).encode`. The circuit size is then polynomial, being at most the running
time.

**Formalization Note** Polynomial time is the published `CookPvsNP.PolyTimeComputable` (a one-tape
Turing machine halting within `|x|^k + k` steps). The description `CopyTest.encode` writes every
number in binary with a self-delimiting code and is injective, so the machine's output determines
the test. -/
def IsUniformFamily {ι : Type} (inp : ι → List Bool) (dim : ι → ℕ)
    (D : (i : ι) → CopyTest (dim i)) : Prop :=
  ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧ ∀ i, f (inp i) = (D i).encode

end QuantumHMMR


