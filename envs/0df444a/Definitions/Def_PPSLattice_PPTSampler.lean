-- Prove2me | Definitions.Def_PPSLattice_PPTSampler
-- name    : PPSLattice_PPTSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:33.530266+00:00
-- url     : https://prove2.me/theorems/610e9c90-d4b8-4e60-8d16-2110d47cd7eb
-- title:
--   Probabilistic polynomial-time algorithm with given output laws
-- statement:
--   A family of output laws $(\mathcal D_a)_a$ is computed by a **probabilistic polynomial-time algorithm** if there are a polynomial-time machine $M$ and a polynomial $p$ such that, for every input $a$ with code $x$, $\mathcal D_a$ is exactly the law of $M(x,c)$ for $p(|x|)$ independent fair coins $c$.
--
--   This is the reading of "$x\leftarrow A(y)$ denotes the process of sampling $x$ from the output distribution of $A$ when run on $y$ with randomly chosen coins".
--
--   **Formalization Note** Exact equality is required on every input: a law that is only close to the image of fair coins does not qualify.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3, p.15; §4.1, p.17

import Mathlib
import Definitions.Def_BeyondDS_tup
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace PPSLattice

/-- A **probabilistic polynomial-time algorithm** with output laws `law a`: there are a
polynomial-time machine `M` and a polynomial `p` such that, on every input `a` with code
`x = code a`, the law `law a` **equals** the law of `M(tup [x, c])` for `p(|x|)` uniform coins `c`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3, p.15 ("for any PPT algorithm A, x ← A(y) denotes the process of sampling x from the output
distribution of A when run on y with randomly chosen coins"); §4.1, p.17 ("polynomial time
algorithms").

**Formalization Note.** The law is required to equal the image of finitely many fair coins
exactly, on every input; an algorithm whose law is only close to such an image does not qualify. -/
def PPTSampler {ι : Type} (code : ι → Str) (law : ι → PMF Str) : Prop :=
  ∃ (M : Str → Str) (p : ℕ[X]), PolyTimeComputable M ∧
    ∀ a, law a = (PMF.uniformOfFintype (Fin (p.eval (code a).length) → Bool)).map
      fun c => M (BeyondDS.tup [code a, List.ofFn c])

end PPSLattice


