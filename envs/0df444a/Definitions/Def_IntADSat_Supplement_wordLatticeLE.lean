-- Prove2me | Definitions.Def_IntADSat_Supplement_wordLatticeLE
-- name    : IntADSat_Supplement_wordLatticeLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:41:59.992279+00:00
-- url     : https://prove2.me/theorems/ca2c2298-a146-42a5-b95d-401d08ec16c0
-- title:
--   Truncated word lattice $\Lambda_t$
-- statement:
--   For a graph $G$ with adjacency matrix $A$, degree matrix $D$ and all-ones vector $e$, and $t\ge0$,
--   $$\Lambda_t=\sum_{|w|\le t}\mathbb Z\,w(A,D)e\ \subseteq\ \mathbb Z^n,$$
--   the integer span of the word vectors of words of length at most $t$ in the two letters $a,d$ (the empty word, of length $0$, evaluates to the identity, so $\Lambda_0=\mathbb Z e$). Its rational span is $M_t=\mathbb Q\Lambda_t$. The full word lattice $\Lambda_G$ is the union of the increasing chain $\Lambda_0\subseteq\Lambda_1\subseteq\cdots$; Theorem A.6 bounds the step at which it stabilizes.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), §A.2, p.12 (PDF 13)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_wordVec

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat.Supplement

/-- The truncated word lattice `Λ_t = Σ_{|w| ≤ t} ℤ w(A, D)e`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §A.2, p.12 (PDF 13)). Its rational span is `M_t = ℚΛ_t`.

**Formalization Note** `|w|` is `FreeMonoid.length`, the number of letters; the empty word (length
`0`) is included, so `Λ_0 = ℤe`. -/
noncomputable def wordLatticeLE {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) :
    Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ {x | ∃ w : Word, w.length ≤ t ∧ x = IntADSat.wordVec G w}

end IntADSat.Supplement


