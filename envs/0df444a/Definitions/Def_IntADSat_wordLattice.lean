-- Prove2me | Definitions.Def_IntADSat_wordLattice
-- name    : IntADSat_wordLattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:29.648684+00:00
-- url     : https://prove2.me/theorems/18a107ed-475c-45e5-9069-95cb2cdbeb06
-- title:
--   Adjacency–degree word lattice $\Lambda_G=\mathbb Z\langle A,D\rangle e$
-- statement:
--   For a simple graph $G$ on $[n]$ with adjacency matrix $A$, degree matrix $D=\operatorname{diag}(Ae)$ and $e=(1,\dots,1)^{\mathsf T}$, the **adjacency–degree word lattice** is
--
--   $$
--   \Lambda_G=\mathbb Z\langle A,D\rangle e=\operatorname{span}_{\mathbb Z}\{\,w(A,D)e : w \text{ a word in } a,d\,\}\subseteq\mathbb Z^n .
--   $$
--
--   The algebra is unital, so $e\in\Lambda_G$ (empty word), and $\Lambda_G$ is the smallest subgroup of $\mathbb Z^n$ containing $e$ and stable under $A$ and $D$. The graph is **integrally AD-saturated** when $\Lambda_G=\mathbb Z^n$.
--
--   **Formalization Note** A $\mathbb Z$-submodule of `Fin n → ℤ`; saturation is `wordLattice G = ⊤`.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §1, p.1 (PDF 2) and Appendix A, p.11 (PDF 12)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_wordVec

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat

/-- The adjacency–degree word lattice `Λ_G = ℤ⟨A, D⟩e = span_ℤ {w(A, D)e : w a word}`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §1, p.1 (PDF 2); Appendix A, p.11 (PDF 12)). `G` is **integrally AD-saturated** when
`wordLattice G = ⊤`, i.e. `Λ_G = ℤⁿ`.

**Formalization Note** The span is over all words, including the empty word (`e ∈ Λ_G`); this is
the smallest subgroup of `ℤⁿ` containing `e` and stable under `A_G` and `D_G` (p.1). -/
noncomputable def wordLattice {n : ℕ} (G : SimpleGraph (Fin n)) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range (wordVec G))

end IntADSat


