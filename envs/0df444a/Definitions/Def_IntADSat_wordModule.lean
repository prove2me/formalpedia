-- Prove2me | Definitions.Def_IntADSat_wordModule
-- name    : IntADSat_wordModule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:45.82489+00:00
-- url     : https://prove2.me/theorems/cfa3479e-89e6-4e4f-aae1-09c4e250e097
-- title:
--   Cyclic word module $R\langle A,D\rangle e$ (e.g. $M_p(G)$, $M_{\mathbb Q}(G)$)
-- statement:
--   Let $R$ be a commutative ring and $G$ a simple graph on $[n]$. Reduce the integer adjacency matrix $A_G$ and degree matrix $D_G$ entrywise into $R$, obtaining $\bar A,\bar D$, and let $\bar e=(1,\dots,1)\in R^n$. The **word module** is the $R$-span
--
--   $$
--   R\langle \bar A,\bar D\rangle\bar e=\operatorname{span}_R\{\,w(\bar A,\bar D)\bar e : w \text{ a word}\,\}\subseteq R^n .
--   $$
--
--   For $R=\mathbb F_p=\mathbb Z/p\mathbb Z$ this is $M_p(G)=\mathbb F_p\langle A,D\rangle e$ (the graph is **$p$-AD-saturated** when $M_p(G)=\mathbb F_p^n$); for $R=\mathbb Q$ it is $M_{\mathbb Q}(G)$, whose dimension is $r_G$ (the graph is **AD-full** when $r_G=n$).
--
--   **Formalization Note** The reduction is `Matrix.map Int.cast`, so the diagonal of $\bar D$ holds the degrees modulo $p$. The span includes the empty word, so $\bar e$ belongs to the module.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix A, p.11 (PDF 12), Definition A.1 and the display defining $M_{\mathbb Q}(G)$

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat

/-- The cyclic word module `R⟨A, D⟩e` over a commutative ring `R`: the `R`-span of the vectors
`w(Ā, D̄)ē`, where `Ā`, `D̄` are the adjacency and degree matrices of `G` reduced into `R`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix A, p.11 (PDF 12)). For `R = ZMod p` this is `M_p(G) = 𝔽_p⟨A, D⟩e`; for `R = ℚ`
it is `M_ℚ(G) = ℚ⟨A, D⟩e`, whose dimension is `r_G`.

**Formalization Note** The matrices are reduced entrywise from the integer matrices by `Int.cast`
(so the diagonal of `D̄` holds the degrees modulo `p`), and the span is over all words including
the empty one. -/
noncomputable def wordModule (R : Type) [CommRing R] {n : ℕ} (G : SimpleGraph (Fin n)) :
    Submodule R (Fin n → R) :=
  Submodule.span R (Set.range fun w : Word =>
    (wordEval ((adjacency G).map (Int.cast : ℤ → R)) ((degreeMatrix G).map (Int.cast : ℤ → R)) w).mulVec
      (fun _ => 1))

end IntADSat


