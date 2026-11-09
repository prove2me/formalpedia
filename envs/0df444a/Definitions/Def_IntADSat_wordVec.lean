-- Prove2me | Definitions.Def_IntADSat_wordVec
-- name    : IntADSat_wordVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:26.938936+00:00
-- url     : https://prove2.me/theorems/40577a7c-84a7-4ad2-84f2-8954978c4bcd
-- title:
--   Word vectors $w(A_G,D_G)e$
-- statement:
--   Let $G$ be a simple graph on the vertex set $[n]=\{0,\dots,n-1\}$, let $A=A_G\in\mathbb Z^{n\times n}$ be its adjacency matrix, $e=(1,\dots,1)^{\mathsf T}$, and $D=D_G=\operatorname{diag}(Ae)$ its degree matrix. A **word** is a finite string in two noncommuting letters $a,d$; it is evaluated at $(A,D)$ by replacing $a$ by $A$ and $d$ by $D$ and multiplying, the empty word giving the identity. The **word vector** of $w$ is
--
--   $$
--   w(A,D)\,e\in\mathbb Z^n .
--   $$
--
--   Word vectors are the generators of the adjacency–degree word lattice $\Lambda_G$.
--
--   **Formalization Note** Words and their evaluation are the published `UniformADProbes.Trace.Word` (the free monoid on `Bool`) and `wordEval`, with `false` $\mapsto A$ and `true` $\mapsto D$; `adjacency` and `degreeMatrix` are the published integer matrices of a graph on `Fin n`.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §1, p.1 (PDF 2) and Appendix A, p.11 (PDF 12)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat

/-- The word vector `w(A_G, D_G) e ∈ ℤⁿ` of a word `w` in the two noncommuting letters `a, d`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §1, p.1 (PDF 2) and Appendix A, p.11 (PDF 12)): `A_G` is the integer adjacency matrix of
`G`, `D_G = diag(A_G e)` its degree matrix, and `e = (1, …, 1)`.

**Formalization Note** Vertices are `Fin n` (0-based). Words are the published
`UniformADProbes.Trace.Word = FreeMonoid Bool` evaluated by `wordEval`, with `false ↦ A_G` and
`true ↦ D_G`; the empty word evaluates to the identity, so `wordVec G 1 = e`. -/
noncomputable def wordVec {n : ℕ} (G : SimpleGraph (Fin n)) (w : Word) : Fin n → ℤ :=
  (wordEval (adjacency G) (degreeMatrix G) w).mulVec (fun _ => 1)

end IntADSat


