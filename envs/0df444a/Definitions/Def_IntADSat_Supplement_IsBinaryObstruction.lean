-- Prove2me | Definitions.Def_IntADSat_Supplement_IsBinaryObstruction
-- name    : IntADSat_Supplement_IsBinaryObstruction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:45:30.213677+00:00
-- url     : https://prove2.me/theorems/678f7878-fa8f-46fa-bff7-d55c91e157cd
-- title:
--   Binary obstruction of a graph
-- statement:
--   A vector $v\in\{0,1\}^{V(G)}$ is a **binary obstruction** of $G$ if $v\neq0$ and
--   $$v^{\mathsf T}w(A_G,D_G)e\equiv0\pmod 2\quad\text{for every word }w,$$
--   that is, $v$ is a nonzero vector orthogonal modulo $2$ to all AD word vectors. When $I_G=2$ there is exactly one (Theorem S6.4).
--
--   **Formalization Note** $v$ is a vector over $\mathbb Z/2\mathbb Z$ and the word vectors are reduced modulo $2$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorems S6.4, S6.5, p.44 (PDF 45)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_wordVec

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat.Supplement

/-- `v ∈ {0,1}^{V(G)}` is a **binary obstruction** of `G`: a nonzero vector orthogonal modulo `2` to
every AD word vector, `vᵀ w(A, D)e ≡ 0 (mod 2)` for every word `w`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Theorems S6.4, S6.5, p.44 (PDF 45)).

**Formalization Note** `v` is a vector over `ZMod 2` (the `0/1` vector it represents); the word vectors
are reduced modulo `2` entrywise. -/
def IsBinaryObstruction {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → ZMod 2) : Prop :=
  v ≠ 0 ∧ ∀ w : Word, ∑ i, v i * ((IntADSat.wordVec G w i : ℤ) : ZMod 2) = 0

end IntADSat.Supplement


