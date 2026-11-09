-- Prove2me | Definitions.Def_DepthOneQExp_spanProj
-- name    : DepthOneQExp_spanProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:48:26.500328+00:00
-- url     : https://prove2.me/theorems/4d1e6ad8-bf62-4b12-ade6-c2edb4205c68
-- title:
--   Orthogonal projector onto $\mathrm{span}\{|a_1\rangle,\dots,|a_5\rangle\}$
-- statement:
--   The orthogonal projector onto $\mathrm{span}\{|a_1\rangle,\dots,|a_5\rangle\}$, which equals
--   $$
--   \sum_{i=1}^5 |b_i\rangle\langle b_i| ,
--   $$
--   where $|b_1\rangle,\dots,|b_5\rangle$ is the Gram–Schmidt orthonormalization of $|a_1\rangle,\dots,|a_5\rangle$ (Eq. (2.43)).
--
--   **Formalization Note** Defined without choosing a basis, as the matrix of the orthogonal projection of $\mathbb C^{N^2}$ onto the span; for every orthonormal basis $|b_i\rangle$ of the span, in particular the Gram–Schmidt one, it equals $\sum_i|b_i\rangle\langle b_i|$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.43), p.13

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_aVec

namespace DepthOneQExp

/-- The orthogonal projector onto `span{|a_1⟩, …, |a_5⟩}` (Anshu–Balasubramanian–Haferkamp–Harrow–
Tan, *Depth-1 expanders on the unitary group and applications*, arXiv:2609.01605, held version
sha256 3c3f8513…aebfd87, Eq. (2.43), p.13): the matrix `Σ_{i=1}^5 |b_i⟩⟨b_i|`, where
`|b_1⟩, …, |b_5⟩` is the Gram–Schmidt orthonormalization of `|a_1⟩, …, |a_5⟩`.

**Formalization Note** Defined basis-free as the matrix of Mathlib's orthogonal (star) projection
of `EuclideanSpace ℂ (Q n × Q n)` onto the span of the five vectors; for any orthonormal basis
`|b_i⟩` of that span (in particular the Gram–Schmidt one) it equals `Σ_i |b_i⟩⟨b_i|`. -/
noncomputable def spanProj (n : ℕ) :
    Matrix (MITMSynthesis.Q n × MITMSynthesis.Q n) (MITMSynthesis.Q n × MITMSynthesis.Q n) ℂ :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := MITMSynthesis.Q n × MITMSynthesis.Q n)).symm
    (Submodule.span ℂ (Set.range fun i : Fin 5 => WithLp.toLp 2 (aVec n i))).starProjection

end DepthOneQExp


