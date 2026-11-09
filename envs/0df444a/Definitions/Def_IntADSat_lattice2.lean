-- Prove2me | Definitions.Def_IntADSat_lattice2
-- name    : IntADSat_lattice2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:31.580179+00:00
-- url     : https://prove2.me/theorems/724c0781-c26a-40a1-a8ed-08926671c3b1
-- title:
--   Two-$A$ lattice $\Lambda_G^{[2]}$
-- statement:
--   Let $A=A_G$, $D=D_G$, $e=(1,\dots,1)^{\mathsf T}$, and let $q$ be the number of distinct degrees of $G$. Then $\Lambda^{[2]}_G\subseteq\mathbb Z^n$ is the integer span of
--
--   $$
--   D^ie,\qquad D^iAD^je,\qquad D^iAD^jAD^\ell e,\qquad 0\le i,j,\ell\le q-1 .
--   $$
--
--   Every generating word has at most two occurrences of $A$ and length at most $3q-1$, so $\Lambda^{[2]}_G\subseteq\Lambda_G$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix B, p.14 (PDF 15)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_degreeSet

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat

/-- The two-`A` lattice `Λ_G^{[2]}` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix B, p.14 (PDF 15)): the integer span of
`Dⁱe`, `DⁱADʲe`, `DⁱADʲADˡe` for `0 ≤ i, j, l ≤ q − 1`, where `q = |𝒟_G|` is the number of
distinct degrees, `A = A_G`, `D = D_G` and `e = (1, …, 1)`. -/
noncomputable def lattice2 {n : ℕ} (G : SimpleGraph (Fin n)) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ
    ({x | ∃ i < (degreeSet G).card, x = (degreeMatrix G ^ i).mulVec (fun _ => 1)} ∪
     {x | ∃ i < (degreeSet G).card, ∃ j < (degreeSet G).card,
        x = (degreeMatrix G ^ i * adjacency G * degreeMatrix G ^ j).mulVec (fun _ => 1)} ∪
     {x | ∃ i < (degreeSet G).card, ∃ j < (degreeSet G).card, ∃ l < (degreeSet G).card,
        x = (degreeMatrix G ^ i * adjacency G * degreeMatrix G ^ j * adjacency G *
          degreeMatrix G ^ l).mulVec (fun _ => 1)})

end IntADSat


