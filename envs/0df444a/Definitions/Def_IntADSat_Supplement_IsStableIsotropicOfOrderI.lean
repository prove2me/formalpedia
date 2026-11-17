-- Prove2me | Definitions.Def_IntADSat_Supplement_IsStableIsotropicOfOrderI
-- name    : IntADSat_Supplement_IsStableIsotropicOfOrderI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:51:20.363948+00:00
-- url     : https://prove2.me/theorems/9890beb7-6ff2-44f9-b0f0-74cef2d603d6
-- title:
--   $A,D$-stable isotropic subgroup of $D_\Lambda$ of order $I$
-- statement:
--   A subgroup $S\le D_\Lambda$ is an **$A,D$-stable isotropic subgroup of order $I$** if
--
--   1. $S$ is stable under the endomorphisms of $D_\Lambda$ induced by $A=A_G$ and $D=D_G$: for every $x\in\Lambda^\#$ with $x+\Lambda\in S$, the vectors $Ax$ and $Dx$ lie in $\Lambda^\#$ and their classes lie in $S$;
--   2. $S$ is isotropic: $\beta(S,S)=0$, that is $\langle x,y\rangle\in\mathbb Z$ whenever $x+\Lambda,\ y+\Lambda\in S$;
--   3. $|S|=I=I_G=|\mathbb Z^n/\Lambda_G|$.
--
--   By Lemma S5.1 these subgroups correspond to the $A,D$-stable integral unimodular overlattices of $\Lambda$.
--
--   **Formalization Note** Stability and isotropy are written on representatives in $\Lambda^\#$; $I_G$ is the cardinality of the quotient, as in the base mission.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Lemma S5.1, p.41 (PDF 42); Theorem S5.4, p.42 (PDF 43)

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Definitions.Def_IntADSat_wordLattice
import Definitions.Def_IntADSat_Supplement_discGroup

set_option autoImplicit false
open UniformADProbes.Trace

namespace IntADSat.Supplement

/-- `S ≤ D_Λ` is an **`A, D`-stable isotropic subgroup of order `I`** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma S5.1, p.41 (PDF 42);
Theorem S5.4, p.42 (PDF 43)): `S` is stable under the endomorphisms of `D_Λ` induced by `A` and `D`,
`β(S, S) = 0`, and `|S| = I = I_G`.

**Formalization Note** Stability under the induced endomorphism of `A` is written on representatives:
for every `x ∈ Λ^#` with `x + Λ ∈ S`, the vector `Ax` lies in `Λ^#` and `Ax + Λ ∈ S`; likewise for `D`.
`β(x + Λ, y + Λ) = ⟨x, y⟩ + ℤ`, so `β(S, S) = 0` says `⟨x, y⟩ ∈ ℤ` for representatives of elements of `S`.
`I_G = |ℤⁿ/Λ_G|` is `Nat.card` of the quotient, as in the published base mission. -/
def IsStableIsotropicOfOrderI {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Submodule ℤ (discGroup G)) : Prop :=
  (∀ x : ↥(dualLattice (vecLattice G)), Submodule.mkQ _ x ∈ S →
    ∃ y : ↥(dualLattice (vecLattice G)),
      (y : Fin n → ℚ) = ((adjacency G).map (Int.cast : ℤ → ℚ)).mulVec x ∧ Submodule.mkQ _ y ∈ S) ∧
  (∀ x : ↥(dualLattice (vecLattice G)), Submodule.mkQ _ x ∈ S →
    ∃ y : ↥(dualLattice (vecLattice G)),
      (y : Fin n → ℚ) = ((degreeMatrix G).map (Int.cast : ℤ → ℚ)).mulVec x ∧ Submodule.mkQ _ y ∈ S) ∧
  (∀ x y : ↥(dualLattice (vecLattice G)), Submodule.mkQ _ x ∈ S → Submodule.mkQ _ y ∈ S →
    ∃ z : ℤ, (x : Fin n → ℚ) ⬝ᵥ (y : Fin n → ℚ) = z) ∧
  Nat.card S = Nat.card ((Fin n → ℤ) ⧸ IntADSat.wordLattice G)

end IntADSat.Supplement


