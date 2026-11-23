-- Prove2me | Definitions.Def_SetOptLattice_Existence_Supplement_SolutionFamilies
-- name    : SetOptLattice_Existence_Supplement_SolutionFamilies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T07:56:13.468704+00:00
-- url     : https://prove2.me/theorems/6209f4c9-508d-4788-baa7-14e95452c3db
-- title:
--   Definition 3.7 — ordinary and plus solution families
-- statement:
--   Let $\Psi$ be a family of extended-real scalar functions on a set $Z$ and $f:X\to\mathcal P(Z,\Psi)$. For $\varepsilon\ge0$, define
--   $$\operatorname{Sol}(f,\varepsilon,\Psi)=\{M\subseteq X\mid M\text{ is an }(\varepsilon,\Psi)\text{-solution}\},$$
--   and define $\operatorname{Sol}(f,\varepsilon+,\Psi)$ using $(\varepsilon+,\Psi)$-solutions. These families use the published solution predicates: every member is a nonempty $(\varepsilon,\Psi)$-infimizer and consists of the corresponding minimizers. The plus family retains the ordinary infimizer tolerance $\varepsilon$.
--
--   The families provide the carriers of the nets in the well-posedness characterization. The definitions are total in the real parameter; the results use only zero or positive tolerances.
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 16, Definition 3.7

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

namespace SetOptLattice.Existence.Supplement

/-- Definition 3.7, p. 16: the family of nonempty ordinary solutions. -/
def Sol {X Z : Type*} (Ψ : Set (Z → EReal)) (f : X → Set Z) (ε : ℝ) : Set (Set X) :=
  {M | IsSolution Ψ f ε M}

/-- Definition 3.7, p. 16: the plus solution still has the ordinary ε-infimizer condition. -/
def SolPlus {X Z : Type*} (Ψ : Set (Z → EReal)) (f : X → Set Z) (ε : ℝ) : Set (Set X) :=
  {M | IsPlusSolution Ψ f ε M}

end SetOptLattice.Existence.Supplement


