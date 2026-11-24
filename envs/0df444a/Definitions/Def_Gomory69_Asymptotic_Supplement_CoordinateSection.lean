-- Prove2me | Definitions.Def_Gomory69_Asymptotic_Supplement_CoordinateSection
-- name    : Gomory69_Asymptotic_Supplement_CoordinateSection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:22:24.011529+00:00
-- url     : https://prove2.me/theorems/b61e2eb1-913e-4e0c-8a3d-80028bcbef7c
-- title:
--   Zero extension and the coordinate subspace E(N)
-- statement:
--   Let $G$ be an Abelian group and $N$ a finite coordinate set. A vector $x\in\mathbb R^N$ is embedded into $\mathbb R^{G^+}$ by the zero extension $j_N$:
--   $$j_N(x)(g)=\begin{cases}x(g)&g\in N,\\0&g\notin N,\end{cases}\qquad E(N)=\{y:\ y(g)=0\text{ for }g\notin N\}.$$
--   Theorems using this embedding require $0\notin N$, so every corner coordinate occurs in the master space. The definition neither identifies the ordinary and zero-excluded hulls nor changes either published hull.
--
--   These maps make the ambient-space identification in the section and vertex assertions explicit.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 475, definition preceding THEOREM 12

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron

namespace Gomory69.Asymptotic.Supplement

/-- Extend a corner vector by zero in all omitted master coordinates (p. 475). -/
def zeroExtend {G : Type*} [AddCommGroup G] [DecidableEq G]
    (N : Finset G) (x : N → ℝ) : Gomory69.Lifting.Plus G → ℝ :=
  fun g => if hg : (g : G) ∈ N then x ⟨g, hg⟩ else 0

/-- The coordinate subspace `E(N)` of p. 475. -/
def coordinateSpace {G : Type*} [AddCommGroup G] [DecidableEq G]
    (N : Finset G) : Set (Gomory69.Lifting.Plus G → ℝ) :=
  {x | ∀ g : Gomory69.Lifting.Plus G, (g : G) ∉ N → x g = 0}

end Gomory69.Asymptotic.Supplement


