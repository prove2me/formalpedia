-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision
-- name    : ConsistentSubmodular_Deterministic_Reduction_PathSubdivision
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:45.562362+00:00
-- url     : https://prove2.me/theorems/67761160-3866-4358-b828-a6f3829bc34f
-- title:
--   Polygonal paths: $\ell_1$ distance, uniform subdivision into $N$ pieces, and length
-- statement:
--   A polygonal path $\gamma$ in the space of weight vectors $\mathrm{Point}(m)=\mathbb{R}^{\{0,\dots,m\}}$ has `pieces` segments and nodes $\gamma_0,\dots,\gamma_{\text{pieces}}$, with `mix` $(p,q,x)=(1-x)p+xq$ the point at parameter $x$ on the segment from $p$ to $q$.
--
--   - `ConsistentSubmodular.typeL1` $(p,q)$: the $\ell_1$ distance between type vectors,
--   $$\|p-q\|_1=\sum_{i=0}^{m}|p_i-q_i|.$$
--   - `ConsistentSubmodular.PolygonalPath.subdivide` $(\gamma,N)$: the path with $\text{pieces}(\gamma)\cdot N$ pieces obtained by dividing every segment of $\gamma$ into $N$ equal parts. Its node $j$ is
--   $$\mathrm{mix}\big(\gamma_{q},\gamma_{q+1},\ r/N\big),\qquad q=\lfloor j/N\rfloor,\ r=j \bmod N,$$
--   if $q<\text{pieces}(\gamma)$, and the last node of $\gamma$ otherwise. (The division by $N$ uses the real-number convention $x/0=0$.)
--   - `ConsistentSubmodular.PolygonalPath.length` $(\gamma)$: the total $\ell_1$ length
--   $$\sum_{j<\text{pieces}}\|\gamma_{j+1}-\gamma_j\|_1.$$
--
--   The file also proves that the subdivision has `pieces`$\cdot N$ pieces.
--
--   Subdivision lets one refine certificate paths into steps of small $\ell_1$ size, which is needed when rounding the fractional mixture vectors along a path to physical sets (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/PathSubdivision.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Paths

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {m : ℕ}

def typeL1 (p q : Point m) : ℝ := ∑ i, |p i - q i|

namespace PolygonalPath

/-- Uniformly divide every old segment into `N` pieces. -/
def subdivide (γ : PolygonalPath m) (N : ℕ) : PolygonalPath m where
  pieces := γ.pieces * N
  node := fun j => if h : j.val / N < γ.pieces then
    mix (γ.node ⟨j.val / N, by omega⟩) (γ.node ⟨j.val / N + 1, by omega⟩)
      (((j.val % N : ℕ) : ℝ) / N)
    else γ.node (Fin.last γ.pieces)

@[simp] theorem subdivide_pieces (γ : PolygonalPath m) (N : ℕ) :
    (γ.subdivide N).pieces = γ.pieces * N := rfl

def length (γ : PolygonalPath m) : ℝ :=
  ∑ j : Fin γ.pieces, typeL1 (γ.node j.castSucc) (γ.node j.succ)

end PolygonalPath

end ConsistentSubmodular

end


