-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Basic_WindowBounds
-- name    : ConsistentSubmodular_Deterministic_Basic_WindowBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:52.641235+00:00
-- url     : https://prove2.me/theorems/f824d46f-3cab-47a0-bcf4-e7148706d8ca
-- title:
--   Two-type value at stage $j$ for candidates $a,b$: $H_{R_j}(O_a,O_b;s)$
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, arrivals $R_j$ (`arrivals j`), candidates $O_a$ (`candidate a`) and objective $f$. For stages $j,a,b$ and $s\in\mathbb R$ the file defines one quantity.
--
--   - `WindowInstance.pairValue j a b s`: the two-type objective of Appendix B.2.1 with buffer $Q=R_j$ and sets $A=O_a$, $B=O_b$,
--   $$H_{R_j}(O_a,O_b;s)=s(1-s)f(R_j)+(1-s)^2f(R_j\cup O_a)+s^2f(R_j\cup O_b)+s(1-s)f(R_j\cup O_a\cup O_b),$$
--   that is, `twoTypeValue W.objective (W.arrivals j) (W.candidate a) (W.candidate b) s`. It is the sum over the four outcomes of selecting $O_a$ with probability $1-s$ and $O_b$ with probability $s$, independently.
--
--   For $a\ne b$ it equals the mixture value $H_j\big((1-s)\delta_a+s\delta_b\big)$ of the mixture on the edge between the vertices $\delta_a$ and $\delta_b$, and for $a=b$ it is a lower bound for it.
--
--   The definition gives the stage-wise two-type values that appear in the window bounds of Appendix B.1 and in the prefix and suffix bounds of Theorem B.4, and so in the half mixtures that anchor the certificates of Theorem 7 at level $3/4$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/WindowBounds.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Simplex

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The two-type objective `H_{R_j}(O_a, O_b; s)` at stage `j`, summed over the four
outcomes of the two independent type samples. It equals the value of the mixture
`(1 - s) δ_a + s δ_b` when `a ≠ b`, and is a lower bound for it when `a = b`. -/
def pairValue (j a b : Fin (W.lastStage + 1)) (s : ℝ) : ℝ :=
  twoTypeValue W.objective (W.arrivals j) (W.candidate a) (W.candidate b) s

end WindowInstance

end ConsistentSubmodular

end


