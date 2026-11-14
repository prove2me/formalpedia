-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FamilyTransfer
-- name    : ConsistentSubmodular_Deterministic_Reduction_FamilyTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:12:41.861149+00:00
-- url     : https://prove2.me/theorems/54379649-686b-4d18-a788-44accdf05156
-- title:
--   Uniform families of rounded windows and bridges at level $\alpha-2/N$
-- statement:
--   Let $\alpha\in\mathbb R$ and $N,H,L\in\mathbb N$.
--
--   - `HasUniformRoundedFamilies` $\alpha\,N\,H\,L$ (a proposition): for every $n$ and $k$, every objective $f$ on $n$ elements and every `TransferParameters` $p$ for $(N,H,k)$, there exists a `RoundedWindowFamily` $W$ for $f$ with core $p.\text{core}$, level $\beta=\alpha-2/N$, clock `transferClock` $f\,p$, cardinality bound $p.\text{core}+p.\text{block}+H$ and operation coefficient $L$, such that the type of `RoundedBridgeFamily` $W$ is nonempty. The constants $\alpha,N,H,L$ do not depend on $n,k,f,p$.
--
--   A rounded window family consists of entry and exit operation paths for each clock interval, and a bridge family consists of paths connecting the exit of one window to the entry of the next. They are described locally, before the physical operation lists are concatenated and before any update is scheduled.
--
--   This proposition is the family-level form of the uniform local hypothesis in the deterministic reduction of Appendix B.2: it states that rounded windows and bridges exist with instance-independent constants.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/FamilyTransfer.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProgramAssembly
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_UniformTransfer

noncomputable section

namespace ConsistentSubmodular

/-- Uniform local rounded windows and bridges at level `α - 2/N`, before
concatenating the physical operation lists or scheduling any update. -/
def HasUniformRoundedFamilies (α : ℝ) (N H L : ℕ) : Prop :=
  ∀ n k : ℕ, ∀ f : Objective n, ∀ p : TransferParameters N H k,
    ∃ W : RoundedWindowFamily f p.core (α - 2 * ((1 : ℝ) / N))
      (transferClock f p) (p.core + p.block + H) L,
      Nonempty (RoundedBridgeFamily W)

end ConsistentSubmodular

end


