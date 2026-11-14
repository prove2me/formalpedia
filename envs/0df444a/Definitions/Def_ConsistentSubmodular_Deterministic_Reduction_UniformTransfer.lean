-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_UniformTransfer
-- name    : ConsistentSubmodular_Deterministic_Reduction_UniformTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:11:35.522707+00:00
-- url     : https://prove2.me/theorems/e4d232ca-11fa-4108-848c-a8b486c6bec5
-- title:
--   Transfer clock and uniform rounded programs at level $\alpha-2/N$
-- statement:
--   Let $f$ be an objective on a stream of length $n$ and $p$ a `TransferParameters` $N\,H\,k$ with core $\kappa$, block $b$, candidate count $J$ and interval length $\ell$. Write $F(t)=f^{\mathrm{opt}}_\kappa(t)$ for the prefix optimum (the best value of a set of at most $\kappa$ elements among the first $t$ arrivals), a nonnegative monotone sequence.
--
--   - `transferClock` $f\,p$: the protected clock for $F$ with accuracy $\eta=1/N$, block length $b$ and interval length $\ell$, obtained from `protectedClock` with $J=p.\text{candidates}$ candidates. It is a fixed choice of start times $\mathrm{start}(i)\in[(i+1)b,\,(i+2)b-\ell]$ such that, on $[\mathrm{start}(i),\mathrm{start}(i)+\ell]$, $F$ either grows by a factor at most $1+1/N$ or has already stopped growing relative to its value at $(i+1)b$. Its choice depends only on the fully disclosed optimum sequence.
--   - `HasUniformPrograms` $\alpha\,N\,H\,R$ (a proposition): for all $n$, $k$, every objective $f$ on $n$ elements and every parameter package $p$ for $(N,H,k)$, there exists (the type is nonempty) a `ProtectedPrograms` for $f$ with core $p.\text{core}$, level $\beta=\alpha-2/N$, clock `transferClock` $f\,p$, operation coefficient $R$ and cardinality bound $p.\text{core}+p.\text{block}+H$. The constants $\alpha,N,H,R$ are fixed before $n$, $k$, $f$ and $p$.
--
--   These definitions express the hypothesis that rounded local programs exist with constants independent of the instance, which is what the transfer from rounded windows to a global consistent trajectory consumes in the deterministic reduction (Appendix B.2).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/UniformTransfer.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_StreamingParameters
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule

noncomputable section

namespace ConsistentSubmodular

def transferClock {N H k n : ℕ} (f : Objective n) (p : TransferParameters N H k) :
    ProtectedClock (f.prefixOptimum k) ((1 : ℝ) / N) p.block p.interval :=
  protectedClock (f.prefixOptimum k) (f.prefixOptimum_monotone k)
    (f.prefixOptimum_nonnegative k) p.block p.candidates p.interval
    p.candidates_pos p.fit ((1 : ℝ) / N) (by positivity) p.growth

/-- Rounded local programs at level `α - 2/N`. Their constants are chosen before
every instance parameter. -/
def HasUniformPrograms (α : ℝ) (N H R : ℕ) : Prop :=
  ∀ n k : ℕ, ∀ f : Objective n, ∀ p : TransferParameters N H k,
    Nonempty (ProtectedPrograms f p.core (α - 2 * ((1 : ℝ) / N))
      (transferClock f p) R (p.core + p.block + H))

end ConsistentSubmodular

end


