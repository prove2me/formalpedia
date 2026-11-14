-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources
-- name    : ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:13:05.793228+00:00
-- url     : https://prove2.me/theorems/29e90e39-f0b8-46c1-b478-7713fbecd497
-- title:
--   Scalar source floors and polynomials $c,n,a,d$ for low-parameter rollback (Appendix B, $3/4$ certificates)
-- statement:
--   Low-parameter rollback in the selector for the $3/4$-certificate construction is controlled by a family of real-valued scalar expressions in the residual data of a parent stage and a child stage of an atomic profile. Here $k$ is the parent parameter, $q$ the child parameter, $d_0$, $d$, $p$ the parent's scalar residuals, and $\delta$, $P$ the child's residual and benchmark.
--
--   - `parentFloor k d₀ d p` is $(3-k)\,p - k\,d - 2(4-k)\,d_0$, the source floor of the parent.
--   - `childPersistence q d p δ P` is $(3-q)\,P - q\,\delta - 4d - (4-q)\,p$, the persistence floor of the child.
--   - `childCapacity q d δ P` is $(4-q)(1-d) - 4\delta - 4d - P$, the capacity floor of the child.
--   - `childIneligibility q d P` is $(4-q)^2 d - (q-2)^2 - qP$, the ineligibility floor of the child.
--   - `cpoly q` is $(3-q)(4-q)^2 - 4q$.
--   - `npoly q` is $(3-q)(q-2)^2$.
--   - `apoly q` is $q(4-q)$.
--   - `dpoly q` is $q^2 - 3q + 3$.
--
--   The file also proves the basic algebraic facts about these expressions, such as sign and monotonicity properties of the polynomials on the parameter range used later, and the chronology inequalities that place the child attainer beyond the parent's credit ceiling.
--
--   These scalar definitions are the vocabulary for the rollback case analysis of the selector, one of the case branches that produce a certificate at level $3/4$ (Theorem 7); the later files in the rollback chain exclude the forbidden source regions by polynomial inequalities in these quantities.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackSources.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope

noncomputable section

namespace ConsistentSubmodular

namespace LowRollback

variable {m aCount : ℕ}

def parentFloor (k d₀ d p : ℝ) : ℝ := (3 - k) * p - k * d - 2 * (4 - k) * d₀

def childPersistence (q d p δ P : ℝ) : ℝ := (3 - q) * P - q * δ - 4 * d - (4 - q) * p

def childCapacity (q d δ P : ℝ) : ℝ := (4 - q) * (1 - d) - 4 * δ - 4 * d - P

def childIneligibility (q d P : ℝ) : ℝ := (4 - q) ^ 2 * d - (q - 2) ^ 2 - q * P

def cpoly (q : ℝ) : ℝ := (3 - q) * (4 - q) ^ 2 - 4 * q

def npoly (q : ℝ) : ℝ := (3 - q) * (q - 2) ^ 2

def apoly (q : ℝ) : ℝ := q * (4 - q)

def dpoly (q : ℝ) : ℝ := q ^ 2 - 3 * q + 3

end LowRollback

end ConsistentSubmodular

end


