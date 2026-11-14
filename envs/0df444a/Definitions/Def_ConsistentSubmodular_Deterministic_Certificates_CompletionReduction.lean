-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_CompletionReduction
-- name    : ConsistentSubmodular_Deterministic_Certificates_CompletionReduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:12:44.561344+00:00
-- url     : https://prove2.me/theorems/0e9e7054-0523-4c0e-8ed6-a2c0a9ac3a2d
-- title:
--   Atomic completion of a compatible profile
-- statement:
--   Let $P$ be a compatible profile on $m+1$ types (objectives $f_t$, residuals $\rho_t(i)=f_t(\{i\})-f_t(\emptyset)$), and assume the normalization $\rho_0(0)=1$ and the optimality condition $\rho_t(i)\le\rho_t(t)$ for all stages $t$ and types $i$.
--
--   - `CompatibleProfile.atomicCompletion`: the finite atomic profile obtained by first triangularizing $P$ into the length array $\ell_{i,j}$ (equal to the loss $\rho_j(i)-\rho_{j+1}(i)$ for $i\le j<m$, to $\rho_m(i)$ for $j=m\ge i$, and to $0$ for $j<i$) and then atomizing that array column by column. It is thus the composition `toTriangularArray` followed by `toAtomic`; its atoms are the atoms of the maximum-coverage realizations of the columns, with pool equal to the column.
--
--   The definition is the bridge between the compatible-profile model, which arises from window instances with arbitrary overlapping physical cores, and the atomic-profile model on which the finite checkpoint theorem is stated. It is used to transfer the checkpoint certificate back to the original window instance in the proof of Theorem 7.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/CompletionReduction.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Triangularization
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicFacts

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace CompatibleProfile

variable {m : ℕ} (P : CompatibleProfile (m + 1))

variable (hinit : P.residual 0 0 = 1)

variable (hopt : ∀ t : Fin (m + 1), ∀ i, P.residual t.val i ≤ P.residual t.val t)

def atomicCompletion := (P.toTriangularArray hinit hopt).toAtomic

end CompatibleProfile

end ConsistentSubmodular

end


