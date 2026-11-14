-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackExclusions
-- name    : ConsistentSubmodular_Deterministic_Certificates_LowRollbackExclusions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:14:13.568038+00:00
-- url     : https://prove2.me/theorems/31171d54-f0d2-4417-8aa4-3a50360d25a4
-- title:
--   Univariate polynomial certificates $S_A,S_B,S_D,S_E,S_R,S_\beta,S_L,S_S,S_J$ excluding low-rollback source regions
-- statement:
--   The exclusion of the forbidden source regions in low-parameter rollback is certified by explicit polynomials in the child parameter $q$ and the parent parameter $k$, built from the polynomials $c(q)=$ `cpoly q`, $n(q)=$ `npoly q`, $a(q)=$ `apoly q` of the source floors. All are real-valued functions.
--
--   - `SA q` is $n(q) + 2c(q) + 2a(q)$.
--   - `SB q` is $9c(q) + 3a(q)$.
--   - `SD q` is $4c(q) + 3a(q)$.
--   - `SE q` is $5c(q) + 3a(q)$.
--   - `SR k q` is $(3-k)\,c(q) - k\,a(q)$.
--   - `Sbeta k q` is $(9-4k)\,c(q) - 3k\,a(q)$.
--   - `SL k q` is $S_\beta(k,q) - k\,c(q)$.
--   - `SS k q` is $k^2 n(q) - S_R(k,q)\,(2k-3)$.
--   - `SJ k q` is the discriminant-type expression
--   $$S_J(k,q) = \bigl(S_E^2 - 4 S_D S_A\bigr)k^2 + \bigl(36\,c\,S_A + 4 S_D S_B - 18\,c\,S_E - 4 S_E^2\bigr)k - 27\,c^2,$$
--   where $c = c(q)$ and $S_A,S_B,S_D,S_E$ are evaluated at $q$.
--
--   The file also proves the exclusion theorem and its auxiliary sign facts: from exact parent strong credit, failed credit and the child attaining-row floor, both forbidden source regions are impossible.
--
--   These polynomials are the univariate certificates that close the low-parameter branch of the rollback analysis in the selector for the $3/4$ clairvoyant certificates (Theorem 7).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackExclusions.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

set_option maxHeartbeats 1500000

namespace ConsistentSubmodular.LowRollback

def SA (q : ℝ) := npoly q + 2 * cpoly q + 2 * apoly q

def SB (q : ℝ) := 9 * cpoly q + 3 * apoly q

def SD (q : ℝ) := 4 * cpoly q + 3 * apoly q

def SE (q : ℝ) := 5 * cpoly q + 3 * apoly q

def SR (k q : ℝ) := (3 - k) * cpoly q - k * apoly q

def Sbeta (k q : ℝ) := (9 - 4 * k) * cpoly q - 3 * k * apoly q

def SL (k q : ℝ) := Sbeta k q - k * cpoly q

def SS (k q : ℝ) := k ^ 2 * npoly q - SR k q * (2 * k - 3)

def SJ (k q : ℝ) :=
  ((SE q) ^ 2 - 4 * SD q * SA q) * k ^ 2+
  (36 * cpoly q * SA q + 4 * SD q * SB q - 18 * cpoly q * SE q - 4 * (SE q) ^ 2) * k - 27 * (cpoly q) ^ 2

end ConsistentSubmodular.LowRollback


