-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_HalfMixtureCertificate
-- name    : ConsistentSubmodular_Deterministic_Certificates_HalfMixtureCertificate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:10:57.652228+00:00
-- url     : https://prove2.me/theorems/8eb6087c-6882-4190-bf27-8c6d870c5ad4
-- title:
--   Two-segment paths and the envelope $D=\max_j(2K_j-4(1-\beta)P_j)$ of (27) for the half-mixture certificate
-- statement:
--   The elementary certificate at level $1/\sqrt2$ (Appendix B.2.2, Theorem B.4) uses the following notation for a window instance $W$ with stages $0,\dots,m$, benchmark $P_j$ and credits $K_j = 2g_j - r_j$.
--
--   - `PolygonalPath.twoSegments p q r` is the polygonal path with two pieces and nodes $p, q, r$: the segment from $p$ to $q$ followed by the segment from $q$ to $r$.
--   - `WindowInstance.envelopeTerm β j` is the real number $2K_j - 4(1-\beta)\,P_j$ at stage $j$, for a parameter $\beta$.
--   - `WindowInstance.envelope β` is the envelope $D = \max_{0 \le j \le m}\bigl(2K_j - 4(1-\beta)P_j\bigr)$ of (27), the maximum over all stages of `envelopeTerm`.
--
--   The file also proves the basic facts about these objects, such as safety of a segment from pointwise safety on the unit interval and the nonnegativity and monotonicity properties of the residuals.
--
--   In Theorem B.4 the last stage $c$ whose credit $K_c$ reaches $D$ is the partner of $O_0$ in the half mixture; the prefix bound covers stages up to $c$ and the suffix bound the later stages, with a one-segment entry and an exit of at most two segments.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HalfMixtureCertificate.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_WindowBounds
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Paths

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace PolygonalPath

variable {m : ℕ}

/-- The path with the two segments from `p` to `q` and from `q` to `r`. -/
def twoSegments (p q r : Point m) : PolygonalPath m where
  pieces := 2
  node := ![p, q, r]

end PolygonalPath

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The quantity `2 K_j - 4 (1 - β) P_j` whose maximum is the envelope `D` of (27). -/
def envelopeTerm (β : ℝ) (j : Fin (W.lastStage + 1)) : ℝ :=
  2 * W.credit j - 4 * (1 - β) * W.benchmark j

end WindowInstance

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The envelope `D = max_j (2 K_j - 4 (1 - β) P_j)` of (27). -/
def envelope (β : ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty (W.envelopeTerm β)

end WindowInstance

end ConsistentSubmodular

end


