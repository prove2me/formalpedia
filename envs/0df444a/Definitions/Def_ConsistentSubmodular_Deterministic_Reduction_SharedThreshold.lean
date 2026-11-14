-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
-- name    : ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:10:17.099195+00:00
-- url     : https://prove2.me/theorems/a3ee18af-5aaf-4648-affd-846d708ff696
-- title:
--   Shared thresholds: one finite law per coordinate realizing nested inclusion probabilities
-- statement:
--   Let $d\in\mathbb{N}$ and $z : \{0,\dots,d-1\}\to\mathbb{R}$ be a vector of target probabilities.
--
--   - `ConsistentSubmodular.SharedThreshold` $z$: a finite shared-threshold realization of $z$, consisting of a number of cells $c$, a finite law $\mu$ on the cells $\{0,\dots,c-1\}$, and an active set $\mathrm{act}(\omega)\subseteq\{0,\dots,d-1\}$ for each cell $\omega$, such that
--     - inclusion: $\Pr_\mu[\,t\in\mathrm{act}(\omega)\,]=z_t$ for every $t$;
--     - nestedness: if $z_s\le z_t$ and $s\in\mathrm{act}(\omega)$ then $t\in\mathrm{act}(\omega)$, for all $\omega$, $s$, $t$.
--
--     So one random cell drives all coordinates $t$ simultaneously, with larger probabilities giving larger active sets (a threshold structure).
--   - `ConsistentSubmodular.sharedThresholdSample` $(T,\omega)(t)$: for each physical element $e\in\{0,\dots,n-1\}$, let $T_e$ be a shared threshold for the vector $t\mapsto z_t(e)$, and let $\omega=(\omega_e)_e$ be an outcome of the product of the cell laws. The sample at index $t$ is
--   $$\{\,e : t\in\mathrm{act}_e(\omega_e)\,\}\subseteq\{0,\dots,n-1\},$$
--   a set in which element $e$ is included with probability $z_t(e)$, independently across $e$, and with the samples for different $t$ nested whenever the probabilities are ordered.
--
--   These objects allow a family of samples, one for each point of a path of fractional vectors, to be coupled through a single experiment, which is needed in the rounding of fractional windows and the comparison of mixtures along a path (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/SharedThreshold.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteMaxCoverage
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProductLaw

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

structure SharedThreshold {d : ℕ} (z : Fin d → ℝ) where
  cellCount : ℕ
  law : FiniteLaw (Fin cellCount)
  active : Fin cellCount → Finset (Fin d)
  inclusion : ∀ t, law.probability (fun ω => t ∈ active ω) = z t
  ordered : ∀ ω s t, z s ≤ z t → s ∈ active ω → t ∈ active ω

variable {n d : ℕ}

def sharedThresholdSample {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e))
    (ω : ∀ e, Fin (T e).cellCount) (t : Fin d) : Finset (Fin n) :=
  FiniteLaw.selectedSet (fun e a => t ∈ (T e).active a) ω

end ConsistentSubmodular

end


