-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_CompletionScaling
-- name    : ConsistentSubmodular_Deterministic_Certificates_CompletionScaling
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:13:46.231221+00:00
-- url     : https://prove2.me/theorems/3901cb61-eeb3-4c6f-b6f0-78eecc55ad8a
-- title:
--   Positive-scale normalization of objectives and compatible profiles: $f/c$
-- statement:
--   Let $d\in\mathbb N$.
--
--   - `Objective.divided` $f\,c$: for a nonnegative monotone submodular objective $f$ on subsets of $\{0,\dots,d-1\}$ and a real $c>0$ (hypothesis $0<c$), the objective $f/c$ with value $I\mapsto f(I)/c$. Nonnegativity, monotonicity and the submodular inequality $f(I\cup J)+f(I\cap J)\le f(I)+f(J)$ are preserved because division by $c>0$ preserves order and is additive.
--   - `CompatibleProfile.divided` $P\,c$: for a compatible profile $P$ with objectives $f_t$ (value nondecreasing in $t$, all marginals $f_t(J)-f_t(I)$, $I\subseteq J$, nonincreasing in $t$), the compatible profile with objectives $f_t/c$. Both defining monotonicity properties are inherited, since each side is divided by the same $c>0$.
--
--   Dividing by $c$ divides all residuals, baselines and losses by $c$ and leaves ratios unchanged.
--
--   This normalization is used to rescale a compatible profile so that the residual of the initial stage equals $1$, the standing normalization $\rho_0(0)=1$ of canonical profiles, before applying the atomic completion; the zero-scale case is treated separately.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/CompletionScaling.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_CompletionReduction
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SafePaths

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace Objective

variable {d : ℕ} (f : Objective d)

def divided (c : ℝ) (hc : 0 < c) : Objective d where
  value I := f.value I / c
  nonnegative I := div_nonneg (f.nonnegative I) hc.le
  monotone I J h := (div_le_div_iff_of_pos_right hc).mpr (f.monotone I J h)
  submodular I J := by
    rw [← add_div, ← add_div]
    exact (div_le_div_iff_of_pos_right hc).mpr (f.submodular I J)

end Objective

namespace CompatibleProfile

variable {d : ℕ} (P : CompatibleProfile d)

def divided (c : ℝ) (hc : 0 < c) : CompatibleProfile d where
  objective t := (P.objective t).divided c hc
  values_increase s t hst I := (div_le_div_iff_of_pos_right hc).mpr (P.values_increase s t hst I)
  marginals_decrease s t hst I J hIJ := by
    change (P.objective t).value J / c - (P.objective t).value I / c ≤
      (P.objective s).value J / c - (P.objective s).value I / c
    rw [← sub_div, ← sub_div]
    exact (div_le_div_iff_of_pos_right hc).mpr (P.marginals_decrease s t hst I J hIJ)

end CompatibleProfile

end ConsistentSubmodular

end


