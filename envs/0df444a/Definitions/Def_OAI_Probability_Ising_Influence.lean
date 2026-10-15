-- Prove2me | Definitions.Def_OAI_Probability_Ising_Influence
-- name    : OAI_Probability_Ising_Influence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:09:19.572696+00:00
-- url     : https://prove2.me/theorems/7fd05216-a719-4384-a906-49ab8a5e7722
-- title:
--   Influence bound for symmetric nonnegative field perturbations, positive support and two-point correlations
-- statement:
--   Let $V$ be a finite set and $J=(J_{uv})_{u,v\in V}$ a real coupling array, and let $m_o(J,h)=\langle\sigma_o\rangle_{J,h}$ denote the magnetization at $o\in V$ in the Ising measure with Hamiltonian $\sum_{u,v}J_{uv}\sigma_u\sigma_v+\sum_uh_u\sigma_u$. The file defines:
--
--   1. **Influence bound for $J$.** The proposition that for all fields $g,h\in\mathbb{R}^V$ with $h\ge0$ coordinatewise and every site $o\in V$,
--
--      $$m_o(J,g+h)-m_o(J,g-h)\le m_o(J,h)-m_o(J,-h).$$
--
--   2. **Positive support** of a field: $\operatorname{supp}^+(h)=\{u\in V:\ h_u>0\}$.
--
--   3. **Two-point correlation.** $\operatorname{corr}_{J,h}(u,v)=\langle\sigma_u\sigma_v\rangle_{J,h}$.
--
--   The influence bound says that the change of a magnetization caused by switching a nonnegative perturbation from $-h$ to $+h$ is largest when there is no background field $g$: arbitrary real background fields do not increase the influence of the perturbation. For ferromagnetic arrays ($J_{uv}\ge0$) it is proved by induction on the number of sites and on the size of the positive support, and it implies the bound $\operatorname{corr}_{J,g}(u,v)-m_u(J,g)\,m_v(J,g)\le\operatorname{corr}_{J,0}(u,v)$ on truncated correlations.
--
--   **Formalization Note** These are `InfluenceBound J`, `positiveSupport h` and `correlation J h u v` in the namespace `OAI.BufferedIsing.DSS`. `InfluenceBound` is a `Prop`, and $h\ge0$ refers to the pointwise order on `V → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Influence.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Influence.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation
import Definitions.Def_OAI_Probability_Ising_FieldUpdate

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

universe u

variable {V : Type u} [Fintype V]

/-- The nonnegative-increment influence bound for a fixed finite coupling array. -/
def InfluenceBound (J : V → V → ℝ) : Prop :=
  ∀ (g h : V → ℝ), 0 ≤ h → ∀ o : V,
    mean J (g + h) o - mean J (g - h) o ≤ mean J h o - mean J (-h) o

def positiveSupport (h : V → ℝ) : Finset V := Finset.univ.filter (fun u => 0 < h u)

def correlation (J : V → V → ℝ) (h : V → ℝ) (u v : V) : ℝ :=
  average J h (fun σ => sgn (σ u) * sgn (σ v))

end

end BufferedIsing.DSS

end OAI


