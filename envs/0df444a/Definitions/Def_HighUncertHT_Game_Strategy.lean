-- Prove2me | Definitions.Def_HighUncertHT_Game_Strategy
-- name    : HighUncertHT_Game_Strategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:08.454279+00:00
-- url     : https://prove2.me/theorems/5891521b-a647-4916-b436-95e237366dce
-- title:
--   (8)–(13), pp. 5–8 — Lip(Sim) and the admissible strategies 𝔹ⁿ of the scheduler
-- statement:
--   Let $\mathrm{Sim}=\{x\in[0,1]^L:\sum_\ell x_\ell\le1\}$. The effort space is
--   $$
--   \mathfrak B=\mathrm{Lip}(\mathrm{Sim})=\{\psi:\psi(0)=0,\ (t-s)^{-1}(\psi(t)-\psi(s))\in\mathrm{Sim}\text{ for all }0\le s<t\}.
--   $$
--   Let $\underline{\mathcal A}^n=(\Pi^n\times\mathbb R^L_+)^{\mathbb N}$ be the space of control paths whose distributions lie in the uncertainty classes and whose job sizes are nonnegative. A **strategy** of the server controller is a measurable map $\beta^n$ from control paths to effort paths; it is **admissible**, $\beta^n\in\mathbb B^n$, if for every $\underline a^n\in\underline{\mathcal A}^n$, with $\underline B^n=\beta^n(\underline a^n)$:
--
--   1. $\underline B^n\in\mathfrak B$;
--   2. (9) nonnegativity: $\underline A^n_t-n\underline B^n_t\in\mathbb R^L_+$ for all $t\ge0$;
--   3. (12) work conservation: $\underline B^{\mathrm{tot},n}=\mathrm{id}-\Gamma_2(n^{-1}\underline A^{\mathrm{tot},n}-\mathrm{id})$;
--   4. (13) causality: if $\underline a^n_k=\tilde{\underline a}^n_k$ for all $k\le K$, then $\underline B^n_t=\tilde{\underline B}^n_t$ for all $t\in[0,(K+1)n^{-1})$.
--
--   **Formalization Note** Measurability is for the product σ-algebras: on control paths (with the Giry σ-algebra on probability measures, the Borel σ-algebra of the weak topology) this is the paper's Borel σ-field of the product topology, and on continuous paths it is the Borel σ-field of the u.o.c. topology. A strategy is a map on all control paths and all real times; only its values on $\underline{\mathcal A}^n$ and at times $t\ge0$ are constrained or used (a paper strategy extends by a constant off the measurable set $\underline{\mathcal A}^n$). Causality is also required for $K=0$, where it is implied by (9) and $\underline B^n\ge0$.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, pp. 5–8, definition of 𝔅 = Lip(Sim) (p. 5), (8), (9), (12), (13), definition of 𝔹ⁿ (p. 8)

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting
import Definitions.Def_HighUncertHT_Game_Skorokhod
import Definitions.Def_HighUncertHT_Game_System

namespace HighUncertHT.Game

/-!
Atar, Castiel, Shadmi, arXiv:2204.05733v1, §2.1.1–§2.1.2, pp. 5–8: the effort space
`𝔅 = Lip(Sim)` and the admissible strategies `𝔹ⁿ` of the server controller (SC), (8)–(13).
-/

variable {L : ℕ}

/-- `𝔅 = Lip(Sim)` (p. 5): `ψ(0) = 0` and every increment quotient `(t - s)⁻¹(ψ(t) - ψ(s))`,
`0 ≤ s < t`, lies in `Sim = {x ∈ [0, 1]^L : Σ_ℓ x_ℓ ≤ 1}`. (This forces `ψ` to be continuous,
nonnegative and non-decreasing on `[0, ∞)`, i.e. `ψ ∈ C⁺_{ℝ^L}[0, ∞)`.) Values at negative times are
not constrained and never used. -/
def LipSim (B : EffortPath L) : Prop :=
  (∀ ℓ, B 0 ℓ = 0) ∧
  ∀ s t : ℝ, 0 ≤ s → s < t →
    (∀ ℓ, 0 ≤ (B t ℓ - B s ℓ) / (t - s) ∧ (B t ℓ - B s ℓ) / (t - s) ≤ 1) ∧
    ∑ ℓ, (B t ℓ - B s ℓ) / (t - s) ≤ 1

/-- The paper's sample-path space `𝒜̲ⁿ = (Πⁿ × ℝ^L_+)^ℕ` (p. 7), as a subset of `ControlPath L`. -/
def pathSpace (S : Setting L) (n : ℕ) : Set (ControlPath L) :=
  {a | ∀ i, (∀ ℓ, (a i).1 ℓ ∈ S.cls n ℓ) ∧ ∀ ℓ, 0 ≤ (a i).2 ℓ}

/-- An **admissible strategy** for the `n`-th system, `βⁿ ∈ 𝔹ⁿ` (pp. 7–8): a measurable map from
control paths to effort paths such that for every control path in `𝒜̲ⁿ`

1. the effort path lies in `𝔅 = Lip(Sim)`;
2. (9) nonnegativity: `A̲ⁿ_t - n B̲ⁿ_t ∈ ℝ^L_+` for all `t ≥ 0`;
3. (12) work conservation: `B̲^{tot,n} = id - Γ₂(n⁻¹ A̲^{tot,n} - id)` on `[0, ∞)`;
4. (13) causality: if two control paths agree at their first `K` epochs (paper indices
   `k ≤ K`, here `i < K`), the effort paths agree on `[0, (K + 1)/n)`.

Measurability is for the product (evaluation) σ-algebras. On `𝒜̲ⁿ` (a countable product of
second-countable spaces; `ProbabilityMeasure ℝ` carries the Giry σ-algebra, the Borel σ-algebra of
the weak topology) this is the paper's Borel σ-field of the product topology; on continuous paths
the product σ-algebra is the Borel σ-field of the u.o.c. topology. The map is defined on all of
`ControlPath L` and on all real times; only its values on `𝒜̲ⁿ` and at times `t ≥ 0` matter. -/
def IsAdmissible (S : Setting L) (n : ℕ) (β : ControlPath L → EffortPath L) : Prop :=
  Measurable β ∧
  (∀ a ∈ pathSpace S n, LipSim (β a)) ∧
  (∀ a ∈ pathSpace S n, ∀ t : ℝ, 0 ≤ t → ∀ ℓ, 0 ≤ arrivals n a t ℓ - n * β a t ℓ) ∧
  (∀ a ∈ pathSpace S n, ∀ t : ℝ, 0 ≤ t →
    ∑ ℓ, β a t ℓ = t - skorokhodΓ₂ (fun s => (n : ℝ)⁻¹ * ∑ ℓ, arrivals n a s ℓ - s) t) ∧
  (∀ a ∈ pathSpace S n, ∀ a' ∈ pathSpace S n, ∀ K : ℕ, (∀ i < K, a i = a' i) →
    ∀ t : ℝ, 0 ≤ t → t < ((K : ℝ) + 1) / n → β a t = β a' t)

/-- `𝔹ⁿ`, the set of admissible strategies of the `n`-th system (p. 8). -/
def admissibleStrategies (S : Setting L) (n : ℕ) : Set (ControlPath L → EffortPath L) :=
  {β | IsAdmissible S n β}

end HighUncertHT.Game


