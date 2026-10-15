-- Prove2me | Definitions.Def_OAI_Probability_Ising_PinnedMarginal
-- name    : OAI_Probability_Ising_PinnedMarginal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:00:18.223335+00:00
-- url     : https://prove2.me/theorems/16518e0b-54dc-4a4d-b7ed-25d2de2c8a2c
-- title:
--   Contracted pinned Ising weight, pin-induced fields and the pin constant
-- statement:
--   Let $G$ be a finite ferromagnetic graph on $V=\{0,\dots,n-1\}$ whose edges $e$ have endpoints $l(e)\neq r(e)$ and couplings $K_e\ge 0$, with Ising energy $H_h(\sigma)=\sum_eK_e\sigma_{l(e)}\sigma_{r(e)}+\sum_vh_v\sigma_v$ for a field $h\in\mathbb{R}^V$. Let $I,J,F\subseteq V$, let $\tau\in\{-1,+1\}^V$ give the values of the fixed spins on $F$, let $V_F=V\setminus F$, and for $\eta\in\{-1,+1\}^{V_F}$ let $\tau_F\oplus\eta$ be the configuration equal to $\tau$ on $F$ and to $\eta$ off $F$. The file defines:
--
--   1. **Contracted pinned weight.** For $\eta\in\{-1,+1\}^{V_F}$,
--
--      $$\widehat w_{h,\tau}(\eta)=\begin{cases}e^{H_h(\tau_F\oplus\eta)},&\eta\text{ constant on }I\setminus F\text{ and constant on }J\setminus F,\\ 0,&\text{otherwise.}\end{cases}$$
--
--   2. **Pin-induced field.** For a kept vertex $v\in V_F$,
--
--      $$h^{F,\tau}_v=h_v+\sum_{e:\ l(e)=v,\ r(e)\in F}K_e\,\tau_{r(e)}+\sum_{e:\ r(e)=v,\ l(e)\in F}K_e\,\tau_{l(e)} .$$
--
--   3. **Pin constant.** The part of the energy that involves fixed sites only,
--
--      $$C^{F}_{h,\tau}=\sum_{e:\ l(e)\in F,\ r(e)\in F}K_e\,\tau_{l(e)}\tau_{r(e)}+\sum_{v\in F}h_v\,\tau_v .$$
--
--   The contracted pinned weight is the actual arbitrary-field model with pins, restricted to configurations that are constant on the kept part of $I$ and on the kept part of $J$. It retains the original field and all bonds to the fixed sites, in contrast with the zero-field comparison weight of the vertex-deleted graph. The induced field and the pin constant make the elimination of the fixed spins exact: $H_h(\tau_F\oplus\eta)=C^F_{h,\tau}+H^F(\eta)+\sum_{v\in V_F}h^{F,\tau}_v\eta_v$, where $H^F(\eta)=\sum_{e:\,l(e),r(e)\notin F}K_e\eta_{l(e)}\eta_{r(e)}$ is the zero-field energy of the graph with $F$ deleted. Thus pinning amounts to deleting $F$ and adding the finite fields $h^{F,\tau}$, while the constant $C^F_{h,\tau}$ cancels from all normalized quantities.
--
--   **Formalization Note** The Lean names are `contractedPinnedWeight G h I J F τ η`, `pinField G h F τ v` and `pinConstant G h F τ`. The class condition is `Respects (comparisonSetoid G I J F ∅)`, which is equivalent to constancy on the kept vertices of $I$ and on those of $J$. Edges are summed over their indices, so parallel edges contribute separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/PinnedMarginal.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/PinnedMarginal.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- The actual contracted marginal retains arbitrary fields and all effects
of the common pins. It is distinct from the zero-field comparison weight. -/
noncomputable def contractedPinnedWeight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n)
    (σ : KeptVertex F → Bool) : ℝ :=
  if Respects (comparisonSetoid G I J F ∅) σ then weight G h (pinExtension F τ σ) else 0

/-- The finite-field contribution induced by the actual prescribed spins.
Neither these induced fields nor the original fields survive in `qZero`. -/
noncomputable def pinField {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (v : KeptVertex F) : ℝ :=
  h v + (∑ e, if G.left e = v.val ∧ G.right e ∈ F then
    G.coupling e * spin (τ (G.right e)) else 0) +
    ∑ e, if G.right e = v.val ∧ G.left e ∈ F then
      G.coupling e * spin (τ (G.left e)) else 0

/-- Field and bond terms depending only on fixed sites. They cancel from
all normalized laws, but recording them makes the elimination exact. -/
noncomputable def pinConstant {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) : ℝ :=
  (∑ e, if G.left e ∈ F ∧ G.right e ∈ F then
    G.coupling e * spin (τ (G.left e)) * spin (τ (G.right e)) else 0) +
    ∑ v ∈ F, h v * spin (τ v)

end BufferedIsing

end OAI


