-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
-- name    : OAI_Probability_ThorpShuffle_FreshCoins
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:28:03.669045+00:00
-- url     : https://prove2.me/theorems/5f143899-fb55-4282-be88-2c6b8ac1cbcb
-- title:
--   Expected Walsh band energy of the conditional Thorp flow
-- statement:
--   Consider a deck of $2^{d+1}$ cards with positions $Q_{d+1}=\{0,1\}^{d+1}$. A centered state is a pair $v=(B,w)$ consisting of a free marker $B:Q_{d+1}\to\{0,1\}$ and a weight $w:Q_{d+1}\to\mathbb{R}$ with $\sum_xw(x)=0$, $w=0$ off $\{B=1\}$ and $\sum_xw(x)^2\le1$. For a history $\omega$ of $t$ coin vectors $Q_d\to\{0,1\}$, let $w_t^\omega$ be the weight after $t$ conditional Thorp steps, in which weights move with the cards except on pairs of two free positions, where they are averaged. For $u:Q_{d+1}\to\mathbb{R}$ and $j\in\mathbb{N}$, let
--   $$
--   \mathcal B_j(u)=\sum_{\substack{a\in Q_{d+1}\\ a_0=\cdots=a_{j-1}=0}}\Bigl(\sum_{x}u(x)(-1)^{\sum_ia_ix_i}\Bigr)^2
--   $$
--   be the Walsh band energy.
--
--   1. *Expected band energy.* For $t,j\in\mathbb{N}$,
--   $$
--   \mathcal E_{t,j}(v)=\frac{1}{2^{2^dt}}\sum_{\omega}\frac{\mathcal B_j(w_t^\omega)}{2^{d+1}},
--   $$
--   the average over all $2^{2^dt}$ histories of length $t$.
--   2. *Level zero.* $\mathcal E_{t,0}(v)=\mathcal E_t(v)$, the expected energy $\frac{1}{2^{2^dt}}\sum_\omega\sum_xw_t^\omega(x)^2$.
--   3. *Top level.* $\mathcal E_{t,d+1}(v)=0$, because every $w_t^\omega$ has total mass $0$.
--
--   The expected band energies interpolate between the expected energy (level $0$) and zero (level $d+1$). Tracking how energy moves between levels as the coins are revealed one step at a time is the mechanism behind the energy-decay estimates for the conditional Thorp flow.
--
--   **Formalization Note** The definition is `Conditional.expectedBand d v t j`, a uniform `mean` over `History (d + 1) t` of `bandEnergy (d + 1) (iterateState d v t ω).weight j / 2 ^ (d + 1)`. The endpoint identities are the simp lemmas `expectedBand_zero` and `expectedBand_full`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/FreshCoins.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/FreshCoins.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uΩ uι uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def expectedBand (d : ℕ) (v : CenteredState (d + 1)) (t j : ℕ) : ℝ :=
  mean (fun ω : History (d + 1) t =>
    bandEnergy (d + 1) (iterateState d v t ω).weight j / 2 ^ (d + 1))

@[simp] theorem expectedBand_zero (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedBand d v t 0 = expectedEnergy d v t := by
  unfold expectedBand expectedEnergy
  apply mean_congr
  intro ω
  rw [bandEnergy_zero]
  simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin]

@[simp] theorem expectedBand_full (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) :
    expectedBand d v t (d + 1) = 0 := by
  unfold expectedBand
  have hz (ω : History (d + 1) t) :
      bandEnergy (d + 1) (iterateState d v t ω).weight (d + 1) / 2 ^ (d + 1) = 0 := by
    rw [bandEnergy_full, (iterateState d v t ω).mass_zero]
    simp
  simp_rw [hz]
  exact mean_zero

end Conditional

namespace Conditional

end Conditional

end Thorp

end

end OAI


