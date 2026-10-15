-- Prove2me | Definitions.Def_OAI_Probability_ThorpCompatibility_GridDeficits
-- name    : OAI_Probability_ThorpCompatibility_GridDeficits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T23:40:46.403245+00:00
-- url     : https://prove2.me/theorems/82a92a01-d657-4a1c-b6f5-8b0316625a78
-- title:
--   Entropy deficits of the row and column marginals of a law on the grid
-- statement:
--   Let $Q$ be a law on the grid $\mathcal G_{A,D}$ of pairs $a=(r,c)$, with row permutations $r_i\in S_D$ ($i\in[A]$) and column permutations $c_k\in S_A$ ($k\in[D]$). For a law $P$ on a finite set $\Omega$, write $\Delta(P)=\log|\Omega|-H(P)$ for its uniform deficit.
--
--   1. *Joint row deficit.* $\Delta_{\mathrm{rows}}(Q)=\Delta(\text{law of }r)$, the deficit of the joint law of all row permutations on $(S_D)^{[A]}$.
--   2. *Row deficit.* $\Delta_{\mathrm{row}}(Q)=\sum_{i\in[A]}\Delta(\text{law of }r_i)$, the sum of the deficits of the individual rows on $S_D$.
--   3. *Column deficit.* $\Delta_{\mathrm{col}}(Q)=\sum_{k\in[D]}\Delta(\text{law of }c_k)$, the sum of the deficits of the individual columns on $S_A$.
--   4. *Total heavy mass.* For $H\in\mathbb{R}$,
--   $$
--   \mathrm{HT}_H(Q)=\sum_{k\in[D]}\sum_{i\in[A]}\mathbb{E}_{a\sim Q}\big[\mathrm{hm}_{k,i}(a)\big].
--   $$
--   Here $\mathrm{hm}_{k,i}(a)$ is the heavy mass of the entry $c_k(i)$. It is the predicted probability, given $c_k(0),\dots,c_k(i-1)$, of the values whose predicted probability exceeds $H/(A-i)$.
--
--   All four quantities are nonnegative, and $\Delta_{\mathrm{row}}\le\Delta_{\mathrm{rows}}$ by subadditivity of entropy. Suppose $Q$ is supported on compatible pairs and the clump moment hypothesis holds. The entropy estimate then bounds $\Delta(Q)$ from below by $AD$ minus the exposure error, minus $1$, plus $(1-1000/\log m)\,(\Delta_{\mathrm{row}}+\Delta_{\mathrm{col}})$. Along the way the heavy mass and the clump count are absorbed into the marginal deficits. These deficits are then traded against the weights $w_i$ and $v_k$ in the Gibbs variational principle, which produces the marginal factors with exponent $\theta=1-1000/\log m$.
--
--   **Formalization Note** The definitions are `jointRowDeficit`, `rowDeficit`, `colDeficit` and `heavyTotal`. They are built from `Law.uniformDeficit` of push-forwards of $Q$ and from `entryHeavyMass`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/GridDeficits.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/GridDeficits.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpWeightedCompatibility mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
import Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_UniformSupport
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyColumns

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

noncomputable def jointRowDeficit {A D : ℕ} (Q : Law (Grid A D)) : ℝ :=
  (Q.map Prod.fst).uniformDeficit

noncomputable def rowDeficit {A D : ℕ} (Q : Law (Grid A D)) : ℝ :=
  ∑ i : Fin A, (Q.map (fun a => a.1 i)).uniformDeficit

noncomputable def colDeficit {A D : ℕ} (Q : Law (Grid A D)) : ℝ :=
  ∑ k : Fin D, (Q.map (fun a => a.2 k)).uniformDeficit

noncomputable def heavyTotal {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ) : ℝ :=
  ∑ k : Fin D, ∑ i : Fin A, Q.mean (entryHeavyMass Q H k i)

end ThorpCompatibility

end OAI


