-- Prove2me | Definitions.Def_OAI_Probability_Localization_History
-- name    : OAI_Probability_Localization_History
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T19:35:12.394106+00:00
-- url     : https://prove2.me/theorems/6a56f982-8560-430a-b078-b2bab9b9c34a
-- title:
--   Discrete $\sigma$-algebra on the letters of a localization log
-- statement:
--   Fix a dimension $n$ and let $\mathcal{D}_n$ be the set of dyadic cells $Q=(J,k)$, with level $J\in\mathbb{N}$ and index vector $k\in\{0,\dots,2^J-1\}^n$, of the cube $\big[-\tfrac{1}{2\sqrt n},\tfrac{1}{2\sqrt n}\big)^n$. A letter is an element of $\mathcal{L}_n=\{\bot\}\cup\mathcal{D}_n$. In the repeated-localization procedure every attempt records a letter: the first heavy cell into which the procedure moves, or the symbol $\bot$ (none) when the current point lies in no first heavy cell. The logs of the procedure are the finite words over $\mathcal{L}_n$.
--
--   The file equips the set of letters with the discrete $\sigma$-algebra, in which every set of letters is measurable:
--
--   $$
--   \mathcal{F}_{\mathcal{L}_n}=2^{\mathcal{L}_n}.
--   $$
--
--   The alphabet $\mathcal{L}_n$ is countable, so a map from a measurable space into $\mathcal{L}_n$ is measurable exactly when each of its fibers is measurable. This criterion is used to prove measurability of the attempt-letter map, of the run of the procedure and of the terminal log. Logs carry the discrete $\sigma$-algebra as well; that instance is part of the base definitions.
--
--   **Formalization Note** Letters are `Letter n = Option (Cell n)`, with `none` playing the role of $\bot$. The instance is `letterMeasurableSpace n`, defined as the top element of the lattice of measurable-space structures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Localization/History.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Localization/History.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianFiniteEntropy mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianFiniteEntropy
import Definitions.Def_OAI_Probability_Localization_Experiment
import Definitions.Def_OAI_Probability_Localization_Cells

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

instance letterMeasurableSpace (n : ℕ) : MeasurableSpace (Letter n) := ⊤

end FiniteEntropy

end RepeatedLocalization

end OAI


