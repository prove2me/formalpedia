-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
-- name    : OAI_Combinatorics_SharpThreshold_RussoReindex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:26:47.57606+00:00
-- url     : https://prove2.me/theorems/dfd9eb79-6930-4fe0-8902-6f84ba57beae
-- title:
--   Reinserting one coordinate into a configuration
-- statement:
--   For a coordinate $i$, a bit $b$ and a configuration $z$ on the other coordinates $\{j:j\ne i\}$, let $\mathrm{ins}_i(b,z)$ be the configuration with value $b$ at $i$ and $z$ elsewhere. Then
--   $$
--   \mathrm{ins}_i(b,z)(i)=b,\qquad\mathrm{ins}_i(b,z)(j)=z(j)\ (j\ne i),\qquad\mathrm{ins}_i(b,z)^{i\to c}=\mathrm{ins}_i(c,z) .
--   $$
--
--   Splitting off one coordinate this way is the first step of Russo's formula. The derivative of $\mu_p$ in $p$ becomes a sum of pivotal probabilities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/RussoReindex.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/RussoReindex.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance

namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313

variable {ι : Type u} [DecidableEq ι]

/-- Reinsert one Boolean coordinate in a function on the remaining coordinates. -/
def russoInsert (i : ι) (b : Bool) (z : {j : ι // j ≠ i} → Bool) : ι → Bool :=
  (Equiv.funSplitAt i Bool).symm (b, z)

@[simp] theorem russoInsert_self (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) : russoInsert i b z i = b := by
  simp [russoInsert, Equiv.funSplitAt_symm_apply]

@[simp] theorem russoInsert_of_ne (i : ι) (b : Bool)
    (z : {j : ι // j ≠ i} → Bool) (j : ι) (h : j ≠ i) :
    russoInsert i b z j = z ⟨j,h⟩ := by
  simp [russoInsert, Equiv.funSplitAt_symm_apply, h]

@[simp] theorem update_russoInsert (i : ι) (b c : Bool)
    (z : {j : ι // j ≠ i} → Bool) :
    Function.update (russoInsert i b z) i c = russoInsert i c z := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

variable [Fintype ι]

end Problem313

end

end OAI


