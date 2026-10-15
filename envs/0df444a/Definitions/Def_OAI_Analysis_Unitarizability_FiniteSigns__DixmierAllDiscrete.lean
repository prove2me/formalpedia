-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:18:38.543062+00:00
-- url     : https://prove2.me/theorems/ed16f3ad-0a3e-4302-8819-98a68fbb0b5b
-- title:
--   Signed sums $\sum_j a_j\varepsilon_j$ over the finite space of sign assignments
-- statement:
--   Let $J$ be a finite set. A sign assignment is a function $\sigma:J\to\{\mathrm{true},\mathrm{false}\}$; the $2^{|J|}$ assignments form a finite sample space with equal weights, so probabilities are counts divided by $2^{|J|}$ and expectations are averages over all assignments.
--
--   1. **Sign of a bit.** $\varepsilon(\mathrm{true})=1$ and $\varepsilon(\mathrm{false})=-1$, as real numbers.
--   2. **Signed sum.** For real coefficients $a=(a_j)_{j\in J}$ and an assignment $\sigma$,
--   $$V_a(\sigma)=\sum_{j\in J}a_j\,\varepsilon(\sigma_j).$$
--
--   Under the uniform distribution the signs $\varepsilon(\sigma_j)$ are independent Rademacher variables and $V_a$ is a Rademacher sum. The module proves sub-Gaussian tail bounds in counting form: for $t\ge0$ and real $u$, $\#\{\sigma:V_a(\sigma)>u\}\cdot e^{tu}\le2^{|J|}\exp\bigl(\tfrac{t^2}{2}\sum_{j}a_j^2\bigr)$, and if $\sum_{j}a_j^2=1/k$ with $k>0$ then, for every $u>0$, the proportion of assignments with $|V_a(\sigma)|>u$ is at most $2e^{-ku^2/2}$. Applied to the bilinear tests of random sign matrices, these tails produce frames with good bounds on all small subfamilies.
--
--   **Formalization Note** The definitions are `FiniteSigns.sign : Bool → ℝ` and `FiniteSigns.value a σ`; decidable equality on `J` is supplied classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FiniteSigns.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FiniteSigns.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean__DixmierAllDiscrete

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

/-! Finite independent signs. Expectations are explicit finite sums over all sign
assignments with equal weight. -/
noncomputable section
namespace Dixmier
namespace FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
local instance instDecidableEq_oAI : DecidableEq J := Classical.decEq J

def sign (b : Bool) : ℝ := if b then 1 else -1

def value (a : J → ℝ) (σ : J → Bool) : ℝ := ∑ j, a j * sign (σ j)

end FiniteSigns
end Dixmier

end

end OAI


