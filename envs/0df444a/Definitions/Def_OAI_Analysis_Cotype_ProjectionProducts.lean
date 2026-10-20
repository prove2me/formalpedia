-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
-- name    : OAI_Analysis_Cotype_ProjectionProducts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:36:15.208565+00:00
-- url     : https://prove2.me/theorems/55dfa1d1-d8e8-4102-b954-6c501502de9f
-- title:
--   Ordered products of operators
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $P_1,\dots,P_n$ be bounded operators on $X$.
--
--   1. **Product.** $\prod P=P_1P_2\cdots P_n$, with the empty product equal to $1$.
--   2. **Subset products.** For $\varepsilon\in\{0,1\}^n$,
--   $$
--   P_\varepsilon=\prod_i\bigl(P_i\text{ if }\varepsilon_i=1,\ \text{else }1\bigr).
--   $$
--   3. **Commutation.** If each $P_i$ commutes with $Q$, so does the product, and a product of identities is $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionProducts.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionProducts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def projectionProduct : {n : ℕ} → (Fin n → X →L[ℝ] X) → X →L[ℝ] X
  | 0, _ => 1
  | _+1, P => P 0 * projectionProduct (fun i => P i.succ)

def projectionSubset {n : ℕ} (P : Fin n → X →L[ℝ] X) (ε : Cube n) : X →L[ℝ] X :=
  projectionProduct (fun i => if ε i then P i else 1)

theorem projectionProduct_commute {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (Q : X →L[ℝ] X) (h : ∀ i, Commute (P i) Q) :
    Commute (projectionProduct P) Q := by
  induction n with
  | zero => exact Commute.one_left Q
  | succ n ih => exact (h 0).mul_left (ih _ (fun i => h i.succ))

theorem projectionProduct_one (n : ℕ) :
    projectionProduct (fun _ : Fin n => (1 : X →L[ℝ] X)) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [projectionProduct, ih]

end Cotype

end

end OAI


