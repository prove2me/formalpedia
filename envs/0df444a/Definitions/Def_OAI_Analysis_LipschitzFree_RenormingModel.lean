-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
-- name    : OAI_Analysis_LipschitzFree_RenormingModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:55:53.545783+00:00
-- url     : https://prove2.me/theorems/fd958a18-a1e1-44b2-a36c-988cfc911d66
-- title:
--   The real sequence space $\ell^1$ as a fixed normed vector space
-- statement:
--   This file fixes the classical Banach space $\ell^1=\ell^1(\mathbb{N};\mathbb{R})$ as a type of its own.
--
--   Its elements are the real sequences $c=(c_n)_{n\in\mathbb{N}}$ (indexed by $n=0,1,2,\dots$) that are absolutely summable, with coordinatewise addition and scalar multiplication and the norm
--   $$\|c\|_1=\sum_{n=0}^{\infty}|c_n| .$$
--   The file equips this type with the normed additive group structure and the real normed-space structure of $\ell^1$.
--
--   Having $\ell^1$ as a separately named type provides a fixed underlying real vector space, with fixed addition and scalar multiplication, on which other equivalent norms can later be placed and compared with $\|\cdot\|_1$ (renormings of $\ell^1$).
--
--   **Formalization Note** `RealL1` is defined as `lp (fun _ : ℕ => ℝ) 1`; its `NormedAddCommGroup` and `NormedSpace ℝ` instances are inherited from Mathlib's `lp` via `inferInstanceAs`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/RenormingModel.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/RenormingModel.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiscreteLipschitzFree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs

namespace OAI

/-!
# Quantitative renorming of real ℓ¹ with fixed vector-space operations
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

variable {M : Type*} [MetricSpace M]

end DiscreteFree
end

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree

def RealL1 : Type := lp (fun _ : ℕ => ℝ) (1 : ENNReal)

noncomputable instance : NormedAddCommGroup RealL1 :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℕ => ℝ) (1 : ENNReal)))

noncomputable instance : NormedSpace ℝ RealL1 :=
  inferInstanceAs (NormedSpace ℝ (lp (fun _ : ℕ => ℝ) (1 : ENNReal)))

end DiscreteFree
end

end OAI


