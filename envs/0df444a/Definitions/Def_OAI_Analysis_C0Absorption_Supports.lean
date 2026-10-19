-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Supports
-- name    : OAI_Analysis_C0Absorption_Supports
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:08:46.450836+00:00
-- url     : https://prove2.me/theorems/78642c77-b271-4ea2-adb8-b557e93ee3a2
-- title:
--   Radius localization of cylinder bases
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. $c_0$ is the Banach space of real sequences tending to zero with the sup norm, $B$ is its closed unit ball, and for a finite set $I$ of coordinates the cube $[-1,1]^I$ is the image of $B$ under restriction to $I$. For $s\in c_0$, $\tau_N(s)=\sup_{i>N}|s_i|$ is the size of its tail after coordinate $N$.
--
--   A radius localization of a family of cylinder bases specifies which indices are terminal and assigns each index a first coordinate $k_\gamma$. It requires:
--
--   1. for each band bound $j$ and $N$, only finitely many indices with band at most $j$ are terminal or have $k_\gamma\le N$;
--   2. for non-terminal $\gamma$ and $N<k_\gamma$, the tail on the support of the base function is at least the band length:
--   $$
--   \ell_{j_\gamma}\le\tau_N\bigl(\mathrm{ext}(x)\bigr)\qquad\text{for }x\in\operatorname{supp}(\mathrm{base}_\gamma).
--   $$
--
--   So non-terminal base functions live away from sequences with small tails.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Supports.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Supports.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

variable {Γ : Type*} {B : CylinderBases Γ}

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

structure RadiusLocalization {Γ : Type*} (B : CylinderBases Γ) where
  terminal : Γ → Prop
  firstCoordinate : Γ → ℕ
  finite_exceptions : ∀ j N, {γ | B.band γ ≤ j ∧ (terminal γ ∨ firstCoordinate γ ≤ N)}.Finite
  base_radius : ∀ γ, ¬terminal γ → ∀ N, N < firstCoordinate γ →
    ∀ x ∈ tsupport (B.base γ), B.ell (B.band γ) ≤ tau N (cubeExtend (B.coordinates γ) x).val

namespace RadiusLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : RadiusLocalization B)

end RadiusLocalization
end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

end OAI


