-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
-- name    : OAI_Analysis_Littlewood_IntervalPacking
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:20:27.215279+00:00
-- url     : https://prove2.me/theorems/c32b042d-3c56-4cd9-bc0e-ad5f82dc9df7
-- title:
--   Closed arcs on the circle $\mathbb{R}/\mathbb{Z}$ and sign reflections
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ and write $[x]\in\mathbb{T}$ for the class of $x\in\mathbb{R}$. Signs are Boolean values $e\in\{\mathrm{true},\mathrm{false}\}$.
--
--   1. **Arc.** For a center $c\in\mathbb{T}$ and a length $\ell\in\mathbb{R}$,
--   $$
--   \mathrm{Arc}(c,\ell)=\{c+[\tau]:\ \tau\in\mathbb{R},\ |\tau|\le\ell/2\}\subseteq\mathbb{T},
--   $$
--   the closed arc of length $\ell$ centered at $c$ (empty if $\ell<0$, and the whole circle if $\ell\ge1$).
--
--   2. **Signed lift.** For $x\in\mathbb{R}$, $\sigma_e(x)=x$ if $e$ is true and $\sigma_e(x)=-x$ otherwise.
--
--   3. **Signed circle point.** For $z\in\mathbb{T}$, $\sigma_e(z)=z$ if $e$ is true and $\sigma_e(z)=-z$ otherwise.
--
--   These objects formulate the signed interval packing: given nonzero, pairwise nonparallel integer vectors $a_i\in\mathbb{Z}^J$ and widths $w_i>0$ with $2\sum_i w_i<1$, there are $H\ge1$ and points $\theta_1,\dots,\theta_H\in\mathbb{T}^J$ such that the arcs $\mathrm{Arc}\bigl(\sigma_e(\langle a_i,\theta_h\rangle),\,w_i/H\bigr)$, indexed by the sign $e$, the frequency $i$ and the block $h$, are pairwise disjoint; here $\langle a_i,\theta\rangle=\sum_j a_{ij}\theta_j\in\mathbb{T}$. The arcs are the windows in which the sampled chirps of a Fourier packet are stationary, so their disjointness ensures that at every point of the unit circle at most one stationary-phase term contributes.
--
--   **Formalization Note** `circleInterval c ℓ`, `signedLift e x` and `signedCircle e z` are the three definitions above, on `UnitAddCircle = AddCircle (1 : ℝ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/IntervalPacking.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/IntervalPacking.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters

namespace OAI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

def circleInterval (c : UnitAddCircle) (ℓ : ℝ) : Set UnitAddCircle :=
  {z | ∃ t : ℝ, |t|≤ℓ/2 ∧ z=c+(t : UnitAddCircle)}

def signedLift (e : Bool) (x : ℝ) : ℝ := if e then x else -x

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

def signedCircle (e : Bool) (z : UnitAddCircle) : UnitAddCircle := if e then z else -z

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI


