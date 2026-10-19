-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_SignCube
-- name    : OAI_Analysis_DiamondDistortion_SignCube
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:31:51.750187+00:00
-- url     : https://prove2.me/theorems/111e7aac-9e3e-4bfc-a4b6-bded3cb26a64
-- title:
--   Sign histories and their uniform average as iterated fair averages
-- statement:
--   This file sets up finite sequences of fair signs (coin flips) and the corresponding expectation.
--
--   1. **Sign histories.** The set $\mathcal{H}_n$ of sign histories of length $n$ is defined by $\mathcal{H}_0=\{\ast\}$ (the empty history) and
--   $$
--   \mathcal{H}_{n+1}=\mathcal{H}_n\times\{\mathrm{false},\mathrm{true}\},
--   $$
--   so a history of length $n+1$ is a history of length $n$ followed by one more sign. Each $\mathcal{H}_n$ is finite and nonempty; it has $2^n$ elements.
--
--   2. **Uniform average.** For $f:\mathcal{H}_n\to\mathbb{R}$ the average $\mathbb{E}_n f$ is defined recursively by
--   $$
--   \mathbb{E}_0 f=f(\ast),\qquad \mathbb{E}_{n+1}f=\mathbb{E}_n\Big(h\mapsto\tfrac12\big(f(h,\mathrm{false})+f(h,\mathrm{true})\big)\Big),
--   $$
--   that is, the most recent sign is averaged out first. Unwinding the recursion, $\mathbb{E}_n f=2^{-n}\sum_{h\in\mathcal{H}_n}f(h)$ is the expectation of $f$ under the uniform probability measure on $\mathcal{H}_n$. The file records $\mathbb{E}_n 0=0$ and $\mathbb{E}_n c=c$ for every constant $c\in\mathbb{R}$.
--
--   Writing the uniform expectation as iterated fair averages makes it convenient for inductions on the number of signs. It is the averaging operator for the random-sign protocols of the diamond-distortion argument, in which a configuration is refined step by step along a history of signs.
--
--   **Formalization Note** `History n` is `Unit` for $n=0$ and the product of `History n` with `Bool` at length $n+1$, with `Fintype` and `Nonempty` instances; `mean n f` is the recursive average, and `mean_zero`, `mean_const` give its values on constant functions. The cardinality $2^n$ and the closed formula for the average are proved separately (`history_card`, `mean_uniform`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/SignCube.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/SignCube.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_DiamondGraph
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateSpace
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_InfimalCost
import Definitions.Def_OAI_Analysis_DiamondDistortion_PathModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_StartModels
import Definitions.Def_OAI_Analysis_DiamondDistortion_CoordinateDual
import Definitions.Def_OAI_Analysis_DiamondDistortion_Incomparable
import Definitions.Def_OAI_Analysis_DiamondDistortion_ModelMaps
import Definitions.Def_OAI_Analysis_DiamondDistortion_EquivalentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_UpperFunction
import Definitions.Def_OAI_Analysis_DiamondDistortion_RecursiveBounds

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace SignCube
abbrev History : ℕ → Type
  | 0 => Unit
  | n+1 => History n × Bool
instance (n : ℕ) : Fintype (History n) := by induction n with | zero => infer_instance | succ n ih => exact inferInstance
instance (n : ℕ) : Nonempty (History n) := by induction n with | zero => infer_instance | succ n ih => exact inferInstance
/-- Expectation for the uniform sign probability, written as iterated fair averages. -/
def mean : (n : ℕ) → (History n → ℝ) → ℝ
  | 0,f => f ()
  | n+1,f => mean n (fun h => (f (h,false)+f (h,true))/2)
@[simp] lemma mean_zero (n : ℕ) : mean n (fun _ => 0)=0 := by
  induction n with | zero => rfl | succ n ih => simpa only [mean,zero_add,zero_div] using ih
@[simp] lemma mean_const (n : ℕ) (c : ℝ) : mean n (fun _ => c)=c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [mean,show (c+c)/2=c by ring] using ih
namespace Protocol
variable {X I : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [Preorder I]
end Protocol
end SignCube

namespace DirectLayers
open SignCube
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Preorder I]

namespace Regular
-- [generator] dropped: variable {A : Midpoint.Heads I X} (hA : Regular A)
-- [generator] dropped: include hA
end Regular

end DirectLayers

namespace SignCube.Protocol
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [Preorder I]
end SignCube.Protocol

end DiamondDistortion

end

end OAI


