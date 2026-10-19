-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
-- name    : OAI_Analysis_Littlewood_FiniteRank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:10:03.587529+00:00
-- url     : https://prove2.me/theorems/da28edf5-9718-4e9c-9303-0c645cd0ac51
-- title:
--   Dot-product linear functionals and fibers of maps on finite sets
-- statement:
--   1. **Dot-product functional.** Let $K$ be a field, $\iota$ a finite index set and $a\in K^{\iota}$. The map
--   $$
--   \langle a,\cdot\rangle:K^{\iota}\to K,\qquad x\mapsto\sum_{i\in\iota}a_i x_i,
--   $$
--   is $K$-linear; its value at $x$ is the dot product of $a$ and $x$.
--
--   2. **Fiber.** For a map $f:V\to W$ with $V$ finite and $w\in W$, the fiber is the finite set $f^{-1}(w)=\{v\in V:\ f(v)=w\}$, so that $v\in f^{-1}(w)$ if and only if $f(v)=w$.
--
--   In the packing argument the integer frequency vectors $a_i$ are reduced modulo a prime $q$ and become the functionals $\langle a_i,\cdot\rangle$ on $(\mathbb{Z}/q\mathbb{Z})^m$. If the integer rows are nonzero and pairwise nonparallel, then for every prime $q$ above an explicit threshold (a sum of absolute values of $2\times2$ minors) each pair $y\mapsto(\langle a_i,y\rangle,\langle a_j,y\rangle)$ with $i\ne j$ is surjective onto $(\mathbb{Z}/q\mathbb{Z})^2$. Fibers of a surjective additive map between finite groups all have the same size $|V|/|W|$; these counts give the degrees and conditional frequencies in the slot hypergraph.
--
--   **Formalization Note** `dotForm a` is a `LinearMap` whose underlying function is Mathlib's `dotProduct a`, recorded by the simp lemma `dotForm_apply`. `fiber f w` is `Finset.univ.filter (fun v ↦ f v = w)` with simp lemma `mem_fiber`; in the file the maps are additive homomorphisms or linear maps between finite groups, but the definition of the fiber only uses the underlying function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/FiniteRank.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/FiniteRank.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uK uV uι uW uJ

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Linear
variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

def dotForm {ι : Type uι} [Fintype ι] (a : ι → K) : (ι → K) →ₗ[K] K where
  toFun := dotProduct a
  map_add' := fun x y ↦ dotProduct_add a x y
  map_smul' := fun c x ↦ by simp [dotProduct, Finset.mul_sum, mul_left_comm]

@[simp] lemma dotForm_apply {ι : Type uι} [Fintype ι] (a x : ι → K) :
    dotForm a x=dotProduct a x := rfl

end Linear

section Counting
variable {V : Type uV} {W : Type uW} [AddGroup V] [AddGroup W] [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]

def fiber (f : V → W) (w : W) : Finset V := Finset.univ.filter (fun v ↦ f v=w)

omit [AddGroup V] [AddGroup W] [Fintype W] [DecidableEq V] in
@[simp] lemma mem_fiber {f : V → W} {v : V} {w : W} : v∈fiber f w ↔ f v=w := by
  simp [fiber]

end Counting

section PairCounting
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

end PairCounting
section PrimeRanks

end PrimeRanks

end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI


