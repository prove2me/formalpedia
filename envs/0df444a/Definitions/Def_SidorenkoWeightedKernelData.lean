-- Prove2me | Definitions.Def_SidorenkoWeightedKernelData
-- name    : SidorenkoWeightedKernelData
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-08T15:12:32.609375+00:00
-- url     : https://prove2.me/theorems/d908e5a9-8f95-4b38-aec3-5a0155ed86cc
-- title:
--   Finite weighted kernels and the 66-edge incidence moment
-- statement:
--   A finite weighted kernel consists of a positive number of states, a probability vector $p$ on those states, and a symmetric function $W$ with values in $[0,1]$. Its edge mean is
--
--   $$
--   \mu=\sum_{a,b}p_a p_b W(a,b).
--   $$
--
--   For the fixed incidence pattern $H$ with 13 point vertices and 22 face vertices, its pattern moment is
--
--   $$
--   \tau=\sum_{f:V(H)\to\Omega}\left(\prod_{v\in V(H)}p_{f(v)}\right)\prod_{j=0}^{21}\prod_{i\in\mathrm{faces}(j)}W(f(i),f(j)).
--   $$
--
--   Here the point and face arguments of $f$ belong to the corresponding disjoint summands. All assignments, including repeated states, are included. These quantities describe the finite probability kernel used in the symmetrization and random-host stages of the Sidorenko counterexample.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Symmetrization.lean#L125 (SymmetricCounterKernel), together with Types.lean (kernelMean and bipartiteMoment) and RandomHost.lean (sourceMoment_eq_bipartite). This interface reindexes the finite state space by Fin size.

import Mathlib
import Definitions.Def_SidorenkoCounterexample

open scoped BigOperators

namespace OAI.SidorenkoCounterexample

/-- A probability law on a finite space and a symmetric kernel taking values in [0,1]. -/
structure WeightedKernelData where
  size : ℕ
  size_pos : 0 < size
  weight : Fin size → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_total : ∑ a, weight a = 1
  value : Fin size → Fin size → ℝ
  value_symm : ∀ a b, value a b = value b a
  value_nonneg : ∀ a b, 0 ≤ value a b
  value_le_one : ∀ a b, value a b ≤ 1

noncomputable def kernelEdgeMean (K : WeightedKernelData) : ℝ :=
  ∑ a : Fin K.size, ∑ b : Fin K.size, K.weight a * K.weight b * K.value a b

/-- The expectation of the product over all 66 incidence edges of the pattern. -/
noncomputable def kernelPatternMoment (K : WeightedKernelData) : ℝ :=
  ∑ f : PatternVertex → Fin K.size,
    (∏ v : PatternVertex, K.weight (f v)) *
      (∏ j : Fin 22, ∏ i ∈ faces j, K.value (f (.inl i)) (f (.inr j)))

end OAI.SidorenkoCounterexample


