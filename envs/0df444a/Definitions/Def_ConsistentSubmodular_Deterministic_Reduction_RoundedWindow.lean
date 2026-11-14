-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundedWindow
-- name    : ConsistentSubmodular_Deterministic_Reduction_RoundedWindow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:12:41.411203+00:00
-- url     : https://prove2.me/theorems/276e7d82-4da9-461f-8a0b-14bb119dd510
-- title:
--   Rounded window: integral entry and exit set paths for a fractional window
-- statement:
--   Let $W$ be a fractional window for an objective $f$ with old set $\mathrm{old}$, buffers $Q(\cdot)$ (monotone), core budget $\kappa$, grid parameter $N$, duration $T$, initial and terminal sets, level $\alpha$ and segment budget $S$; let $H,L\in\mathbb N$ and write $\mathrm{opt}(Q)=\mathrm{opt}_\kappa(\mathrm{old},Q)=\max\{f(Q\cup B):B\subseteq\mathrm{old},|B|\le\kappa\}$.
--
--   `RoundedWindow W H L` is a structure consisting of two set-operation paths, `entry` $(E_j)$ and `exit` $(X_j)$, with the following properties:
--
--   - $E_0=\text{initial}$, $E_{\text{last}}=X_0$ (the paths join), and $X_{\text{last}}=\text{terminal}$;
--   - total length $\mathrm{len}(E)+\mathrm{len}(X)\le L\kappa$;
--   - all nodes lie in $\mathrm{old}$;
--   - all nodes have size at most $\kappa+\kappa/N+H$;
--   - good values at the endpoints' buffers: $f(Q(0)\cup E_j)\ge(\alpha-2/N)\,\mathrm{opt}(Q(0))$ and $f(Q(T)\cup X_j)\ge(\alpha-2/N)\,\mathrm{opt}(Q(T))$ for every node $j$;
--   - checkpoint tests: for each retained time $r_i$ of $W$, $f(Q(r_i)\cup E_{\text{last}})\ge\alpha\,\mathrm{opt}(Q(r_i))-\mathrm{opt}_\kappa(\mathrm{old},\emptyset)/N$.
--
--   Thus a rounded window is an integral realization, by single-element operations, of the fractional entry and exit paths, losing only an additive $2/N$ in the level and at most $H$ extra elements.
--
--   It is the output of the rounding step of Appendix B and the local object from which protected programs are assembled.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/RoundedWindow.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FractionalWindow
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PhysicalOperationPath
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SamplingScale
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PathSubdivision
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Simplex
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundingBudget
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_WindowCounts

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

structure RoundedWindow {n κ N T S : ℕ} {α : ℝ} {f : Objective n}
    {old initial terminal : Finset (Fin n)} {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
    (W : FractionalWindow f old Q hQ κ N T initial terminal α S) (H L : ℕ) where
  entry : SetOperationPath n
  exit : SetOperationPath n
  entry_initial : entry.node 0 = initial
  join : entry.node entry.length = exit.node 0
  exit_terminal : exit.node exit.length = terminal
  length : entry.length + exit.length ≤ L * κ
  entry_subset : ∀ j, entry.node j ⊆ old
  exit_subset : ∀ j, exit.node j ⊆ old
  entry_card : ∀ j, ((entry.node j).card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N + H
  exit_card : ∀ j, ((exit.node j).card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N + H
  entry_good : ∀ j, (α - 2 / N) * f.bufferedOptimum old (Q 0) κ ≤
    f.value (Q 0 ∪ entry.node j)
  exit_good : ∀ j, (α - 2 / N) * f.bufferedOptimum old (Q T) κ ≤
    f.value (Q T ∪ exit.node j)
  checkpoint_tests : ∀ i, α * f.bufferedOptimum old (Q (W.retained i)) κ -
    f.bufferedOptimum old ∅ κ / N ≤ f.value (Q (W.retained i) ∪ entry.node entry.length)

end ConsistentSubmodular

end


