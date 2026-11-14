-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProgramAssembly
-- name    : ConsistentSubmodular_Deterministic_Reduction_ProgramAssembly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:11:38.854429+00:00
-- url     : https://prove2.me/theorems/7b1f12be-6ffb-4900-bbb4-8cde0e06ffb6
-- title:
--   Rounded window family and rounded bridge family along a protected clock
-- statement:
--   Let $f$ be an objective on $[n]$, $\kappa$ a core budget, $\beta$ a ratio, $C$ a protected clock with start times $s_i$, and $B,L\in\mathbb N$. Write $X_t$ for the arrived prefix, $D_i=X_{s_{i+1}}\setminus X_{s_i}$ for the elements arriving in window $i$, and $\mathrm{OPT}_\kappa(t)=f.\mathrm{prefixOptimum}(\kappa,t)$.
--
--   - `RoundedWindowFamily f κ β C B L`: for every window index $i$, a pair of set-operation paths `entry i` $(E^i_j)$ and `exit i` $(X^i_j)$ such that
--     - the paths join: the last node of $E^i$ is the first node of $X^i$; the first node of $E^i$ has size at most $\kappa$;
--     - all nodes have size at most $B$ and are contained in $X_{s_i}$;
--     - total length $\mathrm{len}(E^i)+\mathrm{len}(X^i)\le L\kappa$;
--     - entry value: $\beta\,\mathrm{OPT}_\kappa(s_i)\le f(E^i_j)$ for all $j$;
--     - exit value: $\beta\,\mathrm{OPT}_\kappa(s_{i+1})\le f(X^i_j\cup D_i)$ for all $j$;
--     - checkpoint value: for $s_i\le t\le s_{i+1}$, $\beta\,\mathrm{OPT}_\kappa(t)\le f\bigl(\mathrm{end}(E^i)\cup(X_t\setminus X_{s_i})\bigr)$.
--   - `RoundedBridgeFamily W`: for a rounded window family $W$, paths $\mathrm{path}_i$ ($i\in\mathbb N$) bridging consecutive windows: $\mathrm{path}_i$ starts at the final node of the exit path of window $i$ and ends at the first node of the entry path of window $i+1$; every node has size at most $B$ and lies in $X_{s_{i+1}}$; the length is at most $L\kappa$; and $\beta\,\mathrm{OPT}_\kappa(s_{i+1})\le f(A\cup D_i)$ for every node $A$.
--
--   These families package the output of the window rounding (Appendix B) so that, together with the bridges, they can be concatenated into the protected programs of the global schedule.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ProgramAssembly.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_PhysicalOperationPath

noncomputable section

namespace ConsistentSubmodular

structure RoundedWindowFamily {n b ell : ℕ} (f : Objective n) (κ : ℕ) (β : ℝ)
    {F : ℕ → ℝ} {η : ℝ} (C : ProtectedClock F η b ell) (B L : ℕ) where
  entry : ℕ → SetOperationPath n
  exit : ℕ → SetOperationPath n
  join : ∀ i, (entry i).node (entry i).length = (exit i).node 0
  initial_card : ∀ i, ((entry i).node 0).card ≤ κ
  entry_card : ∀ i j, ((entry i).node j).card ≤ B
  exit_card : ∀ i j, ((exit i).node j).card ≤ B
  entry_arrived : ∀ i j, (entry i).node j ⊆ arrivedPrefix n (C.start i)
  exit_arrived : ∀ i j, (exit i).node j ⊆ arrivedPrefix n (C.start i)
  length : ∀ i, (entry i).length + (exit i).length ≤ L * κ
  entry_value : ∀ i j, β * f.prefixOptimum κ (C.start i) ≤ f.value ((entry i).node j)
  exit_value : ∀ i j, β * f.prefixOptimum κ (C.start (i + 1)) ≤
    f.value ((exit i).node j ∪
      (arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i)))
  checkpoint_value : ∀ i t, C.start i ≤ t → t ≤ C.start (i + 1) →
    β * f.prefixOptimum κ t ≤ f.value ((entry i).node (entry i).length ∪
      (arrivedPrefix n t \ arrivedPrefix n (C.start i)))

structure RoundedBridgeFamily {n b ell κ B L : ℕ} {f : Objective n} {β η : ℝ}
    {F : ℕ → ℝ} {C : ProtectedClock F η b ell}
    (W : RoundedWindowFamily f κ β C B L) where
  path : ℕ → SetOperationPath n
  initial : ∀ i, (path i).node 0 = (W.exit i).node (W.exit i).length
  terminal : ∀ i, (path i).node (path i).length = (W.entry (i + 1)).node 0
  cardinality : ∀ i j, ((path i).node j).card ≤ B
  arrived : ∀ i j, (path i).node j ⊆ arrivedPrefix n (C.start (i + 1))
  length : ∀ i, (path i).length ≤ L * κ
  value : ∀ i j, β * f.prefixOptimum κ (C.start (i + 1)) ≤
    f.value ((path i).node j ∪
      (arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i)))

end ConsistentSubmodular

end


