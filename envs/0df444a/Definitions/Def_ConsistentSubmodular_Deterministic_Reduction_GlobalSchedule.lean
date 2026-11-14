-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule
-- name    : ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:10:45.086024+00:00
-- url     : https://prove2.me/theorems/a17eba0a-671d-4940-925c-f495e2a46ef6
-- title:
--   Protected programs: global schedule of rounded paths with core and selected sets
-- statement:
--   Let $f$ be an objective on $[n]$, $\kappa$ a core budget, $\beta\in\mathbb R$ a ratio, $C$ a protected clock with start times $s_i$ (windows of length at most $\ell$, buffer scale $b$), and $R,B\in\mathbb N$. Write $X_t$ for the arrived prefix and $\mathrm{OPT}_\kappa(t)=f.\mathrm{prefixOptimum}(\kappa,t)$.
--
--   - `ProtectedPrograms f κ β C R B`: a structure collecting local rounded objects that supply all the data the protected clock needs, including every intermediate physical operation. It consists of set-operation paths $\mathrm{path}_i$ ($i\in\mathbb N$) such that
--     - $\mathrm{path}_0$ starts at $\emptyset$, and each path ends where the next begins;
--     - $\mathrm{len}(\mathrm{path}_i)\le R\,\ell$ and every node has size at most $B$;
--     - every node of $\mathrm{path}_i$ is contained in $X_{s_i}$;
--     - transition values: every node $A$ of $\mathrm{path}_{i+1}$ satisfies $\beta\,\mathrm{OPT}_\kappa(s_{i+1})\le f\bigl(A\cup(X_{s_{i+1}}\setminus X_{s_i})\bigr)$;
--     - checkpoint values: for all $t$ with $s_i\le t\le s_{i+1}$, $\beta\,\mathrm{OPT}_\kappa(t)\le f\bigl(\mathrm{end}(\mathrm{path}_i)\cup(X_t\setminus X_{s_i})\bigr)$.
--   - `ProtectedPrograms.core P t`: the trajectory at time $t$ of the core blocks built by scheduling the paths along the clock.
--   - `ProtectedPrograms.selected P t`: the selected set at time $t$,
--   $$\mathrm{Sel}(t)=\mathrm{core}(t)\cup\bigl(X_t\setminus X_{t-4b}\bigr),$$
--   the core together with the rolling buffer of width $4b$.
--
--   The file also proves that the core and the selected set at time $0$ are empty.
--
--   This is the interface between the local rounding of windows and the global deterministic algorithm: given such programs, the selected sets form the consistent trajectory whose values are compared with the optimum.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/GlobalSchedule.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BlockSchedule
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BufferRecourse

noncomputable section

namespace ConsistentSubmodular

/-- Local rounded objects supply all the data needed by the protected clock.
The conditions include every intermediate physical operation. -/
structure ProtectedPrograms {n b ell : ℕ} (f : Objective n) (κ : ℕ) (β : ℝ)
    {F : ℕ → ℝ} {η : ℝ} (C : ProtectedClock F η b ell) (R B : ℕ) where
  path : ℕ → SetOperationPath n
  initial : (path 0).node 0 = ∅
  joins : ∀ i, (path i).node (path i).length = (path (i + 1)).node 0
  length : ∀ i, (path i).length ≤ R * ell
  cardinality : ∀ i j, ((path i).node j).card ≤ B
  arrived : ∀ i j, (path i).node j ⊆ arrivedPrefix n (C.start i)
  transition : ∀ i j, β * f.prefixOptimum κ (C.start (i + 1)) ≤
    f.value ((path (i + 1)).node j ∪
      (arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i)))
  checkpoint : ∀ i t, C.start i ≤ t → t ≤ C.start (i + 1) →
    β * f.prefixOptimum κ t ≤ f.value ((path i).node (path i).length ∪
      (arrivedPrefix n t \ arrivedPrefix n (C.start i)))

namespace ProtectedPrograms

variable {n b ell κ R B : ℕ} {f : Objective n} {β η : ℝ} {F : ℕ → ℝ}

variable {C : ProtectedClock F η b ell} (P : ProtectedPrograms f κ β C R B)

def core (t : ℕ) : Finset (Fin n) :=
  (C.coreBlocks P.path P.initial P.joins P.length).trajectory t

def selected (t : ℕ) : Finset (Fin n) := P.core t ∪ rollingBuffer n (4 * b) t

@[simp] theorem core_zero : P.core 0 = ∅ := C.coreBlocks_initial _ _ _ _

@[simp] theorem selected_zero : P.selected 0 = ∅ := by simp [selected]

end ProtectedPrograms

end ConsistentSubmodular

end


