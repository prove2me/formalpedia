-- Prove2me | Definitions.Def_JohnsonApprox_SetCover_Config
-- name    : JohnsonApprox_SetCover_Config
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:26:01.782791+00:00
-- url     : https://prove2.me/theorems/cf568b84-bf5c-4d7d-b52c-98dd62667259
-- title:
--   Configurations, runs and selectable sets of algorithm C1 (Section 5, p. 266)
-- statement:
--   These are the notions in which Lemmas 1 and 2 of Johnson (1974) are stated (p. 266). The only internal variables of C1 that are interrogated when decisions are made are $N$, UNCOV and SET$[i]$.
--
--   1. A **configuration** $K$ of the algorithm is a triple $\langle N_K, \mathrm{UNCOV}_K, \langle \mathrm{SET}_K[1], \dots, \mathrm{SET}_K[N_K]\rangle\rangle$ with
--   $$\bigcup_{i=1}^{N_K} \mathrm{SET}_K[i] = \mathrm{UNCOV}_K.$$
--   2. The **initial configuration** for input $F$ is the configuration after Step 1: UNCOV $= \bigcup_i S_i$ and SET$[i] = S_i$.
--   3. A **run** $R$ from a configuration $K$ is a sequence $R = \langle K(1), j(1), K(2), j(2), \dots, K(t-1), j(t-1), K(t)\rangle$ of alternating configurations and integers such that $K(1) = K$, $\mathrm{UNCOV}_{K(i)} \ne \emptyset$ for $i < t$, $\mathrm{UNCOV}_{K(t)} = \emptyset$, and, for $i < t$, if the algorithm enters Step 2 in configuration $K(i)$ it can choose $j(i)$ at Step 3 (that is, $|\mathrm{SET}_{K(i)}[j(i)]|$ is maximal), and the configuration resulting from Step 4 is $K(i+1)$: $\mathrm{UNCOV}_{K(i+1)} = \mathrm{UNCOV}_{K(i)} - \mathrm{SET}_{K(i)}[j(i)]$ and $\mathrm{SET}_{K(i+1)}[m] = \mathrm{SET}_{K(i)}[m] - \mathrm{SET}_{K(i)}[j(i)]$ for all $m$.
--   4. $\mathrm{Numbers}(R)$ is the set of the $j$'s in the run $R$. A set $M$ of indices is **selectable from $K$** if there is a run $R$ from $K$ with $M = \mathrm{Numbers}(R)$.
--
--   **Formalization Note** $N_K$ is fixed by the index type `ι` (it does not change along a run). A run is encoded by the inductive predicate `IsRun K js`, where `js` is the list $[j(1), \dots, j(t-1)]$; the intermediate configurations are the existentially given `K'` of each `ConfigStep`, which determine each other. `Selectable K M` is `∃ js, IsRun K js ∧ M = js.toFinset`. The covering condition $\bigcup_i \mathrm{SET}_K[i] = \mathrm{UNCOV}_K$ is a field of `Config`.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 266, Section 5 (proof of Theorem 4: configuration, run, Numbers(R), selectable)

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem

namespace JohnsonApprox.SetCover

/-!
Configurations, runs and selectable sets (Johnson 1974, p. 266).
-/

variable {ι α : Type} [Fintype ι] [DecidableEq α]

/-- A configuration `K = ⟨N_K, UNCOV_K, ⟨SET_K[1], …, SET_K[N_K]⟩⟩` of algorithm C1, with
`⋃_{i=1}^{N_K} SET_K[i] = UNCOV_K`. The index type `ι` plays the role of `{1, …, N_K}`. -/
structure Config (ι α : Type) [Fintype ι] [DecidableEq α] where
  UNCOV : Finset α
  SET : ι → Finset α
  union_eq : Finset.univ.biUnion SET = UNCOV

/-- The configuration of C1 after it has been given input `F` and initialized itself via
Step 1: `UNCOV = ⋃ S_i`, `SET[i] = S_i`. -/
def initConfig (S : ι → Finset α) : Config ι α := ⟨ground S, S, rfl⟩

/-- If the algorithm enters Step 2 in configuration `K`, it does not halt
(`UNCOV_K ≠ ∅`), it can choose `j` at Step 3 (`|SET_K[j]|` is maximal), and the resulting
configuration after updating at Step 4 is `K'`. -/
def ConfigStep (K : Config ι α) (j : ι) (K' : Config ι α) : Prop :=
  K.UNCOV ≠ ∅ ∧ (∀ i, (K.SET i).card ≤ (K.SET j).card) ∧
    K'.UNCOV = K.UNCOV \ K.SET j ∧ K'.SET = fun i => K.SET i \ K.SET j

/-- `IsRun K js`: there is a run `R = ⟨K(1), j(1), K(2), …, j(t−1), K(t)⟩` from `K` whose
sequence of chosen integers is `js = [j(1), …, j(t−1)]`: `K(1) = K`, each `K(i+1)` results from
`K(i)` by `ConfigStep` with choice `j(i)` (so `UNCOV_{K(i)} ≠ ∅` for `i < t`), and
`UNCOV_{K(t)} = ∅`. -/
inductive IsRun : Config ι α → List ι → Prop
  | halt (K : Config ι α) : K.UNCOV = ∅ → IsRun K []
  | step (K : Config ι α) (j : ι) (K' : Config ι α) (js : List ι) :
      ConfigStep K j K' → IsRun K' js → IsRun K (j :: js)

variable [DecidableEq ι]

/-- `M` is selectable from `K`: there is a run `R` from `K` with `M = Numbers(R)`, the set of the
`j`'s in `R`. -/
def Selectable (K : Config ι α) (M : Finset ι) : Prop :=
  ∃ js : List ι, IsRun K js ∧ M = js.toFinset

end JohnsonApprox.SetCover


