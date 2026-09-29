-- Prove2me | Definitions.Def_JohnsonApprox_ExactCover_C2
-- name    : JohnsonApprox_ExactCover_C2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:30:08.025975+00:00
-- url     : https://prove2.me/theorems/d128f9cb-640c-48e9-8fc9-f3e03cd44e80
-- title:
--   Algorithm C2: the overlap-ratio greedy, its choosable outputs and its cumulative overlap (Section 6)
-- statement:
--   Algorithm C2 of Johnson (1974), Section 6, verbatim:
--
--   1. Set SUB $= \emptyset$, LEFT $= F$, UNCOV $= \bigcup_{S\in F} S$.
--   2. If UNCOV $= \emptyset$, halt and return SUB.
--   3. Let $S' \in$ LEFT be that set $S$ which minimizes $\mathrm{Ratio}(S) = |S - \mathrm{UNCOV}|/|S \cap \mathrm{UNCOV}|$.
--   4. Set SUB $=$ SUB $\cup \{S'\}$, UNCOV $=$ UNCOV $- S'$, LEFT $=$ LEFT $- \{S'\}$.
--   5. Go to 2.
--
--   The paper allows algorithms that are "not always completely determined, [so] more than one solution may be choosable for a given input" (p. 258). Accordingly C2 is a nondeterministic process on states (SUB, LEFT, UNCOV):
--
--   - in state $\sigma$ with UNCOV $\neq \emptyset$, C2 **may choose** $S_i$ when $i \in$ LEFT, $S_i$ meets UNCOV, and for every $j \in$ LEFT with $S_j \cap \mathrm{UNCOV} \neq \emptyset$
--   $$|S_i - \mathrm{UNCOV}|\cdot|S_j \cap \mathrm{UNCOV}| \le |S_j - \mathrm{UNCOV}|\cdot|S_i \cap \mathrm{UNCOV}|,$$
--   that is, $\mathrm{Ratio}(S_i) \le \mathrm{Ratio}(S_j)$; any minimizer may be chosen;
--   - a **step** performs Step 4 for such an $i$;
--   - a subcover $M$ is **choosable** by C2 on $F$ when some finite sequence of steps from the initial state reaches a halting state (UNCOV $= \emptyset$) with SUB $= M$.
--
--   For the analysis the paper defines, for a run of C2, "the overlap ov(S) [as] the value of $|S - \mathrm{UNCOV}|$ when $S$ was added to SUB by C2", and the cumulative overlap $\mathrm{OV}(F_1) = \sum_{S \in F_1} \mathrm{ov}(S)$ (p. 271). The relation $\mathrm{RunOV}(F, \sigma, v)$ says that some run of C2 from Step 1 reaches the state $\sigma$ and the overlaps of the sets it added to SUB sum to $v$.
--
--   **Formalization Note** $\mathrm{Ratio}(S)$ is $+\infty$ when $S \cap \mathrm{UNCOV} = \emptyset$; such a set is never a minimizer while UNCOV is nonempty, because the sets of LEFT still cover UNCOV. The rule is therefore written without division: the candidate must meet UNCOV and ratios are compared by cross-multiplication (in Lean's ℕ, $x/0 = 0$ would make useless sets the most attractive). An empty set ($0/0$) is never chosen; choosing it would change neither UNCOV nor the measure. SUB and LEFT are index sets. The overlap is attached to a run (`RunOV`, an inductive relation), because it depends on the order of the choices, not on the output alone.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), pp. 270–271, Section 6 (algorithm C2); p. 271, proof of Theorem 6 (ov, OV); p. 258, Section 2 (choosable)

import Mathlib
import Definitions.Def_JohnsonApprox_ExactCover_Problem

namespace JohnsonApprox.ExactCover

variable {α : Type} [DecidableEq α]

/-- The state of algorithm C2: the paper's `SUB`, `LEFT` (as index sets) and `UNCOV`. -/
structure State (F : Input α) where
  SUB : Finset (Fin F.p)
  LEFT : Finset (Fin F.p)
  UNCOV : Finset α

/-- Step 1 of C2: `SUB = ∅`, `LEFT = F`, `UNCOV = ⋃_{S ∈ F} S`. -/
def init (F : Input α) : State F := ⟨∅, Finset.univ, F.ground⟩

/-- The halting test of Step 2: `UNCOV = ∅`. -/
def Halts {F : Input α} (σ : State F) : Prop := σ.UNCOV = ∅

/-- Step 3 of C2 may choose `S′ = S_i` in state `σ`: `i ∈ LEFT` and `S_i` minimizes
`Ratio(S) = |S − UNCOV| / |S ∩ UNCOV|` over `LEFT`. `Ratio(S)` is `+∞` when `S ∩ UNCOV = ∅`, so
the minimizer meets `UNCOV` and the comparison ranges over the sets of `LEFT` meeting `UNCOV`;
ratios are compared by cross-multiplication. Every minimizer is allowed (ties are free). -/
def MayChoose (F : Input α) (σ : State F) (i : Fin F.p) : Prop :=
  i ∈ σ.LEFT ∧ (F.S i ∩ σ.UNCOV).Nonempty ∧
    ∀ j ∈ σ.LEFT, (F.S j ∩ σ.UNCOV).Nonempty →
      (F.S i \ σ.UNCOV).card * (F.S j ∩ σ.UNCOV).card ≤
        (F.S j \ σ.UNCOV).card * (F.S i ∩ σ.UNCOV).card

/-- One pass through Steps 2–4 of C2 choosing `S′ = S_i`: Step 2 does not halt, Step 3 may choose
`i`, and Step 4 sets `SUB = SUB ∪ {S′}`, `UNCOV = UNCOV − S′`, `LEFT = LEFT − {S′}`. -/
def StepVia (F : Input α) (σ : State F) (i : Fin F.p) (σ' : State F) : Prop :=
  ¬ Halts σ ∧ MayChoose F σ i ∧
    σ' = ⟨insert i σ.SUB, σ.LEFT.erase i, σ.UNCOV \ F.S i⟩

/-- One iteration of C2, for some admissible choice at Step 3. -/
def Step (F : Input α) (σ σ' : State F) : Prop := ∃ i, StepVia F σ i σ'

/-- `σ` is a state C2 can be in, on input `F`, after finitely many iterations. -/
def Reachable (F : Input α) (σ : State F) : Prop := Relation.ReflTransGen (Step F) (init F) σ

/-- `M` is choosable by C2 on input `F`: some admissible run halts with `SUB = M`. -/
def Choosable (F : Input α) (M : Finset (Fin F.p)) : Prop :=
  ∃ σ, Reachable F σ ∧ Halts σ ∧ σ.SUB = M

/-- `RunOV F σ ov`: some run of C2 on `F`, started at Step 1, reaches the state `σ`, and the
cumulative overlap of the sets it added to `SUB` is `ov`. The overlap `ov(S′)` of a chosen set is
`|S′ − UNCOV|` with `UNCOV` taken at the moment `S′` is added to `SUB`. -/
inductive RunOV (F : Input α) : State F → ℕ → Prop
  | init : RunOV F (init F) 0
  | step {σ : State F} {ov : ℕ} {i : Fin F.p} {σ' : State F} :
      RunOV F σ ov → StepVia F σ i σ' → RunOV F σ' (ov + (F.S i \ σ.UNCOV).card)

end JohnsonApprox.ExactCover


