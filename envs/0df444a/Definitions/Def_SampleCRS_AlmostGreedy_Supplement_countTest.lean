-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_Supplement_countTest
-- name    : SampleCRS_AlmostGreedy_Supplement_countTest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:35:07.643209+00:00
-- url     : https://prove2.me/theorems/038be896-8acd-4234-8fb5-ca56e25a7584
-- title:
--   Count Test candidates and the uniform candidate-slot experiment
-- statement:
--   In arrival order, start with no candidates. Admit active arrival $i$ as a candidate exactly when the previous candidate count plus one is at most $R+\sum_{j\le i}Y_j$. Put $N=R+\sum_jY_j$. Choose uniformly a $\min\{k,N\}$-subset of the $N$ possible candidate slots and accept candidates whose slots are chosen; unused terminal slots have no effect.
--
--   The experiment draws independent online and sample rows, $R$ uniformly from $\{0,\ldots,r\}$, and then the stated uniform slot subset. It defines the actual conditional acceptance probability $C_i=\Pr[A_i]/p_i$ for $p_i>0$:
--   $$\Pr[A_i]=\frac1{r+1}\sum_{R=0}^r E_{X,Y}\!\left[\frac{\sum_{U:|U|=\min(k,N)}1_{\{i\in A(X,Y,R,U)\}}}{\binom N{\min(k,N)}}\right].$$
--   This is the equivalent online rule explicitly given on p.19: before the next candidate, the conditional acceptance bias is $(\min\{k,N\}-A)/(N-C)$. At $N=0$ the only slot subset is empty and no candidate can be admitted. No decision uses the hidden vector $p$.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), Algorithm 5, pp.18–19

import Mathlib
import Definitions.Def_SampleCRS_AlmostGreedy_Supplement_onlineKernel

namespace SampleCRS.AlmostGreedy.Supplement

/-- Algorithm 5's candidates in arrival order. The test uses the number of
candidates before this arrival and includes the current sample. -/
def countCandidates {n : ℕ} (R : ℕ) (X Y : Fin n → Bool) : List (Fin n) :=
  (List.ofFn (fun i : Fin n => i)).foldl (fun C i =>
    if X i = true ∧ C.length + 1 ≤ R + prefixCount Y (i.val + 1) then C ++ [i] else C) []

def countN {n : ℕ} (R : ℕ) (Y : Fin n → Bool) : ℕ := R + activeCount Y

/-- The equivalent online rule on p.19: prechoose a uniform min(k,N)-subset
of the N candidate slots. Slots past the actual list remain unused. This gives
the same conditional fraction (min(k,N)-A)/(N-C) as Algorithm 5. -/
def countRun {n : ℕ} (R : ℕ) (X Y : Fin n → Bool) (U : Finset ℕ) : Finset (Fin n) :=
  (((countCandidates R X Y).zipIdx.filter (fun z => z.2 ∈ U)).map Prod.fst).toFinset

def countChoices {n : ℕ} (k R : ℕ) (Y : Fin n → Bool) : Finset (Finset ℕ) :=
  (Finset.range (countN R Y)).powersetCard (min k (countN R Y))

noncomputable def countE {n : ℕ} (k r : ℕ) (p : Fin n → ℝ)
    (f : Finset (Fin n) → ℝ) : ℝ :=
  (∑ R : Fin (r + 1), ∑ X, ∑ Y, activationWeight p X * activationWeight p Y *
    ((∑ U ∈ countChoices k R.val Y, f (countRun R.val X Y U)) /
      ((countChoices k R.val Y).card : ℝ))) / ((r : ℝ) + 1)

noncomputable def countC {n : ℕ} (k r : ℕ) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  countE k r p (fun A => if i ∈ A then 1 else 0) / p i

def CountFeasible (n k r : ℕ) : Prop :=
  ∀ (R : Fin (r + 1)) (X Y : Fin n → Bool) (U : Finset ℕ), U ∈ countChoices k R.val Y →
    (countRun R.val X Y U).card ≤ k ∧ ∀ i ∈ countRun R.val X Y U, X i = true

end SampleCRS.AlmostGreedy.Supplement


