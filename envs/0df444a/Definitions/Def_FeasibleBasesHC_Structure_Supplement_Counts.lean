-- Prove2me | Definitions.Def_FeasibleBasesHC_Structure_Supplement_Counts
-- name    : FeasibleBasesHC_Structure_Supplement_Counts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:28:12.574809+00:00
-- url     : https://prove2.me/theorems/ff89eb4f-c239-4f87-9264-4511a932ef66
-- title:
--   §4 — class counts, cyclic intervals, first-order coefficients, and the first-passage index
-- statement:
--   For an encoded quadruple, put $R=\{1\}$ and $D=[n]\setminus\{s,s-1\}$. For $P,Q\in\{L,U,R\}$ set
--
--   $$W_{PQ}=\{i\in D:i\in P,\ \pi(i)\in Q\},\qquad N_{PQ}(i)=|I(i)\cap W_{PQ}|.$$
--
--   Here $I(i)$ is the initial segment from $s+1$ through $i$ in cyclic order. The integer coefficient $\alpha_{i1}$ is $1$ on $W_{UU}\cup W_{LL}$, $3-n$ on $W_{UL}$, $n-1$ on $W_{LU}$, $2-n$ on $W_{UR}\cup W_{RL}$, and $0$ on $W_{LR}\cup W_{RU}$. Also $\alpha_{s1}=n/2$ for even $n$ and $\alpha_{s1}=1$ for odd $n$.
--
--   Write $d(i)=N_{UL}(i)+N_{UR}(i)+N_{RL}(i)$. The predicate $\mathrm{IsIStar}(i)$ means that $i\in D$, $d(i)=N_{LU}(i)+1$, and $d(j)\le N_{LU}(j)$ for every $j\in I(i-1)$. It expresses the first passage in Remark 2 without choosing a default index or assuming its existence. Under that remark's hypotheses it is the unique index $i^*$.
--
--   These definitions are the exact finite combinatorial interface used in Theorems 4.1–4.3; they introduce no asymptotic remainder or additional feasibility hypothesis.
--
--   **Formalization Note** Labels use the same zero-based convention as the base module. Fin subtraction happens before taking the natural-number value to compute the cyclic rank. The otherwise unused intervals $I(s)$ and $I(s-1)$ are set to empty; $I(s)=\varnothing$ is the boundary needed when $i^*=s+1$. Coefficients are integers, with exact natural-number division for even $n$. The coefficient table is zero outside its stated domain; every theorem uses it only on $D$.
-- source:
--   Kalinowski, Mohammadian, Feasible Bases for a Polytope Related to the Hamilton Cycle Problem, arXiv:1907.12691v1, pp. 18–19, (4.11), and p. 21, Remark 2

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Supplement_Quadruple

namespace FeasibleBasesHC.Structure.Supplement

variable {n : ℕ} [NeZero n]

/-- R={1} in paper labels. -/
def R (n : ℕ) [NeZero n] : Finset (Fin n) := {0}

/-- The indices of the recurrence, excluding s and s-1. -/
def active (q : Quadruple n) : Finset (Fin n) :=
  Finset.univ \ {q.s, q.s - 1}

/-- W_PQ of pp. 18-19. The extra exclusion s-1 is automatic from pi(s-1)=s. -/
def W (q : Quadruple n) (P Q : Finset (Fin n)) : Finset (Fin n) :=
  (active q).filter (fun i => i ∈ P ∧ q.pi i ∈ Q)

/-- First-order coefficient table (4.11); unused inputs have value zero. -/
def alpha1 (q : Quadruple n) (i : Fin n) : ℤ :=
  if i ∈ W q q.U q.U ∨ i ∈ W q q.L q.L then 1
  else if i ∈ W q q.U q.L then 3 - (n : ℤ)
  else if i ∈ W q q.L q.U then (n : ℤ) - 1
  else if i ∈ W q q.U (R n) ∨ i ∈ W q (R n) q.L then 2 - (n : ℤ)
  else 0

/-- The initial first-order coefficient, p. 19. Nat division is exact for even n. -/
def alphaS (n : ℕ) : ℤ := if Even n then (n / 2 : ℕ) else 1

/-- Position in the cyclic order s+1,...,s-2, computed in Fin n first. -/
def rank (q : Quadruple n) (i : Fin n) : ℕ := (i - (q.s + 1)).val

/-- Inclusive cyclic initial segment I(i). On the omitted endpoints it is empty;
in particular I(s)=empty supplies the first-index boundary in Remark 2. -/
def I (q : Quadruple n) (i : Fin n) : Finset (Fin n) :=
  if i ∈ active q then (active q).filter (fun j => rank q j ≤ rank q i) else ∅

/-- Partial class counts. -/
def N (q : Quadruple n) (P Q : Finset (Fin n)) (i : Fin n) : ℕ :=
  (I q i ∩ W q P Q).card

/-- N_UL+N_UR+N_RL, kept as a sum of counts without truncated subtraction. -/
def downCount (q : Quadruple n) (i : Fin n) : ℕ :=
  N q q.U q.L i + N q q.U (R n) i + N q (R n) q.L i

/-- Remark 2's characterization of i*: first passage to level one.
This predicate makes no choice and assumes no feasibility. -/
def IsIStar (q : Quadruple n) (i : Fin n) : Prop :=
  i ∈ active q ∧ downCount q i = N q q.L q.U i + 1 ∧
    ∀ j ∈ I q (i - 1), downCount q j ≤ N q q.L q.U j

end FeasibleBasesHC.Structure.Supplement


