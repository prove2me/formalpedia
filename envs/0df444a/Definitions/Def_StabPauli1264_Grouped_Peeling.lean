-- Prove2me | Definitions.Def_StabPauli1264_Grouped_Peeling
-- name    : StabPauli1264_Grouped_Peeling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:25:28.285674+00:00
-- url     : https://prove2.me/theorems/9b008237-a8a7-476a-b0a0-fc5319277996
-- title:
--   Algorithm 1: exact maximum-weight peeling and empirical output
-- statement:
--   For known $M,p,\varepsilon,\delta$, set
--
--   $$c_0=2\sqrt{\ln2}\sum_{s=0}^\infty2^{-s/2}\sqrt{s+1},\quad N=\left\lceil\frac{4(c_0+\sqrt{2\ln(1/\delta)})^2}{\varepsilon^2}\right\rceil,\quad\tau=\varepsilon/2.$$
--
--   Starting with $R_1=\operatorname{supp}p$, choose a commuting subset $C_j\subseteq R_j$ of maximum mass $w_j=p(C_j)$, allowing the empty set. If $w_j<\tau$, stop; otherwise remove $C_j$ and continue. Let $k$ be the number selected, $U$ their union, and $W=p(U)$. If $k=0$, return the computational-basis zero stabilizer without measurements. Otherwise allocate $N_j=\lceil Nw_j/W\rceil$ fresh copies to context $C_j$. Return a valid tableau maximizing $\sum_{i\in U}p_i\widehat b_i f_T(i)$, where $\widehat b_i$ is the empirical mean of its observed signs.
--
--   The definitions specify the remaining sets, terminal maximum weight, all copy counts, the full fixed measurement schedule and the actual grouped decision rule. No true means or risk optimum enter the empirical maximization. This is the exact information-theoretic algorithm, with unrestricted classical computation.
--
--   **Formalization Note** One classical choice function fixes all ties from known inputs and empirical scores. A recursion with $m+1$ fuel totalizes peeling; positive thresholds ensure actual termination before fuel exhaustion. Suffix index zero denotes source index one. Unmeasured empirical means totalize to zero and their scores are zero; the empty branch avoids allocation division. The series is a real `tsum`; summability is a conclusion of the goal, never an assumed bound.
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Theorem 2.3 Eq. (7), p. 6; Algorithm 1, p. 7; Lemma 8.1 and upper-bound proof, pp. 20–21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Measurements
set_option autoImplicit false

namespace StabPauli1264.Grouped

open QAlgorithms.Stabilizer
open scoped BigOperators Classical

/-- A fixed choice among exact finite maxima. The fallback only totalizes impossible input. -/
noncomputable def maxContext {n m : ℕ} (M : Window n m) (p : EvalLaw m)
    (R : Finset (Fin m)) : Finset (Fin m) :=
  if h : ∃ C : Finset (Fin m), C ⊆ R ∧ IsContext M C ∧
      ∀ D : Finset (Fin m), D ⊆ R → IsContext M D → mass p D ≤ mass p C then
    Classical.choose h else ∅

noncomputable def support {m : ℕ} (p : EvalLaw m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => 0 < p.mass i)

/-- Fuel is m+1; for positive tau, each selected context removes an index.
There is therefore a genuine stopping test before exhaustion of the fuel. -/
noncomputable def peelAux {n m : ℕ} (M : Window n m) (p : EvalLaw m) (τ : ℝ) :
    ℕ → Finset (Fin m) → List (Finset (Fin m))
  | 0, _ => []
  | fuel + 1, R =>
    let C := maxContext M p R
    if mass p C < τ then [] else C :: peelAux M p τ fuel (R \ C)

noncomputable def peeled {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ε : ℝ) :=
  peelAux M p (ε / 2) (m + 1) (support p)

/-- Zero-based remainder: j=0 is the source's R_1, j=k is its stopping remainder. -/
noncomputable def remainder {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ε : ℝ)
    (j : ℕ) : Finset (Fin m) :=
  ((peeled M p ε).take j).foldl (fun R C => R \ C) (support p)

noncomputable def suffixWeight {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ε : ℝ)
    (j : ℕ) : ℝ := mass p (maxContext M p (remainder M p ε j))

noncomputable def retained {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ε : ℝ) :=
  ((peeled M p ε).flatMap Finset.toList).toFinset

noncomputable def c0Term (s : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(s : ℝ) / 2) * Real.sqrt (s + 1)

noncomputable def c0 : ℝ := 2 * Real.sqrt (Real.log 2) * ∑' s : ℕ, c0Term s

noncomputable def copyBudget (ε δ : ℝ) : ℕ :=
  ⌈4 * (c0 + Real.sqrt (2 * Real.log (1 / δ))) ^ 2 / ε ^ 2⌉₊

/-- The k=0 branch precedes all allocation divisions. W is the actual retained mass. -/
noncomputable def allocations {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ε δ : ℝ) : List ℕ :=
  if (peeled M p ε).isEmpty then [] else
    (peeled M p ε).map (fun C =>
      ⌈(copyBudget ε δ : ℝ) * mass p C / mass p (retained M p ε)⌉₊)

noncomputable def schedule {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ε δ : ℝ) :=
  ((peeled M p ε).zip (allocations M p ε δ)).flatMap (fun z => List.replicate z.2 z.1)

/-- A concrete default tableau for |0...0>. -/
def zeroTableau (n : ℕ) : Tableau n :=
  fun j => ⟨0, fun q => if q = j then .Z else .I⟩

/-- Exact empirical optimization over all valid signed n-generator tableaux. -/
noncomputable def empiricalMax {n m : ℕ} (M : Window n m) (c : Fin m → ℝ) : Tableau n :=
  if h : ∃ T : Tableau n, IsValidTableau T ∧ ∀ S : Tableau n, IsValidTableau S →
      (∑ i, c i * response M S i) ≤ ∑ i, c i * response M T i then
    Classical.choose h else zeroTableau n

noncomputable def empiricalMeans {m : ℕ} (settings : List (Finset (Fin m)))
    (h : List (Record m)) (i : Fin m) : ℝ :=
  ((h.zip settings).map (fun z => if i ∈ z.2 then sign (z.1.2 i) else 0)).sum /
    ((settings.filter (fun C => decide (i ∈ C))).length : ℝ)

/-- Algorithm 1: the schedule is fixed from known data; output sees only the transcript.
Unmeasured coordinates have score zero, and the k=0 case uses no empirical means. -/
noncomputable def peelingLearner {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ε δ : ℝ) :
    GroupedProcedure n m (schedule M p ε δ).length where
  choose h := pointLaw ((schedule M p ε δ).getD h.length ∅)
  output h := pointLaw (if (peeled M p ε).isEmpty then zeroTableau n else
    empiricalMax M (fun i => if i ∈ retained M p ε then
      p.mass i * empiricalMeans (schedule M p ε δ) h i else 0))

end StabPauli1264.Grouped


