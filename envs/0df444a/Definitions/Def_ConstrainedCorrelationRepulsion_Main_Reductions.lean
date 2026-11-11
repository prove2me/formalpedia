-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Reductions
-- name    : ConstrainedCorrelationRepulsion_Main_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:44.80916+00:00
-- url     : https://prove2.me/theorems/a1fb97bf-1304-4d11-ac85-ed0b6a67fb94
-- title:
--   True-twin averaging, expansion and representative projection
-- statement:
--   Must-link components are averaged on the same vertex set. Their internal separation cost is one; incompatible component pairs have separation cost zero and full cross-product cannot-links; compatible component pairs use their original positive-edge density. The fixed cost counts internal negative pairs and positive pairs between incompatible components. Projection repeatedly takes the cheaper of the two constructive twin moves for a separated component pair.
--
--   For probability expansion, $\varepsilon_b=\min(\delta,1)$, $m=\binom n2$, $\gamma=\varepsilon_b/[8(\alpha+1)]$, $\eta=\varepsilon_b/(8m)$, $L_b=\lceil\log(2n/(\gamma\eta))\rceil$, and $T=\lceil256n^4\gamma^{-4}L_b^2\rceil$. Inputs with $n<2$ are handled first. Copy groups are positive cliques with no must-links, cross labels are independent, and all cross-copy pairs of an original hard pair are forbidden. Representatives are independently uniform. A feasible majority-clique solution is returned directly when available. These definitions do not select an optimal partition or condition away the bad expansion event.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), §§3.1–3.2 and Appendix B, equations (7), (46)–(47), printed pp.14–16, 43–45 (PDF pp.15–17, 44–46)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Algorithm
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Repulsion

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators

noncomputable def component {n : ℕ} (I : Instance n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => I.mustLink.Reachable v u)

noncomputable def incompatibleComponents {n : ℕ} (I : Instance n) (u v : Fin n) : Prop :=
  ∃ a ∈ component I u, ∃ b ∈ component I v, I.cannotLink.Adj a b

noncomputable def twinProbability {n : ℕ} (I : Instance n) (u v : Fin n) : ℝ :=
  if I.mustLink.Reachable u v then 1 else if incompatibleComponents I u v then 0 else
    (∑ a ∈ component I u, (positiveDegree I a (component I v) : ℝ)) /
      ((component I u).card * (component I v).card : ℕ)

noncomputable def twinCosts {n : ℕ} (I : Instance n) : PairCosts n :=
  ⟨fun e => twinProbability I e.out.1 e.out.2,
   fun e => 1 - twinProbability I e.out.1 e.out.2⟩

noncomputable def twinInstance {n : ℕ} (I : Instance n) : Instance n :=
  ⟨⊥, ⊥, SimpleGraph.fromRel (incompatibleComponents I)⟩

noncomputable def twinFixedCost {n : ℕ} (I : Instance n) : ℝ :=
  pairSum (fun u v =>
    if I.mustLink.Reachable u v then (if I.positive.Adj u v then 0 else 1)
    else if incompatibleComponents I u v ∧ I.positive.Adj u v then 1 else 0)

def moveVertex {n : ℕ} (P : Partition n) (u v : Fin n) : Partition n :=
  Function.update P u (P v)

/-- The two constructive twin moves, with deterministic choice of the least separated pair.
No optimization over partitions is performed: each comparison evaluates two given moves. -/
noncomputable def gatherStep {n : ℕ} (I : Instance n) (P : Partition n) : Partition n :=
  let pairs := (Finset.univ : Finset (Fin n × Fin n)).filter (fun e =>
    e.1 < e.2 ∧ I.mustLink.Reachable e.1 e.2 ∧ P e.1 ≠ P e.2)
  if h : pairs.Nonempty then
    let e := (pairs.toList.mergeSort (fun a b =>
      decide (a.1.val*n + a.2.val ≤ b.1.val*n + b.2.val))).headD (Classical.choose h)
    let A := moveVertex P e.1 e.2
    let B := moveVertex P e.2 e.1
    if weightedCost (twinCosts I) A ≤ weightedCost (twinCosts I) B then A else B
  else P

noncomputable def gather {n : ℕ} (I : Instance n) (P : Partition n) : Partition n :=
  (gatherStep I)^[n*n + 1] P

noncomputable def copyCount (n : ℕ) (alpha delta : ℝ) : ℕ :=
  if n < 2 then 1 else
    let eps := min delta 1
    let m : ℝ := Nat.choose n 2
    let gamma := eps / (8*(alpha+1))
    let eta := eps / (8*m)
    let Lb : ℝ := ⌈Real.log (2*n/(gamma*eta))⌉₊
    ⌈256 * (n : ℝ)^4 * gamma^(-4 : ℤ) * Lb^2⌉₊

def copyGroup {n T : ℕ} (hT : 0 < T) (v : Fin (n*T)) : Fin n :=
  ⟨v.val / T, (Nat.div_lt_iff_lt_mul hT).2 v.isLt⟩

noncomputable def independentPairs {N : ℕ} (p : Fin N → Fin N → ℝ) :
    List (Fin N × Fin N) → PMF (Finset (Fin N × Fin N))
  | [] => PMF.pure ∅
  | e :: es => (flip (p e.1 e.2)).bind fun take =>
      (independentPairs p es).map fun S => if take then insert e S else S

/-- Appendix B's actual random label expansion. All cross-pair labels are independent.
Groups are positive cliques, have no must-links, and hard pairs are full cross-products. -/
noncomputable def expansionLaw {n T : ℕ} (hT : 0 < T) (I : Instance n)
    (p : ProbabilityWeights n) : PMF (Instance (n*T)) :=
  let pairs := (Finset.univ : Finset (Fin (n*T) × Fin (n*T))).filter (fun e => e.1 < e.2)
  (independentPairs (fun u v => if copyGroup hT u = copyGroup hT v then 1
    else p.positive s(copyGroup hT u, copyGroup hT v)) pairs.toList).map fun edges =>
    {positive := SimpleGraph.fromRel (fun u v => (u,v) ∈ edges ∨ (v,u) ∈ edges),
     mustLink := ⊥,
     cannotLink := SimpleGraph.fromRel (fun u v => I.cannotLink.Adj (copyGroup hT u) (copyGroup hT v))}

/-- Projection samples one representative independently and uniformly in each copy group.
It never tests for, or conditions on, a good concentration event. -/
noncomputable def representativeLaw {n T : ℕ} (hT : 0 < T)
    (Q : Partition (n*T)) : PMF (Partition n) :=
  let choices := categorical (fun _ : Fin n → Fin T => 1 / ((T : ℝ)^n))
  choices.map fun chosen =>
    match chosen with
    | none => id
    | some reps =>
      let label := fun v : Fin n => Q ⟨v.val*T + (reps v).val, by
        have hv := v.isLt
        have hr := (reps v).isLt
        nlinarith⟩
      fun v =>
        let C := Finset.univ.filter (fun u => label u = label v)
        C.min' (by exact ⟨v, by simp [C]⟩)

noncomputable def majoritySolution {n : ℕ} (I : Instance n) (p : ProbabilityWeights n) :
    Option (Partition n) :=
  if h : ∃ P : Partition n, Feasible I P ∧
    ∀ u v, u ≠ v → (P u = P v ↔ (1 : ℝ)/2 ≤ p.positive s(u,v)) then some (Classical.choose h)
  else none

end ConstrainedCorrelationRepulsion.Main


