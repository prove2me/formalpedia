-- Prove2me | Definitions.Def_MajorityDepthThree_Exact_Circuits
-- name    : MajorityDepthThree_Exact_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:50.877109+00:00
-- url     : https://prove2.me/theorems/b4cde147-687d-40ce-9d44-607b94bbd0f7
-- title:
--   Top fan-in circuit minima and conventional majority
-- statement:
--   A circuit is a finite list of CNFs on one fixed finite ground set $V$. It is a width-$k$ depth-three OR-AND-OR circuit if every listed CNF is valid and has width at most $k$. It is monotone if every CNF is monotone. Evaluation is disjunction of CNF satisfaction. Computing the $t$-threshold function means agreement on every subset of $V$ with $|S|\ge t$.
--
--   For the canonical $n$-element carrier, let $s_k(n,t)$ and $s_k^+(n,t)$ be the infima, in natural numbers, of list lengths of all such circuits computing this threshold, respectively allowing signs or requiring monotonicity. These are genuine global size minima whenever $k\ge1$ and $t\le n$, since the monotone unit-clause disjunctive representation supplies circuits. No restriction to the paper's constructed formulas is imposed. Define
--
--   $$u(n)=\lceil n/2\rceil,\quad s(n)=s_3(n,u(n)),\quad s^+(n)=s_3^+(n,u(n)),\quad a=\frac{2}{6^{1/4}},\quad B(n,t)=2^t(3/2)^{(n-t)/2}.$$
--
--   Variable permutations rename both signs. A circuit consists of permutations of $F$ when each CNF is such a renamed copy. The padded construction on $n=4m+j$, $0\le j<4$, uses $m$ disjoint positive four-variable three-cliques, then $\lceil j/2\rceil$ unit clauses; the remaining variables are isolated. Its ambient carrier always has $n$ elements. This gives an explicit source-compatible all-residue construction without invoking the incorrect boundary formula of Fact 3.8.
--
--   Size is top fan-in, the number of CNFs, and may include repeated identical subcircuits. Repetitions never improve the minimum. The empty OR is false. At $n=0$ the majority function is true and a single empty CNF computes it. The goal explicitly asserts positive, attained minima, excluding accidental use of the natural infimum's empty-set convention.
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.7, Section 2.1 and Definition 2.8; p.4, Corollary 1.5; pp.8–9, Definition 3.1 and Section 3.3 (all-residue padding explained locally)

import Definitions.Def_MajorityDepthThree_Exact_CNF

set_option autoImplicit false

namespace MajorityDepthThree.Exact

variable {α : Type} [DecidableEq α]

abbrev Circuit (α : Type) := List (CNF α)

def CircuitValid (V : Finset α) (k : ℕ) (C : Circuit α) : Prop :=
  ∀ F ∈ C, ValidCNF V F ∧ Width k F

def CircuitMonotone (C : Circuit α) : Prop := ∀ F ∈ C, Monotone F

def ComputesThreshold (V : Finset α) (t : ℕ) (C : Circuit α) : Prop :=
  ∀ S ⊆ V, (∃ F ∈ C, S ∈ transversals V F) ↔ t ≤ S.card

noncomputable def thresholdSize (n t k : ℕ) (monotone : Bool) : ℕ :=
  sInf {s : ℕ | ∃ C : Circuit (Fin n), CircuitValid Finset.univ k C ∧
    ComputesThreshold Finset.univ t C ∧
    (monotone = true → CircuitMonotone C) ∧ C.length = s}

def majorityThreshold (n : ℕ) : ℕ := (n + 1) / 2
noncomputable def majoritySize (n : ℕ) : ℕ := thresholdSize n (majorityThreshold n) 3 false
noncomputable def monotoneMajoritySize (n : ℕ) : ℕ := thresholdSize n (majorityThreshold n) 3 true
noncomputable def exponentialBase : ℝ := 2 / (6 : ℝ) ^ (1 / 4 : ℝ)
noncomputable def countingBound (n t : ℕ) : ℝ :=
  (2 : ℝ)^t * (3 / 2 : ℝ)^(((n - t : ℕ) : ℝ) / 2)

noncomputable def permuteCNF {n : ℕ} (σ : Equiv.Perm (Fin n)) (F : CNF (Fin n)) : CNF (Fin n) := by
  classical
  exact F.image (fun c => (c.1.image σ, c.2.image σ))

def PermutationsOf {n : ℕ} (F : CNF (Fin n)) (C : Circuit (Fin n)) : Prop :=
  ∀ G ∈ C, ∃ σ : Equiv.Perm (Fin n), G = permuteCNF σ F

noncomputable def paddedMajorityCNF (n : ℕ) : CNF (Fin n) := by
  classical
  exact Finset.univ.filter (fun c => c.2 = ∅ ∧
    ((c.1.card = 3 ∧ ∃ b < n / 4, ∀ x ∈ c.1, x.val / 4 = b) ∨
      ∃ x : Fin n, c.1 = {x} ∧ 4 * (n / 4) ≤ x.val ∧
        x.val < 4 * (n / 4) + (n % 4 + 1) / 2))

end MajorityDepthThree.Exact


