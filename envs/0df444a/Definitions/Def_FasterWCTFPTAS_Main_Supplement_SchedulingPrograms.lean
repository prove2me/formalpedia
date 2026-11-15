-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_Supplement_SchedulingPrograms
-- name    : FasterWCTFPTAS_Main_Supplement_SchedulingPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:08:53.279384+00:00
-- url     : https://prove2.me/theorems/962812f8-eb28-4b97-b5fa-d7d17148a918
-- title:
--   Scheduling FPTAS and polynomial gap-reduction interfaces
-- statement:
--   For fixed $m\ge2$ and $\alpha,\beta>0$, a fast scheduling scheme is one finite admissible program and a constant $C>0$ such that, for every $n\ge1$, real processing times $p_j>0$, real weights $w_j\ge0$ and $0<\varepsilon\le1$, its published scheduling input produces an assignment evaluated in Smith order with
--
--   $$\operatorname{cost}(\sigma)\le(1+\varepsilon)\operatorname{OPT},\qquad
--   T\le Cn^\beta(1/\varepsilon)^{(m-1)/2-\alpha}.$$
--
--   This imports the base scheduling and encoding objects unchanged, including zero optimum, arbitrary real data and Smith tie-breaking.
--
--   The gap-reduction interface asserts existence of one admissible program and uniform $C>0,d\in\mathbb N$. On every valid Grouped $m$-way Partition input it halts within $C(n+1+\log_2(W+1))^d$ steps. Output $[0]$ must certify No; alternatively output $[1,\Lambda,\lambda,p_1,\ldots,p_n,w_1,\ldots,w_n]$ must give exactly $n$ jobs with valid signs, $\Lambda,\lambda>0$, ratio $\Lambda/\lambda\le Cn^dW^2$, optimum at most $\Lambda$ on Yes, and optimum at least $\Lambda+\lambda$ on No. Output data carry no semantic guarantees as fields. The running time includes binary dependence on $W$, and the same constants can be enlarged to cover time and ratio. This interface is a proposition to be proved by Lemma B.1.
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, A Faster FPTAS for Weighted Completion Time Scheduling, STOC 2027 submission #1072 (October 2026), p.2 (PDF p.3), Theorem 1.2; pp.27–30 (PDF pp.28–31), Lemma B.1 and its use.

import Definitions.Def_FasterWCTFPTAS_Main_Scheduling
import Definitions.Def_FasterWCTFPTAS_Main_Encoding
import Definitions.Def_FasterWCTFPTAS_Main_Supplement_PartitionPrograms

set_option autoImplicit false

namespace FasterWCTFPTAS.Main.Supplement

/-- The forbidden FPTAS, with the published full real-data domain, accuracy (0,1],
multiplicative guarantee (also when OPT=0), and one program and constant for ALL inputs.
The exponent is real subtraction and may be nonpositive. -/
def FastScheduling (m : ℕ) (α β : ℝ) : Prop :=
  ∃ (P : Machine.Program) (C : ℝ), Machine.Admissible P ∧ 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ p w : Fin n → ℝ,
      (∀ j, 0 < p j) → (∀ j, 0 ≤ w j) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ σ : Fin n → Fin m,
          Machine.output P (schedInput ε p w) = some (assignmentOutput σ) ∧
          Machine.HaltsWithin P (schedInput ε p w)
            (C * (n : ℝ) ^ β * (1 / ε) ^ (((m : ℝ) - 1) / 2 - α)) ∧
          smithCost p w σ ≤ (1 + ε) * OPT m p w

/-- Data in the reduction's constructed branch. No semantic conclusion is a field.
The number of jobs is exactly the number of input items. -/
structure GapData (n : ℕ) where
  p : Fin n → ℝ
  w : Fin n → ℝ
  upper : ℝ
  gap : ℝ

/-- Output [1,Λ,λ,p_1,...,p_n,w_1,...,w_n]; [0] is reserved for the early No branch. -/
def gapOutput {n : ℕ} (G : GapData n) : List ℝ :=
  [1, G.upper, G.gap] ++ List.ofFn G.p ++ List.ofFn G.w

/-- Valid scheduling data and ALL three numbered properties of Lemma B.1. -/
def GapProperties {m : ℕ} (I : PartitionData m) (G : GapData I.n)
    (C : ℝ) (d : ℕ) : Prop :=
  (∀ j, 0 < G.p j) ∧ (∀ j, 0 ≤ G.w j) ∧ 0 < G.upper ∧ 0 < G.gap ∧
  G.upper / G.gap ≤ C * (I.n : ℝ) ^ d * (I.W : ℝ) ^ 2 ∧
  (GroupedYes I → OPT m G.p G.w ≤ G.upper) ∧
  (GroupedNo I → G.upper + G.gap ≤ OPT m G.p G.w)

/-- The full deterministic polynomial-time disjunctive gap reduction.
The constants depend only on m. log base 2 includes the binary input-size dependence on W.
The same C,d can bound both runtime and ratio by increasing them (n≥2 on valid inputs).
This predicate does not presuppose the existence of a reduction. -/
def HasGapReduction (m : ℕ) : Prop :=
  ∃ (P : Machine.Program) (C : ℝ) (d : ℕ), Machine.Admissible P ∧ 0 < C ∧
    ∀ I : PartitionData m, GroupedValid I →
      Machine.HaltsWithin P (groupedInput I)
        (C * ((I.n : ℝ) + 1 + Real.logb 2 ((I.W : ℝ) + 1)) ^ d) ∧
      ((Machine.output P (groupedInput I) = some [0] ∧ GroupedNo I) ∨
        ∃ G : GapData I.n, Machine.output P (groupedInput I) = some (gapOutput G) ∧
          GapProperties I G C d)

end FasterWCTFPTAS.Main.Supplement


