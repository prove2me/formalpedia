-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_LabelPerformance
-- name    : GreedyColoringLCA969_LowerBound_Supplement_LabelPerformance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:32:57.718693+00:00
-- url     : https://prove2.me/theorems/78f3d1a2-3379-4821-b688-01532eeb7987
-- title:
--   Finite-label success, average query complexity and MIS
-- statement:
--   Fix a labeling problem $P$, a coding $e:L\to\mathbb Z_+$, a standard-oracle LCA $A$ and a represented graph $R$. Global success on a shared random tape $r$ means there is a correct labeling $l$ such that every execution at $v$ terminates with return code $e(l(v))$:
--
--   $$\operatorname{Succ}_{P,e}(A,R)=\{r:\exists l,\ P(R,l)\ \land\ \forall v,\ A(R,r,v)=e(l(v))\}.$$
--
--   The probability uses the published independent fair-bit tape law. Error-free on degree bound $\Delta$ means this probability is one for every size and every representation of a graph of maximum degree at most $\Delta$. For an arbitrary finite label set a fixed bijection codes its labels by $1,\ldots,|L|$; Boolean labels use $0\mapsto1$, $1\mapsto2$. An out-of-range code and a nonterminating answer both fail global success.
--
--   Average query complexity is $n^{-1}\sum_v\mathbb E_r[q_A(R,r,v)]$, with value zero on the empty graph. Each expectation remains a nonnegative extended real; it is not replaced by a real integral on nonintegrable costs. The MIS predicate requires the vertices labeled $1$ to be independent and every vertex labeled $0$ to have a neighbor labeled $1$. Regularity means every vertex has exactly $\Delta$ neighbors. These concepts share the published execution and query costs without imposing correctness or resource bounds on algorithms.
--
--   The general set predicate for maximal independence is reused from the published `SmoothedMIS.IsMIS`; this item only turns it into a Boolean-labeling problem by taking the set of vertices labeled $1$. The imported body adds no graph assumptions.
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), pp.7–9 (PDF 8–10), §2.1 and Definitions 2.6–2.8; pp.27–29 (PDF 28–30), §5.1 and Theorem 5.6

import Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_Labeling
import Definitions.Def_GreedyColoringLCA969_LowerBound_Performance
import Definitions.Def_SmoothedMIS_IsMIS

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

/-- A fixed bijection from finite labels to codes 1,...,|L|. -/
noncomputable def finiteCode (L : Type) [Fintype L] (α : L) : ℕ+ :=
  ⟨(Fintype.equivFin L α).val + 1, Nat.succ_pos _⟩

def boolCode : Bool → ℕ+
  | false => 1
  | true => 2

/-- Global correctness, using the actual published execution on one shared tape.
An invalid code or a nonterminating answer makes the tape unsuccessful. -/
def labelingSuccess {L : Type} (P : LabelProblem L) (code : L → ℕ+)
    {n : ℕ} (A : Algorithm .standard) (R : Representation n) : Set Tape :=
  {r | ∃ l : Fin n → L, P R.graph l ∧ ∀ v, Returns A R r v (code (l v))}

noncomputable def labelingProbability {L : Type} (P : LabelProblem L) (code : L → ℕ+)
    {n : ℕ} (A : Algorithm .standard) (R : Representation n) : ℝ≥0∞ :=
  tapeLaw (labelingSuccess P code A R)

def ErrorFreeOn {L : Type} (P : LabelProblem L) (code : L → ℕ+)
    (A : Algorithm .standard) (Δ : ℕ) : Prop :=
  ∀ (n : ℕ) (R : Representation n), MaxDegreeAtMost R.graph Δ →
    labelingProbability P code A R = 1

noncomputable def averageQueries {n : ℕ} (A : Algorithm .standard)
    (R : Representation n) : ℝ≥0∞ :=
  if n = 0 then 0 else (∑ v, expectedQueries A R v) / (n : ℝ≥0∞)

/-- Independence and domination, not maximum cardinality. -/
def MIS : LabelProblem Bool := fun G l =>
  SmoothedMIS.IsMIS G {v | l v = true}

def Regular {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℕ) : Prop :=
  ∀ v, Nat.card {u // G.Adj v u} = Δ

end GreedyColoringLCA969.LowerBound.Supplement


