-- Prove2me | Definitions.Def_CoarseMatching_LowerBound_HiddenCore
-- name    : CoarseMatching_LowerBound_HiddenCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:05.796535+00:00
-- url     : https://prove2.me/theorems/32d1a8fd-0c94-4834-8f6f-d1ebee806e64
-- title:
--   Hidden-Core input laws and acceptance gaps
-- statement:
--   Fix a finite public universe $U$ of size $N$, positive integers $d\le h$ with $h+d\le N$, and a normalized count law $R$ on $\{0,\ldots,d\}$. Sample a uniform $h$-subset $C$, independently draw $z\sim R$, and sample $B$ uniformly conditional on $|B|=d$ and $|B\setminus C|=z$. Alice receives $C$ and Bob receives $B$. Neither receives the hidden count. For two count laws, a fair hidden bit selects the input law, and the acceptance gap compares the two conditional output probabilities.
--
--   $$P_0(Z>0)\le1/a,\qquad P_1(Z>0)=1.$$
--
--   The displayed predicate is exactly Equation (4). Hidden-Core protocols receive only their respective sets and public data. Their resource promise records the two set cardinalities. These are actual sampled input laws, not free acceptance tables.
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), §4.1 Equation (4), §4.2, printed pp.11–12 (PDF pp.12–13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Definitions.Def_CoarseMatching_LowerBound_SubsetLaws
import Definitions.Def_CoarseMatching_LowerBound_ProtocolResources

namespace CoarseMatching.LowerBound
noncomputable section

/-- Normalized count law on exactly {0,...,d}. -/
abbrev CountLaw (d : ℕ) := PMF (Fin (d+1))

/-- Kol §4.2, printed p.12 / PDF p.13. Alice sees C, Bob sees B,
not the count or hidden bit. Positive d ≤ h and h+d ≤ |U| ensure every sample is legal. -/
def hiddenLaw {U : Type} [Fintype U] [DecidableEq U] (h d : ℕ) (R : CountLaw d) :
    PMF (Finset U × Finset U) :=
  (subsetLaw (Finset.univ : Finset U) h).bind fun C =>
    R.bind fun z => (neighborLaw C d z.val).map (fun B => (C,B))

/-- Equation (4), printed p.11 / PDF p.12. -/
def EquationFour {d : ℕ} (a : ℝ) (P₀ P₁ : CountLaw d) : Prop :=
  (P₀.toOuterMeasure {z | 0 < z.val}).toReal ≤ 1/a ∧
  P₁.toOuterMeasure {z | 0 < z.val} = 1

/-- Input promise on the two separately known sizes. No parity/count given to players. -/
def HiddenInputs {U : Type} (h d : ℕ) (C B : Finset U) : Prop :=
  C.card = h ∧ B.card = d

def hiddenGap {U : Type} [Fintype U] [DecidableEq U] (h d : ℕ)
    (P₀ P₁ : CountLaw d) (π : Protocol (Finset U) (Finset U)) : ℝ :=
  gap π (hiddenLaw h d P₀) (hiddenLaw h d P₁)

end
end CoarseMatching.LowerBound


