-- Prove2me | Definitions.Def_PermanentStars_Counting_Partitions
-- name    : PermanentStars_Counting_Partitions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:50:42.988259+00:00
-- url     : https://prove2.me/theorems/d7300680-3136-4664-ad50-1ed743be2004
-- title:
--   Partitions, assigned cutoffs, prefix counts and binary entropy
-- statement:
--   For a block family $\pi$ on the ordered leaves $[n]$, let $q_r(\pi)$ count its blocks of size greater than $r$. A parameter record stores a finite cutoff set $R$ and rational fractions $\alpha_r$. Validity means $R$ is nonempty, its cutoffs are positive, and $0\le\alpha_r\le1$. Admissibility and the assigned cutoff are
--   $$q_r(\pi)\le\alpha_r n,\qquad r(\pi)=\max\{r\in R:q_r(\pi)\le\alpha_r n\}.$$
--   Assignment returns no value when the set is empty. The ambient $n$ stays fixed for partitions of subsets. Coverage is a separate proposition.
--
--   The block coefficient is $\mu(\pi)=\prod_{B\in\pi}(-1)^{|B|-1}(|B|-1)!$. The independent center-map sum is $\prod_{B\in\pi}\sum_j\prod_{i\in B}A_{ij}$, with no injectivity requirement. The restricted Binet–Minc sum selects exactly the assigned partitions. Mathlib finite partitions supply nonempty, disjoint blocks.
--
--   Prefix length is the largest $p\le N$ whose initial segment lies in $S$. Its counting function counts all subsets with $|S|\le r\operatorname{pref}(S)$. Entropy is $H(a)=\operatorname{binEntropy}(a)/\log2$, with continuous endpoint values, and
--   $$E(a,c)=\log_2c+H(a)-a\log_2(c-1).$$
--   The binomial budget is the finite sum through $\lfloor an\rfloor$. These definitions contain neither coverage nor any inequality as assumed data.
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), equations (3)–(4), pp.2,5; Definition 4.1, p.9; (11), p.7; §5, pp.10–11

import Mathlib
import Definitions.Def_SetMultCost_RPerm

namespace PermanentStars.Counting

/-- Fixed finite positive cutoffs and rational fractions, §4.3, p.9. -/
structure Cutoffs where
  R : Finset ℕ
  alpha : ℕ → ℚ

def Cutoffs.Valid (P : Cutoffs) : Prop :=
  P.R.Nonempty ∧ (∀ r ∈ P.R, 1 ≤ r) ∧
    (∀ r ∈ P.R, 0 ≤ P.alpha r ∧ P.alpha r ≤ 1)

def largeCount {n : ℕ} (bs : Finset (Finset (Fin n))) (r : ℕ) : ℕ :=
  (bs.filter (fun B => r < B.card)).card

def admissible (P : Cutoffs) (n : ℕ) (bs : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  r ∈ P.R ∧ (largeCount bs r : ℚ) ≤ P.alpha r * n

/-- No cutoff is selected on uncovered inputs; zero is never a default cutoff. -/
noncomputable def assigned (P : Cutoffs) (n : ℕ) (bs : Finset (Finset (Fin n))) : Option ℕ := by
  classical
  let T := P.R.filter (fun r => (largeCount bs r : ℚ) ≤ P.alpha r * n)
  exact if h : T.Nonempty then some (T.max' h) else none

def Covers (P : Cutoffs) (n : ℕ) : Prop :=
  ∀ pi : Finpartition (Finset.univ : Finset (Fin n)), ∃ r, admissible P n pi.parts r

def mobius {n : ℕ} (bs : Finset (Finset (Fin n))) : ℤ :=
  ∏ B ∈ bs, (-1 : ℤ) ^ (B.card - 1) * (B.card - 1).factorial

/-- Equation (3): every center chooses independently, without injectivity. -/
noncomputable def mapSum {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) R) (bs : Finset (Finset (Fin n))) : R :=
  ∏ B ∈ bs, ∑ j, ∏ i ∈ B, A i j

noncomputable def assignedSum {n : ℕ} {R : Type*} [CommRing R]
    (P : Cutoffs) (r : ℕ) (A : Matrix (Fin n) (Fin n) R) : R := by
  classical
  exact ∑ pi : Finpartition (Finset.univ : Finset (Fin n)),
    if assigned P n pi.parts = some r then (mobius pi.parts : R) * mapSum A pi.parts else 0

/-- Equation (11), with zero-based labels: [p] consists of indices with val < p. -/
def prefixLength {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => ∀ i : Fin N, i.val < p → i ∈ S)).sup id

noncomputable def prefixCount (N r : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.card ≤ r * prefixLength S)).card

noncomputable def entropy (a : ℝ) : ℝ := Real.binEntropy a / Real.log 2

noncomputable def exponent (a c : ℝ) : ℝ :=
  Real.log c / Real.log 2 + entropy a - a * (Real.log (c - 1) / Real.log 2)

noncomputable def binomialBudget (n : ℕ) (a c : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (⌊a * n⌋₊ + 1), (n.choose p : ℝ) * (c - 1)⁻¹ ^ p

end PermanentStars.Counting


