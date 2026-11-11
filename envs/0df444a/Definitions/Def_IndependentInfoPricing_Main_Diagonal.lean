-- Prove2me | Definitions.Def_IndependentInfoPricing_Main_Diagonal
-- name    : IndependentInfoPricing_Main_Diagonal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:52.136572+00:00
-- url     : https://prove2.me/theorems/313a3e17-a4a9-4be3-b992-bdaabb75c756
-- title:
--   The explicit independent exponential-support separation family
-- statement:
--   Fix integers $k\ge1$ and $n\ge1$, with $n\ge1+(1+\log a)/(a-1)$, and set $a=e^k$, $r=1+1/k$, $b=a^r$. Indices are the mathematical integers $1,\ldots,n$. Put $\omega_i=n-\lceil i/r\rceil+1$ and $S_i=an/(a^i\omega_i)$. The positive law has mass $S_i-S_{i+1}$ at $a^i$ for $i<n$ and mass $S_n$ at $a^n$. The negative magnitude is uniform on $b^1,\ldots,b^n$. Their product gives $v=(X,-Y)$; no probability-normalization or feasibility conclusion is assumed as a field.
--
--   The diagonal menu uses exactly (29)–(30), including its distinct last option, and includes both free options. Its diagonal contribution is
--
--   $$\operatorname{Diag}=\sum_{i=1}^n\frac{\Pr(X=a^i)}{n}p^{(i)}.$$
--
--   The module also defines the closed expression (34) separately, so its equality with the actual contribution is a theorem obligation. The full menu revenue is evaluated on every type of the product law, including off-diagonal types. Subtraction in $\omega_i$ is real, not truncated natural subtraction. The probability measure constructors use the nonnegative parts of the displayed masses on arbitrary inputs; Lemma 3.2 must prove nonnegativity and normalization for the specified parameters. The positive finite-law predicate records probability, strictly positive finite support, and zero mass outside that support.
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), §§2–4.5, starting printed p.12 (PDF p.14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Laws

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Section 3 uses 1-based indices; all subtraction in omega is in the reals. -/
def baseA (k : ℕ) : ℝ := Real.exp k

def growthR (k : ℕ) : ℝ := 1 + 1 / (k : ℝ)

def baseB (k : ℕ) : ℝ := (baseA k) ^ (growthR k)

def FamilyParameters (k n : ℕ) : Prop :=
  1 ≤ k ∧ 1 ≤ n ∧ 1 + (1 + Real.log (baseA k)) / (baseA k - 1) ≤ (n : ℝ)

def omega (k n i : ℕ) : ℝ := (n : ℝ) - (⌈(i : ℝ) / growthR k⌉ : ℤ) + 1

def survivalX (k n i : ℕ) : ℝ := baseA k * n / ((baseA k) ^ i * omega k n i)

def massX (k n i : ℕ) : ℝ :=
  if i < n then survivalX k n i - survivalX k n (i+1) else survivalX k n n

def familyX (k n : ℕ) : Measure ℝ :=
  ∑ i ∈ Finset.Icc 1 n, ENNReal.ofReal (massX k n i) • Measure.dirac ((baseA k) ^ i)

def familyY (k n : ℕ) : Measure ℝ :=
  ∑ i ∈ Finset.Icc 1 n, ENNReal.ofReal (1 / (n : ℝ)) • Measure.dirac ((baseB k) ^ i)

def oppositeLaw (X Y : Measure ℝ) : Marginals (Fin 2) :=
  fun i => if i = 0 then X else Measure.map (fun y : ℝ => -y) Y

def familyLaw (k n : ℕ) : Measure (Values (Fin 2)) := productLaw (oppositeLaw (familyX k n) (familyY k n))

def sigma (k : ℕ) : ℝ := (baseB k - baseA k) / (baseB k - 1)

def diagonalAllocation (k n i : ℕ) : Values (Fin 2) :=
  fun j => if j = 0 then 1 else
    if i < n then (baseA k - 1) / (baseB k - 1) * (baseA k) ^ (-(growthR k - 1) * (i : ℝ)) else 0

def diagonalPrice (k n i : ℕ) : ℝ :=
  if i < n then sigma k * (baseA k) ^ i else (baseA k) ^ n

def diagonalType (k i : ℕ) : Values (Fin 2) :=
  fun j => if j = 0 then (baseA k) ^ i else -((baseB k) ^ i)

def diagonalMenu (k n : ℕ) : Menu (Fin 2) := by
  classical
  exact (Finset.Icc 1 n).image (fun i => (diagonalAllocation k n i, diagonalPrice k n i)) ∪ {(0,0),(1,0)}

def diagonalRevenue (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, massX k n i / (n : ℝ) * diagonalPrice k n i

def diagonalClosedForm (k n : ℕ) : ℝ :=
  baseA k * sigma k * (∑ i ∈ Finset.Ico 1 n, (1 / omega k n i - 1 / (baseA k * omega k n (i+1)))) +
    baseA k / omega k n n

def PositiveFiniteLaw (D : Measure ℝ) : Prop :=
  IsProbabilityMeasure D ∧ ∃ A : Finset ℝ, (∀ x ∈ A, 0 < x) ∧ D (↑A : Set ℝ)ᶜ = 0

end IndependentInfoPricing.Main


