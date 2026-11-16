-- Prove2me | Definitions.Def_CatalyticMatching_General_Supplement_Relations
-- name    : CatalyticMatching_General_Supplement_Relations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:06:57.882187+00:00
-- url     : https://prove2.me/theorems/370fd3c5-ed52-467a-8639-fbe9861415fa
-- title:
--   Input domains and output relations for mixed-matrix rank and Edmonds’ problem
-- statement:
--   Each domain below is a set of well-formed input strings; none presupposes the desired output.
--
--   1. **Rank/deficiency test (Lemma 4.5).** Input: a standard field with at least $(r+c)^{10}$ elements, an $r\times c$ mixed matrix $A$ and an evaluation $A'$. Output: the single bit of $[\operatorname{rank}A=\operatorname{rank}A'\wedge D(A)=D(A')]$.
--   2. **Maximum-rank completion (Theorem 4.6).** Input: a standard field with at least $(r+c)^{10}$ elements and a mixed matrix $A$. Output: the binary value of $\operatorname{rank}A$ followed by an assignment whose evaluation $A'$ satisfies $\operatorname{rank}A'=\operatorname{rank}A$.
--   3. **Approximate Edmonds' problem (Theorem 5.4).** For a real $\varepsilon\in(0,1)$, input: a standard field with $|F|\ge n^{2/\varepsilon+3}$ and $A_1,\dots,A_m\in F^{n\times n}$. Output: the entries of a matrix $B\in\mathcal A$ with $\operatorname{rank}B\ge(1-\varepsilon)\operatorname{rank}(\mathcal A)$.
--   4. **Few generators (Remark 5.3).** As in 3, restricted to $\dim\mathcal A<\ell$, where $\ell=\lceil1/\varepsilon-1\rceil$; output: a matrix $B\in\mathcal A$ with $\operatorname{rank}B=\operatorname{rank}(\mathcal A)$.
--
--   The search outputs may depend on the initial catalyst; the rank output in 2 and the bit in 1 are determined by the input.
--
--   **Formalization Note** The ℚ presentation satisfies every field-size bound. For $\varepsilon\in(0,1)$, $\ell=\lceil1/\varepsilon-1\rceil\ge1$. The bound $n^{2/\varepsilon+3}$ is a real power.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Lemma 4.5 and Theorem 4.6, printed/PDF p.24; Theorem 1.2, p.5; Remark 5.3 and Theorem 5.4, pp.27–28; Theorem 1.4, p.6

import Definitions.Def_CatalyticMatching_General_CatalyticSpace
import Definitions.Def_CatalyticMatching_General_Supplement_MixedMatrix
import Definitions.Def_CatalyticMatching_General_Supplement_MatrixSpace
import Definitions.Def_CatalyticMatching_General_Supplement_FieldEncoding

namespace CatalyticMatching.General.Supplement

/-- §4 field-size requirement: n^10 distinct test elements, n = r + c (vacuous for ℚ). -/
def mixedFieldBound (r c : ℕ) : ℝ := ((r + c : ℕ) : ℝ) ^ 10

/-- Lemma 4.5 input: a field, a mixed matrix A and an evaluation A′ (all variable values). -/
def mixedTestDomain (x : Bits) : Prop :=
  ∃ (P : Presented) (r c : ℕ) (A : MixedMatrix r c P.F) (a : MixedVar A → P.F),
    StandardField P (mixedFieldBound r c) ∧
      x = P.header ++ mixedBits P.enc A ++ assignBits P.enc A a

/-- Lemma 4.5 output: the single truth bit of rank A = rank A′ ∧ D(A) = D(A′),
with rank A and D(A) those of the generic matrix over F(X). -/
noncomputable def mixedTestRelation (x y : Bits) : Prop := by
  classical
  exact ∃ (P : Presented) (r c : ℕ) (A : MixedMatrix r c P.F) (a : MixedVar A → P.F),
    StandardField P (mixedFieldBound r c) ∧
      x = P.header ++ mixedBits P.enc A ++ assignBits P.enc A a ∧
      y = [decide ((genericMixed A).rank = (mixedEval A a).rank ∧
        rectDeficiency (genericMixed A) = rectDeficiency (mixedEval A a))]

/-- Theorem 4.6 input: a field and an arbitrary rectangular mixed matrix. -/
def completionDomain (x : Bits) : Prop :=
  ∃ (P : Presented) (r c : ℕ) (A : MixedMatrix r c P.F),
    StandardField P (mixedFieldBound r c) ∧ x = P.header ++ mixedBits P.enc A

/-- Theorem 4.6 output: the exact generic rank AND an assignment attaining it. -/
def completionRelation (x y : Bits) : Prop :=
  ∃ (P : Presented) (r c : ℕ) (A : MixedMatrix r c P.F) (a : MixedVar A → P.F),
    StandardField P (mixedFieldBound r c) ∧ x = P.header ++ mixedBits P.enc A ∧
      y = frame (natBits (genericMixed A).rank) ++ assignBits P.enc A a ∧
      (mixedEval A a).rank = (genericMixed A).rank

/-- §5 parameter ℓ = ⌈1/ε − 1⌉. -/
noncomputable def ell (ε : ℝ) : ℕ := ⌈1 / ε - 1⌉₊

/-- Theorem 5.4 field requirement |F| ≥ n^{2/ε+3} (real exponent; vacuous for ℚ). -/
noncomputable def edmondsFieldBound (ε : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (2 / ε + 3)

/-- Theorem 5.4 input: a field with |F| ≥ n^{2/ε+3} and any generators A₁,…,A_m. -/
def edmondsDomain (ε : ℝ) (x : Bits) : Prop :=
  ∃ (P : Presented) (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) P.F),
    StandardField P (edmondsFieldBound ε n) ∧ x = P.header ++ generatorsBits P.enc A

/-- Theorem 5.4 output: a matrix B in the span with rank B ≥ (1−ε)·rank(𝒜). -/
def approxRelation (ε : ℝ) (x y : Bits) : Prop :=
  ∃ (P : Presented) (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) P.F)
    (B : Matrix (Fin n) (Fin n) P.F),
    StandardField P (edmondsFieldBound ε n) ∧ x = P.header ++ generatorsBits P.enc A ∧
      B ∈ matrixSpan A ∧ y = sqMatrixBits P.enc B ∧
      (1 - ε) * (commRank A : ℝ) ≤ (B.rank : ℝ)

/-- Remark 5.3 input: the Theorem 5.4 setting with fewer than ℓ basis matrices, i.e.
dim 𝒜 < ℓ (p.26 reduces any generating list to a basis; every list with m < ℓ is included). -/
def fewGeneratorsDomain (ε : ℝ) (x : Bits) : Prop :=
  ∃ (P : Presented) (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) P.F),
    StandardField P (edmondsFieldBound ε n) ∧ Module.finrank P.F (matrixSpan A) < ell ε ∧
      x = P.header ++ generatorsBits P.enc A

/-- Remark 5.3 output: an exact maximum-rank matrix B of the span. -/
def exactSpanRelation (ε : ℝ) (x y : Bits) : Prop :=
  ∃ (P : Presented) (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) P.F)
    (B : Matrix (Fin n) (Fin n) P.F),
    StandardField P (edmondsFieldBound ε n) ∧ Module.finrank P.F (matrixSpan A) < ell ε ∧
      x = P.header ++ generatorsBits P.enc A ∧
      B ∈ matrixSpan A ∧ y = sqMatrixBits P.enc B ∧ B.rank = commRank A

end CatalyticMatching.General.Supplement


