-- Prove2me | Definitions.Def_StreamTesting_Bipartiteness_Supplement_CommonElement
-- name    : StreamTesting_Bipartiteness_Supplement_CommonElement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:59:52.874183+00:00
-- url     : https://prove2.me/theorems/c69d7044-a73d-419a-8b18-58148e1f8015
-- title:
--   Sorted-list intersection inputs and successful search values
-- statement:
--   Two strictly increasing real sequences $A,B$ of length $n$ are streamed as all of $A$, followed by all of $B$. The common-value set is
--
--   $$I(A,B)=\{A_i:i\in[n]\}\cap\{B_j:j\in[n]\}.$$
--
--   The input domain contains every such sorted pair, without a bit-size or range bound. A successful optional real output is $\mathrm{some}(x)$ for a value $x$ occurring in both sequences; a Boolean nonemptiness verdict is insufficient. The intersection promise is $|I(A,B)|\ge\varepsilon n$ and is imposed separately in correctness.
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026), citation basis published; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; §1.2, printed/PDF p.5; §5 and Theorem 22, printed/PDF pp.26–29.

import Mathlib

noncomputable section

namespace StreamTesting.Bipartiteness.Supplement

/-- The natural stream consists of all of A followed by all of B. -/
def joinSequences {n : ℕ} (A B : Fin n → ℝ) (i : Fin (2 * n)) : ℝ :=
  if hi : i.val < n then A ⟨i.val, hi⟩
  else B ⟨i.val - n, by omega⟩

def commonValues {n : ℕ} (A B : Fin n → ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.image A) ∩ (Finset.univ.image B)

def SortedPairInput (n : ℕ) (f : Fin (2 * n) → ℝ) : Prop :=
  ∃ A B : Fin n → ℝ, StrictMono A ∧ StrictMono B ∧ f = joinSequences A B

def CommonValueOutput {n : ℕ} (A B : Fin n → ℝ) (o : Option ℝ) : Prop :=
  ∃ x : ℝ, o = some x ∧ x ∈ Set.range A ∧ x ∈ Set.range B

end StreamTesting.Bipartiteness.Supplement


