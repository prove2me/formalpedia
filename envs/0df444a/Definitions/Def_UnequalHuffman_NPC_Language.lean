-- Prove2me | Definitions.Def_UnequalHuffman_NPC_Language
-- name    : UnequalHuffman_NPC_Language
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:44:30.696018+00:00
-- url     : https://prove2.me/theorems/7d7cf231-8e94-4c0c-9bb4-8e85099bd143
-- title:
--   Binary Prefix Coding with Unequal Letter Costs as a language over binary-coded instances, and its (M, M + 1) restriction
-- statement:
--   **Binary Prefix Coding with Unequal Letter Costs** (p. 4). An instance consists of positive integer frequencies $w_1,\dots,w_N$ with $N \ge 2$, positive integer letter costs $c_0 < c_1$ and a nonnegative integer threshold $K$, all encoded in binary; it is a yes-instance if some binary prefix code $C$ has $\mathrm{cost}_{c_0,c_1}(C) \le K$. No order of the symbols, codeword lengths or tree shape is prescribed.
--
--   The code of an instance is `instCode w c0 c1 K = encNats ([c0, c1, K] ++ w)` over the published four-letter alphabet `BSym`: each number in binary (least significant digit first, no leading zeros) followed by a separator, so $N$ is determined by the code. `huffLang` is the set of codes of well-formed (`IsValidInstance`: $N \ge 2$, all $w_i \ge 1$, $1 \le c_0 < c_1$) yes-instances; strings that encode no well-formed instance are not in it.
--
--   `huffConsecLang` is the restriction to letter costs $(c_0,c_1) = (M, M+1)$: the codes `instCode w M (M + 1) K` of well-formed yes-instances, i.e. the strings of `huffLang` whose instance has $c_1 = c_0 + 1$. The positive integer $M$ is read from the input; it is not a fixed constant.
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 4 (the decision problem), p. 5 (Theorem 1.1: (M, M + 1), binary encoding)

import Mathlib
import Definitions.Def_UnequalHuffman_NPC_Coding
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false

namespace UnequalHuffman.NPC

open CookPvsNP ProjSchedTW.Complexity FuchsThesis.Coding

/-- The binary code of an instance `(w₁, …, w_N; c₀, c₁; K)` of Binary Prefix Coding with
Unequal Letter Costs: the numbers `c₀, c₁, K, w₁, …, w_N`, each in binary followed by a
separator (`encNats`). Since every number ends with a separator, `N` is determined by the code. -/
def instCode (w : List ℕ) (c0 c1 K : ℕ) : List BSym :=
  encNats ([c0, c1, K] ++ w)

/-- A well-formed instance: `N ≥ 2` symbols, positive integer frequencies, and positive
integer letter costs `c₀ < c₁` (the threshold `K ∈ ℕ` is nonnegative by its type). -/
def IsValidInstance (w : List ℕ) (c0 c1 : ℕ) : Prop :=
  2 ≤ w.length ∧ (∀ x ∈ w, 1 ≤ x) ∧ 1 ≤ c0 ∧ c0 < c1

/-- The yes-condition: some binary prefix code `C = (C₁, …, C_N)` (any words, distinct, none a
prefix of another) has `cost_{c₀,c₁}(C) ≤ K`. -/
def CodingYes (w : List ℕ) (c0 c1 K : ℕ) : Prop :=
  ∃ C : Fin w.length → List Bool, IsInstantaneous C ∧ cost c0 c1 w C ≤ K

/-- Binary Prefix Coding with Unequal Letter Costs (p. 4): the codes of the well-formed
yes-instances, every number in binary. Strings that encode no well-formed instance are not in
the language. -/
def huffLang : Lang BSym :=
  { s | ∃ (w : List ℕ) (c0 c1 K : ℕ),
      IsValidInstance w c0 c1 ∧ CodingYes w c0 c1 K ∧ s = instCode w c0 c1 K }

/-- The restriction to letter costs `(c₀, c₁) = (M, M + 1)`, `M ≥ 1` read from the input: the
strings of `huffLang` whose instance has `c₁ = c₀ + 1` (same code, `c₁ = M + 1` written out). -/
def huffConsecLang : Lang BSym :=
  { s | ∃ (w : List ℕ) (M K : ℕ),
      IsValidInstance w M (M + 1) ∧ CodingYes w M (M + 1) K ∧ s = instCode w M (M + 1) K }

end UnequalHuffman.NPC


