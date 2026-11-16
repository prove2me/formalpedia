-- Prove2me | Definitions.Def_HuffmanMPC_Main_Supplement_Bounds
-- name    : HuffmanMPC_Main_Supplement_Bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:18:51.880325+00:00
-- url     : https://prove2.me/theorems/652c8ab4-8215-4ec0-b196-bfc18bf6560a
-- title:
--   Uniform simultaneous PRAM time and work envelopes
-- statement:
--   Write $\ell(m)=\max\{1,\log_2m\}$, $\ell_2(m)=\max\{1,\log_2\ell(m)\}$, and $R(m,n)=1+\log_2n/\log_2m$. The simultaneous Huffman envelopes are
--   $$T_\varepsilon(m,n)=\varepsilon^{-2}R(m,n)\ell_2(m),\qquad W_\varepsilon(m,n)=\varepsilon^{-2}R(m,n)m^{1+\varepsilon}\ell(m)^4.$$
--   For merging, with $\eta=\lceil m^\delta\rceil$, they are
--   $$T_\delta=\delta^{-1},\qquad W_\delta(m,s)=\delta^{-1}s\eta.$$
--   A guarantee requires one program to solve every admissible instance under both corresponding bounds multiplied by a single positive constant $c$, with word coefficient $k$. Theorems choose $c,k$ before the fixed parameter and choose the program before all input sizes and values. Every legal size is included, with clamped logarithms incorporating small cases. All denominators and exponents are used only under $m\ge2$, $n\ge m$ and a parameter in $(0,1)$.
-- source:
--   Masoud Seddighin, Saeed Seddighin, STOC 2027 submission #377 (October 2026), Massively Parallel Algorithms for Huffman Coding, pp. 41–45, 49–50 (PDF 42–46, 50–51), log convention; Theorem 9.2 and Lemma 9.4

import Definitions.Def_HuffmanMPC_Main_Supplement_Problems

set_option autoImplicit false

namespace HuffmanMPC.Main.Supplement

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2
noncomputable def logFactor (m : ℕ) : ℝ := max 1 (logTwo m)
noncomputable def logLogFactor (m : ℕ) : ℝ := max 1 (logTwo (logFactor m))

/-- The denominator is the actual logarithm; m >= 2 at every invocation. -/
noncomputable def sizeRatio (m n : ℕ) : ℝ := 1 + logTwo n / logTwo m

noncomputable def huffmanTime (eps : ℝ) (m n : ℕ) : ℝ :=
  eps⁻¹ ^ 2 * sizeRatio m n * logLogFactor m
noncomputable def huffmanWork (eps : ℝ) (m n : ℕ) : ℝ :=
  eps⁻¹ ^ 2 * sizeRatio m n * (m : ℝ) ^ (1 + eps) * logFactor m ^ 4

noncomputable def eta (delta : ℝ) (m : ℕ) : ℕ := ⌈(m : ℝ) ^ delta⌉₊
noncomputable def mergeTime (delta : ℝ) : ℝ := delta⁻¹
noncomputable def mergeWork (delta : ℝ) (m s : ℕ) : ℝ :=
  delta⁻¹ * s * eta delta m

/-- Correctness holds for all sizes. Clamped factors absorb the bounded small
cases, so the simultaneous estimates can also be asserted for every size. -/
def HuffmanGuarantee (P : Program) (c : ℝ) (k : ℕ) (eps : ℝ) : Prop :=
  ∀ a : List ℕ, HuffmanInstance a →
    Solves P k a.sum a.length (huffmanInput a) [optimum a]
      (c * huffmanTime eps a.length a.sum) (c * huffmanWork eps a.length a.sum)

def MergeGuarantee (P : Program) (c : ℝ) (k : ℕ) (delta : ℝ) : Prop :=
  ∀ (m n : ℕ) (a b : List ℕ), MergeInstance m n a b →
    Solves P k n (a.length + b.length) (mergeInput m n a b) (mergeOutput a b)
      (c * mergeTime delta) (c * mergeWork delta m (a.length + b.length))

end HuffmanMPC.Main.Supplement


