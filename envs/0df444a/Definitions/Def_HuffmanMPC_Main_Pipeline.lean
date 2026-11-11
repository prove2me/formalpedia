-- Prove2me | Definitions.Def_HuffmanMPC_Main_Pipeline
-- name    : HuffmanMPC_Main_Pipeline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:11.368408+00:00
-- url     : https://prove2.me/theorems/78909500-eff8-44c1-9b1c-9bd417199037
-- title:
--   Raw text and frequency input as MPC problems: Theorem 3.1, Lemma 7.3, Theorem 7.1
-- statement:
--   **Text input.** A text of length $n$ is a list of $n$ symbols, each a natural number below $(n+1)^K$ for a fixed $K$ (symbols of $O(\log n)$ bits over an arbitrary alphabet). Theorem 3.1's problem outputs the single word $\mu(T)$. Its envelope at $\varepsilon$, with $e=\varepsilon$ for $\varepsilon<1$ and $e=1/2$ otherwise, is
--   $$e^{-3}\log(2+\log n)\ \text{rounds},\quad n^{\varepsilon}\log(2n)\ \text{local words},\quad n\,e^{-3}\log^2(2n)\log(2+\log n)\ \text{total memory and work}.$$
--
--   **Preprocessing (Lemma 7.3).** The integer threshold $\lceil n^\varepsilon\rceil$ is a charged input parameter of the preprocessing subroutine. Output records $(0,c_0)$ and $(1,f)$ for $f\in A_0$, where $(c_0,A_0)$ is exactly the state of Huffman merging while both operands are strictly below that threshold (the final carry is retained), and $A_0$ is positive with sum $n$, $\mu(T)=c_0+\mu(A_0)$, either $|A_0|\le1$ or the second-smallest entry of $A_0$ is at least $\lceil n^\varepsilon\rceil$, and $|A_0|\le n^{1-\varepsilon}+1$. Envelope: $\varepsilon^{-1}$ rounds, $n^\varepsilon$ local words, $n\varepsilon^{-1}\log(2n)$ total memory and work.
--
--   **Frequency input (Theorem 7.1).** Index $(m,n)$; input $m_*=\min\{m,\max\{2,n\}\}$ and at most $m$ positive frequencies of sum $n$, in any order; output $\mu$. Envelope at $\varepsilon$:
--   $$\varepsilon^{-3}\Big(1+\tfrac{\log n}{\log m}\Big)\log(2+\log m),\quad m^{\varepsilon}\log(2m),\quad m^{1+\varepsilon}\varepsilon^{-2}\log^2(2m)\log(2+\log m),\quad m^{1+\varepsilon}\varepsilon^{-3}\Big(1+\tfrac{\log n}{\log m}\Big)\log^2(2m)\log(2+\log m).$$
--
--   **Formalization Note** Logarithms are natural; bases change only constants. The frequency problem's word universe is $n$, so words have $O(\log(2+n))$ bits. Since positive frequencies give $|A|\le n$, clipping $m$ preserves every instance. The resource envelopes use the original $m$.
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Theorem 3.1, pp. 3, 36 (PDF 4, 37); Lemma 7.3, p. 35 (PDF 36); Theorem 7.1, pp. 31–32 (PDF 32–33)

import Definitions.Def_HuffmanMPC_Main_Uniform

set_option autoImplicit false

namespace HuffmanMPC.Main

/-! ### Raw text input (Theorem 3.1, Lemma 7.3) -/

/-- A text of length `n` over an arbitrary alphabet of `O(log n)`-bit symbols:
the symbols are any naturals below `(n+1)^K`, for a fixed exponent `K`. -/
def ValidText (K n : ℕ) (t : List ℕ) : Prop :=
  t.length = n ∧ ∀ x ∈ t, x < (n + 1) ^ K

/-- Theorem 3.1's problem: input the raw text, output the single word `μ(T)`. -/
noncomputable def textProblem (K : ℕ) : MPCProblem ℕ where
  Instance _ := List ℕ
  scale n := n
  input t := t
  valid {n} t := ValidText K n t
  output t out := out = [textOptimum t]

/-- `ε` itself below one, and the construction at `1/2` otherwise. -/
noncomputable def effectiveExponent (eps : ℝ) : ℝ := if eps < 1 then eps else 1/2

/-- Theorem 3.1's explicit bounds (p. 36): `O(ε⁻³ log(2 + log n))` rounds,
`O(n^ε log(2n))` local words, `O(n ε⁻³ log²(2n) log(2 + log n))` total memory and
work; for `ε ≥ 1` the factor `ε⁻³` is that of `ε = 1/2`. -/
noncomputable def textEnvelope (eps : ℝ) : ResourceEnvelope ℕ where
  rounds n := (effectiveExponent eps)⁻¹ ^ 3 * Real.log (2 + Real.log n)
  localSpace n := (n : ℝ) ^ eps * Real.log (2 * n)
  aggregate n := n * (effectiveExponent eps)⁻¹ ^ 3 *
    Real.log (2 * n) ^ 2 * Real.log (2 + Real.log n)
  work n := n * (effectiveExponent eps)⁻¹ ^ 3 *
    Real.log (2 * n) ^ 2 * Real.log (2 + Real.log n)

/-- The counter-and-carry procedure performs exactly the Huffman prefix whose
operands are strictly below the threshold. The remaining carry is retained.
The specification is independent of the optimum and of parallel resources. -/
def preprocessingState (a : Frequencies) (threshold : ℕ) : ℕ × Frequencies :=
  stoppingState a (threshold - 1)

/-- Lemma 7.3's output for the text `t` of length `n`: records `[0, c₀]` and `[1, f]`
for `f ∈ A₀`, where these are the actual threshold-prefix cost and frequencies,
with all three listed properties, positivity and preservation of the sum. -/
def PreprocessingOutput (eps : ℝ) (n : ℕ) (t : List ℕ) (out : List ℕ) : Prop :=
  ∃ (c₀ : ℕ) (A₀ : Frequencies),
    EmitsRecords out ([0, c₀] :: A₀.map fun f => [1, f]) ∧
    (c₀, A₀.mergeSort (· ≤ ·)) =
      preprocessingState (textFrequencies t) ⌈(n : ℝ) ^ eps⌉₊ ∧
    Positive A₀ ∧ A₀.sum = n ∧
    textOptimum t = c₀ + optimum A₀ ∧
    (A₀.length ≤ 1 ∨ ⌈(n : ℝ) ^ eps⌉₊ ≤ (A₀.mergeSort (· ≤ ·)).getD 1 0) ∧
    (A₀.length : ℝ) ≤ (n : ℝ) ^ (1 - eps) + 1

/-- The preprocessing subroutine takes its integer threshold as a parameter,
as in Section 7. It is one charged input word, determined by size and epsilon,
and conveys no information about the symbols or their frequencies. -/
noncomputable def preprocessingProblem (K : ℕ) (eps : ℝ) : MPCProblem ℕ where
  Instance _ := List ℕ
  scale n := n
  input {n} t := ⌈(n : ℝ) ^ eps⌉₊ :: t
  valid {n} t := ValidText K n t
  output {n} t out := PreprocessingOutput eps n t out

/-- Lemma 7.3's bounds: `O(ε⁻¹)` rounds, `O(n^ε)` local words, `O(n ε⁻¹ log(2n))`
total memory and work. -/
noncomputable def preprocessingEnvelope (eps : ℝ) : ResourceEnvelope ℕ where
  rounds _ := eps⁻¹
  localSpace n := (n : ℝ) ^ eps
  aggregate n := n * eps⁻¹ * Real.log (2 * n)
  work n := n * eps⁻¹ * Real.log (2 * n)

/-! ### Frequency input (Theorem 7.1) -/

/-- Index `(m, n)`: the size upper bound `m` and the total frequency `n`.  Input
words: `min m (max 2 n)`, then the frequencies in arbitrary order. Positivity
gives `a.length ≤ n`, so clipping the upper bound preserves every instance and
keeps it in an `O(log(2+n))`-bit word even when `m` is arbitrarily large.
The resource envelope still uses the original bound `m`. Output: `μ`. -/
noncomputable def frequencyProblem : MPCProblem (ℕ × ℕ) where
  Instance _ := Frequencies
  scale i := i.2
  input {i} a := min i.1 (max 2 i.2) :: a
  valid {i} a := 2 ≤ i.1 ∧ a.length ≤ i.1 ∧ Positive a ∧ a.sum = i.2
  output a out := out = [optimum a]

/-- Theorem 7.1's bounds. -/
noncomputable def frequencyEnvelope (eps : ℝ) : ResourceEnvelope (ℕ × ℕ) where
  rounds i := eps⁻¹ ^ 3 * (1 + Real.log i.2 / Real.log i.1) * Real.log (2 + Real.log i.1)
  localSpace i := (i.1 : ℝ) ^ eps * Real.log (2 * i.1)
  aggregate i := (i.1 : ℝ) ^ (1 + eps) * eps⁻¹ ^ 2 * Real.log (2 * i.1) ^ 2 *
    Real.log (2 + Real.log i.1)
  work i := (i.1 : ℝ) ^ (1 + eps) * eps⁻¹ ^ 3 * (1 + Real.log i.2 / Real.log i.1) *
    Real.log (2 * i.1) ^ 2 * Real.log (2 + Real.log i.1)

end HuffmanMPC.Main


