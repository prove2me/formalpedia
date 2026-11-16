-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Supplement_FiniteChoice
-- name    : LogSupermodularBIS_Main_Supplement_FiniteChoice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:32:47.89297+00:00
-- url     : https://prove2.me/theorems/76bba443-9b80-4e9a-a0e3-84ae2f4163b5
-- title:
--   Ordered rational choice laws and dyadic inverse transforms
-- statement:
--   For an ordered nonempty list of positive rational weights $\omega_0,\ldots,\omega_{n-1}$, the target law is
--   $$
--   p_j=\frac{\omega_j}{\sum_i\omega_i}.
--   $$
--   The input code contains $n$, a value-length bound $L$, the requested bit count $\ell$, and the rational weight codes in order. The first $\ell$ fair bits determine a uniformly distributed dyadic point $y\in\{0,2^{-\ell},\ldots,1-2^{-\ell}\}$. Its inverse transform is the least $j$ with $y<\sum_{i\le j}\omega_i/\sum_i\omega_i$. The fallback value zero is only for invalid inputs; positive nonempty lists always have a crossing. Finite-law total variation is
--   $$
--   \|p-q\|_{\mathrm{TV}}=\tfrac12\sum_j|p_j-q_j|.
--   $$
--   The inverse transform specifies a mathematical output; the separate finite-program theorem must implement it with charged bit operations and exactly $\ell$ fair bits. Rational comparisons can be made by integer cross multiplication. The weight length convention is the published base definition.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), pp. 41–42 (PDF 42–43), Lemma A.6 and proof

import Mathlib
import Definitions.Def_LogSupermodularBIS_Main_Supplement_BitMachine
import Definitions.Def_LogSupermodularBIS_Main_Weight

set_option autoImplicit false

namespace LogSupermodularBIS.Main.Supplement

/-- Half of the finite L1 distance. Validity of the encoded output is imposed separately. -/
noncomputable def finiteTV {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (∑ x, |p x - q x|) / 2

/-- Normalized rational weighted-choice law, used only for nonempty positive lists. -/
def choiceLaw {n : ℕ} (ω : Fin n → ℚ) (j : Fin n) : ℝ :=
  ((ω j / ∑ i, ω i : ℚ) : ℝ)

/-- Input of a finite-choice program: list length, value-length bound, requested number of
fair bits, then the ordered list of canonical rational codes. -/
def choiceInput {n : ℕ} (ω : Fin n → ℚ) (L ℓ : ℕ) : Bits :=
  encNat n ++ encNat L ++ encNat ℓ ++ (List.ofFn fun i => encRat (ω i)).flatten

/-- Inverse transform of the dyadic grid point represented by the first `ℓ` bits. Rational
comparisons can be implemented by integer cross multiplication. The fallback is irrelevant
for nonempty positive lists, since the final cumulative probability is one. -/
def dyadicChoice {n : ℕ} (ω : Fin n → ℚ) (ℓ : ℕ) (u : ℕ → Bool) : ℕ :=
  let y : ℚ := (bitsValue (List.ofFn fun i : Fin ℓ => u i.val) : ℚ) / (2 : ℚ) ^ ℓ
  ((List.finRange n).find? fun j => decide
    (y < (∑ i : Fin n, if i.val ≤ j.val then ω i else 0) / ∑ i, ω i)).map
      Fin.val |>.getD 0

end LogSupermodularBIS.Main.Supplement


