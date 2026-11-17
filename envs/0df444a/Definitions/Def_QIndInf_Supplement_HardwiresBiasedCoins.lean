-- Prove2me | Definitions.Def_QIndInf_Supplement_HardwiresBiasedCoins
-- name    : QIndInf_Supplement_HardwiresBiasedCoins
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:27:14.394206+00:00
-- url     : https://prove2.me/theorems/645fb977-b600-4b80-bd0e-3bbb90d4eaa0
-- title:
--   Hardwired biased coins: the source-model property behind Theorem A.1
-- statement:
--   For biases $q_i\in[0,1]$, the product state on one-qubit registers with register $i$ in $(1-q_i)|0\rangle\langle0|+q_i|1\rangle\langle1|$ is the state of independent bits with $\Pr[X_i=1]=q_i$. For $\alpha\in\{0,1\}^k$, block length $\ell$ and biases $p_0,p_1$, the machine $T_\alpha$ of the proof of Theorem A.1 outputs bits $X_1,X_2,\dots$ with
--   $$\Pr[X_{(j-1)\ell+u}=1]=p_{\alpha_j}\qquad(j\in[k],\ u\in[\ell]),$$
--   and all later bits $0$ (Eq. (187)).
--
--   A source model **hardwires biased coins** with constant $c_0$ if for every $a\ge64$ ($\epsilon=1/a$) and all $k,\ell$ there are biases
--   $$\tfrac12-3\epsilon\le p_0\le\tfrac12-2\epsilon,\qquad \tfrac12+2\epsilon\le p_1\le\tfrac12+3\epsilon$$
--   and one time bound $t$ such that for every $\alpha\in\{0,1\}^k$ some program $T$ with
--   $$|T|\ \le\ c_0\big(k+\log_2(k+1)+\log_2(a+1)+\log_2(\ell+1)+1\big)$$
--   generates, within $t$ steps and on one-qubit registers, exactly this product state.
--
--   This is the property of the paper's encoding that the proof of Theorem A.1 uses: the description of $T_\alpha$ is a fixed procedure plus $\alpha$, $k$, $\ell$ and the biases (Eq. (188)), and a fixed compilation procedure prepares the registers independently with outcome probabilities in the intervals of Eq. (186) (p.38).
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), Appendix A, proof of Theorem A.1, Eqs. (185)–(188), pp.35–36, and p.38

import Mathlib
import Definitions.Def_QIndInf_QuantumProcess

set_option autoImplicit false

namespace QIndInf.Supplement

open QIndInf

/-- The product of one-qubit diagonal states on `m` one-qubit registers, register `i`
(`0`-based) in the state `(1 − q i)|0⟩⟨0| + q i |1⟩⟨1|`. -/
noncomputable def coinState (q : ℕ → ℝ) (m : ℕ) : Matrix (Regs 1 m) (Regs 1 m) ℂ :=
  Matrix.diagonal fun z => ∏ i : Fin m, (((if (z i).val = 1 then q i.val else 1 - q i.val) : ℝ) : ℂ)

/-- The bias of output bit `i` (`0`-based) of the machine `T_α` of the proof of Theorem A.1
(Eq. (187)): `p_{α_j}` in block `j = ⌊i/ℓ⌋` of the first `k` blocks of length `ℓ`, and `0` (the bit
is `0`) afterwards. -/
noncomputable def blockBias (k ℓ : ℕ) (α : Fin k → Bool) (p₀ p₁ : ℝ) (i : ℕ) : ℝ :=
  if h : i < k * ℓ then
    (if α ⟨i / ℓ, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)⟩ then p₁ else p₀)
  else 0

/-- **The hardwiring property of the source model used in Theorem A.1** (Eqs. (186)–(188) and the
last paragraph of the proof, p.38), with constant `c₀`: for every `a ≥ 64` (`ε = 1/a`) and all
`k, ℓ` there are biases `p₀ ∈ [½ − 3/a, ½ − 2/a]`, `p₁ ∈ [½ + 2/a, ½ + 3/a]` and one time bound `t`
such that for every `α ∈ {0,1}^k` some program `T` with
`|T| ≤ c₀ (k + log₂(k+1) + log₂(a+1) + log₂(ℓ+1) + 1)` generates, within `t` steps, the product of
one-qubit diagonal states whose bit `(j−1)ℓ + u` (`j ∈ [k]`, `u ∈ [ℓ]`) is `1` with probability
`p_{α_j}`, all later bits being `0`.

arXiv:2609.36912 (PDF of 2026-11-02), Appendix A, proof of Theorem A.1, Eqs. (185)–(188),
pp.35–36, and p.38 ("A classical Turing machine can output a circuit generating these independent
bits on one-qubit registers … it suffices to prepare the registers independently so that the two
outcome probabilities lie in the intervals in Equation (186) … A fixed compilation procedure
preserves the description-length estimate, and we can again choose a common time bound").

**Formalization Note.** This is the property of the paper's own encoding that the proof uses
(`|T_α| = O(k + log k + log ε⁻¹ + log δ⁻¹)`, Eq. (188), with `ℓ = Θ(ε⁻²)`); Theorem A.1 is stated
for every source model with it. The source on registers beyond the first `kℓ` is `|0⟩`, the
paper's appended zeros. -/
def HardwiresBiasedCoins (c₀ : ℝ) (gen : SourceModel) : Prop :=
  ∀ a k ℓ : ℕ, 64 ≤ a → ∃ p₀ p₁ : ℝ,
    1 / 2 - 3 / (a : ℝ) ≤ p₀ ∧ p₀ ≤ 1 / 2 - 2 / (a : ℝ) ∧
    1 / 2 + 2 / (a : ℝ) ≤ p₁ ∧ p₁ ≤ 1 / 2 + 3 / (a : ℝ) ∧
    ∃ t : ℕ, ∀ α : Fin k → Bool, ∃ T : List Bool,
      (T.length : ℝ) ≤ c₀ * ((k : ℝ) + Real.logb 2 (k + 1) + Real.logb 2 (a + 1) +
        Real.logb 2 (ℓ + 1) + 1) ∧
      ∀ m : ℕ, (gen 1 t T).state m = coinState (blockBias k ℓ α p₀ p₁) m

end QIndInf.Supplement


