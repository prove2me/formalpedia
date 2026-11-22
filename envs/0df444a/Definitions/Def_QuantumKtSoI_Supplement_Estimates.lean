-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_Estimates
-- name    : QuantumKtSoI_Supplement_Estimates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:30:32.59527+00:00
-- url     : https://prove2.me/theorems/9a62f4c7-f3c2-43e4-89f2-53b9dc5416b9
-- title:
--   Estimating a measure within $\psi$ in time $T$ (Definition 6.12)
-- statement:
--   Let $T,\psi:\mathbb N\to\mathbb N$ and let $\mu$ be a measure of strings. A machine $A$ **estimates $\mu$ within $\psi$ in time $T$** if for all sufficiently large $n$ and every $v\in\{0,1\}^n$: on input $v$, $A$ halts within $T(n)$ steps, and with probability at least $2/3$ its output is the binary expansion of a nonnegative integer $\hat a$ with
--   $$|\hat a-\mu(v)|\le\psi(n).$$
--   With $\mu=\mathrm{qKt}$ this is Definition 6.12; Appendix F uses it with $\mathrm{qKt}^{(c)}$.
--
--   It is the hypothesis of Theorem 6.14 (estimation yields symmetry of information).
--
--   **Formalization Note** Halting is on every branch. The success probability is the sum of $P_A(v;T(n),\mathrm b(\hat a))$ over the finitely many integers $\hat a\ge0$ with $|\hat a-\mu(v)|\le\psi(n)$.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 6.12, p.83

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- **Definition 6.12** (Estimating qKt, p.83 of Myrisiotis, STOC 2027 submission, held version
sha256 6616571c…), for a measure `µ` of strings: a machine `A` **estimates `µ` within `ψ` in time `T`**
if for all sufficiently large `n` and every `v ∈ {0,1}ⁿ`, `A` on input `v` halts within `T(n)` steps
on every branch, and with probability at least `2/3` its output is the binary expansion `b(â)` of a
nonnegative integer `â` with `|â − µ(v)| ≤ ψ(n)`.

**Formalization Note** The success probability is the sum of `P_A(v; T(n), b(â))` over the finitely
many integers `â ≥ 0` with `|â − µ(v)| ≤ ψ(n)` (distinct `â` have distinct expansions `b(â)`).
"Halts within `T(n)` steps" is all-branch halting (Definition 3.4). The paper's definition is the
case `µ = qKt`; Appendix F uses it with `qKt^{(c)}`. -/
def Estimates (μ : List Bool → ℝ) (A : CodedMachine) (T ψ : ℕ → ℕ) : Prop :=
  ∃ n₀ : ℕ, ∀ v : List Bool, n₀ ≤ v.length →
    A.toMachine.HaltsWithin v (T v.length) ∧
      (2 / 3 : ℝ) ≤ ∑ a ∈ (Finset.range (⌈μ v⌉₊ + ψ v.length + 1)).filter
          (fun a : ℕ => |(a : ℝ) - μ v| ≤ ψ v.length),
        A.toMachine.outputProb v (T v.length) (bin a)

end QuantumKtSoI.Supplement


