-- Prove2me | Definitions.Def_NKtLB_RnKt
-- name    : NKtLB_RnKt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:10:45.131034+00:00
-- url     : https://prove2.me/theorems/40650238-523e-4736-b391-600265005ac5
-- title:
--   $R_{\mathrm{nKt}}[s]$: strings of high nKt complexity
-- statement:
--   For $s:\mathbb N\to\mathbb R$,
--   $$
--   R_{\mathrm{nKt}}[s]=\{x\in\{0,1\}^* : \mathrm{nKt}(x)\ge s(|x|)\}.
--   $$
--   For instance, $R_{\mathrm{nKt}}[\gamma\cdot n]$ is the set of strings $x$ with $\mathrm{nKt}(x)\ge\gamma|x|$.
--
--   **Formalization Note** The paper writes $s:\mathbb N\to\mathbb N$ but uses $s(n)=\gamma n$ with real $\gamma$. A real-valued $s$ covers both cases, and for integer-valued $s$ it is the paper's set.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12

import Mathlib
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_toEReal

namespace NKtLB

/-- **`R_{nKt}[s]`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12): "for `s: ℕ → ℕ`, we let
`R_{nKt[s]} = {x ∈ {0,1}^* | nKt(x) ≥ s(|x|)}`."

**Formalization Note.** `s : ℕ → ℝ`, so that `R_{nKt[γ·n]}` (Theorem 8) is `RnKt U (fun n => γ * n)`
without rounding; for integer-valued `s` it is the paper's set. -/
def RnKt (U : Machine) (s : ℕ → ℝ) : Set (List Bool) :=
  {x | ((s x.length : ℝ) : EReal) ≤ toEReal (nKt U ∅ ⊤ x [] [])}

end NKtLB


