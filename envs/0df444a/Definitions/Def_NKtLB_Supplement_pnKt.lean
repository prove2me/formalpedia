-- Prove2me | Definitions.Def_NKtLB_Supplement_pnKt
-- name    : NKtLB_Supplement_pnKt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:21:29.181528+00:00
-- url     : https://prove2.me/theorems/25506fbb-0c93-4fe3-95f7-fe979bdb51ab
-- title:
--   $pn\mathrm{Kt}^O_\lambda(x\mid y)$ — probabilistic nondeterministic Levin–Kolmogorov complexity (Definition 22)
-- statement:
--   For $\lambda\in[0,1]$,
--   $$
--   pn\mathrm{Kt}_\lambda(x\mid y)=\min\Bigl\{\,s\in\mathbb N : \Pr_{r\sim\{0,1\}^{2^s}}\bigl[n\mathrm{Kt}(x\mid y;r)\le s\bigr]\ge\lambda\Bigr\},
--   $$
--   where $n\mathrm{Kt}$ is Definition 18 (base mission). It appears in Theorems 56, 59 and 66.
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). Random string of length $2^s$, as printed; inner measure `NKtLB.nKt` without query bound; values in `ℕ∞`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 22, p.24

import Mathlib
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`pnKt_λ(x | y)`, probabilistic nondeterministic Levin–Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Definition 22, p.24): "`pnKt_λ(x | y) ≜ min { s ∈ ℕ : Pr_{r∼{0,1}^{2^s}}[nKt(x | y; r) ≤ s] ≥ λ }`."

**Formalization Note.** Random string of length `2^s`, as printed; inner measure the base
`nKt U O ⊤ x y r` (Definition 18, no query bound). Value in `ℕ∞`. -/
noncomputable def pnKt (U : Machine) (O : Set (List Bool)) (lam : ℝ) (x y : List Bool) : ℕ∞ :=
  ⨅ (s : ℕ) (_ : lam ≤ prob (2 ^ s) (fun r => nKt U O ⊤ x y r ≤ (s : ℕ∞))), (s : ℕ∞)

end NKtLB.Supplement


