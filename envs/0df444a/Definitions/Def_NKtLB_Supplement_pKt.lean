-- Prove2me | Definitions.Def_NKtLB_Supplement_pKt
-- name    : NKtLB_Supplement_pKt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:19:33.948465+00:00
-- url     : https://prove2.me/theorems/6fc063df-375e-47a3-b16e-757abc02cf50
-- title:
--   $p\mathrm{Kt}^O_\lambda(x\mid y)$ — probabilistic Levin–Kolmogorov complexity (Definition 16)
-- statement:
--   For $\lambda\in[0,1]$,
--   $$
--   p\mathrm{Kt}_\lambda(x\mid y)=\min\Bigl\{\,s\in\mathbb N : \Pr_{r\sim\{0,1\}^{2^s}}\bigl[\mathrm{Kt}(x\mid y;r)\le s\bigr]\ge\lambda\Bigr\}.
--   $$
--   The random string has length $2^s$, as printed. It appears in Theorem 56 and is one of the five measures of Theorem 66.
--
--   **Formalization Note** All measures are taken with respect to a fixed universal machine $U$ of the base mission (program format $s_\alpha 01\langle M\rangle\alpha$, §3.2), with oracle $O$ given to $U$ ($O=\emptyset$ for the unrelativized measure). Values in `ℕ∞`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Definition 16, p.23

import Mathlib
import Definitions.Def_NKtLB_Supplement_Kt
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`pKt_λ(x | y)`, probabilistic Levin–Kolmogorov complexity** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Definition 16, p.23):
"`pKt_λ(x | y) ≜ min { s ∈ ℕ : Pr_{r∼{0,1}^{2^s}}[Kt(x | y; r) ≤ s] ≥ λ }`."

**Formalization Note.** The random string has length `2^s`, as printed. Inner measure `Kt`
(Definition 12) with the same oracle. Value in `ℕ∞`. -/
noncomputable def pKt (U : Machine) (O : Set (List Bool)) (lam : ℝ) (x y : List Bool) : ℕ∞ :=
  ⨅ (s : ℕ) (_ : lam ≤ prob (2 ^ s) (fun r => Kt U O x y r ≤ (s : ℕ∞))), (s : ℕ∞)

end NKtLB.Supplement


