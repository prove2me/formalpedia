-- Prove2me | Definitions.Def_NKtLB_IsTimeConstructible
-- name    : NKtLB_IsTimeConstructible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:01:17.430981+00:00
-- url     : https://prove2.me/theorems/63dd520d-fddb-4f7a-b52b-af6a356c2553
-- title:
--   Time-constructible functions
-- statement:
--   $T:\mathbb N\to\mathbb N$ is **time-constructible** if some machine, on input $1^n$, outputs $1^{T(n)}$ within $c\,T(n)+c$ steps for a constant $c$. This is the standard notion that Lemma 45 assumes.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 45, p.30 (standard notion, not defined in the paper)

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB

/-- **Time-constructible functions** (hypothesis of Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Lemma 45, p.30; standard, not defined in
the paper): some machine on input `1^n` outputs `1^{T(n)}` within `c·T(n) + c` steps. -/
def IsTimeConstructible (T : ℕ → ℕ) : Prop :=
  ∃ (M : Machine) (c : ℕ), ∀ n : ℕ,
    M.Computes (c * T n + c) (List.replicate n true) (List.replicate (T n) true)

end NKtLB


