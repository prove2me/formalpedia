-- Prove2me | Definitions.Def_LawLocalComp_clauseU1
-- name    : LawLocalComp_clauseU1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:14:23.41926+00:00
-- url     : https://prove2.me/theorems/4c06b303-fc47-434f-b9f7-87c55dd81009
-- title:
--   Theorem 1.1, row 1 upper: horizon $N$, order $\varepsilon^{-1/2}\log(N+1)$
-- statement:
--   There are an absolute constant $C>0$ and a family of law-local maps $\Phi_{\varepsilon,N}$, computable by one polynomial-time machine that reads $\varepsilon$ and $N$ in binary and a unary pad of length $\lceil1/\varepsilon\rceil$, such that for every rational $0<\varepsilon\le1$ and every horizon $N\ge2$:
--   1. for every rational law $X$, $\Phi_{\varepsilon,N}(X)$ is a rational conditional-mean replacement of $X$ that preserves the mean and point masses and has at most $C\,\varepsilon^{-1/2}\log(N+1)$ atoms;
--   2. $\Phi_{\varepsilon,N}$ satisfies (1), $\mathbb E g(\tilde L)\le\mathbb E g(L)\le(1+\varepsilon)\mathbb E g(\tilde L)$, for every selection of at most $N$ independent rational jobs, all nonnegative directions and every monotone norm.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; proof in "Endpoint transfer", p.7

import Mathlib
import Definitions.Def_LawLocalComp_IsGoodOutput
import Definitions.Def_LawLocalComp_Contract
import Definitions.Def_LawLocalComp_PolyLawMap

namespace LawLocalComp

/-- **Row 1 upper of Theorem 1.1 (horizon `N`, order `ε^{-1/2} log(N+1)`).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

There is an absolute constant `C` and one polynomial-time family of law-local maps `Φ(ε, N)` such
that for rational `0 < ε ≤ 1` and every horizon `N ≥ 2`, `Φ(ε, N)` sends every rational law to a
rational conditional-mean replacement preserving the mean and point masses, with at most
`C ε^{-1/2} log(N + 1)` atoms, and satisfies (1) for every selection of at most `N` jobs.
The machine reads `ε` and `N` in binary and a unary pad of length `⌈1/ε⌉`.
-/
def clauseU1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Φ : ℚ × ℕ → Law → Law,
    PolyLawMap (fun p => [p.1, (p.2 : ℚ)]) (fun p => ⌈1 / p.1⌉₊) (fun _ => True) Φ ∧
    ∀ ε : ℚ, 0 < ε → ε ≤ 1 → ∀ N : ℕ, 2 ≤ N →
      (∀ X : Law, IsRatLaw X → IsGoodOutput X (Φ (ε, N) X) ∧
        ((Φ (ε, N) X).w.support.card : ℝ) ≤ C * (1 / Real.sqrt ε) * Real.log (N + 1)) ∧
      Contract (Φ (ε, N)) (.horizon N) (fun _ => True) (1 + ε)

end LawLocalComp


