-- Prove2me | Definitions.Def_BehrendWindows_AtMostTwoPerAP
-- name    : BehrendWindows_AtMostTwoPerAP
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T01:46:05.691988+00:00
-- url     : https://prove2.me/theorems/1ec77d83-43cf-4246-9833-efe47960a9b7
-- title:
--   $m$-sparse sets: at most two points on every $m$-term progression
-- statement:
--   A finite set $T\subset\mathbb{Z}$ is **$m$-sparse** if no arithmetic progression of $m$ terms with non-zero common difference contains three elements of $T$. Precisely, $T$ is $m$-sparse when for all $a\in\mathbb{Z}$, all $d\in\mathbb{Z}$ with $d\neq 0$, and all natural numbers $k_1<k_2<k_3<m$,
--
--   $$\neg\big(a+k_1d\in T\ \wedge\ a+k_2d\in T\ \wedge\ a+k_3d\in T\big).$$
--
--   For $m\le 2$ the condition is vacuous. A set is $3$-sparse exactly when it contains no non-trivial three-term arithmetic progression (a Salem–Spencer set), and an $m$-sparse set is $m'$-sparse for every $m'\le m$.
--
--   **Formalization Note** The positions $k_i$ are natural numbers cast to $\mathbb{Z}$. The hypothesis $d\neq 0$ is essential: with $d=0$ every non-empty set would fail the condition for $m\ge 3$.
-- source:
--   No published source states the version uniform in m; statement from the mission proposal, Setting section; m = 3 is the Salem-Spencer / Behrend notion, F. A. Behrend, On sets of integers which contain no three terms in arithmetical progression, PNAS 32 (1946) 331-332, https://doi.org/10.1073/pnas.32.12.331

import Mathlib

namespace BehrendWindows

/-- `T` is `m`-sparse: no arithmetic progression of `m` terms with non-zero
common difference contains three elements of `T`. -/
def AtMostTwoPerAP (T : Finset ℤ) (m : ℕ) : Prop :=
  ∀ a d : ℤ, d ≠ 0 → ∀ k₁ k₂ k₃ : ℕ, k₁ < k₂ → k₂ < k₃ → k₃ < m →
    ¬ (a + k₁ * d ∈ T ∧ a + k₂ * d ∈ T ∧ a + k₃ * d ∈ T)

end BehrendWindows


