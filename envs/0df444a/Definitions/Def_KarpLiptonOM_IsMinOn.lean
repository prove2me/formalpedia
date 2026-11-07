-- Prove2me | Definitions.Def_KarpLiptonOM_IsMinOn
-- name    : KarpLiptonOM_IsMinOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:29.53937+00:00
-- url     : https://prove2.me/theorems/773e8919-10a3-4fab-9c07-23056a984bda
-- title:
--   Minimum of an order on $\{0,1\}^m$
-- statement:
--   A string $\mu$ is the **minimum** of a relation $\prec$ on $\{0,1\}^m$ if $|\mu| = m$ and no $u \in \{0,1\}^m$ satisfies $u \prec \mu$. For a strict linear order on $\{0,1\}^m$ the minimum exists and is unique.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definitions A.2.7 and A.2.9, pp.22–23

import Mathlib

namespace KarpLiptonOM

/-- `μ` is the minimum of `R` on `{0,1}^m`: `|μ| = m` and no `u ∈ {0,1}^m` satisfies `R u μ`
(Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Definitions A.2.7, A.2.9, pp.22–23, "min ≺ₓ", "µₙ = min <ₙ").

**Formalization Note** For a strict linear order on the finite nonempty set `{0,1}^m` such a `μ`
exists and is unique. -/
def IsMinOn (m : ℕ) (R : List Bool → List Bool → Prop) (μ : List Bool) : Prop :=
  μ.length = m ∧ ∀ u, u.length = m → ¬ R u μ

end KarpLiptonOM


