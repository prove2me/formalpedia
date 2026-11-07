-- Prove2me | Definitions.Def_PCNonBool_tau
-- name    : PCNonBool_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:07.427211+00:00
-- url     : https://prove2.me/theorems/9ae62508-f794-4f3c-a51d-b926e69dcbe6
-- title:
--   Number of rounds $\tau=s/(10(2\Delta+3))$
-- statement:
--   Algorithm 1 sets
--   $$\tau=\frac{s}{10\,(2\Delta+3)}$$
--   and runs its loop for $1\le\ell\le\tau$, i.e. for $\lfloor\tau\rfloor$ rounds.
--
--   **Formalization Note** $\tau$ is real; the number of rounds is $\lfloor\tau\rfloor$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Algorithm 1, line 8, p.30 (PDF p.33)

import Mathlib

namespace PCNonBool

/-- The round parameter of Algorithm 1, `τ = s / (10 · (2Δ + 3))` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Algorithm 1,
line 8, p.30 (PDF p.33)). It is a real number; the loop `for 1 ≤ ℓ ≤ τ` runs `⌊τ⌋` rounds. -/
noncomputable def tau (s Δ : ℕ) : ℝ := (s : ℝ) / (10 * (2 * (Δ : ℝ) + 3))

end PCNonBool


