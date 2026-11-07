-- Prove2me | Definitions.Def_QPACLarge_signMaj
-- name    : QPACLarge_signMaj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:27.040823+00:00
-- url     : https://prove2.me/theorems/cfc1512e-27ca-4f39-bd6b-6ca0e3e86645
-- title:
--   Sign of a sum $\mathrm{Sign}(B_1,\dots,B_m)$
-- statement:
--   For signs $B_1, \dots, B_m \in \{-1, +1\}$, $\mathrm{Sign}(B_1, \dots, B_m) \in \{-1, +1\}$ is the sign of $\sum_i B_i$.
--
--   **Formalization Note** A sum that is not positive gets $-1$; an odd number of $\pm1$ values never sums to $0$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.5, p.28

import Mathlib

namespace QPACLarge

/-- **The sign of a sum of signs.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.5, p.28: "`Sign(B₁, …, B_m) ∈ {−1, +1}` denotes the sign of their sum".

**Formalization Note.** A sum that is not positive gets `−1`; for an odd number of `±1` values
the sum is never `0`. -/
noncomputable def signMaj {m : ℕ} (B : Fin m → ℝ) : ℝ :=
  if 0 < ∑ i, B i then 1 else -1

end QPACLarge


