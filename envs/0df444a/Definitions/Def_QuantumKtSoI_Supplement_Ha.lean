-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_Ha
-- name    : QuantumKtSoI_Supplement_Ha
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:24:49.166048+00:00
-- url     : https://prove2.me/theorems/04e3fe7e-d649-4d90-9bbf-bc3c5d153f7b
-- title:
--   The clocks $\Lambda_2$, $F_a$ and $H_a$ of §4.5
-- statement:
--   For integers $N\ge 0$ and $a\ge 1$ put
--   $$\Lambda_2(N)=\big\lceil\log\lceil\log(N+4)\rceil\big\rceil,\qquad F_a(N)=2^{\Lambda_2(N)^a},\qquad H_a(N)=2^{F_a(N)} .$$
--   All three are nondecreasing and integer valued, and $H_a(N)\ge N+4$. For $a\ge 2$ the clock $H_a$ eventually exceeds every fixed quasipolynomial $2^{(\log N)^c}$, while $\log H_a(N)=N^{o(1)}$.
--
--   These are the explicit time bounds at which the gap lower bound (Theorem 4.13) and the worst-case symmetry failure (Theorem 5.10) are stated.
--
--   **Formalization Note** Logarithms are base $2$ and $\lceil\log m\rceil$ is `Nat.clog 2 m`, exact for integers $m\ge1$.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §4.5, p.48

import Mathlib

namespace QuantumKtSoI.Supplement

/-- `Λ₂(N) = ⌈log(⌈log(N+4)⌉)⌉` (§4.5, p.48 of Myrisiotis, *Failure of Symmetry of Information
for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…).

**Formalization Note** `⌈log₂ m⌉` is `Nat.clog 2 m`, exact for every integer `m ≥ 1`; both
arguments here are at least `2`. -/
def Lam2 (N : ℕ) : ℕ := Nat.clog 2 (Nat.clog 2 (N + 4))

/-- `F_a(N) = 2^{Λ₂(N)^a}` (§4.5, p.48). -/
def Fa (a N : ℕ) : ℕ := 2 ^ (Lam2 N ^ a)

/-- The clock `H_a(N) = 2^{F_a(N)}` (§4.5, p.48), for integers `N ≥ 0` and `a ≥ 1`. -/
def Ha (a N : ℕ) : ℕ := 2 ^ Fa a N

end QuantumKtSoI.Supplement


