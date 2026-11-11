-- Prove2me | Definitions.Def_FasterPrimeEnum_idealCount
-- name    : FasterPrimeEnum_idealCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:37:49.688198+00:00
-- url     : https://prove2.me/theorems/ce9e6c50-4207-49e0-aac3-bd527b4b41bb
-- title:
--   $\psi_d(n)$: ideals of $\mathbb Z[\sqrt d]$ of norm $n$
-- statement:
--   For $d\in D$ and an odd integer $n\ge1$, $\psi_d(n)$ is the number of ideals of $\mathbb Z[\sqrt d]$ of norm $n$; for even $n$, $\psi_d(n)=0$. The generating series is $\Psi_d(x)=\sum_{n\ge1}\psi_d(n)x^n$.
--
--   Proposition 2.9 expresses $\Psi_d$ through $F$ and $H_d$, which is how the arithmetic of $\mathbb Z[\sqrt d]$ enters the prime detection.
--
--   **Formalization Note** $\mathbb Z[\sqrt d]$ is Mathlib's `ℤ√d`, and the norm of an ideal $I$ is its index $|\mathbb Z[\sqrt d]/I|$, which equals the absolute norm on nonzero ideals; the zero ideal has infinite index and is never counted.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §2, p.15

import Mathlib

set_option autoImplicit false

namespace FasterPrimeEnum

/-- **`ψ_d(n)`, the number of ideals of `Z[√d]` of norm `n`** — D. Harvey, *Faster enumeration of
primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), §2, p.15: "For odd n ⩾ 1, let ψ_d(n)
denote the number of ideals in Z[√d] of norm n, and set ψ_d(n) := 0 for even n."
The generating series is `Ψ_d(x) := Σ_{n⩾1} ψ_d(n) x^n`, so `idealCount d n` is its coefficient
of `x^n`.

**Formalization Note.** `Z[√d]` is Mathlib's `ℤ√d` (`Zsqrtd d`). The norm of an ideal `I` is its
index `Nat.card (ℤ√d ⧸ I)`, which equals the absolute norm on nonzero ideals; the zero ideal has
infinite index, and `Nat.card` of an infinite type is `0`, so it is never counted at odd `n`. For
each `n ⩾ 1` only finitely many ideals have index `n`, so `Nat.card` here is the true count. -/
noncomputable def idealCount (d : ℤ) (n : ℕ) : ℕ :=
  if n % 2 = 1 then Nat.card {I : Ideal (ℤ√d) // Nat.card (ℤ√d ⧸ I) = n} else 0

end FasterPrimeEnum


