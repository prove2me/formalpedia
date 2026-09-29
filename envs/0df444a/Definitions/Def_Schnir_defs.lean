-- Prove2me | Definitions.Def_Schnir_defs
-- name    : Schnir_defs
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-26T22:46:54.834873+00:00
-- url     : https://prove2.me/theorems/55b5ef4e-f71c-4097-9272-97193118028a
-- title:
--   Definitions for the explicit Schnirelmann constant $100\,001$
-- statement:
--   Definitions used throughout the explicit Schnirelmann argument showing that every odd $n>1$ is a sum of at most $100\,001$ primes.
--
--   1. $r(s)=\#\{(p,q): p,q \text{ odd primes},\ p+q=s\}$, the number of ordered representations of $s$ as a sum of two odd primes (`Schnir.r`).
--   2. $C(s)=\prod_{p\mid s}\left(1+\frac{p}{(p-1)^2}\right)$, the arithmetic factor in the sieve bound (`Schnir.C`).
--   3. For a fixed $s$ and a prime $p$: $\rho_s(p)=1$ if $p\mid s$ and $\rho_s(p)=2$ otherwise, the number of roots of $a(s-a)\equiv 0 \pmod p$ (`Schnir.rho`).
--   4. $h_s(d)=\prod_{p\mid d}\frac{\rho_s(p)}{p-\rho_s(p)}$ (`Schnir.hfun`), and the sieve denominator $G_s(z)=\sum_{d\le z,\ d \text{ squarefree}} h_s(d)$ (`Schnir.G`).
--   5. $S_s(z)=\#\{1\le a\le s : a(s-a) \text{ has no prime divisor } \le z\}$, the sifted count (`Schnir.S`).
--   6. $B=\{(p-3)/2 : p \text{ an odd prime}\}$ and $A=B+B$ (`Schnir.B`, `Schnir.A`).
--
--   **Formalization Note** Everything lives in the namespace `Schnir`. $G_s(z)$ sums over $1\le d\le\lfloor z\rfloor$, and $S_s(z)$ tests primes $p\le\lfloor z\rfloor$. The quantities $h_s$ and $G_s$ are intended for even $s$, where every denominator $p-\rho_s(p)$ is positive.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), §§1–5 (definitions of r(s), C(s) eq. (5), ρ, g, h, G_s(z), S_s(z), B, A)

import Mathlib

/-!
Definitions for the explicit Schnirelmann argument (note: "An explicit elementary constant for
sums of primes"). Shared definitions for the mission's step lemmas.
-/

open Finset

namespace Schnir

/-- `r s` = number of ordered pairs `(p, q)` of odd primes with `p + q = s` (note, §Intro). -/
def r (s : ℕ) : ℕ :=
  ((Finset.range (s + 1)).filter (fun p => p.Prime ∧ p ≠ 2 ∧ (s - p).Prime ∧ s - p ≠ 2)).card

/-- `C s = ∏_{p ∣ s} (1 + p/(p-1)^2)` (note, eq. (5)). -/
noncomputable def C (s : ℕ) : ℝ := ∏ p ∈ s.primeFactors, (1 + (p : ℝ) / ((p : ℝ) - 1) ^ 2)

/-- `ρ_s(p)`: number of roots of `a (s - a) ≡ 0 mod p` (note, §2.1). -/
def rho (s p : ℕ) : ℕ := if p ∣ s then 1 else 2

/-- `h(d) = ∏_{p ∣ d} ρ(p)/(p - ρ(p))` on squarefree `d` (note, §2.1). -/
noncomputable def hfun (s d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, ((rho s p : ℝ) / ((p : ℝ) - (rho s p : ℝ)))

/-- `G_s(z) = ∑_{d ≤ z, d squarefree} h(d)` (note, §2.1). -/
noncomputable def G (s : ℕ) (z : ℝ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 ⌊z⌋₊).filter Squarefree, hfun s d

/-- `S_s(z)`: number of `1 ≤ a ≤ s` such that `a (s - a)` has no prime divisor `≤ z`. -/
noncomputable def S (s : ℕ) (z : ℝ) : ℕ :=
  ((Finset.Icc 1 s).filter
    (fun a => ∀ p ∈ Finset.range (⌊z⌋₊ + 1), p.Prime → ¬ p ∣ a * (s - a))).card

/-- `B = {(p - 3)/2 : p odd prime}` (note, §5). -/
def B : Set ℕ := {b | ∃ p, p.Prime ∧ p ≠ 2 ∧ b = (p - 3) / 2}

open Pointwise in
/-- `A = B + B` (note, §5). -/
def A : Set ℕ := B + B

end Schnir


