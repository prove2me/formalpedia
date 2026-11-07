-- Prove2me | Definitions.Def_LowTempGlauber_IsNPowLittleO
-- name    : LowTempGlauber_IsNPowLittleO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:00.321143+00:00
-- url     : https://prove2.me/theorems/30dafa56-7177-4c8d-a32b-ae30b324f189
-- title:
--   $T(n)=\tilde O(n^a)$: at most $n^{a+o(1)}$
-- statement:
--   The paper writes $\tilde O(g(n))$ for functions of the form $g(n)\,n^{o(1)}$ (footnote 1, p.2). For a step count $T:\mathbb N\to\mathbb N$ and a real exponent $a$, $T(n)=\tilde O(n^a)$ means: for every $\varepsilon>0$,
--   $$T(n)\le n^{a+\varepsilon}\quad\text{for all sufficiently large }n.$$
--
--   This is the form in which the running times $n^{3/2+o(1)}$ and $n^{2+o(1)}$ of Theorem 1 are stated.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), footnote 1, p.2, and p.3

import Mathlib

namespace LowTempGlauber

/-!
# `T(n) = Õ(n^a)`: at most `n^{a + o(1)}`

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), footnote 1, p.2
("we use `Õ(g(n))` to denote functions of the form `g(n) n^{o(1)}`") and p.3 ("asymptotics up to an
`n^{o(1)}` factor").

**Formalization Note.** As an upper bound on a step count `T : ℕ → ℕ`, `T(n) ≤ n^a · n^{o(1)}` means:
for every `ε > 0`, eventually `T(n) ≤ n^{a+ε}`.
-/

/-- `T(n) = Õ(n^a)`: for every `ε > 0`, `T(n) ≤ n^{a+ε}` for all large `n`. -/
def IsNPowLittleO (T : ℕ → ℕ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, (T n : ℝ) ≤ (n : ℝ) ^ (a + ε)

end LowTempGlauber


