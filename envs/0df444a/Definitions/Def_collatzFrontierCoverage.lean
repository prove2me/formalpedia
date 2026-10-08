-- Prove2me | Definitions.Def_collatzFrontierCoverage
-- name    : collatzFrontierCoverage
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-04T17:57:58.779976+00:00
-- url     : https://prove2.me/theorems/2893e840-c968-4ddc-87e4-ff84708a000a
-- title:
--   Executable failure-rate counters for the descent-certificate checker (bounded test, failure count, automatic width)
-- statement:
--   This module fixes the executable coverage/failure-rate counters for the descent-certificate checker of `Def_collatzFrontierCertificate`. `boundedCertificateTest L m n` is one fully specified, finite call to the actual executable checker: it runs the generator `candidateCertificate` on input `n` with $4m$ descent steps and fuel/modulus exponent $L + 8m$, then checks the result with `checkDescent` (returning `false` outright when $m = 0$). `boundedCertificateFailureCount R L m` counts, among the first $R$ positive odd integers $2i+1$ ($i < R$), how many are rejected by `boundedCertificateTest L m`; this is a genuinely computable natural number, built from `Finset.filter` and a `Decidable` predicate — not an unbounded existential membership test. `automaticCertificateFailureCount R m` is the same count with the ambient bit-width $L$ computed automatically from $R$ (as $L = \mathrm{Nat.clog}\,2\,(2R)$, the least $L$ with $2R \le 2^L$), so the failure count becomes a function of $R$ and the accuracy parameter $m$ alone:
--   $$\mathrm{automaticCertificateFailureCount}(R,m) = \#\{\,i<R : \mathrm{boundedCertificateTest}(L,m,2i+1) = \mathrm{false}\,\},\quad L=\lceil\log_2(2R)\rceil.$$
--
--   **Role.** `automaticCertificateFailureCount` is the quantity bounded by the explicit failure-rate theorem and shown to vanish asymptotically by the asymptotic-coverage theorem in this contribution.
--
--   **Formalization Note.** Verbatim defs-only transcription of `lean/CollatzFrontier/ExecutableCertificateCoverage.lean` on the cited branch.
-- source:
--   collatz-frontier (private repo), branch research/executable-coverage-20261002 @ 3835de1c8e7bf56d5632af07979d0fd2d580095c (stacks on research/certificate-density-20261002 @ 61e6b54c74e600c8c72fc2d271f5b4d11e9e8869 and main @ 4d656b9c9c5815305bd391f206c9d3e9587dd395); lean/CollatzFrontier/ExecutableCertificateCoverage.lean (definitions only)

import Definitions.Def_collatzFrontierCertificate
import Mathlib.Data.Nat.Log

/-
Executable coverage/failure-rate counters for the descent-certificate checker, taken
verbatim (defs only, no proofs) from `lean/CollatzFrontier/ExecutableCertificateCoverage.lean`
on branch research/executable-coverage-20261002 @ 3835de1.

`boundedCertificateTest` is one fully specified, finite call to the actual executable
checker on the generated candidate certificate at a fixed accuracy parameter `m` (budget
`4m` steps, fuel/modulus exponent `L + 8m`). `boundedCertificateFailureCount` counts, among
the first `R` positive odd integers, how many are rejected by this one finite test; it is a
genuinely computable `Nat`, built from `Finset.filter` and `Decidable`, not an unbounded
existential search. `automaticCertificateFailureCount` fixes the ambient bit-width `L`
automatically (as `Nat.clog 2 (2 * R)`, the least `L` with `2 * R ≤ 2 ^ L`) so the count
depends only on `R` and `m`.
-/

namespace CollatzFrontier

/-- One fully specified, finite call to the actual executable checker: candidate exponent
budget and modulus exponent both `L + 2 * (4 * m)`, over `4 * m` descent steps, at
accuracy parameter `m`. Fails (returns `false`) when `m = 0` or the checker rejects. -/
def boundedCertificateTest (L m n : ℕ) : Bool :=
  if m = 0 then false else
    checkDescent (candidateCertificate (L + 2 * (4 * m)) (4 * m - 1) n
      (2 ^ (L + 2 * (4 * m))))

/-- Among the first `R` positive odd integers `2*i+1` (`i < R`), the number rejected by
`boundedCertificateTest L m`. A genuinely computable `Nat.card`-style count. -/
def boundedCertificateFailureCount (R L m : ℕ) : ℕ :=
  ((Finset.range R).filter (fun i => boundedCertificateTest L m (2 * i + 1) = false)).card

/-- The same failure count with the ambient bit-width `L` computed automatically from `R`
(as the least `L` with `2 * R ≤ 2 ^ L`), so the count is a function of `R` and `m` alone. -/
def automaticCertificateFailureCount (R m : ℕ) : ℕ :=
  boundedCertificateFailureCount R (Nat.clog 2 (2 * R)) m

end CollatzFrontier


