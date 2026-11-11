-- Prove2me | Definitions.Def_QMAvsQCMAH_PolyBounded
-- name    : QMAvsQCMAH_PolyBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:26.870218+00:00
-- url     : https://prove2.me/theorems/3cade519-92fb-4ef5-8c8d-b5a03533ab55
-- title:
--   Polynomially bounded functions
-- statement:
--   A function $f:\mathbb N\to\mathbb N$ is **polynomially bounded** if there is a polynomial $P$ with natural coefficients such that $f(n)\le P(n)$ for every $n$.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Section 3.2.2, p.20; Definition 13, p.27; Definition 18, p.29

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

/-- A function `f : ℕ → ℕ` is **polynomially bounded**: `f(n) ≤ P(n)` for some polynomial `P`
with natural coefficients and every `n`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Section 3.2.2, p.20 (PDF p.23): "Witness length, workspace, and query length are all
polynomial in n"; Definition 13, p.27: "q_λ = poly(λ) and symbols have b_λ = poly(λ)-bit
encodings"; Definition 18, p.29: "every polynomially bounded integer-valued c(λ) ≥ 0". -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n

end QMAvsQCMAH


