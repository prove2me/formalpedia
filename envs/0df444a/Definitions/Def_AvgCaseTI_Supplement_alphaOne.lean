-- Prove2me | Definitions.Def_AvgCaseTI_Supplement_alphaOne
-- name    : AvgCaseTI_Supplement_alphaOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:33:59.529884+00:00
-- url     : https://prove2.me/theorems/6680b512-b1bc-4c20-b6bf-e403c65fd0d3
-- title:
--   The proportion $\alpha(n,q)$ of matrices with a unique simple $\mathbb F_q$-eigenvalue
-- statement:
--   For a finite field $\mathbb F_q$,
--   $$
--   \alpha(n,q):=\frac{|C_1(n,q)|}{|\mathrm M(n,q)|},
--   $$
--   where $C_1(n,q)$ is the set of $A\in\mathrm M(n,q)$ that have exactly one eigenvalue in $\mathbb F_q$, of algebraic multiplicity $1$ (the eigenvalue may be $0$). Membership in $C_1(n,q)$ is the published predicate `UniqueSimpleEig`.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.3, p.37 (PDF p.39)

import Mathlib
import Definitions.Def_AvgCaseTI_UniqueSimpleEig

set_option autoImplicit false

namespace AvgCaseTI.Supplement

open AvgCaseTI

/-- **`α(n, q) = |C₁(n, q)| / |M(n, q)|`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.3, p.37 (PDF p.39): "Let α(n, q) := |C₁(n,q)| / |M(n,q)| be the probability of a random
matrix A ∈ M(n, q) which has only 1 eigenvalue in F_q with algebraic multiplicity 1."

The eigenvalue may be `0`; membership in `C₁(n, q)` is the published `UniqueSimpleEig`. -/
noncomputable def alphaOne (K : Type*) [Field K] (n : ℕ) : ℝ :=
  (Nat.card {A : Mat K n // UniqueSimpleEig A} : ℝ) / (Nat.card (Mat K n) : ℝ)

end AvgCaseTI.Supplement


