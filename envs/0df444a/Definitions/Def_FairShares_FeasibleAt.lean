-- Prove2me | Definitions.Def_FairShares_FeasibleAt
-- name    : FairShares_FeasibleAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:17.878304+00:00
-- url     : https://prove2.me/theorems/900e1241-0567-4e4c-a732-a3817ce5cecf
-- title:
--   Feasible share, at fixed $m$ and $n$
-- statement:
--   Fix $m$ goods and $n$ agents, a set $D$ of valuations and a share $t$ (the paper's $s(\cdot,n)$). The share is **feasible** on $D$ if for every profile $(v_0,\dots,v_{n-1})$ of valuations in $D$ there is an allocation $A$ that gives every agent an acceptable bundle:
--   $$
--   v_i(A_i)\ge t(v_i)\qquad\text{for every agent } i .
--   $$
--
--   **Formalization Note** Allocations are maps `Fin m → Fin n` (`FairShares.bundle`).
-- source:
--   Babaioff & Feige, Fair Shares: Feasibility, Domination and Incentives, arXiv:2205.07519v1, §3.1, p.10

import Mathlib
import Definitions.Def_FairShares_bundle

namespace FairShares

/-- **Feasible share, at a fixed number of items and agents.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*, arXiv:2205.07519v1, §3.1, p.10: "For a class C of valuation functions, we say that a share s for C is feasible
if for any agents' valuation vector v = (v1, . . . , vn) such that vi ∈ C for every i, there exists
an acceptable allocation A: an allocation that gives every agent an acceptable bundle. That is,
for every agent i the bundle Ai has value at least her share: vi(Ai) ≥ s(vi, n)."

`FeasibleAt n D t`: for every profile `vs : Fin n → _` of valuations in `D` there is an allocation
`A : Fin m → Fin n` with `t (vs i) ≤ vs i (A⁻¹ i)` for every agent `i`.

**Formalization Note.** Allocations are maps `Fin m → Fin n` (see `FairShares.bundle`); the
share `t` is the paper's `s(·, n)` at the given `n`. -/
def FeasibleAt {m : ℕ} (n : ℕ) (D : Set (Finset (Fin m) → ℝ))
    (t : (Finset (Fin m) → ℝ) → ℝ) : Prop :=
  ∀ vs : Fin n → (Finset (Fin m) → ℝ), (∀ i, vs i ∈ D) →
    ∃ A : Fin m → Fin n, ∀ i, t (vs i) ≤ vs i (bundle A i)

end FairShares


