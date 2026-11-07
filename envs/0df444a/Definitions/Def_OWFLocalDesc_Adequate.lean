-- Prove2me | Definitions.Def_OWFLocalDesc_Adequate
-- name    : OWFLocalDesc_Adequate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:31.091872+00:00
-- url     : https://prove2.me/theorems/079921dc-4f15-4af9-ab24-6e7026856400
-- title:
--   Adequate clock for a PAC-style sampler (Definition 3.2)
-- statement:
--   A polynomial schedule $t$ is **adequate** for $D$ (with coding header $\sigma_Q$) if for every $n$:
--
--   1. $t(n)\ge q(n)\,(q(n)+3)$, and
--   2. for every payload $v$ of length at most $q(n)+2$, every query of length $n$ and every public tape of length $t(n)$, the program $\sigma_Q v$ with the empty anchor list halts on $U$ within $t(n)$ steps.
--
--   **Formalization Note** Point lengths are positive.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Definition 3.2, p.15

import Mathlib
import Definitions.Def_OWFLocalDesc_Decoder
import Definitions.Def_OWFLocalDesc_PACSampler
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Adequate clock (Definition 3.2).** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Definition 3.2, p.15: "A
polynomial schedule t is adequate for D if two conditions hold for every n. First,
t(n) ≥ q(n)(q(n)+3). Second, let v be any payload of length at most q(n)+2. On every query of
length n and every public tape, the program σ_Q v with the empty anchor list must halt on U within
t(n) steps."

**Formalization Note.** The public tape has the clock's length `t(n)`; "halts within `t(n)`
steps" is `run … (t n)` being `some _` (runs are monotone). Point lengths are positive (§2,
p.11). The header `σ` is a parameter (see `IsCodingHeader`). -/
def Adequate (U : Decoder) (D : PACSampler) (σ : List Bool) (t : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → D.q n * (D.q n + 3) ≤ t n ∧
    ∀ v : List Bool, v.length ≤ D.q n + 2 → ∀ (w : Fin (t n) → Bool) (z : Fin n → Bool),
      (U.run (σ ++ v) [] (List.ofFn w) (List.ofFn z) (t n)).isSome

end OWFLocalDesc


