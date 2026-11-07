-- Prove2me | Definitions.Def_CallCountPOPBR_Instance_IsValid
-- name    : CallCountPOPBR_Instance_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:05:05.293848+00:00
-- url     : https://prove2.me/theorems/6f12903e-b038-4757-b5b0-b68af3245e06
-- title:
--   Well-formed POPBR instance
-- statement:
--   A POPBR instance $(N,d,p,\mathrm{Obs})$ is **well formed** when
--   $$
--   1\le d\le N,\qquad 1\le p\le N+1,
--   $$
--   the observation list has exactly $N+1$ entries (one per index $0,\dots,N$), and every observed value is a positive integer.
--
--   These are the conditions Definition 2.1 places on an instance.
--
--   **Formalization Note** $N\ge1$ follows from $1\le d\le N$. Entry $n$ of the list is read with default `none`, so indices beyond $N$ count as unobserved.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Definition 2.1, p.4

import Definitions.Def_CallCountPOPBR_Instance

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Well-formed POPBR instance** (Definition 2.1). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Definition 2.1, p.4: "positive
integers N, d, p with 1 ≤ d ≤ N and 1 ≤ p ≤ N + 1, and a partial map Obs : {0, …, N} ⇀ ℤ_{>0}.
The map Obs is encoded as a list of N + 1 entries".

**Formalization Note.** `N ≥ 1` follows from `1 ≤ d ≤ N`. `I.obs.getD n none` is `Obs(n)`
(`none` when `n` is unobserved or `n > N`); every observed value is a positive integer. -/
def Instance.IsValid (I : Instance) : Prop :=
  I.obs.length = I.N + 1 ∧ 1 ≤ I.d ∧ I.d ≤ I.N ∧ 1 ≤ I.p ∧ I.p ≤ I.N + 1 ∧
    ∀ (n v : ℕ), I.obs.getD n none = some v → 0 < v

end CallCountPOPBR


