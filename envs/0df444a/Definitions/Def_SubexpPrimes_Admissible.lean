-- Prove2me | Definitions.Def_SubexpPrimes_Admissible
-- name    : SubexpPrimes_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:00:05.067592+00:00
-- url     : https://prove2.me/theorems/192d84d8-56c0-4104-9428-484f0745569f
-- title:
--   Admissible constraint
-- statement:
--   A constraint $C$ on $n$-bit strings, given by a description $d$ of length $L$, is **admissible** if from $(1^n,d)$ one can construct, in time $\mathrm{poly}(n+L)$, a functional representation of $C$ with $O(n)$ edges and degree $O(n^{3/4})$, whose entries are computable in time $\mathrm{poly}(n+L)$.
--
--   Admissible constraints are the ones the paper's algorithms can attach to a network at linear cost.
--
--   **Formalization Note** Admissibility is a property of the family $(n,d)\mapsto C_{n,d}$, with one set of constants, and the size bounds are stated for $n\ge1$.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Definition 2.3, p.15

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_ExplicitFamily

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT

/-- The input `(1ⁿ, d)` of Definition 2.3 for a description word `d`. -/
def admissibleInput (n : ℕ) (d : List Bool) : List Bool :=
  Encoding.encodeList id [List.replicate n true, d]

/-- **Admissible constraint** — Gajulapalli, *Deterministic Construction of Primes in
Subexponential Time* (manuscript, sha256 6ad4d3de…), Definition 2.3, p.15.

A constraint `C n d` on `n`-bit strings, with description `d` encoded by `encD`, of length
`L = |encD d|`, is admissible if from `(1ⁿ, encD d)` one can construct in time `poly(n + L)` a
functional representation of `C n d` with `O(n)` edges and degree `O(n^{3/4})`, whose entries are
computable in polynomial time.

**Formalization Note.** Admissibility is a property of the family `(n, d) ↦ C n d`, with one set
of constants; the bounds are stated for `n ≥ 1`, since `O(n)` edges has no sense at `n = 0`. A
constraint is a predicate on `List Bool`, applied to words of length `n` with the most significant
bit first. -/
def Admissible {δ : Type*} (encD : δ → List Bool) (C : ℕ → δ → List Bool → Prop) : Prop :=
  HasLinearRep (fun p : ℕ × δ => admissibleInput p.1 (encD p.2)) (fun p => 1 ≤ p.1)
    (fun p => p.1) (fun p => p.1) (fun p => C p.1 p.2)

end SubexpPrimes


