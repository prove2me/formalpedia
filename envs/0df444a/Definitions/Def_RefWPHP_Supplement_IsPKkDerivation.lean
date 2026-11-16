-- Prove2me | Definitions.Def_RefWPHP_Supplement_IsPKkDerivation
-- name    : RefWPHP_Supplement_IsPKkDerivation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:20:26.806774+00:00
-- url     : https://prove2.me/theorems/abbe73e3-a460-48c1-acdf-3e262351377d
-- title:
--   The systems PK$^k_d$ and $\mathrm{Res}(k)$: derivations and refutations with bounded bottom fan-in
-- statement:
--   For $k, d \in \mathbb N$, the system $\mathrm{PK}^k_d$ is the subsystem of the cedent calculus PK "in which the formulas have depth $d+1$, but where all gates at depth $d$ have fan-in at most $k$". A $\mathrm{PK}^k_d$-derivation from a set $\Phi$ of cedents is a sequence of cedents in which
--
--   1. every cedent is in $\Phi$ or follows from earlier cedents by one rule of PK,
--   2. every formula of every cedent has depth at most $d+1$, and
--   3. every conjunction or disjunction at distance exactly $d$ from the root of a formula has at most $k$ arguments.
--
--   A $\mathrm{PK}^k_d$-refutation of $\Phi$ is such a derivation ending in the empty cedent. For $k \ge 2$ the system $\mathrm{PK}^k_0$ is **$k$-DNF Resolution**, $\mathrm{Res}(k)$: its lines are disjunctions of $k$-terms, conjunctions of at most $k$ literals.
--
--   **Formalization Note** The rules are the base mission's `PKStep` and size is the base `derivSize`; only the shape of the lines is restricted. "Depth $d$" of a gate is read as its distance from the root of the formula, so in $\mathrm{PK}^k_0$ every top-level gate has fan-in at most $k$.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.2, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation

namespace RefWPHP

namespace Supplement

open PKFormula

/-- `FanInAt k e φ`: every gate (conjunction or disjunction) of `φ` at distance exactly `e` from the
root of `φ` has at most `k` arguments. Literals are not gates. -/
def FanInAt {V : Type} (k : ℕ) : ℕ → PKFormula V → Prop
  | _, .pos _ => True
  | _, .neg _ => True
  | 0, .and l => l.length ≤ k
  | 0, .or l => l.length ≤ k
  | e + 1, .and l => ∀ ψ ∈ l.attach, FanInAt k e ψ.1
  | e + 1, .or l => ∀ ψ ∈ l.attach, FanInAt k e ψ.1

/-- A `PK^k_d`-derivation from a set `Φ` of cedents, after N. Arteche, *Resolution Lower Bounds
versus the Weak Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…),
§2.1.2, p.15 (PDF 17): "the systems `PK^k_d` … in which the formulas have depth `d + 1`, but where
all gates at depth `d` have fan-in at most `k`". Every line follows from `Φ` and the earlier lines
by one step of the base calculus `PKStep`, every formula of every line has depth at most `d + 1`,
and every gate at distance `d` from the root of a formula has at most `k` arguments.

**Formalization Note.**
1. "Depth `d`" of a gate is read as its distance from the root: for `d = 0` this bounds the fan-in
   of the top gate, so a line of `PK^k_0` is a cedent of literals, `k`-terms (conjunctions of at most
   `k` literals) and disjunctions of at most `k` literals, which is a `k`-DNF; "For `k ≥ 2`, the
   system `PK^k_0` is denoted `Res(k)`" (p.15).
2. The inference rules are exactly the base mission's (`PKStep`), and size is the base `derivSize`;
   only the shape of the lines is restricted. -/
def IsPKkDerivation {V : Type} (k d : ℕ) (Φ : Set (Cedent V)) (ρ : List (Cedent V)) : Prop :=
  ∀ (i : ℕ) (h : i < ρ.length),
    PKStep Φ (ρ.take i) (ρ[i]'h) ∧ ∀ φ ∈ ρ[i]'h, depth φ ≤ d + 1 ∧ FanInAt k d φ

/-- A `PK^k_d`-refutation of `Φ`: a `PK^k_d`-derivation from `Φ` ending in the empty cedent.
`Res(k)`-refutations are `IsPKkRefutation k 0`. -/
def IsPKkRefutation {V : Type} (k d : ℕ) (Φ : Set (Cedent V)) (ρ : List (Cedent V)) : Prop :=
  IsPKkDerivation k d Φ ρ ∧ ρ.getLast? = some []

end Supplement

end RefWPHP


