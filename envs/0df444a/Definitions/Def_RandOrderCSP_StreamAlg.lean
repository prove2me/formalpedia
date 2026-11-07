-- Prove2me | Definitions.Def_RandOrderCSP_StreamAlg
-- name    : RandOrderCSP_StreamAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:08:05.773997+00:00
-- url     : https://prove2.me/theorems/559c154c-a327-46e5-a545-ec0c01f37f30
-- title:
--   Deterministic and randomized $s$-space streaming algorithms
-- statement:
--   A **deterministic $s$-space streaming algorithm** over an update set $U$ is an update function $\{0,1\}^s\times U\to\{0,1\}^s$ with an output function on $\{0,1\}^s$. On a stream $u_1,\dots,u_m$ it starts at $0^s$, applies the update, and outputs the value at the final state. A **randomized** algorithm is a distribution over deterministic ones, with no charge for randomness or time.
--
--   The update set for instances on $[n]$ is the set of constraints: an injective scope $(i_1,\dots,i_k)$ with a predicate. The module also defines the instance attached to a list of constraints and the stream of that list in an order $\pi$.
--
--   **Formalization Note** The update sees neither a position counter nor the stream length, so no free memory enters. For a finite alphabet the deterministic algorithms form a finite set, so a distribution is a `PMF`.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.5, p.15; p.1

import Mathlib
import Definitions.Def_RandOrderCSP_CSP

namespace RandOrderCSP

/-- A constraint on the variable set `[n]` (p.1): a scope `e = (i₁, …, i_k)` of `k` distinct
variables together with a predicate `f : Σ^k → {0,1}`. This is also the stream update
`(M_H(j,1), …, M_H(j,k), f(j))` of §3.5 (p.15). -/
abbrev Constraint (k : ℕ) (Sig : Type) (n : ℕ) : Type :=
  (Fin k ↪ Fin n) × ((Fin k → Sig) → Bool)

/-- **Deterministic `s`-space streaming algorithm** (§3.5, p.15; p.1).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.5, p.15: "a (deterministic) s-space streaming
algorithm is determined by an update function, which has signature update : {0,1}^s × U → {0,1}^s,
as well as an output function output : {0,1}^s → Λ. Such a streaming algorithm induces a map
U^* → Λ by, given a “stream” u₁, …, u_m, initializing S ← 0^s, iteratively updating
S ← update(S, u_j) (for j = 1, …, m), and finally outputting output(S)."

**Formalization Note.** The state is `Fin s → Bool`; the update sees only the state and the current
update (no position counter, no stream length); the start state is `0^s` (`fun _ => false`). The
output set is `Λ = Bool` (`true` = YES). -/
structure DetAlg (U : Type) (s : ℕ) where
  /-- `update : {0,1}^s × U → {0,1}^s`. -/
  update : (Fin s → Bool) → U → (Fin s → Bool)
  /-- `output : {0,1}^s → Λ`. -/
  output : (Fin s → Bool) → Bool

namespace DetAlg

variable {U : Type} {s : ℕ}

/-- The final state after the stream `l`, starting from `0^s`. -/
def run (A : DetAlg U s) (l : List U) : Fin s → Bool :=
  l.foldl A.update (fun _ => false)

/-- The answer of the algorithm on the stream `l`. -/
def answer (A : DetAlg U s) (l : List U) : Bool :=
  A.output (A.run l)

end DetAlg

/-- A randomized `s`-space streaming algorithm: a distribution over deterministic ones (§3.5, p.15:
"randomized streaming algorithms, which may be viewed as distributions over deterministic streaming
algorithms"). For a finite update set the deterministic algorithms form a finite set, so every
distribution over them is a `PMF`. -/
abbrev RandAlg (U : Type) (s : ℕ) : Type := PMF (DetAlg U s)

/-- The CSP instance on `[n]` with constraints `Φ 0, …, Φ (m-1)` (the edge-index set is `Fin m`;
repeated constraints are distinguished by their index, as `ℰ_H` does on p.13). -/
def toCSP {k : ℕ} {Sig : Type} {n m : ℕ} (Φ : Fin m → Constraint k Sig n) :
    CSP k Sig (Fin n) (Fin m) where
  H := ⟨fun j => (Φ j).1, fun j => (Φ j).1.injective⟩
  f := fun j => (Φ j).2

/-- The stream of the instance `Φ` in the order `π` (§3.5): the `j`-th update is `Φ (π j)`. -/
def streamOf {α : Type} {m : ℕ} (Φ : Fin m → α) (π : Equiv.Perm (Fin m)) : List α :=
  List.ofFn (fun j => Φ (π j))

end RandOrderCSP


