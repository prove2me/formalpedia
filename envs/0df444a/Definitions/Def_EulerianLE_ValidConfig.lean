-- Prove2me | Definitions.Def_EulerianLE_ValidConfig
-- name    : EulerianLE_ValidConfig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:00:18.27756+00:00
-- url     : https://prove2.me/theorems/187f986c-b495-40fc-966a-2da16285fa84
-- title:
--   Roles, valid round-$r$ configurations and successful configurations
-- statement:
--   In round $r\ge1$, node $u$ is **Counting** if $\mathrm{ID}_u\ge r$, **Check** if $\mathrm{ID}_u=r-1$ and **Relay** if $\mathrm{ID}_u<r-1$; Counting and Check nodes are **non-relay**. A configuration assigns to each node $u$ a pair $(\mathit{result}[u],\pi[u])$.
--
--   (Definition 4) A configuration in which every $\pi[u]$ is a port pairing of $u$ is a **valid round-$r$ configuration** if
--
--   1. every circuit of $\pi$ contains a node that is non-relay in round $r$, and
--   2. $\mathit{result}[u]=\emptyset$ for every node $u$.
--
--   A configuration is **successful with leader $v$** if $\mathit{result}[v]=$ Leader and $\mathit{result}[v']=$ Non-Leader for every $v'\neq v$.
--
--   Theorem 12 states that each round turns a valid configuration into a valid configuration of the next round or a successful one. The module also gives the variables of a node at a time of an execution of round $r$.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §5.1, p.24 (PDF p.26), roles and Definition 4

import Mathlib
import Definitions.Def_EulerianLE_program1

namespace EulerianLE

variable (G : Network)

/-- The role of node `u` in round `r ≥ 1` (§5.1, p.24): "node u is Counting if ID_u ≥ r, Check if
ID_u = r − 1, and Relay if ID_u < r − 1". -/
inductive Role : Type
  | counting
  | check
  | relay
  deriving DecidableEq, Repr

/-- The role of `u` in round `r`. -/
def role (ids : G.V → ℕ) (r : ℕ) (u : G.V) : Role :=
  if r ≤ ids u then .counting else if ids u + 1 = r then .check else .relay

/-- "A node with role Counting or Check is called a non-relay node" (p.24): `ID_u ≥ r − 1`. -/
def NonRelay (ids : G.V → ℕ) (r : ℕ) (u : G.V) : Prop := r ≤ ids u + 1

instance (ids : G.V → ℕ) (r : ℕ) (u : G.V) : Decidable (NonRelay G ids r u) := by
  unfold NonRelay; infer_instance

/-- The pairings `π` of a configuration `x`, one per node. -/
def pairsOf (x : ∀ u, CIO G u) : ∀ u, Pairs (G.deg u) := fun u => (x u).2

/-- Definition 4 (Valid round-r configuration), p.24, for `r ≥ 1`: every `π[u]` is a port pairing of
`u`, (1) every circuit of `π` contains a node that is non-relay in round `r`, and (2) `result[u] = ∅`
for every node `u`. -/
def ValidConfig (ids : G.V → ℕ) (r : ℕ) (x : ∀ u, CIO G u) : Prop :=
  (∀ u, IsPairing (x u).2) ∧
  (∀ p : G.Port, ∃ q : G.Port, SameCircuit (pairsOf G x) p q ∧ NonRelay G ids r q.1) ∧
  ∀ u, (x u).1 = .none

/-- Definition 4 (Successful configuration), p.24: "exactly one node v holds result[v] = Leader and
every other node v′ ≠ v holds result[v′] = Non-Leader; we call v its leader". -/
def SuccessfulWith (x : ∀ u, CIO G u) (ℓ : G.V) : Prop :=
  (x ℓ).1 = .leader ∧ ∀ v, v ≠ ℓ → (x v).1 = .nonLeader

variable {G}

/-- The variables of node `u` at time `t` of an execution of round `r`, if `u` is running its chunk. -/
def roundStoreAt {ids : G.V → ℕ} {r : ℕ} {x : ∀ u, CIO G u}
    {tag : Tag ((roundAlg G ids r).progs x)} (ρ : Run ((roundAlg G ids r).progs x) tag) (u : G.V)
    (t : ℕ) : Option (Store (G.deg u)) :=
  match (ρ.cfg t).status u with
  | .running st => some (st : RunState (G.deg u) (Store (G.deg u))).ctx.store
  | _ => none

end EulerianLE


