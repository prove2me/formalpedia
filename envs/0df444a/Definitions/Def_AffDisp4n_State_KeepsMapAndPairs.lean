-- Prove2me | Definitions.Def_AffDisp4n_State_KeepsMapAndPairs
-- name    : AffDisp4n_State_KeepsMapAndPairs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:19.342192+00:00
-- url     : https://prove2.me/theorems/0657dcde-1ede-4488-ae55-d585c08008b9
-- title:
--   The same map $\Phi$ and the same pairs
-- statement:
--   A state $\sigma'$ **keeps the map and the pairs** of $\sigma$ if both have the same number of parameters, the same vector $b$ and matrix $L$, so the same $\Phi$, and the same set $P$ of pairs. It **keeps the pairs** if it has the same number of parameters and the same set of pairs.
--
--   This is what the deletions of §3.1 say about the parameters: "Each gate deletion removes a gate or an equation without changing the map $\Phi$" and "no parameters or pairs are changed".
--
--   **Formalization Note** The parameters of $\sigma'$ are compared with those of $\sigma$ through the cast along $m' = m$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §3.1, pp.19–20; §3.2, p.21

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_State

namespace AffDisp4n

/-- **`σ'` has the same parameters and the same pairs as `σ`** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.1, p.20:
"as no parameters or pairs are changed"; §3.2, p.21: "all pairs … are unchanged"). The two states have
the same number `m` of parameters, and a pair belongs to `P'` exactly when it belongs to `P`. -/
def State.KeepsPairs {n : ℕ} (σ' σ : State n) : Prop :=
  ∃ h : σ'.m = σ.m, ∀ p r : Fin σ'.m, s(p, r) ∈ σ'.P ↔ s(Fin.cast h p, Fin.cast h r) ∈ σ.P

/-- **`σ'` has the same map `Φ` and the same pairs as `σ`** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §3.1, p.19:
"Each gate deletion removes a gate or an equation without changing the map Φ"; p.20: "no parameters or
pairs are changed"). The two states have the same `m`, `b` and `L`, and a pair belongs to `P'` exactly when
it belongs to `P`.

**Formalization Note** `m` is a field of the state, so the parameters of `σ'` are compared with those of
`σ` through the cast along `σ'.m = σ.m`. -/
def State.KeepsMapAndPairs {n : ℕ} (σ' σ : State n) : Prop :=
  ∃ h : σ'.m = σ.m, σ'.b = σ.b ∧ (∀ i j, σ'.L i j = σ.L i (Fin.cast h j)) ∧
    ∀ p r : Fin σ'.m, s(p, r) ∈ σ'.P ↔ s(Fin.cast h p, Fin.cast h r) ∈ σ.P

end AffDisp4n


