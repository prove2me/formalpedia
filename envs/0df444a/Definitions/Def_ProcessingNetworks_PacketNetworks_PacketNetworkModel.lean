-- Prove2me | Definitions.Def_ProcessingNetworks_PacketNetworks_PacketNetworkModel
-- name    : ProcessingNetworks_PacketNetworks_PacketNetworkModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:44:58.106737+00:00
-- url     : https://prove2.me/theorems/704e71b7-cb43-4a60-b49a-d6d9bae768fd
-- title:
--   The packet network model, its input-output matrices, and Assumption 12.1 (Section 12.1, Definition 12.2)
-- statement:
--   **Section 12.1.** A packet network has `I` packet classes and `J` activities (service types).
--   Activity $j$'s **input class** $u(j)$ and **output class** $d(j)$ (or $d(j)=0$/`none` if
--   type-$j$ service removes the packet) determine the $I\times J$ **input-output matrix** $R$
--   ($R_{ij}=1$ if $i=u(j)$, $-1$ if $i=d(j)$, else $0$; `Rint` is the same matrix with integer
--   entries) and the material-requirements matrix $B$ (the $1$s of $R$ only). `nextState dat z e s`
--   is one timeslot of the packet count dynamics (12.7): counts $z$ at the start of a timeslot,
--   arrivals $e$ during it and schedule $s$ give $z + e - Rs$ at its end. A **cycle** is a sequence
--   of activities $j_1,\dots,j_n$ with $d(j_1)=u(j_2),\dots,d(j_{n-1})=u(j_n)$, $d(j_n)=u(j_1)$.
--
--   **Assumption 12.1.** (a) Each packet class is the input class for some activity; (b) no
--   cycles exist.
--
--   **Definition 12.2 (processing plan).** A processing plan for class $i$ is a sequence of
--   activities $j_1,\dots,j_n$ with $u(j_1)=i$, $d(j_k)=u(j_{k+1})$, and $d(j_n)=0$.
--
--   **Formalization note.** A length-$(n{+}1)$ chain (cycle or processing plan) is indexed by
--   `Fin (n+1) → Fin J`, with `Fin.castSucc`/`Fin.succ`/`Fin.last` giving the consecutive-index and
--   terminal-index maps.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 225-226, Section 12.1, Assumption 12.1, Definition 12.2

import Mathlib

namespace ProcessingNetworks.PacketNetworks

/-- The packet network model's data (Section 12.1): `I` packet classes, `J` activities
(service types). `u j` is the input class of activity `j` (`Rᵢⱼ = 1`); `d j` is its output
class, or `none` if type-`j` service removes the packet from the network (`Rᵢⱼ = -1` for
`d j = some i`, else the column has no `-1`). -/
structure PacketNetworkData (I J : ℕ) where
  u : Fin J → Fin I
  d : Fin J → Option (Fin I)

/-- The input-output matrix `R` (Section 12.1, consistent with the general SPN definition
(5.3)): column `j` has a single `1` in row `u j`, and a single `-1` in row `i` when
`d j = some i` (all zero if `d j = none`). -/
def R {I J : ℕ} (dat : PacketNetworkData I J) : Matrix (Fin I) (Fin J) ℝ :=
  fun i j => (if dat.u j = i then (1 : ℝ) else 0) + (if dat.d j = some i then (-1 : ℝ) else 0)

/-- The same input-output matrix `R` with integer entries, used for the integer-valued packet
count dynamics (12.6)–(12.7); `R dat = (Rint dat).map Int.cast`. -/
def Rint {I J : ℕ} (dat : PacketNetworkData I J) : Matrix (Fin I) (Fin J) ℤ :=
  fun i j => (if dat.u j = i then (1 : ℤ) else 0) + (if dat.d j = some i then (-1 : ℤ) else 0)

/-- One timeslot of the packet count dynamics (12.7): from class-level counts `z` at the start of
a timeslot, external arrivals `e` during it and schedule `s` employed in it, the counts at its
end are `z + e − R s`. -/
def nextState {I J : ℕ} (dat : PacketNetworkData I J) (z : Fin I → ℤ) (e : Fin I → ℕ)
    (s : Fin J → ℕ) : Fin I → ℤ :=
  fun i => z i + (e i : ℤ) - ∑ j, Rint dat i j * (s j : ℤ)

/-- The material-requirements matrix `B` (Section 12.2, "a precise analog" of Chapter 2's `B`):
`1` in the same components as `R`'s `u`-entries, `0` elsewhere. -/
def B {I J : ℕ} (dat : PacketNetworkData I J) : Matrix (Fin I) (Fin J) ℝ :=
  fun i j => if dat.u j = i then 1 else 0

/-- A cycle of length `n+1` (Section 12.1, just before Assumption 12.1): activities
`j 0, ..., j n` with `d (j k) = u (j (k+1))` for every `k`, indices taken cyclically in
`Fin (n+1)` (so `d (j n) = u (j 0)` closes the cycle). -/
def IsCycle {I J : ℕ} (dat : PacketNetworkData I J) {n : ℕ} (js : Fin (n + 1) → Fin J) : Prop :=
  ∀ k : Fin (n + 1), dat.d (js k) = some (dat.u (js (k + 1)))

/-- Assumption 12.1, Dai & Harrison p. 225 (PDF p. 241): (a) each packet class `i` is the input
class for some activity, and (b) no cycles exist (of any length `n+1 ≥ 1`). -/
def SatisfiesAssumption121 {I J : ℕ} (dat : PacketNetworkData I J) : Prop :=
  (∀ i : Fin I, ∃ j, dat.u j = i) ∧ ∀ (n : ℕ) (js : Fin (n + 1) → Fin J), ¬ IsCycle dat js

/-- Definition 12.2, Dai & Harrison p. 226 (PDF p. 242): a processing plan for packet class `i`
is a sequence of activities `j 0, ..., j n` (length `n+1`) with `u (j 0) = i`, `d (j k) = u
(j (k+1))` for `k < n`, and `d (j n) = none` (the plan ends by exiting the network). -/
def IsProcessingPlan {I J : ℕ} (dat : PacketNetworkData I J) (i : Fin I) {n : ℕ}
    (js : Fin (n + 1) → Fin J) : Prop :=
  dat.u (js 0) = i ∧
  (∀ k : Fin n, dat.d (js k.castSucc) = some (dat.u (js k.succ))) ∧
  dat.d (js (Fin.last n)) = none

end ProcessingNetworks.PacketNetworks


