-- Prove2me | Definitions.Def_DetConnSketch_Main_Protocol
-- name    : DetConnSketch_Main_Protocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:41:21.256993+00:00
-- url     : https://prove2.me/theorems/56713cb3-f129-4db5-a288-81ec76c6bb6f
-- title:
--   Deterministic one-way protocols for connectivity and connected components under edge deletions
-- statement:
--   Alice holds a simple undirected graph $G_A$ on a vertex set $V$ and Bob holds a graph $G_B$ on the same vertex set, with the promise $G_B \le G_A$ (every edge of $G_B$ is an edge of $G_A$). Write $G_A - G_B$ (in Lean `GA \ GB`) for the graph on $V$ whose edges are the edges of $G_A$ not in $G_B$. Alice sends one message $M \in \{0,1\}^m$, computed from $G_A$ alone; Bob answers from $M$ and $G_B$ alone.
--
--   A **deterministic one-way connectivity protocol** with $m$-bit messages is a pair of maps
--   $$\mathrm{msg} : \{\text{graphs on } V\} \to \{0,1\}^m, \qquad \mathrm{dec} : \{0,1\}^m \times \{\text{graphs on } V\} \to \{\text{true},\text{false}\}$$
--   such that for **every** $G_A$ and **every** $G_B \le G_A$ (no bound on the number of deleted edges, zero error), $\mathrm{dec}(\mathrm{msg}(G_A), G_B) = \text{true}$ if and only if $G_A - G_B$ is connected.
--
--   A **deterministic one-way connected-components protocol** has the same shape, except that Bob outputs a binary relation on $V$, which must equal the reachability relation of $G_A - G_B$ (two vertices are related iff they lie in the same connected component; isolated vertices form their own components).
--
--   The least $m$ for which a protocol exists is the deterministic one-way communication complexity of the problem; Theorem 1.1 bounds it for connectivity on $n$ labeled vertices.
--
--   **Formalization Note.** `ConnProtocol V m` and `CompProtocol V m` are structures with fields `msg`, `dec` and the correctness property `correct`; messages are `Fin m → Bool`. No computability condition is imposed on `msg` or `dec`. Mathlib's `Connected` requires a nonempty vertex set. Messages have exactly $m$ bits (§2.1 says "$\le m$ bits"; padding makes the two equivalent up to one bit).
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 1 (PDF 5), §1.1; p. 13 (PDF 17), §2.1

import Mathlib

namespace DetConnSketch.Main

/-!
# Deterministic one-way protocols for connectivity and connected components under edge deletions

Khanna, Putterman, Sudan, *Deterministic Connectivity Sketches Under Edge Deletions*,
arXiv:2611.06626 (copy sha256 fff87f5b…), p. 1 (§1.1) and p. 13 (§2.1).

Alice holds a simple graph `GA` on the vertex type `V`, Bob a graph `GB` with `GB ≤ GA`
(`E_B ⊆ E_A`). Alice sends a message in `{0,1}^m` (`Fin m → Bool`) that depends on `GA` only;
Bob answers from the message and `GB` only. The answer must be correct, with zero error, for
**every** `GB ≤ GA` (no bound on the number of deleted edges). `GA − GB` is the graph
difference `GA \ GB` (same vertex set, edge set `E_A ∖ E_B`). No computability condition is
imposed on either party.
-/

/-- A deterministic one-way **connectivity** protocol on vertex type `V` with `m`-bit messages:
Bob outputs `true` exactly when `GA \ GB` is connected. -/
structure ConnProtocol (V : Type) (m : ℕ) where
  /-- Alice's message, a function of her graph only. -/
  msg : SimpleGraph V → (Fin m → Bool)
  /-- Bob's decision, a function of the message and his graph only. -/
  dec : (Fin m → Bool) → SimpleGraph V → Bool
  /-- Zero-error correctness for every valid deletion set `GB ≤ GA`. -/
  correct : ∀ GA GB : SimpleGraph V, GB ≤ GA →
    (dec (msg GA) GB = true ↔ (GA \ GB).Connected)

/-- A deterministic one-way **connected-components** protocol on vertex type `V` with `m`-bit
messages: Bob outputs the reachability relation of `GA \ GB` on all of `V` (isolated vertices
included), i.e. its partition into connected components. -/
structure CompProtocol (V : Type) (m : ℕ) where
  /-- Alice's message, a function of her graph only. -/
  msg : SimpleGraph V → (Fin m → Bool)
  /-- Bob's output, a binary relation on `V`, from the message and his graph only. -/
  dec : (Fin m → Bool) → SimpleGraph V → (V → V → Prop)
  /-- Zero-error correctness for every valid deletion set `GB ≤ GA`. -/
  correct : ∀ GA GB : SimpleGraph V, GB ≤ GA → dec (msg GA) GB = (GA \ GB).Reachable

end DetConnSketch.Main


