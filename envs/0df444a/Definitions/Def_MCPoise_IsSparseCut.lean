-- Prove2me | Definitions.Def_MCPoise_IsSparseCut
-- name    : MCPoise_IsSparseCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:31.987561+00:00
-- url     : https://prove2.me/theorems/54ce8ced-05f3-4e5c-8433-00981eb75d8d
-- title:
--   The sparse cut of Lemma 2.4
-- statement:
--   Let $H = C \setminus U$, and for an endpoint $z$ and an integer $h \ge 0$ let
--   $$Z_h = \{ z_a \in Z_C : d_H(z, z_a) \le 2h \}, \qquad S_h = Z_h \cup N_H(Z_h).$$
--   A set $S$ is a **sparse cut** for the failed attempt when $S \subsetneq V(C)$, $0 < |S \cap Z_C| \le |Z_C|/2$, $w_C(S, V(C) \setminus S) \le (2/\rho) |S \cap Z_C|$, and $S = S_h$ for some $z \in \{z_i, z^*\}$ and $h \le \rho^2/4$.
--
--   **Formalization Note** The source's "breadth-first search algorithm" is stated by the shape of its output: a ball that a breadth-first search finds. The bound on $h$ is integer division.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.4, p.13; proof, p.14

import Mathlib
import Definitions.Def_MCPoise_RouteState

namespace MCPoise

variable {k : ℕ} {A : SimpleGraph (AVert k)}

/-- `Z_h := {z_a ∈ Z_C : d_H(z, z_a) ≤ 2h}` of the proof of Lemma 2.4, p.14, with reachability as its own clause. -/
def ballZ (C : A.Subgraph) (H : SimpleGraph (AVert k)) (z : Fin k) (h : ℕ) : Set (Fin k) :=
  {a | Sum.inl a ∈ C.verts ∧ H.Reachable (Sum.inl z) (Sum.inl a) ∧
    H.dist (Sum.inl z) (Sum.inl a) ≤ 2 * h}

/-- `S_h := Z_h ∪ N_H(Z_h)` of the proof of Lemma 2.4, p.14. -/
def ballS (C : A.Subgraph) (H : SimpleGraph (AVert k)) (z : Fin k) (h : ℕ) : Set (AVert k) :=
  {v | (∃ a ∈ ballZ C H z h, v = Sum.inl a) ∨ ∃ a ∈ ballZ C H z h, H.Adj (Sum.inl a) v}

/-- `w_C(S, V(C) ∖ S)`: the total weight of the edges of `C` with exactly one endpoint in `S` (p.13). -/
noncomputable def wCut (C : A.Subgraph) (S : Set (AVert k)) : ℝ :=
  open scoped Classical in
  ∑ a : Fin k, ∑ c : Copy k,
    if C.Adj (Sum.inl a) (Sum.inr c) ∧ (Sum.inl a ∈ S ↔ Sum.inr c ∉ S) then wt c else 0

/-- `S ∩ Z_C`. -/
noncomputable def pairsIn (C : A.Subgraph) (S : Set (AVert k)) : Finset (Fin k) :=
  open scoped Classical in (pairsOf C).filter fun a => Sum.inl a ∈ S

/-- **The sparse cut of Lemma 2.4.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.4, p.13: "a set S ⊊ V(C) such that 0 < |S ∩ Z_C| ≤ |Z_C|/2 and w_C(S, V(C) ∖ S) ≤ (2/ρ)|S ∩ Z_C|";
proof, p.14: `S = S_h` around an endpoint `z ∈ {z_i, z*_C}`, for an integer `0 ≤ h ≤ ρ²/4`, in `H = C ∖ U`.

**Formalization Note.** "There exists a breadth-first search algorithm that finds a set" is stated by the shape of the
output: `S` is a ball `S_h` of `H`, which a breadth-first search finds. `h ≤ ρ²/4` is `ℕ` division (the floor). The running
time is carried by the goal theorem; no separate machine is stated for this search. -/
def IsSparseCut (ρ : ℕ) (C : A.Subgraph) (i z : Fin k) (U S : Set (AVert k)) : Prop :=
  S ⊂ C.verts ∧
  0 < (pairsIn C S).card ∧
  2 * (pairsIn C S).card ≤ (pairsOf C).card ∧
  wCut C S ≤ 2 / (ρ : ℝ) * ((pairsIn C S).card : ℝ) ∧
  ∃ z₀, (z₀ = i ∨ z₀ = z) ∧ ∃ h, h ≤ ρ ^ 2 / 4 ∧ S = ballS C (avoid C U) z₀ h

end MCPoise


