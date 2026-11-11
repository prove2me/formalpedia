-- Prove2me | Definitions.Def_LindbladShallow_activity
-- name    : LindbladShallow_activity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:21.653817+00:00
-- url     : https://prove2.me/theorems/93ad3f77-4643-4748-a741-501e4c35a355
-- title:
--   Overlap graph, connected sets, $d_w$, $W_S$, $\zeta$ and crossing activity
-- statement:
--   For labels $b$ with finite supports $X_b$ the **overlap graph** joins distinct $b,c$ when $X_b\cap X_c\neq\emptyset$. A **connected set** is a nonempty set of labels inducing a connected subgraph. For a finite label set $B$, weights $\omega$, source $S$ and cut $C$:
--   $$d_w=\sup_{b\in B}\sum_{c\in B:\,X_c\cap X_b\ne\emptyset}\omega_c,\qquad W_S=\sum_{b\in S}\omega_b,\qquad \zeta=\frac{W_S(6d_w)^{m_*-1}}{1-6d_w},$$
--   and the **crossing activity** is $\sum_F\prod_{b\in F}\omega_b$ over connected $F\subseteq B$ meeting $S$ and $C$.
--
--   These are the quantities of Lemma 3.3 and Theorem 3.4.
--
--   **Formalization Note** $d_w$ is a real supremum over the finite set $B$: the maximum when $B\ne\emptyset$, and $0$ for $B=\emptyset$.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §3.1, p.14; p.16; Lemma 3.3, p.16

import Mathlib

namespace LindbladShallow

/-- The overlap graph of a family of supports `X : β → Finset α`: distinct labels `b, c` are
adjacent when their supports overlap, irrespective of chronological position (arXiv:2610.05362,
held version sha256 8f4637ef…, §3.1, p.14). -/
def overlapGraph {α β : Type*} [DecidableEq α] (X : β → Finset α) : SimpleGraph β :=
  SimpleGraph.fromRel fun b c => (X b ∩ X c).Nonempty

/-- `F` is a connected set: a nonempty set of labels inducing a connected subgraph of the overlap
graph. -/
def IsConnSet {α β : Type*} [DecidableEq α] (X : β → Finset α) (F : Finset β) : Prop :=
  ((overlapGraph X).induce (F : Set β)).Connected

/-- `d_w := sup_{b ∈ B} Σ_{c ∈ B : X_c ∩ X_b ≠ ∅} ω_c` (arXiv:2610.05362, p.16). The sum includes
`c = b`.

**Formalization Note** A real `⨆` over the finite subtype of `B`: it is the maximum when `B` is
nonempty and `0` for `B = ∅` (where every sum of the lemma vanishes). -/
noncomputable def dwt {α β : Type*} [DecidableEq α] (B : Finset β) (X : β → Finset α)
    (ω : β → ℝ) : ℝ :=
  ⨆ b : B, ∑ c ∈ B.filter (fun c => (X c ∩ X b).Nonempty), ω c

/-- `W_S := Σ_{b ∈ S} ω_b` (p.16). -/
def WSum {β : Type*} (S : Finset β) (ω : β → ℝ) : ℝ := ∑ b ∈ S, ω b

/-- `ζ := W_S (6d_w)^{m∗−1} / (1 − 6d_w)` (Lemma 3.3, p.16). -/
noncomputable def zeta {α β : Type*} [DecidableEq α] (B S : Finset β) (X : β → Finset α)
    (ω : β → ℝ) (mstar : ℕ) : ℝ :=
  WSum S ω * (6 * dwt B X ω) ^ (mstar - 1) / (1 - 6 * dwt B X ω)

/-- The total activity `Σ_F ∏_{b ∈ F} ω_b` of all connected crossing sets `F ⊆ B` (sets meeting both
the source `S` and the cut `C`) (p.16). -/
noncomputable def crossActivity {α β : Type*} [DecidableEq α] [DecidableEq β] (B S C : Finset β)
    (X : β → Finset α) (ω : β → ℝ) : ℝ :=
  open Classical in
  ∑ F ∈ B.powerset.filter (fun F => IsConnSet X F ∧ (F ∩ S).Nonempty ∧ (F ∩ C).Nonempty),
    ∏ b ∈ F, ω b

end LindbladShallow


