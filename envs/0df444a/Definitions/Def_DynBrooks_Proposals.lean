-- Prove2me | Definitions.Def_DynBrooks_Proposals
-- name    : DynBrooks_Proposals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:12.560441+00:00
-- url     : https://prove2.me/theorems/45d8b87b-3333-4331-98fb-21e0fb742c9e
-- title:
--   Lemma 4.7 setting — random color proposals and retained colors
-- statement:
--   Given a graph $Q$ on a finite vertex set, a probability $p$ and a palette $[\Delta]$: independently, each vertex becomes active with probability $p$ and proposes a uniformly random color from $[\Delta]$. An outcome records, for each vertex, either "inactive" or its proposed color, so an outcome has probability $\prod_v w_v$ with $w_v=1-p$ for an inactive vertex and $p/\Delta$ for an active vertex with a given color. An active vertex **retains** its color if no active neighbor proposes the same color.
--
--   **Formalization Note** Colors are $\{0,\dots,\Delta-1\}$ standing for $[\Delta]$; only the number of distinct colors matters.
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 4.7, p.23 (PDF 25)

import Mathlib

namespace DynBrooks

/-! # Random color proposals

Mishra, Mukherjee, *Fully Dynamic Brooks Coloring* (STOC 2027 submission, sha256 6542a9f1…), Lemma 4.7,
p.23 (PDF 25): "Independently, each vertex becomes active with probability p and proposes a uniformly
random color from [∆]. An active vertex retains its color if no active neighbor proposes the same
color."

**Formalization Note.** An outcome is `ω : V → Option (Fin Δ)`, with `none` for an inactive vertex.
The probability space is finite: an outcome has probability the product over `v` of `1 - p` if `ω v`
is `none`, and `p/Δ` otherwise. For `0 ≤ p ≤ 1` and `Δ ≥ 1` these sum to `1`. -/

/-- The probability of one outcome. -/
noncomputable def proposalWeight {V : Type} [Fintype V] (Δ : ℕ) (p : ℝ) (ω : V → Option (Fin Δ)) : ℝ :=
  ∏ v, (if ω v = none then 1 - p else p / Δ)

open Classical in
/-- The probability of an event of the proposal process. -/
noncomputable def proposalProb {V : Type} [Fintype V] (Δ : ℕ) (p : ℝ)
    (E : (V → Option (Fin Δ)) → Prop) : ℝ :=
  ∑ ω, if E ω then proposalWeight Δ p ω else 0

/-- Vertex `v` retains color `c`: it is active, proposes `c`, and no neighbor proposes `c`. -/
def Retains {V : Type} {Δ : ℕ} (Q : SimpleGraph V) (ω : V → Option (Fin Δ)) (v : V) (c : Fin Δ) :
    Prop :=
  ω v = some c ∧ ∀ u, Q.Adj v u → ω u ≠ some c

end DynBrooks


