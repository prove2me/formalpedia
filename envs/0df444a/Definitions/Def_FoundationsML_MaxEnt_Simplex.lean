-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_Simplex
-- name    : FoundationsML_MaxEnt_Simplex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:11:49.82707+00:00
-- url     : https://prove2.me/theorems/26599e93-38fb-487a-a92b-b267d64d879f
-- title:
--   The simplex of distributions over a finite set
-- statement:
--   **§12.4, p. 299, PDF p. 316.** $\Delta = \{p:X\to\mathbb R \mid \forall x, p(x)\ge0,
--   \sum_{x\in X}p(x)=1\}$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, §12.4, p. 299 (PDF p. 316)

import Mathlib

namespace FoundationsML.MaxEnt

/-- The simplex `Δ` of all probability distributions over a finite set `X` (Mohri, Rostamizadeh
& Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, §12.4, p. 299, PDF p.
316): `Δ = {p : X → ℝ | ∀x, p(x) ≥ 0, ∑_{x∈X} p(x) = 1}`. -/
def Simplex (X : Type*) [Fintype X] : Set (X → ℝ) :=
  {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1}

end FoundationsML.MaxEnt


