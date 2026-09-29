-- Prove2me | Definitions.Def_FoundationsML_MaxEnt_PartitionFunction
-- name    : FoundationsML_MaxEnt_PartitionFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:12:07.213508+00:00
-- url     : https://prove2.me/theorems/9407c285-b14f-4b74-9aea-151635b7217f
-- title:
--   Partition function of a Gibbs distribution (Eq. 12.9)
-- statement:
--   **Eq. (12.9), p. 300, PDF p. 317.** $Z(w) = \sum_{x\in X}p_0(x)\exp(w\cdot\Phi(x))$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 300, Eq. (12.9) (PDF p. 317)

import Mathlib

namespace FoundationsML.MaxEnt

/-- The partition function `Z(w)` of a Gibbs distribution with prior `p0`, feature map `Φ`,
and parameter `w` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, Eq. (12.9), p. 300, PDF p. 317): `Z(w) = ∑_{x∈X} p0(x) exp(w·Φ(x))`. -/
noncomputable def PartitionFunction {X : Type*} [Fintype X] {N : ℕ}
    (p0 : X → ℝ) (Φ : X → Fin N → ℝ) (w : Fin N → ℝ) : ℝ :=
  ∑ x, p0 x * Real.exp (∑ j, w j * Φ x j)

end FoundationsML.MaxEnt


