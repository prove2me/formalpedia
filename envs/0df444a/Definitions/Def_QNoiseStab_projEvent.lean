-- Prove2me | Definitions.Def_QNoiseStab_projEvent
-- name    : QNoiseStab_projEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:45.589224+00:00
-- url     : https://prove2.me/theorems/ffabe7b2-0a77-4ad6-8ef3-f8f0e20a49df
-- title:
--   Projection $\Pi_E$ onto the input states of an event $E$
-- statement:
--   For an event $E\subseteq\mathbb Z_m^{\,n}$, the projection onto the input states that correspond to $E$ is the diagonal operator
--
--   $$
--   \Pi_E=\sum_{x\in E}|x\rangle\langle x|
--   $$
--
--   in the standard basis of $\mathbb C^{\mathbb Z_m^n}$.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 3.4, p.12 (Π_E)

import Mathlib

namespace QNoiseStab

/-- The projection `Π_E` onto the input states that correspond to an event `E ⊆ Z_mⁿ`
(Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space
Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 3.4,
p.12: "If ΠE is the projection onto the input states that correspond to event E"): the diagonal
matrix `Σ_{x ∈ E} |x⟩⟨x|` in the standard basis. -/
noncomputable def projEvent {n m : ℕ} (E : Finset (Fin n → ZMod m)) :
    Matrix (Fin n → ZMod m) (Fin n → ZMod m) ℂ :=
  Matrix.diagonal fun x => if x ∈ E then 1 else 0

end QNoiseStab


