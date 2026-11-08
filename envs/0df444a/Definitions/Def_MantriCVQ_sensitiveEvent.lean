-- Prove2me | Definitions.Def_MantriCVQ_sensitiveEvent
-- name    : MantriCVQ_sensitiveEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:31.583915+00:00
-- url     : https://prove2.me/theorems/b92e08ff-d0bd-48bb-be51-fd5f1872d94c
-- title:
--   The sensitivity event (6.2)
-- statement:
--   For independent blocks with prescribed root values, $X$ is the generated input and $X^{(i)}$ is the input in which block $i$ alone is generated from the opposite root value, with the same seeds. The event (6.2) is
--   $$\Phi(X)=1\quad\text{and}\quad\Phi(X^{(i)})=0\text{ for all }i,$$
--   that $\Phi$ accepts $X$ and is sensitive at $X$ to the free leaf of every block.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Eq. (6.2), p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_MantriCVQ_Forest
import Definitions.Def_SamplingAC0_DNF

open QAlgorithms.Complexity SamplingAC0

namespace MantriCVQ

/-- The event (6.2) (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Eq. (6.2), p. 26 (PDF p.
28)): `Φ` accepts `X` and rejects every `X^{(i)}`, the input in which block `i` alone is generated from
the opposite root value, with the same seeds. -/
def sensitiveEvent (C : (m : ℕ) → Bits m → Bits m → Bool) {ι : Type} [DecidableEq ι] (ms : List ℕ)
    (Φ : DNF (ι × Addr ms)) (v : ι → Bool) (s : ι → Seed ms) : Prop :=
  DNF.eval Φ (forestInput C ms s v) = true ∧
    ∀ i : ι, DNF.eval Φ (forestInput C ms s (Function.update v i (!v i))) = false

end MantriCVQ


