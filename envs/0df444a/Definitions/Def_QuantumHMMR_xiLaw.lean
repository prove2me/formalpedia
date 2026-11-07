-- Prove2me | Definitions.Def_QuantumHMMR_xiLaw
-- name    : QuantumHMMR_xiLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:11.983367+00:00
-- url     : https://prove2.me/theorems/fde75997-333b-4ca9-a1b4-2a0abb95bde8
-- title:
--   Insertion distribution $\xi_n$
-- statement:
--   The **insertion distribution** $\xi_n$ applies a uniformly random rotation $e^{i\varphi Z}$ to the first qubit: it is the law of
--   $$
--   e^{i\varphi Z} \otimes I_{2^{n-1}}, \qquad \varphi \sim \mathrm{Unif}[0, 2\pi).
--   $$
--   Inserted rarely into the local Clifford walk, these rotations remove the low-order moment obstructions of the Clifford group.
--
--   **Formalization Note** The first qubit is wire $0$ (published `firstWireLift`). The uniform law on $[0,2\pi)$ is Lebesgue measure conditioned on $[0, 2\pi)$; the verification file proves that $\xi_n$ is a probability measure. Footnote 4 (p.11) notes that a discretization of the angle reproduces the $t$-th moment; the ideal real angle is kept, as the theorem is stated for it.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 4, p.11 and footnote 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_rotZ

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory
open scoped ENNReal

namespace QuantumHMMR

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- The single-qubit insertion distribution `ξ_n` (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), §4, p.11): "apply a uniformly random
rotation `e^{iϕZ}` to the first qubit". It is the law of `firstWireLift n (rotZ φ)` for `φ`
uniform on `[0, 2π)`.

**Formalization Note** The first qubit is wire `0` (published `firstWireLift`). The uniform law
on `[0, 2π)` is Lebesgue measure conditioned on `[0, 2π)`. Footnote 4 (p.11) notes that a
discretization of the angle reproduces the `t`-th moment; the formalization keeps the ideal real
angle, as the theorem is stated for it. -/
noncomputable def xiLaw (n : ℕ) : Measure (QMat n) :=
  Measure.map (fun φ : ℝ => firstWireLift n (rotZ φ))
    (ProbabilityTheory.cond volume (Set.Ico 0 (2 * Real.pi)))

end QuantumHMMR


