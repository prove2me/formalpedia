-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_heavySupportD
-- name    : ArbLindbladLearn_Supplement_heavySupportD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:13:17.6954+00:00
-- url     : https://prove2.me/theorems/d2796520-b8d0-4d41-b922-536c13436006
-- title:
--   $\eta$-heavy dissipative support $\mathcal S_D^{\ge\eta}$
-- statement:
--   Let $\mathcal L$ be an $n$-qubit Lindbladian with dissipative coefficients $\{\gamma_{ab}\}$ (Definition 2.6). For a threshold $\eta$, the **$\eta$-heavy dissipative support** is the set of ordered pairs of nonidentity labels whose dissipative coefficient has modulus at least $\eta$:
--   $$\mathcal S_D^{\ge\eta}=\{(a,b):\ a,b\ne0,\ |\gamma_{ab}|\ge\eta\}.$$
--
--   Theorem 3.8 asks the support-learning stage to output a candidate set of pairs containing it.
--
--   **Formalization Note** A finite set of ordered pairs of public labels; $|\gamma_{ab}|$ is the complex modulus.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Definition 2.7, p.14

import Mathlib
import Definitions.Def_ArbLindbladLearn_Coeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- The `η`-heavy dissipative support (Definition 2.7, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.14):
`𝒮_D^{≥η} = {(a, b) : a, b ≠ 0, |γ_ab| ≥ η}`, the ordered pairs of nonidentity labels whose
dissipative coefficient has modulus at least `η`.

**Formalization Note** A `Finset` of ordered pairs of public labels `Pauli n`; `|γ_ab|` is the
complex modulus `‖c.γ a b‖`. -/
def heavySupportD {n : ℕ} (c : Coeffs n) (η : ℝ) : Finset (Pauli n × Pauli n) := by
  classical
  exact Finset.univ.filter (fun p : Pauli n × Pauli n =>
    p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ η ≤ ‖c.γ p.1 p.2‖)

end ArbLindbladLearn.Supplement


