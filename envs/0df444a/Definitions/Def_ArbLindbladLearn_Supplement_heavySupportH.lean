-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_heavySupportH
-- name    : ArbLindbladLearn_Supplement_heavySupportH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:12:39.631329+00:00
-- url     : https://prove2.me/theorems/1a2f38df-6b56-43fe-891d-efbbcd72ae65
-- title:
--   $\eta$-heavy Hamiltonian support $\mathcal S_H^{\ge\eta}$
-- statement:
--   Let $\mathcal L$ be an $n$-qubit Lindbladian with Hamiltonian coefficients $\{h_a\}$ (Definition 2.6). For a threshold $\eta$, the **$\eta$-heavy Hamiltonian support** is the set of nonidentity Pauli labels whose Hamiltonian coefficient has magnitude at least $\eta$:
--   $$\mathcal S_H^{\ge\eta}=\{a\ne0:\ |h_a|\ge\eta\}.$$
--
--   Theorem 3.8 asks the support-learning stage to output a candidate set containing it.
--
--   **Formalization Note** A finite set of the public labels $\mathrm{Pauli}\,n=\mathrm{Fin}\,n\to\mathrm{Fin}\,4$, over the published coefficients `Coeffs`. The paper uses $\eta>0$; the definition puts no condition on $\eta$.
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

/-- The `η`-heavy Hamiltonian support (Definition 2.7, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.14):
`𝒮_H^{≥η} = {a ≠ 0 : |h_a| ≥ η}`, the nonidentity labels whose Hamiltonian coefficient has magnitude
at least `η`.

**Formalization Note** A `Finset` of the public labels `Pauli n = Fin n → Fin 4` over the
published coefficients `Coeffs`. The paper uses it for `η > 0` (Definition 2.7; Theorem 3.8 takes
`η ∈ (0, Λ]`); the definition itself puts no condition on `η`. -/
def heavySupportH {n : ℕ} (c : Coeffs n) (η : ℝ) : Finset (Pauli n) := by
  classical
  exact Finset.univ.filter (fun a : Pauli n => a ≠ 0 ∧ η ≤ |c.h a|)

end ArbLindbladLearn.Supplement


