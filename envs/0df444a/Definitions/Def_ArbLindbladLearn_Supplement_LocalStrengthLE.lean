-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_LocalStrengthLE
-- name    : ArbLindbladLearn_Supplement_LocalStrengthLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:17:45.271616+00:00
-- url     : https://prove2.me/theorems/53d9493f-4279-4081-ac91-7435c067702c
-- title:
--   Local dynamical strength bound $\max_i\sum_{S\ni i}\|\mathcal L_S^\dagger\|_{\infty\to\infty}\le\Lambda_{\mathrm{loc}}$
-- statement:
--   Write $\mathcal L=\sum_S\mathcal L_S$, where $\mathcal L_S$ collects the canonical Hamiltonian coordinates with support exactly $S$ and the dissipative coordinates with union support exactly $S$. A **local dynamical strength bound** $\Lambda_{\mathrm{loc}}$ satisfies
--   $$\max_i\sum_{S\ni i}\|\mathcal L_S^\dagger\|_{\infty\to\infty}\le\Lambda_{\mathrm{loc}},$$
--   the maximum taken over the qubits $i$ and the sum over the subsets $S$ containing $i$.
--
--   This is the strength promise of Theorems 5.7 and 5.8.
--
--   **Formalization Note** $\mathcal L_S^\dagger$ is the Hilbert–Schmidt adjoint (the conjugate transpose of the superoperator matrix), as in the published global bound `StrengthLE`; the norm is the induced spectral norm. The maximum is a bound for every qubit.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), §1.1, p.2 (Strength parameter)

import Mathlib
import Definitions.Def_ArbLindbladLearn_gen
import Definitions.Def_ArbLindbladLearn_Supplement_coordPart
import Definitions.Def_ArbLindbladLearn_Supplement_indNorm

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- The local dynamical-strength bound (§1.1, p.2, "Strength parameter", Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…)):
"A supplied local dynamical strength bound satisfies `max_i Σ_{S∋i} ‖ℒ_S†‖_{∞→∞} ≤ Λ_loc`", where
`ℒ = Σ_S ℒ_S` and `ℒ_S` collects the Hamiltonian coordinates with support exactly `S` and the
dissipative coordinates with union support exactly `S`.

**Formalization Note** `ℒ_S = gen (coordPart c S)`; its Hilbert–Schmidt adjoint `ℒ_S†` is the
conjugate transpose of the superoperator matrix, as in the published `StrengthLE`; the induced norm
is `indNorm` (spectral norm on both sides). The maximum over qubits `i` is stated as a bound for
every `i : Fin n`. -/
def LocalStrengthLE {n : ℕ} (c : Coeffs n) (Λloc : ℝ) : Prop :=
  ∀ i : Fin n,
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
      indNorm (gen (coordPart c S))ᴴ ≤ Λloc

end ArbLindbladLearn.Supplement


