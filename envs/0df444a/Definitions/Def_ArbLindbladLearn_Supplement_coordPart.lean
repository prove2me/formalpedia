-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_coordPart
-- name    : ArbLindbladLearn_Supplement_coordPart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:16:14.916111+00:00
-- url     : https://prove2.me/theorems/0bc9f633-2a23-48eb-b083-3e80ba7ae55d
-- title:
--   Support-$S$ part $\mathcal L_S$ of a Lindbladian
-- statement:
--   Every $n$-qubit Lindbladian decomposes as $\mathcal L=\sum_S\mathcal L_S$ over subsets $S$ of the qubits, where $\mathcal L_S$ collects the canonical Hamiltonian coordinates $h_a$ with support exactly $S$ ($\operatorname{supp}P_a=S$) and the dissipative coordinates $\gamma_{ab}$ with union support exactly $S$ ($\operatorname{supp}P_a\cup\operatorname{supp}P_b=S$).
--
--   This definition gives the coefficients of $\mathcal L_S$: those of $\mathcal L$ on the coordinates of support $S$, and $0$ elsewhere. The generator $\mathcal L_S$ is the published generator of these coefficients. It enters the local dynamical strength.
--
--   **Formalization Note** Each coordinate has exactly one (union) support, so the parts add up to the original coefficients.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), §1.1, p.2 (Strength parameter)

import Mathlib
import Definitions.Def_ArbLindbladLearn_Coeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- The support-`S` part of a Lindbladian (§1.1, p.2, "Strength parameter", Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…)):
"write `ℒ = Σ_S ℒ_S`, where `ℒ_S` collects the canonical Hamiltonian coordinates with support exactly
`S` and dissipative coordinates with union support exactly `S`". `coordPart c S` keeps `h_a` when
`supp P_a = S` and `γ_ab` when `supp P_a ∪ supp P_b = S`, and sets every other coefficient to `0`;
`ℒ_S` is `gen (coordPart c S)`.

**Formalization Note** `support` is the public support of a Pauli label. Since every coordinate has
exactly one (union) support, `Σ_S coordPart c S = c` coordinatewise, and `gen` is linear, so
`Σ_S ℒ_S = ℒ`. -/
def coordPart {n : ℕ} (c : Coeffs n) (S : Finset (Fin n)) : Coeffs n := by
  classical
  exact ⟨fun a => if support a = S then c.h a else 0,
    fun a b => if support a ∪ support b = S then c.γ a b else 0⟩

end ArbLindbladLearn.Supplement


