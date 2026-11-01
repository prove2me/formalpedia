-- Prove2me | Definitions.Def_WildeQIT_Purification_IsPurification
-- name    : WildeQIT_Purification_IsPurification
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:19:54.762133+00:00
-- url     : https://prove2.me/theorems/5a0b1f7d-e04e-4cc3-90e8-b3fe79b06e01
-- title:
--   Purification $|\psi\rangle_{RA}$ of a density operator $\rho_A$ (Definition 5.1.1)
-- statement:
--   Let $\mathcal H_R$ and $\mathcal H_A$ be finite-dimensional Hilbert spaces (a **reference** system $R$ and the original system $A$), and let $\rho_A$ be an operator on $\mathcal H_A$. A vector $|\psi\rangle_{RA}\in\mathcal H_R\otimes\mathcal H_A$ is a **purification** of $\rho_A$ when
--
--   1. $|\psi\rangle_{RA}$ is a pure state, i.e. a unit vector: $\||\psi\rangle_{RA}\|_2 = 1$;
--   2. its reduced state on $A$ is $\rho_A$:
--
--   $$
--   \rho_A = \operatorname{Tr}_R\{|\psi\rangle\langle\psi|_{RA}\}.
--   $$
--
--   A purification presents the noise in a mixed state $\rho_A$ as entanglement with an inaccessible reference system. The definition is the setting of the purification theorems of Chapter 5.
--
--   **Formalization Note** The vector is a function on the product basis $R\times A$, with the reference as the **left** factor; $|\psi\rangle\langle\psi|$ is the matrix with entries $\psi(i)\overline{\psi(j)}$, and $\operatorname{Tr}_R$ is `WildeQIT.partialTraceLeft`. The book's requirement $\rho_A\in\mathcal D(\mathcal H_A)$ is not a separate clause: the two conditions force $\rho_A$ to be positive semidefinite with unit trace.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 5.1.1, eq. (5.1), p. 184

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

namespace WildeQIT.Purification

/-- **Purification.** Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Definition 5.1.1, p. 184: "A purification of a density operator ρ_A ∈ D(H_A) is a pure
bipartite state |ψ⟩_{RA} ∈ H_R ⊗ H_A on a reference system R and the original system A, with
the property that the reduced state on system A is equal to ρ_A: ρ_A = Tr_R{|ψ⟩⟨ψ|_{RA}}." (5.1)

The vector `ψ : r × a → ℂ` is `|ψ⟩_{RA}` in the product basis of `H_R ⊗ H_A`, the reference
`R` being the **left** factor. `IsPurification ρ ψ` holds when `ψ` is a unit vector
(a pure state) and `Tr_R{|ψ⟩⟨ψ|} = ρ`, where `|ψ⟩⟨ψ| = vecMulVec ψ (star ψ)` has entries
`ψ(i) · conj ψ(j)` and `Tr_R` is `WildeQIT.partialTraceLeft` (the trace over the left factor).

**Formalization Note.** The book's `ρ_A ∈ D(H_A)` is not a separate clause: a unit vector `ψ`
with `Tr_R |ψ⟩⟨ψ| = ρ` forces `ρ` to be positive semidefinite with unit trace. Hilbert spaces are
finite-dimensional, with orthonormal bases indexed by finite types (`r` for `R`, `a` for `A`). -/
def IsPurification {a r : Type} [Fintype a] [Fintype r] (ρ : Matrix a a ℂ) (ψ : r × a → ℂ) :
    Prop :=
  (∑ i, Complex.normSq (ψ i) = 1) ∧
    WildeQIT.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)) = ρ

end WildeQIT.Purification


