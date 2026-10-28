-- Prove2me | Definitions.Def_WildeQIT_uhlmannFidelity
-- name    : WildeQIT_uhlmannFidelity
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T06:40:26.808645+00:00
-- url     : https://prove2.me/theorems/284c4b88-12d7-439d-9e62-44775029c137
-- title:
--   Uhlmann fidelity: $\max_U |\langle\phi^\rho| U_R \otimes I_A |\phi^\sigma\rangle|^2$ over canonical purifications
-- statement:
--   **Definition 9.2.3 (Uhlmann Fidelity).** The Uhlmann fidelity $F(\rho_A, \sigma_A)$ between two mixed states $\rho_A$ and $\sigma_A$ is the maximum overlap between their respective purifications, where the maximization is with respect to all unitaries $U$ acting on the purification system $R$:
--
--   $$
--   F(\rho_A, \sigma_A) = \max_{U} \left| \langle \phi^\rho |_{RA}\, U_R \otimes I_A\, | \phi^\sigma \rangle_{RA} \right|^2 .
--   $$
--
--   The purifications are the canonical ones of §5.1.1, $|\phi^\rho\rangle_{RA} = (I_R \otimes \sqrt{\rho_A})|\Gamma\rangle_{RA}$ with $|\Gamma\rangle = \sum_i |i\rangle_R |i\rangle_A$, so $\dim \mathcal{H}_R = \dim \mathcal{H}_A$.
--
--   **Formalization Note.** `WildeQIT.canonicalPurification ρ : n × n → ℂ` has component $(\sqrt{\rho})_{x r}$ at $(r, x)$ (reference index first). `WildeQIT.uhlmannFidelity ρ σ` is the real supremum `sSup` of the squared overlaps `‖star φ^ρ ⬝ᵥ ((U ⊗ₖ 1) *ᵥ φ^σ)‖ ^ 2` over `U ∈ Matrix.unitaryGroup n ℂ`; the set is nonempty and bounded (Theorem 9.2.1 shows the supremum is attained and equals $\|\sqrt\rho\sqrt\sigma\|_1^2$), so it is the book's maximum.
-- source:
--   Wilde, *Quantum Information Theory*, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), §9.2.3 "Uhlmann Fidelity", Definition 9.2.3 (Uhlmann Fidelity).

import Definitions.Def_WildeQIT_traceNorm
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §9.2.3, Definition 9.2.3 (Uhlmann Fidelity).

The Uhlmann fidelity `F(ρ_A, σ_A)` between two mixed states is the maximum overlap between their
respective purifications, the maximization being over all unitaries `U` on the purification
system `R`: `F(ρ_A, σ_A) = max_U |⟨φ^ρ|_{RA} (U_R ⊗ I_A) |φ^σ⟩_{RA}|²`.

The purifications used are the canonical ones of §5.1.1, `|φ^ρ⟩_{RA} = (I_R ⊗ √ρ_A)|Γ⟩_{RA}`
with `|Γ⟩ = ∑ᵢ |i⟩_R |i⟩_A`, so that `dim ℋ_R = dim ℋ_A`.
-/

open Matrix
open Kronecker
open scoped MatrixOrder

namespace WildeQIT

/-- The **canonical purification** `|φ^ρ⟩_{RA} = (I_R ⊗ √ρ_A)|Γ⟩_{RA}` of `ρ : Matrix n n ℂ`,
a vector on `R × A` with `R` a copy of the index type `n`: its `(r, x)` component is `(√ρ)ₓᵣ`. -/
noncomputable def canonicalPurification {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) : n × n → ℂ :=
  fun p => CFC.sqrt ρ p.2 p.1

/-- **Definition 9.2.3 (Uhlmann Fidelity).** The supremum over unitaries `U` on the reference
system of the squared overlap `|⟨φ^ρ| (U ⊗ I) |φ^σ⟩|²` of the canonical purifications; the
supremum is attained (Theorem 9.2.1), so this is the book's maximum. -/
noncomputable def uhlmannFidelity {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : ℝ :=
  sSup {x : ℝ | ∃ U ∈ Matrix.unitaryGroup n ℂ,
    x = ‖star (canonicalPurification ρ) ⬝ᵥ (((U : Matrix n n ℂ) ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ
      canonicalPurification σ)‖ ^ 2}

end WildeQIT


