-- Prove2me | Definitions.Def_WildeQIT_Gentle_IsPurification
-- name    : WildeQIT_Gentle_IsPurification
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:05.559729+00:00
-- url     : https://prove2.me/theorems/f7df7623-4c9e-4964-a802-189379e01fb4
-- title:
--   Purification $|\psi\rangle_{RA}$ of $\rho_A$
-- statement:
--   Let $A$ be a finite-dimensional system and $R$ a finite-dimensional reference system. A vector $|\psi\rangle_{RA}\in\mathcal H_R\otimes\mathcal H_A$ is a **purification** of an operator $\rho_A$ on $\mathcal H_A$ when tracing out the reference system from the rank-one operator $|\psi\rangle\langle\psi|_{RA}$ gives back $\rho_A$:
--
--   $$\operatorname{Tr}_R\{|\psi\rangle\langle\psi|_{RA}\}=\rho_A .$$
--
--   Purifications are the objects over which Uhlmann's theorem (Theorem 9.2.1) maximizes and with which the entanglement fidelity (Definition 9.5.1) is defined.
--
--   **Formalization Note** A vector on $R\otimes A$ is a function on the index type $r\times a$ (reference first); $\operatorname{Tr}_R$ is the published `WildeQIT.partialTraceLeft`. No normalization is imposed: when $\rho_A$ is a density operator, $\langle\psi|\psi\rangle=\operatorname{Tr}\rho_A=1$ follows.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §5.1 (Purification), p. 184; used in §9.2.3, p. 265 and Definition 9.5.1, p. 281

import Definitions.Def_WildeQIT_partialTrace
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §5.1 (Purification),
p. 184, used in §9.2.3 (Uhlmann fidelity, p. 265) and §9.5.2 (entanglement fidelity, p. 281).
-/

open Matrix

namespace WildeQIT.Gentle

/-- **Purification** (Wilde, arXiv:1106.1445v8, §5.1, p. 184). A vector `|ψ⟩_{RA}` on a
reference system `R` (basis indexed by `r`) and the system `A` (basis indexed by `a`) purifies
`ρ_A` when tracing out the reference system from `|ψ⟩⟨ψ|_{RA}` gives back `ρ_A`:
`Tr_R{|ψ⟩⟨ψ|_{RA}} = ρ_A`.

**Formalization Note.** A vector on `R ⊗ A` is a function `r × a → ℂ` (Mathlib's Kronecker
index convention, reference first); `|ψ⟩⟨ψ|` is `vecMulVec ψ (star ψ)`; `Tr_R` is the published
`WildeQIT.partialTraceLeft`, which traces out the left factor. No normalization is imposed: when
`ρ` is a density operator, `⟨ψ|ψ⟩ = Tr ρ = 1` follows. -/
def IsPurification {r a : Type} [Fintype r] (ψ : r × a → ℂ) (ρ : Matrix a a ℂ) : Prop :=
  partialTraceLeft (vecMulVec ψ (star ψ)) = ρ

end WildeQIT.Gentle


