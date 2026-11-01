-- Prove2me | Definitions.Def_WildeQIT_Schumacher_purifiedSourceState
-- name    : WildeQIT_Schumacher_purifiedSourceState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:55.470145+00:00
-- url     : https://prove2.me/theorems/d4fdd0ee-1598-49f6-8909-5744db672464
-- title:
--   Purified i.i.d. source state $(\phi^\rho_{RA})^{\otimes n}$
-- statement:
--   Let $\rho$ be a density operator on $\mathcal H_A = \mathbb C^a$. Its canonical purification is the vector
--
--   $$
--   |\phi^\rho\rangle_{RA} = \sum_r |r\rangle_R \otimes \sqrt\rho\,|r\rangle_A ,
--   $$
--
--   with reference system $R$ a copy of $A$; it satisfies $\mathrm{Tr}_R\,|\phi^\rho\rangle\langle\phi^\rho| = \rho$. The purified i.i.d. source state is the rank-one operator $(\phi^\rho_{RA})^{\otimes n} = (|\phi^\rho\rangle\langle\phi^\rho|_{RA})^{\otimes n}$ on $\mathcal H_{R^n}\otimes\mathcal H_{A^n}$; its vector has coordinates $\Phi(r^n, x^n) = \prod_i (\sqrt\rho)_{x_i,r_i}$.
--
--   It is the state on which the error of a quantum compression protocol is measured (eq. (18.5)).
--
--   **Formalization Note** The systems are grouped $R^nA^n$ (index type `(Fin n → a) × (Fin n → a)`, reference first) rather than $(RA)^n$, a reordering of tensor factors. The book purifies with an ensemble $\{p_X(x),|\psi_x\rangle\}$ of $\rho$ (eq. (18.3)); any two purifications of $\rho^{\otimes n}$ are related by an isometry on the reference system, which commutes with channels on $A^n$ and preserves the trace norm, so the error criterion does not depend on the purification chosen.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §18.1, eqs. (18.3) and (18.5), p. 523

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §18.1, eq. (18.3), p. 523:
the quantum information source with density operator `ρ` is purified to `|ϕ^ρ⟩_{RA}`, with `R` an
inaccessible reference system, and the i.i.d. state produced is `(|ϕ^ρ⟩_{RA})^{⊗n}`.
-/

open Matrix
open scoped MatrixOrder

namespace WildeQIT.Schumacher

/-- **The purified i.i.d. source state** `(ϕ^ρ_{RA})^{⊗n}` (Wilde, arXiv:1106.1445v8, §18.1,
eq. (18.3), p. 523, and eq. (18.5)). The purification is the canonical one,
`|ϕ^ρ⟩_{RA} = ∑_r |r⟩_R ⊗ √ρ |r⟩_A`, with reference system `R` a copy of `A`; its coordinates are
`ϕ(r, x) = (√ρ)_{x,r}`, and `Tr_R |ϕ^ρ⟩⟨ϕ^ρ| = √ρ √ρ† = ρ` for a density operator `ρ`. The
`n`-fold state is the rank-one operator `|Φ⟩⟨Φ|` on `ℋ_{Rⁿ} ⊗ ℋ_{Aⁿ}` with
`Φ(rⁿ, xⁿ) = ∏ᵢ ϕ(rᵢ, xᵢ)`.

**Formalization Note.** The systems are grouped as `Rⁿ Aⁿ` (index type
`(Fin n → a) × (Fin n → a)`, reference first) rather than `(RA)ⁿ`; this is the same state up to
the reordering of tensor factors. The book's (18.3) uses the purification built from an ensemble
`{p_X(x), |ψ_x⟩}` of `ρ`; any two purifications are related by a (partial) isometry on the
reference system (Theorem 5.1.1), which leaves the error criterion (18.5) unchanged since the
channels act on `Aⁿ` only, so fixing the canonical purification changes no instance. `√ρ` is
`CFC.sqrt`, as in the published `WildeQIT.traceNorm`. -/
noncomputable def purifiedSourceState {a : Type} [Fintype a] [DecidableEq a]
    (ρ : Matrix a a ℂ) (n : ℕ) :
    Matrix ((Fin n → a) × (Fin n → a)) ((Fin n → a) × (Fin n → a)) ℂ :=
  Matrix.vecMulVec (fun rx : (Fin n → a) × (Fin n → a) => ∏ i, CFC.sqrt ρ (rx.2 i) (rx.1 i))
    (star fun rx : (Fin n → a) × (Fin n → a) => ∏ i, CFC.sqrt ρ (rx.2 i) (rx.1 i))

end WildeQIT.Schumacher


