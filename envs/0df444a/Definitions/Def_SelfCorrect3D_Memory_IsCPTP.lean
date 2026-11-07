-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_IsCPTP
-- name    : SelfCorrect3D_Memory_IsCPTP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:48.819356+00:00
-- url     : https://prove2.me/theorems/1cf9f6de-fdae-4707-9230-3c3d57e00150
-- title:
--   Completely positive trace-preserving map
-- statement:
--   A map $\Phi$ from $\alpha\times\alpha$ complex matrices to $\beta\times\beta$ complex matrices is **CPTP** if it is linear, trace preserving ($\mathrm{Tr}\,\Phi(X)=\mathrm{Tr}\,X$ for all $X$), and completely positive: for every $m$ and every positive semidefinite matrix $R$ on $\alpha\times\{1,\dots,m\}$, the matrix $(\Phi\otimes\mathrm{id}_m)(R)$, obtained by applying $\Phi$ to each $\alpha\times\alpha$ block of $R$, is positive semidefinite.
--
--   Theorem 2.6 asserts a CPTP logical encoding map $\mathrm{Enc}:L(\mathbb C^2)\to L(\mathcal H_S)$.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, Theorem 2.6, p. 21

import Mathlib
open scoped ComplexOrder

namespace SelfCorrect3D.Memory

/-- **Completely positive trace-preserving (CPTP) map** between matrix algebras. Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
Theorem 2.6, p. 21 ("a CPTP logical encoding map Enc : L(ℂ²) → L(𝓗_S)").

`Φ` is linear, trace preserving (`Tr Φ(X) = Tr X` for all `X`), and completely positive: for every
`m` and every positive semidefinite `R` on `α × Fin m`, `(Φ ⊗ id_m)(R)` is positive semidefinite,
where `(Φ ⊗ id_m)(R)` applies `Φ` to each `α × α` block `R_{ij}`. -/
def IsCPTP {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (Φ : Matrix α α ℂ → Matrix β β ℂ) : Prop :=
  IsLinearMap ℂ Φ ∧ (∀ X, (Φ X).trace = X.trace) ∧
    ∀ (m : ℕ) (R : Matrix (α × Fin m) (α × Fin m) ℂ), R.PosSemidef →
      (Matrix.of fun p q : β × Fin m =>
        Φ (Matrix.of fun a b => R (a, p.2) (b, q.2)) p.1 q.1).PosSemidef

end SelfCorrect3D.Memory


