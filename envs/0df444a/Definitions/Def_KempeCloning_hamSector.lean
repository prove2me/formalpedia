-- Prove2me | Definitions.Def_KempeCloning_hamSector
-- name    : KempeCloning_hamSector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:26:09.787999+00:00
-- url     : https://prove2.me/theorems/d9a7b157-b1f1-4def-be17-fa9f02736a0b
-- title:
--   Matrix of $\mathcal H$ in the sector basis (15)
-- statement:
--   For real $\gamma$ and $m, N\in\mathbb N$, $\mathrm{hamSector}(\gamma,m,N)$ is the square matrix indexed by the sector labels with entries
--
--   $$M_{pq} = \langle \mathrm{sectorIndex}(p)|\,\mathcal H\,|\mathrm{sectorIndex}(q)\rangle ,$$
--
--   the amplitude of the basis state $|\mathrm{sectorIndex}(p)\rangle$ in $\mathcal H|\mathrm{sectorIndex}(q)\rangle$, read off from the Hamiltonian (14) itself.
--
--   It is the compression of $\mathcal H$ to the span of the sector states (15). Since that span is invariant under $\mathcal H$, it is the restriction of $\mathcal H$ to a finite-dimensional invariant subspace containing the initial state.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, (14)–(15), p.4

import Definitions.Def_KempeCloning_ham
import Definitions.Def_KempeCloning_sectorIndex

namespace KempeCloning

/-- **The matrix of `H` (14) in the basis (15) of the sector.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, (14)–(15), p.4: "Action of (14) on
(13) generates Fock basis states of the general form (15)".

Entry `(p, q)` is the amplitude of the basis state `|sectorIndex p⟩` in `H |sectorIndex q⟩`, i.e.
the matrix element `⟨p| H |q⟩`, read off from `ham γ` itself.

**Formalization Note.** This is the compression of `H` to the span of the states (15). Because
that span is `H`-invariant (milestone `sector_invariant`), it is the restriction of `H`, and the
matrix exponential of `−iHt` below is the Schrödinger evolution of (14). No entry is computed by
hand. -/
noncomputable def hamSector (γ : ℝ) (m N : ℕ) : Matrix (Sector N) (Sector N) ℂ :=
  fun p q => ham γ (Finsupp.single (sectorIndex m N q) 1) (sectorIndex m N p)

end KempeCloning


