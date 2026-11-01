-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_groundSpace
-- name    : BaconThesis_Supercoherence_groundSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:46.750912+00:00
-- url     : https://prove2.me/theorems/7e0a622f-166a-4639-a353-d24635bb9687
-- title:
--   The eigenspace of a matrix $H$ at energy $E$ (the ground space when $E$ is the lowest eigenvalue)
-- statement:
--   For a square complex matrix $H$ on $\mathbb C^\iota$ and a real number $E$, the eigenspace
--
--   $$\mathcal G(H,E) = \{ v \in \mathbb C^\iota : H v = E v \} = \ker (H - E\,I).$$
--
--   When $E$ is the lowest eigenvalue of $H$ this is the space spanned by the ground states of $H$, the book's "degenerate ground state" when its dimension is at least $2$. If $E$ is not an eigenvalue, $\mathcal G(H,E) = \{0\}$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186), and Definition 15.2.1, pp.170–171 (PDF pp.187–188)

import Mathlib

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186) and Definition 15.2.1, pp.170–171 (PDF pp.187–188): the
eigenspace `{v | H v = E v}` of a matrix `H` at the real energy `E`. When `E` is the lowest
eigenvalue of `H` (`IsGroundEnergy H E`) this is the book's (degenerate) ground state, the space
spanned by all ground states.

**Formalization Note.** Defined as the kernel of `H - E • 1` acting on column vectors
`ι → ℂ` (`Matrix.toLin'`); it is `⊥` when `E` is not an eigenvalue. -/
def groundSpace {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (E : ℝ) :
    Submodule ℂ (ι → ℂ) :=
  LinearMap.ker (Matrix.toLin' (H - (E : ℂ) • (1 : Matrix ι ι ℂ)))

end BaconThesis.Supercoherence


