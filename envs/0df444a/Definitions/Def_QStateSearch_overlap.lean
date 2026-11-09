-- Prove2me | Definitions.Def_QStateSearch_overlap
-- name    : QStateSearch_overlap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:18.971729+00:00
-- url     : https://prove2.me/theorems/5460cd88-decc-423c-9793-5696fee90494
-- title:
--   Overlap of the oracle-input register with $\psi$
-- statement:
--   For $\psi\in\mathbb C^D$ and a vector $\phi$ of $\{0,1\}\times[D]\times W$,
--   $$
--   \mathrm{ov}(\psi,\phi)=\sum_{c,w}\Big|\sum_i\overline{\psi_i}\,\phi(c,i,w)\Big|^2=\big\|(I\otimes\langle\psi|\otimes I)\phi\big\|^2=\langle\psi|\,\mathrm{Tr}_{\mathrm{rest}}|\phi\rangle\langle\phi|\,|\psi\rangle .
--   $$
--   For a branch vector $\phi_h$ of squared norm $w_h$ and reduced oracle-input state $\rho_h=\mathrm{Tr}_{\mathrm{rest}}|\phi_h\rangle\langle\phi_h|/w_h$, this is $w_h\langle\psi|\rho_h|\psi\rangle$, the conditional overlap of the paper weighted by the probability of the branch.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Lemma 3, p.11; proof of Theorem 4, p.13

import Mathlib
import Definitions.Def_QStateSearch_Reg

namespace QStateSearch

/-- The (unnormalized) overlap of the oracle-input register of `φ` with `ψ`:
`overlap ψ φ = ∑_{c,w} |∑_i conj(ψ_i) φ(c, i, w)|² = ‖(I ⊗ ⟨ψ| ⊗ I) φ‖² = ⟨ψ| Tr_rest(|φ⟩⟨φ|) |ψ⟩`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 3, p.11 (Lemma 3, "⟨Ψ|ρ_{t,T_t}|Ψ⟩") and Section 4, p.13 ("let u be the overlap of
its oracle-input register with |ψ⟩").

**Formalization Note.** For a branch vector `φ_h` of squared norm `w_h`, the reduced state of
the oracle-input register is `ρ_h = Tr_rest(|φ_h⟩⟨φ_h|)/w_h`, so `overlap ψ φ_h = w_h ⟨ψ|ρ_h|ψ⟩`:
the conditional overlap weighted by the probability of the branch. -/
noncomputable def overlap {D : ℕ} {W : Type} [Fintype W] [DecidableEq W] (ψ : EuclideanSpace ℂ (Fin D)) (φ : Reg D W → ℂ) : ℝ :=
  ∑ c : Fin 2, ∑ w : W, ‖∑ i : Fin D, star (ψ i) * φ (c, i, w)‖ ^ 2

end QStateSearch


