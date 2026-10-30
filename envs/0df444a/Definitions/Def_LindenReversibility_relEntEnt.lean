-- Prove2me | Definitions.Def_LindenReversibility_relEntEnt
-- name    : LindenReversibility_relEntEnt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:23.186234+00:00
-- url     : https://prove2.me/theorems/32b41bb5-98d7-4cde-889d-98281ec2774c
-- title:
--   Relative entropy of entanglement $E_r(\rho^{BC}) = \min_{\sigma\ \mathrm{sep}} S(\rho^{BC}\|\sigma)$ (eq. 11)
-- statement:
--   Let $B$ and $C$ be finite nonempty index sets (Bob's and Claire's systems, ancillas included). For a matrix $\rho$ on $\mathbb C^B\otimes\mathbb C^C$, the **relative entropy of entanglement** is
--
--   $$
--   E_r(\rho) = \min_{\sigma\ \text{separable}} S(\rho\|\sigma),
--   $$
--
--   where $\sigma$ ranges over the separable states, the finite convex combinations $\sum_j w_j\,\sigma^B_j\otimes\sigma^C_j$ of products of density matrices, and $S$ is the relative entropy (9) with natural logarithms.
--
--   It measures how far Bob and Claire's state is from the set of unentangled states; it is the entanglement measure whose average increase the paper bounds by the decrease of Alice's entropy.
--
--   **Formalization Note** "Separable" is the published `QAlgorithms.Entanglement.IsSeparableDensity`. The minimum is written as an infimum in $[0,+\infty]$; it is attained (the separable set is compact and the relative entropy is lower semicontinuous), so the value is the same. The infimum is over a nonempty set, and on density matrices it is finite (the maximally mixed product state has full support).
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eq. (11), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_LindenReversibility_relEntropy

open scoped ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eq. (11), p.3: the
relative entropy of entanglement of a state `ρ` of Bob and Claire's joint system,
`E_r(ρ) = min_{σ separable} S(ρ‖σ)`.

**Formalization Note.** Bob's and Claire's systems are arbitrary finite nonempty index types `B`,
`C` (each "including ancilla's", p.2). "Separable" is the published
`QAlgorithms.Entanglement.IsSeparableDensity`: a finite convex combination of products
`σ_B ⊗ σ_C` of density matrices (it is in particular a density matrix). The page's `min` is
written as an infimum; the minimum is attained (the separable set is compact and the relative
entropy is lower semicontinuous), so the value is the same. Natural logarithms, as in (9). -/
noncomputable def relEntEnt {B C : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C] (ρ : Matrix (B × C) (B × C) ℂ) : ℝ≥0∞ :=
  ⨅ (σ : Matrix (B × C) (B × C) ℂ) (_ : QAlgorithms.Entanglement.IsSeparableDensity σ),
    relEntropy ρ σ

end LindenReversibility


