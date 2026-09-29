-- Prove2me | Definitions.Def_GaloisRep_TameCharacter
-- name    : GaloisRep_TameCharacter
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/fb2ec975-e5ec-5d63-8d83-ee2c11f38a4a
-- title:
--   Tame character attached to a place of Q​
-- statement:
--   The module defines a single function, [`ValuationSubring.tameCharacter`](../def/GaloisRep_TameCharacter.html#L7). Its data are: a valuation subring $P$ of $\overline{\mathbb{Q}}$ (the algebraic closure of $\mathbb{Q}$ as constructed in Mathlib), regarded as a place of $\overline{\mathbb{Q}}$; an element $\pi \in \overline{\mathbb{Q}}$; and a $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$. The value $\mathrm{tameCharacter}\,P\,\pi\,\sigma$ lies in the residue field $\kappa(P)$ of the local ring $P$, and is defined by a case distinction on whether the quotient $\sigma(\pi)/\pi$, formed in the field $\overline{\mathbb{Q}}$, belongs to $P$: if it does, the value is the image of that element under the residue map $P \to \kappa(P)$; otherwise the value is $0$. In particular the value is $0$ whenever $\sigma(\pi)/\pi$ has negative valuation at $P$, and also when $\pi = 0$, where the division convention gives $\sigma(\pi)/\pi = 0$ and the residue is $0$ anyway.
--
--   The definition is thus a bare function of $\sigma$, with no multiplicativity, no restriction to a decomposition or inertia subgroup, and no hypothesis relating $\pi$ to $P$ built in; the membership condition is settled by classical decidability. The intended situation is that $P$ lies over a prime $p$ and $\pi$ is a root of $X^{p^n-1} - p$, so that $(\sigma(\pi)/\pi)^{p^n-1} = 1$, the quotient is a root of unity lying in $P$, and the restriction of $\sigma \mapsto \mathrm{tameCharacter}\,P\,\pi\,\sigma$ to the inertia subgroup at $P$ is the fundamental character of level $n$ of tame inertia, with values in the $(p^n-1)$-st roots of unity of $\kappa(P)$. Multiplicativity on inertia, independence of the choice of $\pi$, and the behaviour under conjugation by a Frobenius element are separate assertions about this function rather than part of its definition.
--
--   **Relation to Mathlib.** Built from Mathlib's `ValuationSubring`, `IsLocalRing.ResidueField` and `IsLocalRing.residue`; Mathlib has no notion of tame character or fundamental character of tame inertia, so this is the project's own definition.
--
--   **Where it is used.** This function supplies the tame (fundamental) characters used to analyse the restriction to inertia at $p$ of mod $p$ Galois representations, in particular in the local analysis underlying level lowering and the classification of the possible shapes of $\bar\rho|_{I_p}$. It is imported throughout the Galois-representation-theoretic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_TameCharacter.lean

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Algebra.Rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace ValuationSubring

noncomputable def tameCharacter (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : IsLocalRing.ResidueField P := by
  classical
  exact if h : σ π / π ∈ P then IsLocalRing.residue P ⟨σ π / π, h⟩ else 0

end ValuationSubring


