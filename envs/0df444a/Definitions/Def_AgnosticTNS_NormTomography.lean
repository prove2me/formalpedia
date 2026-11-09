-- Prove2me | Definitions.Def_AgnosticTNS_NormTomography
-- name    : AgnosticTNS_NormTomography
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:29.678221+00:00
-- url     : https://prove2.me/theorems/1b439b37-a4f1-4a7f-929d-96349bb4eaae
-- title:
--   Normalised tomography procedure with copy function $m_A$
-- statement:
--   A function $m_A(r,D,\eta,\beta)$ is the copy function of a **normalised tomography procedure** if for every finite-dimensional system of dimension $D$, rank bound $r\ge1$, accuracy $\eta>0$ and failure probability $\beta\in(0,1)$ there is a measurement with finitely many outcomes on $m_A(r,D,\eta,\beta)$ copies and an estimator with density-operator values such that for every state $\rho$ of rank at most $r$, $\|\rho-\hat\rho\|_1\le\eta$ with probability at least $1-\beta$. The paper uses the procedure of [Pel+25, Theorem 1.3], with $m_A=O((rD+\log(1/\beta))/\eta^2)$ (2.11).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 2.3, Eq. (2.11), p.14

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
open scoped ComplexOrder
open Classical

namespace AgnosticTNS

/-- **A normalised tomography procedure with copy function `m_A`**, §2.3, Eq. (2.11), p.14 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
for every finite-dimensional system `α` (dimension `D = |α|`), rank bound `r ≥ 1`, accuracy `η > 0`
and failure probability `β ∈ (0, 1)`, a measurement (POVM `E` with finitely many outcomes) on
`m_A(r, D, η, β)` copies and an estimator `est` with density-operator values such that for every
density operator `ρ` of rank at most `r`, `‖ρ − est‖₁ ≤ η` with probability at least `1 − β`.

**Formalization Note** The paper fixes the procedure of [Pel+25, Theorem 1.3]; this predicate is the
property of it that Corollary 2.7 uses. Probabilities are `Σ_ω tr(E_ω ρ^{⊗m})`. -/
def NormTomography (mA : ℕ → ℕ → ℝ → ℝ → ℕ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (r : ℕ) (η β : ℝ), 1 ≤ r → 0 < η → 0 < β → β < 1 →
    ∃ (Ω : Type) (_ : Fintype Ω)
      (E : Ω → Matrix (Fin (mA r (Fintype.card α) η β) → α) (Fin (mA r (Fintype.card α) η β) → α) ℂ)
      (est : Ω → Matrix α α ℂ),
      (∀ ω, (E ω).PosSemidef) ∧ ∑ ω, E ω = 1 ∧ (∀ ω, WildeQIT.IsDensityOperator (est ω)) ∧
      ∀ ρ : Matrix α α ℂ, WildeQIT.IsDensityOperator ρ → ρ.rank ≤ r →
        1 - β ≤ ∑ ω, if WildeQIT.traceNorm (ρ - est ω) ≤ η then
          (E ω * ShadowTomography.UpperBound.tensorPow ρ (mA r (Fintype.card α) η β)).trace.re else 0

end AgnosticTNS


