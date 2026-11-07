-- Prove2me | Definitions.Def_GaussTesting_IsTester
-- name    : GaussTesting_IsTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:00:50.932209+00:00
-- url     : https://prove2.me/theorems/49e1d15b-4761-4c73-835d-9ab5bd187d16
-- title:
--   $(\varepsilon_1,\varepsilon_2,\delta)$-testers (Definition 1.2)
-- statement:
--   Let $\mathcal C$ be a class of pure states on $\mathcal H$. A tester $T$ is an **$(\varepsilon_1,\varepsilon_2,\delta)$-tester for $\mathcal C$** if for every unit vector $|\psi\rangle\in\mathcal H$:
--
--   1. if $\mathrm{dist}(\psi,\mathcal C)\le\varepsilon_1$, then $\Pr[T(|\psi\rangle^{\otimes t})=\mathrm{ACCEPT}]\ge1-\delta$;
--   2. if $\mathrm{dist}(\psi,\mathcal C)\ge\varepsilon_2$, then $\Pr[T(|\psi\rangle^{\otimes t})=\mathrm{ACCEPT}]\le\delta$.
--
--   The quantifier ranges over all unit vectors of the full Hilbert space (for Fock spaces: no parity, particle-number or energy promise, Remark 1.5).
--
--   **Formalization Note** The ranges $0\le\varepsilon_1<\varepsilon_2$, $0\le\delta<1/2$ of Definition 1.2 are hypotheses of the theorems that use this predicate.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Definition 1.2, p.4

import Definitions.Def_GaussTesting_BlockTester
import Definitions.Def_GaussTesting_distTo

namespace GaussTesting

/-- `T` is an `(ε₁, ε₂, δ)`-tester for the class `𝒞`: for every pure state `|ψ⟩`,
1. if `dist(ψ, 𝒞) ≤ ε₁` then `Pr[T accepts] ≥ 1 − δ`, and
2. if `dist(ψ, 𝒞) ≥ ε₂` then `Pr[T accepts] ≤ δ`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Definition 1.2, p.4.

**Formalization Note.** "For all `|ψ⟩ ∈ ℋ`" ranges over all unit vectors of the whole Fock space
(no parity, particle-number or energy promise; Remark 1.5, p.6). The range conditions
`0 ≤ ε₁ < ε₂`, `0 ≤ δ < 1/2` of Definition 1.2 are hypotheses of the theorems that use this predicate;
the number of copies is `k · T.rounds`. -/
def IsTester {ι : Type*} {k : ℕ} (C : Set (Ell2 ι)) (T : BlockTester ι k) (ε₁ ε₂ δ : ℝ) : Prop :=
  ∀ ψ : Ell2 ι, ‖ψ‖ = 1 →
    (distTo ψ C ≤ ε₁ → 1 - δ ≤ T.acceptProb ψ) ∧ (ε₂ ≤ distTo ψ C → T.acceptProb ψ ≤ δ)

end GaussTesting


