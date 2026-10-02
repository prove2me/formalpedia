-- Prove2me | Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
-- name    : TeschlQM_Shared_IsProjValuedMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:25:20.533518+00:00
-- url     : https://prove2.me/theorems/a17d1ba6-8da8-402a-86e5-4b2caa11a862
-- title:
--   Projection-valued measure on the Borel sets of $\mathbb{R}$ (3.5)
-- statement:
--   Let $\mathfrak H$ be a complex Hilbert space and let $\mathfrak L(\mathfrak H)$ denote the bounded linear operators on $\mathfrak H$. A map $\Omega \mapsto P(\Omega)$ from the Borel sets $\Omega \subseteq \mathbb{R}$ to $\mathfrak L(\mathfrak H)$ is a **projection-valued measure** if every $P(\Omega)$ is an orthogonal projection, $P(\Omega)^* = P(\Omega) = P(\Omega)^2$, and
--
--   1. $P(\mathbb{R}) = \mathbb{I}$;
--   2. (strong $\sigma$-additivity) whenever $\Omega = \bigcup_n \Omega_n$ with $\Omega_n \cap \Omega_m = \emptyset$ for $n \ne m$,
--   $$\sum_n P(\Omega_n)\psi = P(\Omega)\psi \qquad \text{for every } \psi \in \mathfrak H .$$
--
--   The convergence in (2) is convergence of the series in the norm of $\mathfrak H$ for each fixed vector $\psi$, not convergence of the operators $\sum_n P(\Omega_n)$ in operator norm, which already fails for multiplication operators.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `02-spectral-theorem`: p. 89, Section 3.1; p. 90, Theorem 3.1; p. 92, Theorem 3.2; p. 94, Lemma 3.5; p. 96, Theorem 3.7; p. 97, Theorem 3.8; p. 97, Corollary 3.9
--   - chunk `04-min-max`: p. 119, Theorem 4.12 (i); p. 119, Theorem 4.12 (ii)
--   - chunk `05-rage`: pp. 123–124, Theorem 5.1; p. 128, Theorem 5.6, Eq. (5.13); p. 129, Theorem 5.7, Eq. (5.14); p. 130, Theorem 5.8, Eq. (5.18); p. 130, Corollary 5.9, Eqs. (5.19)–(5.20)
--   - chunk `14-scattering`: p. 248, Lemma 12.1; p. 248, Theorem 12.2, Eq. (12.8); p. 249, Lemma 12.3, Eqs. (12.11)–(12.12); p. 249, Theorem 12.4
--
--   **Formalization Note.** $P$ is a function on all subsets of $\mathbb{R}$ with values in `H →L[ℂ] H`; only its values on Borel sets (`MeasurableSet` for the Borel $\sigma$-algebra of $\mathbb{R}$) are constrained, and its values on other sets play no role anywhere in this development (uniqueness statements compare values on Borel sets only). "Orthogonal projection" is `IsSelfAdjoint` together with `IsIdempotentElem`. The families in (2) are indexed by $\mathbb{N}$ and the series is the limit of its partial sums; a finite family is the case where all but finitely many $\Omega_n$ are empty. The Hilbert space is not assumed separable.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 88, Section 3.1, Eq. (3.5)

import Mathlib

namespace TeschlQM.Shared

/-- Teschl, p. 88, (3.5): a **projection-valued measure** on the complex Hilbert space `H`.
`P` assigns to every Borel set `Ω ⊆ ℝ` an orthogonal projection `P Ω` (`P(Ω)* = P(Ω) = P(Ω)²`)
such that (i) `P(ℝ) = 𝕀` and (ii) for pairwise disjoint Borel sets `Ω n`, the series
`∑ₙ P(Ωₙ)ψ` converges to `P(⋃ₙ Ωₙ)ψ` for every `ψ` (strong σ-additivity; not norm convergence).
Only the values of `P` on Borel sets are constrained; its values on other sets play no role. -/
def IsProjValuedMeasure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Prop :=
  (∀ Ω : Set ℝ, MeasurableSet Ω → IsSelfAdjoint (P Ω) ∧ IsIdempotentElem (P Ω)) ∧
  P Set.univ = 1 ∧
  ∀ Ω : ℕ → Set ℝ, (∀ n, MeasurableSet (Ω n)) → Pairwise (Function.onFun Disjoint Ω) →
    ∀ ψ : H, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, P (Ω n) ψ) Filter.atTop
      (nhds (P (⋃ n, Ω n) ψ))

end TeschlQM.Shared


