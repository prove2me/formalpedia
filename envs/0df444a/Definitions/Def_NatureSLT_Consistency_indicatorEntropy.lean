-- Prove2me | Definitions.Def_NatureSLT_Consistency_indicatorEntropy
-- name    : NatureSLT_Consistency_indicatorEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:09.790394+00:00
-- url     : https://prove2.me/theorems/ca5b24f8-faf3-47d4-8a3b-bc1c6342ec27
-- title:
--   Entropy, annealed VC entropy and growth function of a set of indicator functions
-- statement:
--   Let $Q(z,\alpha)$, $\alpha\in\Lambda$, be a set of indicator functions on $Z$ (values $0$ and $1$), $F$ a probability measure on $Z$, and $z_1,\dots,z_\ell$ a sample. Let $N^\Lambda(z_1,\dots,z_\ell)$ be the number of different binary vectors $q(\alpha)=(Q(z_1,\alpha),\dots,Q(z_\ell,\alpha))$, $\alpha\in\Lambda$, that is, the number of different separations of the sample by the set. With the expectation taken over an i.i.d. sample from $F$:
--
--   1. the **entropy** $H^\Lambda(\ell) = E\ln N^\Lambda(z_1,\dots,z_\ell)$;
--   2. the **annealed VC entropy** $H^\Lambda_{\mathrm{ann}}(\ell) = \ln E N^\Lambda(z_1,\dots,z_\ell)$;
--   3. the **growth function**
--   $$G^\Lambda(\ell) = \ln \sup_{z_1,\dots,z_\ell} N^\Lambda(z_1,\dots,z_\ell).$$
--
--   These three quantities are the capacity concepts behind the three milestones of learning theory: conditions on their growth in $\ell$ give consistency, a fast rate of convergence, and distribution-free guarantees.
--
--   **Formalization Note** $N^\Lambda$ is the cardinality of the set of vectors $q(\alpha)$ (a Lean `Nat.card`); for $\{0,1\}$-valued functions it is finite and at most $2^\ell$, which also makes the real supremum in $G^\Lambda$ genuine. Theorems using these quantities assume $Q$ is $\{0,1\}$-valued and $N^\Lambda$ a measurable function of the sample. Logarithms are natural.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 42, Section 2.3.2, and p. 55, Section 2.7

import Mathlib

open MeasureTheory

namespace NatureSLT.Consistency

/-- `N^Λ(z₁, …, z_ℓ)` (Vapnik 2000, Section 2.3.2, p. 42): for a set of indicator functions
`Q(z, α) ∈ {0, 1}`, the number of different binary vectors
`q(α) = (Q(z₁, α), …, Q(z_ℓ, α))`, `α ∈ Λ`, i.e. the number of different separations of the
sample by the set of functions. It is `Nat.card` of the range of `α ↦ q(α)`; for `{0, 1}`-valued
`Q` that range lies in `{0, 1}^ℓ`, so the count is finite and at most `2^ℓ`. -/
noncomputable def diversity {Z Λ : Type*} (Q : Λ → Z → ℝ) {ℓ : ℕ} (z : Fin ℓ → Z) : ℕ :=
  Nat.card (Set.range fun α : Λ => fun i : Fin ℓ => Q α (z i))

/-- The **entropy** `H^Λ(ℓ) = E ln N^Λ(z₁, …, z_ℓ)` of a set of indicator functions on samples of
size `ℓ` (p. 42; p. 55), the expectation taken under the product measure `F^ℓ`. -/
noncomputable def entropy {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) (ℓ : ℕ) : ℝ :=
  ∫ z, Real.log (diversity Q z : ℝ) ∂(Measure.pi fun _ : Fin ℓ => F)

/-- The **annealed VC entropy** `H^Λ_ann(ℓ) = ln E N^Λ(z₁, …, z_ℓ)` (Section 2.7, p. 55). -/
noncomputable def annealedEntropy {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) (ℓ : ℕ) : ℝ :=
  Real.log (∫ z, (diversity Q z : ℝ) ∂(Measure.pi fun _ : Fin ℓ => F))

/-- The **growth function** `G^Λ(ℓ) = ln sup_{z₁, …, z_ℓ} N^Λ(z₁, …, z_ℓ)` (Section 2.7, p. 55).
For an indicator set the values `N^Λ ≤ 2^ℓ` are bounded, so the real supremum is genuine. -/
noncomputable def growthFunction {Z Λ : Type*} (Q : Λ → Z → ℝ) (ℓ : ℕ) : ℝ :=
  Real.log (⨆ z : Fin ℓ → Z, (diversity Q z : ℝ))

end NatureSLT.Consistency


