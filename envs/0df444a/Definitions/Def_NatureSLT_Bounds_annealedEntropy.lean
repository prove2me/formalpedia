-- Prove2me | Definitions.Def_NatureSLT_Bounds_annealedEntropy
-- name    : NatureSLT_Bounds_annealedEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:35.36899+00:00
-- url     : https://prove2.me/theorems/e98e8931-709f-4e20-93ba-624d1885682d
-- title:
--   Annealed VC entropy $H^\Lambda_{\mathrm{ann}}(\ell) = \ln E N^\Lambda(z_1, \dots, z_\ell)$
-- statement:
--   Let $(Z, F)$ be a probability space, $Q(z, \alpha)$, $\alpha \in \Lambda$, a set of indicator functions on $Z$, and $N^\Lambda(z_1, \dots, z_\ell)$ the number of different separations of a sample $z_1, \dots, z_\ell$ by the set (Section 2.3.2). The **annealed VC entropy** of the set on samples of size $\ell$ is
--   $$H^\Lambda_{\mathrm{ann}}(\ell) = \ln E\, N^\Lambda(z_1, \dots, z_\ell),$$
--   where the expectation is taken over an i.i.d. sample $z_1, \dots, z_\ell$ drawn from $F$, i.e. with respect to the product measure $F^\ell$ on $Z^\ell$, and $\ln$ is the natural logarithm.
--
--   The annealed entropy lies between the VC entropy $E \ln N^\Lambda$ and the growth function $\ln \sup N^\Lambda$, and is the quantity in the distribution-dependent basic inequalities (Theorems 3.1 and 3.2 of the book).
--
--   **Formalization Note** The expectation is the Bochner integral of $N^\Lambda$ (cast to $\mathbb R$) against `Measure.pi (fun _ => F)`. The integral is only meaningful when $N^\Lambda$ is measurable on $Z^\ell$ (it is bounded by $2^\ell$, so it is then integrable); every theorem using this definition assumes that measurability explicitly.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 55, Section 2.7 (i)

import Mathlib
import Definitions.Def_NatureSLT_Bounds_numSeparations

open MeasureTheory

namespace NatureSLT.Bounds

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., p. 55, §2.7 (i): the annealed
VC entropy `H^Λ_ann(ℓ) = ln E N^Λ(z₁, …, z_ℓ)`, the expectation taken over an i.i.d. sample
`z₁, …, z_ℓ` drawn from `F`, i.e. under the product measure `F^ℓ`. -/
noncomputable def annealedEntropy {Λ Z : Type*} [MeasurableSpace Z] (F : Measure Z)
    (Q : Λ → Z → ℝ) (ℓ : ℕ) : ℝ :=
  Real.log (∫ z, (numSeparations Q z : ℝ) ∂(Measure.pi fun _ : Fin ℓ => F))

end NatureSLT.Bounds


