-- Prove2me | Definitions.Def_FoundationsML_Stability_UniformlyStable
-- name    : FoundationsML_Stability_UniformlyStable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:21:16.76766+00:00
-- url     : https://prove2.me/theorems/c71b112e-a9b2-4f19-bbf6-137b099655dc
-- title:
--   Uniform stability (Definition 14.1)
-- statement:
--   **Definition 14.1 (Uniform stability), p. 334, PDF p. 351.** Let $S$ and $S'$ be any two
--   training samples that differ by a single point. A learning algorithm $A$ is uniformly
--   $\beta$-stable if the hypotheses it returns when trained on any such $S$ and $S'$ satisfy
--   $\forall z\in Z,\ |L_z(h_S) - L_z(h_{S'})| \le \beta$. The smallest such $\beta$ is called
--   the stability coefficient of $A$.
--
--   **Formalization Note.** "$S$ and $S'$ differ by a single point" is `∃ i, ∀ j ≠ i, S j = S'
--   j`; the "smallest such `β`" optimality remark is not incorporated into the `Prop` itself,
--   matching the definition's own formal content.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 334, Definition 14.1 (PDF p. 351)

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss

namespace FoundationsML.Stability

/-- Definition 14.1 (Uniform stability; Mohri, Rostamizadeh & Talwalkar, *Foundations of
Machine Learning*, 2nd ed., MIT Press 2018, p. 334, PDF p. 351). A learning algorithm `A`
(mapping a sample of size `m` to a hypothesis) is uniformly `β`-stable if, for any two training
samples `S`, `S'` that differ by a single point, the hypotheses it returns satisfy
`∀ z, |L_z(h_S) − L_z(h_{S'})| ≤ β`.

**Formalization Note.** "`S` and `S'` differ by a single point" is `∃ i, ∀ j ≠ i, S j = S' j`
(they agree at every index except one); the book's "smallest such `β`" (the stability
coefficient) is a separate optimality remark, not part of the `Prop` itself. -/
def UniformlyStable {X Y Y' : Type*} {m : ℕ} (L : Y' → Y → ℝ)
    (A : (Fin m → X × Y) → (X → Y')) (β : ℝ) : Prop :=
  ∀ S S' : Fin m → X × Y, (∃ i : Fin m, ∀ j : Fin m, j ≠ i → S j = S' j) →
    ∀ z : X × Y, |Loss L (A S) z - Loss L (A S') z| ≤ β

end FoundationsML.Stability


