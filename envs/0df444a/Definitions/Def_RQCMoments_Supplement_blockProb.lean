-- Prove2me | Definitions.Def_RQCMoments_Supplement_blockProb
-- name    : RQCMoments_Supplement_blockProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:48:00.138034+00:00
-- url     : https://prove2.me/theorems/b2693c59-2adb-497e-9629-6383cda7fb47
-- title:
--   Block probability $X=\sum_{r\in S}|\langle r|U|y\rangle|^2$ and the law of a product of independent variables
-- statement:
--   For a unitary $U\in U(N)$, a set $S$ of row indices and a column $y$, the **block probability** is
--
--   $$X(U)=\sum_{r\in S}|\langle r|U|y\rangle|^2 ,$$
--
--   the total probability of the basis states in $S$ when $U$ acts on $|y\rangle$. For real distributions $\mu,\nu$, the law of the product $XY$ of independent $X\sim\mu$ and $Y\sim\nu$ is the image of the product measure $\mu\otimes\nu$ under $(x,y)\mapsto xy$.
--
--   These are the objects of Theorems 6.11 and 6.13, which compare the law of $X_kY$ for a design with that of $XY$ for Haar, with $Y\sim\mathrm{Beta}(1,a-1)$ independent.
--
--   **Formalization Note** $|\langle r|U|y\rangle|^2$ is the published `RQCMoments.entry`.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.11, p.45 (PDF p.47); (145), p.38; (41), p.18

import Mathlib
import Definitions.Def_RQCMoments_entry

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- The law of the product `XY` of independent real random variables `X ∼ μ` and `Y ∼ ν`: the
pushforward of the product measure `μ ⊗ ν` under `(x, y) ↦ x y`
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.11, p.45, PDF p.47). -/
noncomputable def productLaw (μ ν : Measure ℝ) : Measure ℝ :=
  (μ.prod ν).map (fun z : ℝ × ℝ => z.1 * z.2)

/-- The block probability `X = ∑_{r ∈ S} |⟨r|U|y⟩|²` of a set `S` of basis states in column `y`
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 6.11, p.45, PDF p.47; (145), p.38; (41), p.18).

**Formalization Note** `entry r y U = |⟨r|U|y⟩|²` is the published `RQCMoments.entry`. -/
noncomputable def blockProb {N : ℕ} (S : Finset (Fin N)) (y : Fin N) (U : Matrix.unitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ r ∈ S, entry r y U

end Supplement

end RQCMoments


