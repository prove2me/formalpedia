-- Prove2me | Definitions.Def_BosonicLearn_priorMu
-- name    : BosonicLearn_priorMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:25:14.151811+00:00
-- url     : https://prove2.me/theorems/e8b30a78-b620-4da8-a59b-3f5857587787
-- title:
--   The prior $\mu(X)\propto e^{-\frac n4\|X\|_{\mathrm F}^2}\mathbb 1(\|X\|_{\mathrm{op}}\le4)$
-- statement:
--   The prior $\mu$ is the probability measure on $\mathrm{Herm}_0(n)$ with density
--
--   $$\mu(X)=Z_\mu^{-1}\exp\Big(-\frac n4\|X\|_{\mathrm F}^2\Big)\,\mathbb 1(\|X\|_{\mathrm{op}}\le 4)$$
--
--   with respect to Lebesgue measure, $Z_\mu$ the normalizing constant. It is the traceless Gaussian unitary ensemble conditioned on $G_{\mathrm{supp}}$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.1, Eq. (32), p. 30

import Mathlib
import Definitions.Def_BosonicLearn_Gsupp

open MeasureTheory

namespace BosonicLearn

/-- **The prior `µ` on fugacity perturbations.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.1, Eq. (32), p. 30: "Sample X ∼ GUE*(n) conditioned on X ∈ G_supp. … The density of X with respect
to the Lebesgue measure on Herm_0(n) is given by µ(X) = Z_µ^{−1} exp(−(n/4)‖X‖_F²) 𝟙(‖X‖_op ≤ 4)."

`priorMu n` is the probability measure on `Herm₀(n)` with density proportional to `exp(−(n/4)‖X‖_F²)` on
`G_supp` with respect to Lebesgue (additive Haar) measure, normalized by its total mass `Z_µ`.

**Formalization Note.** `Measure.addHaar` is one fixed Haar measure; after normalization the result does not
depend on that choice. `‖X‖_F` is the Schatten 2-norm. -/
noncomputable def priorMu (n : ℕ) : Measure (Herm0 n) :=
  let m : Measure (Herm0 n) := ((Measure.addHaar : Measure (Herm0 n)).restrict (Gsupp n)).withDensity
    (fun X => ENNReal.ofReal (Real.exp (-(n / 4 : ℝ) * WHMultiplicativity.schattenNorm 2 (X : Matrix (Fin n) (Fin n) ℂ) ^ 2)))
  (m Set.univ)⁻¹ • m

end BosonicLearn


