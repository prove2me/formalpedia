-- Prove2me | Definitions.Def_PottsRapidMixing_CondLaw
-- name    : PottsRapidMixing_CondLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:38.926123+00:00
-- url     : https://prove2.me/theorems/61a1c6e0-9037-4755-b682-ca8646f8055c
-- title:
--   Conditional laws, conditional entropy and the aggregate local entropy $I_\pi(\nu)$
-- statement:
--   Let $\pi$ be a law on a finite product $S^I$. For $A\subseteq I$ and a configuration $x$, $\pi(\cdot\mid x_A)$ is $\pi$ restricted to the configurations agreeing with $x$ on $A$, renormalized, and
--   $$\mathbb E_\pi\bigl[\mathrm{Ent}_\pi(f\mid x_A)\bigr]=\sum_x\pi(x)\,\mathrm{Ent}_{\pi(\cdot\mid x_A)}(f),\qquad \mathrm{Ent}_\mu(f)=\mathbb E_\mu[f\log f]-\mathbb E_\mu[f]\log\mathbb E_\mu[f].$$
--   The *aggregate local entropy to stationarity* of a law $\nu$ (Definition 1.5) is
--   $$I_\pi(\nu)=\sum_{i\in I}\mathbb E_{\nu_{-i}}\bigl[\mathrm{KL}\bigl(\nu_i(\cdot\mid x_{-i})\,\|\,\pi_i(\cdot\mid x_{-i})\bigr)\bigr].$$
--
--   The quantity $I_\pi(\nu)$ measures how far the single-site conditionals of $\nu$ are from those of $\pi$; it is the escape side of the shattering–escape dichotomy.
--
--   **Formalization Note** $\mathrm{Ent}$ is the published `GibbsCongestion.entropy`. Expanding the expectation and the divergence gives $I_\pi(\nu)=\sum_i\sum_x\nu(x)\log\bigl(\nu(x_i\mid x_{-i})/\pi(x_i\mid x_{-i})\bigr)$, the form in Lean; terms with $\nu(x)=0$ vanish, which is the convention $0\log0=0$, so $\nu$ need not have full support. The reference law $\pi$ has full support in every use. The vertex case is $I=V$, $S=[q]$; the edge case $I_\phi$ is $I=E$, $S=\{0,1\}$.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Definition 1.5, p.6; p.13 (Ent, I_ϕ); p.29 (Ent(h | A_{-e}))

import Mathlib
import Definitions.Def_GibbsCongestion_entropy

open scoped Classical

namespace PottsRapidMixing

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

/-- The conditional law `π(· | x_A)` of a law `π` on the product `I → S`, given the coordinates in
`A`: the restriction of `π` to the configurations that agree with `x` on `A`, renormalized
(Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, pp.10, 13, 16).

**Formalization Note.** Every use has a reference law of full support, so the normalizer is
positive. -/
noncomputable def condLaw (π : (I → S) → ℝ) (A : Finset I) (x : I → S) : (I → S) → ℝ :=
  fun y => if ∀ i ∈ A, y i = x i then
    π y / ∑ z ∈ Finset.univ.filter (fun z : I → S => ∀ i ∈ A, z i = x i), π z
  else 0

/-- `E_π[Ent_π(f | x_A)]`: the expected entropy of `f` under the conditional law given the
coordinates in `A` (arXiv:2610.42059, pp.13, 29). `Ent` is the published
`GibbsCongestion.entropy`, which is `E_π[f log f] − E_π[f] log E_π[f]`, with `0 log 0 = 0`. -/
noncomputable def expCondEnt (π : (I → S) → ℝ) (A : Finset I) (f : (I → S) → ℝ) : ℝ :=
  ∑ x, π x * GibbsCongestion.entropy (condLaw π A x) f

/-- The single-site conditional probability `π(x_i | x_{−i})`. -/
noncomputable def condSite (π : (I → S) → ℝ) (i : I) (x : I → S) : ℝ :=
  π x / ∑ a, π (Function.update x i a)

/-- The aggregate local entropy to stationarity, Definition 1.5 (arXiv:2610.42059, p.6):
`I_π(ν) = ∑_i E_{ν_{−i}}[KL(ν_i(· | x_{−i}) ‖ π_i(· | x_{−i}))]`.

**Formalization Note.** Expanding the expectation and the divergence gives the sum over
configurations written here, `∑_i ∑_x ν(x) log(ν(x_i | x_{−i}) / π(x_i | x_{−i}))`, and terms with
`ν(x) = 0` vanish, which is the `0 log 0 = 0` convention. `ν` need not have full support; the
reference law `π` has full support in every use. The vertex case is `I = V`, `S = Fin q`, the edge
case (`I_ϕ`, p.13) is `I = E`, `S = Bool`. -/
noncomputable def localEntropy (π ν : (I → S) → ℝ) : ℝ :=
  ∑ i, ∑ x, ν x * Real.log (condSite ν i x / condSite π i x)

end PottsRapidMixing


