-- Prove2me | Definitions.Def_MDPFinance_POMDP_FilterData
-- name    : MDPFinance_POMDP_FilterData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:13:24.811355+00:00
-- url     : https://prove2.me/theorems/72743b37-1d08-4fa0-a17d-bd6e3f4bc275
-- title:
--   The density assumption, the Bayes operator $\Phi$, and the filter recursion $\mu_n$
-- statement:
--   Assuming $Q$ has a density $q$ w.r.t. $\sigma$-finite $\lambda$ on $E_X$, $\nu$ on
--   $E_Y$: the **Bayes operator**
--   $$\Phi(x,\rho,a,x')(C) := \frac{\int_C\big(\int q(x',y'|x,y,a)\rho(dy)\big)\nu(dy')}
--   {\int_{E_Y}\big(\int q(x',y'|x,y,a)\rho(dy)\big)\nu(dy')}$$
--   and the **filter recursion** $\mu_0:=Q_0$, $\mu_{n+1}(\cdot\mid h_n,a_n,x_{n+1}) :=
--   \Phi(x_n,\mu_n(\cdot\mid h_n),a_n,x_{n+1})$ (Eq. (5.3)-(5.4)).
--
--   $\mu_n$ is the whole chapter's key computational object: a recursively-updatable posterior over
--   the hidden state, computed from the observable history alone.
--
--   **Formalization Note.** `Phi` is carried as *data* — a genuine function into
--   `ProbabilityMeasure E_Y` — characterized by `hPhi`, its defining ratio-of-integrals formula,
--   rather than *constructed* by normalizing a raw numerator measure: proving that formula always
--   produces a well-normalized probability measure is a routine Fubini calculation the book itself
--   does not spell out, and reproducing it would be proof content belonging to a theorem, not this
--   definition. This is the chunk's own flagged pitfall (`ℙ(E_Y)` needing genuine Borel structure)
--   resolved without requiring a normalization proof at definition time.
--
--   **Moderation note.** `Phi` is required to be measurable (the book's $Q'$ is a stochastic kernel, which needs it; it is also what makes $h_n\mapsto\mu_n(\cdot\mid h_n)$ and the policy of Theorem 5.3.3(b) measurable). The defining ratio is stated with Lebesgue integrals and only where the normalizing constant $\int\!\int q(x',y'|x,y,a)\rho(dy)\nu(dy')$ is positive and finite: the draft demanded the formula for every $x'$, and at an observation $x'$ with $q(x',\cdot\mid x,\cdot,a)\equiv 0$ (e.g. any model with finitely supported observations) it demanded $\Phi(x,\rho,a,x')(E_Y)=0/0=0$, which no probability measure satisfies, so no `FilterData` existed and every theorem of the mission was vacuous. Such $x'$ form a $Q^X(\cdot|x,\rho,a)$-null set, on which the book's $\Phi$ is undefined as well.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 151, PDF 164, standing density assumption and Equations (5.3)-(5.4)

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.POMDP

variable {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]

/-- The standing assumption of §5.2 (Bäuerle–Rieder, p. 151, PDF 164): `Q` has a density `q`
with respect to σ-finite reference measures `λ` on `E_X` and `ν` on `E_Y`,
`Q(d(x',y')|x,y,a) = q(x',y'|x,y,a)λ(dx')ν(dy')`. The Bayes operator `Φ` (`Phi`) is *data*, not a
raw formula: it is a genuine measurable `ProbabilityMeasure E_Y`-valued function (so the
reduction's state space `E_X × ℙ(E_Y)` is a bona fide Borel space, per this chunk's own
pitfall), characterized by `hPhi`, the ratio-of-integrals formula the book defines it by,
wherever that formula defines a probability measure, i.e. wherever the normalizing constant
`∫ ∫ q(x',y'|x,y,a) ρ(dy) ν(dy')` is positive and finite (elsewhere the book's quotient is
`0/0` or `∞/∞`, and such `x'` form a null set for the marginal `Q^X(·|x,ρ,a)`). -/
structure FilterData (M : PartiallyObservableMDM EX EY A) where
  lam : Measure EX
  nu : Measure EY
  hlam_sigmaFinite : SigmaFinite lam
  hnu_sigmaFinite : SigmaFinite nu
  q : EX → EY → A → EX → EY → ℝ
  hq_meas : Measurable fun p : (EX × EY × A) × (EX × EY) => q p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2
  hq_nonneg : ∀ x y a x' y', 0 ≤ q x y a x' y'
  hQ_density : ∀ x y a, M.Q ((x, y), a) =
    (lam.prod nu).withDensity fun p => ENNReal.ofReal (q x y a p.1 p.2)
  Phi : EX → ProbabilityMeasure EY → A → EX → ProbabilityMeasure EY
  hPhi_meas : Measurable fun p : (EX × ProbabilityMeasure EY) × A × EX =>
    Phi p.1.1 p.1.2 p.2.1 p.2.2
  hPhi : ∀ x (ρ : ProbabilityMeasure EY) a x',
    0 < (∫⁻ y', (∫⁻ y, ENNReal.ofReal (q x y a x' y') ∂ρ.toMeasure) ∂nu) →
    (∫⁻ y', (∫⁻ y, ENNReal.ofReal (q x y a x' y') ∂ρ.toMeasure) ∂nu) < ⊤ →
    ∀ C, MeasurableSet C →
    (Phi x ρ a x').toMeasure C =
      (∫⁻ y' in C, (∫⁻ y, ENNReal.ofReal (q x y a x' y') ∂ρ.toMeasure) ∂nu) /
        (∫⁻ y', (∫⁻ y, ENNReal.ofReal (q x y a x' y') ∂ρ.toMeasure) ∂nu)

/-- The filter recursion `μ_0 := Q_0`, `μ_{n+1}(·|h_n,a_n,x_{n+1}) := Φ(x_n,μ_n(·|h_n),a_n,
x_{n+1})` (Bäuerle–Rieder, Eq. (5.3)-(5.4), p. 151, PDF 164), as a pure function of the
observable history `(xs,as)` (padded `ℕ`-indexed sequences, as in `Policy`). -/
noncomputable def FilterData.mu (M : PartiallyObservableMDM EX EY A) (Fd : FilterData M) :
    (n : ℕ) → (ℕ → EX) → (ℕ → A) → ProbabilityMeasure EY
  | 0, _, _ => ⟨M.Q0, M.isProbQ0⟩
  | (n + 1), xs, as => Fd.Phi (xs n) (Fd.mu M n xs as) (as n) (xs (n + 1))

end MDPFinance.POMDP


