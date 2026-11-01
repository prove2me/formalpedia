-- Prove2me | Definitions.Def_StrategicNRM_Equilibrium
-- name    : StrategicNRM_Equilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:41.176274+00:00
-- url     : https://prove2.me/theorems/6e0d2aa2-725c-429a-876a-17cfcacbf344
-- title:
--   Equilibrium, the revenue $J^\pi$ and the optimal revenue $J^\star$
-- statement:
--   A **profile** consists of a symmetric rule $\sigma$, one rule for each type, and an outcome of each customer of each crowd. For one more customer of type $\phi$ taking the decision $d=(\tau,a)$ against a crowd $c$ of others, the outcome is $d$ if the product is still there at his place $(\tau,t_\phi)$ in the order, and otherwise he exits with nothing; the price is read on the others' price path. Write $y_\phi(c)$ for the outcome of $\phi$ following $\sigma_\phi$ against $c$.
--
--   The profile is an **equilibrium** under the policy $\theta$ if
--
--   1. every rule $\sigma_\phi$ is feasible;
--   2. on every crowd of types the outcomes form a play;
--   3. for every type $\phi$ and every feasible rule $r$ with integrable payoff,
--
--   $$
--   E_{-\phi}\big[U(\phi,\text{outcome of } r)\big]\le E_{-\phi}\big[U(\phi,y_\phi)\big];
--   $$
--
--   4. the outcome is jointly measurable in the type and the crowd, the price of each type is integrable, and the absolute payments of the crowd have a finite expected total.
--
--   The **revenue** is $J=E[\sum_{\phi\in\mathcal H_T}p_\phi]$, and $J^\star$ is its supremum over admissible policies and their equilibria.
--
--   **Formalization Note** The others' path is the path the customer faces: he is invisible to the seller until he leaves, so his presence changes no price up to his exit. The best response is ex ante, which the printed conditional best response implies by the tower property, and is required of every type in $\Phi$, as p.9 uses it. The paper proves neither existence nor uniqueness of an equilibrium (footnote 2, p.8), so $J^\star$ is over all of them; a policy with no equilibrium contributes nothing. Item 4 says that the expectations of the paper are defined. A proved instance of an equilibrium is kept with the mission's verification files.
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §2, pp.7–8

import Mathlib
import Definitions.Def_StrategicNRM_Game

open MeasureTheory
open scoped ENNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- The customers' side of the game: the symmetric rule `σ` (one rule for each type) and, for each
crowd, the outcome of each of its customers. -/
structure Profile (n : ℕ) where
  σ : CType n → Rule n
  play : (c : Crowd (CType n)) → Fin c.1 → Decision n

/-- The price path of the crowd `c`. -/
noncomputable def Profile.path (P : Profile n) (θ : Policy n) (c : Crowd (CType n)) : PricePath n :=
  priceAt θ (salesOf (P.play c))

open Classical in
/-- The units of resource `r` used in the crowd `c` strictly before the position `(s, t)` in the
order (time of purchase, time of arrival). -/
noncomputable def Profile.consumedOut (P : Profile n) (I : Instance n m) (c : Crowd (CType n))
    (s t : ℝ) (r : Fin m) : ℕ :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin c.1 => (P.play c l).1 < s ∨
      ((P.play c l).1 = s ∧ (c.2 l).1 < t)), I.usage r (P.play c l).2

/-- The outcome `(τ, a, p)` of one more customer of type `φ` taking the decision `d` against the
crowd `c` of the others: `d` if the product is still there at his place `(τ, t_φ)` in the order,
else he exits with nothing; `p` is the price on the others' path.

**Formalization Note.** The others' path is the path he faces: a customer is invisible to the
seller until he leaves, so his presence changes no price up to his own exit time. -/
noncomputable def Profile.outcome (P : Profile n) (I : Instance n m) (θ : Policy n) (φ : CType n)
    (d : Decision n) (c : Crowd (CType n)) : ℝ × Option (Fin n) × ℝ :=
  let e := ration (Fits I (P.consumedOut I c d.1 φ.1) d) d
  (e.1, e.2, paid (P.path θ c) e)

/-- `yᵩ`: the outcome of a type `φ` following his rule against the others `c`. -/
noncomputable def Profile.y (P : Profile n) (I : Instance n m) (θ : Policy n) (φ : CType n)
    (c : Crowd (CType n)) : ℝ × Option (Fin n) × ℝ :=
  P.outcome I θ φ (P.σ φ (P.path θ c)) c

/-- `(σ, play)` is an equilibrium of the customers under `θ`.

Chen & Trichakis, SSRN 2959489 (version of May 29, 2018), §2, pp.7–8. Every rule is feasible; the
play of every crowd of types is a play; and each type's rule is a best response, in expected
utility, to the others following the symmetric rule. The others of a customer form a Poisson crowd
again, so the expectation is over `I.law`.

**Formalization Note.** The best response is ex ante, among the rules with integrable payoff, for
every type in `Φ` (including those off the support, as p.9 uses them). It is implied by the
printed best response `E[U | 𝒞_{t_φ}]`, by the tower property. The measurability and integrability
fields say that the expectations `E₋φ` and `Jᵖ` of the paper are defined: the sum over `H_T` in
`Jᵖ` converges absolutely in expectation. `IsEquilibrium` must carry them, because a Bochner integral
of a non-integrable function is `0`. -/
structure IsEquilibrium (I : Instance n m) (θ : Policy n) (P : Profile n) : Prop where
  feasible : ∀ φ, I.IsType φ → FeasibleRule I φ.1 (P.σ φ)
  isPlay : ∀ c : Crowd (CType n), (∀ i, I.IsType (c.2 i)) → IsPlay I θ P.σ c.2 (P.play c)
  best_response : ∀ φ, I.IsType φ → ∀ r : Rule n, FeasibleRule I φ.1 r →
    Integrable (fun c => utility φ (P.outcome I θ φ (r (P.path θ c)) c)) I.law →
    ∫ c, utility φ (P.outcome I θ φ (r (P.path θ c)) c) ∂I.law ≤
      ∫ c, utility φ (P.y I θ φ c) ∂I.law
  meas_time : Measurable fun x : CType n × Crowd (CType n) => (P.y I θ x.1 x.2).1
  meas_alloc : ∀ j, MeasurableSet {x : CType n × Crowd (CType n) | (P.y I θ x.1 x.2).2.1 = some j}
  meas_pay : Measurable fun x : CType n × Crowd (CType n) => (P.y I θ x.1 x.2).2.2
  int_pay : ∀ φ, I.IsType φ → Integrable (fun c => (P.y I θ φ c).2.2) I.law
  int_total : Integrable (fun c => ∑ i, |paid (P.path θ c) (P.play c i)|) I.law

/-- `Jᵖ = E[Σ_{φ ∈ H_T} pᵩ]`: the expected revenue of the policy `θ` when the customers play `P`
(p.8). -/
noncomputable def J (I : Instance n m) (θ : Policy n) (P : Profile n) : ℝ :=
  ∫ c, ∑ i, paid (P.path θ c) (P.play c i) ∂I.law

/-- `J⋆ = sup_{π ∈ Π} Jᵖ` (p.8).

**Formalization Note.** The paper does not prove that an equilibrium exists or is unique
(footnote 2, p.8), so the supremum runs over admissible policies and all their equilibria; a
policy with no equilibrium contributes nothing. -/
noncomputable def Jstar (I : Instance n m) : EReal :=
  ⨆ θ : {θ : Policy n // Admissible I θ}, ⨆ P : {P : Profile n // IsEquilibrium I θ.1 P},
    ((J I θ.1 P.1 : ℝ) : EReal)

end StrategicNRM


