-- Prove2me | Definitions.Def_StrategicNRM_Mechanism
-- name    : StrategicNRM_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:38.404976+00:00
-- url     : https://prove2.me/theorems/5bd20636-b216-4407-b39f-041a74df8377
-- title:
--   The mechanism design problem (5), corrected, and $J^{\mathrm{md}}$
-- statement:
--   A **mechanism** gives a customer reporting $\phi$, when the other reports are $c$, an outcome $y_\phi(c)=(\tau,a,p)$. It is **feasible** if
--
--   1. (causality) $\tau\in[t_\phi,T]$, and the outcome depends on $c$ only through the reports that arrive by $\tau$;
--   2. (substitutability) at most one product is allocated;
--   3. (limited inventory) $\sum_{\phi\in\mathcal H_T}\sum_j A_{ij}a^j_\phi\le x_0^i$ almost surely, for every $i$.
--
--   $J^{\mathrm{md}}$ is the supremum of $V(y)=E[\sum_{\phi\in\mathcal H_T}p_\phi]$ over feasible mechanisms subject to
--
--   $$
--   \begin{aligned}
--   &E_{-\phi}[U(\phi,y_\phi)]\ge E_{-\phi}[U(\phi,y_{\hat\phi})]\quad\forall\phi,\hat\phi:\ t_{\hat\phi}=t_\phi, &&\text{(IC)}\\
--   &U(\phi,y_\phi)\ge 0\ \text{ a.s.}\quad\forall\phi, &&\text{(IR)}\\
--   &E_{-\phi}[U(\phi,y_\phi)(1-a^j_\phi)]\le E_{-\phi}[U(\phi_{j,0},y_{\phi_{j,0}})]\quad\forall\phi,j.
--   \end{aligned}
--   $$
--
--   This relaxation of the game is the bridge between the pricing game and a one-dimensional problem.
--
--   **Formalization Note** The problem differs from the printed (5) in three ways, each of which enlarges the feasible set. (a) The last line replaces $U(\phi,y_\phi)=U(\phi_{j,0},y_{\phi_{j,0}})$ whenever $a^j_\phi=0$, which fails for the mechanism of a policy (see Lemma 1(ii)); given (IR) the printed line implies the corrected one. (b) (IC) is for $t_{\hat\phi}=t_\phi$, not $t_{\hat\phi}\in[t_\phi,T]$: under rationing by arrival a later report does not carry a later priority for the true customer, and only reports of the valuations are ever used. (c) Constraint 4 of p.12, $p_\phi\ge 0$, is dropped, because $\Pi$ has no sign condition and no step uses it. Causality is written on crowds of types, with the reports listed in index order, because the index breaks ties. Measurability and integrability fields say that the expectations are defined.
-- source:
--   Chen & Trichakis, On Revenue Management with Strategic Customers Choosing When and What to Buy, SSRN 2959489 (version of May 29, 2018), §3.2.1, pp.11–12, problem (5)

import Mathlib
import Definitions.Def_StrategicNRM_Instance

open MeasureTheory
open scoped ENNReal

namespace StrategicNRM

variable {n m : ℕ}

/-- The class `𝒴` of feasible mechanisms, pp.11–12. A mechanism gives `y φ c = (τ, a, p)` to a
customer reporting `φ` when the other reports are `c`.

1. Causality: `τ ∈ [t_φ, T]`, and `y φ` depends on `c` only through the reports with arrival at
   most `τ`, which makes `τ` a stopping time and `(a, p)` measurable at `τ`.
2. Substitutability: built into `Option`.
3. Limited inventory (4), almost surely along the crowd.

**Formalization Note (correction).** Constraint 4 of p.12, `pᵩ ≥ 0`, is dropped. `Π` does not
require non-negative prices (p.6 has `πₜ ∈ ℝⁿ`), so the mechanism of a policy may break it, and no
step uses it. The fields `meas_*` and `int_*` say that the expectations of problem (5) are
defined. Causality is asked of crowds of types only, since that is where a play is defined. -/
structure IsFeasibleMechanism (I : Instance n m)
    (y : CType n → Crowd (CType n) → ℝ × Option (Fin n) × ℝ) : Prop where
  meas_time : Measurable fun x : CType n × Crowd (CType n) => (y x.1 x.2).1
  meas_alloc : ∀ j, MeasurableSet {x : CType n × Crowd (CType n) | (y x.1 x.2).2.1 = some j}
  meas_pay : Measurable fun x : CType n × Crowd (CType n) => (y x.1 x.2).2.2
  time_mem : ∀ φ, I.IsType φ → ∀ c, (y φ c).1 ∈ Set.Icc φ.1 I.T
  causal : ∀ φ, I.IsType φ → ∀ c c' : Crowd (CType n), (∀ i, I.IsType (c.2 i)) →
    (∀ i, I.IsType (c'.2 i)) →
    c.upTo Prod.fst (y φ c).1 = c'.upTo Prod.fst (y φ c).1 → y φ c' = y φ c
  inventory : ∀ᵐ c ∂I.law, ∀ r, ∑ i, I.usage r (y (c.2 i) (c.others i)).2.1 ≤ I.x0 r
  int_pay : ∀ φ, I.IsType φ → Integrable (fun c => (y φ c).2.2) I.law
  int_total : Integrable (fun c => ∑ i, |(y (c.2 i) (c.others i)).2.2|) I.law

/-- The constraints of problem (5), p.12, with the corrections of Lemma 2.

* (IC) `E₋φ[U(φ, y_φ)] ≥ E₋φ[U(φ, y_φ̂)]`, for `t_φ̂ = t_φ`.
* (IR) `U(φ, y_φ) ≥ 0` almost surely.
* The last line, corrected: `E₋φ[U(φ, y_φ)(1 − aʲ_φ)] ≤ E₋φ[U(φ_{j,0}, y_{φ_{j,0}})]`.

**Formalization Note (correction).** Printed (IC) is for `t_φ̂ ∈ [t_φ, T]`, and the printed last
line is `U(φ, y_φ) = U(φ_{j,0}, y_{φ_{j,0}})` whenever `aʲ_φ = 0`. Both are relaxed: under rationing
by arrival a later report does not carry a later priority for the true customer, and no step uses
such a report; and the printed last line fails for the mechanism of a policy (see `lemma_1_ii`),
while its corrected form is implied by the printed one given (IR). -/
structure IsDesignFeasible (I : Instance n m)
    (y : CType n → Crowd (CType n) → ℝ × Option (Fin n) × ℝ) : Prop extends
    IsFeasibleMechanism I y where
  ic : ∀ φ φ', I.IsType φ → I.IsType φ' → φ'.1 = φ.1 →
    ∫ c, utility φ (y φ' c) ∂I.law ≤ ∫ c, utility φ (y φ c) ∂I.law
  ir : ∀ φ, I.IsType φ → ∀ᵐ c ∂I.law, 0 ≤ utility φ (y φ c)
  zero : ∀ φ j, I.IsType φ →
    ∫ c, utility φ (y φ c) * (1 - alloc (y φ c).2.1 j) ∂I.law ≤
      ∫ c, utility (withVal φ j 0) (y (withVal φ j 0) c) ∂I.law

/-- `V(y) = E[Σ_{φ ∈ H_T} pᵩ]` (p.12). -/
noncomputable def V (I : Instance n m) (y : CType n → Crowd (CType n) → ℝ × Option (Fin n) × ℝ) :
    ℝ :=
  ∫ c, ∑ i, (y (c.2 i) (c.others i)).2.2 ∂I.law

/-- `Jᵐᵈ`, the optimal value of the mechanism design problem (5), p.12, corrected. -/
noncomputable def Jmd (I : Instance n m) : EReal :=
  ⨆ y : {y // IsDesignFeasible I y}, ((V I y.1 : ℝ) : EReal)

end StrategicNRM


