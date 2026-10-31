-- Prove2me | Definitions.Def_NonlinearPriority_IsSteadyStateLaw
-- name    : NonlinearPriority_IsSteadyStateLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:36.676824+00:00
-- url     : https://prove2.me/theorems/607fcc06-278b-4991-bc74-0e8d07a44595
-- title:
--   Steady-state waiting-time law $W^{\gamma}_i$ as a limit in distribution
-- statement:
--   Let $V^{\gamma,x_0}_{i,k}$ be the waiting time of the $k$th arriving type-$i$ customer under policy $\gamma$ from the initial state $x_0$. A probability measure $w$ on $\mathbb R$ is the **steady-state waiting-time law** of type $i$ under $\gamma$ if, for every initial state $x_0$,
--   $$V^{\gamma,x_0}_{i,k}\xrightarrow{d} w\qquad (k\to\infty).$$
--   Expectations of the steady-state waiting time are integrals against this law: $\mathbb E[g(W^\gamma_i)]=\int g\,dw$.
--
--   **Formalization Note** The paper names $W^\gamma_i$ ("the steady-state waiting time of a type i customer under policy $\pi$") without a definition; its proof of Lemma A.1(b) uses it as this limit in distribution. Convergence in distribution is Mathlib's `TendstoInDistribution`.
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, p.4 (PDF 5); proof of Lemma A.1(b), p.16 (PDF 17); Table A.2, p.17 (PDF 18)

import Mathlib
import Definitions.Def_NonlinearPriority_Inputs
import Definitions.Def_NonlinearPriority_waitingTime

open MeasureTheory Filter

namespace NonlinearPriority

variable {K : ℕ} {P : Params K} {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}

/-- The realization of the arrival stream at the outcome `ω`: interarrival times `A n ω`, types
`Y n ω`, and the service time `Sv (Y n ω) n ω` of arrival `n`. -/
def Inputs.realize (X : Inputs P Ω Pr) (ω : Ω) : Realization K where
  a n := X.A n ω
  y n := X.Y n ω
  sv n := X.Sv (X.Y n ω) n ω

/-- `V^{γ,x0}_{i,k}`: the waiting time of the `k`th arriving type-`i` customer (`k = 0, 1, …`)
under the policy `ord` and initial state `x0` (p. 4; Table A.2, p. 17). The `k`th type-`i` arrival
is `Nat.nth (fun n => Y n ω = i) k`. -/
noncomputable def typeWait (X : Inputs P Ω Pr) (x0 : InitState K) (ord : Fin K → ℕ) (i : Fin K)
    (k : ℕ) (ω : Ω) : ℝ :=
  waitingTime x0 (X.realize ω) ord (Nat.nth (fun n => X.Y n ω = i) k)

/-- **`w` is the steady-state waiting-time law of type `i` under the policy `ord`**
(`W^γ_i`, p. 4, PDF 5; used as a limit in distribution in the proof of Lemma A.1(b), p. 16, PDF 17:
"as n → ∞, V^{γ,x0}_{i,n} →d W^γ_i"). Ouyang, Argon and Ziya, Management Science (2021),
doi:10.1287/mnsc.2020.3952.

For every initial state `x0`, the waiting times `V^{ord,x0}_{i,k}` of the successive type-`i`
arrivals converge in distribution to `w` as `k → ∞`. Expectations `E[g(W^γ_i)]` are
`∫ g dw`.

**Formalization Note.** The paper defines `W^γ_i` only by name ("the steady-state waiting time of
a type i customer under policy π"); its proofs use it as this limit law, from every initial state.
Convergence in distribution is Mathlib's `TendstoInDistribution` (weak convergence of the laws,
with each `V` a.e.-measurable), with limit the identity on `(ℝ, w)`. -/
def IsSteadyStateLaw [IsProbabilityMeasure Pr] (X : Inputs P Ω Pr) (ord : Fin K → ℕ) (i : Fin K)
    (w : ProbabilityMeasure ℝ) : Prop :=
  ∀ x0 : InitState K,
    TendstoInDistribution (fun k ω => typeWait X x0 ord i k ω) atTop id (fun _ => Pr)
      (w : Measure ℝ)

end NonlinearPriority


