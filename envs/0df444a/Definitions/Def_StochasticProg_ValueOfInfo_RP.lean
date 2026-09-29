-- Prove2me | Definitions.Def_StochasticProg_ValueOfInfo_RP
-- name    : StochasticProg_ValueOfInfo_RP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T04:50:32.558935+00:00
-- url     : https://prove2.me/theorems/d7ac81cd-e500-4895-871c-7e8f94121dad
-- title:
--   The recourse, wait-and-see, EV, EVPI, EEV, VSS, EVRS and pairs-subproblem optimal values
-- statement:
--   This bundle defines the ten optimal values of Birge & Louveaux Chapter 4, each as the
--   optimal value of a variant of the two-stage recourse problem of an `Instance` (see the
--   companion `Instance` definition), restricted or evaluated differently:
--
--   - $RP = \min_{x\in K_1}\mathbb E_\xi\,z(x,\xi)$, the recourse problem's optimal (here-and-now)
--     value (eq. 1.3, p. 164).
--   - $WS = \mathbb E_\xi\big[\min_{x\in K_1} z(x,\xi)\big]$, the wait-and-see value (eq. 1.2, p. 164).
--   - $EV = \min_{x\in K_1} z(x,\bar\xi)$, the expected value problem's optimal value at the mean
--     scenario $\bar\xi$ (eq. 2.1, p. 165).
--   - $EVPI = RP - WS$, the expected value of perfect information (eq. 1.4, p. 164).
--   - $EEV = \mathbb E_\xi\,z(\bar x(\bar\xi),\xi)$, given `xBar`, an optimal solution of the
--     $EV$ problem, i.e. $\bar x(\bar\xi)$ (eq. 2.2, p. 165).
--   - $VSS = EEV - RP$, the value of the stochastic solution relative to the same `xBar`
--     (eq. 2.3, p. 165).
--   - $EVRS = \mathbb E_\xi\,z(\bar x^r,\xi)$, given `xBarR`, an optimal solution to
--     $\min_{x\in K_1} z(x,\xi^r)$ for a reference scenario $\xi^r$ that need not be one of the
--     $K$ possible scenarios (p. 173).
--   - `VSSRef` $= EVRS - RP$, the reference-scenario generalization of $VSS$ (p. 173): the book
--     reuses the symbol "VSS" for both this and the mean-scenario `VSS` above, so this bundle
--     keeps them as two distinct definitions.
--   - The reference scenario's own probability $p_r = \Pr(\xi=\xi^r) = \sum_{k:\,\xi^k=\xi^r} p_k$
--     (`refProb`, p. 172), computed from the instance itself rather than supplied separately.
--   - The **pairs subproblem** optimal value of $\xi^r$ (probability $p_r$) and a scenario
--     $\xi^k$: `pairsValue` $= \min_{x\in K_1}\big[p_r\,z(x,\xi^r) + (1-p_r)\,z(x,\xi^k)\big]$
--     (p. 172).
--   - $SPEV = (1-p_r)^{-1}\sum_{k:\,\xi^k\ne\xi^r} p_k\cdot\mathrm{pairsValue}(\xi^r,\xi^k)$, the
--     sum of pairs expected values, summed over the scenarios *other than* the reference scenario
--     itself (pp. 172-173), so that $\sum_{k:\,\xi^k\ne\xi^r}p_k = 1-p_r$ as the book's proof of
--     Proposition 7 uses.
--   - $EPEV = \min\big(\min_{k=1,\dots,K}\mathbb E_\xi\,z(\bar x^k,\xi),\ \mathbb E_\xi\,z(\bar
--     x^r,\xi)\big)$, given `xBarK k`, an optimal solution of the pairs subproblem of
--     $\xi^r,\xi^k$ for each $k$, and `xBarR` as above (p. 173).
--
--   These eleven values are the objects related by this mission's four milestone propositions and
--   its goal theorem (Chapter 4, Theorem 9).
--
--   **Formalization Note** $EEV$, the mean-scenario $VSS$, $EVRS$, `VSSRef` and $EPEV$ each take
--   an explicit witness first-stage solution (`xBar`, `xBarR`, or `xBarK`) as an argument rather
--   than an internally chosen one, because the book only ever specifies these as "*an* optimal
--   solution" — their numeric value genuinely depends on which optimal solution is chosen when
--   the underlying LP has multiple optima (the book's own Example 2 in §4.4 exhibits this). The
--   theorems that use these definitions state the witness's optimality as an explicit hypothesis.
--   Every addition and subtraction above (inside `expect`, `WS`, `EVPI`, `VSS`, `VSSRef`,
--   `pairsValue` and `SPEV`) uses the book's own convention (p. 164) that $+\infty$
--   (infeasibility) dominates, i.e. $(+\infty)+(-\infty)=+\infty$, via the `badd`/`bsub`/`bsum`
--   operations defined alongside `Instance` — not Mathlib's `EReal` addition, whose
--   $\top+\bot=\bot$ would make $VSS\ge 0$ (Proposition 5(a)) and the goal's own leftmost
--   inequality false whenever a witness solution is infeasible in some positive-probability
--   scenario (the book's own Example 2, pp. 174-175, is such a case).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, pp. 164-165, 172-173, Chapter 4

import Mathlib
import Definitions.Def_StochasticProg_ValueOfInfo_Instance

namespace StochasticProg.ValueOfInfo

variable {n1 d K : ℕ}

/-- The recourse problem's optimal value (the here-and-now solution), eq. (1.3),
p. 164: `RP = min_{x ∈ K1} E_ξ z(x,ξ)`. -/
noncomputable def RP (I : Instance n1 d K) : EReal :=
  ⨅ x ∈ I.K1, expect I x

/-- The wait-and-see solution's expected value, eq. (1.2), p. 164:
`WS = E_ξ [min_{x ∈ K1} z(x,ξ)]`, under the book's `+∞` convention. -/
noncomputable def WS (I : Instance n1 d K) : EReal :=
  bsum (fun k => (I.p k : EReal) * (⨅ x ∈ I.K1, I.z x (I.xi k)))

/-- The expected value problem's optimal value, eq. (2.1), p. 165:
`EV = min_{x ∈ K1} z(x, ξ̄)`. -/
noncomputable def EV (I : Instance n1 d K) : EReal :=
  ⨅ x ∈ I.K1, I.z x (xiBar I)

/-- The expected value of perfect information, eq. (1.4), p. 164: `EVPI = RP − WS`,
under the book's `+∞` convention. -/
noncomputable def EVPI (I : Instance n1 d K) : EReal :=
  bsub (RP I) (WS I)

/-- The expected result of using the EV solution `x̄(ξ̄)`, eq. (2.2), p. 165:
`EEV = E_ξ z(x̄(ξ̄),ξ)`, relative to `xBar`, an optimal solution of the expected
value problem `EV`. -/
noncomputable def EEV (I : Instance n1 d K) (xBar : Fin n1 → ℝ) : EReal :=
  expect I xBar

/-- The value of the stochastic solution, eq. (2.3), p. 165: `VSS = EEV − RP`,
relative to the EV-solution `xBar` used to compute `EEV`, under the book's `+∞`
convention. -/
noncomputable def VSS (I : Instance n1 d K) (xBar : Fin n1 → ℝ) : EReal :=
  bsub (EEV I xBar) (RP I)

/-- The expected value of the reference-scenario solution `x̄^r`, p. 173:
`EVRS = E_ξ z(x̄^r,ξ)`, relative to `xBarR`, an optimal solution to
`min_{x ∈ K1} z(x,ξ^r)` for a reference scenario `ξ^r` (not necessarily one of
the `K` possible scenarios). -/
noncomputable def EVRS (I : Instance n1 d K) (xBarR : Fin n1 → ℝ) : EReal :=
  expect I xBarR

/-- The value of the stochastic solution, generalized to a reference scenario
`ξ^r`, p. 173: `VSS = EVRS − RP`, under the book's `+∞` convention. -/
noncomputable def VSSRef (I : Instance n1 d K) (xBarR : Fin n1 → ℝ) : EReal :=
  bsub (EVRS I xBarR) (RP I)

/-- The optimal value of the pairs subproblem of the reference scenario `ξ^r`
(probability `pᵣ = refProb I xir`, p. 172) and scenario `ξ^k`:
`min_{x ∈ K1} [pᵣ · z(x,ξ^r) + (1 − pᵣ) · z(x,ξ^k)]`, under the book's `+∞`
convention. -/
noncomputable def pairsValue (I : Instance n1 d K) (xir : Fin d → ℝ) (k : Fin K) :
    EReal :=
  ⨅ x ∈ I.K1, badd ((refProb I xir : EReal) * I.z x xir)
    (((1 - refProb I xir : ℝ) : EReal) * I.z x (I.xi k))

/-- The sum of pairs expected values, p. 172-173, summed over the scenarios other
than the reference scenario itself (`ξ_k ≠ ξ^r`):
`SPEV = (1 − pᵣ)⁻¹ ∑_{k : ξ_k ≠ ξ^r} p_k · (optimal value of the pairs subproblem
of ξ^r,ξ^k)`. -/
noncomputable def SPEV (I : Instance n1 d K) (xir : Fin d → ℝ) : EReal :=
  ((1 - refProb I xir : ℝ) : EReal)⁻¹ *
    bsum (fun k => if I.xi k = xir then 0 else (I.p k : EReal) * pairsValue I xir k)

/-- The expectation of pairs expected value, p. 173:
`EPEV = min_{k ∈ {1,…,K} ∪ {r}} E_ξ z(x̄^k,ξ)`, relative to `xBarK k`, an
optimal solution to the pairs subproblem of `ξ^r,ξ^k` for each `k`, and
`xBarR`, an optimal solution to `min_{x ∈ K1} z(x,ξ^r)`. -/
noncomputable def EPEV (I : Instance n1 d K) (xBarK : Fin K → (Fin n1 → ℝ))
    (xBarR : Fin n1 → ℝ) : EReal :=
  min (⨅ k, expect I (xBarK k)) (expect I xBarR)

end StochasticProg.ValueOfInfo


