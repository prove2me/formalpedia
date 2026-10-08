-- Prove2me | Definitions.Def_PrivateRelease_NetMechanism_ExpMech
-- name    : PrivateRelease_NetMechanism_ExpMech
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:07:42.102381+00:00
-- url     : https://prove2.me/theorems/3fb99e29-be62-4762-b464-a7f95506c036
-- title:
--   The exponential mechanism and the Net mechanism (Definition 3.1, Algorithm 1)
-- statement:
--   Let $X$ be a data universe, $n$ the input size, $R$ a finite range and $q:X^n\times R\to\mathbb R$ a **quality score**. Its sensitivity is
--   $$
--   GS_q=\max_{r\in R} GS_{q(\cdot,r)},
--   $$
--   the largest global sensitivity of the maps $z\mapsto q(z,r)$.
--
--   1. **Exponential mechanism** (Definition 3.1, McSherry–Talwar). With privacy parameter $\varepsilon$, $M_E(z,q,R)$ outputs $r\in R$ with probability
--   $$
--   \Pr[M_E(z,q,R)=r]=\frac{\exp\!\big(\varepsilon q(z,r)/(2GS_q)\big)}{\sum_{r'\in R}\exp\!\big(\varepsilon q(z,r')/(2GS_q)\big)} .
--   $$
--   2. **Net mechanism** (Algorithm 1). For a class $\mathcal Q$ of queries and a finite set $N\subseteq X^*$ of databases, the quality score is
--   $$
--   q(z,D')=-\max_{Q\in\mathcal Q}|Q(z)-Q(D')| ,
--   $$
--   and $\mathrm{NetMechanism}$ outputs $D'\in N$ by the exponential mechanism $M_E(z,q,N)$. The paper runs it on $N=N_\alpha(C)$, a minimum α-net.
--
--   The Net mechanism is the paper's general-purpose private release algorithm: it outputs a synthetic database that, with high probability, answers every query of the class nearly as the true database does.
--
--   **Formalization Note** The output law is the finite mixture $\sum_{r\in R}p_r\,\delta_r$ of point masses. When $GS_q=0$ the paper's formula is undefined; Lean's convention $x/0=0$ then yields the uniform law on $R$, and the theorems that rely on the paper's formula assume $GS_q>0$. The maximum over $\mathcal Q$ is a real supremum; it is the maximum whenever the family $|Q(z)-Q(D')|$ is bounded, which always holds for counting queries (values in $[0,1]$). The net is an explicit parameter of the mechanism, and theorems quantify over minimum nets because $N_\alpha(C)$ need not be unique.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), pp. 7–8, Definition 3.1 and Algorithm 1

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_Queries

namespace PrivateRelease.NetMechanism

open MeasureTheory

/-- Definition 3.1 (p. 7): the sensitivity `GS_q` of a quality score
`q : Xⁿ × R → ℝ` in its database argument, maximised over the outputs `r` of the finite range `R`:
`GS_q = max_{r ∈ R} GS_{q(·, r)}` (`0` for an empty range). -/
noncomputable def scoreSens {X O : Type} {n : ℕ} (R : Finset O) (q : (Fin n → X) → O → ℝ) : ℝ :=
  ⨆ r : R, GS fun z => q z r.1

/-- Definition 3.1 (p. 7): the exponential mechanism `M_E(D, q, R)` of McSherry and Talwar, with
privacy parameter `ε`. On the input `z` it outputs `r ∈ R` with probability proportional to
`exp(ε q(z, r) / (2 GS_q))`: its law is the finite mixture of point masses
`Σ_{r ∈ R} (w(r) / Σ_{r′ ∈ R} w(r′)) δ_r` with `w(r) = exp(ε q(z, r) / (2 GS_q))`.
When `GS_q = 0` the paper's formula is undefined; Lean's `x / 0 = 0` then gives the uniform law on
`R`, and the theorems that need the paper's formula assume `0 < GS_q`. -/
noncomputable def expMech {X O : Type} [MeasurableSpace O] {n : ℕ} (R : Finset O)
    (q : (Fin n → X) → O → ℝ) (ε : ℝ) (z : Fin n → X) : Measure O :=
  ∑ r ∈ R, ENNReal.ofReal (Real.exp (ε * q z r / (2 * scoreSens R q)) /
      ∑ r' ∈ R, Real.exp (ε * q z r' / (2 * scoreSens R q))) • Measure.dirac r

/-- Algorithm 1 (p. 8): the quality score of the Net mechanism,
`q(D, D′) = − max_{Q ∈ QC} |Q(D) − Q(D′)|`, for the input `z` (as the database `D`) and a
candidate output `D′ ∈ X*`. The maximum is the real supremum over the class, which is the maximum
whenever the family is bounded (always, for counting queries, whose values lie in `[0, 1]`). -/
noncomputable def netScore {X : Type} {n : ℕ} (QC : Set (Multiset X → ℝ)) (z : Fin n → X)
    (D' : Database X) : ℝ :=
  -⨆ Q : QC, |Q.1 (inputDB z) - Q.1 D'.1|

/-- The sensitivity `GS_q` of the Net mechanism's quality score over the range `R = N`. -/
noncomputable def netSens {X : Type} (n : ℕ) (QC : Set (Multiset X → ℝ))
    (N : Finset (Database X)) : ℝ :=
  scoreSens N (netScore (n := n) QC)

/-- Algorithm 1 (p. 8): `NetMechanism(D, C, ε, α)`. With `R ← N` (the paper takes `N = N_α(C)`,
an α-net of minimum cardinality) and the quality score `netScore`, sample and output `D′ ∈ R` with
the exponential mechanism `M_E(D, q, R)`. The net is a parameter; the theorems quantify over
minimum α-nets. -/
noncomputable def netMech {X : Type} {n : ℕ} (QC : Set (Multiset X → ℝ)) (ε : ℝ)
    (N : Finset (Database X)) (z : Fin n → X) : Measure (Database X) :=
  expMech N (netScore QC) ε z

end PrivateRelease.NetMechanism


