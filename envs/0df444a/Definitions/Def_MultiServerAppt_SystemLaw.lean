-- Prove2me | Definitions.Def_MultiServerAppt_SystemLaw
-- name    : MultiServerAppt_SystemLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:04:19.024986+00:00
-- url     : https://prove2.me/theorems/3be143bb-fd94-41be-b7f2-a51a2b5d4e20
-- title:
--   The system law after client $s+i$, Eqs. (7), (11), (12)
-- statement:
--   This predicate states that the system after client $s+i$ is described by $\mathrm{PH}(\alpha_{s+i},S_{s+i})$. For every $u\ge 0$:
--
--   1. $\mathbb P(Y_{s+i}(u)=0)=p_0^{(s+i)}(u)$;
--   2. for $1\le j\le s+i$ and every bounded measurable $g$,
--
--   $$\mathbb E\Big[\mathbf 1\{Y_{s+i}(u)=j\}\prod_{d\ \text{in service}}g\big(\mathrm{dep}_d-(t_{s+i}+u)\big)\Big]=\sum_{m}p^{(s+i)}_{j,m}(u)\prod_{\ell}\hat g(m_\ell).$$
--
--   Jointly with $\{Y_{s+i}(u)=j\}$, the residual services of the clients in service are independent with laws $\mathrm{PH}(e_{m_\ell},S)$, where $(j,m)$ has probability $p^{(s+i)}_{j,m}(u)$.
--
--   **Formalization Note** The model (6) contains service times and no phase process, and the page leaves open which client sits in slot $\ell$. This is the slot-free and phase-free content of $p_{j,(m_1,\dots,m_\xi)}(t)=\mathbb P[(Y,Z)=(j,(m_1,\dots,m_\xi))]$: it determines the law of the multiset of phases, and $g\equiv 1$ gives the sentence of p.11 that $p_j\mathbf 1$ is the probability that $j$ clients remain.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, §4.1, Eqs. (7), (11), (12), pp.11-12

import Mathlib
import Definitions.Def_MultiServerAppt_p0
import Definitions.Def_MultiServerAppt_clientCount
import Definitions.Def_MultiServerAppt_phaseProd
import Definitions.Def_MultiServerAppt_ghat
import Definitions.Def_MultiServerAppt_Y
import Definitions.Def_MultiServerAppt_inService

open MeasureTheory

namespace MultiServerAppt

/-- The system law after client `s + i`, the content of Eqs. (7), (11), (12). For all `u ≥ 0`, the
system is empty with probability `p_0^(s+i)(u)`, and for `1 ≤ j ≤ s + i` and every bounded measurable
`g`, jointly with `{Y_{s+i}(u) = j}`, the residual services of the clients in service are independent
with laws `PH(e_{m_ℓ}, S)`, where `(j, m)` has probability `p_{j,m}^(s+i)(u)`. Kuiper–Lee, Appointment
Scheduling for Multiple Servers, SSRN 3975471, §4.1, Eqs. (7), (11), (12), pp.11-12.

**Formalization Note** The model (6) has service times and no phase process, and the page leaves open
which client sits in slot `ℓ` ("without loss of generality", p.11). This is the slot-free and
phase-free form of `p_{j,(m₁,…,m_ξ)}(t) = P[(Y, Z) = (j, (m₁,…,m_ξ))]`: it determines the law of the
multiset of phases, and `g ≡ 1` gives the sentence of p.11 that `p_j 𝟙` is the probability that `j`
clients remain. -/
def SystemLaw {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : ℕ) (α : ι → ℝ) (S : Matrix ι ι ℝ) (x : ℕ → ℝ) (B : ℕ → Ω → ℝ)
    (i : ℕ) : Prop :=
  ∀ u : ℝ, 0 ≤ u →
    P.real {ω | Y s x (fun c => B c ω) (s + i) u = 0} = p0 α S s x i u ∧
    ∀ j ∈ Finset.Icc 1 (s + i), ∀ g : ℝ → ℝ, Measurable g → (∃ C, ∀ r, |g r| ≤ C) →
      ∫ ω, (if Y s x (fun c => B c ω) (s + i) u = j then
          ∏ d ∈ inService s x (fun c => B c ω) (s + i) u,
            g (dep s x (fun c => B c ω) d - (arr s x (s + i) + u))
        else 0) ∂P =
      ∑ p ∈ Finset.univ.filter (fun p : State ι s i => clientCount p = j),
        pVec α S s x i u p * phaseProd (ghat S g) p

end MultiServerAppt


