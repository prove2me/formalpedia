-- Prove2me | Definitions.Def_HeymanStidham_HLG_Supplement_Lift
-- name    : HeymanStidham_HLG_Supplement_Lift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:13:09.031813+00:00
-- url     : https://prove2.me/theorems/358ea71f-5817-4edd-b43d-debd61a2f35d
-- title:
--   §1, pp. 984–986 — interarrivals and the inherited pathwise domain
-- statement:
--   On each sample path let $0\le t_1\le t_2\le\cdots$ be the arrival epochs, $f_n$ the customer functions on nonnegative time, and $s_n\ge0$ their support spans. All pathwise objects $g_n,h,N,\lambda,G,H,f_n^\pm$ are the published definitions from the base mission. Define the interarrivals by
--
--   $$\tau_1=t_1,\qquad \tau_{n+1}=t_{n+1}-t_n.$$
--
--   The inherited domain consists of (i) $f_n(u)=0$ outside $[t_n,t_n+s_n]$ for $u\ge0$, (ii) $s_n/n\to0$, integrability of each $f_n$ on $[0,\infty)$, and existence of a positive finite pathwise arrival rate. It also requires either the nonnegative case of Theorem 1 (nonnegative customer functions and a finite customer average) or the signed case of Theorem 2 (finite customer averages for the integrated positive and negative parts separately). These two alternatives are retained explicitly; no time-average existence or deterministic arrival rate is assumed.
--
--   This supplies the common domain to which Theorems 4 and 5 add their stochastic assumptions.
--
--   **Formalization Note** Lean customer $n$ is the paper's $n+1$. Values of $f_n$ at negative time are unconstrained. The published time-average predicate includes local interval integrability. Positive finite pathwise arrival rates exclude the published arrival-count definition's infinite-set default. The printed (iv) is read as genuine integrability, consistently with the base mission.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), DOI 10.1287/opre.28.4.983, pp. 984–986, §1, ASSUMPTION (i)–(ii), THEOREMS 1–2; PDF pp. 2–4

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

namespace HeymanStidham.HLG.Supplement

open MeasureTheory

/-- Interarrivals of p. 984, with Lean customer n representing paper customer n+1. -/
def interarrival (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => t 0
  | n + 1 => t (n + 1) - t n

/-- The domain inherited from Theorem 1 OR Theorem 2. Existence of a positive
finite pathwise arrival rate and finite customer averages is retained literally:
the extra assumptions of Theorems 4 and 5 are added to these hypotheses.
No time-average existence or common arrival rate is assumed. -/
def InheritedPath (t : ℕ → ℝ) (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) : Prop :=
  Monotone t ∧ 0 ≤ t 0 ∧ CondI t f s ∧ CondII s ∧
  (∀ n, IntegrableOn (f n) (Set.Ici 0)) ∧
  (∃ l : ℝ, 0 < l ∧ IsArrivalRate t l) ∧
  (((∀ n τ, 0 ≤ τ → 0 ≤ f n τ) ∧
      ∃ G : ℝ, IsCustomerAverage (custTotal f) G) ∨
    ∃ Gp Gm : ℝ,
      IsCustomerAverage (custTotal (posPartFn f)) Gp ∧
      IsCustomerAverage (custTotal (negPartFn f)) Gm)

end HeymanStidham.HLG.Supplement


