-- Prove2me | Definitions.Def_MetricMinTest_Supplement_IsCertCover
-- name    : MetricMinTest_Supplement_IsCertCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:36:00.013978+00:00
-- url     : https://prove2.me/theorems/8fdf6e6d-6428-4040-89d9-ba3602928959
-- title:
--   Fractional certificate cover (Definition K.1)
-- statement:
--   In a finite certificate system (an instance class with disjoint subsets $\mathcal P^+,\mathcal P^-$, a finite certificate family $\mathcal C$, certificate means $m_c(P)$ and known thresholds $a_c$), let $N(P)=\{c: m_c(P)\le a_c\}$ be the certificates whose null holds at $P$. A **fractional certificate cover** is $y\ge0$ with
--   $$\sum_{c\in N(P)}y_c\ge1\qquad\text{for every }P\in\mathcal P^-.$$
--
--   **Formalization Note** The instance class is a type $X$ and $x\mapsto$ the laws of the certificates (an instance indexed by $\mathcal C$).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Definition K.1, p.32

import Mathlib
import Definitions.Def_MetricMinTest_Instance_mean

namespace MetricMinTest.Supplement

/-- **Fractional certificate cover** (Definition K.1). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Definition K.1, p.32: "Write
N(P) = {c : m_c(P) ≤ a_c}. A fractional certificate cover satisfies y ≥ 0 and
∑_{c∈N(P)} y_c ≥ 1 for every P ∈ P−."

**Formalization Note.** The instance class is a type `X`; `inst x` gives the laws of the
certificates (an `Instance` indexed by the certificate family `C`), `m_c(P)` is its mean. -/
def IsCertCover {C X : Type} [Fintype C] (inst : X → Instance C) (Pneg : Set X) (a : C → ℝ)
    (y : C → ℝ) : Prop :=
  (∀ c, 0 ≤ y c) ∧
  ∀ x ∈ Pneg, 1 ≤ ∑ c ∈ Finset.univ.filter (fun c => (inst x).mean c ≤ a c), y c

end MetricMinTest.Supplement


