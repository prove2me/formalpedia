-- Prove2me | Definitions.Def_HeymanStidham_HLG_Supplement_Stationary
-- name    : HeymanStidham_HLG_Supplement_Stationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:10:50.068796+00:00
-- url     : https://prove2.me/theorems/e6bbbf8d-9e5f-4210-b842-c8cef8fb1c89
-- title:
--   (vi)–(vii), p. 988 — stationarity, metric transitivity and finite expectations
-- statement:
--   Let $X_1,X_2,\ldots$ be measurable real random variables on $(\Omega,\mathcal F,P)$ and let $Q$ be their joint law on $\mathbb R^{\mathbb N}$. Write $S(x)_n=x_{n+1}$ for the left shift. Strict stationarity means that every finite-dimensional distribution is unchanged by a shift, equivalently
--
--   $$Q\circ S^{-1}=Q.$$
--
--   Condition (vii) additionally requires $\mathbb E[X_n]$ to exist as a finite real expectation for every $n$; this is represented by integrability. Applied to the customer totals, these are exactly the two requirements on p. 988. Neither ergodicity nor independence is required. For (vi), the local predicate IsStationaryErgodic additionally requires ergodicity of the sequence law under the left shift: invariant measurable events have probability zero or one. Only the interarrivals require this property.
--
--   **Formalization Note** The measurable path law uses the product sigma algebra. Lean index zero represents the first random variable. No mixing, boundedness or second moment is included. The published GenEmpLik stationary-ergodic item is not reused: its cited source page describes mixing, which is stronger than Heyman’s metric transitivity.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), DOI 10.1287/opre.28.4.983, p. 988, (vi)–(vii); PDF p. 6

import Mathlib

namespace HeymanStidham.HLG.Supplement

open MeasureTheory

/-- The left shift of the one-sided sequence law used in (vi) and (vii). -/
def seqShift (x : ℕ → ℝ) : ℕ → ℝ := fun n => x (n + 1)

/-- Condition (vi), p. 988: a measurable strictly stationary and metrically
transitive sequence. Ergodicity is imposed on its path law, not on the whole
queue probability space, and does not impose mixing. -/
def IsStationaryErgodic {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) : Prop :=
  (∀ n, Measurable (X n)) ∧ Ergodic seqShift (P.map (fun ω n => X n ω))

/-- Strict stationarity, (vii), p. 988: the measurable real sequence has a
shift-invariant path law. Unlike (vi), ergodicity is not required. -/
def IsStationary {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) : Prop :=
  (∀ n, Measurable (X n)) ∧
    MeasurePreserving seqShift (P.map (fun ω n => X n ω))
      (P.map (fun ω n => X n ω))

/-- The entire condition (vii): stationarity and existence of finite expectations. -/
def StationaryIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsStationary X P ∧ ∀ n, Integrable (X n) P

end HeymanStidham.HLG.Supplement


