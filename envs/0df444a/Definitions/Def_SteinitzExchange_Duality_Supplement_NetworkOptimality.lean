-- Prove2me | Definitions.Def_SteinitzExchange_Duality_Supplement_NetworkOptimality
-- name    : SteinitzExchange_Duality_Supplement_NetworkOptimality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:27:50.595834+00:00
-- url     : https://prove2.me/theorems/77733e73-4408-4d51-9424-5d7fd4097e7b
-- title:
--   Problem P and potential certificate (7.8)–(7.11)
-- statement:
--   For the finite network and capacities of (7.1)–(7.4), additionally impose $(\partial\varphi)^-\in B^-$, where $B^-$ is a finite exit domain. Problem P maximizes
--   $$F(\varphi)=\langle w,\varphi\rangle_A+\omega^+((\partial\varphi)^+)+\omega^-((\partial\varphi)^-).$$
--   `IsOptimalFlow` compares this objective with every integral feasible flow. For a real vertex potential $q$, put
--   $$w_q(a)=w(a)-q(\operatorname{tail}a)+q(\operatorname{head}a).$$
--   `PotentialCertificate` asserts all three conditions of Theorem 7.6: a negative reduced weight forces the lower capacity, a positive reduced weight forces the upper capacity, and the entrance and exit boundaries maximize $\omega^+[q^+]$ and $\omega^-[q^-]$ on their respective domains. Both boundary perturbations use a plus sign. The two domains and the current flow are explicit inputs; feasibility is supplied by the theorem's hypotheses.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), pp. 307–308, Problem P, Eqs. (7.8)–(7.11)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Supplement_Network

namespace SteinitzExchange.Duality.Supplement

/-- Feasibility of Problem P: (7.2)–(7.4) and (7.8). -/
def IsProblemFlow {N A : Type*} [Fintype A] [DecidableEq N]
    (tail head : A → N) (Vp Vm : Finset N) (lo up : A → ℤ)
    (Bp : Finset (Vp → ℤ)) (Bm : Finset (Vm → ℤ)) (φ : A → ℤ) : Prop :=
  IsFeasibleFlow tail head Vp Vm lo up Bp φ ∧ exitBd tail head Vm φ ∈ Bm

/-- The objective of Problem P, p. 307. -/
def problemValue {N A : Type*} [Fintype A] [DecidableEq N]
    (tail head : A → N) (Vp Vm : Finset N) (w : A → ℝ)
    (ωp : (Vp → ℤ) → ℝ) (ωm : (Vm → ℤ) → ℝ) (φ : A → ℤ) : ℝ :=
  arcWeight w φ + ωp (entranceBd tail head Vp φ) + ωm (exitBd tail head Vm φ)

/-- Global maximality among all integral feasible flows of Problem P. -/
def IsOptimalFlow {N A : Type*} [Fintype A] [DecidableEq N]
    (tail head : A → N) (Vp Vm : Finset N) (lo up : A → ℤ) (w : A → ℝ)
    (Bp : Finset (Vp → ℤ)) (Bm : Finset (Vm → ℤ))
    (ωp : (Vp → ℤ) → ℝ) (ωm : (Vm → ℤ) → ℝ) (φ : A → ℤ) : Prop :=
  ∀ ψ : A → ℤ, IsProblemFlow tail head Vp Vm lo up Bp Bm ψ →
    problemValue tail head Vp Vm w ωp ωm ψ ≤ problemValue tail head Vp Vm w ωp ωm φ

/-- Reduced arc weight (7.9): initial vertex has a minus sign. -/
def potentialWeight {N A : Type*} (tail head : A → N) (w : A → ℝ) (q : N → ℝ)
    (a : A) : ℝ := w a - q (tail a) + q (head a)

/-- Conditions (i)–(iii) of Theorem 7.6. Boundary functions use the plus
perturbation ω[q]; the arc term subtracts the same boundary pairing. -/
def PotentialCertificate {N A : Type*} [Fintype A] [DecidableEq N]
    (tail head : A → N) (Vp Vm : Finset N) (lo up : A → ℤ) (w : A → ℝ)
    (Bp : Finset (Vp → ℤ)) (Bm : Finset (Vm → ℤ))
    (ωp : (Vp → ℤ) → ℝ) (ωm : (Vm → ℤ) → ℝ) (φ : A → ℤ) (q : N → ℝ) : Prop :=
  (∀ a, (potentialWeight tail head w q a < 0 → φ a = lo a) ∧
    (0 < potentialWeight tail head w q a → φ a = up a)) ∧
  (∀ x ∈ Bp, ωp x + pairing (fun v : Vp => q v) (toReal x) ≤
    ωp (entranceBd tail head Vp φ) +
      pairing (fun v : Vp => q v) (toReal (entranceBd tail head Vp φ))) ∧
  (∀ x ∈ Bm, ωm x + pairing (fun v : Vm => q v) (toReal x) ≤
    ωm (exitBd tail head Vm φ) +
      pairing (fun v : Vm => q v) (toReal (exitBd tail head Vm φ)))

end SteinitzExchange.Duality.Supplement


