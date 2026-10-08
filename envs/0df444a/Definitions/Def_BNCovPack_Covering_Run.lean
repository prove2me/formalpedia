-- Prove2me | Definitions.Def_BNCovPack_Covering_Run
-- name    : BNCovPack_Covering_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:12:08.017943+00:00
-- url     : https://prove2.me/theorems/c0b8a4e0-eb22-487d-b92a-523a23075250
-- title:
--   Phases and runs of the online fractional covering scheme
-- statement:
--   Let $I$ be a finite nonempty set of covering variables, let the constraints be indexed by $0,\ldots,m-1$, and let $a_{ik}\ge0$ and $c_i>0$ be the coefficients and costs of a general covering instance. For $B>0$, the first phase starts with
--
--   $$
--   \alpha_1=\frac1B\min_{i:a_{i0}>0}\frac{c_i}{a_{i0}},\qquad x_i=\frac{\alpha_1}{2|I|c_i},\qquad y_k=0.
--   $$
--
--   In a phase with bound $\alpha$, processing the next known constraint $k$ raises only $y_k=t\ge0$ and sets $x_i=\frac{\alpha}{2|I|c_i}\exp\bigl(\frac{\log(2|I|)}{c_i}\sum_h a_{ih}y_h\bigr)$. The round stops at the first time that coverage reaches $1/B$ or the phase cost reaches $\alpha$. If coverage is attained, processing advances to the next known constraint. If the cost cap is attained while coverage is still below $1/B$, the phase is recorded, the bound doubles, the dual variables reset, and all known constraints are processed again from the first. A new external constraint arrives only after the current phase has processed all previously known constraints. The output is the coordinatewise maximum of the primal vectors from all phases.
--
--   This definition supplies the algorithmic object to which the four claims in the proof of Theorem 4.1 apply. It retains the old phase values in the output even though their dual vectors are reset on restart.
--
--   **Formalization Note** Indices start at zero in Lean, whereas the paper starts at one. The minimum omits zero coefficients so division by zero cannot set the first bound to zero. A phase ending at exactly its cost cap is the continuous stopping-time reading of the paper's phrase “exceeds this bound”; coverage wins a simultaneous tie.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, pp. 3–4, Fig. 1, and p. 8, Section 4, scheme

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance

namespace BNCovPack.Covering

open OnlinePrimalDual.GeneralPacking

variable {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}

/-- The least first-constraint cost ratio, with zero coefficients omitted. The paper's
minimum is understood over positive coefficients. -/
noncomputable def firstAlpha (inst : GeneralInstance I (Fin m)) (B : ℝ) (hm : 0 < m) : ℝ :=
  (1 / B) * sInf {z : ℝ | ∃ i : I, 0 < inst.a i ⟨0, hm⟩ ∧ z = inst.c i / inst.a i ⟨0, hm⟩}

/-- The phase's current primal and dual values. `seen` constraints have been processed
in this phase; a restart sets `seen` back to zero. -/
structure Phase (I : Type*) (m : ℕ) where
  alpha : ℝ
  x : I → ℝ
  y : Fin m → ℝ
  seen : ℕ

/-- A phase starts with the exponential formula at zero dual variables. -/
noncomputable def initialPhase (inst : GeneralInstance I (Fin m)) (alpha : ℝ) : Phase I m where
  alpha := alpha
  x := fun i => alpha / (2 * (Fintype.card I : ℝ) * inst.c i)
  y := fun _ => 0
  seen := 0

/-- Exponential primal value when the phase dual vector is `y`. -/
noncomputable def phasePrimal (inst : GeneralInstance I (Fin m)) (alpha : ℝ)
    (y : Fin m → ℝ) (i : I) : ℝ :=
  alpha / (2 * (Fintype.card I : ℝ) * inst.c i) *
    Real.exp ((Real.log (2 * (Fintype.card I : ℝ)) / inst.c i) *
      ∑ k : Fin m, inst.a i k * y k)

/-- The phase after raising the current dual variable to `t` and recomputing `x`.
The index `k` has not yet been marked processed. -/
noncomputable def atTime (inst : GeneralInstance I (Fin m)) (p : Phase I m)
    (k : Fin m) (t : ℝ) : Phase I m :=
  let y' := Function.update p.y k t
  { alpha := p.alpha, x := phasePrimal inst p.alpha y', y := y', seen := p.seen }

/-- The two quantities that stop a continuous round: coverage and phase cost. -/
noncomputable def coverage (inst : GeneralInstance I (Fin m)) (p : Phase I m)
    (k : Fin m) : ℝ := ∑ i : I, inst.a i k * p.x i

noncomputable def phaseCost (inst : GeneralInstance I (Fin m)) (p : Phase I m) : ℝ :=
  ∑ i : I, inst.c i * p.x i

/-- No earlier time in this round reached either stopping condition. -/
def BeforeStop (inst : GeneralInstance I (Fin m)) (B : ℝ) (p : Phase I m)
    (k : Fin m) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∀ u : ℝ, 0 ≤ u → u < t →
    coverage inst (atTime inst p k u) k < 1 / B ∧
    phaseCost inst (atTime inst p k u) < p.alpha

/-- The online state includes every completed phase. Their primal values remain part of
the actual online output after a restart. -/
structure State (I : Type*) (m : ℕ) where
  finished : List (Phase I m)
  current : Phase I m
  arrived : ℕ

/-- The output uses the coordinatewise maximum over completed and current phases. -/
noncomputable def output (s : State I m) (i : I) : ℝ :=
  s.finished.foldl (fun v p => max v (p.x i)) (s.current.x i)

/-- The sum of the phase costs, used in claim (iii). -/
noncomputable def totalPhaseCost (inst : GeneralInstance I (Fin m)) (s : State I m) : ℝ :=
  (s.finished.map (phaseCost inst)).sum + phaseCost inst s.current

/-- A single event of the phased covering scheme. An arrival waits until every known
constraint is processed. A covered round advances; an uncovered round whose cost hits the
cap archives its phase and replays the known constraints with doubled alpha. -/
inductive Step (inst : GeneralInstance I (Fin m)) (B : ℝ) : State I m → State I m → Prop
  | arrive (s : State I m) (hready : s.current.seen = s.arrived)
      (hmore : s.arrived < m) :
      Step inst B s { s with arrived := s.arrived + 1 }
  | cover (s : State I m) (k : Fin m) (t : ℝ)
      (hk : s.current.seen = k.val) (hknown : k.val < s.arrived)
      (hstop : BeforeStop inst B s.current k t)
      (hcover : 1 / B ≤ coverage inst (atTime inst s.current k t) k) :
      Step inst B s { s with current := { (atTime inst s.current k t) with seen := k.val + 1 } }
  | restart (s : State I m) (k : Fin m) (t : ℝ)
      (hk : s.current.seen = k.val) (hknown : k.val < s.arrived)
      (hstop : BeforeStop inst B s.current k t)
      (hcap : phaseCost inst (atTime inst s.current k t) = s.current.alpha)
      (huncovered : coverage inst (atTime inst s.current k t) k < 1 / B) :
      Step inst B s
        { finished := s.finished ++ [atTime inst s.current k t]
          current := initialPhase inst (2 * s.current.alpha)
          arrived := s.arrived }

/-- The state just after the first constraint arrives. -/
noncomputable def firstState (inst : GeneralInstance I (Fin m)) (B : ℝ)
    (hm : 0 < m) : State I m where
  finished := []
  current := initialPhase inst (firstAlpha inst B hm)
  arrived := 1

/-- A complete run after `J` arrivals ends between rounds, with all `J` known constraints
processed in the current phase. Every intermediate step follows `Step`. -/
def Run (inst : GeneralInstance I (Fin m)) (B : ℝ) (hm : 0 < m)
    (J : ℕ) (s : State I m) : Prop :=
  Relation.ReflTransGen (Step inst B) (firstState inst B hm) s ∧
  s.arrived = J ∧ s.current.seen = J

end BNCovPack.Covering


