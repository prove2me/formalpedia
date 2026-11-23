-- Prove2me | Definitions.Def_LogBarrierIPM_Iterations_Supplement_TropicalTube
-- name    : LogBarrierIPM_Iterations_Supplement_TropicalTube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:11:52.074006+00:00
-- url     : https://prove2.me/theorems/bc598335-ce9c-45c1-b86a-ba3a69afc7eb
-- title:
--   Tropical segment counts, tubes, vertex separation and t₁
-- statement:
--   For a real curve $C$ and $a\le b$, let $\gamma([a,b])$ be the least positive number of consecutive tropical segments whose union is $C([a,b])$, with their first and last points $C(a)$ and $C(b)$. A missing finite representation gives $+\infty$; a singleton interval admits one degenerate segment. Vertex parameters are exactly the points of non-differentiability. Define
--   $$\varepsilon_0=\tfrac16\inf_{v,w\text{ vertices},\,C(v)\ne C(w)}d_\infty(C(v),C(w)),$$
--   with value $+\infty$ when fewer than two distinct vertices exist. The tube is the union of closed $d_\infty$-balls of radius $\varepsilon$ centered on $C([a,b])$. The endpoints $a\le b$ are separated at radius $\varepsilon$ when every vertex parameter $v\in(a,b)$ satisfies
--   $$d_\infty(C(a),C(v))>2\varepsilon,\qquad d_\infty(C(b),C(v))>4\varepsilon.$$
--   Finally $\varepsilon_t=\log_t(2N/(1-\theta))+\delta(t)$, and $t_1\ge\max(t_0,1)$ requires $\varepsilon_t<\varepsilon_0$ for all $t>t_1$. These are the objects of §6.1; the separation condition is the repair of Proposition 28 and Theorem 29, whose printed forms fail when an endpoint is next to a vertex.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 23, def-gamma

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_Specialization
import Definitions.Def_LogBarrierIPM_Iterations_TropicalSegment

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

/-- Union of p consecutive tropical segments. -/
def tropicalChain {d : ℕ} (p : ℕ) (z : Fin (p + 1) → Fin d → WithBot ℝ) :
    Set (Fin d → WithBot ℝ) :=
  ⋃ i : Fin p, tsegm (z i.castSucc) (z i.succ)

/-- Least positive segment count; +∞, never zero, if no finite representation exists.
For a=b a single degenerate segment is admissible. -/
noncomputable def gamma {d : ℕ} (C : ℝ → Fin d → ℝ) (a b : ℝ) : WithTop ℕ :=
  sInf {k | ∃ p : ℕ, 1 ≤ p ∧ k = (p : WithTop ℕ) ∧
    ∃ z : Fin (p + 1) → Fin d → WithBot ℝ,
      z 0 = tropicalizeReal (C a) ∧ z (Fin.last p) = tropicalizeReal (C b) ∧
      tropicalChain p z = (fun lam => tropicalizeReal (C lam)) '' Set.Icc a b}

/-- Vertex parameters: precisely the points of non-differentiability. -/
def vertexParameters {d : ℕ} (C : ℝ → Fin d → ℝ) : Set ℝ :=
  {v | ¬ DifferentiableAt ℝ C v}

/-- One sixth of the least distance between distinct vertices; +∞ if there are fewer than two. -/
noncomputable def epsilonZero {d : ℕ} (C : ℝ → Fin d → ℝ) : EReal :=
  (1 / 6 : EReal) * (⨅ v ∈ vertexParameters C, ⨅ w ∈ vertexParameters C,
    if C v ≠ C w then dInf (tropicalizeReal (C v)) (tropicalizeReal (C w)) else ⊤)

def tropicalBall {d : ℕ} (x : Fin d → WithBot ℝ) (ε : EReal) :
    Set (Fin d → WithBot ℝ) := {z | dInf z x ≤ ε}

def tube {d : ℕ} (C : ℝ → Fin d → ℝ) (a b : ℝ) (ε : EReal) :
    Set (Fin d → WithBot ℝ) :=
  ⋃ lam ∈ Set.Icc a b, tropicalBall (tropicalizeReal (C lam)) ε

/-- The endpoint repair: every interior vertex is farther than 2ε from the lower endpoint and
farther than 4ε from the upper one. -/
def EndpointsSeparated {d : ℕ} (C : ℝ → Fin d → ℝ) (a b : ℝ) (ε : EReal) : Prop :=
  ∀ v ∈ vertexParameters C, v ∈ Set.Ioo a b →
    2 * ε < dInf (tropicalizeReal (C a)) (tropicalizeReal (C v)) ∧
    4 * ε < dInf (tropicalizeReal (C b)) (tropicalizeReal (C v))

/-- Left side of (35), at the actual t, retaining δ(t). -/
noncomputable def epsilonAt {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) (θ t : ℝ) : EReal :=
  (Real.logb t (2 * (n + m : ℕ) / (1 - θ)) : EReal) + delta A b c t

def TubeThreshold {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux) (θ t0 t1 : ℝ) : Prop :=
  t0 ≤ t1 ∧ 1 ≤ t1 ∧ ∀ t : ℝ, t1 < t →
    epsilonAt A b c θ t < epsilonZero (tropicalPath A b c)

end LogBarrierIPM.Iterations.Supplement


