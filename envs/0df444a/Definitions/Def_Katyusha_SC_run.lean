-- Prove2me | Definitions.Def_Katyusha_SC_run
-- name    : Katyusha_SC_run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T06:13:49.40098+00:00
-- url     : https://prove2.me/theorems/5698dc8e-827f-44b9-a8b6-f68b854dd572
-- title:
--   Algorithm 1, Option I — the Katyusha run
-- statement:
--   Let $f_i:\mathbb R^d\to\mathbb R$ be $n$ convex component functions, let $f=n^{-1}\sum_i f_i$, and let $F=f+\psi$ for a strongly convex regularizer $\psi$. Each component gradient is represented by a vector field $g_i=\nabla f_i$. A problem instance records the component functions, gradients, regularizer, smoothness constant $L$, and strong convexity modulus $\sigma$. Its validity predicate requires $n\ge1$, $L,\sigma>0$, the actual gradient relation, convexity and $L$ smoothness of each component, and $\sigma$ strong convexity of $\psi$.
--
--   For an epoch length $m$, Algorithm 1 sets $\tau_2=1/2$, $\tau_1=\min\{\sqrt{m\sigma}/\sqrt{3L},1/2\}$ and $\alpha=1/(3\tau_1L)$. An epoch starts with snapshot $\widetilde x$, and persistent iterates $y,z$. At each sampled index $i$, it forms
--   $$x=\tau_1 z+\tfrac12\widetilde x+(\tfrac12-\tau_1)y,\qquad \widetilde\nabla=\nabla f(\widetilde x)+\nabla f_i(x)-\nabla f_i(\widetilde x),$$
--   then applies the two proximal updates of lines 10 and 11 to obtain the new $z$ and $y$. The next snapshot is the average of the new $y$ iterates, weighted by $(1+\alpha\sigma)^j$ for $j=0,\dots,m-1$. The initial snapshot and both iterates are $x_0$; $y,z$ persist between epochs. The output is the final snapshot.
--
--   The accompanying finite expectation averages uniformly over all $n^{Sm}$ index sequences, corresponding to independent uniform choices in $S$ epochs of $m$ steps. These definitions provide the algorithm whose objective is bounded in Theorem 2.1.
--
--   **Formalization Note** Vectors are `EuclideanSpace ℝ (Fin d)`, and indices are `Fin n`. The map $P(\gamma,\cdot)$ is constrained to be the proximal map of the actual $\psi$ for every $\gamma>0$. Only Option I is represented. The proximal minimizers and the finite-sum objective use the referenced SAGA definitions. The regularizer is real valued, including nondifferentiable functions but excluding extended-valued indicator penalties.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, p. 1, Problem (1.1); p. 6, Definition 1.2; p. 7, Algorithm 1, Option I

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaRun

namespace Katyusha.SC

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The data of Problem (1.1). -/
structure Problem (d n : ℕ) where
  f : Fin n → Vec d → ℝ
  grad : Fin n → Vec d → Vec d
  ψ : Vec d → ℝ
  smoothness : ℝ
  modulus : ℝ

/-- Standing assumptions of Theorem 2.1. -/
def IsValid {d n : ℕ} (p : Problem d n) : Prop :=
  0 < n ∧ 0 < p.smoothness ∧ 0 < p.modulus ∧
  (∀ (i : Fin n) (x : Vec d), HasGradientAt (p.f i) (p.grad i x) x) ∧
  (∀ (i : Fin n), ConvexOn ℝ Set.univ (p.f i)) ∧
  (∀ (i : Fin n) (x y : Vec d), ‖p.grad i x - p.grad i y‖ ≤ p.smoothness * ‖x - y‖) ∧
  StrongConvexOn Set.univ p.modulus p.ψ

noncomputable def objective {d n : ℕ} (p : Problem d n) (x : Vec d) : ℝ :=
  SAGA.Convex.fAvg p.f x + p.ψ x

noncomputable def estimator {d n : ℕ} (p : Problem d n)
    (snapshot x : Vec d) (i : Fin n) : Vec d :=
  SAGA.Convex.gradAvg p.grad snapshot + p.grad i x - p.grad i snapshot

/-- The proximal map is tied to the actual regularizer at every positive step size. -/
def IsProxMap {d : ℕ} (ψ : Vec d → ℝ) (P : ℝ → Vec d → Vec d) : Prop :=
  ∀ γ, 0 < γ → ∀ x, SAGA.Convex.IsProxPoint ψ γ x (P γ x)

noncomputable def τ {d n : ℕ} (p : Problem d n) (m : ℕ) : ℝ :=
  min (Real.sqrt ((m : ℝ) * p.modulus) / Real.sqrt (3 * p.smoothness)) (1 / 2)

noncomputable def α {d n : ℕ} (p : Problem d n) (m : ℕ) : ℝ :=
  1 / (3 * τ p m * p.smoothness)

noncomputable def θ {d n : ℕ} (p : Problem d n) (a : ℝ) : ℝ :=
  1 + a * p.modulus

/-- The snapshot and the two persistent iterates at an epoch boundary. -/
structure State (d : ℕ) where
  snapshot : Vec d
  y : Vec d
  z : Vec d

noncomputable def mixedPoint {d : ℕ} (t : ℝ) (s : State d) : Vec d :=
  t • s.z + (1 / 2 : ℝ) • s.snapshot + (1 - t - 1 / 2 : ℝ) • s.y

noncomputable def nextY {d n : ℕ} (p : Problem d n) (P : ℝ → Vec d → Vec d)
    (snapshot x : Vec d) (i : Fin n) : Vec d :=
  let g := estimator p snapshot x i
  P (1 / (3 * p.smoothness)) (x - (1 / (3 * p.smoothness)) • g)

noncomputable def nextZ {d n : ℕ} (p : Problem d n) (P : ℝ → Vec d → Vec d)
    (a : ℝ) (snapshot x z : Vec d) (i : Fin n) : Vec d :=
  let g := estimator p snapshot x i
  P a (z - a • g)

noncomputable def progress {d n : ℕ} (p : Problem d n) (P : ℝ → Vec d → Vec d)
    (snapshot x : Vec d) (i : Fin n) : ℝ :=
  let y := nextY p P snapshot x i
  (-(3 * p.smoothness / 2 * ‖y - x‖ ^ 2 +
    inner ℝ (estimator p snapshot x i) (y - x) + p.ψ y - p.ψ x))

noncomputable def genericStep {d n : ℕ} (p : Problem d n) (P : ℝ → Vec d → Vec d)
    (t a : ℝ) (s : State d) (i : Fin n) : State d :=
  let x := mixedPoint t s
  { snapshot := s.snapshot
    y := nextY p P s.snapshot x i
    z := nextZ p P a s.snapshot x s.z i }

structure EpochAcc (d : ℕ) where
  state : State d
  weighted : Vec d
  count : ℕ

/-- One epoch of Algorithm 1 with explicit coupling and prox parameters. -/
noncomputable def genericEpoch {d n : ℕ} (p : Problem d n) (P : ℝ → Vec d → Vec d)
    (m : ℕ) (t a : ℝ) (s : State d) (indices : List (Fin n)) : State d :=
  let b := indices.foldl (fun b i =>
    let next := genericStep p P t a b.state i
    { state := next
      weighted := b.weighted + (θ p a) ^ b.count • next.y
      count := b.count + 1 : EpochAcc d })
    { state := s, weighted := 0, count := 0 }
  { snapshot := (1 / ∑ j ∈ Finset.range m, (θ p a) ^ j) • b.weighted
    y := b.state.y
    z := b.state.z }

/-- Algorithm 1, Option I: the parameters come from line 2. -/
noncomputable def epoch {d n : ℕ} (p : Problem d n) (P : ℝ → Vec d → Vec d)
    (m : ℕ) (s : State d) (indices : List (Fin n)) : State d :=
  genericEpoch p P m (τ p m) (α p m) s indices

/-- Algorithm 1, Option I, with persistent y and z and m indices per epoch. -/
noncomputable def run {d n : ℕ} (p : Problem d n) (P : ℝ → Vec d → Vec d)
    (m : ℕ) (x0 : Vec d) : (S : ℕ) → List (Fin n) → State d
  | 0, _ => { snapshot := x0, y := x0, z := x0 }
  | S + 1, indices => epoch p P m (run p P m x0 S (indices.take (S * m)))
      (indices.drop (S * m))

/-- Uniform expectation over the S·m independent sampled indices. -/
noncomputable def expectedObjective {d n : ℕ} (p : Problem d n)
    (P : ℝ → Vec d → Vec d) (m S : ℕ) (x0 : Vec d) : ℝ :=
  SAGA.Convex.expectIdx n (S * m) (fun js =>
    objective p (run p P m x0 S (List.ofFn js)).snapshot)

noncomputable def gap {d n : ℕ} (p : Problem d n) (xstar x : Vec d) : ℝ :=
  objective p x - objective p xstar

noncomputable def potential {d n : ℕ} (p : Problem d n) (m : ℕ)
    (xstar : Vec d) (s : State d) : ℝ :=
  ((1 / 2 : ℝ) / τ p m) * gap p xstar s.snapshot *
      (∑ j ∈ Finset.range m, (θ p (α p m)) ^ j) +
  (1 - τ p m - 1 / 2) / τ p m * gap p xstar s.y +
  1 / (2 * α p m) * ‖s.z - xstar‖ ^ 2

end Katyusha.SC


