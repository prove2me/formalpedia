-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Supplement_GreedyDR
-- name    : SingleSampleCombPI_XOS_Supplement_GreedyDR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:37:19.15732+00:00
-- url     : https://prove2.me/theorems/49ba1b03-4d80-400b-8fce-a15c947e2a67
-- title:
--   Continuous greedy and canonical Aumann–Shapley fixed-point free-disposal dynamics
-- statement:
--   Algorithm 5 chooses a maximizer of $\Phi_H(x)=v(x)+\mathrm{FD}_{1-x}(H)$ on the entire cube using one fixed choice rule, then appends the allocation and its frozen supporting prices. It does not modify previous provisional allocations. Zero fallback only totalizes malformed inputs; existence on source inputs is a theorem conclusion. This exact noncomputable specification has no efficiency assertion attached to its cost fields.
--
--   For Algorithm 6, valuations are twice differentiable, normalized, nonnegative and monotone on the nonnegative orthant. The DR condition is the antitone-gradient condition of Definition 6; concavity is imposed separately as in Theorem 4.7. Derivatives within the orthant encode boundary derivatives without a C² assumption. The supporting map is the canonical Aumann–Shapley map $q_v(x)=\int_0^1\nabla v(tx)\,dt$.
--
--   Put $\gamma=1-e^{-1}$ and $F(t)=(e^{t-1}-e^{-1})/\gamma$. Frozen histories determine $y_j(w)=\min\{1,\sum_e x_{e,j}\mathbf1[q_{e,j}\ge w]\}$ and $\alpha_j=\int_0^\infty F(y_j(w))\,dw$. Condition 1 requires $x$ to maximize $v(x')-\langle x',\alpha(H\mathbin{\|}(x,q_v(x)))\rangle$: these are hypothetical post-update prices, not pre-update prices. Reachable histories are built from the initialization and these transitions. A valid trace records each buyer's condition and defines $\beta_i=v_i(x_i)-\langle x_i,\alpha^{(i)}\rangle$ independently of the desired inequalities. Algorithm 6 selects such a fixed point when one exists; existence and competitiveness are theorem conclusions. No time bound is claimed for Algorithm 6.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Definition 6 and Proposition 2.2, printed p. 8 / PDF p. 10; Algorithms 5–6 and Condition 1, printed pp. 21–27 / PDF pp. 23–29.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Continuous

namespace SingleSampleCombPI.XOS.Supplement

/-- The zero point of the cube. -/
def cubeZero (m : ℕ) : Cube m := ⟨0, fun _ => ⟨le_rfl, zero_le_one⟩⟩

/-- Exact source maximization, with a fixed choice rule and total zero fallback
on malformed inputs. Existence on the source class is a theorem conclusion. -/
noncomputable def greedyChoice {m : ℕ} (H : FrozenHistory m) (b : Buyer m) : Cube m := by
  classical
  exact if h : ∃ x : Cube m, CubeMaximizer (surrogate H b) x.1 then
    Classical.choose h else cubeZero m

/-- Algorithm 5 as a state machine. The cost fields of this noncomputable
specification are not used for computational assertions: efficient implementations
are separately quantified as terminating oracle programs. -/
noncomputable def alg5 (n m : ℕ) : FDAlg .divisible n m where
  State := FrozenHistory m
  Ω := Unit
  seed := RandomSource.ofPMF (PMF.pure ())
  init := fun _ => []
  step := fun H _ b => let x := greedyChoice H b; (x, H ++ [freeze b x])
  seedCost := 0
  stepCost := fun _ _ _ => 0

def ContinuousBuyer {m : ℕ} (b : Buyer m) : Prop :=
  b.Valid .divisible ∧ ContinuousOn b.v {x | InDom .divisible x}

def ConcaveBuyer {m : ℕ} (b : Buyer m) : Prop :=
  ContinuousBuyer b ∧ ConcaveOn ℝ {x | InDom .divisible x} b.v

/-- The source nonnegative orthant, including the boundary. -/
def orthant (m : ℕ) : Set (Vec m) := {x | 0 ≤ x}

noncomputable def gradient {m : ℕ} (v : Vec m → ℝ) (x : Vec m) : Vec m := by
  classical
  exact fun j => (fderivWithin ℝ v (orthant m) x) (Pi.single j 1)

/-- Twice differentiable on the orthant, normalized nonnegative monotone,
with antitone gradient (Definition 6) and concave (Theorem 4.7). No C² or
Lipschitz assumption has been added. -/
def DRConcave {m : ℕ} (v : Vec m → ℝ) : Prop :=
  v 0 = 0 ∧ (∀ x ∈ orthant m, 0 ≤ v x) ∧ MonotoneOn v (orthant m) ∧
  DifferentiableOn ℝ v (orthant m) ∧
  DifferentiableOn ℝ (fun x => fderivWithin ℝ v (orthant m) x) (orthant m) ∧
  (∀ x ∈ orthant m, ∀ y ∈ orthant m, x ≤ y → gradient v y ≤ gradient v x) ∧
  ConcaveOn ℝ (orthant m) v

/-- The canonical Aumann–Shapley map (Proposition 2.2), not an arbitrary
supporting-price oracle supplied by the input. -/
noncomputable def aumann {m : ℕ} (v : Vec m → ℝ) (x : Vec m) : Vec m :=
  fun j => ∫ t in Set.Icc (0:ℝ) 1, gradient v (t • x) j

noncomputable def drBuyer {m : ℕ} (v : Vec m → ℝ) : Buyer m :=
  ⟨v, aumann v, fun _ => ∅⟩

noncomputable def gamma : ℝ := 1 - Real.exp (-1)
noncomputable def splitFunction (t : ℝ) : ℝ := (Real.exp (t-1) - Real.exp (-1))/gamma

/-- The primal layer y=min(1,sum of frozen masses). -/
noncomputable def a6Layer {m : ℕ} (H : FrozenHistory m) (j : Fin m) (w : ℝ) : ℝ :=
  min 1 (layerMass H j w)

noncomputable def a6Alpha {m : ℕ} (H : FrozenHistory m) : Vec m :=
  fun j => ∫ w in Set.Ioi (0:ℝ), splitFunction (a6Layer H j w)

/-- The post-update alpha is computed using the candidate x itself. -/
def condition1 {m : ℕ} (H : FrozenHistory m) (v : Vec m → ℝ) (x : Cube m) : Prop :=
  ∀ y : Cube m,
    v y.1 - dot (a6Alpha (H ++ [freeze (drBuyer v) x])) y.1 ≤
      v x.1 - dot (a6Alpha (H ++ [freeze (drBuyer v) x])) x.1

/-- Reachability, rather than an assumed primal/dual invariant. -/
inductive A6Reachable {m : ℕ} : FrozenHistory m → Prop
  | initial : A6Reachable []
  | step {H : FrozenHistory m} {v : Vec m → ℝ} {x : Cube m} :
      A6Reachable H → DRConcave v → condition1 H v x →
      A6Reachable (H ++ [freeze (drBuyer v) x])

noncomputable def a6Choice {m : ℕ} (H : FrozenHistory m) (v : Vec m → ℝ) : Cube m := by
  classical
  exact if h : ∃ x : Cube m, condition1 H v x then Classical.choose h else cubeZero m

/-- Algorithm 6. Earlier allocations remain frozen. Existence of the implicit
fixed point is not a field, hypothesis or cost certificate of this algorithm. -/
noncomputable def alg6 (n m : ℕ) : FDAlg .divisible n m where
  State := FrozenHistory m
  Ω := Unit
  seed := RandomSource.ofPMF (PMF.pure ())
  init := fun _ => []
  step := fun H _ b => let x := a6Choice H b.v; (x, H ++ [freeze (drBuyer b.v) x])
  seedCost := 0
  stepCost := fun _ _ _ => 0

/-- History of an actual conditional-choice trace, in arrival order. -/
noncomputable def a6History {n m : ℕ} (v : Fin n → Vec m → ℝ) (ρ : Equiv.Perm (Fin n))
    (x : Fin n → Cube m) (t : ℕ) : FrozenHistory m :=
  (((List.finRange n).take t).map fun k => freeze (drBuyer (v (ρ k))) (x (ρ k)))

def A6Trace {n m : ℕ} (v : Fin n → Vec m → ℝ) (ρ : Equiv.Perm (Fin n))
    (x : Fin n → Cube m) : Prop :=
  ∀ k : Fin n, condition1 (a6History v ρ x k.val) (v (ρ k)) (x (ρ k))

noncomputable def a6Beta {n m : ℕ} (v : Fin n → Vec m → ℝ)
    (ρ : Equiv.Perm (Fin n)) (x : Fin n → Cube m) (i : Fin n) : ℝ :=
  v i (x i).1 - dot (a6Alpha (a6History v ρ x ((ρ.symm i).val+1))) (x i).1

end SingleSampleCombPI.XOS.Supplement


