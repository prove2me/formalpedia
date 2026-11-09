-- Prove2me | Definitions.Def_MixedCloning_Optimal_Model
-- name    : MixedCloning_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:55:27.977126+00:00
-- url     : https://prove2.me/theorems/a32f68d9-8c69-453b-a6cd-fe7623a7c91e
-- title:
--   Sections 1–3 — states, tensor powers, Haar measure, RPC and PCT
-- statement:
--   Let $d,r,n,k$ be nonnegative integers. Operators are complex matrices on a specified finite computational basis. A state is a positive semidefinite operator of trace one; channels use the published finite normalized Kraus-family definition, so their action is linear, completely positive and trace preserving on all operators. Tensor powers use the basis of words of length $n$, including the unique empty word for $n=0$. Fidelity is the square of the published root fidelity:
--
--   $$F(X,Y)=\bigl(\operatorname{tr}\sqrt{\sqrt X Y\sqrt X}\bigr)^2.$$
--
--   The symmetric projector is the average of register permutations, with inverse-permutation action. Its dimension is $d[n]=\binom{n+d-1}{n}$. Werner's map is compressed to the symmetric input corner and completed on the orthogonal complement by a fixed state $\tau$. The normalized Haar measure on $U(d)$ has mass one. A random purification channel (RPC) has, for every state $\rho$ of rank at most $r$ and every unit purification $u$ of $\rho$, the specified Haar-averaged action
--
--   $$R(\rho^{\otimes n})=\int (I\otimes U)^{\otimes n}|u\rangle\langle u|^{\otimes n}(I\otimes U^\dagger)^{\otimes n}\,dU.$$
--
--   The PCT map applies $R$, the completed Werner map in dimension $dr$, and a partial trace over every auxiliary register. The feasible sample set consists of the integers $n$ for which a channel attains fidelity at least $1-\varepsilon$ on all rank-at-most-$r$ states. Its infimum in the natural numbers defines $n_*$. Rank-$r$ projectors, projector states $P/r$, overlap, minimum and Haar-average overlap, and independent input/output permutation invariance are also defined here. These operational objects support both bounds; no fidelity bound or existence assertion is built into the RPC specification beyond its defining action.
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), pp. 3–5, 10–12, 15–18, 22

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

noncomputable section

namespace MixedCloning.Optimal

open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Word (a : Type) (n : ℕ) := Fin n → a
abbrev Op (a : Type) := Matrix a a ℂ
abbrev Cloner (d n m : ℕ) := QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d) m)

/-- Section 2: positive semidefinite matrices of trace one. -/
abbrev IsState {a : Type} [Fintype a] (X : Op a) : Prop := QAlgorithms.IsDensityMatrix X

/-- Section 2: squared, rather than root, fidelity. -/
def fidelity {a : Type} [Fintype a] [DecidableEq a] (X Y : Op a) : ℝ :=
  QAlgorithms.rootFidelity X Y ^ 2

/-- Tensor powers, including the empty tensor power. -/
def tensorPower {a : Type} (n : ℕ) (X : Op a) : Op (Word a n) :=
  fun i j => ∏ t, X (i t) (j t)

/-- Section 2.1, the inverse-permutation convention. -/
def permMatrix {a : Type} (n : ℕ) (p : Equiv.Perm (Fin n)) : Op (Word a n) :=
  fun i j => if i = j ∘ p.symm then 1 else 0

/-- Orthogonal projector on the permutation-fixed subspace, by finite group averaging. -/
def symProjector (a : Type) (n : ℕ) : Op (Word a n) :=
  ((Nat.factorial n : ℂ)⁻¹) • ∑ p : Equiv.Perm (Fin n), permMatrix (a := a) n p

def symDimension (d n : ℕ) : ℕ := Nat.choose (n + d - 1) n

/-- Adjoin k identity factors, without changing the register order. -/
def appendIdentity {a : Type} (n k : ℕ) (X : Op (Word a n)) : Op (Word a (n+k)) :=
  fun i j => X (fun t => i (Fin.castAdd k t)) (fun t => j (Fin.castAdd k t)) *
    if (fun t : Fin k => i (Fin.natAdd n t)) = (fun t : Fin k => j (Fin.natAdd n t)) then 1 else 0

/-- Werner's map on the Bose corner, extended by the fixed state tau on its complement. -/
def werner (a : Type) [Fintype a] (n k : ℕ) (tau : Op (Word a (n+k))) :
    QAlgorithms.Superop (Word a n) (Word a (n+k)) := fun X =>
  let P := symProjector a n
  let Q := symProjector a (n+k)
  ((symDimension (Fintype.card a) n : ℂ) / symDimension (Fintype.card a) (n+k)) •
    (Q * appendIdentity n k (P * X * P) * Q) + (( (1-P) * X).trace) • tau

/-- Trace out B in (A tensor B)^n, preserving the A register order. -/
def partialTrace {a b : Type} [Fintype b] (n : ℕ) (X : Op (Word (a × b) n)) : Op (Word a n) :=
  fun i j => ∑ z : Word b n, X (fun t => (i t, z t)) (fun t => (j t, z t))

def pure {a : Type} (u : a → ℂ) : Op a := fun i j => u i * conj (u j)

def auxAction {d r : ℕ} (U : Matrix.unitaryGroup (Fin r) ℂ) : Op (Fin d × Fin r) :=
  fun i j => if i.1 = j.1 then (U : Op (Fin r)) i.2 j.2 else 0

instance unitaryContinuousInv (d : ℕ) : ContinuousInv (Matrix.unitaryGroup (Fin d) ℂ) where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star
instance unitaryTopologicalGroup (d : ℕ) : IsTopologicalGroup (Matrix.unitaryGroup (Fin d) ℂ) where
instance unitaryMeasurable (d : ℕ) : MeasurableSpace (Matrix.unitaryGroup (Fin d) ℂ) := borel _
instance unitaryBorel (d : ℕ) : BorelSpace (Matrix.unitaryGroup (Fin d) ℂ) := ⟨rfl⟩
lemma unitaryClosed (d : ℕ) : IsClosed (Matrix.unitaryGroup (Fin d) ℂ : Set (Op (Fin d))) := by
  exact isClosed_unitary

instance unitaryCompact (d : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin d) ℂ) := by
  open scoped Matrix.Norms.Elementwise in
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Op (Fin d)) 1).of_isClosed_subset (unitaryClosed d)
  intro U hU
  simpa [Metric.mem_closedBall, dist_zero_right] using entrywise_sup_norm_bound_of_unitary hU

/-- Haar measure with total mass one, normalized on the whole compact unitary group. -/
def haar (d : ℕ) : Measure (Matrix.unitaryGroup (Fin d) ℂ) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
instance haarProbability (d : ℕ) : IsProbabilityMeasure (haar d) :=
  ⟨Measure.haarMeasure_self⟩

/-- The RPC is specified on every rank-at-most-r input and every unit purification. -/
def IsRPC (d r n : ℕ)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n)) : Prop :=
  QAlgorithms.IsChannel R ∧ ∀ rho : Op (Fin d), IsState rho → rho.rank ≤ r →
    ∀ u : EuclideanSpace ℂ (Fin d × Fin r), ‖u‖ = 1 →
      (fun i j => ∑ z : Fin r, pure u (i,z) (j,z)) = rho →
      R (tensorPower n rho) = ∫ U, let A := tensorPower n (auxAction (d := d) U)
        A * tensorPower n (pure u) * Aᴴ ∂haar r

/-- Figure 1 / Figure 7: random purification, Werner, then trace. -/
def pct (d r n k : ℕ)
    (R : QAlgorithms.Superop (Word (Fin d) n) (Word (Fin d × Fin r) n))
    (tau : Op (Word (Fin d × Fin r) (n+k))) : Cloner d n (n+k) :=
  fun X => partialTrace (n+k) (werner (Fin d × Fin r) n k tau (R X))

def Clones (d r n k : ℕ) (eps : ℝ) (C : Cloner d n (n+k)) : Prop :=
  QAlgorithms.IsChannel C ∧ ∀ rho : Op (Fin d), IsState rho → rho.rank ≤ r →
    1-eps ≤ fidelity (C (tensorPower n rho)) (tensorPower (n+k) rho)

def feasibleSamples (d r k : ℕ) (eps : ℝ) : Set ℕ :=
  {n | ∃ C : Cloner d n (n+k), Clones d r n k eps C}

def sampleComplexity (d r k : ℕ) (eps : ℝ) : ℕ := sInf (feasibleSamples d r k eps)

/-- Orthogonal rank-r projectors. -/
def IsProjector {a : Type} [Fintype a] (r : ℕ) (P : Op a) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ P.rank = r

def projectorState {a : Type} (r : ℕ) (P : Op a) : Op a := (r : ℂ)⁻¹ • P

/-- Fixed rank-r projector onto the last r coordinates (r=0 gives zero). -/
def baseProjector (d r : ℕ) : Op (Fin d) :=
  Matrix.diagonal fun i => if d-r ≤ i.val then 1 else 0

def rotatedProjector {d : ℕ} (r : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) : Op (Fin d) :=
  (U : Op (Fin d)) * baseProjector d r * (U : Op (Fin d))ᴴ

def overlap (d r n m : ℕ) (C : Cloner d n m) (P : Op (Fin d)) : ℝ :=
  (C (tensorPower n (projectorState r P)) * tensorPower m P).trace.re

def minimumOverlap (d r n m : ℕ) (C : Cloner d n m) : ℝ :=
  sInf {v | ∃ P : Op (Fin d), IsProjector r P ∧ v = overlap d r n m C P}

def averageOverlap (d r n m : ℕ) (C : Cloner d n m) : ℝ :=
  ∫ U, overlap d r n m C (rotatedProjector r U) ∂haar d

def PermInvariant (d n m : ℕ) (C : Cloner d n m) : Prop :=
  ∀ (pi : Equiv.Perm (Fin m)) (si : Equiv.Perm (Fin n)) (X : Op (Word (Fin d) n)),
    let A := permMatrix (a := Fin d) n si
    let B := permMatrix (a := Fin d) m pi
    B * C (A * X * Aᴴ) * Bᴴ = C X

end MixedCloning.Optimal


