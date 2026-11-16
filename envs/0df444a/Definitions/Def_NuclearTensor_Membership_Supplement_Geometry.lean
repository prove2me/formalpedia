-- Prove2me | Definitions.Def_NuclearTensor_Membership_Supplement_Geometry
-- name    : NuclearTensor_Membership_Supplement_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:40:24.903727+00:00
-- url     : https://prove2.me/theorems/08edec76-ac00-4258-846d-5a3def32dc76
-- title:
--   Complex multipartite geometry and real Hermitian coordinates
-- statement:
--   All local spaces are $\mathbb C^d$ and the $k$-party matrix space has dimension $d^k$ on each side. A density matrix is positive semidefinite with trace one. The norm $\|A\|_F$ is the unnormalized Hilbert–Schmidt norm. Fully separable states form the real convex hull of pure product projectors:
--
--   $$\operatorname{Sep}(d,k)=\operatorname{conv}_{\mathbb R}\{\bigotimes_{j=1}^k |x_j\rangle\langle x_j|:\|x_j\|=1\}.$$
--
--   This bundle supplies products, partial traces, signed product-Hermitian operators, normalized convex mixtures, finite product-basis subspaces, and explicit serialization. Density matrices, pure projectors, trace norm and the general channel predicate reuse the published ClonableQMASep definitions. Local diagonal, symmetric, and antisymmetric Hermitian basis matrices give real orthonormal coordinates of dimension $d^2$; off-diagonal entries use $1/\sqrt2$. The tensor product of these bases defines the coordinate map to the published real Geometry arrays.
--
--   These definitions support the classical separability application and the copy-access branch with one shared geometry.
--
--   **Formalization Note** Rows and parties use zero-based finite indices and row-major coordinates. The distance is an infimum in the extended nonnegative reals, with empty-set distance infinity. Confidence notation is $L(\delta)=1+\max(0,\log(1/\delta))$; logarithmic dimension notation is $\ell(d)=1+\lceil\log_2 d\rceil$. All theorem inputs have positive local dimension and party count.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp. 9, 21–35, 38–51; Section 2, Definitions 6.2–6.3, Section 7.1 and Appendices A–C.

import Definitions.Def_NuclearTensor_Membership_Optimization
import Definitions.Def_ClonableQMASep_Main_Channels

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate ENNReal

namespace NuclearTensor.Membership.Supplement

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev CVec (n : ℕ) := Fin n → ℂ
abbrev IsDensity {n : ℕ} (A : CMat n) := ClonableQMASep.Main.IsDensity A
abbrev traceNorm {n : ℕ} (A : CMat n) := ClonableQMASep.Main.traceNorm A
abbrev IsChannel {a b : ℕ} (f : CMat a → CMat b) := ClonableQMASep.Main.IsChannel f
abbrev pure {n : ℕ} (x : CVec n) := ClonableQMASep.Main.pureDM x

def normSq {n : ℕ} (x : CVec n) : ℝ := ∑ i, Complex.normSq (x i)
def hsNorm {n : ℕ} (A : CMat n) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j))
def hsInner {n : ℕ} (A B : CMat n) : ℝ := (Matrix.trace (A * B)).re

def unitProducts (d k : ℕ) : Set (Fin k → CVec d) := {x | ∀ j, normSq (x j) = 1}

def digit (d k I j : ℕ) : ℕ := I / d ^ (k - 1 - j) % d

def productVector {d k : ℕ} (x : Fin k → CVec d) : CVec (d ^ k) := fun I =>
  ∏ j, if h : digit d k I.val j.val < d then x j ⟨_, h⟩ else 0

def productMatrix {d k : ℕ} (A : Fin k → CMat d) : CMat (d ^ k) := fun I J =>
  ∏ j, if h : digit d k I.val j.val < d ∧ digit d k J.val j.val < d then
    A j ⟨_, h.1⟩ ⟨_, h.2⟩ else 0

def sep (d k : ℕ) : Set (CMat (d ^ k)) :=
  convexHull ℝ ((fun x => pure (productVector x)) '' unitProducts d k)

def sepDistance {d k : ℕ} (A : CMat (d ^ k)) : ℝ≥0∞ :=
  ⨅ B ∈ sep d k, ENNReal.ofReal (hsNorm (A - B))

def sepDecision {d k : ℕ} (η : ℝ) (A : CMat (d ^ k)) (b : Bool) : Prop :=
  (A ∈ sep d k → b = true) ∧ (ENNReal.ofReal η ≤ sepDistance A → b = false)

/-- Normalized convex mixture; the word signed concerns rho minus this state. -/
structure Mixture (d k T : ℕ) where
  weight : Fin T → ℝ
  factor : Fin T → Fin k → CMat d
  nonneg : ∀ l, 0 ≤ weight l
  total : ∑ l, weight l = 1
  density : ∀ l j, IsDensity (factor l j)

def Mixture.matrix {d k T : ℕ} (S : Mixture d k T) : CMat (d ^ k) :=
  ∑ l, (S.weight l : ℂ) • productMatrix (S.factor l)

/-- Signed product-Hermitian operator used by LocalSearch, not a density mixture. -/
structure SignedOperator (d k T : ℕ) where
  coefficient : Fin T → ℝ
  factor : Fin T → Fin k → CMat d
  hermitian : ∀ l j, (factor l j).IsHermitian
  bounded : ∀ l j, hsNorm (factor l j) ≤ 1

def SignedOperator.matrix {d k T : ℕ} (K : SignedOperator d k T) : CMat (d ^ k) :=
  ∑ l, (K.coefficient l : ℂ) • productMatrix (K.factor l)

def SignedOperator.G {d k T : ℕ} (K : SignedOperator d k T) : ℝ :=
  1 + ∑ l, |K.coefficient l|

def value {d k : ℕ} (A : CMat (d ^ k)) (x : Fin k → CVec d) : ℝ :=
  hsInner A (pure (productVector x))

def amplitude {d k : ℕ} (x y : Fin k → CVec d) : ℝ :=
  ‖∏ j, ∑ i, conj (x j i) * y j i‖

/-- Partial trace in row-major tensor coordinates. -/
def partialTrace {d k : ℕ} (A : CMat (d ^ k)) (j : Fin k) : CMat d := fun a b =>
  ∑ I : Fin (d ^ k), if digit d k I.val j.val = a.val then
    if h : I.val - a.val * d ^ (k - 1 - j.val) + b.val * d ^ (k - 1 - j.val) < d ^ k then
      A I ⟨_, h⟩ else 0 else 0

/-- Local real orthonormal Hermitian basis: diagonal, symmetric, and imaginary antisymmetric.
The two off-diagonal entries have magnitude 1/sqrt(2). -/
def hermitianBasis (d : ℕ) (r : Fin (d * d)) : CMat d := fun a b =>
  let i := r.val / d
  let j := r.val % d
  if i = j then (if a.val = i ∧ b.val = i then 1 else 0)
  else if i < j then
    (if (a.val = i ∧ b.val = j) ∨ (a.val = j ∧ b.val = i) then
      (Real.sqrt 2 : ℂ)⁻¹ else 0)
  else if a.val = j ∧ b.val = i then Complex.I / (Real.sqrt 2 : ℂ)
  else if a.val = i ∧ b.val = j then -Complex.I / (Real.sqrt 2 : ℂ) else 0

def localCoordinates {d : ℕ} (A : CMat d) : Vec (d * d) :=
  WithLp.toLp 2 (fun r => hsInner A (hermitianBasis d r))

/-- All real coordinates of an arbitrary Hermitian operator in the tensor product of the
local orthonormal bases. No positivity or trace assumption is used. -/
def tensorCoordinates {d k : ℕ} (A : CMat (d ^ k)) : Tensor (List.replicate k (d * d)) :=
  WithLp.toLp 2 (fun I => hsInner A (productMatrix (fun j : Fin k =>
    if h : digit (d * d) k I.val j.val < d * d then hermitianBasis d ⟨_, h⟩ else 0)))

def encodeComplex (z : ℂ) : List ℝ := [z.re, z.im]
def encodeMatrix {n : ℕ} (A : CMat n) : List ℝ :=
  (List.ofFn fun i => (List.ofFn fun j => encodeComplex (A i j)).flatten).flatten

def encodeProducts {d k : ℕ} (x : Fin k → CVec d) : List ℝ :=
  (List.ofFn fun j => (List.ofFn fun i => encodeComplex (x j i)).flatten).flatten

def encodeMixture {d k T : ℕ} (S : Mixture d k T) : List ℝ :=
  List.ofFn S.weight ++ (List.ofFn fun l =>
    (List.ofFn fun j => encodeMatrix (S.factor l j)).flatten).flatten

def encodeSigned {d k T : ℕ} (K : SignedOperator d k T) : List ℝ :=
  List.ofFn K.coefficient ++ (List.ofFn fun l =>
    (List.ofFn fun j => encodeMatrix (K.factor l j)).flatten).flatten

/-- A subspace specified by a classical list of orthonormal product vectors. D=0 is allowed. -/
structure ProductSubspace (d k D : ℕ) where
  factors : Fin D → Fin k → CVec d
  unit : ∀ l, factors l ∈ unitProducts d k
  orthonormal : ∀ l r, (∑ i, conj (productVector (factors l) i) *
    productVector (factors r) i) = if l = r then 1 else 0

def ProductSubspace.projector {d k D : ℕ} (V : ProductSubspace d k D) : CMat (d ^ k) :=
  ∑ l, pure (productVector (V.factors l))

def ProductSubspace.lift {d k D : ℕ} (V : ProductSubspace d k D) (B : CMat D) : CMat (d ^ k) :=
  fun i j => ∑ l, ∑ r, productVector (V.factors l) i * B l r *
    conj (productVector (V.factors r) j)

def ProductSubspace.encode {d k D : ℕ} (V : ProductSubspace d k D) : List ℝ :=
  (List.ofFn fun l => encodeProducts (V.factors l)).flatten

def confidence (δ : ℝ) : ℝ := 1 + max 0 (Real.log δ⁻¹)
def inverseScale (ε : ℝ) : ℝ := 1 + ε⁻¹
def logSize (d : ℕ) : ℝ := 1 + Nat.clog 2 d

end NuclearTensor.Membership.Supplement


