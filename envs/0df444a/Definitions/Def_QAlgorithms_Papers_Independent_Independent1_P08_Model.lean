-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P08_Model
-- name    : QAlgorithms_Papers_Independent_Independent1_P08_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:14:47.110278+00:00
-- url     : https://prove2.me/theorems/2e5982d2-c57d-4999-8b8f-cf310837ab9a
-- title:
--   Qubit Entanglement Breaking Channels: supporting definitions
-- statement:
--   Reviewed paper-local supporting definitions and conventions. The attached text aggregates the existing blind readbacks of every definition; it makes no theorem proof claim.
-- source:
--   Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3. PDF SHA-256: dba60bd30b3ca1e23dac55f1e413d595e822e7d75c0dff71bf1b94f65337b81d. Exact locators remain in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
/-! Ruskai, Qubit Entanglement Breaking Channels, arXiv:quant-ph/0302032v3.
All locators are PDF pages. Convexity is real; ambiguous claims are in HARD.md. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P08

open QAlgorithms.Entanglement QAlgorithms.QubitChannels

abbrev QMap := Matrix Bool Bool ℂ →ₗ[ℂ] Matrix Bool Bool ℂ

abbrev Bloch := Fin 3 → ℝ

/-- Trace preservation on every operator, p.2. -/
def TracePreserving (Phi : QMap) : Prop := ∀ X, (Phi X).trace = X.trace

/-- CPT means completely positive and trace preserving, p.2. -/
def CPT (Phi : QMap) : Prop := TracePreserving Phi ∧ IsCompletelyPositive Phi

/-- EBT includes trace preservation, p.2; no characterization theorem assumed. -/
def EBT (Phi : QMap) : Prop := TracePreserving Phi ∧ IsEntanglementBreaking Phi

/-- The full real convex channel sets, pp.7,14. -/
def cptSet : Set QMap := {Phi | CPT Phi}

def ebtSet : Set QMap := {Phi | EBT Phi}

def cqSet : Set QMap := {Phi | IsCQMap Phi}

/-- Equation (3), in the ordered Pauli basis X,Y,Z, pp.2-3. -/
def canonical (t lam : Bloch) : QMap := blochAffineMap t (Matrix.diagonal lam)

/-- The Bloch matrix, p.2; arbitrary vectors need not give positive matrices. -/
def blochDensity (t : Bloch) : Matrix Bool Bool ℂ :=
  (2⁻¹ : ℂ) • (1 + ∑ j, (t j : ℂ) • sigma j)

/-- Euclidean length, not the function-space maximum norm, p.2. -/
def blochNorm (t : Bloch) : ℝ := Real.sqrt (∑ j, t j ^ 2)

/-- The normalized Bell state and Choi state of (4), p.4. -/
def bell : EuclideanSpace ℂ (Bool × Bool) := finiteMaxEntangled Bool

def choiState (Phi : QMap) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  idTensorSuperop Phi (pureDensity bell)

/-- Complex-linear transposition, p.3. -/
def transposeMap : QMap where
  toFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_smul' := by intro a X; rfl

/-- Independent input/output unitary bases, pp.2-3. -/
def changeBases (U V : Matrix.unitaryGroup Bool ℂ) (Phi : QMap) : QMap where
  toFun X := conjSuperop (V : Matrix Bool Bool ℂ) (Phi (conjSuperop (U : Matrix Bool Bool ℂ) X))
  map_add' X Y := by simp [conjSuperop, Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' a X := by simp [conjSuperop, Matrix.mul_smul, Matrix.smul_mul, map_smul]

/-- QC: orthogonal pure outputs, arbitrary input POVM, p.2. -/
def IsQC (Phi : QMap) : Prop :=
  ∃ U : Matrix.unitaryGroup Bool ℂ, ∃ F : Bool → Matrix Bool Bool ℂ,
    IsPOVM F ∧ Phi = holevoMap (fun b => pureDensity (act (U : Matrix Bool Bool ℂ) (ket b))) F

/-- Point channels are constant only on trace-one inputs, p.11. -/
def IsPoint (Phi : QMap) : Prop :=
  ∃ R : Matrix Bool Bool ℂ, IsDensityMatrix R ∧ ∀ X, Phi X = X.trace • R

/-- Nonnegative amplitude-damping parameterization, p.5. -/
def damping (a : ℝ) : QMap := canonical ![0, 0, 1-a^2] ![a, a, a^2]

/-- Trine POVM and output states of the explicit p.7 example. -/
def trineVector : Fin 3 → Bloch :=
  ![![1,0,0], ![-1/2,0,Real.sqrt 3/2], ![-1/2,0,-Real.sqrt 3/2]]

def trineEffect (k : Fin 3) : Matrix Bool Bool ℂ :=
  (3⁻¹ : ℂ) • (1 + ∑ j, (trineVector k j : ℂ) • sigma j)

def trineOutput (k : Fin 3) : Matrix Bool Bool ℂ := (2⁻¹ : ℂ) • (1+sigma k)

def trineChannel : QMap := holevoMap trineOutput trineEffect

/-- Fixed-coordinate unital EBT parameters and six vertices, p.12. -/
def unitalParameters : Set Bloch := {lam | CPT (canonical 0 lam) ∧ EBT (canonical 0 lam)}

def octahedronVertices : Set Bloch :=
  {lam | ∃ j : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ lam = Pi.single j s}

def lambdaRegion (t : Bloch) : Set Bloch := {lam | IsCompletelyPositive (canonical t lam)}

/-- Same-basis canonical CQ maps, p.16(a). -/
def canonicalCQ : Set QMap := {Phi | ∃ t lam, Phi = canonical t lam ∧ IsCQMap Phi}

def planarCQ (j : Fin 3) : Set QMap :=
  {Phi | ∃ t lam, Phi = canonical t lam ∧ IsCQMap Phi ∧ lam j = 0 ∧
    (Finset.univ.filter fun k => lam k ≠ 0).card ≤ 1}

/-- Four-dimensional fixed-t3, lambda3=0 slice, p.16(a). -/
def zeroThirdSlice (t3 : ℝ) : Set (Bloch × Bloch) :=
  {p | p.1 2 = t3 ∧ p.2 2 = 0 ∧ CPT (canonical p.1 p.2)}

/-- Planar EBT points in a fixed (t,lambda3) slice, p.17(c). -/
def planarSliceMaps (t : Bloch) (l3 : ℝ) : Set QMap :=
  {Phi | ∃ lam, Phi = canonical t lam ∧ EBT Phi ∧ lam 2 = l3 ∧ (lam 0 = 0 ∨ lam 1 = 0)}

/-- Same-basis summands after aligning translation with axis 1, p.17(d).
No nonzero lambda is fixed in these summands. -/
def axialCQ : Set QMap :=
  {Phi | ∃ t lam, Phi = canonical t lam ∧ IsCQMap Phi ∧
    ∃ j : Fin 3, j ≠ 0 ∧ t j = 0 ∧ lam j = 0}

/-- Computed Hilbert-Schmidt adjoint via matrix units, p.8. -/
def hsAdjoint (Phi : QMap) : QMap where
  toFun X := Matrix.of fun i j => ∑ a : Bool, ∑ b : Bool,
    star (Phi (Matrix.single i j 1) a b) * X a b
  map_add' X Y := by ext i j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c X := by ext i j; simp [Finset.mul_sum, mul_left_comm]; ring

/-- Unitary completion of computed adjoint Choi blocks, p.8 (12), p.14.
Unnormalized blocks avoid the missing factor 1/2 in (12); singular blocks require
no inverse. Verified also in cited arXiv:quant-ph/0101003v2, Theorem 7 and Lemma 8,
PDF p.13, including singular blocks. -/
def GeneralizedExtreme (Phi : QMap) : Prop :=
  CPT Phi ∧ ∃ R : Matrix.unitaryGroup Bool ℂ,
    hsAdjoint Phi (Matrix.single false true 1) =
      cfc Real.sqrt (hsAdjoint Phi (Matrix.single false false 1)) * (R : Matrix Bool Bool ℂ) *
        cfc Real.sqrt (hsAdjoint Phi (Matrix.single true true 1))

/-- Relative interior of a two-dimensional planar patch in S, p.15 Lemma 11(II). -/
def PlanarInterior (Phi : QMap) : Prop :=
  ∃ A B : QMap, LinearIndependent ℝ (![A,B] : Fin 2 → QMap) ∧
    ∃ r : ℝ, 0 < r ∧ ∀ x y : ℝ, x^2+y^2 < r^2 → CPT (Phi+x • A+y • B)

/-! Local sanity examples: basis order, zero inputs, adjoint orientation, real vertices. -/

example : blochNorm (0 : Bloch) = 0 := by simp [blochNorm]

example : trineVector 0 = ![1,0,0] := rfl

example : trineOutput 0 = (2⁻¹ : ℂ) • (1+pauliX) := rfl

example (X : Matrix Bool Bool ℂ) : transposeMap (transposeMap X) = X := rfl

example (Phi : QMap) : changeBases 1 1 Phi = Phi := by
  ext X i j
  simp [changeBases,conjSuperop]

example (Phi : QMap) : choiState Phi = idTensorSuperop Phi (pureDensity bell) := rfl

example : (0 : Bloch) ∉ octahedronVertices := by
  rintro ⟨j,s,hs,h⟩
  have he := congrFun h j
  simp only [Pi.zero_apply,Pi.single_eq_same] at he
  rcases hs with rfl | rfl <;> norm_num at he

example : hsAdjoint 0 = 0 := by ext X i j; simp [hsAdjoint]

example (j : Fin 3) (Phi : QMap) (h : Phi ∈ planarCQ j) : Phi ∈ canonicalCQ := by
  obtain ⟨t,lam,he,hcq,_,_⟩ := h
  exact ⟨t,lam,he,hcq⟩

example (t : Bloch) : canonical t 0 0 = 0 := map_zero _

example : (LinearMap.id : QMap) ∈ cptSet := by
  refine ⟨fun X => rfl, ?_⟩
  intro r X hX
  change X.PosSemidef
  exact hX

example : ¬ EBT (0 : QMap) := by
  intro h
  have ht := h.1 (1 : Matrix Bool Bool ℂ)
  norm_num [Matrix.trace_one] at ht

example (Phi : QMap) : Phi ∈ ebtSet ↔ EBT Phi := Iff.rfl

example (Phi : QMap) : Phi ∈ cqSet ↔ IsCQMap Phi := Iff.rfl

example : blochDensity 0 = (2⁻¹ : ℂ) • (1 : Matrix Bool Bool ℂ) := by
  simp [blochDensity]

example : bell (false,true) = 0 := by simp [bell,finiteMaxEntangled]

example : bell (false,false) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [bell,finiteMaxEntangled]

example (F : Bool → Matrix Bool Bool ℂ) (hF : IsPOVM F) :
    IsQC (holevoMap (fun b => pureDensity (ket b)) F) := by
  refine ⟨1,F,hF,?_⟩
  simp [act]

example (R : Matrix Bool Bool ℂ) (hR : IsDensityMatrix R) :
    IsPoint (holevoMap (fun _ : Unit => R) (fun _ => 1)) := by
  refine ⟨R,hR,?_⟩
  intro X
  simp [holevoMap]

example : damping 0 = canonical ![0,0,1] 0 := by
  have hz : (![0,0,0] : Bloch) = 0 := by ext i; fin_cases i <;> rfl
  simpa [damping,hz]

example : trineEffect 0 false false = 1/3 := by
  norm_num [trineEffect,trineVector,sigma,pauliX,pauliY,pauliZ,Fin.sum_univ_succ]

example : trineChannel = holevoMap trineOutput trineEffect := rfl

example (lam : Bloch) : lam ∈ unitalParameters ↔
    CPT (canonical 0 lam) ∧ EBT (canonical 0 lam) := Iff.rfl

example (t lam : Bloch) : lam ∈ lambdaRegion t ↔
    IsCompletelyPositive (canonical t lam) := Iff.rfl

example (t lam : Bloch) (h : IsCQMap (canonical t lam)) :
    canonical t lam ∈ canonicalCQ := ⟨t,lam,rfl,h⟩

example (t lam : Bloch) (h : CPT (canonical t lam)) (hz : lam 2 = 0) :
    (t,lam) ∈ zeroThirdSlice (t 2) := ⟨rfl,hz,h⟩

example (t lam : Bloch) (h : EBT (canonical t lam)) (hz : lam 0 = 0) :
    canonical t lam ∈ planarSliceMaps t (lam 2) := ⟨lam,rfl,h,rfl,Or.inl hz⟩

example (t lam : Bloch) (h : IsCQMap (canonical t lam)) (ht : t 1 = 0) (hl : lam 1 = 0) :
    canonical t lam ∈ axialCQ := ⟨t,lam,rfl,h,1,by decide,ht,hl⟩

example : hsAdjoint (LinearMap.id : QMap) = LinearMap.id := by
  ext X i j
  cases i <;> cases j <;> simp [hsAdjoint,Matrix.single_apply,eq_comm]

example : ¬ GeneralizedExtreme (0 : QMap) := by
  intro h
  have ht := h.1.1 (1 : Matrix Bool Bool ℂ)
  norm_num [Matrix.trace_one] at ht

example (Phi : QMap) (h : PlanarInterior Phi) : CPT Phi := by
  obtain ⟨A,B,_,r,hr,hball⟩ := h
  have hc := hball 0 0 (by nlinarith [sq_pos_of_pos hr])
  simpa using hc





















end QAlgorithms.Papers.Independent.Independent1.P08


