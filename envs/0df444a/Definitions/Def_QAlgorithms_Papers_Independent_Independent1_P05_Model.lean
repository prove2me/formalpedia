-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
-- name    : QAlgorithms_Papers_Independent_Independent1_P05_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:28:07.510644+00:00
-- url     : https://prove2.me/theorems/feb50ad2-eb54-43bb-a56f-526c47cb50da
-- title:
--   NLTS Hamiltonians from good quantum codes: supporting definitions
-- statement:
--   Reviewed paper-local supporting definitions and conventions. The attached text aggregates the existing blind readbacks of every definition; it makes no theorem proof claim.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4. PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d. Exact locators remain in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P05

open PresentedCSS

/-- Source binary words, with addition over F_2 (PDF p.2). -/
abbrev NLTSWord (n : ℕ) := Fin n → ZMod 2

/-- Measurement mass in the standard or product-Hadamard basis (PDF p.3). -/
def nltsMass {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (had : Bool) (S : Finset (NLTSWord n)) : ℝ :=
  ∑ y ∈ S, densityProb (if had then hadamardN n*rho*star (hadamardN n) else rho)
    (bitsOfZMod y)

/-- Approximate words: the threshold uses the actual check-row count (PDF p.2). -/
def nltsApprox {n mx mz : ℕ} (C : CheckPresentation n mx mz) (had : Bool)
    (delta : ℝ) : Finset (NLTSWord n) :=
  Finset.univ.filter fun y => if had then (hammingNorm (C.HX.mulVec y) : ℝ) ≤ delta*mx
    else (hammingNorm (C.HZ.mulVec y) : ℝ) ≤ delta*mz

/-- Stabilizers modulo which each side measures reduced weight (PDF p.2). -/
def nltsOppositeDual {n mx mz : ℕ} (C : CheckPresentation n mx mz) (had : Bool) :
    Submodule (ZMod 2) (NLTSWord n) :=
  if had then codeDual C.Cz else codeDual C.Cx

/-- The computed close-pair relation of Section 2 (PDF p.4). -/
def nltsRelated {n mx mz : ℕ} (C : CheckPresentation n mx mz) (c1 eps1 : ℝ)
    (had : Bool) (x y : NLTSWord n) : Prop :=
  (NLTS.reducedHammingWeight (nltsOppositeDual C had) (x+y) : ℝ) ≤ 2*c1*eps1*n

/-- A computed class restricted to approximate codewords (PDF p.4). -/
def nltsClass {n mx mz : ℕ} (C : CheckPresentation n mx mz) (c1 eps1 : ℝ)
    (had : Bool) (x : NLTSWord n) : Finset (NLTSWord n) :=
  (nltsApprox C had eps1).filter (nltsRelated C c1 eps1 had x)

/-- Distinct computed classes, rather than a partition supplied as data (PDF p.4). -/
def nltsClasses {n mx mz : ℕ} (C : CheckPresentation n mx mz) (c1 eps1 : ℝ)
    (had : Bool) : Finset (Finset (NLTSWord n)) :=
  (nltsApprox C had eps1).image (nltsClass C c1 eps1 had)

/-- A finite union of clusters (PDF pp.4--5). -/
def nltsClusterUnion {n : ℕ} (M : Finset (Finset (NLTSWord n))) : Finset (NLTSWord n) :=
  M.biUnion id

/-- Definition 6, PDF p.5: expansion on a specified subset; n is the column count. -/
def nltsExpanding {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (V : Set (NLTSWord n)) (alpha beta : ℝ) : Prop :=
  ∀ x ∈ V, (hammingNorm x : ℝ) ≤ alpha*n →
    beta*(hammingNorm x : ℝ) ≤ hammingNorm (A.mulVec x)

/-- Definition 7, PDF p.5: the syndrome threshold also uses the column count. -/
def nltsClustering {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (V : Set (NLTSWord n)) (delta mu nu : ℝ) : Prop :=
  ∀ x ∈ V, (hammingNorm (A.mulVec x) : ℝ) ≤ delta*n →
    (hammingNorm x : ℝ) ≤ mu*n ∨ nu*n ≤ hammingNorm x

/-- The minimal representatives V_z^delta and V_x^delta constructed on PDF p.6. -/
def nltsMinimal {n mx mz : ℕ} (C : CheckPresentation n mx mz) (had : Bool)
    (delta : ℝ) : Set (NLTSWord n) :=
  {y | y ∈ nltsApprox C had delta ∧ ∀ s ∈ nltsOppositeDual C had,
    hammingNorm y ≤ hammingNorm (y+s)}

/-- Public CSS check matrices, with no expansion or NLTS guarantee as data. -/
structure NLTSCheckFamily where
  rowsX : ℕ → ℕ
  rowsZ : ℕ → ℕ
  checks : (n : ℕ) → CheckPresentation n (rowsX n) (rowsZ n)

/-- Finite descriptions include actual row counts. Explicit in Theorem 1 (PDF p.2)
is interpreted as deterministic polynomial-time generation from unary n. -/
def nltsCheckEncoding {n mx mz : ℕ} (C : CheckPresentation n mx mz) : Complexity.Str :=
  LocalHamiltonian.encBin n ++ LocalHamiltonian.encBin mx ++ LocalHamiltonian.encBin mz ++
    (List.ofFn fun i : Fin mx => List.ofFn fun j : Fin n => decide (C.HX i j = 1)).flatten ++
    (List.ofFn fun i : Fin mz => List.ofFn fun j : Fin n => decide (C.HZ i j = 1)).flatten

/-- Actual local projectors, including dependent or zero rows (PDF p.2). -/
def nltsTerms {n mx mz : ℕ} (C : CheckPresentation n mx mz) :
    Fin (mx+mz) → Matrix (Qubits n) (Qubits n) ℂ :=
  Fin.addCases (fun i => (2⁻¹ : ℂ) • (1-NLTS.rowOperator true (C.HX i)))
    (fun i => (2⁻¹ : ℂ) • (1-NLTS.rowOperator false (C.HZ i)))

example {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ) (had : Bool) :
    nltsMass rho had ∅ = 0 := by simp [nltsMass]

example {n mx mz : ℕ} (C : CheckPresentation n mx mz) :
    nltsOppositeDual C false = codeDual C.Cx := rfl

example {n mx mz : ℕ} (C : CheckPresentation n mx mz) :
    nltsOppositeDual C true = codeDual C.Cz := rfl

example {n mx mz : ℕ} (C : CheckPresentation n mx mz) (had : Bool) :
    (0 : NLTSWord n) ∈ nltsApprox C had 0 := by
  cases had <;> simp [nltsApprox]

example {n mx mz : ℕ} (C : CheckPresentation n mx mz) (c1 eps1 : ℝ) (had : Bool)
    (x y : NLTSWord n) : y ∈ nltsClass C c1 eps1 had x ↔
      y ∈ nltsApprox C had eps1 ∧ nltsRelated C c1 eps1 had x y := by
  simp [nltsClass]

example {n mx mz : ℕ} (C : CheckPresentation n mx mz) (c1 eps1 : ℝ) (had : Bool)
    (x : NLTSWord n) (hx : x ∈ nltsApprox C had eps1) :
    nltsClass C c1 eps1 had x ∈ nltsClasses C c1 eps1 had :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

example {n : ℕ} (S : Finset (NLTSWord n)) : nltsClusterUnion {S} = S := by
  simp [nltsClusterUnion]

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (a b : ℝ) :
    nltsExpanding A ∅ a b := by intro x hx; exact False.elim hx

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (d u v : ℝ) :
    nltsClustering A ∅ d u v := by intro x hx; exact False.elim hx

example {n mx mz : ℕ} (C : CheckPresentation n mx mz) (had : Bool) :
    (0 : NLTSWord n) ∈ nltsMinimal C had 0 := by
  refine ⟨?_,fun s _ => ?_⟩
  · cases had <;> simp [nltsApprox]
  · simp

example {n mx mz : ℕ} (C : CheckPresentation n mx mz) (i : Fin mx) :
    nltsTerms C (Fin.castAdd mz i) = (2⁻¹ : ℂ) • (1-NLTS.rowOperator true (C.HX i)) := by
  simp [nltsTerms]

example {n mx mz : ℕ} (C : CheckPresentation n mx mz) :
    nltsCheckEncoding C = LocalHamiltonian.encBin n ++ LocalHamiltonian.encBin mx ++
      LocalHamiltonian.encBin mz ++
      (List.ofFn fun i : Fin mx => List.ofFn fun j : Fin n => decide (C.HX i j = 1)).flatten ++
      (List.ofFn fun i : Fin mz => List.ofFn fun j : Fin n => decide (C.HZ i j = 1)).flatten := rfl










end QAlgorithms.Papers.Independent.Independent1.P05


