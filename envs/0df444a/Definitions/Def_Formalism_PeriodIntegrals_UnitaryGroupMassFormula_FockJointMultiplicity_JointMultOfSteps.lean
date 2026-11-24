-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:29:21.33706+00:00
-- url     : https://prove2.me/theorems/779947dc-b91c-4323-8590-7d0ef0e66d7f
-- title:
--   Joint Mult Of Steps
-- statement:
--   Definitions and structural lemmas for Joint Mult Of Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/JointMultOfSteps.lean

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
namespace PI.FJM
def JH (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) : Submodule ℂ (Pol p q r s) :=
  hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (Jset p q r s)
def Exist : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  JointShape p q r s μ μ' → ∃ P ∈ JH p q r s μ μ', P ≠ 0
def ShapeOf : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  ∀ P ∈ JH p q r s μ μ', P ≠ 0 → JointShape p q r s μ μ'
def RankLe : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  JointShape p q r s μ μ' → ∃ v : Pol p q r s, JH p q r s μ μ' ≤ Submodule.span ℂ {v}
def dd {p q r s : ℕ} (l l' : Ln p q r s) : Module.End ℂ (Pol p q r s) :=
  (MvPolynomial.pderiv l).toLinearMap * (MvPolynomial.pderiv l').toLinearMap
def lapA {p q r s : ℕ} (i : Fin p) (j : Fin q) : Module.End ℂ (Pol p q r s) :=
  ∑ l : Fin s, dd (Sum.inl i, Sum.inr l) (Sum.inr j, Sum.inr l)
def lapB {p q r s : ℕ} (i : Fin p) (j : Fin q) : Module.End ℂ (Pol p q r s) :=
  ∑ k : Fin r, dd (Sum.inl i, Sum.inl k) (Sum.inr j, Sum.inl k)
def lapC {p q r s : ℕ} (k : Fin r) (l : Fin s) : Module.End ℂ (Pol p q r s) :=
  ∑ i : Fin p, dd (Sum.inl i, Sum.inl k) (Sum.inl i, Sum.inr l)
def lapD {p q r s : ℕ} (k : Fin r) (l : Fin s) : Module.End ℂ (Pol p q r s) :=
  ∑ j : Fin q, dd (Sum.inr j, Sum.inl k) (Sum.inr j, Sum.inr l)
def FormJ : Prop := ∀ (p q r s : ℕ) (P : Pol p q r s),
  P ∈ Jset p q r s ↔ (∀ i j, lapA (r := r) (s := s) i j P = 0) ∧ (∀ i j, lapB (r := r) (s := s) i j P = 0) ∧
    (∀ k l, lapC (p := p) (q := q) k l P = 0) ∧ (∀ k l, lapD (p := p) (q := q) k l P = 0)
def wt1 {p q r s : ℕ} (m : Ln p q r s →₀ ℕ) (a : Ix p q) : ℤ :=
  ∑ c : Ix r s, if linePos (a, c) then (m (a, c) : ℤ) else -(m (a, c) : ℤ)
def wt2 {p q r s : ℕ} (m : Ln p q r s →₀ ℕ) (c : Ix r s) : ℤ :=
  ∑ a : Ix p q, if linePos (a, c) then (m (a, c) : ℤ) else -(m (a, c) : ℤ)
def sh1 (p q r s : ℕ) : Ix p q → ℚ := Sum.elim (fun _ => cPair r s) (fun _ => -cPair r s)
def sh2 (p q r s : ℕ) : Ix r s → ℚ := Sum.elim (fun _ => cPair p q) (fun _ => -cPair p q)
def FormWt1 : Prop := ∀ (p q r s : ℕ) (a : Ix p q) (m : Ln p q r s →₀ ℕ),
  fockAct1 p q r s (Eab a a) (MvPolynomial.monomial m 1) =
    (((wt1 m a : ℚ) + sh1 p q r s a : ℚ) : ℂ) • MvPolynomial.monomial m 1
def FormWt2 : Prop := ∀ (p q r s : ℕ) (c : Ix r s) (m : Ln p q r s →₀ ℕ),
  fockAct2 p q r s (Eab c c) (MvPolynomial.monomial m 1) =
    (((wt2 m c : ℚ) + sh2 p q r s c : ℚ) : ℂ) • MvPolynomial.monomial m 1
def rai1 {p q r s : ℕ} (a b : Ix p q) : Module.End ℂ (Pol p q r s) :=
  ∑ c : Ix r s, raiB (a, c) * lowB (b, c)
def rai2 {p q r s : ℕ} (c d : Ix r s) : Module.End ℂ (Pol p q r s) :=
  ∑ a : Ix p q, raiB (a, c) * lowB (a, d)
def FormRaise1 : Prop := ∀ (p q r s : ℕ) (a b : Ix p q), a ≠ b →
  fockAct1 p q r s (Eab a b) = rai1 (r := r) (s := s) a b
def FormRaise2 : Prop := ∀ (p q r s : ℕ) (c d : Ix r s), c ≠ d →
  fockAct2 p q r s (Eab c d) = rai2 (p := p) (q := q) c d
def varMat {p q r s m k : ℕ} (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) :
    Matrix (Fin m) (Fin k) (Pol p q r s) :=
  Matrix.of fun i j => MvPolynomial.X (ρ i, κ j)
def leadT {R : Type*} [CommRing R] {m k : ℕ} (M : Matrix (Fin m) (Fin k) R) (t : ℕ) : R :=
  if h : t ≤ m ∧ t ≤ k then (M.submatrix (Fin.castLE h.1) (Fin.castLE h.2)).det else 0
def shapeProd {R : Type*} [CommRing R] {m k : ℕ} (M : Matrix (Fin m) (Fin k) R) (α : List ℕ) : R :=
  ∏ t ∈ Finset.range α.length, leadT M (t + 1) ^ (α.getD t 0 - α.getD (t + 1) 0)
def ShapeData (p q r s : ℕ) (a b c d : List ℤ) : Prop :=
  (∀ v ∈ a, 0 < v) ∧ (∀ v ∈ c, 0 < v) ∧ (∀ v ∈ b, v < 0) ∧ (∀ v ∈ d, v < 0) ∧
    a.Pairwise (· ≥ ·) ∧ b.Pairwise (· ≥ ·) ∧ c.Pairwise (· ≥ ·) ∧ d.Pairwise (· ≥ ·) ∧
    a.length + b.length ≤ p ∧ c.length + d.length ≤ q ∧
    a.length + d.length ≤ r ∧ c.length + b.length ≤ s
def posPart (a : List ℤ) : List ℕ := a.map Int.toNat
def negPart (b : List ℤ) : List ℕ := (b.map fun v => (-v).toNat).reverse
def hwVec (p q r s : ℕ) (a b c d : List ℤ) : Pol p q r s :=
  shapeProd (varMat (fun i : Fin p => (Sum.inl i : Ix p q)) (fun k : Fin r => (Sum.inl k : Ix r s))) (posPart a) *
  shapeProd (varMat (fun i : Fin p => (Sum.inl (Fin.rev i) : Ix p q))
    (fun l : Fin s => (Sum.inr (Fin.rev l) : Ix r s))) (negPart b) *
  shapeProd (varMat (fun j : Fin q => (Sum.inr j : Ix p q)) (fun l : Fin s => (Sum.inr l : Ix r s))) (posPart c) *
  shapeProd (varMat (fun j : Fin q => (Sum.inr (Fin.rev j) : Ix p q))
    (fun k : Fin r => (Sum.inl (Fin.rev k) : Ix r s))) (negPart d)
def wtOf1 (p q r s : ℕ) (a b c d : List ℤ) : Ix p q → ℚ := fun i =>
  ofBlocks (pad a (p - a.length - b.length) b) (pad c (q - c.length - d.length) d) i + sh1 p q r s i
def wtOf2 (p q r s : ℕ) (a b c d : List ℤ) : Ix r s → ℚ := fun i =>
  ofBlocks (pad a (r - a.length - d.length) d) (pad c (s - c.length - b.length) b) i + sh2 p q r s i
def VecNe : Prop := ∀ (p q r s : ℕ) (a b c d : List ℤ), ShapeData p q r s a b c d → hwVec p q r s a b c d ≠ 0
def VecJ : Prop := ∀ (p q r s : ℕ) (a b c d : List ℤ), ShapeData p q r s a b c d →
  hwVec p q r s a b c d ∈ Jset p q r s
def VecHW1 : Prop := ∀ (p q r s : ℕ) (a b c d : List ℤ), ShapeData p q r s a b c d →
  hwVec p q r s a b c d ∈ hwSub (fockAct1 p q r s) (wtOf1 p q r s a b c d)
def VecHW2 : Prop := ∀ (p q r s : ℕ) (a b c d : List ℤ), ShapeData p q r s a b c d →
  hwVec p q r s a b c d ∈ hwSub (fockAct2 p q r s) (wtOf2 p q r s a b c d)
end PI.FJM


