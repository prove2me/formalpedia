-- Prove2me | Definitions.Def_QAlgorithms_Defs_GroverPolynomial
-- name    : QAlgorithms_Defs_GroverPolynomial
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:13:26.995864+00:00
-- url     : https://prove2.me/theorems/4abef847-36bd-421c-8d48-4c829541c7be
-- title:
--   GroverPolynomial
-- statement:
--   GroverPolynomial
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\GroverPolynomial.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- Finite classical labels psi,psiPerp,pi,piPerp select the frame's four states. Source: arxiv-2207.08628v3 PDF p.5; arxiv-2207.08628v3 PDF p.14. -/
inductive GroverLabel where
  | psi
  | psiPerp
  | pi
  | piPerp
  deriving DecidableEq

/-- Represent the source's two orthonormal signal bases and their four known classical labels. Source: arxiv-2207.08628v3 PDF p.5; arxiv-2207.08628v3 PDF p.6; arxiv-2207.08628v3 PDF p.14. -/
structure GroverFrame where
  basis : Matrix.unitaryGroup Bool ℂ
  amplitude : Set.Icc (0 : ℝ) 1

/-- Operational helper GroverFrame.state for the source construction. Source: arxiv-2207.08628v3 PDF p.5; arxiv-2207.08628v3 PDF p.6; arxiv-2207.08628v3 PDF p.14. -/
def GroverFrame.state (F : GroverFrame) (label : GroverLabel) : EuclideanSpace ℂ Bool :=
  let piState := act (F.basis : Matrix Bool Bool ℂ) (ket false)
  let piPerpState := act (F.basis : Matrix Bool Bool ℂ) (ket true)
  match label with
  | .pi => piState
  | .piPerp => piPerpState
  | .psi => (F.amplitude.val : ℂ) • piState +
      (Real.sqrt (1 - F.amplitude.val ^ 2) : ℂ) • piPerpState
  | .psiPerp => (Real.sqrt (1 - F.amplitude.val ^ 2) : ℂ) • piState -
      (F.amplitude.val : ℂ) • piPerpState
/-- For a normalized ψ and orthogonal projector Π, a:=‖act Π ψ‖, abar:=sqrt(1-a²). Source: arxiv-2207.08628v3 PDF p.5. -/
def groverAmplitude {ι : Type*} [Fintype ι] [DecidableEq ι]
    (psi : EuclideanSpace ℂ ι) (Pi : Matrix ι ι ℂ) : ℝ := ‖act Pi psi‖

/-- Zψ:=pureDensity ψ-pureDensity ψperp and ZΠ:=pureDensity Πket-pureDensity Πperp on the completed signal space, eqs. Source: arxiv-2207.08628v3 PDF p.6. -/
def groverBasisReflection (F : GroverFrame) (piBasis : Bool) : Matrix Bool Bool ℂ :=
  if piBasis then pureDensity (F.state .pi) - pureDensity (F.state .piPerp)
  else pureDensity (F.state .psi) - pureDensity (F.state .psiPerp)

/-- For each real φ, exp(+iφ Zψ), exp(+iφ ZΠ) on the signal space, equivalently diagonal phases exp(+iφ),exp(-iφ) in each Grover basis. Source: arxiv-2207.08628v3 PDF p.6; arxiv-2207.08628v3 PDF p.9. -/
def groverRotationOracle (F : GroverFrame) (piBasis : Bool) (phi : ℝ) : Matrix Bool Bool ℂ :=
  NormedSpace.exp ((Complex.I * (phi : ℂ)) • groverBasisReflection F piBasis)

/-- On a flag qubit first and signal second, exp(iφZ)⊕exp(-iφZ):=|0⟩⟨0|⊗exp(iφZ)+|1⟩⟨1|⊗exp(-iφZ), for Zψ and ZΠ. Source: arxiv-2207.08628v3 PDF p.12. -/
def oppositeAngleOracle (F : GroverFrame) (piBasis : Bool) (phi : ℝ) :
    Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then
    groverRotationOracle F piBasis (if p.1 then -phi else phi) p.2 q.2 else 0

/-- Predicate on P,Q : Polynomial ℂ: (HasParity P 0 ∧ HasParity Q 1) ∨ (HasParity P 1 ∧ HasParity Q 0), together with ∀x∈[-1,1], ‖P.eval(x:ℂ)‖²+(1-x²)*‖Q.eval(x:ℂ)‖²=1. Source: arxiv-2207.08628v3 PDF p.8. -/
def IsPellPair (P Q : Polynomial ℂ) : Prop :=
  ((HasParity P 0 ∧ HasParity Q 1) ∨ (HasParity P 1 ∧ HasParity Q 0)) ∧
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖P.eval (x : ℂ)‖ ^ 2 + (1 - x ^ 2) * ‖Q.eval (x : ℂ)‖ ^ 2 = 1

/-- P : Polynomial ℂ is Pellian iff ∃Q : Polynomial ℂ, PellPair P Q. Source: arxiv-2207.08628v3 PDF p.8. -/
def IsPellian (P : Polynomial ℂ) : Prop := ∃ Q, IsPellPair P Q

/-- Polynomial ℝ obtained by taking the real part of each complex coefficient (equivalently on real x its evaluation is Re(P.eval(x:ℂ))). Source: arxiv-2207.08628v3 PDF p.12. -/
def realPartPolynomial (P : Polynomial ℂ) : Polynomial ℝ :=
  ∑ j ∈ P.support, Polynomial.monomial j (P.coeff j).re

/-- P : Polynomial ℝ is semi-Pellian iff ∃Ptilde : Polynomial ℂ, Pellian Ptilde ∧ realPartPoly Ptilde=P. Source: arxiv-2207.08628v3 PDF p.12. -/
def IsSemiPellian (P : Polynomial ℝ) : Prop :=
  ∃ Q : Polynomial ℂ, IsPellian Q ∧ realPartPolynomial Q = P

/-- Sanity test. Source: arxiv-2207.08628v3 PDF p.5; arxiv-2207.08628v3 PDF p.6; arxiv-2207.08628v3 PDF p.14. -/
example : IsPellPair 1 0 := by
  refine ⟨Or.inl ⟨by simp [HasParity], by simp [HasParity]⟩, ?_⟩
  intro x hx
  simp

/-- Sanity test. Source: arxiv-2207.08628v3 PDF p.5; arxiv-2207.08628v3 PDF p.6; arxiv-2207.08628v3 PDF p.14. -/
example (F : GroverFrame) (p : Bool) : groverRotationOracle F p 0 = 1 := by
  simp [groverRotationOracle]

/-- Sanity test. Source: arxiv-2207.08628v3 PDF p.5; arxiv-2207.08628v3 PDF p.6; arxiv-2207.08628v3 PDF p.14. -/
example : realPartPolynomial (Polynomial.C Complex.I) = 0 := by
  simp [realPartPolynomial]

/-- Endpoint completion is a ray convention. Source: arxiv-2207.08628v3 PDF p.6. -/
example (F : GroverFrame) (h : F.amplitude.val = 0) : F.state .psi = F.state .piPerp := by
  simp [GroverFrame.state, h]

/-- At amplitude one the complementary vector may differ by a minus phase.
Source: arxiv-2207.08628v3 PDF p.6. -/
example (F : GroverFrame) (h : F.amplitude.val = 1) : F.state .psiPerp = -F.state .piPerp := by
  simp [GroverFrame.state, h]

/-- The frame stores a genuine unitary basis. Source: arxiv-2207.08628v3 PDF pp.5–6. -/
example (F : GroverFrame) : IsState (F.state .pi) := by
  change ‖act (F.basis : Matrix Bool Bool ℂ) (ket false)‖ = 1
  rw [act_norm_of_mem_unitaryGroup F.basis.property]
  simp [ket]

end QAlgorithms


