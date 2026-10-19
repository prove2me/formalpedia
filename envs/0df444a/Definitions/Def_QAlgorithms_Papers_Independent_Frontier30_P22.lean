-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P22
-- name    : QAlgorithms_Papers_Independent_Frontier30_P22
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:20:46.899403+00:00
-- url     : https://prove2.me/theorems/d96c4fba-3383-4120-af68-0a2bc6a7b2f9
-- title:
--   Definitions for Conditions for strictly purity-decreasing quantum Markovian dynamics
-- statement:
--   The objects the formalized statements of *Conditions for strictly purity-decreasing quantum Markovian dynamics* (arXiv:quant-ph/0411119) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finitePurity`: PDF p.1, Eq.(1): purity is the real trace of the square, on all matrix sizes.
--   - `finiteIdentityImage`: PDF p.2, Eq.(9): the identity image of the dissipator, also that of G.
--   - `finitePurityNonincreasing`: PDF pp.1–2: every initial density, and all pairs of forward times.
--   - `SelfAdjointHamiltonian`: PDF pp.1–2: an actual densely defined self-adjoint Hamiltonian. Symmetry and maximal adjoint domain together say that the operator equals its Hilbert adjoint; the action is defined only on its genuine linear domain.
--   - `RegularHamiltonianCommutator`: PDF pp.1–2, Eq.(6): the actual Hamiltonian commutator on its dense domain, with a trace-class bounded extension C. Only domain vectors are used to apply H. No trace-class condition on H rho or rho H separately is imposed: generator-domain states can have a well-defined commutator without either product being trace class.
--   - `hilbertPurity`: PDF p.1, Eq.(1): basis-independent on trace-class inputs and bounded products. Every theorem using this expression requires trace class; no divergent tsum is used.
--   - `HasTraceDerivative`: PDF pp.1–2: a right trace-norm derivative, rather than an operator-norm derivative. Membership guards prevent the total nuclear-norm formula from creating fake limits. The source requires differentiability only at regular generator-domain inputs.
--   - `boundedJumpTerm`: PDF p.1, Eq.(4): one bounded-jump dissipator with its exact one-half factor.
--   - `fockPurity`: PDF pp.1,3: the same purity in the full number basis, with no energy cutoff. It is used only on trace-class inputs or outputs explicitly certified below.
--   - `properIsometryGenerator`: PDF p.3: for an isometric jump V, Eq.(4) is X maps to V X V-adjoint minus X.
--   - `properIsometryEvolution`: PDF pp.1,3: the bounded generator's actual exponential, on the full Fock space.
--   - `properIsometryKraus`: A Kraus realization of exp(t(V(.)V-adjoint-id)), for t>=0. This records complete positivity and trace preservation in the accepted channel model.
--   - `dampingOutput`: PDF p.3: amplitude damping in Eq.(4)'s normalization has amplitude transmissivity exp(-t/2). The trace-norm sum is specified in the theorem, so the zero fallback is never treated as a physical output. Negative times are unused.
--   - `dampingGeneratorDyad`: PDF p.3: the F=a generator on |m><n|. Zero ladder coefficients handle m=0 or n=0, so truncated Nat subtraction does not create a spurious vacuum term.
--   - `dampingIdentityForm`: PDF p.3: the formal [a,a-adjoint] form from its number-basis coefficients. The coefficient is (n+1)-n, and the resulting bounded form extends to every Fock vector; a and a-adjoint themselves are not declared bounded operators.
-- source:
--   Conditions for strictly purity-decreasing quantum Markovian dynamics, arXiv:quant-ph/0411119v2, https://arxiv.org/abs/quant-ph/0411119v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Statements from Lidar, Shabani and Alicki, quant-ph/0411119v2.
Purity-decreasing means nonincreasing, as explicitly specified on PDF p.1.
The general unbounded theorem and nonlinear raising example are deferred in HARD.md.
All analytic sums below have convergence guards; compilation is pending batch handoff.
-/

noncomputable section

open Filter
open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P22

namespace TC

export QAlgorithms.Papers.Independent.Dependency50.P13 (operatorTrace IsPositive)

end TC

local notation "FD" => QAlgorithms.Papers.Independent.Dependency50.P16.LindbladData
local notation "finiteG" => QAlgorithms.Papers.Independent.Dependency50.P16.gkslGenerator
local notation "finiteEvolution" => QAlgorithms.Papers.Independent.Dependency50.P16.semigroupEvolution

/-- PDF p.1, Eq.(1): purity is the real trace of the square, on all matrix sizes. -/
def finitePurity {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (rho * rho).trace.re

/-- PDF p.2, Eq.(9): the identity image of the dissipator, also that of G. -/
def finiteIdentityImage {d : ℕ} (D : FD d) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ a, (D.jump a * (D.jump a)ᴴ - (D.jump a)ᴴ * D.jump a)

/-- PDF pp.1–2: every initial density, and all pairs of forward times. -/
def finitePurityNonincreasing {d : ℕ} (D : FD d) : Prop :=
  ∀ rho : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix rho →
    AntitoneOn (fun t : ℝ => finitePurity (finiteEvolution (finiteG D) t rho))
      (Set.Ici 0)

example {d : ℕ} : finitePurity (0 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
  simp [finitePurity]

example {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    finiteIdentityImage (⟨0, Fin.elim0, H, hH⟩ : FD d) = 0 := by
  simp [finiteIdentityImage]

section HilbertPurity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF pp.1–2: an actual densely defined self-adjoint Hamiltonian.
Symmetry and maximal adjoint domain together say that the operator equals its
Hilbert adjoint; the action is defined only on its genuine linear domain. -/
structure SelfAdjointHamiltonian where
  domain : Submodule ℂ H
  action : domain →ₗ[ℂ] H
  dense : Dense (domain : Set H)
  symmetric : ∀ x y : domain,
    inner ℂ (action x) (y : H) = inner ℂ (x : H) (action y)
  adjoint_domain : ∀ y z : H,
    (∀ x : domain, inner ℂ (action x) y = inner ℂ (x : H) z) →
      ∃ hy : y ∈ domain, action ⟨y, hy⟩ = z

/-- PDF pp.1–2, Eq.(6): the actual Hamiltonian commutator on its dense domain,
with a trace-class bounded extension C. Only domain vectors are used to apply H.
No trace-class condition on H rho or rho H separately is imposed: generator-domain
states can have a well-defined commutator without either product being trace class. -/
def RegularHamiltonianCommutator (K : SelfAdjointHamiltonian (H := H))
    (rho C : H →L[ℂ] H) : Prop :=
  QAlgorithms.Papers.Independent.Dependency50.P39.IsTraceClass C ∧
    ∀ v : K.domain, ∃ hv : rho (v : H) ∈ K.domain,
      K.action ⟨rho (v : H), hv⟩ - rho (K.action v) = C (v : H)

example (K : SelfAdjointHamiltonian (H := H)) (x y : K.domain) :
    inner ℂ (K.action x) (y : H) = inner ℂ (x : H) (K.action y) :=
  K.symmetric x y

example (K : SelfAdjointHamiltonian (H := H)) :
    RegularHamiltonianCommutator K 0 0 := by
  constructor
  · refine ⟨fun _ => 0, fun _ => 0, ?_⟩
    simp [QAlgorithms.Papers.Independent.Dependency50.P39.NuclearExpansion]
  · intro v
    refine ⟨by simp, ?_⟩
    simp
    exact K.action.map_zero

/-- PDF p.1, Eq.(1): basis-independent on trace-class inputs and bounded products.
Every theorem using this expression requires trace class; no divergent tsum is used. -/
def hilbertPurity {I : Type*} (b : HilbertBasis I ℂ H) (rho : H →L[ℂ] H) : ℝ :=
  (TC.operatorTrace b (rho * rho)).re

/-- PDF pp.1–2: a right trace-norm derivative, rather than an operator-norm derivative.
Membership guards prevent the total nuclear-norm formula from creating fake limits.
The source requires differentiability only at regular generator-domain inputs. -/
def HasTraceDerivative (rho : ℝ → H →L[ℂ] H) (V : H →L[ℂ] H) (t : ℝ) : Prop :=
  (∀ s, QAlgorithms.Papers.Independent.Dependency50.P39.IsTraceClass (rho s)) ∧
  QAlgorithms.Papers.Independent.Dependency50.P39.IsTraceClass V ∧
  (∀ h : ℝ, 0 < h → QAlgorithms.Papers.Independent.Dependency50.P39.IsTraceClass
    ((h : ℂ)⁻¹ • (rho (t + h) - rho t) - V)) ∧
  Tendsto (fun h : ℝ => QAlgorithms.Papers.Independent.Dependency50.P39.nuclearTraceNorm
    ((h : ℂ)⁻¹ • (rho (t + h) - rho t) - V))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

example (rho : ℝ → H →L[ℂ] H) (V : H →L[ℂ] H) (t : ℝ)
    (h : HasTraceDerivative rho V t) :
    QAlgorithms.Papers.Independent.Dependency50.P39.IsTraceClass V := h.2.1

/-- PDF p.1, Eq.(4): one bounded-jump dissipator with its exact one-half factor. -/
def boundedJumpTerm (F rho : H →L[ℂ] H) : H →L[ℂ] H :=
  F * rho * F.adjoint - (1 / 2 : ℂ) •
    (F.adjoint * F * rho + rho * F.adjoint * F)

example {I : Type*} (b : HilbertBasis I ℂ H) :
    hilbertPurity b (0 : H →L[ℂ] H) = 0 := by
  simp [hilbertPurity, TC.operatorTrace]

example (F : H →L[ℂ] H) : boundedJumpTerm F 0 = 0 := by
  simp [boundedJumpTerm]

end HilbertPurity

local notation "Fock" => QAlgorithms.Papers.Independent.Dependency50.P39.Fock
local notation "BOp" => QAlgorithms.Papers.Independent.Dependency50.P39.FockOperator
local notation "fockKet" => QAlgorithms.Papers.Independent.Dependency50.P39.fockKet
local notation "fockDyad" => QAlgorithms.Papers.Independent.Dependency50.P39.fockDyad
local notation "IsDensity" => QAlgorithms.Papers.Independent.Dependency50.P39.IsDensity
local notation "IsTraceClass" => QAlgorithms.Papers.Independent.Dependency50.P39.IsTraceClass
local notation "TraceHasSum" => QAlgorithms.Papers.Independent.Dependency50.P39.TraceHasSum
local notation "traceNorm" => QAlgorithms.Papers.Independent.Dependency50.P39.nuclearTraceNorm
local notation "krausTerm" => QAlgorithms.Papers.Independent.Dependency50.P39.krausTerm
local notation "attenuatorKraus" => QAlgorithms.Papers.Independent.Dependency50.P39.attenuatorKraus

/-- PDF pp.1,3: the same purity in the full number basis, with no energy cutoff.
It is used only on trace-class inputs or outputs explicitly certified below. -/
def fockPurity (X : BOp) : ℝ :=
  (∑' n : ℕ, (X * X) (fockKet n) n).re

/-- PDF p.3: for an isometric jump V, Eq.(4) is X maps to V X V-adjoint minus X. -/
def properIsometryGenerator (V : BOp) : BOp →L[ℂ] BOp :=
  ContinuousLinearMap.mulLeftRight ℂ BOp V V.adjoint - ContinuousLinearMap.id ℂ BOp

/-- PDF pp.1,3: the bounded generator's actual exponential, on the full Fock space. -/
def properIsometryEvolution (V : BOp) (t : ℝ) : BOp →L[ℂ] BOp := by
  letI : NormedRing (BOp →L[ℂ] BOp) := ContinuousLinearMap.toNormedRing
  exact NormedSpace.exp ((t : ℂ) • properIsometryGenerator V)

/-- A Kraus realization of exp(t(V(.)V-adjoint-id)), for t>=0.
This records complete positivity and trace preservation in the accepted channel model. -/
def properIsometryKraus (V : BOp) (t : ℝ) (n : ℕ) : BOp :=
  (Real.exp (-t / 2) * Real.sqrt (t ^ n / (Nat.factorial n : ℝ)) : ℂ) • V ^ n

example : fockPurity (0 : BOp) = 0 := by
  simp [fockPurity]

example : properIsometryGenerator (0 : BOp) = -ContinuousLinearMap.id ℂ BOp := by
  simp [properIsometryGenerator]

example (V : BOp) (X : BOp) :
    properIsometryGenerator V X = V * X * V.adjoint - X := rfl

example (V : BOp) : properIsometryEvolution V 0 = ContinuousLinearMap.id ℂ BOp := by
  letI : NormedRing (BOp →L[ℂ] BOp) := ContinuousLinearMap.toNormedRing
  simpa only [properIsometryEvolution, Complex.ofReal_zero, zero_smul,
    ContinuousLinearMap.one_def] using
    (NormedSpace.exp_zero (𝔸 := BOp →L[ℂ] BOp))

example (V : BOp) : properIsometryKraus V 0 0 = 1 := by
  simp [properIsometryKraus]

/-- PDF p.3: amplitude damping in Eq.(4)'s normalization has amplitude
transmissivity exp(-t/2). The trace-norm sum is specified in the theorem, so the
zero fallback is never treated as a physical output. Negative times are unused. -/
def dampingOutput (t : ℝ) (X : BOp) : BOp := by
  classical
  exact if h : ∃ Y : BOp, TraceHasSum
      (fun n => krausTerm (attenuatorKraus (Real.exp (-t / 2)) n) X) Y then
    Classical.choose h
  else 0

/-- PDF p.3: the F=a generator on |m><n|. Zero ladder coefficients handle
m=0 or n=0, so truncated Nat subtraction does not create a spurious vacuum term. -/
def dampingGeneratorDyad (m n : ℕ) : BOp :=
  (Real.sqrt ((m : ℝ) * n) : ℂ) • fockDyad (m - 1) (n - 1) -
    ((((m : ℝ) + (n : ℝ)) / 2 : ℝ) : ℂ) • fockDyad m n

/-- PDF p.3: the formal [a,a-adjoint] form from its number-basis coefficients.
The coefficient is (n+1)-n, and the resulting bounded form extends to every
Fock vector; a and a-adjoint themselves are not declared bounded operators. -/
def dampingIdentityForm (v : Fock) : ℝ :=
  ∑' n : ℕ, ((Real.sqrt ((n : ℝ) + 1)) ^ 2 - (Real.sqrt (n : ℝ)) ^ 2) * ‖v n‖ ^ 2

example (t : ℝ) (X : BOp)
    (h : ∃ Y : BOp, TraceHasSum
      (fun n => krausTerm (attenuatorKraus (Real.exp (-t / 2)) n) X) Y) :
    dampingOutput t X = Classical.choose h := by
  classical
  simp only [dampingOutput, dif_pos h]

example : dampingGeneratorDyad 0 0 = 0 := by
  simp [dampingGeneratorDyad]

example : dampingIdentityForm (0 : Fock) = 0 := by
  simp [dampingIdentityForm]

end QAlgorithms.Papers.Independent.Frontier30.P22


