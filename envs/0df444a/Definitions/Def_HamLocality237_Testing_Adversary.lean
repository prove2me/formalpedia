-- Prove2me | Definitions.Def_HamLocality237_Testing_Adversary
-- name    : HamLocality237_Testing_Adversary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:37:42.144103+00:00
-- url     : https://prove2.me/theorems/45be7fc3-85bd-40fe-8a8c-66cf937556db
-- title:
--   The hard spectral law, input registers, and correction operators
-- statement:
--   Let $b$ and $M$ be the normalized bump and multiplication operator on $L^2([-1/2,1/2])$. The single input register is the Hilbert direct sum $\mathbb C\oplus L^2([-1/2,1/2])$, with distinguished vector $|\perp\rangle=(1,0)$ and
--
--   $$J_\varepsilon(q,r)=(\varepsilon\langle b,r\rangle,\varepsilon q b+Mr).$$
--
--   Its scalar Riesz spectral measure at $|\perp\rangle$ defines $\nu_\varepsilon$; independent entries use the genuine finite product measure. Completed tensor powers give the joint input register, its product vacuum, one-site operators and the joint algorithm/input space. Purified states are defined by the actual Dyson evolutions of Equation (12).
--
--   On the half-line, the observation and response formulas are $Or(\tau)=\langle b,e^{-iM\tau}r\rangle$ and $Ru(\tau)=-i\int_0^\tau\langle b,e^{-iM(\tau-\sigma)}b\rangle u(\sigma)\,d\sigma$. Each operator is the chosen bounded map with that a.e. action if one exists, and zero otherwise. Define $\eta^2=1+\|R\|^2$, $D=\eta^2I-R^\dagger R$, its bounded two-sided inverse when it exists (zero otherwise), and
--
--   $$g=0\oplus(O^\dagger O+O^\dagger RD^{-1}R^\dagger O),\qquad G=\sum_xg_x.$$
--
--   Finally, $P(t)=1-\operatorname{Re}\langle\Psi_Z(t),\Psi_F(t)\rangle+\tfrac14\langle\Psi_F(t),(I\otimes G)\Psi_F(t)\rangle$ and $C_{\rm prog}=1+\eta^2/4$. The hard measure is zero only if self-adjointness fails. Lemma 3.2 verifies the valid spectral branch and all probability/representation properties; the bounded-operator milestone verifies the observation, response, and inverse branches. These properties are conclusions, never assumptions about arbitrary substitute objects. None of $O,R,\eta,g,G$ depends on the input precision or algorithm.
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), Definition 3.1 and Eq. (8), p.13; Eqs. (11)–(12), p.16; Eq. (14), p.17; Eqs. (17)–(19), p.18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_HamLocality237_Testing_HardOperator
import Definitions.Def_HamLocality237_Testing_SpectralMeasure
import Definitions.Def_HamLocality237_Testing_Tensor
import Definitions.Def_HamLocality237_Testing_Dynamics

open QAlgorithms
open MeasureTheory
open scoped BigOperators TensorProduct
noncomputable section

namespace HamLocality237.Testing

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev SingleRegister := WithLp 2 (ℂ × BandSpace)

def scalarPart : SingleRegister →L[ℂ] ℂ := WithLp.fstL 2 ℂ ℂ BandSpace
def bandPart : SingleRegister →L[ℂ] BandSpace := WithLp.sndL 2 ℂ ℂ BandSpace

def pairRegister (a : SingleRegister →L[ℂ] ℂ) (b : SingleRegister →L[ℂ] BandSpace) :
    SingleRegister →L[ℂ] SingleRegister :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ BandSpace).symm.toContinuousLinearMap ∘L a.prod b

def bottomVector : SingleRegister := WithLp.toLp 2 (1, 0)
def bandVector (r : BandSpace) : SingleRegister := WithLp.toLp 2 (0, r)

/-- The actual block operator (8), with no spectral properties assumed. -/
def hardOperator (ε : ℝ) : SingleRegister →L[ℂ] SingleRegister :=
  pairRegister ((ε : ℂ) • ((innerSL ℂ bumpVector) ∘L bandPart))
    (((ε : ℂ) • (scalarPart.smulRight bumpVector)) + multiplicationOperator ∘L bandPart)


/-- Complex functional calculus via real and imaginary parts on the real spectrum. -/
def complexRealCalculus {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (f : ℝ → ℂ) (A : E →L[ℂ] E) : E →L[ℂ] E :=
  cfc (p := IsSelfAdjoint) (fun x => (f x).re) A + Complex.I • cfc (p := IsSelfAdjoint) (fun x => (f x).im) A

/-- Riesz measure totalized by zero if self-adjointness fails. Valid parameters
are shown to use the first branch in lemma_3_2, not assumed as an input. -/
def hardMeasure (ε : ℝ) : Measure ℝ :=
  if h : IsSelfAdjoint (hardOperator ε) then
    scalarSpectralMeasure (hardOperator ε) h bottomVector else 0

def hardProductMeasure (n : ℕ) (ε : ℝ) : Measure (Qubits n → ℝ) :=
  Measure.pi (fun _ => hardMeasure ε)

abbrev HalfLineSpace := Lp ℂ 2 (volume.restrict (Set.Ici (0 : ℝ)))

def freeBandEvolution (t : ℝ) : BandSpace →L[ℂ] BandSpace :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • multiplicationOperator)

def observationFormula (r : BandSpace) (t : ℝ) : ℂ :=
  inner ℂ bumpVector (freeBandEvolution t r)

def responseFormula (u : HalfLineSpace) (t : ℝ) : ℂ :=
  -Complex.I * ∫ s in (0 : ℝ)..t, observationFormula bumpVector (t - s) * u s

/-- Exists as a bounded map with the prescribed a.e. action, or zero otherwise. -/
def observationOperator : BandSpace →L[ℂ] HalfLineSpace :=
  if h : ∃ O : BandSpace →L[ℂ] HalfLineSpace,
      ∀ r, O r =ᵐ[volume.restrict (Set.Ici 0)] observationFormula r then h.choose else 0

def responseOperator : HalfLineSpace →L[ℂ] HalfLineSpace :=
  if h : ∃ R : HalfLineSpace →L[ℂ] HalfLineSpace,
      ∀ u, R u =ᵐ[volume.restrict (Set.Ici 0)] responseFormula u then h.choose else 0

def etaSquared : ℝ := 1 + ‖responseOperator‖ ^ 2

def penaltyOperator : HalfLineSpace →L[ℂ] HalfLineSpace :=
  (etaSquared : ℂ) • 1 - responseOperator.adjoint * responseOperator

/-- True bounded two-sided inverse when one exists, else zero. -/
def penaltyInverse : HalfLineSpace →L[ℂ] HalfLineSpace :=
  if h : ∃ B : HalfLineSpace →L[ℂ] HalfLineSpace,
      B * penaltyOperator = 1 ∧ penaltyOperator * B = 1 then h.choose else 0

def bandCorrection : BandSpace →L[ℂ] BandSpace :=
  observationOperator.adjoint ∘L observationOperator +
    observationOperator.adjoint ∘L responseOperator ∘L penaltyInverse ∘L
      responseOperator.adjoint ∘L observationOperator

def singleCorrection : SingleRegister →L[ℂ] SingleRegister :=
  pairRegister 0 (bandCorrection ∘L bandPart)

def progressConstant : ℝ := 1 + etaSquared / 4

/-- Any finite enumeration is a change of tensor-factor labels only. -/
def siteEnumeration (n : ℕ) : Qubits n ≃ Fin (Fintype.card (Qubits n)) := Fintype.equivFin _

abbrev InputRegister (n : ℕ) := HilbertPower SingleRegister (Fintype.card (Qubits n))

def inputVacuum (n : ℕ) : InputRegister n := hilbertProduct (fun _ => bottomVector)

def inputLift {n : ℕ} (x : Qubits n) (a : SingleRegister →L[ℂ] SingleRegister) :
    InputRegister n →L[ℂ] InputRegister n := hilbertLift (siteEnumeration n x) a

def fullCorrection (n : ℕ) : InputRegister n →L[ℂ] InputRegister n :=
  ∑ x, inputLift x singleCorrection

abbrev JointRegister {n : ℕ} (A : ContinuousAlgorithm n) :=
  UniformSpace.Completion (A.Space ⊗[ℂ] InputRegister n)

def jointProduct {n : ℕ} (A : ContinuousAlgorithm n) (v : A.Space) (r : InputRegister n) :
    JointRegister A := (v ⊗ₜ[ℂ] r : UniformSpace.Completion (A.Space ⊗[ℂ] InputRegister n))

def jointLift {n : ℕ} (A : ContinuousAlgorithm n) (a : A.Space →L[ℂ] A.Space)
    (b : InputRegister n →L[ℂ] InputRegister n) : JointRegister A →L[ℂ] JointRegister A :=
  (TensorProduct.mapL a b).completion

def jointHamiltonian {n : ℕ} (A : ContinuousAlgorithm n) (ε : ℝ) (t : ℝ) :
    JointRegister A →L[ℂ] JointRegister A :=
  jointLift A (A.driver t) 1 + (A.intensity t : ℂ) •
    ∑ x, jointLift A (A.query x t) (inputLift x (hardOperator ε))

def purifiedFar {n : ℕ} (A : ContinuousAlgorithm n) (ε : ℝ) (t : ℝ) : JointRegister A :=
  dysonEvolution (jointHamiltonian A ε) t (jointProduct A A.initial (inputVacuum n))

def purifiedZero {n : ℕ} (A : ContinuousAlgorithm n) (t : ℝ) : JointRegister A :=
  dysonEvolution (fun s => jointLift A (A.driver s) 1) t
    (jointProduct A A.initial (inputVacuum n))

def progress {n : ℕ} (A : ContinuousAlgorithm n) (ε : ℝ) (t : ℝ) : ℝ :=
  1 - (inner ℂ (purifiedZero A t) (purifiedFar A ε t)).re +
    (inner ℂ (purifiedFar A ε t)
      (jointLift A 1 (fullCorrection n) (purifiedFar A ε t))).re / 4

end HamLocality237.Testing


