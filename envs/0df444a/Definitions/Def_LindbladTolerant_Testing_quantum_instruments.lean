-- Prove2me | Definitions.Def_LindbladTolerant_Testing_quantum_instruments
-- name    : LindbladTolerant_Testing_quantum_instruments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:53:52.853177+00:00
-- url     : https://prove2.me/theorems/fd072333-2f83-4939-b0fd-043f4d042d78
-- title:
--   Completely positive instruments with measurable classical outcomes
-- statement:
--   A quantum instrument has a finite input space and an arbitrary measurable outcome space $\Omega$. Its finite output dimension may depend on the outcome without a common bound. It is represented by a dominating probability measure $\nu$ and completely positive densities $\mathcal I_o$. For every positive semidefinite input $\rho$, the trace density is integrable and
--   $$\int_\Omega\operatorname{Tr}(\mathcal I_o(\rho))\,d\nu(o)=\operatorname{Tr}\rho.$$
--   The actual outcome measure and unnormalized posterior are
--   $$\Pr_\rho(do)=\operatorname{Tr}(\mathcal I_o(\rho))\,d\nu(o),\qquad \mathcal I_o(\rho).$$
--   This is an instrument representation, not an arbitrary response law for the unknown oracle. Finite-dimensional instruments admit scalar domination by their trace measure; a countable partition by output dimension handles outcome-dependent finite output spaces. No finite outcome alphabet is imposed.
--
--   This general object supplies free known operations, randomness, and joint measurements in the source oracle model. Null outcomes need no normalized posterior state.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, §3, pp.16–18, PDF pp.16–18; operational meaning of known quantum operations, ancillary systems, measurements and internal randomness

import Definitions.Def_LindbladTolerant_Testing_matrix_model

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Matrix

namespace LindbladTolerant.Testing

/-- A quantum instrument with arbitrary measurable classical outcomes and
finite, outcome-dependent quantum output spaces. The measure is a dominating
probability measure, not an oracle-dependent output law. The CP densities and
trace normalization give the actual Born measure. -/
structure QuantumInstrument {Ω : Type*} [MeasurableSpace Ω]
    (I : Type) [Fintype I] [DecidableEq I]
    (O : Ω → Type) [∀ o, Fintype (O o)] [∀ o, DecidableEq (O o)] where
  base : Measure Ω
  probability : IsProbabilityMeasure base
  branch : (o : Ω) → Super I (O o)
  outputDimensionMeasurable : Measurable (fun o => Fintype.card (O o))
  coefficientMeasurable : ∀ (ij : I × I) (a b : ℕ),
    Measurable (fun o =>
      if ha : a < Fintype.card (O o) then
      if hb : b < Fintype.card (O o) then
        branch o ((Fintype.equivFin (O o)).symm ⟨a,ha⟩,
          (Fintype.equivFin (O o)).symm ⟨b,hb⟩) ij
      else 0 else 0)
  completelyPositive : ∀ o, IsCP (branch o)
  integrableMass : ∀ x : Op I, x.PosSemidef →
    Integrable (fun o => (applySuper (branch o) x).trace.re) base
  normalized : ∀ x : Op I, x.PosSemidef →
    ∫ o, (applySuper (branch o) x).trace.re ∂base = x.trace.re

/-- Unnormalized posterior matrices determine the outcome measure; null outcomes
need no normalized posterior and introduce no physical state. -/
def instrumentLaw {Ω : Type*} [MeasurableSpace Ω]
    {I : Type} [Fintype I] [DecidableEq I]
    {O : Ω → Type} [∀ o, Fintype (O o)] [∀ o, DecidableEq (O o)]
    (a : QuantumInstrument I O) (x : Op I) : Measure Ω :=
  a.base.withDensity (fun o => ENNReal.ofReal (applySuper (a.branch o) x).trace.re)

end LindbladTolerant.Testing


