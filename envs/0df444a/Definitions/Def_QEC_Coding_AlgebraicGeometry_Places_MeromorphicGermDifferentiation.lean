-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
-- name    : QEC_Coding_AlgebraicGeometry_Places_MeromorphicGermDifferentiation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:04:32.874039+00:00
-- url     : https://prove2.me/theorems/e08aa34a-6a16-434a-9331-b481877b60b8
-- title:
--   Meromorphic Germ Differentiation
-- statement:
--   Definitions and structural lemmas for Meromorphic Germ Differentiation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGermDifferentiation.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Mathlib.RingTheory.Derivation.Basic
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
def germComplexConstants (x : ℂ) : ℂ →+* MeromorphicGermRing x where
  toFun c := ⟨((fun _ : ℂ => c) : Germ (𝓝[≠] x) ℂ),
    (fun _ : ℂ => c),MeromorphicAt.const c x,rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
def germDerivative (x : ℂ) (A : MeromorphicGermRing x) : MeromorphicGermRing x :=
  ⟨(deriv A.property.choose : Germ (𝓝[≠] x) ℂ),deriv A.property.choose,
    A.property.choose_spec.1.deriv,rfl⟩
lemma germDerivative_value (x : ℂ) (A : MeromorphicGermRing x)
    (f : ℂ → ℂ) (_hf : MeromorphicAt f x) (he : A.val = (f : Germ (𝓝[≠] x) ℂ)) :
    (germDerivative x A).val = (deriv f : Germ (𝓝[≠] x) ℂ) := by
  apply Germ.coe_eq.mpr
  exact (Germ.coe_eq.mp (A.property.choose_spec.2.symm.trans he)).nhdsNE_deriv
lemma germDerivative_add (x : ℂ) (A B : MeromorphicGermRing x) :
    germDerivative x (A+B) = germDerivative x A + germDerivative x B := by
  obtain ⟨f,hf,he⟩ := A.property
  obtain ⟨g,hg,he'⟩ := B.property
  have hab : (A+B).val = (f+g : Germ (𝓝[≠] x) ℂ) := by
    change A.val+B.val = _
    rw [he,he']
  apply Subtype.ext
  change (germDerivative x (A+B)).val = (germDerivative x A).val + (germDerivative x B).val
  rw [germDerivative_value x (A+B) (f+g) (hf.add hg) hab,
    germDerivative_value x A f hf he,germDerivative_value x B g hg he']
  apply Germ.coe_eq.mpr
  filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with z hz hz'
  exact deriv_add hz.differentiableAt hz'.differentiableAt
lemma germDerivative_mul (x : ℂ) (A B : MeromorphicGermRing x) :
    germDerivative x (A*B) = A*germDerivative x B + B*germDerivative x A := by
  obtain ⟨f,hf,he⟩ := A.property
  obtain ⟨g,hg,he'⟩ := B.property
  have hab : (A*B).val = (f*g : Germ (𝓝[≠] x) ℂ) := by
    change A.val*B.val = _
    rw [he,he']
  apply Subtype.ext
  change (germDerivative x (A*B)).val = A.val*(germDerivative x B).val + B.val*(germDerivative x A).val
  rw [germDerivative_value x (A*B) (f*g) (hf.mul hg) hab,
    germDerivative_value x A f hf he,germDerivative_value x B g hg he',he,he']
  apply Germ.coe_eq.mpr
  filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with z hz hz'
  simpa only [Pi.mul_apply,Pi.add_apply,mul_comm,add_comm] using
    deriv_mul hz.differentiableAt hz'.differentiableAt
lemma germDerivative_constant (x : ℂ) (c : ℂ) :
    germDerivative x (germComplexConstants x c) = 0 := by
  apply Subtype.ext
  rw [germDerivative_value x _ (fun _ : ℂ => c) (MeromorphicAt.const c x) rfl]
  apply Germ.coe_eq.mpr
  filter_upwards with z
  simp only [deriv_const]
section ComplexDerivation
variable (x : ℂ)
local instance _p2m_local_instance_95258147c8_82 : Algebra ℂ (MeromorphicGermRing x) := (germComplexConstants x).toAlgebra
def germCoefficientDerivation : Derivation ℂ (MeromorphicGermRing x) (MeromorphicGermRing x) := by
  let D : MeromorphicGermRing x →ₗ[ℂ] MeromorphicGermRing x :=
    { toFun := germDerivative x
      map_add' := germDerivative_add x
      map_smul' := by
        intro c A
        change germDerivative x (germComplexConstants x c * A) =
          germComplexConstants x c * germDerivative x A
        rw [germDerivative_mul,germDerivative_constant,mul_zero,add_zero] }
  exact Derivation.mk' D (germDerivative_mul x)
end ComplexDerivation
end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms


