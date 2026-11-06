-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
-- name    : OAI_NumberTheory_DirichletL_Moments_FullCorrelation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:33.89412+00:00
-- url     : https://prove2.me/theorems/5aabd16f-3d41-44ff-8cce-8f33991ccc76
-- title:
--   Full Correlation
-- statement:
--   Definitions and structural lemmas for Full Correlation, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/FullCorrelation.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]
def scaledResidue (d a m : A) (hm : m = d * a) :
    (A ⧸ Ideal.span {d}) → (A ⧸ Ideal.span {m}) := fun x =>
  Quotient.liftOn' x (fun z => Ideal.Quotient.mk (Ideal.span {m}) (a * z)) (by
    intro x y hxy
    apply Ideal.Quotient.eq.mpr
    have hd : d ∣ x - y := Ideal.mem_span_singleton.mp
      ((Ideal.span {d}).quotientRel_def.mp hxy)
    apply Ideal.mem_span_singleton.mpr
    obtain ⟨z, hz⟩ := hd
    refine ⟨z, ?_⟩
    rw [hm, ← mul_sub, hz]
    ring)
def fullModulusCorrelation (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A) : ℂ :=
  fullCorrelation (scaledResidue u v (u * v) rfl)
    (scaledResidue v u (u * v) (mul_comm u v)) χu χv
    (Ideal.Quotient.mk (Ideal.span {u * v}) j)
variable [IsDomain A]
end SevenEighths.CenteredMomentCorrelation
end
end OAI


