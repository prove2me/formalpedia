-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
-- name    : QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:02:33.506895+00:00
-- url     : https://prove2.me/theorems/66695fa0-ee22-413f-ac98-97541458fa8a
-- title:
--   Meromorphic Germs
-- statement:
--   Definitions and structural lemmas for Meromorphic Germs, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/MeromorphicGerms.lean

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Algebra.Polynomial.AlgebraMap
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
noncomputable section
def meromorphicGermSubring (x : ℂ) : Subring (Germ (𝓝[≠] x) ℂ) where
  carrier := {A | ∃ f : ℂ → ℂ, MeromorphicAt f x ∧ A = (f : Germ (𝓝[≠] x) ℂ)}
  zero_mem' := ⟨0, MeromorphicAt.const 0 x, rfl⟩
  one_mem' := ⟨1, MeromorphicAt.const 1 x, rfl⟩
  add_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f+g,hf.add hg,rfl⟩
  neg_mem' := by
    rintro A ⟨f,hf,rfl⟩
    exact ⟨-f,hf.neg,rfl⟩
  mul_mem' := by
    rintro A B ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f*g,hf.mul hg,rfl⟩
abbrev MeromorphicGermRing (x : ℂ) := ↥(meromorphicGermSubring x)
def germOrder (x : ℂ) (A : Germ (𝓝[≠] x) ℂ) : WithTop ℤ :=
  Germ.liftOn A (fun f => meromorphicOrderAt f x)
    (fun _ _ h => meromorphicOrderAt_congr h)
def meromorphicOrderValuation (x : ℂ) : AddValuation (MeromorphicGermRing x) (WithTop ℤ) :=
  AddValuation.of (fun A => germOrder x A.val)
    (by change meromorphicOrderAt (0 : ℂ → ℂ) x = ⊤; simp)
    (by change meromorphicOrderAt (1 : ℂ → ℂ) x = 0; simp)
    (by
      intro A B
      obtain ⟨f,hf,he⟩ := A.property
      obtain ⟨g,hg,hgerm⟩ := B.property
      change min (germOrder x A.val) (germOrder x B.val) ≤ germOrder x (A.val+B.val)
      rw [he,hgerm]
      exact meromorphicOrderAt_add hf hg)
    (by
      intro A B
      obtain ⟨f,hf,he⟩ := A.property
      obtain ⟨g,hg,hgerm⟩ := B.property
      change germOrder x (A.val*B.val) = germOrder x A.val + germOrder x B.val
      rw [he,hgerm]
      exact meromorphicOrderAt_mul hf hg)
end
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms


