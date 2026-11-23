-- Prove2me | Definitions.Def_KernelRankLean_Defs
-- name    : KernelRankLean_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:47:49.260611+00:00
-- url     : https://prove2.me/theorems/dbb82e92-d16e-4da9-98b4-5a57ef3acde9
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean

import Mathlib
set_option autoImplicit true
open Complex Polynomial
namespace KernelRank
def IsSumOfProducts {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι] {X : ι → Type*}
    (K : (∀ i, X i) → 𝕜) (N : ℕ) : Prop :=
  ∃ f : Fin N → ∀ i, X i → 𝕜, ∀ x, K x = ∑ n, ∏ i, f n i (x i)
noncomputable def separableRank {𝕜 : Type*} [CommSemiring 𝕜] {ι : Type*} [Fintype ι]
    {X : ι → Type*} (K : (∀ i, X i) → 𝕜) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : IsSumOfProducts K N), (N : ℕ∞)
def padTwo {α : Type*} [Zero α] {d : ℕ} (y : Fin 2 → α) (i : Fin d) : α :=
  if h : (i : ℕ) < 2 then y ⟨i, h⟩ else 0
structure Component where
  rate : ℂ
  poly : ℂ[X]
namespace Component
noncomputable def eval (c : Component) (s : ℝ) : ℝ :=
  (c.poly.eval (s : ℂ) * exp (c.rate * s)).re
noncomputable def multiplicity (c : Component) : ℕ :=
  c.poly.natDegree + 1
noncomputable def cost (c : Component) : ℕ :=
  if c.rate.im = 0 then c.multiplicity else 2 * c.multiplicity
def IsGaussian (c : Component) : Prop :=
  c.poly.natDegree = 0
noncomputable def gaussianCost (d : ℕ) (c : Component) : ℕ :=
  if c.rate.im = 0 then 1 else d
noncomputable def multiCost (d : ℕ) (c : Component) : ℕ :=
  if c.rate.im = 0 then (d - 1) * c.poly.natDegree + 1
  else 2 * (d - 1) * c.poly.natDegree + d
noncomputable def borderCost (d : ℕ) (c : Component) : ℕ :=
  if c.rate.im = 0 then c.poly.natDegree + 1 else d * (c.poly.natDegree + 1)
def WellFormed (c : Component) : Prop :=
  c.poly ≠ 0 ∧ 0 ≤ c.rate.im ∧ (c.rate.im = 0 → ∀ k, (c.poly.coeff k).im = 0)
end Component
noncomputable def profile (cs : List Component) (s : ℝ) : ℝ :=
  (cs.map fun c => c.eval s).sum
noncomputable def totalCost (cs : List Component) : ℕ :=
  (cs.map Component.cost).sum
noncomputable def gaussianTotalCost (d : ℕ) (cs : List Component) : ℕ :=
  (cs.map (Component.gaussianCost d)).sum
noncomputable def multiTotalCost (d : ℕ) (cs : List Component) : ℕ :=
  (cs.map (Component.multiCost d)).sum
noncomputable def borderTotalCost (d : ℕ) (cs : List Component) : ℕ :=
  (cs.map (Component.borderCost d)).sum
def IsRepresentation (cs : List Component) : Prop :=
  (∀ c ∈ cs, c.WellFormed) ∧ (cs.map Component.rate).Nodup
def IsGaussianRepresentation (cs : List Component) : Prop :=
  IsRepresentation cs ∧ ∀ c ∈ cs, c.IsGaussian
end KernelRank


