-- Prove2me | Definitions.Def_FBMStrongSim_RecordBreak_Supplement_CoefficientModel
-- name    : FBMStrongSim_RecordBreak_Supplement_CoefficientModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:26:49.407995+00:00
-- url     : https://prove2.me/theorems/9fa3af13-ceef-4ba3-8d91-54258bb6c66c
-- title:
--   Bounded C² matrix fields with entrywise derivative envelopes
-- statement:
--   Vectors in $\mathbb R^d$ and $\mathbb R^h$ have the maximum norm. A field $f:\mathbb R^d\to\mathbb R^{d\times h}$ acts as a continuous linear map on each driving increment. It is twice continuously differentiable and has uniform entrywise bounds
--   $$|f_{ij}(a)|\le F_0,\quad|\partial_l f_{ij}(a)|\le F_1,\quad|\partial_r\partial_l f_{ij}(a)|\le F_2.$$
--   Here $F_0,F_1>0$ and $F_2\ge0$. Existence of such envelopes describes exactly the bounded $C^2$ fields of Assumption 5.4. Positive envelopes cover zero and constant fields without division by zero in the later constants. Their numerical use, including the local entrywise correction in Lemma 5.8, is disclosed in the theorem items and DISPROOF.md.
--
--   Differences from the source:
--   - reading: the absolute-value notation for vector and derivative bounds → maximum vector norms and entrywise partial-derivative bounds; reason: this is the declared norm reading of the brief, consistent with the explicit d and d² factors in the composition estimate
--   - correction: exact coefficient and derivative norms may be zero → positive uniform value and first-derivative envelopes F0,F1, and a nonnegative second-derivative envelope F2; reason: the constant-field refutation and the zero denominator in ω are recorded in DISPROOF.md; every bounded C² field admits such envelopes
--   - encoding: a d×h matrix field → a continuous-linear-map-valued C² function with entries and partials evaluated on basis vectors; reason: finite-dimensional continuous linear maps represent all matrices, so no coefficient fields are lost
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, pp. 29–30, (5.3), Assumption 5.4

import Mathlib

namespace FBMStrongSim.RecordBreak.Supplement

abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Field (d h : ℕ) := Vec d → (Vec h →L[ℝ] Vec d)

noncomputable def basisVec {d : ℕ} (i : Fin d) : Vec d := Pi.single i 1
noncomputable def fieldEntries {d h : ℕ} (f : Field d h) (a : Vec d) : Fin d × Fin h → ℝ :=
  fun ij => f a (basisVec ij.2) ij.1

/-- Assumption 5.4, with positive value/first-derivative envelopes and a nonnegative second-derivative envelope.
No differentiability or existence conclusion is bundled into the solution predicate. -/
structure CoefficientBounds {d h : ℕ} (f : Field d h) (F0 F1 F2 : ℝ) : Prop where
  pos0 : 0 < F0
  pos1 : 0 < F1
  nonneg2 : 0 ≤ F2
  smooth : ContDiff ℝ 2 f
  value : ∀ a i j, |f a (basisVec j) i| ≤ F0
  deriv : ∀ a i j l, |fderiv ℝ f a (basisVec l) (basisVec j) i| ≤ F1
  deriv2 : ∀ a i j l r,
    |fderiv ℝ (fun b => fderiv ℝ f b) a (basisVec r) (basisVec l) (basisVec j) i| ≤ F2


end FBMStrongSim.RecordBreak.Supplement


