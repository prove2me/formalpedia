-- Prove2me | Definitions.Def_ValiantBorder_gridComplete
-- name    : ValiantBorder_gridComplete
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:13:58.452934+00:00
-- url     : https://prove2.me/theorems/f81ceabd-f0f1-4699-9b0d-4ca7f953264f
-- title:
--   Grid completeness under affine substitutions
-- statement:
--   A finite bipartite incidence pattern defines a polynomial by assigning a bit to every vertex, multiplying its local weights, and summing over the bit assignments. Each local weight is constant or affine in its designated variable. A family is grid-complete with factor $κ$ if every such sum is obtained from its size-$S$ member by affine substitutions whenever $S$ is at least $κ$ times the number of incidences.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Nc/Rate/Defs.lean).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Nc/Rate/Defs.lean.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*, Appendix M and the sections
on grids. Source: `anthropics/formal-math` revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5,
`vp-vnp/Nc/PermValiant.lean`, `Nc/Rate/Defs.lean`, `Nc/Perm{Coeff,Grid,Sum,Pad}.lean`,
`Nc/Hc/{Grid,Segments}.lean` and `Paper/{Grids,HcGrid}.lean`, Apache-2.0. -/
namespace ValiantBorder
open MvPolynomial Finset
variable {F : Type*} [Field F] {ι : Type*}
/-- Constant, or affine in one variable. -/
def IsAffine (p : MvPolynomial ι F) : Prop := (∃ b, p = C b) ∨ ∃ i a b, p = C a * X i + C b

/-- The constants and, for `some i`, the span of the constants and `X i`. -/
noncomputable def affIn (o : Option ι) : Submodule F (MvPolynomial ι F) :=
  match o with
  | none => Submodule.span F {1}
  | some i => Submodule.span F {X i, 1}


/-- The polynomials `G S`, one for every size `S`, are complete for grid sums with the blow-up `κ`: a sum over two
families of bits of a product of weights, one for every incidence, each affine in the variable of its incidence, is a
projection with affine entries of `G S` for all `S ≥ κ * #incidences`. -/
def GridComplete (F : Type) [Field F] (G : ∀ S : ℕ, MvPolynomial (Fin S × Fin S) F) (κ : ℕ) : Prop :=
  ∀ {ι N V W' : Type} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype W'] [DecidableEq W']
    (v : N → V) (w : N → W'), Function.Surjective v → Function.Surjective w →
    ∀ (W : N → Bool → Bool → MvPolynomial ι F) (o : W' → Option ι),
    (∀ n x r, W n x r ∈ affIn (F := F) (o (w n))) → ∀ S : ℕ, κ * Fintype.card N ≤ S →
    ∃ M : Fin S × Fin S → MvPolynomial ι F, (∀ q, IsAffine (M q)) ∧
      aeval M (G S) = ∑ x : V → Bool, ∑ r : W' → Bool, ∏ n, W n (x (v n)) (r (w n))


end ValiantBorder


