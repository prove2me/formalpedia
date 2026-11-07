-- Prove2me | solution 1 for AaronsonAmbainis.abstract_cs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:53.874273+00:00
-- url     : https://prove2.me/submissions/446a3e1c-b1e3-49ef-bfeb-ccaf67a9dd7b

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Theorems.Thm_AaronsonAmbainis_inv_sq_mul_self
import Theorems.Thm_AaronsonAmbainis_cs_core

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (a : α → ι → ℝ) (b : β → ι → ℝ) (ha : ∀ x j, 0 ≤ a x j) (hb : ∀ y j, 0 ≤ b y j)
    (D : α → β → Finset ι) (C : ℝ) (hC : 0 ≤ C)
    (hpos : ∀ x ∈ O, ∀ y ∈ N, ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      0 < ∑ j ∈ D x y, w j * a x j * b y j)
    (hpairs : ∀ w : ι → ℝ, (∀ j, 0 < w j) →
      ∑ x ∈ O, ∑ y ∈ N, (∑ j ∈ D x y, w j * a x j * b y j)⁻¹ ≤ C * ∑ j, (w j)⁻¹) :
    (∑ x ∈ O, (∑ j, a x j)⁻¹) * (∑ y ∈ N, (∑ j, b y j)⁻¹) ≤ C :=
  cs_core O N a b ha hb (fun x => (∑ j, a x j)⁻¹) (fun y => (∑ j, b y j)⁻¹)
    (fun x => inv_sq_mul_self (∑ j, a x j)) (fun y => inv_sq_mul_self (∑ j, b y j))
    D C hC hpos hpairs
end AaronsonAmbainis
