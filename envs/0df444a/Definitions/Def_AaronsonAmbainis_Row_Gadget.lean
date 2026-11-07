-- Prove2me | Definitions.Def_AaronsonAmbainis_Row_Gadget
-- name    : AaronsonAmbainis_Row_Gadget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:02:08.702226+00:00
-- url     : https://prove2.me/theorems/26826cf8-4c41-44fb-8fe6-0cecf03ba1d4
-- title:
--   Gadget
-- statement:
--   Definitions and structural lemmas for Gadget, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Gadget.lean

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Degree
set_option autoImplicit true
namespace AaronsonAmbainis
namespace Row
open Finset Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]
noncomputable def cnt (S : β → Finset ι) (i : ι) (w : Cube β) : ℝ :=
  ∑ b ∈ univ.filter (fun b : β => i ∈ S b), (if w b then (1 : ℝ) else 0)
noncomputable def gate (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) (w : Cube β) : ℝ :=
  (Chebyshev.T ℝ m).eval (1 - c * cnt S i w)
noncomputable def gadget (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ)
    (w : Cube β) : ℝ :=
  ∑ T : Finset ι, a T * ∏ i ∈ T, (sgn (x i) * gate S m c i w)
end Row
end AaronsonAmbainis


