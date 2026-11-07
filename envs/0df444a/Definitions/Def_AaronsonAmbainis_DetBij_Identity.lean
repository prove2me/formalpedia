-- Prove2me | Definitions.Def_AaronsonAmbainis_DetBij_Identity
-- name    : AaronsonAmbainis_DetBij_Identity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:26:08.362312+00:00
-- url     : https://prove2.me/theorems/dd3ced11-293c-4921-9291-b18667b80e81
-- title:
--   Identity
-- statement:
--   Definitions and structural lemmas for Identity, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Identity.lean

import Definitions.Def_AaronsonAmbainis_DetBij_Basic
set_option autoImplicit true
namespace AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def Pmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x w => if diffSet x.1 w.1 ⊆ A x.1 then ∏ i ∈ diffSet x.1 w.1, -(X i) else 0
noncomputable def Umat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  Matrix.diagonal fun x => ∏ i ∈ A x.1, (1 - X i ^ 2)
noncomputable def Qmat (g : Cube ι → Bool) (A : Cube ι → Finset ι) :
    Matrix (Ones g) (Ones g) (MvPolynomial ι ℤ) :=
  fun x z => if Disjoint (agSet x.1 z.1) (A x.1) then agMon x.1 z.1 else 0
noncomputable def fAg (x z : Cube ι) (i : ι) : MvPolynomial ι ℤ := if x i = z i then X i else 1
noncomputable def gAg (x z : Cube ι) (i : ι) : MvPolynomial ι ℤ := if x i = z i then 1 else X i
end AaronsonAmbainis.DetBij


