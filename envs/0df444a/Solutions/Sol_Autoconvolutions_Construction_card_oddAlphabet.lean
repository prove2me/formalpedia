-- Prove2me | solution 1 for Autoconvolutions.Construction.card_oddAlphabet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:48:17.432339+00:00
-- url     : https://prove2.me/submissions/6fe400b9-317e-49bb-90e7-53a2c602ac4f

module
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Real.Basic
public import Definitions.Def_Autoconvolutions_Levels

set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction
namespace Autoconvolutions.Construction
theorem _root_.solution (r : ℕ) : (oddAlphabet r).card = r := by simp [oddAlphabet]
end Autoconvolutions.Construction
