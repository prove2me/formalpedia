-- Prove2me | solution 1 for Autoconvolutions.Blocks.rowKey_determines_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:53.641741+00:00
-- url     : https://prove2.me/submissions/a70baf2d-6994-4bff-9f51-4d87fff899cf

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Theorems.Thm_Autoconvolutions_Blocks_mem_rows
public import Theorems.Thm_Autoconvolutions_Blocks_rowKey_injective

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Blocks
open Finset
namespace Autoconvolutions.Blocks
theorem _root_.solution {m n s s' D : ℕ} {I J : Finset (Fin m)}
    (hD : 1 < D) (hd : Disjoint I J) (hs : s ≤ 2*n) (hs' : s' ≤ 2*n)
    (hnD : 4*n < D) {t t' : Row m}
    (ht : t ∈ rows I J (2*n-s) (2*n+s) D)
    (ht' : t' ∈ rows I J (2*n-s') (2*n+s') D)
    (he : rowKey D t = rowKey D t') : s = s' ∧ t = t' := by
  have h := rowKey_injective hD hd (by omega) (by omega) ht ht' he
  subst t'
  have h1 := (Finset.mem_piAntidiag.mp (mem_rows.mp ht).2.1).1
  have h2 := (Finset.mem_piAntidiag.mp (mem_rows.mp ht').2.1).1
  exact ⟨by omega, rfl⟩
end Autoconvolutions.Blocks
