-- Prove2me | solution 1 for Autoconvolutions.Blocks.rowKey_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:16.857219+00:00
-- url     : https://prove2.me/submissions/53325eb0-30d1-4c9e-b28a-38f79d52a063

module
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Theorems.Thm_Autoconvolutions_Blocks_mem_rows
public import Theorems.Thm_Autoconvolutions_Blocks_code_add
public import Theorems.Thm_Autoconvolutions_Blocks_low_and_high
public import Theorems.Thm_Autoconvolutions_Blocks_coord_zero_of_notMem
public import Theorems.Thm_Autoconvolutions_Blocks_coord_le

set_option autoImplicit true
@[expose] public section
public section
open Autoconvolutions Autoconvolutions.Blocks
open Finset
namespace Autoconvolutions.Blocks
theorem _root_.solution {m u v u' v' D : ℕ} {I J : Finset (Fin m)}
    (hD : 1 < D) (hd : Disjoint I J) (huv : u+v < D) (huv' : u'+v' < D)
    {t t' : Row m} (ht : t ∈ rows I J u v D) (ht' : t' ∈ rows I J u' v' D)
    (he : rowKey D t = rowKey D t') : t = t' := by
  obtain ⟨ha, hb, hh⟩ := mem_rows.mp ht
  obtain ⟨ha', hb', hh'⟩ := mem_rows.mp ht'
  have hi := low_and_high hD
    (a := fun i => t.1.1 i + t.1.2 i) (b := fun i => t'.1.1 i + t'.1.2 i)
    (fun i => lt_of_le_of_lt (Nat.add_le_add (coord_le ha i) (coord_le hb i)) huv)
    (fun i => lt_of_le_of_lt (Nat.add_le_add (coord_le ha' i) (coord_le hb' i)) huv')
    hh hh' (by simpa only [code_add, rowKey, key] using he)
  have hleft : t.1.1 = t'.1.1 := by
    funext i
    by_cases hiI : i ∈ I
    · have hiJ := Finset.disjoint_left.mp hd hiI
      simpa [coord_zero_of_notMem hb hiJ, coord_zero_of_notMem hb' hiJ] using congrFun hi.2 i
    · rw [coord_zero_of_notMem ha hiI, coord_zero_of_notMem ha' hiI]
  have hright : t.1.2 = t'.1.2 := by
    funext i
    have heq := congrFun hi.2 i
    rw [congrFun hleft i] at heq
    omega
  exact Prod.ext (Prod.ext hleft hright) hi.1
end Autoconvolutions.Blocks
