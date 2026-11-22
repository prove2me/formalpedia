-- Prove2me | solution 1 for Autoconvolutions.Blocks.peakCode_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:51.442694+00:00
-- url     : https://prove2.me/submissions/f7c150af-f09d-486d-9fba-4b935f491dba

module
public import Definitions.Def_Autoconvolutions_BlockKeys
public import Definitions.Def_Autoconvolutions_Occupancy
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Theorems.Thm_Autoconvolutions_Blocks_peak_mem
public import Theorems.Thm_Autoconvolutions_Blocks_peak_row
public import Theorems.Thm_Autoconvolutions_Blocks_peak_rowKey
public import Theorems.Thm_Autoconvolutions_Blocks_rowKey_determines_level
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet


attribute [local simp] Autoconvolutions.Blocks.peak_rowKey

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Blocks
namespace Autoconvolutions.Blocks
theorem _root_.solution {m n K D : ℕ} {I J : Finset (Fin m)}
    (hD : 1 < D) (hd : Disjoint I J) (hK : K ≤ n) (hnD : 4*n < D) :
    Set.InjOn (peakCode D) (↑(peakSet I J n K) : Set (Peak m)) := by
  intro x hx y hy he
  have hx' := peak_mem hx
  have hy' := peak_mem hy
  have ht := rowKey_determines_level hD hd (by omega : x.1 ≤ 2*n) (by omega : y.1 ≤ 2*n)
    hnD (peak_row hx (by omega : 0 < D)) (peak_row hy (by omega : 0 < D))
    (by simpa only [peak_rowKey, Nat.add_zero] using congrArg (D * ·) he)
  obtain ⟨s, a,b⟩ := x
  obtain ⟨t, c,d⟩ := y
  obtain ⟨hst, hab⟩ := ht
  have hh : (a,b) = (c,d) := congrArg Prod.fst hab
  cases hst
  cases hh
  rfl
end Autoconvolutions.Blocks
