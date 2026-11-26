-- Prove2me | Definitions.Def_Scott1972_ContinuousLattice_Theorem212
-- name    : Scott1972_ContinuousLattice_Theorem212
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:34:44.714998+00:00
-- url     : https://prove2.me/theorems/39a45153-504f-47aa-8a34-1e822541035a
-- title:
--   Theorem212
-- statement:
--   Definitions and structural lemmas for Theorem212, from Lars Warren Ericson (catskillsresearch/scott1972; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Dana Scott's Continuous Lattices (1972): injective T0-spaces, Scott topology, and D_infinity homeomorphism development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Theorem212.lean

import Definitions.Def_Scott1972_ContinuousLattice_Constructions
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_isOpen_iff_scottOpen
import Theorems.Thm_Scott1972_ContinuousLattice_preservesDirectedSup_monotone

set_option autoImplicit true
namespace Scott1972.ContinuousLattice
open Topology Set
section FixedPoints
variable {L : Type*} [CompleteLattice L]
abbrev IdemFix (e : L → L) : Type _ := {x : L // e x = x}
namespace IdemFix
variable {e : L → L}
@[reducible] noncomputable def supSet (hidem : ∀ x, e (e x) = e x) : SupSet (IdemFix e) :=
  ⟨fun S => ⟨e (sSup (Subtype.val '' S)), hidem _⟩⟩
theorem isLUB_sSup (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) :
    letI := supSet hidem
    ∀ S : Set (IdemFix e), IsLUB S (sSup S) := by
  letI := supSet hidem
  intro S
  constructor
  · intro k hk
    rw [Subtype.coe_le_coe.symm, Subtype.coe_mk]
    show (k : L) ≤ e (sSup (Subtype.val '' S))
    calc (k : L) = e k := k.2.symm
      _ ≤ e (sSup (Subtype.val '' S)) :=
          hmono (le_sSup (Set.mem_image_of_mem _ hk))
  · intro w hw
    rw [Subtype.coe_le_coe.symm, Subtype.coe_mk]
    show e (sSup (Subtype.val '' S)) ≤ (w : L)
    calc e (sSup (Subtype.val '' S)) ≤ e (w : L) := by
          refine hmono (sSup_le ?_)
          rintro _ ⟨k, hk, rfl⟩
          exact hw hk
      _ = (w : L) := w.2
@[reducible] noncomputable def completeLattice (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) :
    CompleteLattice (IdemFix e) :=
  letI := supSet hidem
  completeLatticeOfSup (IdemFix e) (isLUB_sSup hidem hmono)
theorem coe_sSup (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) (S : Set (IdemFix e)) :
    letI := completeLattice hidem hmono
    ((sSup S : IdemFix e) : L) = e (sSup (Subtype.val '' S)) := rfl
end IdemFix
variable {e : L → L}
theorem idemFix_incl_preservesDirectedSup (hidem : ∀ x, e (e x) = e x)
    (hsc : PreservesDirectedSup e) :
    letI := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
    PreservesDirectedSup (Subtype.val : IdemFix e → L) := by
  letI := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  intro S hS hSdir
  show e (sSup (Subtype.val '' S)) = sSup (Subtype.val '' S)
  have hdir' : DirectedOn (· ≤ ·) (Subtype.val '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨c.val, Set.mem_image_of_mem _ hc, hac, hbc⟩
  have hne' : (Subtype.val '' S).Nonempty := hS.image _
  rw [hsc hne' hdir']
  congr 1
  rw [← Set.image_comp]
  exact Set.image_congr (fun s _ => s.2)
theorem idemFix_retr_preservesDirectedSup (hidem : ∀ x, e (e x) = e x)
    (hsc : PreservesDirectedSup e) :
    letI := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
    PreservesDirectedSup (fun x : L => (⟨e x, hidem x⟩ : IdemFix e)) := by
  letI := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  have hmono := preservesDirectedSup_monotone hsc
  intro T hT hTdir
  apply Subtype.ext
  rw [IdemFix.coe_sSup hidem hmono]
  show e (sSup T) = e (sSup (Subtype.val '' ((fun x : L => (⟨e x, hidem x⟩ : IdemFix e)) '' T)))
  have himg : Subtype.val '' ((fun x : L => (⟨e x, hidem x⟩ : IdemFix e)) '' T) = e '' T := by
    rw [← Set.image_comp]; rfl
  rw [himg]
  have hTdir' : DirectedOn (· ≤ ·) (e '' T) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hTdir a ha b hb
    exact ⟨e c, Set.mem_image_of_mem _ hc, hmono hac, hmono hbc⟩
  have hTne' : (e '' T).Nonempty := hT.image _
  rw [hsc hT hTdir, hsc hTne' hTdir']
  congr 1
  rw [← Set.image_comp]
  exact Set.image_congr (fun x _ => (hidem x).symm)
noncomputable def idemFixRetraction (hidem : ∀ x, e (e x) = e x) (hsc : PreservesDirectedSup e) :
    @IsContinuousLatticeRetraction (IdemFix e) L
      (IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)) _ :=
  letI := IdemFix.completeLattice hidem (preservesDirectedSup_monotone hsc)
  { incl := ⟨Subtype.val,
      continuous_of_preservesDirectedSup (idemFix_incl_preservesDirectedSup hidem hsc)⟩
    retr := ⟨fun x => ⟨e x, hidem x⟩,
      continuous_of_preservesDirectedSup (idemFix_retr_preservesDirectedSup hidem hsc)⟩
    retr_incl := fun k => Subtype.ext k.2 }
end FixedPoints
universe u
section Theorem212Transfer
variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]
theorem scottOpen_preimage_orderIso (e : A ≃o B) {U : Set B} (hU : ScottOpen U) :
    ScottOpen (e ⁻¹' U) := by
  refine ⟨fun x y hxy hx => hU.1 (e.monotone hxy) hx, ?_⟩
  intro S hSne hSdir hsup
  have hImgNe : (e '' S).Nonempty := hSne.image e
  have hImgDir : DirectedOn (· ≤ ·) (e '' S) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hSdir x hx y hy
    exact ⟨e z, Set.mem_image_of_mem e hz, e.monotone hxz, e.monotone hyz⟩
  have hmap : e (sSup S) = sSup (e '' S) := by
    rw [e.map_sSup, sSup_image]
  obtain ⟨_, ⟨s, hs, rfl⟩, hes⟩ := hU.2 hImgNe hImgDir (hmap ▸ hsup)
  exact ⟨s, hs, hes⟩
noncomputable def orderIsoScottHomeomorph (e : A ≃o B) :
    @Homeomorph A B (@scottTopologicalSpace A latticeA)
      (@scottTopologicalSpace B latticeB) := by
  letI : TopologicalSpace A := @scottTopologicalSpace A latticeA
  letI : TopologicalSpace B := @scottTopologicalSpace B latticeB
  letI : Preorder A := latticeA.toPreorder
  letI : Preorder B := latticeB.toPreorder
  exact {
  toEquiv := e.toEquiv
  continuous_toFun := by
    rw [continuous_def]
    intro U hU
    exact isOpen_iff_scottOpen.mpr
      (scottOpen_preimage_orderIso e (isOpen_iff_scottOpen.mp hU))
  continuous_invFun := by
    rw [continuous_def]
    intro U hU
    exact isOpen_iff_scottOpen.mpr
      (scottOpen_preimage_orderIso e.symm (isOpen_iff_scottOpen.mp hU))
  }
end Theorem212Transfer
section Lemma39
variable {X Y D D' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompleteLattice D] [CompleteLattice D']
end Lemma39
end Scott1972.ContinuousLattice


