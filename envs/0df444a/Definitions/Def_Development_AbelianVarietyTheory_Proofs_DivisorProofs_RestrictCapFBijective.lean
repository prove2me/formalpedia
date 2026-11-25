-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RestrictCapFBijective
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:12:18.445385+00:00
-- url     : https://prove2.me/theorems/b5e3d350-f296-5291-8ab0-6f8926610a17
-- title:
--   Restrict Cap FBijective
-- statement:
--   Definitions and structural lemmas for Restrict Cap FBijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RestrictCapFBijective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechPullOneBijectiveLatticeCover
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Glue_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Sep_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van1_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van2_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_VandermondeTwoBasis_CovBy_mono
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR
namespace GlobalTheory.CechCmp
instance instSupNE (I : Type) : SemilatticeSup {S : Set I // S.Nonempty} :=
  Subtype.semilatticeSup fun _ _ h _ => h.mono Set.subset_union_left
abbrev NE (I : Type) : Type := {S : Set I // S.Nonempty}ᵒᵈ
variable {I : Type} {X : Scheme.{0}}
def NE.set (S : NE I) : Set I := (OrderDual.ofDual S).1
theorem NE.le_iff {S T : NE I} : S ≤ T ↔ T.set ⊆ S.set := Iff.rfl
theorem NE.nonempty (S : NE I) : S.set.Nonempty := (OrderDual.ofDual S).2
def NE.single (i : I) : NE I := OrderDual.toDual ⟨{i}, Set.singleton_nonempty i⟩
def NE.pair (i j : I) : NE I := OrderDual.toDual ⟨{i, j}, Set.insert_nonempty i {j}⟩
theorem NE.pair_le_single_left (i j : I) : NE.pair i j ≤ NE.single i :=
  NE.le_iff.2 (Set.singleton_subset_iff.2 (Set.mem_insert i {j}))
theorem NE.pair_le_single_right (i j : I) : NE.pair i j ≤ NE.single j :=
  NE.le_iff.2 (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem i rfl))
def NE.pt (S : NE I) : I := S.nonempty.some
def cap (U : I → X.Opens) (S : NE I) : X.Opens := ⨅ i ∈ S.set, U i
theorem cap_mono (U : I → X.Opens) : Monotone (cap U) := fun _ _ h => le_iInf₂ fun i hi => iInf₂_le i (h hi)
theorem isAffineOpen_cap [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) (S : NE I) :
    IsAffineOpen (cap U S) := by
  have key : ∀ s : Set I, s.Finite → s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i) := by
    intro s hs
    obtain ⟨t, rfl⟩ := hs.exists_finset_coe
    classical
    induction t using Finset.induction_on with
    | empty => intro h; simp at h
    | insert a t _ ih =>
      intro _
      rw [Finset.coe_insert]
      rcases (t : Set I).eq_empty_or_nonempty with ht | ht
      · rw [ht, iInf_insert, iInf_emptyset, inf_top_eq]; exact hU a
      · rw [iInf_insert]; exact hinf _ _ (hU a) (ih (Set.toFinite _) ht)
  exact key _ (Set.toFinite _) S.nonempty
def capAff [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) (S : NE I) : X.affineOpens :=
  ⟨cap U S, isAffineOpen_cap U hU hinf S⟩
theorem capAff_mono [Finite I] (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)) :
    Monotone (capAff U hU hinf) := fun _ _ h => cap_mono U h
section Maps
variable {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
  (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))
abbrev capF : (NE I)ᵒᵖ ⥤ CommAlgCat.{0} R := (capAff_mono U hU hinf).functor.op ⋙ OAff s
def cv (T : (NE I)ᵒᵖ) : (capF s U hU hinf).obj T ≃+* Γ(X, cap U T.unop) := RingEquiv.refl _
def toPos (c : C1 U) : CatCoh.C1 (capF s U hU hinf) :=
  fun T T' _ => (cv s U hU hinf T').symm (rsT (c T.unop.pt T'.unop.pt) (cap U T'.unop))
def toCech (f : CatCoh.C1 (capF s U hU hinf)) : C1 U := fun i j =>
  rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single i)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_left i j)).op))
      (U i ⊓ U j) -
    rsT (cv s U hU hinf (op (NE.pair i j)) (f (op (NE.single j)) (op (NE.pair i j)) (homOfLE (NE.pair_le_single_right i j)).op))
      (U i ⊓ U j)
end Maps
end GlobalTheory.CechCmp
namespace GlobalTheory.CechCmp
variable {I : Type} {X : Scheme.{0}} {R : Type} [CommRing R] [Finite I] (s : X ⟶ Sp R) (U : I → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W))
end GlobalTheory.CechCmp


