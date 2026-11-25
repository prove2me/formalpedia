-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealTangentSpace
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:16:08.164798+00:00
-- url     : https://prove2.me/theorems/fd39dd47-8944-51f9-b518-ce7d2bb21317
-- title:
--   Real Tangent Space
-- statement:
--   Definitions and structural lemmas for Real Tangent Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealTangentSpace.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeSpanMembership
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_maj_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_add_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_gI_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_maj_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_smul_fam_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_MajorantOperators_zero_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_orthogonal_lattice_decomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace RealTangentSpace
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
def Usub (z : Frame X.Ψ r) (ξ : Fin r → E) : Submodule ℝ (X.Ψ → Fin r → ℂ) where
  carrier := X.Uz z ξ
  add_mem' := MajorantOperators.add_mem
  zero_mem' := MajorantOperators.zero_mem z ξ
  smul_mem' c u hu := by
    have h := MajorantOperators.smul_fam_mem (fun _ => (c : ℂ)) hu
    convert h using 1
    funext τ
    exact (Complex.coe_smul c (u τ)).symm
def VT (z : Frame X.Ψ r) (ξ : Fin r → E) : Type := ↥(Usub (X := X) z ξ)
variable (z : Frame X.Ψ r) (ξ : Fin r → E)
noncomputable instance : AddCommGroup (VT (X := X) z ξ) := inferInstanceAs (AddCommGroup ↥(Usub (X := X) z ξ))
noncomputable instance : Module ℝ (VT (X := X) z ξ) := inferInstanceAs (Module ℝ ↥(Usub (X := X) z ξ))
instance : FiniteDimensional ℝ (VT (X := X) z ξ) :=
  inferInstanceAs (FiniteDimensional ℝ ↥(Usub (X := X) z ξ))
def VT.val {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) : X.Ψ → Fin r → ℂ :=
  (u : ↥(Usub (X := X) z ξ)).1
def VT.mk {z : Frame X.Ψ r} {ξ : Fin r → E} (u : X.Ψ → Fin r → ℂ) (hu : u ∈ X.Uz z ξ) :
    VT (X := X) z ξ := (⟨u, hu⟩ : ↥(Usub (X := X) z ξ))
@[simp] theorem VT.val_mk {z : Frame X.Ψ r} {ξ : Fin r → E} (u : X.Ψ → Fin r → ℂ)
    (hu : u ∈ X.Uz z ξ) : (VT.mk u hu).val = u := rfl
theorem VT.ext {z : Frame X.Ψ r} {ξ : Fin r → E} {u v : VT (X := X) z ξ} (h : u.val = v.val) :
    u = v := by
  exact Subtype.ext h
@[simp] theorem VT.val_add {z : Frame X.Ψ r} {ξ : Fin r → E} (u v : VT (X := X) z ξ) :
    (u + v).val = u.val + v.val := rfl
@[simp] theorem VT.val_smul {z : Frame X.Ψ r} {ξ : Fin r → E} (c : ℝ) (u : VT (X := X) z ξ) :
    (c • u).val = c • u.val := rfl
@[simp] theorem VT.val_zero {z : Frame X.Ψ r} {ξ : Fin r → E} : (0 : VT (X := X) z ξ).val = 0 := rfl
@[simp] theorem VT.val_neg {z : Frame X.Ψ r} {ξ : Fin r → E} (u : VT (X := X) z ξ) :
    (-u).val = -u.val := rfl
@[simp] theorem VT.val_sub {z : Frame X.Ψ r} {ξ : Fin r → E} (u v : VT (X := X) z ξ) :
    (u - v).val = u.val - v.val := rfl
variable [hz : Fact (z ∈ X.dom)]
@[instance_reducible]
noncomputable def core : InnerProductSpace.Core ℝ (VT (X := X) z ξ) where
  inner u v := MajorantOperators.gI z u.val v.val
  conj_inner_symm u v := by
    simp only [starRingEnd_apply, star_trivial]
    exact MajorantOperators.gI_comm hz.out _ _
  re_inner_nonneg u := by
    simp only [RCLike.re_to_real]
    rw [MajorantOperators.gI_self hz.out]
    exact Finset.sum_nonneg fun τ _ => MajorantOperators.maj_nonneg hz.out τ _
  add_left u v w := by
    show MajorantOperators.gI z (u.val + v.val) w.val = _
    exact MajorantOperators.gI_add_left z _ _ _
  smul_left u v c := by
    show MajorantOperators.gI z (c • u.val) v.val = _
    rw [MajorantOperators.gI_smul_left]
    simp
  definite u h := by
    rw [MajorantOperators.gI_self hz.out] at h
    have h0 : ∀ τ ∈ Finset.univ, X.maj z τ (u.val τ) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => MajorantOperators.maj_nonneg hz.out τ _).mp h
    apply VT.ext
    funext τ
    by_contra hne
    exact (X.maj_pos hz.out τ hne).ne' (h0 τ (Finset.mem_univ τ))
noncomputable instance : NormedAddCommGroup (VT (X := X) z ξ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (VT (X := X) z ξ) _ _ _ (core z ξ)
noncomputable instance : InnerProductSpace ℝ (VT (X := X) z ξ) :=
  InnerProductSpace.ofCore (core z ξ).toCore
omit hz in
theorem ucomp_add (u v : X.Ψ → Fin r → ℂ) :
    X.ucomp z ξ (u + v) = X.ucomp z ξ u + X.ucomp z ξ v := by
  have hHf : ∀ (σ : X.Ψ) (a b w : Fin r → ℂ),
      X.Hf z σ (a + b) w = X.Hf z σ a w + X.Hf z σ b w := by
    intro σ a b w
    rw [Data.Hf, Data.Hf, Data.Hf, Data.ppos_add, ← hermC_add_left]
    congr 1
    rw [smul_add]
    abel
  funext τ
  simp only [Data.ucomp, Data.aproj, Data.lineV, Pi.add_apply, Pi.sub_apply, hHf, add_div, add_smul]
  abel
theorem embV_add (u v : Fin r → E) : X.embV (u + v) = X.embV u + X.embV v := by
  funext τ a
  simp [Data.embV, Data.emb]
omit hz in
theorem embV_mem_Iperp {μ : Fin r → E} (hμ : μ ∈ X.Λp ξ) : X.embV μ ∈ X.Iperp ξ := by
  have hk : herm X.Gm μ ξ = 0 := AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp hμ).2
  show ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.embV μ τ) (Data.emb τ.1 ξ) = 0
  intro τ
  simp only [Data.embV]
  rw [hermC_emb, hk, map_zero]
noncomputable def phi (hξ : X.IsIso ξ) : X.Λp ξ →+ VT (X := X) z ξ :=
  AddMonoidHom.mk' (fun μ => VT.mk (X.ucomp z ξ (X.embV μ))
      (orthogonal_lattice_decomposition r X ξ hξ z hz.out _ (embV_mem_Iperp ξ μ.2)))
    (fun μ ν => VT.ext (by
      simp only [VT.val_mk, VT.val_add, AddSubgroup.coe_add]
      rw [embV_add, ucomp_add]))
noncomputable def Lat (hξ : X.IsIso ξ) : Submodule ℤ (VT (X := X) z ξ) :=
  (phi z ξ hξ).range.toIntSubmodule
end RealTangentSpace
end ReciprocityTheory.ChartRestriction.G.FD


