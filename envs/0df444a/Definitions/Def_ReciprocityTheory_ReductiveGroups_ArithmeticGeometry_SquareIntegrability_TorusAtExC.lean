-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtExC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtExC
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:46:34.483855+00:00
-- url     : https://prove2.me/theorems/4f4d7fa8-754f-5c0a-b40b-f505d36774d2
-- title:
--   Torus At Ex C
-- statement:
--   Definitions and structural lemmas for Torus At Ex C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtExC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtExB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_Data_conjugate_conjugate__4a5ffdebff34
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_conj_mem_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_sum_emb_split
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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_c_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_linIndR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_span_embV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_zero_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_finrank
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
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField ReciprocityTheory.ChartRestriction.G.FD ComplexConjugate
noncomputable section
namespace TX
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
open Classical in

def dimT (σ : E →+* ℂ) : ℕ := if σ ∈ X.Ψ then X.p0 else r - X.p0
theorem conj_notMem (τ : X.Ψ) : ComplexEmbedding.conjugate τ.1 ∉ X.Ψ := by
  rw [← X.conj_mem_iff, Data.conjugate_conjugate']; exact τ.2
theorem dimT_of_mem {σ : E →+* ℂ} (h : σ ∈ X.Ψ) : dimT X σ = X.p0 := by
  classical
  simp [dimT, h]
theorem dimT_of_notMem {σ : E →+* ℂ} (h : σ ∉ X.Ψ) : dimT X σ = r - X.p0 := by
  classical
  simp [dimT, h]
theorem dimT_le (σ : E →+* ℂ) : dimT X σ ≤ r := by
  classical
  unfold dimT; split_ifs
  · exact X.p0_le
  · omega
theorem dimT_conj (σ : E →+* ℂ) : dimT X σ + dimT X (ComplexEmbedding.conjugate σ) = r := by
  by_cases h : σ ∈ X.Ψ
  · have h' : ComplexEmbedding.conjugate σ ∉ X.Ψ := by rw [X.conj_mem_iff]; exact not_not.mpr h
    rw [dimT_of_mem X h, dimT_of_notMem X h']; have := X.p0_le; omega
  · have h' : ComplexEmbedding.conjugate σ ∈ X.Ψ := (X.conj_mem_iff σ).mpr h
    rw [dimT_of_notMem X h, dimT_of_mem X h']; have := X.p0_le; omega
def psiOf (σ : E →+* ℂ) (h : σ ∉ X.Ψ) : X.Ψ := ⟨ComplexEmbedding.conjugate σ, (X.conj_mem_iff σ).mpr h⟩
theorem psiOf_conj (τ : X.Ψ) : psiOf X (ComplexEmbedding.conjugate τ.1) (conj_notMem X τ) = τ :=
  Subtype.ext (Data.conjugate_conjugate' τ.1)
theorem hermC_add_left (τ : E →+* ℂ) (u u' v : Fin r → ℂ) :
    hermC τ X.Gm (u + u') v = hermC τ X.Gm u v + hermC τ X.Gm u' v := by
  simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
theorem hermC_smul_left (τ : E →+* ℂ) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ X.Gm (c • u) v = c * hermC τ X.Gm u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
theorem hermC_sum_left (τ : E →+* ℂ) {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ X.Gm (∑ i ∈ s, f i) v = ∑ i ∈ s, hermC τ X.Gm (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hermC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hermC_add_left, ih]
variable (e : X.Ψ → Fin r → (Fin r → ℂ))
theorem neg_lt (σ : E →+* ℂ) (h : σ ∉ X.Ψ) (a : Fin (dimT X σ)) : X.p0 + a.1 < r := by
  have h1 := dimT_of_notMem X h
  have := a.2; have := X.p0_le; omega
open Classical in

def coordF (u : X.Ψ → Fin r → ℂ) (i : Idx (dimT X)) : ℂ :=
  if h : i.1 ∈ X.Ψ then
    (Real.sqrt (X.c ⟨i.1, h⟩) : ℂ) *
      hermC i.1 X.Gm (u ⟨i.1, h⟩) (e ⟨i.1, h⟩ ⟨i.2.1, lt_of_lt_of_le i.2.2 (dimT_le X i.1)⟩)
  else
    (Real.sqrt (X.c (psiOf X i.1 h)) : ℂ) *
      conj (-hermC (psiOf X i.1 h).1 X.Gm (u (psiOf X i.1 h))
        (e (psiOf X i.1 h) ⟨X.p0 + i.2.1, neg_lt X i.1 h i.2⟩))
def Lc : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] Vsp (dimT X) where
  toFun u := WithLp.toLp 2 (coordF X e u)
  map_add' u u' := by
    ext i
    simp only [coordF, Pi.add_apply, WithLp.toLp_add, PiLp.add_apply]
    split_ifs <;> simp [hermC_add_left, mul_add] <;> ring
  map_smul' c u := by
    ext i
    simp only [coordF, Pi.smul_apply, RingHom.id_apply, PiLp.smul_apply, WithLp.toLp_smul]
    have hc : ∀ w : Fin r → ℂ, c • w = (c : ℂ) • w := fun w => rfl
    split_ifs
    · rw [hc, hermC_smul_left]; simp [Complex.real_smul]; ring
    · rw [hc, hermC_smul_left]; simp [Complex.real_smul]; ring
theorem Lc_pos (u : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (a : Fin (dimT X τ.1)) :
    Lc X e u ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      hermC τ.1 X.Gm (u τ) (e τ ⟨a.1, lt_of_lt_of_le a.2 (dimT_le X τ.1)⟩) := by
  show coordF X e u ⟨τ.1, a⟩ = _
  simp only [coordF, dif_pos τ.2]
theorem Lc_neg (u : X.Ψ → Fin r → ℂ) (τ : X.Ψ) (a : Fin (dimT X (ComplexEmbedding.conjugate τ.1))) :
    Lc X e u ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      conj (-hermC τ.1 X.Gm (u τ) (e τ ⟨X.p0 + a.1, neg_lt X _ (conj_notMem X τ) a⟩)) := by
  show coordF X e u ⟨ComplexEmbedding.conjugate τ.1, a⟩ = _
  simp only [coordF, dif_neg (conj_notMem X τ)]
  rw [psiOf_conj]
variable {X e}
theorem sgn_ne (a : ℕ) : ((sgn X.p0 a : ℝ) : ℂ) ≠ 0 := by
  unfold sgn; split_ifs <;> norm_num
theorem hermC_zero_left (τ : E →+* ℂ) (v : Fin r → ℂ) : hermC τ X.Gm 0 v = 0 := by simp [hermC]
def IsOF (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)) : Prop :=
  ∀ τ : X.Ψ, ∀ a b, hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((sgn X.p0 a : ℝ) : ℂ) else 0
theorem hermC_comb (he : IsOF X e) (τ : X.Ψ) (d : Fin r → ℂ) (a : Fin r) :
    hermC τ.1 X.Gm (∑ j, d j • e τ j) (e τ a) = d a * ((sgn X.p0 a : ℝ) : ℂ) := by
  rw [hermC_sum_left]
  simp only [hermC_smul_left, he τ, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ a]
  simp
theorem e_linInd (he : IsOF X e) (τ : X.Ψ) : LinearIndependent ℂ (e τ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun w => hermC τ.1 X.Gm w (e τ i)) hg
  rw [hermC_comb he τ g i, hermC_zero_left] at h
  exact (mul_eq_zero.mp h).resolve_right (sgn_ne i)
theorem span_top_of_linInd {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] {f : ι → V} (hf : LinearIndependent K f) (hc : Fintype.card ι = Module.finrank K V) :
    Submodule.span K (Set.range f) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card hf, hc]
theorem eq_zero_of_hermC (he : IsOF X e) (τ : X.Ψ) (w : Fin r → ℂ)
    (hw : ∀ a, hermC τ.1 X.Gm w (e τ a) = 0) : w = 0 := by
  have hsp : Submodule.span ℂ (Set.range (e τ)) = ⊤ := span_top_of_linInd (e_linInd he τ) (by simp)
  have hwm : w ∈ Submodule.span ℂ (Set.range (e τ)) := hsp ▸ Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hwm
  have hd0 : ∀ a, d a = 0 := by
    intro a
    have h := hw a
    rw [← hd, hermC_comb he τ d a] at h
    exact (mul_eq_zero.mp h).resolve_right (sgn_ne a)
  rw [← hd]; simp [hd0]
theorem Lc_injective (he : IsOF X e) : Function.Injective (Lc X e) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  funext τ
  show u τ = 0
  apply eq_zero_of_hermC he τ
  intro a
  have hsc : (Real.sqrt (X.c τ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (QuadraticLatticeForms.c_pos X τ)).ne'
  by_cases ha : (a : ℕ) < X.p0
  · have h := congrArg (fun y : Vsp (dimT X) => y ⟨τ.1, ⟨a.1, by rw [dimT_of_mem X τ.2]; exact ha⟩⟩) hu
    simp only [Lc_pos, PiLp.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left hsc
  · have hlt : a.1 - X.p0 < dimT X (ComplexEmbedding.conjugate τ.1) := by
      rw [dimT_of_notMem X (conj_notMem X τ)]; have := a.2; omega
    have h := congrArg (fun y : Vsp (dimT X) => y ⟨ComplexEmbedding.conjugate τ.1, ⟨a.1 - X.p0, hlt⟩⟩) hu
    simp only [Lc_neg, PiLp.zero_apply] at h
    have hidx : (⟨X.p0 + (a.1 - X.p0), neg_lt X _ (conj_notMem X τ) ⟨a.1 - X.p0, hlt⟩⟩ : Fin r) = a :=
      Fin.ext (by simp only; omega)
    rw [hidx] at h
    have h2 := (mul_eq_zero.mp h).resolve_left hsc
    simpa using h2
variable (X) in
theorem card_idx : Fintype.card (Idx (dimT X)) = Fintype.card X.Ψ * r := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have h := X.sum_emb_split (fun σ => ((dimT X σ : ℕ) : ℂ))
  have h2 : ∑ τ : X.Ψ, (((dimT X τ.1 : ℕ) : ℂ) + ((dimT X (ComplexEmbedding.conjugate τ.1) : ℕ) : ℂ)) =
      ((Fintype.card X.Ψ * r : ℕ) : ℂ) := by
    simp only [← Nat.cast_add, dimT_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast; ring
  rw [h2] at h
  exact_mod_cast h
variable (X) in
theorem finrank_Λ : Module.finrank ℤ X.Λ = 2 * (Fintype.card X.Ψ * r) := by
  have b := Module.Basis.mk (RealPlaceEmbeddings.linIndR X (RealPlaceEmbeddings.zb X)) (RealPlaceEmbeddings.span_embV X (RealPlaceEmbeddings.zb X)).ge
  have h := Module.finrank_eq_card_basis b
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  rw [← h]; ring
variable (X) in
theorem finrank_V : Module.finrank ℝ (Vsp (dimT X)) = 2 * Fintype.card (Idx (dimT X)) := cab_finrank
theorem linInd_V (he : IsOF X e) :
    LinearIndependent ℝ (fun i => Lc X e (X.embV (RealPlaceEmbeddings.zb X i : Fin r → E))) :=
  (RealPlaceEmbeddings.linIndR X (RealPlaceEmbeddings.zb X)).map' (Lc X e) (LinearMap.ker_eq_bot.mpr (Lc_injective he))
variable (X) in
theorem card_eq : Fintype.card (Fin (Module.finrank ℤ X.Λ)) = Module.finrank ℝ (Vsp (dimT X)) := by
  rw [Fintype.card_fin, finrank_Λ, finrank_V, card_idx]
theorem span_V (he : IsOF X e) :
    Submodule.span ℝ (Set.range (fun i => Lc X e (X.embV (RealPlaceEmbeddings.zb X i : Fin r → E)))) = ⊤ :=
  span_top_of_linInd (linInd_V he) (card_eq X)
def bV (he : IsOF X e) : Module.Basis (Fin (Module.finrank ℤ X.Λ)) ℝ (Vsp (dimT X)) :=
  Module.Basis.mk (linInd_V he) (span_V he).ge
variable (X) in
theorem card_eq' : Module.finrank ℤ X.Λ = 2 * Fintype.card (Idx (dimT X)) := by
  rw [finrank_Λ, card_idx]
def bT (he : IsOF X e) : Module.Basis (Fin (2 * Fintype.card (Idx (dimT X)))) ℝ (Vsp (dimT X)) :=
  (bV he).reindex (finCongr (card_eq' X))
variable (X e) in

def phi : (Fin r → E) →+ Vsp (dimT X) where
  toFun v := Lc X e (X.embV v)
  map_zero' := by
    have : X.embV (0 : Fin r → E) = 0 := by funext τ a; simp [Data.embV, Data.emb]
    rw [this, map_zero]
  map_add' u v := by
    have : X.embV (u + v) = X.embV u + X.embV v := by funext τ a; simp [Data.embV, Data.emb]
    rw [this, map_add]
end TX
end
end ReciprocityTheory.ChartRestriction.G.I2


