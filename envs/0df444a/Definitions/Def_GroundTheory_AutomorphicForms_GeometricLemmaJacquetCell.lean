-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:14.091246+00:00
-- url     : https://prove2.me/theorems/614fd4c3-fc3a-5f4e-a1f7-d74238a0c3ca
-- title:
--   Geometric Lemma Jacquet Cell
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Jacquet Cell, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaJacquetCell.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCount
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgFinite_map_mulEquiv
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgFinite_of_isOpen
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_add
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_linearMap
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_map_mulEquiv
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_smul
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellCoinvRep_mk
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellLeviParabolic_le_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_permGL_mem_blockUpper_iff
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_unipotentCompactG_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_unipotentCompactG_support
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_unipotentCompactG
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_conj_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_parabolicIndSpace
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_rightStab
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_parabolicInd_permGL_mul_cellLeviParabolic
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_parabolicInd_permGL_mul_cellUnipotent
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_inf_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_ne_zero_of_isCompact_of_isOpen
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_smul_avgOver_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relVol_eq_relIndex_mul
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relVol_pos
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentCompactG_eq
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentCompactG_le
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentCompactG_mono
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_mem_indSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
section CellCompact
variable (γ) in

def IsCellCompact (K : Subgroup (GL (Fin n) F)) : Prop :=
  K ≤ unipotentRadical F n γ ∧ IsCompact (K : Set (GL (Fin n) F)) ∧
    ∃ U : Subgroup (GL (Fin n) F), IsOpen (U : Set (GL (Fin n) F)) ∧ unipotentRadical F n γ ⊓ U ≤ K
theorem isCellCompact_unipotentCompactG (e : ℕ) :
    IsCellCompact γ (unipotentCompactG (F := F) γ e) :=
  ⟨unipotentCompactG_le e, isCompact_unipotentCompactG e,
    _, isOpen_conj_integralGL (rankTorus F n γ e), (unipotentCompactG_eq e).ge⟩
theorem IsCellCompact.relIndex_ne_zero {K K' : Subgroup (GL (Fin n) F)} (hK : IsCellCompact γ K)
    (hK' : IsCellCompact γ K') : K.relIndex K' ≠ 0 := by
  obtain ⟨U, hU, hUK⟩ := hK.2.2
  have h1 : (unipotentRadical F n γ ⊓ U).relIndex K' ≠ 0 := by
    have : (unipotentRadical F n γ ⊓ U).subgroupOf K' = U.subgroupOf K' := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hK'.1 x.2, h⟩⟩
    rw [Subgroup.relIndex, this, ← Subgroup.relIndex]
    exact relIndex_ne_zero_of_isCompact_of_isOpen hK'.2.1 hU
  intro h0
  exact h1 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left K' hUK))
theorem IsCellCompact.exists_le {K : Subgroup (GL (Fin n) F)} (hK : IsCellCompact γ K) :
    ∃ e : ℕ, K ≤ unipotentCompactG γ e := by
  obtain ⟨e, he⟩ := exists_unipotentCompactG_of_isCompact hK.2.1 hK.1
  exact ⟨e, fun x hx => he hx⟩
theorem IsCellCompact.map_conj {K : Subgroup (GL (Fin n) F)} (hK : IsCellCompact γ K)
    {b : GL (Fin n) F} (hb : b ∈ levi F n γ) :
    IsCellCompact γ (K.map (MulAut.conj b).toMonoidHom) := by
  obtain ⟨hKN, hKc, U, hU, hUK⟩ := hK
  refine ⟨?_, ?_, U.map (MulAut.conj b).toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_unipotentRadical (levi_le_blockUpper hb) (hKN hx)
  · rw [Subgroup.coe_map]
    exact hKc.image (conjHomeomorph b).continuous
  · rw [Subgroup.coe_map]
    exact (conjHomeomorph b).isOpenMap _ hU
  · rintro x ⟨hxN, y, hy, rfl⟩
    refine ⟨y, hUK ⟨?_, hy⟩, rfl⟩
    have : y = b⁻¹ * ((MulAut.conj b).toMonoidHom y) * b := by
      change y = b⁻¹ * (b * y * b⁻¹) * b
      group
    rw [this]
    simpa using conj_mem_unipotentRadical ((blockUpper F n γ).inv_mem (levi_le_blockUpper hb)) hxN
end CellCompact
section CellFun
variable (F β γ w) in

def cellNorm (K : Subgroup (GL (Fin n) F)) : ℝ :=
  relVol (unipotentCompactG (F := F) γ 0) K /
    relVol (unipotentCompactG (F := F) γ 0 ⊓ cellUnipotent F β γ w) (K ⊓ cellUnipotent F β γ w)
theorem cellNorm_pos {K : Subgroup (GL (Fin n) F)} (hK : IsCellCompact γ K) :
    0 < cellNorm F β γ w K := by
  have h0 := isCellCompact_unipotentCompactG (F := F) (γ := γ) 0
  unfold cellNorm
  exact div_pos (relVol_pos (h0.relIndex_ne_zero hK) (hK.relIndex_ne_zero h0))
    (relVol_pos (relIndex_inf_ne_zero (h0.relIndex_ne_zero hK))
      (relIndex_inf_ne_zero (hK.relIndex_ne_zero h0)))
theorem cellNorm_eq_of_le {K K' : Subgroup (GL (Fin n) F)} (hK : IsCellCompact γ K)
    (hK' : IsCellCompact γ K') (hKK' : K ≤ K') :
    cellNorm F β γ w K' = cellNorm F β γ w K * K.relIndex K' /
      (K ⊓ cellUnipotent F β γ w).relIndex (K' ⊓ cellUnipotent F β γ w) := by
  have h0 := isCellCompact_unipotentCompactG (F := F) (γ := γ) 0
  unfold cellNorm
  rw [relVol_eq_relIndex_mul hKK' (hK.relIndex_ne_zero h0),
    relVol_eq_relIndex_mul (inf_le_inf_right _ hKK')
      (relIndex_inf_ne_zero (hK.relIndex_ne_zero h0))]
  have ha : ((K ⊓ cellUnipotent F β γ w).relIndex (K' ⊓ cellUnipotent F β γ w) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (relIndex_inf_ne_zero (hK.relIndex_ne_zero hK'))
  have hb : relVol (unipotentCompactG (F := F) γ 0 ⊓ cellUnipotent F β γ w)
      (K ⊓ cellUnipotent F β γ w) ≠ 0 :=
    (relVol_pos (relIndex_inf_ne_zero (h0.relIndex_ne_zero hK))
      (relIndex_inf_ne_zero (hK.relIndex_ne_zero h0))).ne'
  field_simp
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable (w) in

def cellFun (f : parabolicIndSpace F n β σ) (m : GL (Fin n) F) : GL (Fin n) F → W :=
  fun y => (f : GL (Fin n) F → W) (permGL F w * y * m)
theorem cellFun_mul_left (f : parabolicIndSpace F n β σ) (m : GL (Fin n) F)
    (a : cellUnipotent F β γ w) (y : GL (Fin n) F) :
    cellFun w σ f m ((a : GL (Fin n) F) * y) = cellRepA β γ w σ a (cellFun w σ f m y) := by
  unfold cellFun
  rw [show permGL F w * ((a : GL (Fin n) F) * y) * m = permGL F w * ((a : GL (Fin n) F) * (y * m))
    by group, parabolicInd_permGL_mul_cellUnipotent, ← mul_assoc]
theorem exists_rightStab_parabolicInd (f : parabolicIndSpace F n β σ) :
    ∃ K : Subgroup (GL (Fin n) F), IsOpen (K : Set (GL (Fin n) F)) ∧
      ∀ k ∈ K, ∀ g, (f : GL (Fin n) F → W) (g * k) = (f : GL (Fin n) F → W) g :=
  ((mem_parabolicIndSpace σ).1 f.2).2
theorem avgFinite_cellFun (f : parabolicIndSpace F n β σ) (m : GL (Fin n) F)
    {K : Subgroup (GL (Fin n) F)} (hK : IsCompact (K : Set (GL (Fin n) F))) :
    AvgFinite K (cellFun w σ f m) := by
  obtain ⟨U, hU, hUf⟩ := exists_rightStab_parabolicInd σ f
  refine avgFinite_of_isOpen (U := U.map (MulAut.conj m).toMonoidHom) hK ?_ ?_
  · rw [Subgroup.coe_map]
    exact (conjHomeomorph m).isOpenMap _ hU
  · rintro _ ⟨k, hk, rfl⟩
    rw [mem_rightStab]
    intro y
    unfold cellFun
    change (f : GL (Fin n) F → W) (permGL F w * (y * (m * k * m⁻¹)) * m) = _
    rw [show permGL F w * (y * (m * k * m⁻¹)) * m = permGL F w * y * m * k by group, hUf k hk]
variable (γ w) in

def CellSupp (f : parabolicIndSpace F n β σ) (m : GL (Fin n) F) (K : Subgroup (GL (Fin n) F)) :
    Prop :=
  ∀ y ∈ unipotentRadical F n γ, cellFun w σ f m y ≠ 0 →
    ∃ a ∈ cellUnipotent F β γ w, ∃ k ∈ K, y = a * k
theorem CellSupp.mono {σ : Representation ℂ (levi F n β) W} {f : parabolicIndSpace F n β σ} {m : GL (Fin n) F}
    {K K' : Subgroup (GL (Fin n) F)} (h : CellSupp γ w σ f m K) (hKK' : K ≤ K') :
    CellSupp γ w σ f m K' := fun y hy hf => by
  obtain ⟨a, ha, k, hk, rfl⟩ := h y hy hf
  exact ⟨a, ha, k, hKK' hk, rfl⟩
theorem exists_cellSupp {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) {m : GL (Fin n) F}
    (hm : m ∈ levi F n γ) : ∃ e : ℕ, CellSupp γ w σ f m (unipotentCompactG γ e) := by
  obtain ⟨e, he⟩ := exists_unipotentCompactG_support w hYo hCY hf hm
  refine ⟨e, fun y hy hfy => ?_⟩
  obtain ⟨a, haN, haP, v, hv, rfl⟩ := he y hy hfy
  exact ⟨a, ⟨haN, (conj_permGL_mem_blockUpper_iff w).1 haP⟩, v, hv, rfl⟩
end CellFun
section CellJacquet
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable (γ w) in

def cellEv (f : parabolicIndSpace F n β σ) (m : GL (Fin n) F) (K : Subgroup (GL (Fin n) F)) :
    Representation.Coinvariants (cellRepA β γ w σ) :=
  ((cellNorm F β γ w K : ℝ) : ℂ) •
    Representation.Coinvariants.mk _ (avgOver K (cellFun w σ f m) 1)
theorem mk_comp_cellRepA (a : cellUnipotent F β γ w) :
    Representation.Coinvariants.mk (cellRepA β γ w σ) ∘ₗ cellRepA β γ w σ a =
      Representation.Coinvariants.mk _ :=
  LinearMap.ext fun v => Representation.Coinvariants.mk_self_apply _ a v
theorem cellEv_eq_of_le (f : parabolicIndSpace F n β σ) (m : GL (Fin n) F)
    {K K' : Subgroup (GL (Fin n) F)} (hK : IsCellCompact γ K) (hK' : IsCellCompact γ K')
    (hKK' : K ≤ K') (hs : CellSupp γ w σ f m K) :
    cellEv γ w σ f m K' = cellEv γ w σ f m K := by
  have hθ := relIndex_smul_avgOver_eq (fun a => cellRepA β γ w σ a)
    (Representation.Coinvariants.mk _) (mk_comp_cellRepA σ) (h := cellFun w σ f m)
    (cellFun_mul_left σ f m) hKK' (avgFinite_cellFun σ f m hK.2.1) (hK.relIndex_ne_zero hK')
    (fun y hy hfy => hs y (hK'.1 hy) hfy)
  unfold cellEv
  rw [cellNorm_eq_of_le hK hK' hKK']
  have ha : ((K.relIndex K' : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hK.relIndex_ne_zero hK')
  have hb : (((K ⊓ cellUnipotent F β γ w).relIndex (K' ⊓ cellUnipotent F β γ w) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (relIndex_inf_ne_zero (hK.relIndex_ne_zero hK'))
  set X' := Representation.Coinvariants.mk (cellRepA β γ w σ) (avgOver K' (cellFun w σ f m) 1)
  set X := Representation.Coinvariants.mk (cellRepA β γ w σ) (avgOver K (cellFun w σ f m) 1)
  set c := cellNorm F β γ w K
  set a := K.relIndex K'
  set b := (K ⊓ cellUnipotent F β γ w).relIndex (K' ⊓ cellUnipotent F β γ w)
  calc ((c * a / b : ℝ) : ℂ) • X' = ((c : ℂ) / b) • ((a : ℂ) • X') := by
        rw [smul_smul]
        congr 1
        push_cast
        ring
    _ = ((c : ℂ) / b) • ((b : ℂ) • X) := by rw [hθ]
    _ = (c : ℂ) • X := by
        rw [smul_smul]
        congr 1
        field_simp
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
include hYo hCY
theorem exists_cellEv_eventually {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y)
    {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    ∃ v, ∀ᶠ e in atTop, cellEv γ w σ f m (unipotentCompactG γ e) = v := by
  obtain ⟨e₀, he₀⟩ := exists_cellSupp σ hYo hCY hf hm
  exact ⟨cellEv γ w σ f m (unipotentCompactG γ e₀), eventually_atTop.2 ⟨e₀, fun e he =>
    cellEv_eq_of_le σ f m (isCellCompact_unipotentCompactG e₀) (isCellCompact_unipotentCompactG e)
      (unipotentCompactG_mono he) he₀⟩⟩
omit hYo hCY in
variable (γ w) in

def cellJacquet (f : parabolicIndSpace F n β σ) (m : GL (Fin n) F) :
    Representation.Coinvariants (cellRepA β γ w σ) :=
  Classical.epsilon fun v => ∀ᶠ e in atTop, cellEv γ w σ f m (unipotentCompactG γ e) = v
theorem eventually_cellEv_eq_cellJacquet {f : parabolicIndSpace F n β σ}
    (hf : f ∈ supportedIn σ Y) {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    ∀ᶠ e in atTop, cellEv γ w σ f m (unipotentCompactG γ e) = cellJacquet γ w σ f m :=
  Classical.epsilon_spec (exists_cellEv_eventually σ hYo hCY hf hm)
theorem cellJacquet_eq_cellEv {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y)
    {m : GL (Fin n) F} (hm : m ∈ levi F n γ) {K : Subgroup (GL (Fin n) F)}
    (hK : IsCellCompact γ K) (hs : CellSupp γ w σ f m K) :
    cellJacquet γ w σ f m = cellEv γ w σ f m K := by
  obtain ⟨e₁, he₁⟩ := hK.exists_le
  obtain ⟨e, he, hge⟩ := ((eventually_cellEv_eq_cellJacquet σ hYo hCY hf hm).and
    (eventually_ge_atTop e₁)).exists
  rw [← he]
  exact cellEv_eq_of_le σ f m hK (isCellCompact_unipotentCompactG e)
    (he₁.trans (unipotentCompactG_mono hge)) hs
theorem exists_cellSupp_pair {f g : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y)
    (hg : g ∈ supportedIn σ Y) {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    ∃ e, CellSupp γ w σ f m (unipotentCompactG γ e) ∧ CellSupp γ w σ g m (unipotentCompactG γ e) := by
  obtain ⟨e₁, h₁⟩ := exists_cellSupp σ hYo hCY hf hm
  obtain ⟨e₂, h₂⟩ := exists_cellSupp σ hYo hCY hg hm
  exact ⟨max e₁ e₂, h₁.mono (unipotentCompactG_mono (le_max_left _ _)),
    h₂.mono (unipotentCompactG_mono (le_max_right _ _))⟩
theorem cellJacquet_add {f g : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y)
    (hg : g ∈ supportedIn σ Y) {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    cellJacquet γ w σ (f + g) m = cellJacquet γ w σ f m + cellJacquet γ w σ g m := by
  obtain ⟨e, hfe, hge⟩ := exists_cellSupp_pair σ hYo hCY hf hg hm
  have hfg : CellSupp γ w σ (f + g) m (unipotentCompactG γ e) := by
    intro y hy hy0
    by_cases h : cellFun w σ f m y = 0
    · refine hge y hy fun h' => hy0 ?_
      show (f : GL (Fin n) F → W) _ + (g : GL (Fin n) F → W) _ = 0
      exact (congrArg₂ (· + ·) h h').trans (add_zero 0)
    · exact hfe y hy h
  have hK := isCellCompact_unipotentCompactG (F := F) (γ := γ) e
  rw [cellJacquet_eq_cellEv σ hYo hCY (add_mem hf hg) hm hK hfg,
    cellJacquet_eq_cellEv σ hYo hCY hf hm hK hfe, cellJacquet_eq_cellEv σ hYo hCY hg hm hK hge]
  unfold cellEv
  have : cellFun w σ (f + g) m = cellFun w σ f m + cellFun w σ g m := rfl
  rw [this, avgOver_add (avgFinite_cellFun σ f m hK.2.1) (avgFinite_cellFun σ g m hK.2.1),
    Pi.add_apply, map_add, smul_add]
theorem cellJacquet_smul (c : ℂ) {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y)
    {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    cellJacquet γ w σ (c • f) m = c • cellJacquet γ w σ f m := by
  obtain ⟨e, hfe⟩ := exists_cellSupp σ hYo hCY hf hm
  have hcf : CellSupp γ w σ (c • f) m (unipotentCompactG γ e) := by
    intro y hy hy0
    refine hfe y hy fun h => hy0 ?_
    show c • (f : GL (Fin n) F → W) _ = 0
    exact (congrArg (c • ·) h).trans (smul_zero c)
  have hK := isCellCompact_unipotentCompactG (F := F) (γ := γ) e
  rw [cellJacquet_eq_cellEv σ hYo hCY (Submodule.smul_mem _ c hf) hm hK hcf,
    cellJacquet_eq_cellEv σ hYo hCY hf hm hK hfe]
  unfold cellEv
  have : cellFun w σ (c • f) m = c • cellFun w σ f m := rfl
  rw [this, avgOver_smul c (avgFinite_cellFun σ f m hK.2.1), Pi.smul_apply, map_smul,
    smul_comm]
omit hYo hCY in

theorem exists_cellJacquet_mul_right (f : parabolicIndSpace F n β σ) :
    ∃ U : Subgroup (GL (Fin n) F), IsOpen (U : Set (GL (Fin n) F)) ∧
      ∀ k ∈ U, ∀ m, cellJacquet γ w σ f (m * k) = cellJacquet γ w σ f m := by
  obtain ⟨U, hU, hUf⟩ := exists_rightStab_parabolicInd σ f
  refine ⟨U, hU, fun k hk m => ?_⟩
  have : ∀ K, cellEv γ w σ f (m * k) K = cellEv γ w σ f m K := by
    intro K
    unfold cellEv cellFun
    congr 3
    funext y
    rw [← mul_assoc, hUf k hk]
  unfold cellJacquet
  simp only [this]
end CellJacquet
section Character
theorem map_conj_cellUnipotent {b : GL (Fin n) F} (hb : b ∈ cellLeviParabolic F β γ w) :
    (cellUnipotent F β γ w).map (MulAut.conj b).toMonoidHom = cellUnipotent F β γ w := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact conj_mem_cellUnipotent hb ha
  · intro a ha
    refine ⟨b⁻¹ * a * b, ?_, by show b * (b⁻¹ * a * b) * b⁻¹ = a; group⟩
    simpa using conj_mem_cellUnipotent ((cellLeviParabolic F β γ w).inv_mem hb) ha
theorem cellNorm_map_conj_eq_of_le {b : GL (Fin n) F} (hb : b ∈ cellLeviParabolic F β γ w)
    {K K' : Subgroup (GL (Fin n) F)} (hK : IsCellCompact γ K) (hK' : IsCellCompact γ K')
    (hKK' : K ≤ K') :
    cellNorm F β γ w K / cellNorm F β γ w (K.map (MulAut.conj b).toMonoidHom) =
      cellNorm F β γ w K' / cellNorm F β γ w (K'.map (MulAut.conj b).toMonoidHom) := by
  have hbM : b ∈ levi F n γ := cellLeviParabolic_le_levi hb
  have hinj : Function.Injective (MulAut.conj b).toMonoidHom := (MulAut.conj b).injective
  have h1 := cellNorm_eq_of_le (w := w) (β := β) hK hK' hKK'
  have h2 := cellNorm_eq_of_le (w := w) (β := β) (hK.map_conj hbM) (hK'.map_conj hbM)
    (Subgroup.map_mono hKK')
  rw [Subgroup.relIndex_map_map_of_injective _ _ hinj] at h2
  have hA : ∀ L : Subgroup (GL (Fin n) F), L.map (MulAut.conj b).toMonoidHom ⊓
      cellUnipotent F β γ w = (L ⊓ cellUnipotent F β γ w).map (MulAut.conj b).toMonoidHom := by
    intro L
    rw [Subgroup.map_inf_eq _ _ _ hinj, map_conj_cellUnipotent hb]
  rw [hA K, hA K', Subgroup.relIndex_map_map_of_injective _ _ hinj] at h2
  rw [h1, h2]
  have hc1 := (cellNorm_pos (w := w) (β := β) hK).ne'
  have hc2 := (cellNorm_pos (w := w) (β := β) (hK.map_conj hbM)).ne'
  have ha : ((K.relIndex K' : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hK.relIndex_ne_zero hK')
  have hb' : (((K ⊓ cellUnipotent F β γ w).relIndex (K' ⊓ cellUnipotent F β γ w) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (relIndex_inf_ne_zero (hK.relIndex_ne_zero hK'))
  field_simp
variable (F β γ w) in

def cellChar (b : GL (Fin n) F) : ℝ :=
  cellNorm F β γ w (unipotentCompactG γ 0) /
    cellNorm F β γ w ((unipotentCompactG γ 0).map (MulAut.conj b⁻¹).toMonoidHom)
theorem cellNorm_div_map_conj {b : GL (Fin n) F} (hb : b ∈ cellLeviParabolic F β γ w)
    {K : Subgroup (GL (Fin n) F)} (hK : IsCellCompact γ K) :
    cellNorm F β γ w K / cellNorm F β γ w (K.map (MulAut.conj b⁻¹).toMonoidHom) =
      cellChar F β γ w b := by
  have hb' : b⁻¹ ∈ cellLeviParabolic F β γ w := (cellLeviParabolic F β γ w).inv_mem hb
  have h0 := isCellCompact_unipotentCompactG (F := F) (γ := γ) 0
  obtain ⟨e₁, he₁⟩ := hK.exists_le
  have hE := isCellCompact_unipotentCompactG (F := F) (γ := γ) (max e₁ 0)
  rw [cellChar, cellNorm_map_conj_eq_of_le hb' hK hE (he₁.trans (unipotentCompactG_mono
      (le_max_left _ _))),
    cellNorm_map_conj_eq_of_le hb' h0 hE (unipotentCompactG_mono (le_max_right _ _))]
theorem cellChar_one : cellChar F β γ w 1 = 1 := by
  have h0 := isCellCompact_unipotentCompactG (F := F) (γ := γ) 0
  have : (unipotentCompactG (F := F) γ 0).map (MulAut.conj (1 : GL (Fin n) F)⁻¹).toMonoidHom =
      unipotentCompactG γ 0 := by
    rw [inv_one, map_one]
    exact Subgroup.map_id _
  rw [cellChar, this, div_self (cellNorm_pos h0).ne']
theorem cellChar_mul {b b' : GL (Fin n) F} (hb : b ∈ cellLeviParabolic F β γ w)
    (hb' : b' ∈ cellLeviParabolic F β γ w) :
    cellChar F β γ w (b * b') = cellChar F β γ w b * cellChar F β γ w b' := by
  have h0 := isCellCompact_unipotentCompactG (F := F) (γ := γ) 0
  have h1 := h0.map_conj (cellLeviParabolic_le_levi ((cellLeviParabolic F β γ w).inv_mem hb))
  have hmap : (unipotentCompactG (F := F) γ 0).map (MulAut.conj (b * b')⁻¹).toMonoidHom =
      ((unipotentCompactG (F := F) γ 0).map (MulAut.conj b⁻¹).toMonoidHom).map
        (MulAut.conj b'⁻¹).toMonoidHom := by
    rw [Subgroup.map_map, _root_.mul_inv_rev, map_mul]
    rfl
  rw [← cellNorm_div_map_conj hb' h1, cellChar, hmap]
  have hc1 := (cellNorm_pos (w := w) (β := β) h1).ne'
  unfold cellChar
  field_simp
variable (F β γ w) in

def cellCharHom : cellLeviParabolic F β γ w →* ℂ where
  toFun b := ((cellChar F β γ w b : ℝ) : ℂ)
  map_one' := by simp [cellChar_one]
  map_mul' b b' := by
    simp only [Subgroup.coe_mul]
    rw [cellChar_mul b.2 b'.2]
    push_cast
    rfl
end Character
section JacquetMap
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable (F β γ w) in

abbrev cellLeviSub : Subgroup (levi F n γ) := (cellLeviParabolic F β γ w).subgroupOf (levi F n γ)
variable (F β γ w) in

def cellLeviSubIncl : cellLeviSub F β γ w →* cellLeviParabolic F β γ w where
  toFun x := ⟨((x : levi F n γ) : GL (Fin n) F), x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
variable (β γ w) in

def cellInducing : Representation ℂ (cellLeviSub F β γ w)
    (Representation.Coinvariants (cellRepA β γ w σ)) :=
  twist ((cellCharHom F β γ w).comp (cellLeviSubIncl F β γ w))
    ((cellCoinvRep σ).comp (cellLeviSubIncl F β γ w))
variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
include hYo hCY
theorem cellJacquet_mul_left {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y)
    {b : GL (Fin n) F} (hb : b ∈ cellLeviParabolic F β γ w) {m : GL (Fin n) F}
    (hm : m ∈ levi F n γ) :
    cellJacquet γ w σ f (b * m) =
      ((cellChar F β γ w b : ℝ) : ℂ) • cellCoinvRep σ ⟨b, hb⟩ (cellJacquet γ w σ f m) := by
  have hbM : b ∈ levi F n γ := cellLeviParabolic_le_levi hb
  have hbm : b * m ∈ levi F n γ := (levi F n γ).mul_mem hbM hm
  obtain ⟨e₀, he₀⟩ := exists_cellSupp σ hYo hCY hf hm
  obtain ⟨e₁, he₁⟩ := exists_cellSupp σ hYo hCY hf hbm
  obtain ⟨e₂, he₂⟩ := ((isCellCompact_unipotentCompactG (F := F) (γ := γ) e₀).map_conj hbM).exists_le
  set E := max e₁ e₂
  have hKE := isCellCompact_unipotentCompactG (F := F) (γ := γ) E
  set K' := (unipotentCompactG (F := F) γ E).map (MulAut.conj b⁻¹).toMonoidHom
  have hK' : IsCellCompact γ K' := hKE.map_conj ((levi F n γ).inv_mem hbM)
  have hKE' : K'.map (MulAut.conj b).toMonoidHom = unipotentCompactG (F := F) γ E := by
    rw [Subgroup.map_map]
    have : (MulAut.conj b).toMonoidHom.comp (MulAut.conj b⁻¹).toMonoidHom =
        MonoidHom.id (GL (Fin n) F) := by
      refine MonoidHom.ext fun x => ?_
      show b * (b⁻¹ * x * b⁻¹⁻¹) * b⁻¹ = x
      group
    rw [this, Subgroup.map_id]
  have hs' : CellSupp γ w σ f m K' := by
    refine he₀.mono fun x hx => ?_
    refine ⟨b * x * b⁻¹, unipotentCompactG_mono (le_max_right _ _) (he₂ ⟨x, hx, rfl⟩), ?_⟩
    show b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x
    group
  rw [cellJacquet_eq_cellEv σ hYo hCY hf hbm hKE (he₁.mono (unipotentCompactG_mono
      (le_max_left _ _))), cellJacquet_eq_cellEv σ hYo hCY hf hm hK' hs']
  unfold cellEv
  have hfun : cellFun w σ f (b * m) =
      fun y => cellRepM β γ w σ ⟨b, hb⟩ (cellFun w σ f m ((MulAut.conj b).symm y)) := by
    funext y
    unfold cellFun
    have e : permGL F w * y * (b * m) =
        permGL F w * (b * ((MulAut.conj b).symm y * m)) := by
      rw [MulAut.conj_symm_apply]
      group
    rw [e, parabolicInd_permGL_mul_cellLeviParabolic σ f ⟨b, hb⟩, ← mul_assoc]
  have hfin : AvgFinite K' (cellFun w σ f m) := avgFinite_cellFun σ f m hK'.2.1
  have hav : avgOver (unipotentCompactG γ E)
      (fun y => cellRepM β γ w σ ⟨b, hb⟩ (cellFun w σ f m ((MulAut.conj b).symm y))) 1 =
      cellRepM β γ w σ ⟨b, hb⟩ (avgOver K' (cellFun w σ f m) 1) := by
    rw [← hKE', avgOver_comp_linearMap (avgFinite_map_mulEquiv (MulAut.conj b) hfin),
      avgOver_map_mulEquiv (MulAut.conj b) hfin, map_one]
  rw [hfun, hav, ← cellCoinvRep_mk, map_smul, smul_smul]
  congr 1
  have hr := cellNorm_div_map_conj (w := w) hb hKE
  have hpos : ((cellNorm F β γ w K' : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (cellNorm_pos (w := w) (β := β) hK').ne'
  change cellNorm F β γ w (unipotentCompactG γ E) / cellNorm F β γ w K' = _ at hr
  rw [← hr]
  push_cast
  field_simp
omit hYo hCY in

def cellJacquetFun (f : parabolicIndSpace F n β σ) :
    levi F n γ → Representation.Coinvariants (cellRepA β γ w σ) :=
  fun m => cellJacquet γ w σ f m
theorem cellJacquetFun_mem {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) :
    cellJacquetFun (γ := γ) (w := w) σ f ∈ indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ) := by
  refine (mem_indSpace).2 ⟨fun b m => ?_, ?_⟩
  · exact cellJacquet_mul_left σ hYo hCY hf b.2 m.2
  · obtain ⟨U, hU, hUf⟩ := exists_cellJacquet_mul_right (γ := γ) (w := w) σ f
    refine ⟨U.subgroupOf (levi F n γ), ?_, fun k hk m => hUf k hk m⟩
    rw [Subgroup.coe_subgroupOf]
    exact hU.preimage continuous_subtype_val
variable (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)
variable (γ w) in

def cellJacquetMap : supportedIn σ Y →ₗ[ℂ] indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ) where
  toFun f := ⟨cellJacquetFun σ f, cellJacquetFun_mem σ hYo hCY f.2⟩
  map_add' f g := Subtype.ext (funext fun m => cellJacquet_add σ hYo hCY f.2 g.2 m.2)
  map_smul' c f := Subtype.ext (funext fun m => cellJacquet_smul σ hYo hCY c f.2 m.2)
end JacquetMap
end Parabolic
end GroundTheory.Automorphic


