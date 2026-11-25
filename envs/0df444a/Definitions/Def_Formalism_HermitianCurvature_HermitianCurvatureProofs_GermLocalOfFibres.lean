-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfFibres
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfFibres
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:56.132247+00:00
-- url     : https://prove2.me/theorems/37eaa897-7770-5cc0-8cb6-c68f7ec9c02a
-- title:
--   Germ Local Of Fibres
-- statement:
--   Definitions and structural lemmas for Germ Local Of Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermLocalOfFibres.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermLocalOfRealised
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermRealisation_ae_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_cvec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.GermRealisation
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
def ptX (s : ℕ) (h : C.LPt) (x : ℂ) : C.LPt := h ++ [(s - 1, x⁻¹)]
def utOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (s : ℕ) (V : C.LPt → ℂ → H) (h : C.LPt)
    (x D : ℂ) : H :=
  ((‖x‖ ^ (s - 1) : ℝ) : ℂ) • V (ptX s h x) (x ^ (s - 1) * D)
theorem cvec_utOf {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (s : ℕ) (V : C.LPt → ℂ → H)
    (h : C.LPt) (x : ℂ) (hx : x ≠ 0) : cvec s (utOf s V h) x = V (ptX s h x) := by
  funext c
  have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
  have hr : ‖x‖ ^ (s - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  simp only [cvec, utOf, smul_smul]
  rw [mul_div_assoc', mul_div_cancel_left₀ c ha, ← Complex.ofReal_mul, inv_mul_cancel₀ hr,
    Complex.ofReal_one, one_smul]
theorem ptSize_ptX (s : ℕ) (h : C.LPt) (x : ℂ) : D.ptSize (ptX s h x) = D.ptSize h + (s - 1) := by
  simp [D.ptSize, ptX]
theorem rd_pos (E : Type) [Field E] [NumberField E] : 0 < S6.rd E := by
  unfold S6.rd
  apply Real.rpow_pos_of_pos
  exact Int.cast_pos.mpr (abs_pos.mpr (NumberField.discr_ne_zero E))
section loc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
theorem dlB_ne_zero (S : C.HidaSetting E Wp Wq) (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (b s : ℕ) :
    KB.dlB S b s ≠ 0 := by
  have hrd := rd_pos E
  have hg0 : 0 < S.g := Nat.mul_pos hg1 hg2
  have hg : (0 : ℝ) < (S.g : ℝ) := by exact_mod_cast hg0
  unfold KB.dlB D.deG
  apply div_ne_zero (zpow_ne_zero _ hrd.ne')
  apply div_ne_zero two_ne_zero
  exact mul_ne_zero hrd.ne' (pow_ne_zero _ hg.ne')
structure FibreGerm (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (ε : ℝ) (b s : ℕ) (a : List C.Letter) (Y : Finset C.LPt) where
  H : Type
  [nag : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  V : C.LPt → ℂ → H
  bt : C.LPt → ℂ → H
  β : ℂ
  ε' : ℂ
  hβ : β ≠ 0
  hε' : ‖ε'‖ = 1
  hpsi : ∀ σ z : ℂ, G.psi β (σ * z) = KB.psiL S σ z
  measV : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → AEStronglyMeasurable (V (ptX s h x)) volume
  fibre : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 → ∀ c : ℂ, c ≠ 0 →
    KB.gN S v ε (b + s - 1) a (ptX s h x ++ [(1, c)]) (ptX s h' x' ++ [(1, c)]) =
      (KB.dlB S (b + s - 1) 1 : ℂ) * ⟪V (ptX s h x) c, V (ptX s h' x') c⟫_ℂ
  meas : ∀ h ∈ Y, StronglyMeasurable (bt h)
  loc : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s (bt h) z‖ ^ 2) K
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D, D ∈ K → ‖utOf s V h x D - mainD s β ε' (bt h) x D‖ ≤ C * ‖x‖⁻¹
  dens : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ z : ℂ, z ≠ 0 →
    gDens S v ε b s a h h' z = (KB.dlB S b s : ℂ) * ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ
attribute [instance] FibreGerm.nag FibreGerm.ips FibreGerm.cs
def GermFibres (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 2 → ∀ a, D.AdmAt S v a → ∀ Y : Finset C.LPt,
    (∀ h ∈ Y, D.ptSize h = b - 1) → Nonempty (FibreGerm S v ε b s a Y)
theorem integrable_of_decay {φ : ℂ → ℂ} (hφ : Continuous φ) {Cφ : ℝ}
    (h : ∀ c : ℂ, ‖φ c‖ ≤ Cφ * ((1 + ‖c‖) ^ 3)⁻¹) : Integrable φ := by
  have hg : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) := by
    apply integrable_one_add_norm
    rw [Complex.finrank_real_complex]
    norm_num
  have e : ∀ c : ℂ, (1 + ‖c‖) ^ (-(3 : ℝ)) = ((1 + ‖c‖) ^ 3)⁻¹ := fun c => by
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  refine (hg.const_mul Cφ).mono' hφ.aestronglyMeasurable (ae_of_all _ fun c => ?_)
  rw [e]
  exact h c
def FibreGerm.toGermReal {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {ε : ℝ} {b s : ℕ} {a : List C.Letter}
    {Y : Finset C.LPt} (R : FibreGerm S v ε b s a Y) (hI : JC.ThmPIntPlace S v fun i => KB.dlB S i 1)
    (hg1 : 0 < S.G.g1) (hg2 : 0 < S.G.g2) (hε : 0 < ε) (hb : 1 ≤ b) (hs : 2 ≤ s) (hbs : b + s ≤ S.G.r + 2)
    (ha : D.AdmAt S v a) (hY : ∀ h ∈ Y, D.ptSize h = b - 1) : GermReal S v ε b s a Y := by
  classical

  have key : ∀ h ∈ Y, ∀ h' ∈ Y, ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      Integrable (fun c => ⟪R.V (ptX s h x) c, R.V (ptX s h' x') c⟫_ℂ) ∧
      gK S v ε b s a (h, x) (h', x') = ∫ c, ⟪R.V (ptX s h x) c, R.V (ptX s h' x') c⟫_ℂ := by
    intro h hh h' hh' x x' hx hx'
    obtain ⟨w, hw⟩ := ha
    have hsz : D.ptSize (ptX s h x) = b + s - 1 - 1 := by rw [ptSize_ptX, hY h hh]; omega
    have hsz' : D.ptSize (ptX s h' x') = b + s - 1 - 1 := by rw [ptSize_ptX, hY h' hh']; omega
    obtain ⟨φ, hφc, hφeq, ⟨Cφ, hCφ⟩, hφint⟩ :=
      hI ε hε (b + s - 1) (by omega) (by omega) w (ptX s h x) (ptX s h' x') hsz hsz'
    have hdl : (KB.dlB S (b + s - 1) 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (dlB_ne_zero S hg1 hg2 _ _)
    have hpt : ∀ c : ℂ, c ≠ 0 → ⟪R.V (ptX s h x) c, R.V (ptX s h' x') c⟫_ℂ =
        (KB.dlB S (b + s - 1) 1 : ℂ)⁻¹ * (φ c / (S.sizeAt v a : ℂ)) := by
      intro c hc
      have hf := R.fibre h hh h' hh' x x' hx hx' c hc
      rw [hφeq c hc, hw]
      unfold KB.gN at hf
      rw [hf, ← mul_assoc, inv_mul_cancel₀ hdl, one_mul]
    have hae : (fun c => ⟪R.V (ptX s h x) c, R.V (ptX s h' x') c⟫_ℂ) =ᵐ[volume]
        fun c => (KB.dlB S (b + s - 1) 1 : ℂ)⁻¹ * (φ c / (S.sizeAt v a : ℂ)) := by
      filter_upwards [ae_ne_zero] with c hc using hpt c hc
    have hφI : Integrable φ := integrable_of_decay hφc hCφ
    refine ⟨((hφI.div_const _).const_mul _).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_const_mul, integral_div, hφint, hw]
    have e : b + s - 1 - 1 = b + s - 2 := by omega
    rw [e]
    unfold gK KB.gN
    simp only [ptX]
    rw [mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hdl, one_mul]
  have memV : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (R.V (ptX s h x)) 2 volume := by
    intro h hh x hx
    refine (memLp_two_iff_integrable_sq_norm (R.measV h hh x hx)).2 ?_
    have hi := (key h hh h hh x x hx hx).1
    refine hi.re.congr (Eventually.of_forall fun c => ?_)
    simp only
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  exact
    { H := R.H
      ut := utOf s R.V
      bt := R.bt
      β := R.β
      ε' := R.ε'
      hβ := R.hβ
      hε' := R.hε'
      hdl := dlB_ne_zero S hg1 hg2 b s
      hpsi := R.hpsi
      memU := fun h hh x hx => (memLp_cvec s (utOf s R.V h) x hx).2 (by rw [cvec_utOf s R.V h x hx]; exact memV h hh x hx)
      gram := fun h hh h' hh' x x' hx hx' => by
        rw [(key h hh h' hh' x x' hx hx').2]
        simp only [gramL, Uc]
        rw [cvec_utOf s R.V h x hx, cvec_utOf s R.V h' x' hx']
      meas := R.meas
      loc := R.loc
      germ := R.germ
      dens := R.dens }
end loc
def GermLocOfFibres : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq),
    0 < S.G.g1 → 0 < S.G.g2 → KB.IntAll S → (∀ v, GermFibres S v) → (∀ v, GermCont S v) → ∀ v, KB.GermLoc S v
end
end Formalism.FourierDecayAlt.P.GermRealisation


