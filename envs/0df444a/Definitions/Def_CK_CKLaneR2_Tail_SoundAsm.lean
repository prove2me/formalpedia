-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_SoundAsm
-- name    : CK_CKLaneR2_Tail_SoundAsm
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:58:22.984086+00:00
-- url     : https://prove2.me/theorems/6a755913-3e66-439a-a034-2637136ab3ca
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.SoundAsm` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.SoundAsm` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.SoundAsm` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.SoundAsm (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/SoundAsm.lean)

import Definitions.Def_CK_CKLaneR2_Tail_SoundT5S

-- ===== source module CKLaneR2.Tail.SoundAsm =====
section

/-!
# Lane R2 — tail checker soundness, part 8: assembly (`cellG` containment and the cell theorem)
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell GeneralCK

/-! ## Factored contact block -/

theorem C_raysecF_raw {Z iE ds de dde : TM} {zf ief dsf dfn ddfn : ℝ → ℝ → ℝ → ℝ} (V : Poly) (rho : ℕ)
    (hZ : Contains one Z zf) (hiE : Contains one iE ief) (hds : Contains one ds dsf)
    (hde : Contains one de dfn) (hdde : Contains one dde ddfn)
    (hz0 : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ zf x y z) :
    Contains one (raysecF Z iE ds de dde (contactFuncs Z (checkImplicit true Z V rho)))
      (fun x y z => rawRS (zf x y z) (ief x y z) (dsf x y z) (dfn x y z) (ddfn x y z)) := by
  obtain ⟨hD, hlp, hlm⟩ := checkImplicit_contact hZ hz0 V rho
  obtain ⟨hF0, hF1, hF2⟩ := C_contactFuncs hZ hD hlp hlm
  have ha := Contains.sub hds (C_mul hZ hde)
  have h := Contains.add (C_mul (C_mul (C_mul ha ha) hiE) hF2) (C_mul hdde (Contains.sub hF0 (C_mul hZ hF1)))
  refine Contains.congr h (fun x y z _ _ _ => ?_)
  unfold rawRS; ring

/-! ## Front semantics -/

structure FSem where
  b : ℝ → ℝ → ℝ → ℝ
  t : ℝ → ℝ → ℝ → ℝ
  u : ℝ → ℝ → ℝ → ℝ
  lam : ℝ → ℝ → ℝ → ℝ
  w : ℝ → ℝ → ℝ → ℝ
  cq : ℝ → ℝ → ℝ → ℝ
  gg : ℝ → ℝ → ℝ → ℝ

structure FOK (F : Front) (S : FSem) : Prop where
  hB : Contains one F.B S.b
  hT : Contains one F.T S.t
  hlogB : Contains one F.logB (fun x y z => Real.log (S.b x y z))
  hU : Contains one F.U S.u
  hLam : Contains one F.Lam S.lam
  hW : Contains one F.W S.w
  homU : Contains one F.omU (fun x y z => 1 - S.u x y z)
  hCq : Contains one F.Cq S.cq
  hG1 : Contains one F.G1 S.gg
  b_pos : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 < S.b x y z
  b_le : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → S.b x y z ≤ 1 / 2
  t_nn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ S.t x y z
  t_le : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → S.t x y z ≤ 1
  u_nn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ S.u x y z
  w_nn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ S.w x y z
  cq_nn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → 0 ≤ S.cq x y z
  hu_le : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
    (S.w x y z + (1 - S.u x y z) * S.cq x y z) * (1 / Real.log 2) ≤ 1

/-- Physical points: the noise/front quantities are the true functions of `u`. -/
def Phys (S : FSem) (x y z : ℝ) : Prop :=
  0 < S.u x y z ∧ S.lam x y z = (-Real.log (S.u x y z))⁻¹ ∧ S.w x y z = S.u x y z * (-Real.log (S.u x y z)) ∧
    S.cq x y z = -Real.log (1 - S.u x y z) ∧ S.gg x y z = g1 (S.u x y z)

/-! ## Mode S containment -/

theorem t5S_contains (F : Front) {s3 Dd : TM} {s3f bf tf uf lamf ggf cqf : ℝ → ℝ → ℝ → ℝ}
    (hs3 : Contains one s3 s3f) (hDd : Contains one Dd (fun x y z => bf x y z - uf x y z))
    (hT : Contains one F.T tf) (hU : Contains one F.U uf)
    (hLam : Contains one F.Lam lamf) (hG1 : Contains one F.G1 ggf) (hCq : Contains one F.Cq cqf)
    (homU : Contains one F.omU (fun x y z => 1 - uf x y z)) :
    Contains one (t5S F s3 Dd)
      (fun x y z => rawT5S (tf x y z) (uf x y z) (bf x y z) (s3f x y z) (lamf x y z) (cqf x y z) (ggf x y z)) := by
  have homega := C_mul (C_oneSub (C_mul hLam hCq)) (C_recip (C_addOne (C_mul hLam hG1)))
  have hTU := C_mul hT hU
  have ha := Contains.scaleInt (C_mul (C_mul hTU hU) (C_recip hDd)) 2
  have hb := Contains.scaleInt (C_mul hTU homega) 4
  have hc := C_mul hs3 (C_mul homega homega)
  have hUB1 := Contains.scaleInt (C_mul (Contains.add (Contains.add ha hb) hc) invLc_contains) 4
  have hUB2 := C_mul (Contains.scaleInt (C_mul hs3 hLam) 2) (C_mul invLc_contains (C_recip homU))
  have hres := Contains.neg (C_half (Contains.add hUB1 hUB2))
  exact Contains.congr hres (fun x y z _ _ _ => rfl)

/-! ## The raw value of a cell -/

open Classical in
/-- The `ρ` function used in mode R: the true ratio at physical points with `s3 > 0`, else the certificate centre. -/
noncomputable def rhoF (S : FSem) (Pc : Poly) (x y z : ℝ) : ℝ :=
  if Phys S x y z ∧ 0 < ((-2 : ℤ) : ℝ) * S.b x y z + 1 + ((2 : ℤ) : ℝ) * (S.t x y z * (S.b x y z - S.u x y z)) then
    radialContact ((((-2 : ℤ) : ℝ) * S.b x y z + 1 + ((2 : ℤ) : ℝ) * (S.t x y z * (S.b x y z - S.u x y z)))
      / H (S.u x y z)) 1 / S.u x y z
  else evalP 0 Pc x y z / one

noncomputable def rawG (S : FSem) (q : TCert) (sMode : Bool) (x y z : ℝ) : ℝ :=
  let b := S.b x y z
  let t := S.t x y z
  let u := S.u x y z
  let lam := S.lam x y z
  let w := S.w x y z
  let cq := S.cq x y z
  let gg := S.gg x y z
  let Hb := -(b * Real.log b + (1 - b) * Real.log (1 - b)) * (1 / Real.log 2)
  let Hu := (w + (1 - u) * cq) * (1 / Real.log 2)
  let E := (Hu + Hb) / 2
  let iE := E⁻¹
  let d := b - u
  let TD := t * d
  let r12b := ((-2 : ℤ) : ℝ) * b + 1
  let s3 := r12b + ((2 : ℤ) : ℝ) * TD
  let uJ := (w - u * cq) * (1 / Real.log 2)
  let ude := -uJ / 2
  let iomU := (1 - u)⁻¹
  let u2dde := -(u * iomU * (1 / Real.log 2)) / 2
  let uT := u * t
  let a0 := ((3 : ℤ) : ℝ) * (u * iomU)
  let a1 := (b + 1 + ((-3 : ℤ) : ℝ) * u) * (((-2 : ℤ) : ℝ) * u + 1) * (iomU * iomU) / 2
  let u2T0 := (a0 + a1) * (1 / Real.log 2)
  let t1 := rawRS (TD * iE) iE uT ude u2dde
  let t2 := -rawRS (d * iE) iE u ude u2dde
  let t3 := rawRS ((r12b + TD) * iE) iE uT ude u2dde
  let t4 := rawEta E ude u2dde
  let t5 := if sMode then rawT5S t u b s3 lam cq gg else rawT5R t u s3 lam cq gg (rhoF S q.rhoP x y z)
  show ℝ from u2T0 + t1 + t2 + t3 + t4 + t5

theorem cellG_contains (F : Front) (S : FSem) (hF : FOK F S) (q : TCert) (sMode : Bool)
    (hub : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 → S.u x y z < S.b x y z) :
    Contains one (cellG F q sMode) (fun x y z => rawG S q sMode x y z) := by
  have hB := hF.hB; have hT := hF.hT; have hlogB := hF.hlogB; have hU := hF.hU; have hLam := hF.hLam
  have hW := hF.hW; have homU := hF.homU; have hCq := hF.hCq; have hG1 := hF.hG1
  -- base block
  have hlog1mB := C_log (C_oneSub hB)
  have hHb := C_mul (Contains.neg (Contains.add (C_mul hB hlogB) (C_mul (C_oneSub hB) hlog1mB))) invLc_contains
  have hHu := C_mul (Contains.add hW (C_mul homU hCq)) invLc_contains
  have hE := C_half (Contains.add hHu hHb)
  have hiE := C_recip hE
  have hDd := Contains.sub hB hU
  have hTD := C_mul hT hDd
  have hr12b := C_addOne (Contains.scaleInt hB (-2))
  have hs3 := Contains.add hr12b (Contains.scaleInt hTD 2)
  have hZ0 := C_mul hTD hiE
  have hZ1 := C_mul hDd hiE
  have hZ2 := C_mul (Contains.add hr12b hTD) hiE
  have huJ := C_mul (Contains.sub hW (C_mul hU hCq)) invLc_contains
  have hude := C_half (Contains.neg huJ)
  have hiomU := C_recip homU
  have hu2dde := C_half (Contains.neg (C_mul (C_mul hU hiomU) invLc_contains))
  have huT := C_mul hU hT
  have ha0 := Contains.scaleInt (C_mul hU hiomU) 3
  have ha1 := C_half (C_mul (C_mul (Contains.add (C_addOne hB) (Contains.scaleInt hU (-3)))
    (C_addOne (Contains.scaleInt hU (-2)))) (C_mul hiomU hiomU))
  have hu2T0 := C_mul (Contains.add ha0 ha1) invLc_contains
  -- positivity facts for the contact arguments
  have hHbpos : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      0 < -(S.b x y z * Real.log (S.b x y z) + (1 - S.b x y z) * Real.log (1 - S.b x y z)) * (1 / Real.log 2) := by
    intro x y z hx hy hz
    have hb0 := hF.b_pos x y z hx hy hz; have hb1 := hF.b_le x y z hx hy hz
    have := H_pos hb0 (by linarith : S.b x y z < 1)
    rw [H_logs hb0 (by linarith)] at this
    have e : -(S.b x y z * Real.log (S.b x y z) + (1 - S.b x y z) * Real.log (1 - S.b x y z)) * (1 / Real.log 2)
        = (S.b x y z * -Real.log (S.b x y z) + (1 - S.b x y z) * -Real.log (1 - S.b x y z)) / Real.log 2 := by ring
    rw [e]; exact this
  have hHunn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      0 ≤ (S.w x y z + (1 - S.u x y z) * S.cq x y z) * (1 / Real.log 2) := by
    intro x y z hx hy hz
    have := hF.w_nn x y z hx hy hz; have := hF.cq_nn x y z hx hy hz
    have hu1 : S.u x y z < 1 := by linarith [hub x y z hx hy hz, hF.b_le x y z hx hy hz]
    have hL := log2_pos
    have : 0 ≤ 1 - S.u x y z := by linarith
    positivity
  have hEpos : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      0 < ((S.w x y z + (1 - S.u x y z) * S.cq x y z) * (1 / Real.log 2)
        + -(S.b x y z * Real.log (S.b x y z) + (1 - S.b x y z) * Real.log (1 - S.b x y z)) * (1 / Real.log 2)) / 2 :=
    fun x y z hx hy hz => by have := hHbpos x y z hx hy hz; have := hHunn x y z hx hy hz; linarith
  have hiEnn : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      0 ≤ (((S.w x y z + (1 - S.u x y z) * S.cq x y z) * (1 / Real.log 2)
        + -(S.b x y z * Real.log (S.b x y z) + (1 - S.b x y z) * Real.log (1 - S.b x y z)) * (1 / Real.log 2)) / 2)⁻¹ :=
    fun x y z hx hy hz => (inv_pos.mpr (hEpos x y z hx hy hz)).le
  have ht1 := C_raysecF_raw q.V0 q.r0 hZ0 hiE huT hude hu2dde (fun x y z hx hy hz =>
    mul_nonneg (mul_nonneg (hF.t_nn x y z hx hy hz) (by linarith [hub x y z hx hy hz])) (hiEnn x y z hx hy hz))
  have ht2 := Contains.neg (C_raysecF_raw q.V1 q.r1 hZ1 hiE hU hude hu2dde (fun x y z hx hy hz =>
    mul_nonneg (by linarith [hub x y z hx hy hz]) (hiEnn x y z hx hy hz)))
  have ht3 := C_raysecF_raw q.V2 q.r2 hZ2 hiE huT hude hu2dde (fun x y z hx hy hz => by
    have h1 := hF.b_le x y z hx hy hz
    have h2 : 0 ≤ S.t x y z * (S.b x y z - S.u x y z) :=
      mul_nonneg (hF.t_nn x y z hx hy hz) (by linarith [hub x y z hx hy hz])
    apply mul_nonneg _ (hiEnn x y z hx hy hz)
    push_cast; linarith)
  have ht4 := C_etaBlock_raw q.Vm q.rm hE hude hu2dde (fun x y z hx hy hz => by
    refine ⟨hEpos x y z hx hy hz, ?_⟩
    have hb0 := hF.b_pos x y z hx hy hz; have hb1 := hF.b_le x y z hx hy hz
    have hHb1 := H_le_one (S.b x y z)
    rw [H_logs hb0 (by linarith)] at hHb1
    have e : -(S.b x y z * Real.log (S.b x y z) + (1 - S.b x y z) * Real.log (1 - S.b x y z)) * (1 / Real.log 2)
        = (S.b x y z * -Real.log (S.b x y z) + (1 - S.b x y z) * -Real.log (1 - S.b x y z)) / Real.log 2 := by ring
    have := hF.hu_le x y z hx hy hz
    rw [e]; linarith)
  have ht5 : Contains one (if sMode then t5S F (base F).s3 (base F).Dd else t5R F (base F).s3 q.rhoP q.rhoR)
      (fun x y z => if sMode then rawT5S (S.t x y z) (S.u x y z) (S.b x y z)
          ((((-2 : ℤ) : ℝ) * S.b x y z + 1) + ((2 : ℤ) : ℝ) * (S.t x y z * (S.b x y z - S.u x y z)))
          (S.lam x y z) (S.cq x y z) (S.gg x y z)
        else rawT5R (S.t x y z) (S.u x y z)
          ((((-2 : ℤ) : ℝ) * S.b x y z + 1) + ((2 : ℤ) : ℝ) * (S.t x y z * (S.b x y z - S.u x y z)))
          (S.lam x y z) (S.cq x y z) (S.gg x y z) (rhoF S q.rhoP x y z)) := by
    cases sMode with
    | true => exact t5S_contains F hs3 hDd hT hU hLam hG1 hCq homU
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine t5R_contains F q.rhoP q.rhoR hs3 hT hU hLam hG1 hCq homU hF.u_nn ?_
      intro x y z hx hy hz hm0 hup hRm hRp
      have hmp : evalP 0 q.rhoP x y z / one + ((-(q.rhoR : Int) : Int) : ℝ) / one
          ≤ evalP 0 q.rhoP x y z / one + (((q.rhoR : Int) : Int) : ℝ) / one := by
        have : ((-(q.rhoR : Int) : Int) : ℝ) / one ≤ (((q.rhoR : Int) : Int) : ℝ) / one := by
          apply div_le_div_of_nonneg_right _ CKLaneR2.Cell.hone'.le
          push_cast; linarith [(Nat.cast_nonneg q.rhoR : (0 : ℝ) ≤ q.rhoR)]
        linarith
      unfold rhoF
      split_ifs with hc
      · obtain ⟨⟨hu0, hlam, _, _, hgg⟩, hs3pos⟩ := hc
        have hu12 : S.u x y z < 1 / 2 := by linarith [hub x y z hx hy hz, hF.b_le x y z hx hy hz]
        have hlog : 0 < -Real.log (S.u x y z) := by
          have := Real.log_neg hu0 (by linarith : S.u x y z < 1); linarith
        have hlam' : S.lam x y z * (-Real.log (S.u x y z)) = 1 := by rw [hlam]; exact inv_mul_cancel₀ hlog.ne'
        rw [hgg] at hRm hRp
        have hbr := t5_bracket hs3pos hu0 hu12 hlam' hm0 hmp hup hRm hRp
        constructor
        · rw [le_div_iff₀ hu0]; linarith [hbr.1]
        · rw [div_le_iff₀ hu0]; linarith [hbr.2]
      · constructor
        · have : ((-(q.rhoR : Int) : Int) : ℝ) / one ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg _ CKLaneR2.Cell.hone'.le
            push_cast; linarith [(Nat.cast_nonneg q.rhoR : (0 : ℝ) ≤ q.rhoR)]
          linarith
        · have : (0 : ℝ) ≤ (((q.rhoR : Int) : Int) : ℝ) / one := by
            apply div_nonneg _ CKLaneR2.Cell.hone'.le
            push_cast; exact Nat.cast_nonneg _
          linarith
  have hG := Contains.add (Contains.add (Contains.add (Contains.add (Contains.add hu2T0 ht1) ht2) ht3) ht4) ht5
  exact Contains.congr hG (fun x y z _ _ _ => rfl)

end CKLaneR2.Tail

end


