-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNDptPrj
-- name    : IntMul_Kappa_R8_Data_BitOppbankNDptPrj
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T11:08:40.653493+00:00
-- url     : https://prove2.me/theorems/764d935b-50f9-4ae3-a4d2-419fd1ecee43
-- title:
--   ND–PT Le helper pack: IsPrj nesting, orthOK_sound, and Pnd_orth on published Pnd
-- statement:
--   # ND–PT Le helpers, projector-nesting pack
--
--   Bilinear-form projector calculus: $P_{\mathrm{nd}}$ is the projector onto $\mathrm{span}S(\mathrm{sup})$ when the support is centred, $1-P_\ell(T)$ is the projector onto $x_v(T)^\perp$, and $\mathrm{orthOK}$ implies $\mathrm{span}S\subseteq x_v(T)^\perp$. The packing lemma is
--   $$\mathrm{Le}\bigl(P_{\mathrm{nd}}(\mathrm{sup}),\,1-P_\ell(T)\bigr).$$
--   Published Pnd only (no PndFix). Depends on the `NDptBits` and `NDptCard` packs.
-- source:
--   R8 BitOppbank FormalOK published Pnd nest_Le_ND_NDpt helper pack (IsPrj / Pnd_orth).

-- NDpt helper pack (published Pnd only; no PndFix).
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNDptBits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNDptCard
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.NDptBits
open IntMul.Kappa.R8.Bit.Oppbank.NDptCard
namespace IntMul.Kappa.R8.Bit.Oppbank.NDptPrj

/-! ## IsPrj helpers (from the accepted Le_Pnd_of_land sol) -/

theorem mat_ext {P Q : M23} (h : ∀ u, P *ᵥ u = Q *ᵥ u) : P = Q := by
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun u => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h]

theorem decomp {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V)) (u : V23) :
    ∃ a ∈ V, ∃ b ∈ Bf.orthogonal V, u = a + b := by
  have : u ∈ V ⊔ Bf.orthogonal V := by rw [h.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 this
  exact ⟨a, ha, b, hb, e.symm⟩

theorem IsPrj.eq {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V))
    {P Q : M23} (hP : IsPrj P V) (hQ : IsPrj Q V) : P = Q := by
  apply mat_ext
  intro u
  obtain ⟨a, ha, b, hb, rfl⟩ := decomp h u
  rw [mulVec_add, mulVec_add, hP.1 a ha, hQ.1 a ha, hP.2 b hb, hQ.2 b hb]

theorem IsPrj.mem {V : Submodule ℚ V23} (h : IsCompl V (Bf.orthogonal V))
    {P : M23} (hP : IsPrj P V) (u : V23) :
    P *ᵥ u ∈ V ∧ u - P *ᵥ u ∈ Bf.orthogonal V := by
  obtain ⟨a, ha, b, hb, rfl⟩ := decomp h u
  rw [mulVec_add, hP.1 a ha, hP.2 b hb, add_zero, add_sub_cancel_left]
  exact ⟨ha, hb⟩

theorem IsPrj.nested {V V' : Submodule ℚ V23} (hVV : V ≤ V')
    (h : IsCompl V (Bf.orthogonal V)) (h' : IsCompl V' (Bf.orthogonal V'))
    {P P' : M23} (hP : IsPrj P V) (hP' : IsPrj P' V') :
    P' * P = P ∧ P * P' = P := by
  have horth : Bf.orthogonal V' ≤ Bf.orthogonal V := LinearMap.BilinForm.orthogonal_le hVV
  constructor
  · exact IsPrj.eq h ⟨fun v hv => by rw [← mulVec_mulVec, hP.1 v hv, hP'.1 v (hVV hv)],
      fun w hw => by rw [← mulVec_mulVec, hP.2 w hw, mulVec_zero]⟩ hP
  · refine IsPrj.eq h ⟨fun v hv => by rw [← mulVec_mulVec, hP'.1 v (hVV hv), hP.1 v hv],
      fun w hw => ?_⟩ hP
    rw [← mulVec_mulVec]
    have hm := (IsPrj.mem h' hP' w).2
    have : P' *ᵥ w = w - (w - P' *ᵥ w) := by abel
    rw [this, mulVec_sub, hP.2 w hw, hP.2 _ (horth hm), sub_zero]

theorem prjM_spec (V : Submodule ℚ V23) (h : IsCompl V (Bf.orthogonal V)) :
    IsPrj (prjM V h) V := by
  refine ⟨fun v hv => ?_, fun w hw => ?_⟩
  · rw [prjM, LinearMap.toMatrix'_mulVec, Submodule.projection_apply_of_mem_left h hv]
  · rw [prjM, LinearMap.toMatrix'_mulVec, Submodule.projection_apply_of_mem_right h hw]

theorem Pnd_prj {sup : ℕ} (h : HasCentre sup) : IsPrj (Pnd sup) (spanS sup) := by
  rw [Pnd_eq_prj h]; exact prjM_spec _ _

/-! ## Pl is the Bf-projector onto span {xv T}; 1-Pl onto the orthogonal -/

theorem Pl_mulVec (T : ℕ) (w : V23) :
    Pl T *ᵥ w = (yv T ⬝ᵥ w) • xv T := by
  simpa [Pl] using (vecMulVec_mulVec (xv T) (yv T) w)


theorem bfF_add (u v w : V23) : bfF (u + v) w = bfF u w + bfF v w := by
  have hdot : (u + v) ⬝ᵥ w = u ⬝ᵥ w + v ⬝ᵥ w := by
    simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsum : ∑ p, (u + v) p = ∑ p, u p + ∑ p, v p := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  simp only [bfF, hdot, hsum]
  ring

theorem bfF_smul (r : ℚ) (u v : V23) : bfF (r • u) v = r * bfF u v := by
  simp only [bfF, dotProduct, Pi.smul_apply, smul_eq_mul]
  have hdot : ∑ i, (r * u i) * v i = r * ∑ i, u i * v i := by
    have : ∑ i, (r * u i) * v i = ∑ i, r * (u i * v i) :=
      Finset.sum_congr rfl fun i _ => (mul_assoc r (u i) (v i))
    rw [this, Finset.mul_sum]
  have hsum : ∑ i, r * u i = r * ∑ i, u i := (Finset.mul_sum Finset.univ (fun i => u i) r).symm
  rw [hdot, hsum]
  ring

theorem Bf_nondeg {w : V23} (h : ∀ v, bfF v w = 0) : w = 0 := by
  have hi (i : Fin 23) : w i - (∑ p, w p) / 9 = 0 := by
    have := h (Pi.single i 1)
    have hdot : (Pi.single i (1 : ℚ)) ⬝ᵥ w = w i := by
      simp [dotProduct, Pi.single_apply]
    have hsum : (∑ p, (Pi.single i (1 : ℚ)) p) = 1 := by
      simp [Pi.single_apply, Finset.sum_ite_eq]
    simpa [bfF, hdot, hsum] using this
  have hw (i : Fin 23) : w i = (∑ p, w p) / 9 := by linarith [hi i]
  have hsum : ∑ p, w p = 23 * ((∑ p, w p) / 9) := by
    have : ∑ p, w p = ∑ _p : Fin 23, (∑ q, w q) / 9 :=
      Finset.sum_congr rfl fun p _ => hw p
    simpa [Finset.sum_const, Finset.card_univ] using this
  have hz : (∑ p, w p) = 0 := by
    have := congrArg (fun x => 9 * x) hsum
    ring_nf at this
    linarith
  funext i
  simp [hw i, hz]

theorem orthogonal_top : Bf.orthogonal (⊤ : Submodule ℚ V23) = ⊥ := by
  ext w
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_top, Submodule.mem_bot,
    forall_true_left, Bf_apply]
  constructor
  · intro h; exact Bf_nondeg fun v => h v
  · intro h; subst h; intro v; simp [bfF]

theorem orthogonal_sup (V W : Submodule ℚ V23) :
    Bf.orthogonal (V ⊔ W) = Bf.orthogonal V ⊓ Bf.orthogonal W := by
  ext x
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_inf, Bf_apply]
  constructor
  · intro h
    exact ⟨fun v hv => h v (Submodule.mem_sup_left hv),
      fun w hw => h w (Submodule.mem_sup_right hw)⟩
  · intro ⟨hV, hW⟩ u hu
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 hu
    have hsum : bfF (v + w) x = bfF v x + bfF w x := bfF_add v w x
    rw [hsum, hV v hv, hW w hw, add_zero]

theorem le_ortho_ortho (V : Submodule ℚ V23) :
    V ≤ Bf.orthogonal (Bf.orthogonal V) := by
  intro v hv w hw
  have h := (mem_orth.1 hw) v hv
  -- h : bfF v w = 0, goal typically Bf w v = 0
  simpa [Bf_apply, bfF_comm] using h

theorem ortho_ortho_eq {V : Submodule ℚ V23}
    (h : IsCompl V (Bf.orthogonal V)) : Bf.orthogonal (Bf.orthogonal V) = V := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := decomp h x
    have ha' : a ∈ Bf.orthogonal (Bf.orthogonal V) := le_ortho_ortho V ha
    have hb' : b ∈ Bf.orthogonal (Bf.orthogonal V) := by
      have : (a + b) - a = b := by abel
      exact this ▸ sub_mem hx ha'
    have hbot : Bf.orthogonal V ⊓ Bf.orthogonal (Bf.orthogonal V) = ⊥ := by
      rw [← orthogonal_sup, h.sup_eq_top, orthogonal_top]
    have hb0 : b = 0 := (Submodule.mem_bot ℚ).1 (hbot.le ⟨hb, hb'⟩)
    simpa [hb0] using ha
  · exact le_ortho_ortho V

theorem isCompl_span_xv {T : ℕ} (hT : T < 1771) :
    IsCompl (Submodule.span ℚ {xv T}) (Bf.orthogonal (Submodule.span ℚ {xv T})) := by
  rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint Bf_refl, Submodule.disjoint_def]
  intro x hx hxo
  have hxspan := Submodule.mem_span_singleton.1 hx
  obtain ⟨c, rfl⟩ := hxspan
  have h0 : bfF (xv T) (c • xv T) = 0 :=
    (mem_orth.1 hxo) (xv T) (Submodule.mem_span_singleton_self _)
  have hmul : bfF (xv T) (c • xv T) = c * bfF (xv T) (xv T) := by
    rw [bfF_comm, bfF_smul, mul_comm, bfF_comm]
  have hc : c = 0 := by
    have : c * bfF (xv T) (xv T) = 0 := by rw [← hmul]; exact h0
    rw [xv_ne' hT] at this
    linarith
  simp [hc]

theorem Pl_isPrj {T : ℕ} (hT : T < 1771) :
    IsPrj (Pl T) (Submodule.span ℚ {xv T}) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have : Pl T *ᵥ (c • xv T) = (c * (yv T ⬝ᵥ xv T)) • xv T := by
      rw [Pl_mulVec, dotProduct_smul]
      simp [smul_eq_mul, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    rw [this, yx' hT, mul_one]
  · intro w hw
    have : bfF (xv T) w = 0 := (mem_orth.1 hw) (xv T) (Submodule.mem_span_singleton_self _)
    rw [Pl_mulVec, yv_dot', this, zero_div, zero_smul]

theorem mPl_isPrj {T : ℕ} (hT : T < 1771) :
    IsPrj (1 - Pl T) (Bf.orthogonal (Submodule.span ℚ {xv T})) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    have hPl : Pl T *ᵥ v = 0 := (Pl_isPrj hT).2 v hv
    rw [sub_mulVec, one_mulVec, hPl, sub_zero]
  · intro w hw
    -- w ∈ (span xv)⊥⊥ = span xv
    have hw' : w ∈ Submodule.span ℚ {xv T} := by
      have := ortho_ortho_eq (isCompl_span_xv hT)
      rw [← this]; exact hw
    have hPl : Pl T *ᵥ w = w := (Pl_isPrj hT).1 w hw'
    rw [sub_mulVec, one_mulVec, hPl, sub_self]

theorem isCompl_orth_xv {T : ℕ} (hT : T < 1771) :
    IsCompl (Bf.orthogonal (Submodule.span ℚ {xv T}))
      (Bf.orthogonal (Bf.orthogonal (Submodule.span ℚ {xv T}))) := by
  have h := isCompl_span_xv hT
  rw [ortho_ortho_eq h]
  exact IsCompl.symm h

/-! ## orthOK_sound and Pnd_orth -/

theorem bfF_span_of_gens {sup T : ℕ}
    (hgen : ∀ i, sup.testBit i = true → bfF (tvQ i) (xv T) = 0)
    {v : V23} (hv : v ∈ spanS sup) : bfF v (xv T) = 0 := by
  let K : Submodule ℚ V23 :=
    { carrier := {v | bfF v (xv T) = 0}
      add_mem' := fun {a b} ha hb => by
        change bfF (a + b) (xv T) = 0
        have ha' : bfF a (xv T) = 0 := ha
        have hb' : bfF b (xv T) = 0 := hb
        rw [bfF_add, ha', hb', add_zero]
      zero_mem' := by simp [bfF]
      smul_mem' := fun r a ha => by
        change bfF (r • a) (xv T) = 0
        have ha' : bfF a (xv T) = 0 := ha
        rw [bfF_smul, ha', mul_zero] }
  have hle : spanS sup ≤ K := by
    rw [spanS, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hgen i hi
  exact hle hv

theorem orthOK_sound {n T : ℕ} (hT : T < 1771) (h : orthOK n T = true) :
    ∀ v ∈ spanS (densSupG n), bfF (xv T) v = 0 := by
  intro v hv
  have hland : Nat.land (densSupG n) (Pnd.orthTL T) = densSupG n := by
    simpa [orthOK, Nat.beq_eq] using h
  have hgen : ∀ i, (densSupG n).testBit i = true → bfF (tvQ i) (xv T) = 0 := by
    intro i hi
    have hiT : (Pnd.orthTL T).testBit i = true := by
      have : ((densSupG n) &&& (Pnd.orthTL T)).testBit i = true := by
        change (Nat.land (densSupG n) (Pnd.orthTL T)).testBit i = true
        rwa [hland]
      rw [Nat.testBit_and, Bool.and_eq_true] at this
      exact this.2
    have hi_lt : i < 1771 := by
      -- bits of a centred support are < 1771; use AllDensCentred when n is in range,
      -- but here we only know orthOK. If i ≥ 1771, Pnd.starL never sets that bit, so
      -- Pnd.orthTL cannot have it. Prove: Pnd.orthTL bits are all < 1771.
      by_contra hge
      have : ¬ (Pnd.orthTL T).testBit i = true := by
        intro ht
        have hmem := (mem_orthTL T i).mp ht
        have notstar (c : ℕ) : ¬ (Pnd.starL c).testBit i = true := by
          intro hs
          exact (not_lt.mpr (Nat.le_of_not_gt hge)) ((mem_starL c i).mp hs).1
        rcases hmem with ⟨hs, _, _⟩ | ⟨hs, _, _⟩ | ⟨hs, _, _⟩
        · exact notstar _ hs
        · exact notstar _ hs
        · exact notstar _ hs
      exact this hiT
    exact bfF_of_orthTL hT hi_lt hiT
  have := bfF_span_of_gens hgen hv
  rw [bfF_comm]; exact this

theorem Pnd_orth {sup T : ℕ} (hC : HasCentre sup) (hT : T < 1771)
    (horth : ∀ v ∈ spanS sup, bfF (xv T) v = 0) :
    Le (Pnd sup) (1 - Pl T) := by
  have hspan : spanS sup ≤ Bf.orthogonal (Submodule.span ℚ {xv T}) := by
    intro v hv
    apply mem_orth.2
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hv' := horth v hv
    have : bfF (c • xv T) v = c * bfF (xv T) v := by
      rw [bfF_smul]
    rw [this, hv', mul_zero]
  exact IsPrj.nested hspan (compl_spanS hC) (isCompl_orth_xv hT)
    (Pnd_prj hC) (mPl_isPrj hT)

end IntMul.Kappa.R8.Bit.Oppbank.NDptPrj


