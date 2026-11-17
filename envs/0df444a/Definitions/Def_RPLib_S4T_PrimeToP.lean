-- Prove2me | Definitions.Def_RPLib_S4T_PrimeToP
-- name    : RPLib_S4T_PrimeToP
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:23:05.55807+00:00
-- url     : https://prove2.me/theorems/f7663a99-a4f3-468b-87b1-df7d03e67bfe
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: `RPLib.S4T.Glue.L5Stmt` (route L4 + L5)
-- statement:
--   `RPLib.S4T.Glue.L5Stmt` (route L4 + L5).
--
--   * `phase1`: divide `β` by `p` while it kills `X₁[p]`; otherwise `ker β` meets one of the lines `L(α₁)`,
--     `L(ᾱ₁)` trivially and `phase2` (part B) applies to `α₁` or to `ᾱ₁`.
--   * `finish`: a rational `u₀ ≠ 0` injective on `X₁[p]` has `w₀` with `w₀ ∘ u₀ = N = u₀ ∘ w₀`, `p ∤ N`
--     (dual pair `σ₀` of `u₀`, `σ₀ = p^b w₀` by 6256914e).
--   * `l5 : Glue.L5Stmt`.
--   FLT statements are explicit hypotheses (never used as lemmas).
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_PrimeToPB

/-!
# S4T-PrimeToP: `RPLib.S4T.Glue.L5Stmt` (route L4 + L5)

* `phase1`: divide `β` by `p` while it kills `X₁[p]`; otherwise `ker β` meets one of the lines `L(α₁)`,
  `L(ᾱ₁)` trivially and `phase2` (part B) applies to `α₁` or to `ᾱ₁`.
* `finish`: a rational `u₀ ≠ 0` injective on `X₁[p]` has `w₀` with `w₀ ∘ u₀ = N = u₀ ∘ w₀`, `p ∤ N`
  (dual pair `σ₀` of `u₀`, `σ₀ = p^b w₀` by 6256914e).
* `l5 : Glue.L5Stmt`.
FLT statements are explicit hypotheses (never used as lemmas).
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RPLib.S4T.PrimeToP

open WeierstrassCurve WeierstrassCurve.Affine

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [DecidableEq Ω]

/-- **Phase 1.** -/
theorem phase1 (h625 : FLT.S_6256914e.{0, 0}) (ha78 : FLT.S_a78cfa46.{0, 0}) (hfe3 : FLT.S_fe3c6240.{0, 0})
    (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0}) {p : ℕ} [Fact p.Prime]
    {X₁ X₂ : WeierstrassCurve Ω} [X₁.IsElliptic] [X₂.IsElliptic] {t q c m : ℤ}
    (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n) (ht : ¬ (p : ℤ) ∣ t)
    (hcm : (p : ℤ) * m = q + p * c * t + p ^ 2 * c ^ 2) (hm : IsCoprime m (p : ℤ))
    {α₁ : X₁.toAffine.Point →+ X₁.toAffine.Point} (hα₁ : α₁ ∈ rationalHomSet Ω X₁ X₁)
    (h₁ : α₁.comp α₁ + q • AddMonoidHom.id X₁.toAffine.Point = t • α₁)
    (hcard₁ : Nat.card (Lsub X₁ p α₁) = p) (hcard₂ : Nat.card (Lsub X₁ p (bar X₁ t α₁)) = p)
    (hα0₁ : ∃ Y : X₁.toAffine.Point, Y ≠ 0 ∧ Y ∈ Lsub X₁ p α₁)
    (hα0₂ : ∃ Y : X₁.toAffine.Point, Y ≠ 0 ∧ Y ∈ Lsub X₁ p (bar X₁ t α₁))
    {α₂' : X₂.toAffine.Point →+ X₂.toAffine.Point} (hα₂' : α₂' ∈ rationalHomSet Ω X₂ X₂) (e : ℕ) :
    ∀ β : X₁.toAffine.Point →+ X₂.toAffine.Point, β ∈ rationalHomSet Ω X₁ X₂ → β ≠ 0 →
      (∀ P, β (α₁ P) = α₂' (β P)) →
      (∀ (P : X₁.toAffine.Point) (k : ℕ), p ^ k • P = 0 → β P = 0 → p ^ e • P = 0) →
      ∃ u : X₁.toAffine.Point →+ X₂.toAffine.Point, u ∈ rationalHomSet Ω X₁ X₂ ∧ u ≠ 0 ∧
        ∀ P, p • P = 0 → u P = 0 → P = 0 := by
  have hp : p.Prime := Fact.out
  induction e with
  | zero =>
    intro β hβ hβ0 _ hA3
    refine ⟨β, hβ, hβ0, fun P hP hβP => ?_⟩
    have := hA3 P 1 (by rwa [pow_one]) hβP
    rwa [pow_zero, one_smul] at this
  | succ e ih =>
    intro β hβ hβ0 hint hA3
    by_cases hall : ∀ P : X₁.toAffine.Point, ((p : ℕ) : ℤ) • P = 0 → β P = 0
    · obtain ⟨β₀, hβ₀, hβeq⟩ := h625 Ω X₁ X₂ (Nat.cast_ne_zero.mpr hp.ne_zero : ((p : ℕ) : Ω) ≠ 0) hβ hall
      let β'' : X₁.toAffine.Point →+ X₂.toAffine.Point := β₀
      have hβ'' : β'' ∈ rationalHomSet Ω X₁ X₂ := hβ₀
      have hβP : ∀ P : X₁.toAffine.Point, β P = ((p : ℕ) : ℤ) • β'' P := hβeq
      have hβPn : ∀ P : X₁.toAffine.Point, β P = β'' (p • P) := fun P => by
        rw [hβP, natCast_zsmul, map_nsmul]
      have hβ''0 : β'' ≠ 0 := by
        intro h0
        apply hβ0
        ext P
        show β P = 0
        rw [hβP, h0, AddMonoidHom.zero_apply, smul_zero]
      have hint'' : ∀ P, β'' (α₁ P) = α₂' (β'' P) := by
        have := eq_of_nsmul ha78 h195 h580 X₁ X₂ (hfe3 Ω X₁ X₁ X₂ hα₁ hβ'') (hfe3 Ω X₁ X₂ X₂ hβ'' hα₂') p
          hp.pos (fun P => by
            show p • β'' (α₁ P) = p • α₂' (β'' P)
            rw [← natCast_zsmul (β'' (α₁ P)) p, ← hβP, hint, hβP, map_zsmul, natCast_zsmul])
        exact fun P => DFunLike.congr_fun this P
      have hA3'' : ∀ (P : X₁.toAffine.Point) (k : ℕ), p ^ k • P = 0 → β'' P = 0 → p ^ e • P = 0 := by
        intro P k hk hβ''P
        obtain ⟨P', rfl⟩ := exists_nsmul_eq ha78 h195 X₁ p hp.pos P
        have hk' : p ^ (k + 1) • P' = 0 := by rw [pow_succ, mul_smul, hk]
        have := hA3 P' (k + 1) hk' (by rw [hβPn, hβ''P])
        rw [← mul_smul, ← pow_succ]
        exact this
      exact ih β'' hβ'' hβ''0 hint'' hA3''
    push Not at hall
    obtain ⟨Z₂, hZ₂p, hβZ₂⟩ := hall
    have hZ₂p' : p • Z₂ = 0 := by rwa [natCast_zsmul] at hZ₂p
    obtain ⟨d, u, hdu⟩ := exists_inv p hp ht
    by_cases hA2 : ∀ Y ∈ Lsub X₁ p (bar X₁ t α₁), β Y = 0 → Y = 0
    · exact phase2 h625 ha78 hfe3 h195 h580 hq ht hcm hm hα₁ h₁ hcard₁ hα0₁ hα₂' (e + 1) β hβ hβ0 hint hA2 hA3
    push Not at hA2
    obtain ⟨Y, hY, hβY, hY0⟩ := hA2
    have hkill₂ : ∀ Y' ∈ Lsub X₁ p (bar X₁ t α₁), β Y' = 0 := by
      intro Y' hY'
      obtain ⟨k, rfl⟩ := L_zmultiples hcard₂ hY0 hY hY'
      rw [map_zsmul, hβY, smul_zero]
    have hA2' : ∀ Y' ∈ Lsub X₁ p (bar X₁ t (bar X₁ t α₁)), β Y' = 0 → Y' = 0 := by
      rw [bar_bar]
      intro Y' hY' hβY'
      by_contra hY'0
      have hkill₁ : ∀ Y'' ∈ Lsub X₁ p α₁, β Y'' = 0 := by
        intro Y'' hY''
        obtain ⟨k, rfl⟩ := L_zmultiples hcard₁ hY'0 hY' hY''
        rw [map_zsmul, hβY', smul_zero]
      apply hβZ₂
      rw [split_p (α := α₁) p hdu hZ₂p', map_add, hkill₁ _ (split_mem₀ p h₁ hq d hZ₂p'),
        hkill₂ _ (split_mem₁ p h₁ hq d hZ₂p'), add_zero]
    have hintb : ∀ P, β (bar X₁ t α₁ P) = bar X₂ t α₂' (β P) := by
      intro P
      rw [bar_apply, bar_apply, map_sub, map_zsmul, hint]
    exact phase2 h625 ha78 hfe3 h195 h580 hq ht hcm hm (bar_mem h195 h580 hα₁) (bar_ch h₁) hcard₂ hα0₂
      (bar_mem h195 h580 hα₂') (e + 1) β hβ hβ0 hintb hA2' hA3

/-- **Finish.** -/
theorem finish (h625 : FLT.S_6256914e.{0, 0}) (h0e8 : FLT.S_0e8f5714.{0, 0}) (ha78 : FLT.S_a78cfa46.{0, 0})
    (hfe3 : FLT.S_fe3c6240.{0, 0}) (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0}) {p : ℕ}
    (hp : p.Prime) {X₁ X₂ : WeierstrassCurve Ω} [X₁.IsElliptic] [X₂.IsElliptic]
    {u₀ : X₁.toAffine.Point →+ X₂.toAffine.Point} (hu₀ : u₀ ∈ rationalHomSet Ω X₁ X₂) (hu₀0 : u₀ ≠ 0)
    (hinj : ∀ P, p • P = 0 → u₀ P = 0 → P = 0) :
    ∃ w : X₂.toAffine.Point →+ X₁.toAffine.Point, w ∈ rationalHomSet Ω X₂ X₁ ∧
      ∃ N : ℕ, ¬ p ∣ N ∧ w.comp u₀ = (N : ℤ) • AddMonoidHom.id X₁.toAffine.Point ∧
        u₀.comp w = (N : ℤ) • AddMonoidHom.id X₂.toAffine.Point := by
  obtain ⟨σ₀', hσ₀', n, hn, hdual⟩ := h0e8 Ω X₁ X₂ hu₀ hu₀0
  let σ₀ : X₂.toAffine.Point →+ X₁.toAffine.Point := σ₀'
  have hσ₀ : σ₀ ∈ rationalHomSet Ω X₂ X₁ := hσ₀'
  have hL : ∀ P : X₁.toAffine.Point, σ₀ (u₀ P) = n • P := hdual.comp_left
  have hR : ∀ Q : X₂.toAffine.Point, u₀ (σ₀ Q) = n • Q := hdual.comp_right
  obtain ⟨n', hn'⟩ : ∃ n' : ℕ, (n' : ℤ) = n := ⟨n.toNat, Int.toNat_of_nonneg hn.le⟩
  have hn'pos : 0 < n' := by omega
  obtain ⟨b, N, hNb, hNp⟩ : ∃ b N : ℕ, p ^ b * N = n' ∧ ¬ p ∣ N :=
    ⟨_, _, Nat.ordProj_mul_ordCompl_eq_self n' p, Nat.not_dvd_ordCompl hp hn'pos.ne'⟩
  have hsurj : ∀ Q : X₂.toAffine.Point, ∃ P : X₁.toAffine.Point, u₀ P = Q := ha78 Ω hu₀ hu₀0
  have hσker : ∀ Q : X₂.toAffine.Point, ((p ^ b : ℕ) : ℤ) • Q = 0 → σ₀ Q = 0 := by
    intro Q hQ
    rw [natCast_zsmul] at hQ
    obtain ⟨P, hP⟩ := hsurj Q
    have hP' : u₀ P = Q := hP
    rw [← hP'] at hQ ⊢
    have hR0 : u₀ (p ^ b • P) = 0 := by rw [map_nsmul, hQ]
    have hnR : n' • (p ^ b • P) = 0 := by
      rw [← natCast_zsmul (p ^ b • P) n', hn', ← hL, hR0, map_zero]
    have hS : N • (p ^ b • P) = 0 := by
      by_contra hS0
      obtain ⟨j, hj0, hj⟩ := exists_ptors p hS0 b (by rw [← mul_smul (p ^ b) N (p ^ b • P), hNb, hnR])
      exact hj0 (hinj _ hj (by simp only [map_nsmul, hQ, smul_zero]))
    rw [hL, ← hn', natCast_zsmul, ← hNb, mul_comm, mul_smul]
    exact hS
  have hpb : ((p ^ b : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  obtain ⟨w₀, hw₀, hweq⟩ := h625 Ω X₂ X₁ hpb hσ₀ hσker
  let w : X₂.toAffine.Point →+ X₁.toAffine.Point := w₀
  have hw : w ∈ rationalHomSet Ω X₂ X₁ := hw₀
  have hwP : ∀ Q : X₂.toAffine.Point, σ₀ Q = ((p ^ b : ℕ) : ℤ) • w Q := hweq
  have hpbpos : 0 < p ^ b := pow_pos hp.pos b
  refine ⟨w, hw, N, hNp, ?_, ?_⟩
  · apply eq_of_nsmul ha78 h195 h580 X₁ X₁ (hfe3 Ω X₁ X₂ X₁ hu₀ hw)
      (CMGlue.zsmul_mem h195 h580 X₁ X₁ (id_mem_rationalHomSet Ω X₁) _) (p ^ b) hpbpos
    intro P
    show p ^ b • w (u₀ P) = p ^ b • ((N : ℤ) • P)
    rw [← natCast_zsmul (w (u₀ P)) (p ^ b), ← hwP, hL, ← hn', natCast_zsmul P n', natCast_zsmul P N, ← hNb,
      mul_smul]
  · apply eq_of_nsmul ha78 h195 h580 X₂ X₂ (hfe3 Ω X₂ X₁ X₂ hw hu₀)
      (CMGlue.zsmul_mem h195 h580 X₂ X₂ (id_mem_rationalHomSet Ω X₂) _) (p ^ b) hpbpos
    intro Q
    show p ^ b • u₀ (w Q) = p ^ b • ((N : ℤ) • Q)
    rw [← map_nsmul u₀ (p ^ b) (w Q), ← natCast_zsmul (w Q) (p ^ b), ← hwP, hR, ← hn', natCast_zsmul Q n',
      natCast_zsmul Q N, ← hNb, mul_smul]

/-- **L4 + L5.** -/
theorem l5 (h625 : FLT.S_6256914e.{0, 0}) (h0e8 : FLT.S_0e8f5714.{0, 0}) (ha78 : FLT.S_a78cfa46.{0, 0})
    (h976 : FLT.S_97650530.{0, 0}) (hfe3 : FLT.S_fe3c6240.{0, 0}) (h195 : FLT.S_195173b3.{0, 0})
    (h580 : FLT.S_580839d4.{0, 0}) : Glue.L5Stmt := by
  intro p _ _ X₁ X₂ _ _ t q hirr hq ht α₁ α₂ hα₁ hα₂ h₁ h₂ hinf₁ β hβ hβ0
  have hp : p.Prime := Fact.out
  obtain ⟨β', hβ', hβ'0, α₂', hα₂', hint⟩ := intertwine h195 h580 hfe3 hα₁ hα₂ h₁ h₂ hβ hβ0
  obtain ⟨σ', -, n, hn, hdual⟩ := h0e8 (AlgebraicClosure ℚ) X₁ X₂ hβ' hβ'0
  obtain ⟨n', hn'⟩ : ∃ n' : ℕ, (n' : ℤ) = n := ⟨n.toNat, Int.toNat_of_nonneg hn.le⟩
  have hA3 : ∀ (P : X₁.toAffine.Point) (k : ℕ), p ^ k • P = 0 → β' P = 0 → p ^ n' • P = 0 := by
    intro P k hk hP
    have h1 : n • P = 0 := hdual.ker_le_torsion_right hP
    exact pow_nsmul_eq_zero_of hp (by omega) (by rw [← natCast_zsmul, hn']; exact h1) hk
  have hb₁ : bar X₁ t α₁ ∈ rationalHomSet (AlgebraicClosure ℚ) X₁ X₁ := bar_mem h195 h580 hα₁
  have hα0₁ := exists_L_ne_zero h625 h976 hfe3 h195 h580 ha78 hp hq hα₁ h₁ (fun m hm => (hinf₁ m hm).1)
  have hα0₂ := exists_L_ne_zero h625 h976 hfe3 h195 h580 ha78 hp hq hb₁ (bar_ch h₁) (fun m hm => (hinf₁ m hm).2)
  have hcard₁ := card_L hp hq ht h₁ hα0₁ hα0₂
  have hcard₂ := card_L hp hq ht (bar_ch h₁) hα0₂ (by rw [bar_bar]; exact hα0₁)
  obtain ⟨c, m, hcm, hm⟩ := exists_cm hp hq ht
  obtain ⟨u₀, hu₀, hu₀0, hinj⟩ :=
    phase1 h625 ha78 hfe3 h195 h580 hq ht hcm hm hα₁ h₁ hcard₁ hcard₂ hα0₁ hα0₂ hα₂' n' β' hβ' hβ'0 hint hA3
  obtain ⟨w, hw, N, hNp, hwu, huw⟩ := finish h625 h0e8 ha78 hfe3 h195 h580 hp hu₀ hu₀0 hinj
  exact ⟨u₀, hu₀, w, hw, N, hNp, hwu, huw⟩

end RPLib.S4T.PrimeToP


