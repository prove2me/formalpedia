-- Prove2me | Definitions.Def_RPLib_S4T_PrimeToPB
-- name    : RPLib_S4T_PrimeToPB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:20:35.894929+00:00
-- url     : https://prove2.me/theorems/660be930-52aa-41ad-87d4-e89aa5ea2040
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: the L4 intertwining trick and the prime-to-`p` descent along one line
-- statement:
--   The L4 intertwining trick and the prime-to-`p` descent along one line.
--
--   * `intertwine` (L4, no commutativity of `End X₂` needed): from `β ≠ 0` get `β' ≠ 0` and a rational `α₂'` with
--     `β' ∘ α₁ = α₂' ∘ β'` (`γ₁ := α₂ ∘ β - β ∘ ᾱ₁` intertwines `α₁` with `α₂`; if it is `0`, `β` intertwines `α₁`
--     with `ᾱ₂`).
--   * `step` / `phase2`: if `ker β` meets the line `L(ᾱ)` trivially, then dividing `β ∘ λ` by `p`, `λ := ᾱ + p c`,
--     lowers the `p`-exponent of `ker β` until `ker β ∩ X[p] = 0`.
--   FLT statements are explicit hypotheses (never used as lemmas).
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_PrimeToPA

/-!
# S4T-PrimeToP, part B: the L4 intertwining trick and the prime-to-`p` descent along one line

* `intertwine` (L4, no commutativity of `End X₂` needed): from `β ≠ 0` get `β' ≠ 0` and a rational `α₂'` with
  `β' ∘ α₁ = α₂' ∘ β'` (`γ₁ := α₂ ∘ β - β ∘ ᾱ₁` intertwines `α₁` with `α₂`; if it is `0`, `β` intertwines `α₁`
  with `ᾱ₂`).
* `step` / `phase2`: if `ker β` meets the line `L(ᾱ)` trivially, then dividing `β ∘ λ` by `p`, `λ := ᾱ + p c`,
  lowers the `p`-exponent of `ker β` until `ker β ∩ X[p] = 0`.
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

theorem bar_mem (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0}) {X : WeierstrassCurve Ω}
    [X.IsElliptic] {t : ℤ} {α : X.toAffine.Point →+ X.toAffine.Point} (hα : α ∈ rationalHomSet Ω X X) :
    bar X t α ∈ rationalHomSet Ω X X :=
  CMGlue.sub_mem h195 h580 X X (CMGlue.zsmul_mem h195 h580 X X (id_mem_rationalHomSet Ω X) t) hα

/-- **L4 trick.** -/
theorem intertwine (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0}) (hfe3 : FLT.S_fe3c6240.{0, 0})
    {X₁ X₂ : WeierstrassCurve Ω} [X₁.IsElliptic] [X₂.IsElliptic] {t q : ℤ}
    {α₁ : X₁.toAffine.Point →+ X₁.toAffine.Point} {α₂ : X₂.toAffine.Point →+ X₂.toAffine.Point}
    (hα₁ : α₁ ∈ rationalHomSet Ω X₁ X₁) (hα₂ : α₂ ∈ rationalHomSet Ω X₂ X₂)
    (h₁ : α₁.comp α₁ + q • AddMonoidHom.id X₁.toAffine.Point = t • α₁)
    (h₂ : α₂.comp α₂ + q • AddMonoidHom.id X₂.toAffine.Point = t • α₂)
    {β : X₁.toAffine.Point →+ X₂.toAffine.Point} (hβ : β ∈ rationalHomSet Ω X₁ X₂) (hβ0 : β ≠ 0) :
    ∃ β' : X₁.toAffine.Point →+ X₂.toAffine.Point, β' ∈ rationalHomSet Ω X₁ X₂ ∧ β' ≠ 0 ∧
      ∃ α₂' : X₂.toAffine.Point →+ X₂.toAffine.Point, α₂' ∈ rationalHomSet Ω X₂ X₂ ∧
        ∀ P, β' (α₁ P) = α₂' (β' P) := by
  by_cases hγ : α₂.comp β - β.comp (bar X₁ t α₁) = 0
  · refine ⟨β, hβ, hβ0, bar X₂ t α₂, bar_mem h195 h580 hα₂, fun P => ?_⟩
    have hP := DFunLike.congr_fun hγ P
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.zero_apply, bar_apply, map_sub,
      map_zsmul, sub_eq_zero] at hP
    rw [bar_apply, hP]
    abel
  · refine ⟨α₂.comp β - β.comp (bar X₁ t α₁), ?_, hγ, α₂, hα₂, fun P => ?_⟩
    · exact CMGlue.sub_mem h195 h580 X₁ X₂ (hfe3 Ω X₁ X₂ X₂ hβ hα₂) (hfe3 Ω X₁ X₁ X₂ (bar_mem h195 h580 hα₁) hβ)
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, bar_apply, map_sub, map_zsmul, ch_apply h₁,
      ch_apply h₂]
    abel

/-! ### The operator `λ = ᾱ + p c` -/

section Lam

variable (X : WeierstrassCurve Ω) (t c : ℤ) (p : ℕ) (α : X.toAffine.Point →+ X.toAffine.Point)

/-- `λ = ᾱ + p c`. -/
def lam : X.toAffine.Point →+ X.toAffine.Point := bar X t α + ((p : ℤ) * c) • AddMonoidHom.id X.toAffine.Point

theorem lam_apply (P : X.toAffine.Point) : lam X t c p α P = bar X t α P + ((p : ℤ) * c) • P := rfl

variable {X t c p α}

theorem lam_mem (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0}) [X.IsElliptic]
    (hα : α ∈ rationalHomSet Ω X X) : lam X t c p α ∈ rationalHomSet Ω X X :=
  h195 Ω X X (bar_mem h195 h580 hα) (CMGlue.zsmul_mem h195 h580 X X (id_mem_rationalHomSet Ω X) _)

theorem lam_comm (P : X.toAffine.Point) : lam X t c p α (α P) = α (lam X t c p α P) := by
  simp only [lam_apply, bar_apply, map_add, map_sub, map_zsmul]

theorem lam_p_kill {P : X.toAffine.Point} (hP : p • P = 0) : lam X t c p α P = bar X t α P := by
  rw [lam_apply, mul_comm, mul_smul, natCast_zsmul, hP, smul_zero, add_zero]

theorem lam_mul {q m : ℤ} (hch : α.comp α + q • AddMonoidHom.id X.toAffine.Point = t • α)
    (hcm : (p : ℤ) * m = q + p * c * t + p ^ 2 * c ^ 2) (P : X.toAffine.Point) :
    α (lam X t c p α P) + ((p : ℤ) * c) • lam X t c p α P = ((p : ℤ) * m) • P := by
  rw [lam_apply, map_add, comp_bar_apply hch, map_zsmul, hcm, bar_apply]
  module

end Lam

/-- The constants: `p m = q + p c t + p² c²` with `p ∤ m` (`c = 0` if `q = p`, else `c = 1`). -/
theorem exists_cm {p : ℕ} (hp : p.Prime) {t q : ℤ} (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n)
    (ht : ¬ (p : ℤ) ∣ t) :
    ∃ c m : ℤ, (p : ℤ) * m = q + p * c * t + p ^ 2 * c ^ 2 ∧ IsCoprime m (p : ℤ) := by
  obtain ⟨n, hn, rfl⟩ := hq
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rcases k with _ | k
  · exact ⟨0, 1, by ring, isCoprime_one_left⟩
  · refine ⟨1, (p : ℤ) ^ (k + 1) + t + p, by ring, ?_⟩
    have hirr := (Nat.prime_iff_prime_int.mp hp).irreducible
    refine ((Irreducible.coprime_iff_not_dvd hirr).2 ?_).symm
    intro h
    apply ht
    have : t = ((p : ℤ) ^ (k + 1) + t + p) - p * ((p : ℤ) ^ k + 1) := by ring
    rw [this]
    exact dvd_sub h (dvd_mul_right _ _)

/-- `ker β ∩ X[p] ⊆ L(α)` when `ker β ∩ L(ᾱ) = 0`. -/
theorem kerp_alpha {p : ℕ} (hp : p.Prime) {X₁ X₂ : WeierstrassCurve Ω} {t q : ℤ}
    (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n) (ht : ¬ (p : ℤ) ∣ t) {α : X₁.toAffine.Point →+ X₁.toAffine.Point}
    (hch : α.comp α + q • AddMonoidHom.id X₁.toAffine.Point = t • α)
    {α₂' : X₂.toAffine.Point →+ X₂.toAffine.Point} {β : X₁.toAffine.Point →+ X₂.toAffine.Point}
    (hint : ∀ P, β (α P) = α₂' (β P)) (hA2 : ∀ Y ∈ Lsub X₁ p (bar X₁ t α), β Y = 0 → Y = 0)
    {Z : X₁.toAffine.Point} (hZ : p • Z = 0) (hβZ : β Z = 0) : α Z = 0 := by
  obtain ⟨d, u, hdu⟩ := exists_inv p hp ht
  have h3 := hA2 _ (split_mem₁ p hch hq d hZ) (by rw [map_zsmul, hint, hβZ, map_zero, smul_zero])
  exact eq_zero_of_coprime (a := d) (b := (p : ℤ)) ⟨t, u, by linear_combination hdu⟩ h3
    (by rw [natCast_zsmul, ← map_nsmul, hZ, map_zero])

/-- **Case A step.** `β` kills `L(α)`, meets `L(ᾱ)` trivially, `ker β ∩ G ⊆ X[p^(e+1)]`: then `β ∘ λ = p β''`
with `β''` of the same kind and `ker β'' ∩ G ⊆ X[p^e]`. -/
theorem step (h625 : FLT.S_6256914e.{0, 0}) (ha78 : FLT.S_a78cfa46.{0, 0}) (hfe3 : FLT.S_fe3c6240.{0, 0})
    (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0}) {p : ℕ} [Fact p.Prime]
    {X₁ X₂ : WeierstrassCurve Ω} [X₁.IsElliptic] [X₂.IsElliptic] {t q c m : ℤ}
    (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n) (ht : ¬ (p : ℤ) ∣ t)
    (hcm : (p : ℤ) * m = q + p * c * t + p ^ 2 * c ^ 2) (hm : IsCoprime m (p : ℤ))
    {α : X₁.toAffine.Point →+ X₁.toAffine.Point} (hα : α ∈ rationalHomSet Ω X₁ X₁)
    (hch : α.comp α + q • AddMonoidHom.id X₁.toAffine.Point = t • α)
    (hα0 : ∃ Y : X₁.toAffine.Point, Y ≠ 0 ∧ Y ∈ Lsub X₁ p α)
    {α₂' : X₂.toAffine.Point →+ X₂.toAffine.Point} (hα₂' : α₂' ∈ rationalHomSet Ω X₂ X₂)
    {β : X₁.toAffine.Point →+ X₂.toAffine.Point} (hβ : β ∈ rationalHomSet Ω X₁ X₂) (hβ0 : β ≠ 0)
    (hint : ∀ P, β (α P) = α₂' (β P)) (hA1 : ∀ Y ∈ Lsub X₁ p α, β Y = 0)
    (hA2 : ∀ Y ∈ Lsub X₁ p (bar X₁ t α), β Y = 0 → Y = 0) {e : ℕ}
    (hA3 : ∀ (P : X₁.toAffine.Point) (k : ℕ), p ^ k • P = 0 → β P = 0 → p ^ (e + 1) • P = 0) :
    ∃ β'' : X₁.toAffine.Point →+ X₂.toAffine.Point, β'' ∈ rationalHomSet Ω X₁ X₂ ∧ β'' ≠ 0 ∧
      (∀ P, β'' (α P) = α₂' (β'' P)) ∧ (∀ Y ∈ Lsub X₁ p (bar X₁ t α), β'' Y = 0 → Y = 0) ∧
      ∀ (P : X₁.toAffine.Point) (k : ℕ), p ^ k • P = 0 → β'' P = 0 → p ^ e • P = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨d, u, hdu⟩ := exists_inv p hp ht
  have hlam : lam X₁ t c p α ∈ rationalHomSet Ω X₁ X₁ := lam_mem h195 h580 hα
  have hker : ∀ P : X₁.toAffine.Point, ((p : ℕ) : ℤ) • P = 0 → (β.comp (lam X₁ t c p α)) P = 0 := by
    intro P hP
    have hP' : p • P = 0 := by rwa [natCast_zsmul] at hP
    rw [AddMonoidHom.comp_apply, lam_p_kill hP']
    apply hA1
    have := split_mem₀ p hch hq 1 hP'
    rwa [one_smul] at this
  obtain ⟨β₀, hβ₀, hβeq⟩ := h625 Ω X₁ X₂ (Nat.cast_ne_zero.mpr hp.ne_zero : ((p : ℕ) : Ω) ≠ 0)
    (hfe3 Ω X₁ X₁ X₂ hlam hβ) hker
  let β'' : X₁.toAffine.Point →+ X₂.toAffine.Point := β₀
  have hβ'' : β'' ∈ rationalHomSet Ω X₁ X₂ := hβ₀
  have hβP : ∀ P : X₁.toAffine.Point, β (lam X₁ t c p α P) = ((p : ℕ) : ℤ) • β'' P := hβeq
  have hβPn : ∀ P : X₁.toAffine.Point, β (lam X₁ t c p α P) = β'' (p • P) := fun P => by
    rw [hβP, natCast_zsmul, map_nsmul]
  have hlam0 : lam X₁ t c p α ≠ 0 := by
    obtain ⟨Y, hY0, hY⟩ := hα0
    intro h0
    have h1 := DFunLike.congr_fun h0 Y
    rw [lam_p_kill (mem_Lsub.mp hY).1, AddMonoidHom.zero_apply, bar_apply, (mem_Lsub.mp hY).2, sub_zero] at h1
    exact hY0 (eq_zero_of_coprime ⟨d, u, hdu⟩ h1 (by rw [natCast_zsmul]; exact (mem_Lsub.mp hY).1))
  have hsurj := ha78 Ω hlam hlam0
  have hβ''0 : β'' ≠ 0 := by
    intro h0
    apply hβ0
    ext Q
    obtain ⟨P, rfl⟩ := hsurj Q
    show β (lam X₁ t c p α P) = 0
    rw [hβP, h0, AddMonoidHom.zero_apply, smul_zero]
  have hint'' : ∀ P, β'' (α P) = α₂' (β'' P) := by
    have := eq_of_nsmul ha78 h195 h580 X₁ X₂ (hfe3 Ω X₁ X₁ X₂ hα hβ'') (hfe3 Ω X₁ X₂ X₂ hβ'' hα₂') p hp.pos
      (fun P => by
        show p • β'' (α P) = p • α₂' (β'' P)
        rw [← natCast_zsmul (β'' (α P)) p, ← hβP, ← map_nsmul α₂' p (β'' P), ← natCast_zsmul (β'' P) p,
          ← hβP, lam_comm, hint])
    exact fun P => DFunLike.congr_fun this P
  have hA2'' : ∀ Y ∈ Lsub X₁ p (bar X₁ t α), β'' Y = 0 → Y = 0 := by
    intro Y hY hβ''Y
    obtain ⟨hpY, hbY⟩ := mem_Lsub.mp hY
    obtain ⟨Y', rfl⟩ := exists_nsmul_eq ha78 h195 X₁ p hp.pos Y
    have hW : β (lam X₁ t c p α Y') = 0 := by rw [hβPn, hβ''Y]
    have hpW : p • lam X₁ t c p α Y' = 0 := by
      rw [← map_nsmul, lam_apply, hbY, zero_add, mul_comm, mul_smul, natCast_zsmul, hpY, smul_zero]
    have hαW := kerp_alpha hp hq ht hch hint hA2 hpW hW
    have hl := lam_mul hch hcm Y'
    rw [hαW, zero_add, mul_comm (p : ℤ) c, mul_smul, natCast_zsmul _ p, hpW, smul_zero, mul_comm, mul_smul,
      natCast_zsmul _ p] at hl
    exact eq_zero_of_coprime hm hl.symm (by rw [natCast_zsmul]; exact hpY)
  refine ⟨β'', hβ'', hβ''0, hint'', hA2'', ?_⟩
  intro P k hk hβ''P
  obtain ⟨P', rfl⟩ := exists_nsmul_eq ha78 h195 X₁ p hp.pos P
  have hk' : p ^ (k + 1) • P' = 0 := by rw [pow_succ, mul_smul, hk]
  have hR : β (lam X₁ t c p α P') = 0 := by rw [hβPn, hβ''P]
  have hRk : p ^ (k + 1) • lam X₁ t c p α P' = 0 := by rw [← map_nsmul, hk', map_zero]
  have hER := hA3 _ (k + 1) hRk hR
  have hlamQ : lam X₁ t c p α (p ^ (e + 1) • P') = 0 := by rw [map_nsmul, hER]
  have hQk0 : p ^ (k + 1) • (p ^ (e + 1) • P') = 0 := by rw [smul_comm, hk', smul_zero]
  have hQk : p ^ (k + 1) • (p • (p ^ (e + 1) • P')) = 0 := by rw [smul_comm, hQk0, smul_zero]
  have hpQ : p • (p ^ (e + 1) • P') = 0 := by
    have hl := lam_mul hch hcm (p ^ (e + 1) • P')
    rw [hlamQ, map_zero, smul_zero, zero_add, mul_comm, mul_smul, natCast_zsmul _ p] at hl
    exact eq_zero_of_coprime (hm.pow_right (n := k + 1)) hl.symm
      (by rw [← Nat.cast_pow, natCast_zsmul]; exact hQk)
  have hQL : p ^ (e + 1) • P' ∈ Lsub X₁ p (bar X₁ t α) := by
    rw [mem_Lsub]
    refine ⟨hpQ, ?_⟩
    have := hlamQ
    rwa [lam_apply, mul_comm, mul_smul, natCast_zsmul _ p, hpQ, smul_zero, add_zero] at this
  have hβ''Q : β'' (p ^ (e + 1) • P') = 0 := by rw [pow_succ, mul_smul, map_nsmul, hβ''P, smul_zero]
  have hQ0 := hA2'' _ hQL hβ''Q
  rw [← mul_smul, ← pow_succ]
  exact hQ0

/-- **Phase 2.** Induction on the `p`-exponent of `ker β` along the line `L(α)`. -/
theorem phase2 (h625 : FLT.S_6256914e.{0, 0}) (ha78 : FLT.S_a78cfa46.{0, 0}) (hfe3 : FLT.S_fe3c6240.{0, 0})
    (h195 : FLT.S_195173b3.{0, 0}) (h580 : FLT.S_580839d4.{0, 0}) {p : ℕ} [Fact p.Prime]
    {X₁ X₂ : WeierstrassCurve Ω} [X₁.IsElliptic] [X₂.IsElliptic] {t q c m : ℤ}
    (hq : ∃ n : ℕ, 0 < n ∧ q = (p : ℤ) ^ n) (ht : ¬ (p : ℤ) ∣ t)
    (hcm : (p : ℤ) * m = q + p * c * t + p ^ 2 * c ^ 2) (hm : IsCoprime m (p : ℤ))
    {α : X₁.toAffine.Point →+ X₁.toAffine.Point} (hα : α ∈ rationalHomSet Ω X₁ X₁)
    (hch : α.comp α + q • AddMonoidHom.id X₁.toAffine.Point = t • α) (hcard : Nat.card (Lsub X₁ p α) = p)
    (hα0 : ∃ Y : X₁.toAffine.Point, Y ≠ 0 ∧ Y ∈ Lsub X₁ p α)
    {α₂' : X₂.toAffine.Point →+ X₂.toAffine.Point} (hα₂' : α₂' ∈ rationalHomSet Ω X₂ X₂) (e : ℕ) :
    ∀ β : X₁.toAffine.Point →+ X₂.toAffine.Point, β ∈ rationalHomSet Ω X₁ X₂ → β ≠ 0 →
      (∀ P, β (α P) = α₂' (β P)) → (∀ Y ∈ Lsub X₁ p (bar X₁ t α), β Y = 0 → Y = 0) →
      (∀ (P : X₁.toAffine.Point) (k : ℕ), p ^ k • P = 0 → β P = 0 → p ^ e • P = 0) →
      ∃ u : X₁.toAffine.Point →+ X₂.toAffine.Point, u ∈ rationalHomSet Ω X₁ X₂ ∧ u ≠ 0 ∧
        ∀ P, p • P = 0 → u P = 0 → P = 0 := by
  have hp : p.Prime := Fact.out
  induction e with
  | zero =>
    intro β hβ hβ0 _ _ hA3
    refine ⟨β, hβ, hβ0, fun P hP hβP => ?_⟩
    have := hA3 P 1 (by rwa [pow_one]) hβP
    rwa [pow_zero, one_smul] at this
  | succ e ih =>
    intro β hβ hβ0 hint hA2 hA3
    by_cases hinj : ∀ P, p • P = 0 → β P = 0 → P = 0
    · exact ⟨β, hβ, hβ0, hinj⟩
    push Not at hinj
    obtain ⟨Z, hZp, hβZ, hZ0⟩ := hinj
    have hZα := kerp_alpha hp hq ht hch hint hA2 hZp hβZ
    have hA1 : ∀ Y ∈ Lsub X₁ p α, β Y = 0 := by
      intro Y hY
      obtain ⟨k, rfl⟩ := L_zmultiples hcard hZ0 (mem_Lsub.mpr ⟨hZp, hZα⟩) hY
      rw [map_zsmul, hβZ, smul_zero]
    obtain ⟨β'', hβ'', hβ''0, hint'', hA2'', hA3''⟩ :=
      step h625 ha78 hfe3 h195 h580 hq ht hcm hm hα hch hα0 hα₂' hβ hβ0 hint hA1 hA2 hA3
    exact ih β'' hβ'' hβ''0 hint'' hA2'' hA3''

end RPLib.S4T.PrimeToP


