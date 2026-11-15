-- Prove2me | Definitions.Def_RPLib_S3_DWSTateK
-- name    : RPLib_S3_DWSTateK
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:41:19.546689+00:00
-- url     : https://prove2.me/theorems/98579a4f-4e73-4de5-8f1b-74ca50ff2bb6
-- title:
--   Weight-two Ramanujan-Petersson library: the ideal `I'` of an `R`-stable quotient and its properness (b7c, step K)
-- statement:
--   The ideal `I'` of an `R`-stable quotient and its properness (b7c, step K).
--
--   Setting: `hq : IsQuot G φ ψ n` (`φ : E → E₁`), `R`-structures `s`, `s₁`, `φ` `R`-linear (`hφ`).
--   * `IsQuot.ι_mem`: `G` is `R`-stable.
--   * `idealOf s hq hφ P₀ = {r | ι r P₀ ∈ G}` (`I'`), `natCast_mem_idealOf`, `mem_iff_idealOf` (`G = I' P₀`).
--   * `annOf I' n = {x | ∀ t ∈ I', n ∣ x t}` (`I = Ann G`), `natCast_mem_annOf`.
--   * **`proper_idealOf`**: `y I' ⊆ n I'` ⇒ `n ∣ y` (uses `End(E₁) = R` through FAITH on `E₁`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateJ

/-!
# S3-DWS-Tate, part K: the ideal `I'` of an `R`-stable quotient and its properness (b7c, step K)

Setting: `hq : IsQuot G φ ψ n` (`φ : E → E₁`), `R`-structures `s`, `s₁`, `φ` `R`-linear (`hφ`).
* `IsQuot.ι_mem`: `G` is `R`-stable.
* `idealOf s hq hφ P₀ = {r | ι r P₀ ∈ G}` (`I'`), `natCast_mem_idealOf`, `mem_iff_idealOf` (`G = I' P₀`).
* `annOf I' n = {x | ∀ t ∈ I', n ∣ x t}` (`I = Ann G`), `natCast_mem_annOf`.
* **`proper_idealOf`**: `y I' ⊆ n I'` ⇒ `n ∣ y` (uses `End(E₁) = R` through FAITH on `E₁`).
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section AnnDef

variable {R : Type*} [CommRing R]

/-- `I = {x | x I' ⊆ nR}`. -/
def annOf (I' : Ideal R) (n : ℕ) : Ideal R where
  carrier := {x | ∀ t ∈ I', (n : R) ∣ x * t}
  add_mem' := fun {x y} hx hy t ht => by rw [add_mul]; exact dvd_add (hx t ht) (hy t ht)
  zero_mem' := fun t _ => by rw [zero_mul]; exact dvd_zero _
  smul_mem' := fun c x hx t ht => by rw [smul_eq_mul, mul_assoc]; exact dvd_mul_of_dvd_right (hx t ht) c

lemma mem_annOf {I' : Ideal R} {n : ℕ} {x : R} : x ∈ annOf I' n ↔ ∀ t ∈ I', (n : R) ∣ x * t := Iff.rfl

lemma natCast_mem_annOf (I' : Ideal R) (n : ℕ) : (n : R) ∈ annOf I' n := fun t _ => dvd_mul_right _ _

end AnnDef

section K

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W W₁ : WeierstrassCurve F} [W.IsElliptic] [W₁.IsElliptic] {R : Type*} [CommRing R]
  {s : OAct R W L} {s₁ : OAct R W₁ L} {G : AddSubgroup (Pt W L)} {φ : Pt W L →+ Pt W₁ L}
  {ψ : Pt W₁ L →+ Pt W L} {n : ℕ}

/-- (K1) `G = ker φ` is `R`-stable when `φ` is `R`-linear. -/
lemma IsQuot.ι_mem (hq : IsQuot G φ ψ n) (hφ : ∀ r, r ∈ commSub s s₁ φ) (r : R) {P : Pt W L}
    (hP : P ∈ G) : s.ι r P ∈ G := by
  rw [← hq.ker] at hP ⊢
  rw [(mem_commSub.mp (hφ r)) P, hP, map_zero]

variable (s) in
/-- (K2) `I' = {r | ι r P₀ ∈ G}`. -/
def idealOf (hq : IsQuot G φ ψ n) (hφ : ∀ r, r ∈ commSub s s₁ φ) (P₀ : Pt W L) : Ideal R where
  carrier := {r | s.ι r P₀ ∈ G}
  add_mem' := fun {x y} hx hy => by
    show s.ι (x + y) P₀ ∈ G
    rw [s.ι_add_apply]; exact G.add_mem hx hy
  zero_mem' := by
    show s.ι 0 P₀ ∈ G
    rw [s.ι_zero_apply]; exact G.zero_mem
  smul_mem' := fun c x hx => by
    show s.ι (c * x) P₀ ∈ G
    rw [s.ι_mul_apply]; exact hq.ι_mem hφ c hx

lemma mem_idealOf {hq : IsQuot G φ ψ n} {hφ : ∀ r, r ∈ commSub s s₁ φ} {P₀ : Pt W L} {r : R} :
    r ∈ idealOf s hq hφ P₀ ↔ s.ι r P₀ ∈ G := Iff.rfl

lemma natCast_mem_idealOf (hq : IsQuot G φ ψ n) (hφ : ∀ r, r ∈ commSub s s₁ φ) {P₀ : Pt W L}
    (hP₀ : n • P₀ = 0) : (n : R) ∈ idealOf s hq hφ P₀ := by
  rw [mem_idealOf, s.natCast_apply, hP₀]; exact G.zero_mem

variable {a b : ℤ} {s : OAct (QuadraticAlgebra ℤ a b) W L} {s₁ : OAct (QuadraticAlgebra ℤ a b) W₁ L}

/-- (K2) `G = I' P₀` for a free generator `P₀` of `E[n]`. -/
lemma mem_iff_idealOf (hq : IsQuot G φ ψ n) (hφ : ∀ r, r ∈ commSub s s₁ φ) {P₀ : Pt W L}
    (hgen : IsGen s n P₀) {P : Pt W L} : P ∈ G ↔ ∃ t ∈ idealOf s hq hφ P₀, s.ι t P₀ = P := by
  constructor
  · intro hP
    obtain ⟨t, ht⟩ := hgen.exists_eq hq.hn (hq.nsmul_eq_zero hP)
    exact ⟨t, by rw [mem_idealOf, ht]; exact hP, ht⟩
  · rintro ⟨t, ht, rfl⟩
    exact ht

/-- **(K4) Properness**: if `y I' ⊆ n I'` then `n ∣ y` (`I'` built from `P₀ = n P₁`, `P₁` a free generator
of `E[n²]`). Proof: `ι₁ y` kills `E₁[n]`, then FAITH on `E₁`. -/
theorem proper_idealOf (hq : IsQuot G φ ψ n) (hφ : ∀ r, r ∈ commSub s s₁ φ) {P₁ : Pt W L}
    (h₁ : IsGen s (n * n) P₁) {y : QuadraticAlgebra ℤ a b}
    (hy : ∀ t ∈ idealOf s hq hφ (n • P₁), ∃ t' ∈ idealOf s hq hφ (n • P₁), y * t = n * t') :
    (n : QuadraticAlgebra ℤ a b) ∣ y := by
  apply s₁.natCast_dvd_of_kills hq.hn
  intro Q hQ
  obtain ⟨P, rfl⟩ := hq.surj Q
  have hnP : n • P ∈ G := (hq.ker _).mp (by rw [map_nsmul]; exact hQ)
  have hnnP : (n * n) • P = 0 := by rw [mul_nsmul', hq.nsmul_eq_zero hnP]
  have hnn : ((n * n : ℕ) : F) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hq.hn hq.hn
  obtain ⟨t, rfl⟩ := h₁.exists_eq hnn hnnP
  have ht : t ∈ idealOf s hq hφ (n • P₁) := by
    rw [mem_idealOf, map_nsmul]; exact hnP
  obtain ⟨t', ht', he⟩ := hy t ht
  rw [← (mem_commSub.mp (hφ y)), ← s.ι_mul_apply, he, s.ι_mul_apply, s.natCast_apply, ← map_nsmul]
  exact (hq.ker _).mpr ht'

end K

end RPLib.DWS


