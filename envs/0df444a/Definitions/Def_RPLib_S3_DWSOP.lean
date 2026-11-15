-- Prove2me | Definitions.Def_RPLib_S3_DWSOP
-- name    : RPLib_S3_DWSOP
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:39:50.714206+00:00
-- url     : https://prove2.me/theorems/3824ebef-4c0f-4c8f-b473-4e4f97885695
-- title:
--   Weight-two Ramanujan-Petersson library: points of exact order `M` through a free generator (O4)
-- statement:
--   Points of exact order `M` through a free generator (O4).
--
--   `R = QuadraticAlgebra ℤ a b` acting on an elliptic curve `W/F_q` by an `R`-structure `s` (`s.ι : R ≅ End_{F_q}(E)`)
--   with `s.ι π = Frobenius`. A free generator `P₀` of `E[M]` (`exists_isGen`, `p ∤ M`) gives the parametrisation
--   `kap : (ℤ/M)² → E[M]`, `v ↦ (v₀ + v₁ ω) P₀`, an injective additive map onto `E[M]` carrying the matrix of
--   multiplication by `π` (`mulMat π`) to the Frobenius.
--   **`card_ptOrd_eq_levelCount`**: `#{P ∈ W(F_q) of exact order M} = levelCount M 1 (mulMat π)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_Statements
import Definitions.Def_RPLib_S3_DWSTateJ
import Definitions.Def_RPLib_S3_DWSOM

/-!
# S3-DWS-Ordinary, part P: points of exact order `M` through a free generator (O4)

`R = QuadraticAlgebra ℤ a b` acting on an elliptic curve `W/F_q` by an `R`-structure `s` (`s.ι : R ≅ End_{F_q}(E)`)
with `s.ι π = Frobenius`. A free generator `P₀` of `E[M]` (`exists_isGen`, `p ∤ M`) gives the parametrisation
`kap : (ℤ/M)² → E[M]`, `v ↦ (v₀ + v₁ ω) P₀`, an injective additive map onto `E[M]` carrying the matrix of
multiplication by `π` (`mulMat π`) to the Frobenius.
**`card_ptOrd_eq_levelCount`**: `#{P ∈ W(F_q) of exact order M} = levelCount M 1 (mulMat π)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Matrix

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS

section Alg

variable {a b : ℤ} {M : ℕ} [NeZero M]

/-- The matrix of multiplication by `π = x + y ω` on `ℤ[ω]` (`ω² = a + b ω`) in the basis `1, ω`. -/
def mulMat (π : QuadraticAlgebra ℤ a b) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![π.re, a * π.im; π.im, π.re + b * π.im]

/-- The lift `v ↦ v₀ + v₁ ω` with `0 ≤ vᵢ < M`. -/
def vecQA (v : Fin 2 → ZMod M) : QuadraticAlgebra ℤ a b := ⟨((v 0).val : ℤ), ((v 1).val : ℤ)⟩

variable (M) in
/-- Reduction `R → (ℤ/M)²` in the basis `1, ω`. -/
def red (r : QuadraticAlgebra ℤ a b) : Fin 2 → ZMod M := ![(r.re : ZMod M), (r.im : ZMod M)]

lemma red_vecQA (v : Fin 2 → ZMod M) : red M (vecQA (a := a) (b := b) v) = v := by
  funext i; fin_cases i <;> simp [red, vecQA]

lemma red_add (r r' : QuadraticAlgebra ℤ a b) : red M (r + r') = red M r + red M r' := by
  funext i; fin_cases i <;> simp [red]

lemma red_mul (π r : QuadraticAlgebra ℤ a b) :
    red M (π * r) = (mulMat π).map (Int.castRingHom (ZMod M)) *ᵥ red M r := by
  funext i; fin_cases i <;>
    simp [red, mulMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] <;> ring

lemma dvd_vecQA_red_sub (r : QuadraticAlgebra ℤ a b) : (M : QuadraticAlgebra ℤ a b) ∣ vecQA (red M r) - r := by
  rw [natCast_dvd_iff_QA]
  constructor
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    simp [vecQA, red]
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    simp [vecQA, red]

lemma red_eq_of_dvd {r r' : QuadraticAlgebra ℤ a b} (h : (M : QuadraticAlgebra ℤ a b) ∣ r - r') :
    red M r = red M r' := by
  rw [natCast_dvd_iff_QA] at h
  have e1 : ((r.re - r'.re : ℤ) : ZMod M) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr (by simpa using h.1)
  have e2 : ((r.im - r'.im : ℤ) : ZMod M) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr (by simpa using h.2)
  push_cast at e1 e2
  funext i; fin_cases i
  · simpa [red] using sub_eq_zero.mp e1
  · simpa [red] using sub_eq_zero.mp e2

lemma eq_of_dvd_vecQA {v v' : Fin 2 → ZMod M}
    (h : (M : QuadraticAlgebra ℤ a b) ∣ vecQA v - vecQA v') : v = v' := by
  rw [← red_vecQA (a := a) (b := b) v, ← red_vecQA (a := a) (b := b) v']
  exact red_eq_of_dvd h

end Alg

section Pts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L]
  [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W : WeierstrassCurve F} [W.IsElliptic] {a b : ℤ} (s : OAct (QuadraticAlgebra ℤ a b) W L)
  {M : ℕ} [NeZero M] {P₀ : Pt W L}

lemma ι_eq_of_dvd (hP₀ : M • P₀ = 0) {r r' : QuadraticAlgebra ℤ a b}
    (h : (M : QuadraticAlgebra ℤ a b) ∣ r - r') : s.ι r P₀ = s.ι r' P₀ := by
  obtain ⟨k, hk⟩ := h
  have h0 : s.ι (r - r') P₀ = 0 := by
    rw [hk, mul_comm, s.ι_mul_apply, s.natCast_apply, hP₀, map_zero]
  rwa [s.ι_sub_apply, sub_eq_zero] at h0

variable (P₀) in
/-- The parametrisation `(ℤ/M)² → E[M]`, `v ↦ (v₀ + v₁ ω) P₀`. -/
noncomputable def kap (v : Fin 2 → ZMod M) : Pt W L := s.ι (vecQA v) P₀

lemma ι_apply_eq_kap (hP₀ : M • P₀ = 0) (r : QuadraticAlgebra ℤ a b) : s.ι r P₀ = kap s P₀ (red M r) :=
  (ι_eq_of_dvd s hP₀ (dvd_vecQA_red_sub r)).symm

lemma kap_add (hP₀ : M • P₀ = 0) (v w : Fin 2 → ZMod M) :
    kap s P₀ (v + w) = kap s P₀ v + kap s P₀ w := by
  have hvw : v + w = red M (vecQA (a := a) (b := b) v + vecQA w) := by
    rw [red_add, red_vecQA, red_vecQA]
  rw [hvw, ← ι_apply_eq_kap s hP₀, s.ι_add_apply]
  rfl

lemma kap_zero (hP₀ : M • P₀ = 0) : kap s P₀ (0 : Fin 2 → ZMod M) = 0 := by
  have h := kap_add s hP₀ (0 : Fin 2 → ZMod M) 0
  rw [add_zero] at h
  simpa using h

/-- `kap` as an additive map. -/
noncomputable def kapHom (hP₀ : M • P₀ = 0) : (Fin 2 → ZMod M) →+ Pt W L where
  toFun := kap s P₀
  map_zero' := kap_zero s hP₀
  map_add' := kap_add s hP₀

lemma kap_nsmul (hP₀ : M • P₀ = 0) (d : ℕ) (v : Fin 2 → ZMod M) : d • kap s P₀ v = kap s P₀ (d • v) :=
  (map_nsmul (kapHom s hP₀) d v).symm

lemma kap_injective (hG : IsGen s M P₀) : Function.Injective (kap s P₀ : (Fin 2 → ZMod M) → Pt W L) := by
  intro v v' h
  apply eq_of_dvd_vecQA (a := a) (b := b)
  apply hG.2
  rw [s.ι_sub_apply]
  exact sub_eq_zero.mpr h

lemma kap_eq_zero_iff (hG : IsGen s M P₀) (v : Fin 2 → ZMod M) : kap s P₀ v = 0 ↔ v = 0 :=
  (kap_injective s hG).eq_iff' (kap_zero s hG.1)

lemma kap_mem (hG : IsGen s M P₀) (v : Fin 2 → ZMod M) : M • kap s P₀ v = 0 := by
  rw [kap, ← map_nsmul, hG.1, map_zero]

lemma exists_kap (hM : (M : F) ≠ 0) (hG : IsGen s M P₀) {P : Pt W L} (hP : M • P = 0) :
    ∃ v : Fin 2 → ZMod M, kap s P₀ v = P := by
  obtain ⟨r, hr⟩ := IsGen.exists_eq hM hG hP
  exact ⟨red M r, by rw [← ι_apply_eq_kap s hG.1, hr]⟩

lemma frob_kap {π : QuadraticAlgebra ℤ a b} (hπ : s.ι π = piE W L) (hG : IsGen s M P₀)
    (v : Fin 2 → ZMod M) :
    piE W L (kap s P₀ v) = kap s P₀ ((mulMat π).map (Int.castRingHom (ZMod M)) *ᵥ v) := by
  rw [← hπ]
  show s.ι π (s.ι (vecQA v) P₀) = _
  rw [← s.ι_mul_apply, ι_apply_eq_kap s hG.1, red_mul, red_vecQA]

lemma addOrderOf_kap (hG : IsGen s M P₀) (v : Fin 2 → ZMod M) :
    addOrderOf (kap s P₀ v) = M ↔ ∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0 := by
  rw [addOrderOf_eq_iff (Nat.pos_of_ne_zero (NeZero.ne M))]
  have key : ∀ d : ℕ, d • kap s P₀ v = 0 ↔ d • v = 0 := fun d => by
    rw [kap_nsmul s hG.1, kap_eq_zero_iff s hG]
  refine ⟨fun h d hd hd0 => ?_, fun h => ⟨kap_mem s hG v, fun d hd hd0 => ?_⟩⟩
  · have := h.2 d (Finset.mem_range.mp hd) hd0
    exact fun h0 => this ((key d).mpr h0)
  · have := h d (Finset.mem_range.mpr hd) hd0
    exact fun h0 => this ((key d).mp h0)

omit [NeZero M] in
lemma levelCount_eq_natCard (M : ℕ) [NeZero M] (δ' : ZMod M) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    levelCount M δ' g = Nat.card {v : Fin 2 → ZMod M // (∀ d ∈ Finset.range M, 0 < d → d • v ≠ 0) ∧
      (g.map (Int.castRingHom (ZMod M))).mulVec v = δ' • v} := by
  rw [levelCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Frobenius-fixed points of `E(F̄_q)` of exact order `M`. -/
def FixOrd (W : WeierstrassCurve F) [W.IsElliptic] (L : Type*) [Field L] [Algebra F L] [IsAlgClosed L]
    [DecidableEq L] (M : ℕ) : Type _ :=
  {Q : Pt W L // piE W L Q = Q ∧ addOrderOf Q = M}

/-- `W(F_q)[exact M] ≃ E(F̄_q)^{Frob}[exact M]` via base change. -/
noncomputable def ptOrdToFix : PtOrd W M → FixOrd W L M := fun P =>
  ⟨RPLib.EllFq.baseChangePt W L P.1, (RPLib.EllFq.frob_eq_self_iff W L _).mpr ⟨P.1, rfl⟩, by
    rw [addOrderOf_injective _ (RPLib.EllFq.baseChangePt_injective W L)]; exact P.2⟩

lemma ptOrdToFix_bijective : Function.Bijective (ptOrdToFix (W := W) (L := L) (M := M)) := by
  refine ⟨fun P P' h => Subtype.ext (RPLib.EllFq.baseChangePt_injective W L (congrArg Subtype.val h)), ?_⟩
  rintro ⟨Q, hQ, hord⟩
  obtain ⟨P, rfl⟩ := (RPLib.EllFq.frob_eq_self_iff W L Q).mp hQ
  refine ⟨⟨P, ?_⟩, rfl⟩
  rwa [addOrderOf_injective _ (RPLib.EllFq.baseChangePt_injective W L)] at hord

/-- **(O4)** `#{P ∈ W(F_q) of exact order M} = levelCount M 1 (mulMat π)` for an `R`-structure with
`s.ι π = Frobenius`, `p ∤ M`. -/
theorem card_ptOrd_eq_levelCount (hM : (M : F) ≠ 0) {π : QuadraticAlgebra ℤ a b} (hπ : s.ι π = piE W L) :
    Nat.card (PtOrd W M) = levelCount M 1 (mulMat π) := by
  obtain ⟨P₀, hG⟩ := exists_isGen s M hM
  rw [Nat.card_congr (Equiv.ofBijective _ (ptOrdToFix_bijective (W := W) (L := L) (M := M))),
    levelCount_eq_natCard]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun v => (⟨kap s P₀ v.1, ?_, ?_⟩ : FixOrd W L M)) ⟨?_, ?_⟩)
  · rw [frob_kap s hπ hG, v.2.2, one_smul]
  · exact (addOrderOf_kap s hG v.1).mpr v.2.1
  · intro v v' h
    exact Subtype.ext (kap_injective s hG (congrArg Subtype.val h))
  · rintro ⟨Q, hQ, hord⟩
    have hMQ : M • Q = 0 := by rw [← hord]; exact addOrderOf_nsmul_eq_zero Q
    obtain ⟨v, rfl⟩ := exists_kap s hM hG hMQ
    have hfix : (mulMat π).map (Int.castRingHom (ZMod M)) *ᵥ v = (1 : ZMod M) • v := by
      rw [one_smul]
      apply kap_injective s hG
      rw [← frob_kap s hπ hG, hQ]
    exact ⟨⟨v, (addOrderOf_kap s hG v).mp hord, hfix⟩, rfl⟩

end Pts

end RamanujanPetersson.S3.DWSO


