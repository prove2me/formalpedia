-- Prove2me | Definitions.Def_RPLib_S3_DWSTateH
-- name    : RPLib_S3_DWSTateH
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:33:31.837217+00:00
-- url     : https://prove2.me/theorems/2fd4dcdf-6ee8-46a3-8bbd-b4876a3726c0
-- title:
--   Weight-two Ramanujan-Petersson library: ideal classes ↔ quotient curves (b9 assembly, injectivity half)
-- statement:
--   Ideal classes ↔ quotient curves (b9 assembly, injectivity half).
--
--   `R = QuadraticAlgebra ℤ a b` (`D = b² + 4a < 0`) acting on `E` by an `R`-structure `s : OAct R W L`.
--   * `GoodIdeal F I`: `I I' = (N)` with `p ∤ N`; `picMk hD hI` its class in `PicQ hD`.
--   * `exists_good_rep`: every ideal class has a good representative (`p ∤ f.a` for a form ideal `I_f`).
--   * `exists_principal_of_rel`: `[I] = [J]` (good) ⇒ `(N_J) I = (γ) J` with `γ γ̄ = M`, `p ∤ M`.
--   * `QuotClass hD s c W₁`: `W₁` is a Vélu quotient `E → E/E[I]` for a good `I` of class `c`.
--   * **`exists_quotClass`** (every class is realised), **`isoFq_iff_of_quotClass`** (`E/E[I] ≅ E/E[J]` ⇔ `[I] = [J]`),
--     `quotClass_of_isoFq` (the realised set is closed under `≅`).
--   * `endFqEquiv s : R ≃+* endFq W L`, `card_units_endFq`: `#Aut_{F_q}(E) = #Rˣ`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateG
import Definitions.Def_RPLib_S3_DWSTateQ6

/-!
# S3-DWS-Tate, part H: ideal classes ↔ quotient curves (b9 assembly, injectivity half)

`R = QuadraticAlgebra ℤ a b` (`D = b² + 4a < 0`) acting on `E` by an `R`-structure `s : OAct R W L`.
* `GoodIdeal F I`: `I I' = (N)` with `p ∤ N`; `picMk hD hI` its class in `PicQ hD`.
* `exists_good_rep`: every ideal class has a good representative (`p ∤ f.a` for a form ideal `I_f`).
* `exists_principal_of_rel`: `[I] = [J]` (good) ⇒ `(N_J) I = (γ) J` with `γ γ̄ = M`, `p ∤ M`.
* `QuotClass hD s c W₁`: `W₁` is a Vélu quotient `E → E/E[I]` for a good `I` of class `c`.
* **`exists_quotClass`** (every class is realised), **`isoFq_iff_of_quotClass`** (`E/E[I] ≅ E/E[J]` ⇔ `[I] = [J]`),
  `quotClass_of_isoFq` (the realised set is closed under `≅`).
* `endFqEquiv s : R ≃+* endFq W L`, `card_units_endFq`: `#Aut_{F_q}(E) = #Rˣ`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse QuadraticAlgebra RamanujanPetersson.Hurwitz

section GoodDef

variable (F : Type*) [Field F] {a b : ℤ}

/-- `I` has a prime-to-`p` multiple of an inverse: `I I' = (N)` with `N ≠ 0` in `F`. -/
def GoodIdeal (I : Ideal (QuadraticAlgebra ℤ a b)) : Prop :=
  ∃ I' : Ideal (QuadraticAlgebra ℤ a b), ∃ N : ℕ,
    I * I' = Ideal.span {(N : QuadraticAlgebra ℤ a b)} ∧ (N : F) ≠ 0

variable {F}

theorem natCast_ne_zero_QA {N : ℕ} (hN : (N : F) ≠ 0) : (N : QuadraticAlgebra ℤ a b) ≠ 0 := by
  have hN0 : (N : ℤ) ≠ 0 := by
    intro h0
    apply hN
    have : N = 0 := by exact_mod_cast h0
    rw [this, Nat.cast_zero]
  have := QA.intCast_ne_zero' (a := a) (b := b) hN0
  rwa [Int.cast_natCast] at this

theorem GoodIdeal.inv {I : Ideal (QuadraticAlgebra ℤ a b)} (hI : GoodIdeal F I) :
    ∃ J : Ideal (QuadraticAlgebra ℤ a b), ∃ ν, ν ≠ 0 ∧ I * J = Ideal.span {ν} := by
  obtain ⟨I', N, h, hN⟩ := hI
  exact ⟨I', _, natCast_ne_zero_QA hN, h⟩

/-- The ideal class of a good ideal. -/
def picMk (hD : b ^ 2 + 4 * a < 0) {I : Ideal (QuadraticAlgebra ℤ a b)} (hI : GoodIdeal F I) : QA.PicQ hD :=
  Quotient.mk (QA.picSetoid hD) ⟨I, hI.inv⟩

theorem picMk_eq_iff (hD : b ^ 2 + 4 * a < 0) {I J : Ideal (QuadraticAlgebra ℤ a b)} (hI : GoodIdeal F I)
    (hJ : GoodIdeal F J) : picMk hD hI = picMk hD hJ ↔ QA.IdealRel I J :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

end GoodDef

section GoodRep

variable {F : Type*} [Field F] [Fintype F] {a b : ℤ}

/-- Every ideal class contains a good ideal (a form ideal `I_f` with `p ∤ f.a`). -/
theorem exists_good_rep (hD : b ^ 2 + 4 * a < 0) (c : QA.PicQ hD) :
    ∃ I : Ideal (QuadraticAlgebra ℤ a b), ∃ hI : GoodIdeal F I, picMk hD hI = c := by
  refine Quotient.inductionOn c (fun I₀ => ?_)
  obtain ⟨J, ν, hν, hIJ⟩ := I₀.2
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  obtain ⟨f, hf, hpa, hrel, hmul⟩ := QA.exists_formIdeal_rel_not_dvd hD hν hIJ hp
  have ha0 : 0 ≤ f.a := le_of_lt hf.2.1.1
  have hN : ((f.a.toNat : ℕ) : F) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff F (ringChar F)] at h0
    apply hpa
    have : ((ringChar F : ℕ) : ℤ) ∣ ((f.a.toNat : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h0
    rwa [Int.toNat_of_nonneg ha0] at this
  have hcast : ((f.a.toNat : ℕ) : QuadraticAlgebra ℤ a b) = (f.a : QuadraticAlgebra ℤ a b) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg ha0]
  have hgood : GoodIdeal F (QA.formIdeal f : Ideal (QuadraticAlgebra ℤ a b)) :=
    ⟨_, f.a.toNat, by rw [hcast]; exact hmul, hN⟩
  exact ⟨_, hgood, Quotient.sound hrel.symm⟩

/-- `[I] = [J]` for good `I`, `J` ⇒ `(N_J) I = (γ) J` with `γ γ̄ = M`, `p ∤ M`. -/
theorem exists_principal_of_rel (hD : b ^ 2 + 4 * a < 0) {I I' J J' : Ideal (QuadraticAlgebra ℤ a b)}
    {NI NJ : ℕ} (hI : I * I' = Ideal.span {(NI : QuadraticAlgebra ℤ a b)}) (hNI : (NI : F) ≠ 0)
    (hJ : J * J' = Ideal.span {(NJ : QuadraticAlgebra ℤ a b)}) (hNJ : (NJ : F) ≠ 0) (hrel : QA.IdealRel I J) :
    ∃ γ : QuadraticAlgebra ℤ a b, Ideal.span {(NJ : QuadraticAlgebra ℤ a b)} * I = Ideal.span {γ} * J ∧
      ∃ M : ℕ, γ * star γ = M ∧ (M : F) ≠ 0 := by
  have := QA.isDomain hD
  obtain ⟨α, β, hα, -, h⟩ := hrel
  have h2 : Ideal.span {α} * (I * J') = Ideal.span {β * NJ} := by
    rw [← mul_assoc, h, mul_assoc, hJ, Ideal.span_singleton_mul_span_singleton]
  have hmem : β * NJ ∈ Ideal.span {α} * (I * J') := by
    rw [h2]; exact Ideal.mem_span_singleton_self _
  obtain ⟨γ, -, hγ⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have hIJ' : I * J' = Ideal.span {γ} := by
    rw [← Ideal.span_singleton_mul_right_inj hα, h2, Ideal.span_singleton_mul_span_singleton, hγ]
  refine ⟨γ, ?_, ?_⟩
  · rw [← hIJ', mul_assoc, mul_comm J' J, hJ, mul_comm]
  · have hNIm : (NI : QuadraticAlgebra ℤ a b) ∈ I := natCast_mem_of_mul_eq hI
    have hNJm : (NJ : QuadraticAlgebra ℤ a b) ∈ J' := natCast_mem_of_mul_eq (by rw [mul_comm]; exact hJ)
    have hm : (NI : QuadraticAlgebra ℤ a b) * NJ ∈ Ideal.span {γ} := by
      rw [← hIJ']; exact Ideal.mul_mem_mul hNIm hNJm
    obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.mp hm
    have hnorm : QuadraticAlgebra.norm δ * QuadraticAlgebra.norm γ = ((NI * NJ : ℕ) : ℤ) ^ 2 := by
      rw [← map_mul, hδ, ← Nat.cast_mul, QuadraticAlgebra.norm_natCast]
    have h0 : 0 ≤ QuadraticAlgebra.norm γ := QA.norm_nonneg hD γ
    refine ⟨(QuadraticAlgebra.norm γ).toNat, ?_, ?_⟩
    · rw [QA.mul_star_eq_norm, ← Int.cast_natCast, Int.toNat_of_nonneg h0]
    · intro hM
      have hF := congrArg (fun z : ℤ => (z : F)) hnorm
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_mul] at hF
      have hγF : ((QuadraticAlgebra.norm γ : ℤ) : F) = 0 := by
        rw [← Int.toNat_of_nonneg h0, Int.cast_natCast]; exact hM
      rw [hγF, mul_zero] at hF
      exact mul_ne_zero (pow_ne_zero 2 hNI) (pow_ne_zero 2 hNJ) (by rw [← mul_pow]; exact hF.symm)

end GoodRep

section Quot

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W W₁ W₂ : WeierstrassCurve F} [W.IsElliptic] [W₁.IsElliptic] [W₂.IsElliptic] {a b : ℤ}

/-- A Vélu quotient composed with an `F_q`-isomorphism is again a quotient by the same kernel. -/
theorem IsQuot.comp_iso {G : AddSubgroup (Pt W L)} {φ : Pt W L →+ Pt W₁ L} {ψ : Pt W₁ L →+ Pt W L} {n : ℕ}
    (hq : IsQuot G φ ψ n) {u : Pt W₁ L →+ Pt W₂ L} {v : Pt W₂ L →+ Pt W₁ L} (hu : IsIsog u) (hv : IsIsog v)
    (hvu : ∀ P, v (u P) = P) (huv : ∀ Q, u (v Q) = Q)
    (huf : ∀ P, u (RPLib.EllFq.frob W₁ L P) = RPLib.EllFq.frob W₂ L (u P)) :
    IsQuot G (u.comp φ) (ψ.comp v) n where
  hn := hq.hn
  isog := hu.comp hq.isog
  isogψ := hq.isogψ.comp hv
  ker S := by
    show u (φ S) = 0 ↔ S ∈ G
    rw [← hq.ker S]
    constructor
    · intro h; rw [← hvu (φ S), h, map_zero]
    · intro h; rw [h, map_zero]
  surj Q := by
    obtain ⟨P, hP⟩ := hq.surj (v Q)
    exact ⟨P, by show u (φ P) = Q; rw [hP, huv]⟩
  dual1 P := by
    show ψ (v (u (φ P))) = n • P
    rw [hvu, hq.dual1]
  dual2 Q := by
    show u (φ (ψ (v Q))) = n • Q
    rw [hq.dual2, map_nsmul, huv]
  frob P := by
    show u (φ (RPLib.EllFq.frob W L P)) = RPLib.EllFq.frob W₂ L (u (φ P))
    rw [hq.frob, huf]
  frobψ Q := by
    show ψ (v (RPLib.EllFq.frob W₂ L Q)) = RPLib.EllFq.frob W L (ψ (v Q))
    rw [frob_inv hvu huv huf, hq.frobψ]

variable (W₁) in
/-- `W₁` is a Vélu quotient `E → E/E[I]` (with dual) by the kernel of a good ideal `I` of class `c`. -/
def QuotClass (hD : b ^ 2 + 4 * a < 0) (s : OAct (QuadraticAlgebra ℤ a b) W L) (c : QA.PicQ hD) : Prop :=
  ∃ I : Ideal (QuadraticAlgebra ℤ a b), ∃ hI : GoodIdeal F I, picMk hD hI = c ∧
    ∃ φ : Pt W L →+ Pt W₁ L, ∃ ψ : Pt W₁ L →+ Pt W L, ∃ n : ℕ, IsQuot (kerI s I) φ ψ n

/-- **(b9) every ideal class is realised by a quotient curve.** -/
theorem exists_quotClass (hD : b ^ 2 + 4 * a < 0) (s : OAct (QuadraticAlgebra ℤ a b) W L) (c : QA.PicQ hD) :
    ∃ W₁ : WeierstrassCurve F, ∃ _ : W₁.IsElliptic, QuotClass W₁ hD s c := by
  obtain ⟨I, hI, hc⟩ := exists_good_rep (F := F) hD c
  obtain ⟨I', N, hII', hN⟩ := id hI
  obtain ⟨W₁, hE, φ, ψ, hq⟩ := exists_quotI (s := s) (natCast_mem_of_mul_eq hII') hN
  exact ⟨W₁, hE, I, hI, hc, φ, ψ, _, hq⟩

/-- The realised set is closed under `F_q`-isomorphism. -/
theorem quotClass_of_isoFq (hD : b ^ 2 + 4 * a < 0) {s : OAct (QuadraticAlgebra ℤ a b) W L} {c : QA.PicQ hD}
    (h : QuotClass W₁ hD s c) (hiso : IsoFq W₁ W₂ L) : QuotClass W₂ hD s c := by
  obtain ⟨I, hI, hc, φ, ψ, n, hq⟩ := h
  obtain ⟨u, v, hu, hv, hvu, huv, huf⟩ := hiso
  exact ⟨I, hI, hc, _, _, n, hq.comp_iso hu hv hvu huv huf⟩

/-- **(b9) the class of a quotient curve is well defined and determines it up to `F_q`-isomorphism.** -/
theorem isoFq_iff_of_quotClass (hD : b ^ 2 + 4 * a < 0) {s : OAct (QuadraticAlgebra ℤ a b) W L}
    {c c' : QA.PicQ hD} (h₁ : QuotClass W₁ hD s c) (h₂ : QuotClass W₂ hD s c') :
    IsoFq W₁ W₂ L ↔ c = c' := by
  have := QA.isDomain hD
  obtain ⟨I, hI, rfl, φ, ψ, n, hq₁⟩ := h₁
  obtain ⟨J, hJ, rfl, φ₂, ψ₂, n₂, hq₂⟩ := h₂
  rw [picMk_eq_iff]
  obtain ⟨I', NI, hII', hNI⟩ := id hI
  obtain ⟨J', NJ, hJJ', hNJ⟩ := id hJ
  constructor
  · intro hiso
    obtain ⟨c, hc0, hc⟩ := span_mul_eq_of_isoFq s hII' hNI hJJ' hNJ hq₁ hq₂ hiso
    exact QA.IdealRel.symm ⟨c, (n₂ : QuadraticAlgebra ℤ a b), hc0, s.natCast_ne_zero hq₂.hn, hc⟩
  · intro hrel
    obtain ⟨γ, hγ, M, hM, hMF⟩ := exists_principal_of_rel hD hII' hNI hJJ' hNJ hrel
    have hNJ2 : (NJ : QuadraticAlgebra ℤ a b) * NJ = ((NJ * NJ : ℕ) : QuadraticAlgebra ℤ a b) := by
      rw [Nat.cast_mul]
    have hNJF : ((NJ * NJ : ℕ) : F) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hNJ hNJ
    exact isoFq_of_span_mul_eq s hq₁ hq₂ hNJ2 hNJF hM hMF hγ

/-- The `R`-structure identifies `R` with `End_{F_q}(E)`. -/
noncomputable def endFqEquiv (s : OAct (QuadraticAlgebra ℤ a b) W L) :
    QuadraticAlgebra ℤ a b ≃+* endFq W L :=
  RingEquiv.ofBijective (s.ι.codRestrict (endFq W L) s.mem)
    ⟨fun x y h => s.inj (congrArg Subtype.val h), fun γ => by
      obtain ⟨x, hx⟩ := s.surj γ.1 γ.2
      exact ⟨x, Subtype.ext hx⟩⟩

/-- **`#Aut_{F_q}(E) = #Rˣ`** (automorphisms = units of `End_{F_q}(E)`). -/
theorem card_units_endFq (s : OAct (QuadraticAlgebra ℤ a b) W L) :
    Nat.card (endFq W L)ˣ = Nat.card (QuadraticAlgebra ℤ a b)ˣ :=
  (Nat.card_congr (Units.mapEquiv (endFqEquiv s).toMulEquiv).toEquiv).symm

end Quot

end RPLib.DWS


