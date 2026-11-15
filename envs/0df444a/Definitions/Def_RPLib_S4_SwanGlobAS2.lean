-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobAS2
-- name    : RPLib_S4_SwanGlobAS2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:49:33.760058+00:00
-- url     : https://prove2.me/theorems/be2cc8d7-bed1-47aa-8d84-747dd8c217fd
-- title:
--   Artin-Schreier covers at infinity: one jump at $\deg f$ and $\mathrm{Sw}_\infty = N \dim$
-- statement:
--   Let $C$ be a Galois cover of $\mathbb{F}_q(x)$ with field $L$ containing $y$ with $$y^q = y - f, \qquad f \ne 0,\ \deg f = N \ge 1,\ p \nmid N,$$ such that only the identity fixes $y$. The file proves that at every place $P$ over infinity the inertia group is all of $G$, the ramification function is $i(\sigma) = N + 1$ for $\sigma \ne 1$, and for every representation $\rho$ of $G$ $$\mathrm{Sw}_P(\rho) = N \cdot \operatorname{cod}(V^G),$$ so every nontrivial character of $G$ has all breaks $N$ at infinity.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1 (p. 13); H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.7 (Artin-Schreier extensions)

import Mathlib
import Definitions.Def_RPLib_S4_SwanGlobAS1
import Definitions.Def_RPLib_S4_ArtinSchreierField
import Definitions.Def_RPLib_S4_SwanAS

/-!
# S4-Swan (K2), part 23: Artin-Schreier covers at `∞`

For a Galois cover `C` whose function field `L` is generated over `Fq(X)` by `y` with `y^q = y - f`,
`deg f = N ≥ 1`, `p ∤ N`, and a place `P` of `L` over `∞`: every `σ` moves `y` by a constant of `Fq`, so
`|G| ≤ q`; the valuation `v_P(y^q) = v_P(f) = -e N` forces `q ∣ e`, hence the inertia group at `P` is all of
`G` (`e = |G| = q`) and `v_P(y) = -N`; with `q m = 1 + N b` the element `π^m y^b` is a uniformizer and
`LocData.ramFn_i_of_as` gives one ramification jump at `N` (`infRamFn_constI_as`). Headlines:
`swanInf_as` (`Sw_∞(ρ) = N · codim V^G`) and `chiAllBrk_as` (a nontrivial character has all breaks `N`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open IsDedekindDomain

namespace RamanujanPetersson

namespace GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

/-- Frobenius is additive in an `Fq`-algebra. -/
theorem sub_pow_card_Fq (Fq : Type) [Field Fq] [Fintype Fq] {R : Type*} [CommRing R] [Algebra Fq R]
    (a b : R) : (a - b) ^ Fintype.card Fq = a ^ Fintype.card Fq - b ^ Fintype.card Fq := by
  have hF : ∀ x : R, FiniteField.frobeniusAlgHom Fq R x = x ^ Fintype.card Fq := fun _ => rfl
  rw [← hF, map_sub, hF, hF]

/-- Bezout for coprime `N, q`: `q m = 1 + N b`. -/
theorem exists_bezout {N q : ℕ} (hcop : Nat.Coprime N q) (hq : 1 < q) :
    ∃ b m : ℕ, q * m = 1 + N * b := by
  obtain ⟨t, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hq
  have hd := Nat.div_add_mod (N * t) q
  rw [ht.2] at hd
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  generalize N * t / (r + 1) = k at hd
  refine ⟨r * t, r * k + 1, ?_⟩
  have h2 : N * (r * t) = r * (N * t) := by ring
  rw [h2, ← hd]; ring

section ASVal

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]
variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L] [Fintype Fq]

attribute [local instance] infChartAction infChart_isGaloisGroup

/-- `v_P(x) = e_P · v_∞(x) = -e_P deg x` for `x ∈ Fq(X)` and a place `P` over `∞`. -/
theorem infVal_eq (P : HeightOneSpectrum (infChart Fq L)) {x : RatFunc Fq} (hx : x ≠ 0) :
    Swan.adicAdd P (algebraMap (RatFunc Fq) L x) =
      (((Nat.card (P.asIdeal.inertia C.G) : ℤ) * -x.intDegree : ℤ) : WithTop ℤ) :=
  Swan.adicAdd_algebraMap_eq (A := Places.Oinf Fq) C.G P x (-x.intDegree)
    (Swan.adicAdd_inf_eq (P.under (Places.Oinf Fq)) hx)

/-- The cover group fixes `Fq(X)`. -/
theorem smul_algebraMap_K (σ : C.G) (x : RatFunc Fq) :
    σ • algebraMap (RatFunc Fq) L x = algebraMap (RatFunc Fq) L x := by
  have := C.isGaloisGroup_frac (RatFunc Fq) L
  have : SMulCommClass C.G (RatFunc Fq) L := IsGaloisGroup.commutes
  exact smul_algebraMap σ x

variable {C Fq L}

/-- Each `σ` moves an Artin-Schreier root by a constant: `σ y = y + c`, `c ∈ Fq`. -/
theorem exists_smul_sub {y : L} {f : RatFunc Fq}
    (hy : y ^ Fintype.card Fq = y - algebraMap (RatFunc Fq) L f) (σ : C.G) :
    ∃ c : Fq, σ • y = y + algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) c) := by
  let : Algebra Fq L := ((algebraMap (RatFunc Fq) L).comp (algebraMap Fq (RatFunc Fq))).toAlgebra
  have hz : (σ • y - y) ^ Fintype.card Fq = σ • y - y := by
    rw [sub_pow_card_Fq Fq, ← smul_pow', hy, smul_sub, smul_algebraMap_K C Fq L σ f]; ring
  obtain ⟨c, hc⟩ := ArtinSchreier.exists_algebraMap_eq_of_pow_card Fq hz
  have hc' : algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) c) = σ • y - y := hc
  exact ⟨c, by rw [hc']; ring⟩

/-- `σ ↦ σ y - y` is injective when `y` generates, so `|G| ≤ q`. -/
theorem card_le_of_as {y : L} {f : RatFunc Fq}
    (hy : y ^ Fintype.card Fq = y - algebraMap (RatFunc Fq) L f)
    (hgen : ∀ σ : C.G, σ • y = y → σ = 1) : Nat.card C.G ≤ Fintype.card Fq := by
  choose c hc using exists_smul_sub (C := C) hy
  have hinj : Function.Injective c := by
    intro σ τ h
    have h1 : σ • y = τ • y := by rw [hc σ, hc τ, h]
    have h2 : (τ⁻¹ * σ) • y = y := by rw [mul_smul, h1, inv_smul_smul]
    exact (inv_mul_eq_one.1 (hgen _ h2)).symm
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective c hinj

variable (C Fq L)

/-- **Total ramification at `∞`**: `e_P = |G| = q` and `v_P(y) = -N`. -/
theorem as_inertia_val (P : HeightOneSpectrum (infChart Fq L)) {y : L} {f : RatFunc Fq} {N : ℕ}
    (hy : y ^ Fintype.card Fq = y - algebraMap (RatFunc Fq) L f) (hf0 : f ≠ 0)
    (hfN : f.intDegree = N) (hN : 1 ≤ N) (hcop : Nat.Coprime N (Fintype.card Fq))
    (hgen : ∀ σ : C.G, σ • y = y → σ = 1) :
    Nat.card (P.asIdeal.inertia C.G) = Fintype.card Fq ∧ Nat.card C.G = Fintype.card Fq ∧
      Swan.adicAdd P y = ((-(N : ℤ) : ℤ) : WithTop ℤ) := by
  have hq : 1 < Fintype.card Fq := Fintype.one_lt_card
  have he1 : 1 ≤ Nat.card (P.asIdeal.inertia C.G) := Nat.card_pos
  have heG : Nat.card (P.asIdeal.inertia C.G) ≤ Nat.card C.G := Subgroup.card_le_card_group _
  have hGq := card_le_of_as (C := C) hy hgen
  have hF := infVal_eq C Fq L P hf0
  rw [hfN] at hF
  have hyF : algebraMap (RatFunc Fq) L f = y - y ^ Fintype.card Fq := by rw [hy]; ring
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), sub_zero, map_eq_zero_iff _ (algebraMap (RatFunc Fq) L).injective] at hyF
    exact hf0 hyF
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff (Swan.adicAdd P)).2 hy0)
  have hpow : Swan.adicAdd P (y ^ Fintype.card Fq) = ((Fintype.card Fq * m : ℤ) : WithTop ℤ) := by
    rw [AddValuation.map_pow, ← hm, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have heN : (1 : ℤ) ≤ (Nat.card (P.asIdeal.inertia C.G) : ℤ) * N := by
    have h1 : (1 : ℤ) ≤ Nat.card (P.asIdeal.inertia C.G) := by exact_mod_cast he1
    have h2 : (1 : ℤ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hq' : (2 : ℤ) ≤ Fintype.card Fq := by exact_mod_cast hq
  have hm0 : m < 0 := by
    have hmin := AddValuation.map_sub (Swan.adicAdd P) y (y ^ Fintype.card Fq)
    rw [← hyF, hF, ← hm, hpow, ← WithTop.coe_min, WithTop.coe_le_coe] at hmin
    by_contra h
    have h := not_lt.1 h
    rcases min_le_iff.1 hmin with h' | h' <;> nlinarith
  have hlt : Swan.adicAdd P (-(y ^ Fintype.card Fq)) < Swan.adicAdd P y := by
    rw [AddValuation.map_neg, hpow, ← hm, WithTop.coe_lt_coe]; nlinarith
  have heq := hF
  rw [hyF, sub_eq_neg_add, AddValuation.map_add_eq_of_lt_left _ hlt, AddValuation.map_neg, hpow,
    WithTop.coe_eq_coe] at heq
  have hdvd : Fintype.card Fq ∣ Nat.card (P.asIdeal.inertia C.G) * N := by
    have : ((Fintype.card Fq : ℕ) : ℤ) ∣ ((Nat.card (P.asIdeal.inertia C.G) * N : ℕ) : ℤ) :=
      ⟨-m, by push_cast; linear_combination heq⟩
    exact Int.natCast_dvd_natCast.1 this
  have hqe : Fintype.card Fq ∣ Nat.card (P.asIdeal.inertia C.G) :=
    (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right hdvd
  have he : Nat.card (P.asIdeal.inertia C.G) = Fintype.card Fq :=
    le_antisymm (heG.trans hGq) (Nat.le_of_dvd (by omega) hqe)
  refine ⟨he, le_antisymm hGq (he ▸ heG), ?_⟩
  rw [he] at heq
  have hq0 : ((Fintype.card Fq : ℕ) : ℤ) ≠ 0 := by omega
  rw [← hm, mul_left_cancel₀ hq0 heq]

include C in
/-- Nonzero constants have valuation `0` at `P`. -/
theorem infVal_const (P : HeightOneSpectrum (infChart Fq L)) {c : Fq} (hc : c ≠ 0) :
    Swan.adicAdd P (algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) c)) = 0 := by
  have h0 : algebraMap Fq (RatFunc Fq) c ≠ 0 := (map_ne_zero _).2 hc
  rw [infVal_eq C Fq L P h0,
    show (algebraMap Fq (RatFunc Fq) c).intDegree = 0 from RatFunc.intDegree_C c]
  simp

/-- **One ramification jump at `N`** for an Artin-Schreier cover at `∞`. -/
theorem infRamFn_constI_as (P : HeightOneSpectrum (infChart Fq L)) {y : L} {f : RatFunc Fq} {N : ℕ}
    (hy : y ^ Fintype.card Fq = y - algebraMap (RatFunc Fq) L f) (hf0 : f ≠ 0)
    (hfN : f.intDegree = N) (hN : 1 ≤ N) (hcop : Nat.Coprime N (Fintype.card Fq))
    (hgen : ∀ σ : C.G, σ • y = y → σ = 1) : (C.infRamFn Fq L P).ConstI N := by
  obtain ⟨he, -, hyv⟩ := as_inertia_val C Fq L P hy hf0 hfN hN hcop hgen
  obtain ⟨b, m, hbm⟩ := exists_bezout hcop Fintype.one_lt_card
  have hbF : (b : Fq) ≠ 0 := by
    intro h0
    have h1 := congrArg (Nat.cast : ℕ → Fq) hbm
    push_cast at h1
    rw [FiniteField.cast_card_eq_zero, h0] at h1
    simp at h1
  have hb : Swan.adicAdd P (b : L) = 0 := by
    have : (b : L) = algebraMap (RatFunc Fq) L (algebraMap Fq (RatFunc Fq) (b : Fq)) := by simp
    rw [this]; exact infVal_const C Fq L P hbF
  have hxv : Swan.adicAdd P (algebraMap (RatFunc Fq) L
      (algebraMap (Places.Oinf Fq) (RatFunc Fq) (Places.piInf Fq) ^ m)) =
      ((Nat.card (P.asIdeal.inertia C.G) * m : ℤ) : WithTop ℤ) :=
    Swan.adicAdd_algebraMap_eq (A := Places.Oinf Fq) C.G P _ (m : ℤ)
      (by rw [AddValuation.map_pow, Swan.adicAdd_piInf]; simp)
  have hϖ : Swan.adicAdd P (algebraMap (RatFunc Fq) L
      (algebraMap (Places.Oinf Fq) (RatFunc Fq) (Places.piInf Fq) ^ m) * y ^ b) = 1 := by
    rw [AddValuation.map_mul, hxv, AddValuation.map_pow, hyv, he, ← WithTop.coe_nsmul,
      ← WithTop.coe_add, ← WithTop.coe_one, WithTop.coe_eq_coe, nsmul_eq_mul]
    have h1 : ((Fintype.card Fq * m : ℕ) : ℤ) = ((1 + N * b : ℕ) : ℤ) := by rw [hbm]
    push_cast at h1
    linear_combination h1
  have hD : (C.infLocData Fq L P).v = Swan.adicAdd P := rfl
  intro σ hσ
  obtain ⟨c, hc⟩ := exists_smul_sub (C := C) hy (σ : C.G)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero, add_zero] at hc
    exact hσ (Subtype.ext (hgen _ hc))
  exact (C.infLocData Fq L P).ramFn_i_of_as hN (smul_algebraMap_K C Fq L (σ : C.G) _) hc
    (by rw [hD]; exact infVal_const C Fq L P hc0) (by rw [hD]; exact hyv) (by rw [hD]; exact hb)
    (by rw [hD]; exact hϖ)

/-- The inertia group at `∞` of an Artin-Schreier cover is the whole cover group. -/
theorem infInertia_eq_top_as (P : HeightOneSpectrum (infChart Fq L)) {y : L} {f : RatFunc Fq} {N : ℕ}
    (hy : y ^ Fintype.card Fq = y - algebraMap (RatFunc Fq) L f) (hf0 : f ≠ 0)
    (hfN : f.intDegree = N) (hN : 1 ≤ N) (hcop : Nat.Coprime N (Fintype.card Fq))
    (hgen : ∀ σ : C.G, σ • y = y → σ = 1) : C.infInertia Fq L P.asIdeal = ⊤ := by
  obtain ⟨he, hG, -⟩ := as_inertia_val C Fq L P hy hf0 hfN hN hcop hgen
  exact Subgroup.eq_top_of_card_eq _ (he.trans hG.symm)

/-- **Swan conductor of an Artin-Schreier cover at `∞`**: `Sw_P(ρ) = N · codim V^G`
(`= N` for a nontrivial character, e.g. `L_ψ(f)`). -/
theorem swanInf_as {k V : Type} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k C.G V)
    (P : HeightOneSpectrum (infChart Fq L)) {y : L} {f : RatFunc Fq} {N : ℕ}
    (hy : y ^ Fintype.card Fq = y - algebraMap (RatFunc Fq) L f) (hf0 : f ≠ 0)
    (hfN : f.intDegree = N) (hN : 1 ≤ N) (hcop : Nat.Coprime N (Fintype.card Fq))
    (hgen : ∀ σ : C.G, σ • y = y → σ = 1) : C.swanInf Fq L ρ P = N * Swan.cod ρ ⊤ := by
  rw [swanInf, (infRamFn_constI_as C Fq L P hy hf0 hfN hN hcop hgen).swan, Swan.cod_comp,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, infInertia_eq_top_as C Fq L P hy hf0 hfN hN hcop hgen]

/-- **All breaks `N`**: a character of the cover group that is nontrivial has all breaks `N` at `∞`. -/
theorem chiAllBrk_as {k : Type} [Field k] (χ : C.G →* kˣ) (hχ : ∃ σ, χ σ ≠ 1)
    (P : HeightOneSpectrum (infChart Fq L)) {y : L} {f : RatFunc Fq} {N : ℕ}
    (hy : y ^ Fintype.card Fq = y - algebraMap (RatFunc Fq) L f) (hf0 : f ≠ 0)
    (hfN : f.intDegree = N) (hN : 1 ≤ N) (hcop : Nat.Coprime N (Fintype.card Fq))
    (hgen : ∀ σ : C.G, σ • y = y → σ = 1) :
    (C.infRamFn Fq L P).ChiAllBrk (χ.comp (C.infInertia Fq L P.asIdeal).subtype) N := by
  apply (infRamFn_constI_as C Fq L P hy hf0 hfN hN hcop hgen).chiAllBrk
  obtain ⟨σ, hσ⟩ := hχ
  have hI : σ ∈ C.infInertia Fq L P.asIdeal := by
    rw [infInertia_eq_top_as C Fq L P hy hf0 hfN hN hcop hgen]; exact Subgroup.mem_top σ
  exact ⟨⟨σ, hI⟩, hσ⟩

end ASVal

end GalCover

end RamanujanPetersson


