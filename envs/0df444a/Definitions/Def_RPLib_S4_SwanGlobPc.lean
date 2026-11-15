-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobPc
-- name    : RPLib_S4_SwanGlobPc
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:42:33.846229+00:00
-- url     : https://prove2.me/theorems/42dfd2c3-09ec-4d29-bd95-591dfb5de638
-- title:
--   Swan conductors and breaks at infinity do not depend on the place over infinity
-- statement:
--   For a Galois cover of $\mathbb{F}_q(x)$ with group $G$, any two places $P, P'$ over infinity are conjugate, $P' = gP$, and conjugation by $g$ maps $I_P$ isomorphically onto $I_{P'}$ respecting ramification functions. The file proves this and that representations restricted along conjugation are equivalent, so that $$\mathrm{Sw}_{P'}(\rho) = \mathrm{Sw}_P(\rho)$$ and the breaks agree; hence $\mathrm{Sw}_\infty(\rho)$ and the breaks at infinity are well defined.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter I, Section 7; N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1

import Mathlib
import Definitions.Def_RPLib_S4_SwanGlobP

/-!
# S4-Swan (K2), part 20: Swan conductors and breaks at `∞` do not depend on the place

If `τ • P = P'` for two height-one primes of a Dedekind domain with a Galois action, then
`v_{P'}(τ x) = v_P(x)` (`adicAdd_smul_eq`), conjugation `σ ↦ τ⁻¹ σ τ` maps the inertia group of `P'` onto that
of `P` (`conjInertia`), and the two inertia local data form a `LocData.Tower` along `τ` with trivial kernel
(`conjTower`). Isomorphic representations have equal Swan conductors and breaks (`RamFn.swan_equiv`,
`RamFn.allBrk_equiv`), so the Swan conductor and breaks of `ρ` restricted to inertia agree at `P` and `P'`.
At `∞` the base `O_∞` is local, so the cover group acts transitively on the places over `∞`
(`GalCover.exists_smul_inf`), giving `GalCover.swanInf_eq` and `GalCover.allBrkInf_eq`.
-/

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped Pointwise

namespace RamanujanPetersson

namespace Swan

section AdicConj

variable {S : Type*} [CommRing S] [IsDedekindDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
include hc

/-- The Galois action transports valuations: `v_{τP}(τ x) = v_P(x)`. -/
theorem adicAdd_smul_eq (τ : G) {P P' : HeightOneSpectrum S} (h : τ • P.asIdeal = P'.asIdeal) (x : L) :
    adicAdd P' (τ • x) = adicAdd P x := by
  have hpow : ∀ n : ℕ, τ • (P.asIdeal ^ n) = P'.asIdeal ^ n := fun n => by
    rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def, h]
  have hint : ∀ r : S, adicAdd P' (algebraMap S L (τ • r)) = adicAdd P (algebraMap S L r) := by
    intro r
    refine withTop_eq_of_natCast_le_iff (adicAdd_algebraMap_nonneg P' _)
      (adicAdd_algebraMap_nonneg P _) (fun n => ?_)
    rw [natCast_le_adicAdd_algebraMap_iff, natCast_le_adicAdd_algebraMap_iff, ← hpow n]
    exact Ideal.smul_mem_pointwise_smul_iff
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  rw [smul_div₀', hc, hc, AddValuation.map_div, AddValuation.map_div, hint, hint]

end AdicConj

section ConjInertia

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]

theorem conj_mem_inertia (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') {σ : G} (hσ : σ ∈ Q'.inertia G) :
    τ⁻¹ * σ * τ ∈ Q.inertia G := by
  rw [Ideal.inertia, AddSubgroup.mem_inertia] at hσ ⊢
  intro x
  have hx : σ • τ • x - τ • x ∈ τ • Q := by rw [h]; exact hσ (τ • x)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul] at hx
  rw [mul_smul, mul_smul]
  exact hx

/-- Conjugation `σ ↦ τ⁻¹ σ τ` from the inertia group of `τ • Q` to the inertia group of `Q`. -/
def conjInertia (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') : Q'.inertia G →* Q.inertia G where
  toFun σ := ⟨τ⁻¹ * σ * τ, conj_mem_inertia τ h σ.2⟩
  map_one' := Subtype.ext (by show τ⁻¹ * 1 * τ = 1; group)
  map_mul' a b := Subtype.ext (by show τ⁻¹ * ((a : G) * b) * τ = (τ⁻¹ * a * τ) * (τ⁻¹ * b * τ); group)

theorem conjInertia_coe (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') (σ : Q'.inertia G) :
    (conjInertia τ h σ : G) = τ⁻¹ * σ * τ := rfl

theorem conjInertia_surjective (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') :
    Function.Surjective (conjInertia τ h) := by
  intro g
  have h' : τ⁻¹ • Q' = Q := by rw [← h, inv_smul_smul]
  have hm := conj_mem_inertia τ⁻¹ h' g.2
  rw [inv_inv] at hm
  exact ⟨⟨_, hm⟩, Subtype.ext (by show τ⁻¹ * (τ * (g : G) * τ⁻¹) * τ = g; group)⟩

theorem conjInertia_injective (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') :
    Function.Injective (conjInertia τ h) := by
  intro a b hab
  have : τ⁻¹ * (a : G) * τ = τ⁻¹ * b * τ := congrArg Subtype.val hab
  exact Subtype.ext (by simpa using this)

theorem card_ker_conjInertia (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') [Fintype (conjInertia τ h).ker] :
    Fintype.card (conjInertia τ h).ker = 1 := by
  rw [← Nat.card_eq_fintype_card, Subgroup.card_eq_one, MonoidHom.ker_eq_bot_iff]
  exact conjInertia_injective τ h

end ConjInertia

section ConjTower

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (τ : G) {P P' : HeightOneSpectrum S} (h : τ • P.asIdeal = P'.asIdeal)
  [Finite (S ⧸ P.asIdeal)] [Finite (S ⧸ P'.asIdeal)]

/-- The inertia local data at `P` and at `τ • P` form a tower along conjugation by `τ`. -/
theorem conjTower [Fintype (conjInertia τ h).ker] :
    LocData.Tower (inertiaLocData (R := R) hc P) (inertiaLocData (R := R) hc P')
      (MulSemiringAction.toRingHom G L τ) (conjInertia τ h) where
  surj := conjInertia_surjective τ h
  compat σ x := by
    show (σ : G) • τ • x = τ • ((τ⁻¹ * σ * τ) • x)
    rw [mul_smul, mul_smul, smul_inv_smul]
  v_iota x m hx := by
    rw [card_ker_conjInertia, Nat.cast_one, one_mul, ← hx]
    exact adicAdd_smul_eq hc τ h x
  val x _ hx0 := by
    rw [card_ker_conjInertia]
    exact ⟨-WithZero.log (P'.valuation L x), by rw [Nat.cast_one, one_mul]; exact negLogV_of_ne P' hx0⟩

end ConjTower

section RepEquiv

variable {G : Type*} [Group G] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (ρ₁ ρ₂ : Representation k G V) (e : V ≃ₗ[k] V) (he : ∀ g v, ρ₁ g (e v) = e (ρ₂ g v))
include he

theorem fixd_map_equiv (H : Subgroup G) : (fixd ρ₂ H).map (e : V →ₗ[k] V) = fixd ρ₁ H := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine (mem_fixd ρ₁).2 fun σ hσ => ?_
    rw [LinearEquiv.coe_coe, he, (mem_fixd ρ₂).1 hv σ hσ]
  · intro w hw
    refine Submodule.mem_map.2 ⟨e.symm w, (mem_fixd ρ₂).2 fun σ hσ => ?_, by simp⟩
    apply e.injective
    rw [← he, e.apply_symm_apply, (mem_fixd ρ₁).1 hw σ hσ]

theorem cod_equiv (H : Subgroup G) : cod ρ₁ H = cod ρ₂ H := by
  rw [cod, cod, ← fixd_map_equiv ρ₁ ρ₂ e he H, LinearEquiv.finrank_map_eq]

theorem fixd_eq_top_iff_equiv (H : Subgroup G) : fixd ρ₁ H = ⊤ ↔ fixd ρ₂ H = ⊤ := by
  have ht : (⊤ : Submodule k V).map (e : V →ₗ[k] V) = ⊤ := by rw [Submodule.map_top, LinearEquiv.range]
  rw [← fixd_map_equiv ρ₁ ρ₂ e he H]
  conv_lhs => rw [← ht]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

theorem fixd_eq_bot_iff_equiv (H : Subgroup G) : fixd ρ₁ H = ⊥ ↔ fixd ρ₂ H = ⊥ := by
  rw [← fixd_map_equiv ρ₁ ρ₂ e he H]
  conv_lhs => rw [← Submodule.map_bot (e : V →ₗ[k] V)]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff

namespace RamFn

variable (R : RamFn G)

/-- Isomorphic representations have the same Swan conductor. -/
theorem swan_equiv [Fintype G] : R.swan ρ₁ = R.swan ρ₂ := by
  unfold swan
  exact Finset.sum_congr rfl fun u _ => by rw [cod_equiv ρ₁ ρ₂ e he]

/-- Isomorphic representations have the same breaks. -/
theorem allBrk_equiv [Fintype G] (x : ℚ) : R.AllBrk ρ₁ x ↔ R.AllBrk ρ₂ x := by
  simp only [AllBrk, BrkLE, fixd_eq_top_iff_equiv ρ₁ ρ₂ e he, fixd_eq_bot_iff_equiv ρ₁ ρ₂ e he]

end RamFn

end RepEquiv

section ConjRep

variable {G : Type*} [Group G] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- `ρ τ` as a linear automorphism. -/
def repEquiv (τ : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinearMap (ρ τ) (ρ τ⁻¹) (LinearMap.ext fun v => ρ.self_inv_apply τ v)
    (LinearMap.ext fun v => ρ.inv_self_apply τ v)

variable {S : Type*} [CommRing S] [MulSemiringAction G S]

/-- `ρ` on the inertia of `τ • Q` is conjugate (by `ρ τ`) to `ρ` on the inertia of `Q` pulled back along
conjugation. -/
theorem conj_rep_intertwine (τ : G) {Q Q' : Ideal S} (h : τ • Q = Q') (g : Q'.inertia G) (v : V) :
    (ρ.comp (Q'.inertia G).subtype) g (repEquiv ρ τ v) =
      repEquiv ρ τ (((ρ.comp (Q.inertia G).subtype).comp (conjInertia τ h)) g v) := by
  show ρ (g : G) (ρ τ v) = ρ τ (ρ (τ⁻¹ * (g : G) * τ) v)
  rw [show (τ⁻¹ * (g : G) * τ : G) = τ⁻¹ * ((g : G) * τ) by group, map_mul, Module.End.mul_apply,
    ρ.self_inv_apply, map_mul, Module.End.mul_apply]

end ConjRep

section ConjSwan

variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S] {G : Type*}
  [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (τ : G) {P P' : HeightOneSpectrum S} (h : τ • P.asIdeal = P'.asIdeal)
  [Finite (S ⧸ P.asIdeal)] [Finite (S ⧸ P'.asIdeal)]
  [Fintype (P.asIdeal.inertia G)] [Fintype (P'.asIdeal.inertia G)]
  {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

include h in
/-- The Swan conductor of `ρ` at `P` equals the one at `τ • P`. -/
theorem swan_inertia_conj [FiniteDimensional k V] :
    (inertiaLocData (R := R) hc P').ramFn.swan (ρ.comp (P'.asIdeal.inertia G).subtype) =
      (inertiaLocData (R := R) hc P).ramFn.swan (ρ.comp (P.asIdeal.inertia G).subtype) := by
  classical
  have : Fintype (conjInertia τ h).ker := Fintype.ofFinite _
  rw [← (conjTower hc τ h).swan_comp]
  exact RamFn.swan_equiv _ _ (repEquiv ρ τ) (conj_rep_intertwine ρ τ h) _

include h in
/-- The breaks of `ρ` at `P` equal the ones at `τ • P`. -/
theorem allBrk_inertia_conj (x : ℚ) :
    (inertiaLocData (R := R) hc P').ramFn.AllBrk (ρ.comp (P'.asIdeal.inertia G).subtype) x ↔
      (inertiaLocData (R := R) hc P).ramFn.AllBrk (ρ.comp (P.asIdeal.inertia G).subtype) x := by
  classical
  have : Fintype (conjInertia τ h).ker := Fintype.ofFinite _
  rw [← (conjTower hc τ h).allBrk_iff]
  exact RamFn.allBrk_equiv _ _ (repEquiv ρ τ) (conj_rep_intertwine ρ τ h) _ x

end ConjSwan

end Swan

namespace GalCover

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

section Place

variable {A : Type} [CommRing A] [IsDomain A] (C : GalCover A)
variable (Fq : Type) [Field Fq] [DecidableEq (RatFunc Fq)] [Algebra A (RatFunc Fq)]
  [IsFractionRing A (RatFunc Fq)]
variable (L : Type) [Field L] [Algebra C.B L] [IsFractionRing C.B L] [Algebra (RatFunc Fq) L]
  [Algebra A L] [IsScalarTower A (RatFunc Fq) L] [IsScalarTower A C.B L] [MulSemiringAction C.G L]
  [SMulDistribClass C.G C.B L]
variable [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L] [Fintype Fq]

attribute [local instance] infChartAction infChart_isGaloisGroup

omit [FiniteDimensional (RatFunc Fq) L] [Algebra.IsSeparable (RatFunc Fq) L] [Fintype Fq] in
/-- The cover group acts transitively on the places over `∞` (`O_∞` is local). -/
theorem exists_smul_inf (P P' : HeightOneSpectrum (infChart Fq L)) :
    ∃ τ : C.G, τ • P.asIdeal = P'.asIdeal := by
  have : Algebra.IsInvariant (Places.Oinf Fq) (infChart Fq L) C.G := IsGaloisGroup.isInvariant
  have : SMulCommClass C.G (Places.Oinf Fq) (infChart Fq L) := IsGaloisGroup.commutes
  have : Algebra.IsIntegral (Places.Oinf Fq) (infChart Fq L) :=
    Algebra.IsInvariant.isIntegral (Places.Oinf Fq) (infChart Fq L) C.G
  have := P.isPrime.isMaximal P.ne_bot
  have := P'.isPrime.isMaximal P'.ne_bot
  have hu : P.asIdeal.under (Places.Oinf Fq) = P'.asIdeal.under (Places.Oinf Fq) := by
    rw [IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under (Places.Oinf Fq) P.asIdeal),
      IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under (Places.Oinf Fq) P'.asIdeal)]
  obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (A := Places.Oinf Fq)
    (B := infChart Fq L) (G := C.G) P.asIdeal P'.asIdeal hu
  exact ⟨τ, hτ.symm⟩

/-- **Place independence of the Swan conductor at `∞`.** -/
theorem swanInf_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k C.G V) (P P' : HeightOneSpectrum (infChart Fq L)) :
    C.swanInf Fq L ρ P = C.swanInf Fq L ρ P' := by
  obtain ⟨τ, h⟩ := exists_smul_inf C Fq L P P'
  let : Fintype (P.asIdeal.inertia C.G) := C.infInertia_fintype Fq L P
  let : Fintype (P'.asIdeal.inertia C.G) := C.infInertia_fintype Fq L P'
  have e := Swan.swan_inertia_conj (R := Places.Oinf Fq) (S := infChart Fq L) (G := C.G) (L := L)
    (fun _ _ => rfl) τ h ρ
  exact e.symm

/-- **Place independence of the breaks at `∞`.** -/
theorem allBrkInf_eq {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k C.G V) (P P' : HeightOneSpectrum (infChart Fq L)) (x : ℚ) :
    (C.infRamFn Fq L P).AllBrk (ρ.comp (C.infInertia Fq L P.asIdeal).subtype) x ↔
      (C.infRamFn Fq L P').AllBrk (ρ.comp (C.infInertia Fq L P'.asIdeal).subtype) x := by
  obtain ⟨τ, h⟩ := exists_smul_inf C Fq L P P'
  let : Fintype (P.asIdeal.inertia C.G) := C.infInertia_fintype Fq L P
  let : Fintype (P'.asIdeal.inertia C.G) := C.infInertia_fintype Fq L P'
  have e := Swan.allBrk_inertia_conj (R := Places.Oinf Fq) (S := infChart Fq L) (G := C.G) (L := L)
    (fun _ _ => rfl) τ h ρ x
  exact e.symm

end Place

end GalCover

end RamanujanPetersson


