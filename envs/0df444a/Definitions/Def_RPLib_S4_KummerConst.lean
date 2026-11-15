-- Prove2me | Definitions.Def_RPLib_S4_KummerConst
-- name    : RPLib_S4_KummerConst
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:10:15.444995+00:00
-- url     : https://prove2.me/theorems/4fda0c04-dc05-4ef5-8d40-81c3b7111c12
-- title:
--   Constant field extensions are unramified, and roots of unity in $K_U$
-- statement:
--   Let $K$ have characteristic $p$, $q = p^e$, and $A \to K$ any ring with an algebra map. The file proves that the constant level $K(\text{roots of } X^{p^k} - X)$ is a finite Galois subextension of $\overline{K}/K$ whose inertia groups at all primes of the integral closure of $A$ are trivial, so every constant of $\overline{K}$ lies in $K_U$, the maximal extension unramified over $A$. For $N$ prime to $p$ there is a primitive $N$-th root of unity $\zeta \in K_U$ which is a constant, fixed by the geometric fundamental group, with $\varphi(\zeta) = \zeta^q$ for an arithmetic Frobenius lift. Hence the curve form of Kummer theory $$H^1(U \otimes \overline{\mathbb{F}}_q, \mathbb{Z}/N) \cong \operatorname{rad}/(\text{fixed units}),$$ with $F[\kappa_\alpha] = q\,[\kappa_{\varphi^{-1}\alpha}]$ for the geometric Frobenius.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.6

import Mathlib
import Definitions.Def_RPLib_S4_KummerH1
import Definitions.Def_RPLib_S4_CurveCohCurve

/-!
# S4-Kummer, part 3: constants are unramified; `μ_N ⊆ K_U`; the curve form of Kummer theory

`K` of characteristic `p`, `q = p ^ e` (`e > 0`), `A` any ring with `K = Frac`-like algebra `A → K` (no hypothesis on
`A` is needed: constant extensions are unramified over every `A`).

* `constLevel K p k = K(roots of X^(p^k) - X)` is a finite Galois subextension of `K̄/K` with trivial inertia at every
  prime of the integral closure of `A` (`constLevel_mem_unramSet`): an inertia element `σ` moves a root `s` to a root,
  `σ s - s` is again a root (Frobenius is additive), hence `0` or a unit, and it lies in the prime;
* `mem_maxUnram_of_isConst`: every constant of `K̄` lies in `K_U = maxUnram A K`;
* `exists_zeta`: for `N` prime to `p` there is a primitive `N`-th root of unity `ζ ∈ K_U` which is a constant;
  `zeta_fixed`: `π₁^geo` fixes it; `frobLift_zeta`: an arithmetic Frobenius lift sends `ζ ↦ ζ ^ q`;
* `curveKummerEquiv`: `H¹(U ⊗ 𝔽̄, ZMod N) ≃ rad / (π₁^geo-fixed units)`, and `geomFrobH1_kclass`:
  `F [kchar α] = q • [kchar (φ⁻¹ α)]` for the GEOMETRIC Frobenius of `Def_RP_CurveCoh_Curve` (review R4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh Polynomial

noncomputable section

/-- In a field, `y ^ n = y`, `y ≠ 0`, `1 ≤ n` give `y ^ (n - 1) = 1`. -/
theorem pow_pred_eq_one {F : Type} [Field F] {y : F} {n : ℕ} (hn : 1 ≤ n) (hy : y ^ n = y) (h0 : y ≠ 0) :
    y ^ (n - 1) = 1 := by
  have h : y ^ (n - 1) * y = 1 * y := by rw [← pow_succ, Nat.sub_add_cancel hn, hy, one_mul]
  exact mul_right_cancel₀ h0 h

section Level

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

/-- The constant level `K(𝔽_{p^k}) = K(roots of X^(p^k) - X)` inside `K̄`. -/
def constLevel (k : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K (((X : K[X]) ^ (p ^ k) - X).rootSet (AlgebraicClosure K))

variable {K p}

theorem one_lt_pow_p {k : ℕ} (hk : 0 < k) : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.out.one_lt

theorem mem_constLevel {k : ℕ} (hk : 0 < k) {x : AlgebraicClosure K} (hx : x ^ (p ^ k) = x) :
    x ∈ constLevel K p k := by
  refine IntermediateField.subset_adjoin _ _ ((mem_rootSet).2 ⟨FiniteField.X_pow_card_sub_X_ne_zero K
    (one_lt_pow_p hk), ?_⟩)
  simp [hx]

/-- **Constant extensions are unramified**: `K(𝔽_{p^k}) ∈ unramSet A K`. -/
theorem constLevel_mem_unramSet {k : ℕ} (hk : 0 < k) : constLevel K p k ∈ unramSet A K := by
  have hn : 1 < p ^ k := one_lt_pow_p hk
  have hsplit : ((X : K[X]) ^ (p ^ k) - X).IsSplittingField K (constLevel K p k) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hsep : ((X : K[X]) ^ (p ^ k) - X).Separable := galois_poly_separable p (p ^ k) (dvd_pow_self p hk.ne')
  set L := constLevel K p k with hL
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  refine ⟨hsplit.finiteDimensional _ _, IsGalois.of_separable_splitting_field hsep, fun Q hQ => ?_⟩
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  -- `σ` fixes every generator
  have hgen : ∀ y : L, ((y : AlgebraicClosure K)) ^ (p ^ k) = y → σ y = y := by
    intro y hy0
    have hyp : y ^ (p ^ k) = y := Subtype.ext hy0
    have hint : IsIntegral A y := by
      by_cases h0 : y = 0
      · rw [h0]
        exact isIntegral_zero
      · refine IsIntegral.of_pow (by omega : 0 < p ^ k - 1) ?_
        rw [pow_pred_eq_one hn.le hyp h0]
        exact isIntegral_one
    let yA : integralClosure A L := ⟨y, hint⟩
    have hd : σ • yA - yA ∈ Q := hσ yA
    have hdval : ((σ • yA - yA : integralClosure A L) : L) = σ y - y := rfl
    by_contra hne
    have hd0 : σ y - y ≠ 0 := sub_ne_zero.2 hne
    have hdp : (σ y - y) ^ (p ^ k) = σ y - y := by
      rw [sub_pow_char_pow, ← map_pow, hyp]
    have h1 : (σ • yA - yA) ^ (p ^ k - 1) ∈ Q := Ideal.pow_mem_of_mem Q hd _ (by omega)
    have h1' : (σ • yA - yA) ^ (p ^ k - 1) = 1 := by
      apply Subtype.val_injective
      change ((σ • yA - yA : integralClosure A L) : L) ^ (p ^ k - 1) = 1
      rw [hdval, pow_pred_eq_one hn.le hdp hd0]
    rw [h1'] at h1
    exact hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
  have hext : (L.val.comp (σ : L →ₐ[K] L)) = L.val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin K hL (fun x hx => ?_)
    have hx' : x ^ (p ^ k) = x := by
      have := ((mem_rootSet).1 hx).2
      simpa [sub_eq_zero] using this
    simp only [AlgHom.comp_apply, IntermediateField.coe_val]
    rw [AlgEquiv.coe_toAlgHom, hgen _ hx']
  ext y
  have := congrArg (fun f : L →ₐ[K] AlgebraicClosure K => f y) hext
  simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] at this
  rw [AlgEquiv.one_apply]
  exact this

theorem mem_maxUnram_of_pow {k : ℕ} (hk : 0 < k) {x : AlgebraicClosure K} (hx : x ^ (p ^ k) = x) :
    x ∈ maxUnram A K :=
  le_iSup (fun L : unramSet A K => (L : IntermediateField K (AlgebraicClosure K)))
    ⟨_, constLevel_mem_unramSet A hk⟩ (mem_constLevel hk hx)

/-- Every constant (`x ^ (q ^ n) = x`, `q = p ^ e`, `e, n > 0`) of `K̄` lies in `K_U`. -/
theorem mem_maxUnram_of_isConst {e : ℕ} (he : 0 < e) {x : AlgebraicClosure K} (hx : IsConst (p ^ e) x) :
    x ∈ maxUnram A K := by
  obtain ⟨n, hn, h⟩ := hx
  rw [← pow_mul] at h
  exact mem_maxUnram_of_pow A (Nat.mul_pos he hn) h

end Level

section Zeta

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]
  {e : ℕ} (he : 0 < e) (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

include hN in
theorem coprime_q : Nat.Coprime (p ^ e) N := by
  have h : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).2 h)
  exact Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 h)

include hN in
theorem exists_inv_q : ∃ q' : ZMod N, ((p ^ e : ℕ) : ZMod N) * q' = 1 :=
  ⟨((ZMod.unitOfCoprime (p ^ e) (coprime_q K p N hN))⁻¹ : (ZMod N)ˣ), by
    rw [← ZMod.coe_unitOfCoprime (p ^ e) (coprime_q K p N hN), Units.mul_inv]⟩

include he hN in
/-- `K_U` contains a primitive `N`-th root of unity which is a constant. -/
theorem exists_zeta : ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ N ∧ IsConst (p ^ e) ζ := by
  have : NeZero (N : AlgebraicClosure K) :=
    ⟨by rw [← map_natCast (algebraMap K (AlgebraicClosure K))]; exact (_root_.map_ne_zero _).2 hN⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (cyclotomic N (AlgebraicClosure K))
    (degree_cyclotomic_pos N (AlgebraicClosure K) (NeZero.pos N)).ne'
  have hzp : IsPrimitiveRoot z N := isRoot_cyclotomic_iff.1 hz
  have hpow : z ^ ((p ^ e) ^ Nat.totient N) = z := by
    have h := Nat.ModEq.pow_totient (coprime_q K p N hN (e := e))
    unfold Nat.ModEq at h
    rw [← pow_mod_N hzp, h, pow_mod_N hzp, pow_one]
  have htot : 0 < Nat.totient N := Nat.totient_pos.2 (NeZero.pos N)
  have hmem : z ∈ maxUnram A K := mem_maxUnram_of_isConst A he ⟨_, htot, hpow⟩
  refine ⟨⟨z, hmem⟩, ?_, ⟨_, htot, Subtype.ext hpow⟩⟩
  exact (IsPrimitiveRoot.map_iff_of_injective (ζ := (⟨z, hmem⟩ : maxUnram A K)) (f := (maxUnram A K).val)
    Subtype.val_injective).1 hzp

variable {A K p N}

theorem zeta_fixed {ζ : maxUnram A K} (hc : IsConst (p ^ e) ζ) : ∀ σ ∈ pi1geo A K (p ^ e), σ ζ = ζ :=
  fun σ hσ => (mem_pi1geo A K _ σ).1 hσ ζ hc

/-- An arithmetic Frobenius lift sends a constant primitive root `ζ` to `ζ ^ q`. -/
theorem frobLift_zeta {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N) (hc : IsConst (p ^ e) ζ) {φ : Pi1 A K}
    (hφ : IsFrobLift A K (p ^ e) φ) : φ ζ = epow ζ ((p ^ e : ℕ) : ZMod N) := by
  rw [hφ ζ hc, epow, ZMod.val_natCast, pow_mod_N hζ]

end Zeta

section Curve

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q N : ℕ} [NeZero N] {ζ : maxUnram A K}
  (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ pi1geo A K q, σ ζ = ζ)

instance maxUnram_isIntegral : Algebra.IsIntegral K (maxUnram A K) := inferInstance

/-- **Kummer theory over `F̄ ⊗ A`**: `H¹(U ⊗ 𝔽̄, ZMod N) ≃ rad / (π₁^geo-fixed units)` (all classes Kummer). -/
def curveKummerEquiv :
    rad (pi1geo A K q) N ⧸ (fixUnits (pi1geo A K q)).subgroupOf (rad (pi1geo A K q) N) ≃*
      Multiplicative (curveH1 q (triv K (maxUnram A K) N)) :=
  kummerEquiv hζ hζΓ

/-- **Geometric Frobenius on Kummer classes over the curve** (review R4): for an arithmetic Frobenius lift `φ`,
`F [kchar α] = q • [kchar (φ⁻¹ α)]`. -/
theorem geomFrobH1_kclass {φ : Pi1 A K} (hφ : φ ζ = epow ζ (q : ZMod N)) {q' : ZMod N}
    (hq : (q : ZMod N) * q' = 1) {α : (maxUnram A K)ˣ} (hα : α ∈ rad (pi1geo A K q) N) :
    geomFrobH1 q (triv K (maxUnram A K) N) φ (kclass hζ hζΓ hα) =
      (q : ZMod N) • kclass hζ hζΓ (rad_map φ⁻¹ hα) :=
  geomFrob_kclass hζ hζΓ φ hφ hq hα

end Curve

end

end Kummer
end RamanujanPetersson


