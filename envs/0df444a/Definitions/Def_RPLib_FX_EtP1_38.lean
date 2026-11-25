-- Prove2me | Definitions.Def_RPLib_FX_EtP1_38
-- name    : RPLib_FX_EtP1_38
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T08:10:03.89238+00:00
-- url     : https://prove2.me/theorems/e7c700ae-2a7f-5f97-b329-fa994df200ac
-- title:
--   Étale cohomology of the projective line, library file 38 (an extra file from a re-cut)
-- statement:
--   File 38 (an extra file from a re-cut) of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Kummer_Unr`: S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified
--   * `S4.Def_RP_Kummer_Bridge`: S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes
--   * `S4.Def_RP_EtCompact_GmRoot`: S4-EtCompact: Kummer theory of `G_m` (O8c, file M4a)
--   * `S4.Def_RP_EtCompact_GmKc`: S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_16

/-!
# Étale cohomology of the projective line, library file 38 (extra file from a re-cut)

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Kummer_Unr`: S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified
* `S4.Def_RP_Kummer_Bridge`: S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes
* `S4.Def_RP_EtCompact_GmRoot`: S4-EtCompact: Kummer theory of `G_m` (O8c, file M4a)
* `S4.Def_RP_EtCompact_GmKc`: S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Kummer_Unr =====
section

/-!
# S4-Kummer, part K4a (assembly): Kummer roots of `N`-th-power ideal classes are unramified

* `mem_fixingSubgroup_adjoin`: an automorphism of `K̄` fixing `S` fixes `K(S)`.
* `lift_mem_fixingSubgroup`: a lift to `K̄` of an inertia element of `Gal(L/K)` fixes every unramified
  Galois subextension of `L` (the `key` step of `GalCover.sup_mem_unramSet`).
* `root_mem_maxUnram`: `M ∈ unramSet A K`, `0 ≠ a ∈ M`, `N` invertible in `A`, and for every `τ ∈ Gal(M/K)` a
  fractional ideal `I` of `integralClosure A M` with `I ^ N * (τ a) = 1`: every `γ ∈ K̄` with `γ ^ N = a` lies in
  `K_U = maxUnram A K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Kummer

noncomputable section

variable {K : Type} [Field K]

section Lift

variable (A : Type) [CommRing A] [Algebra A K]

/-- **Kummer roots of `N`-th-power ideal classes are unramified.** -/
theorem root_mem_maxUnram {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    [IsFractionRing (integralClosure A M) M] {N : ℕ} [NeZero N] (hN : IsUnit (N : A)) {a : M} (ha : a ≠ 0)
    (hI : ∀ τ : M ≃ₐ[K] M, ∃ I : FractionalIdeal (nonZeroDivisors (integralClosure A M)) M,
      I ^ N * FractionalIdeal.spanSingleton _ (τ a) = 1)
    {γ : AlgebraicClosure K} (hγ : γ ^ N = (a : AlgebraicClosure K)) : γ ∈ maxUnram A K := by
  obtain ⟨fM, gM, uM⟩ := hM
  have hNK : (N : K) ≠ 0 := by
    have h := hN.map (algebraMap A K)
    rw [map_natCast] at h
    exact h.ne_zero
  have hNM : (N : M) ≠ 0 := by
    rw [← map_natCast (algebraMap K M)]
    exact (_root_.map_ne_zero _).2 hNK
  have haint : IsIntegral K (a : AlgebraicClosure K) := Algebra.IsIntegral.isIntegral _
  set P : K[X] := (minpoly K (a : AlgebraicClosure K)).comp (X ^ N) with hPdef
  have hP0 : P ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt (n := 0)
    rw [hPdef, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
    exact Nat.mul_pos (minpoly.natDegree_pos haint) (NeZero.pos N)
  -- every root of `P` is an `N`-th root of a Galois conjugate of `a`
  have hroot : ∀ y ∈ P.rootSet (AlgebraicClosure K), ∃ τ : M ≃ₐ[K] M,
      y ^ N = ((τ a : M) : AlgebraicClosure K) := by
    intro y hy
    have hy0 : aeval (y ^ N) (minpoly K (a : AlgebraicClosure K)) = 0 := by
      have h := (Polynomial.mem_rootSet.1 hy).2
      rwa [hPdef, Polynomial.aeval_comp, Polynomial.aeval_X_pow] at h
    have hsplit : ((minpoly K a).map (algebraMap K M)).Splits := Normal.splits inferInstance a
    rw [IntermediateField.minpoly_eq] at hsplit
    have hmem : y ^ N ∈ M := by
      refine (IntermediateField.splits_iff_mem (IsAlgClosed.splits _)).1 hsplit _ ?_
      exact Polynomial.mem_rootSet.2 ⟨minpoly.ne_zero haint, hy0⟩
    have hmin : minpoly K (⟨y ^ N, hmem⟩ : M) = minpoly K a := by
      rw [IntermediateField.minpoly_eq, IntermediateField.minpoly_eq]
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible haint) hy0 (minpoly.monic haint)).symm
    obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.1 ((Normal.minpoly_eq_iff_mem_orbit (F := K) (E := ↥M)).1 hmin)
    exact ⟨τ, by rw [← AlgEquiv.smul_def, hτ]⟩
  have hsep : ∀ y ∈ P.rootSet (AlgebraicClosure K), IsSeparable K y := by
    intro y hy
    obtain ⟨τ, hτ⟩ := hroot y hy
    have hb : τ a ≠ 0 := (_root_.map_ne_zero τ).2 ha
    have hpol : (X ^ N - C (τ a) : M[X]).Separable := separable_X_pow_sub_C (τ a) hNM hb
    have hay : aeval y (X ^ N - C (τ a) : M[X]) = 0 := by
      rw [map_sub, aeval_X_pow, aeval_C, hτ]
      exact sub_eq_zero.2 rfl
    have hsepM : IsSeparable M y := hpol.of_dvd (minpoly.dvd M y hay)
    exact IsSeparable.of_algebra_isSeparable_of_isSeparable (F := K) (E := M) hsepM
  set E : IntermediateField K (AlgebraicClosure K) := IntermediateField.adjoin K (P.rootSet (AlgebraicClosure K))
    with hEdef
  have hspl : IsSplittingField K E P := IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional K E := IsSplittingField.finiteDimensional E P
  have : Normal K E := Normal.of_isSplittingField P
  have : Algebra.IsSeparable K E := (IntermediateField.isSeparable_adjoin_iff_isSeparable K (AlgebraicClosure K)).2 hsep
  have : IsGalois K E := ⟨⟩
  have hL : M ⊔ E ∈ unramSet A K := by
    refine ⟨inferInstance, inferInstance, fun Q hQ => ?_⟩
    rw [eq_bot_iff]
    intro τ hτ
    rw [Subgroup.mem_bot]
    obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ y : ↥(M ⊔ E),
        σ (y : AlgebraicClosure K) = ((τ y : ↥(M ⊔ E)) : AlgebraicClosure K) :=
      ⟨τ.liftNormal (AlgebraicClosure K), fun y => τ.liftNormal_commutes (AlgebraicClosure K) y⟩
    have hσM : σ ∈ M.fixingSubgroup := lift_mem_fixingSubgroup A le_sup_left uM Q τ hτ σ hσ
    have hτM : ∀ x : M, τ (IntermediateField.inclusion (le_sup_left : M ≤ M ⊔ E) x) =
        IntermediateField.inclusion (le_sup_left : M ≤ M ⊔ E) x := by
      intro x
      apply Subtype.ext
      rw [← hσ]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσM _ x.2
    have hσE : σ ∈ E.fixingSubgroup := by
      apply mem_fixingSubgroup_adjoin
      intro y hy
      obtain ⟨τ', hτ'⟩ := hroot y hy
      obtain ⟨I, hI'⟩ := hI τ'
      have hyL : y ∈ M ⊔ E := (le_sup_right : E ≤ M ⊔ E) (IntermediateField.subset_adjoin K _ hy)
      have hpow : (⟨y, hyL⟩ : ↥(M ⊔ E)) ^ N = IntermediateField.inclusion (le_sup_left : M ≤ M ⊔ E) (τ' a) :=
        Subtype.ext (by simpa using hτ')
      have hfix := fixed_of_inertia (le_sup_left : M ≤ M ⊔ E) hN Q τ hτ hτM I hI' ⟨y, hyL⟩ hpow
      have := hσ ⟨y, hyL⟩
      rw [hfix] at this
      exact this
    have hfix : σ ∈ (M ⊔ E).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hσM, hσE⟩
    ext y
    rw [AlgEquiv.one_apply, ← hσ]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hfix _ y.2
  have hγE : γ ∈ E := by
    apply IntermediateField.subset_adjoin
    refine Polynomial.mem_rootSet.2 ⟨hP0, ?_⟩
    rw [hPdef, Polynomial.aeval_comp, Polynomial.aeval_X_pow, hγ]
    exact minpoly.aeval K _
  exact le_iSup (fun L : unramSet A K => (L : IntermediateField K (AlgebraicClosure K))) ⟨_, hL⟩
    ((le_sup_right : E ≤ M ⊔ E) hγE)

end Lift

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_Kummer_Bridge =====
section

/-!
# S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes

* `count_spanSingleton`: `val_v((a)) = -log v(a)` for a nonzero `a` in the fraction field of a Dedekind domain.
* `exists_pow_mul_spanSingleton_eq_one`: if `N ∣ log v(a)` for every height-one prime `v`, then
  `I ^ N * (a) = 1` for a fractional ideal `I`.
* `root_mem_maxUnram_of_dvd`: `M ∈ unramSet A K`, `0 ≠ a ∈ M` with `N ∣ log v(a)` at every prime of the integral
  closure of `A` in `M`, `N` invertible in `A`: every `γ ∈ K̄` with `γ ^ N = a` lies in `maxUnram A K`
  (Galois conjugates handled by `PicDescent.valuation_pullH`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson
namespace Kummer

noncomputable section

section Bridge

variable {B M : Type*} [CommRing B] [IsDedekindDomain B] [Field M] [Algebra B M] [IsFractionRing B M]

/-- **Divisible valuations give an `N`-th-power ideal class**: `I ^ N * (a) = 1`. -/
theorem exists_pow_mul_spanSingleton_eq_one {N : ℕ} [NeZero N] {a : M} (ha : a ≠ 0)
    (hdiv : ∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a)) :
    ∃ I : FractionalIdeal (nonZeroDivisors B) M,
      I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a = 1 := by
  classical
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors B) a ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).2 ha
  have hfin : (Function.support fun v : HeightOneSpectrum B =>
      -(FractionalIdeal.count M v (FractionalIdeal.spanSingleton (nonZeroDivisors B) a)) / (N : ℤ)).Finite := by
    refine (Filter.eventually_cofinite.1
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors B) a))).subset ?_
    intro v hv h0
    apply hv
    simp only [h0, neg_zero, EuclideanDomain.zero_div]
  let e := Finsupp.ofSupportFinite _ hfin
  let I : FractionalIdeal (nonZeroDivisors B) M := e.prod (HeightOneSpectrum.asIdeal · ^ ·)
  have hI0 : I ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  have hJ0 : I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a ≠ 0 := mul_ne_zero (pow_ne_zero _ hI0) hspan
  have hcount : ∀ v : HeightOneSpectrum B,
      FractionalIdeal.count M v (I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a) = 0 := by
    intro v
    rw [FractionalIdeal.count_mul M v (pow_ne_zero _ hI0) hspan, FractionalIdeal.count_pow,
      FractionalIdeal.count_finsuppProd, Finsupp.ofSupportFinite_coe, count_spanSingleton v ha]
    obtain ⟨k, hk⟩ := hdiv v
    rw [hk, neg_neg, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 (NeZero.ne N))]
    ring
  refine ⟨I, ?_⟩
  calc I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a
      = ∏ᶠ v : HeightOneSpectrum B, (v.asIdeal : FractionalIdeal (nonZeroDivisors B) M) ^
          (FractionalIdeal.count M v (I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a)) :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization' M hJ0).symm
    _ = 1 := by simp only [hcount, zpow_zero, finprod_one]

end Bridge

section Assembly

variable {K : Type} [Field K] (A : Type) [CommRing A] [Algebra A K]

/-- **Kummer roots of elements with `N`-divisible valuations are unramified.** -/
theorem root_mem_maxUnram_of_dvd {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    [IsDedekindDomain (integralClosure A M)] [IsFractionRing (integralClosure A M) M] {N : ℕ} [NeZero N]
    (hN : IsUnit (N : A)) {a : M} (ha : a ≠ 0)
    (hdiv : ∀ v : HeightOneSpectrum (integralClosure A M), (N : ℤ) ∣ WithZero.log (v.valuation M a))
    {γ : AlgebraicClosure K} (hγ : γ ^ N = (a : AlgebraicClosure K)) : γ ∈ maxUnram A K := by
  refine root_mem_maxUnram A hM hN ha (fun τ => exists_pow_mul_spanSingleton_eq_one
    ((_root_.map_ne_zero τ).2 ha) (fun w => ?_)) hγ
  let σ : integralClosure A M ≃+* integralClosure A M := (τ.restrictScalars A).mapIntegralClosure.toRingEquiv
  have h : w.valuation M (τ a) = (PicDescent.pullH σ w).valuation M a :=
    (PicDescent.valuation_pullH σ τ.toRingEquiv (fun b => rfl) w a).symm
  rw [h]
  exact hdiv _

end Assembly

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtCompact_GmRoot =====
section

/-!
# S4-EtCompact: Kummer theory of `G_m` (O8c, file M4a)

`R = k[X]_X`, `K = k(X)`, `E = K_U = maxUnram R K`, `Γ = π₁(G_m) = Gal(E/K)`.

* `LX.exists_root_X`: **`X^{1/N}` lies in `E`** (`N` invertible in `k`; `root_mem_maxUnram_of_dvd` with `M = K`,
  `X` a unit of `R`).
* `kchar_pow_left'`: `kchar (γ ^ j) = j • kchar γ`.
* **`LX.exists_kchar_eq_nsmul`**: for `k` algebraically closed, every Kummer character on `π₁(G_m)` is a multiple of
  the character of `X^{1/N}` (`α ^ N = c X^m b^N` by `dvd_ord_of_unram0` + units of `R`).
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr Kummer EtPi1

section Root

variable (k : Type) [Field k]

/-- **`X^{1/N}` is unramified over `k[X]_X`.** -/
theorem LX.exists_root_X {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) :
    ∃ γ : maxUnram (LX k) (RatFunc k),
      γ ^ N = algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k)) RatFunc.X := by
  have : IsDedekindDomain (integralClosure (LX k)
      (⊥ : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k)))) :=
    integralClosure.isDedekindDomain (A := LX k) (K := RatFunc k)
      (L := (⊥ : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k))))
  have : IsFractionRing (integralClosure (LX k)
      (⊥ : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k))))
      (⊥ : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k))) :=
    integralClosure.isFractionRing_of_finite_extension (A := LX k) (RatFunc k) _
  obtain ⟨b, hb⟩ : ∃ b : integralClosure (LX k) (⊥ : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k))),
      b = algebraMap (LX k) _ (algebraMap k[X] (LX k) X) := ⟨_, rfl⟩
  have hbu : IsUnit b := hb ▸ (LX.isUnit_algebraMap_X k).map _
  obtain ⟨a, ha⟩ : ∃ a : (⊥ : IntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k))),
      a = algebraMap (integralClosure (LX k) _) _ b := ⟨_, rfl⟩
  have ha' : (a : AlgebraicClosure (RatFunc k)) = algebraMap (RatFunc k) _ RatFunc.X := by
    rw [ha, hb]
    show algebraMap (LX k) (AlgebraicClosure (RatFunc k)) (algebraMap k[X] (LX k) X) = _
    rw [IsScalarTower.algebraMap_apply (LX k) (RatFunc k) (AlgebraicClosure (RatFunc k)), LX.algebraMap_X]
  have ha0 : a ≠ 0 := by
    intro h
    have h2 : (a : AlgebraicClosure (RatFunc k)) = 0 := by rw [h]; rfl
    rw [ha', map_eq_zero_iff _ (algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k))).injective] at h2
    exact RatFunc.X_ne_zero h2
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (a : AlgebraicClosure (RatFunc k)) (NeZero.pos N)
  have hU : γ ∈ maxUnram (LX k) (RatFunc k) := by
    refine root_mem_maxUnram_of_dvd (LX k) (bot_mem_unramSet _ _) (LX.isUnit_natCast k hN) ha0 (fun v => ?_) hγ
    have hv : b ∉ v.asIdeal := fun hm => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hbu)
    rw [ha, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hv, WithZero.log_one]
    exact dvd_zero _
  refine ⟨⟨γ, hU⟩, Subtype.ext ?_⟩
  rw [IntermediateField.coe_pow]
  exact hγ.trans ha'

end Root

section KPow

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)} {N : ℕ} [NeZero N]
  {ζ : E} (hζ : IsPrimitiveRoot ζ N)

theorem kchar_pow_left' {γ : Eˣ} (hγ : γ ∈ rad Γ N) (σ : Γ) (j : ℕ) :
    kchar hζ (γ ^ j) σ = j • kchar hζ γ σ := by
  induction j with
  | zero => rw [pow_zero, zero_smul]; exact kchar_of_fix hζ (fixUnits Γ).one_mem σ
  | succ j ih => rw [pow_succ, kchar_mul_left hζ ((rad Γ N).pow_mem hγ j) hγ σ, ih, succ_nsmul]

end KPow

section Kum

variable {k : Type} [Field k] [IsAlgClosed k]

/-- **Kummer characters of `π₁(G_m)` are multiples of the character of `X^{1/N}`.** -/
theorem LX.exists_kchar_eq_nsmul {N : ℕ} [NeZero N] {ζ : maxUnram (LX k) (RatFunc k)} (hζ : IsPrimitiveRoot ζ N)
    (hζΓ : ∀ σ : Pi1 (LX k) (RatFunc k), σ ζ = ζ) {γ : (maxUnram (LX k) (RatFunc k))ˣ}
    (hγ : (γ : maxUnram (LX k) (RatFunc k)) ^ N = algebraMap (RatFunc k) _ RatFunc.X)
    {α : (maxUnram (LX k) (RatFunc k))ˣ} (hα : α ∈ rad (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) N) :
    ∃ m : ℕ, ∀ σ : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))), kchar hζ α σ = m • kchar hζ γ σ := by
  have hγr : γ ∈ rad (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) N := fun σ _ => by
    rw [hγ, AlgEquiv.commutes]
  obtain ⟨a, ha'⟩ := (InfiniteGalois.mem_bot_iff_fixed (k := RatFunc k) (K := maxUnram (LX k) (RatFunc k))
    ((α : maxUnram (LX k) (RatFunc k)) ^ N)).2 (fun σ => hα σ (Subgroup.mem_top σ))
  have ha : algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k)) a = (α : maxUnram (LX k) (RatFunc k)) ^ N := ha'
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact α.ne_zero ((pow_eq_zero_iff (NeZero.ne N)).1 ha.symm)
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite (A := LX k) (K := RatFunc k)
    {((α : maxUnram (LX k) (RatFunc k)) : AlgebraicClosure (RatFunc k))}
    (fun x hx => by rw [Finset.mem_singleton] at hx; exact hx ▸ (α : maxUnram (LX k) (RatFunc k)).2)
  have hαL : ((α : maxUnram (LX k) (RatFunc k)) : AlgebraicClosure (RatFunc k)) ∈ L :=
    hle (IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_singleton_self _)))
  have haN : ((α : maxUnram (LX k) (RatFunc k)) : AlgebraicClosure (RatFunc k)) ^ N =
      algebraMap (RatFunc k) (AlgebraicClosure (RatFunc k)) a := by
    rw [← IntermediateField.coe_pow, ← ha]
    rfl
  have hdvd := fun π hπ => dvd_ord_of_unram0 hL hαL haN ha0 π hπ
  obtain ⟨u, b, hab⟩ := exists_eq_unit_mul_pow (R := LX k) (RatFunc k) ha0 hdvd
  obtain ⟨c, m, hc, hu⟩ := LX.unit_eq k u
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (NeZero.pos N)
  have hN0 : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.2 (NeZero.ne N)
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, (m' : ℤ) = m % N := ⟨(m % N).toNat, Int.toNat_of_nonneg (Int.emod_nonneg m hN0)⟩
  have hX0 : (RatFunc.X : RatFunc k) ≠ 0 := RatFunc.X_ne_zero
  -- `a = F ^ N * X ^ m'` with `F = d * b * X ^ (m / N)`
  have hXm : (RatFunc.X : RatFunc k) ^ m = RatFunc.X ^ m' * (RatFunc.X ^ (m / N)) ^ N := by
    rw [← zpow_natCast (RatFunc.X ^ (m / N)) N, ← zpow_mul, ← zpow_natCast RatFunc.X m', ← zpow_add₀ hX0, hm',
      Int.emod_add_ediv_mul]
  have haF : a = (RatFunc.C d * b * RatFunc.X ^ (m / N)) ^ N * RatFunc.X ^ m' := by
    rw [hab, hu, hXm, ← hd, map_pow]
    ring
  set F : RatFunc k := RatFunc.C d * b * RatFunc.X ^ (m / N) with hF
  have hF0 : F ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne N), zero_mul] at haF
    exact ha0 haF
  have hF0' : algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k)) F ≠ 0 := (_root_.map_ne_zero _).2 hF0
  have hG0 : algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k)) F * (γ : maxUnram (LX k) (RatFunc k)) ^ m' ≠ 0 :=
    mul_ne_zero hF0' (pow_ne_zero _ γ.ne_zero)
  have hXE : algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k)) RatFunc.X ≠ 0 := (_root_.map_ne_zero _).2 hX0
  have hrat : ((α : maxUnram (LX k) (RatFunc k)) /
      (algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k)) F * (γ : maxUnram (LX k) (RatFunc k)) ^ m')) ^ N = 1 := by
    rw [div_pow, ← ha, haF, map_mul, map_pow, map_pow, mul_pow, ← pow_mul, mul_comm m' N, pow_mul, hγ,
      div_self (mul_ne_zero (pow_ne_zero _ hF0') (pow_ne_zero _ hXE))]
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hrat
  -- the fixed factor
  have hf0 : ζ ^ i * algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k)) F ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (hζ.ne_zero (NeZero.ne N))) hF0'
  have hfix : Units.mk0 _ hf0 ∈ fixUnits (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) := fun σ _ => by
    simp only [Units.val_mk0, map_mul, map_pow, hζΓ σ, AlgEquiv.commutes]
  have hαe : α = Units.mk0 _ hf0 * γ ^ m' := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mk0, Units.val_pow_eq_pow_val, hi, mul_assoc, div_mul_cancel₀ _ hG0]
  refine ⟨m', fun σ => ?_⟩
  rw [hαe, kchar_mul_left hζ (fixUnits_le_rad _ N hfix) ((rad _ N).pow_mem hγr m') σ, kchar_of_fix hζ hfix σ,
    zero_add, kchar_pow_left' hζ hγr σ m']

end Kum

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_GmKc =====
section

/-!
# S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)

`R = k[X]_X`, `K = k(X)`, `E = K_U = maxUnram R K`, `Γ = π₁(G_m)`, `N = lⁿ` invertible in `k`, `k` algebraically
closed, `γ ^ N = X`.

* `LX.exists_kchar_eq_one`: some `σ₁` has `kchar γ σ₁ = 1` (else `γ ^ l^(n-1) ∈ K` and `X` is an `l`-th power).
* `LX.hom_eq_kchar_smul`: every locally constant homomorphism `c : Γ → V` (`N • V = 0`) is
  `c σ = (kchar γ σ).val • c σ₁`.
* `LX.h1LinEquiv`: `H¹_cont(Γ, M) ≃ M` (trivial action, `N • M = 0`), evaluation at `σ₁`.
* **`Gm.nonempty_h1Equiv`**: `H^1(G_m, Λ) ≃+ Λ` for `lⁿ • Λ = 0`.
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr Kummer EtPi1

section Gen

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)}

theorem kchar_pow_right' {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ)
    {α : Eˣ} (hα : α ∈ rad Γ N) (σ : Γ) (j : ℕ) : kchar hζ α (σ ^ j) = j • kchar hζ α σ := by
  induction j with
  | zero => rw [pow_zero, zero_smul]; exact kchar_one hζ hζΓ hα
  | succ j ih => rw [pow_succ, kchar_mul hζ hζΓ hα, ih, succ_nsmul]

theorem exists_kchar_eq_one' {l n : ℕ} [Fact l.Prime] (hn : 0 < n) [NeZero (l ^ n)] {ζ : E}
    (hζ : IsPrimitiveRoot ζ (l ^ n)) (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ) {α : Eˣ} (hα : α ∈ rad Γ (l ^ n)) {τ0 : Γ}
    (h0 : (l ^ (n - 1)) • kchar hζ α τ0 ≠ 0) : ∃ τ : Γ, kchar hζ α τ = 1 := by
  have hl : l.Prime := Fact.out
  have hu : IsUnit (kchar hζ α τ0) := by
    rw [← ZMod.natCast_zmod_val (kchar hζ α τ0), ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right n ((Nat.Prime.coprime_iff_not_dvd hl).2 fun hd => h0 ?_).symm
    obtain ⟨w, hw⟩ := hd
    rw [← ZMod.natCast_zmod_val (kchar hζ α τ0), hw, nsmul_eq_mul, ← Nat.cast_mul, ← mul_assoc,
      ← pow_succ, Nat.sub_add_cancel hn, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  refine ⟨τ0 ^ ((hu.unit⁻¹ : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val, ?_⟩
  rw [kchar_pow_right' hζ hζΓ hα, nsmul_eq_mul, ZMod.natCast_zmod_val, IsUnit.val_inv_mul]

end Gen

section Kc

variable {k : Type} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- **`X^{1/lⁿ}` has a Kummer character of exact order `lⁿ`.** -/
theorem LX.exists_kchar_eq_one {l n : ℕ} [Fact l.Prime] (hn : 0 < n) [NeZero (l ^ n)]
    {ζ : maxUnram (LX k) (RatFunc k)} (hζ : IsPrimitiveRoot ζ (l ^ n))
    (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))), σ ζ = ζ) {γ : (maxUnram (LX k) (RatFunc k))ˣ}
    (hγ : (γ : maxUnram (LX k) (RatFunc k)) ^ (l ^ n) = algebraMap (RatFunc k) _ RatFunc.X) :
    ∃ σ₁ : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))), kchar hζ γ σ₁ = 1 := by
  have hγr : γ ∈ rad (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) (l ^ n) := fun σ _ => by
    rw [hγ, AlgEquiv.commutes]
  by_cases h : ∃ τ0 : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))), (l ^ (n - 1)) • kchar hζ γ τ0 ≠ 0
  · obtain ⟨τ0, h0⟩ := h
    exact exists_kchar_eq_one' hn hζ hζΓ hγr h0
  simp only [not_exists, ne_eq, not_not] at h
  exfalso
  have hfix : γ ^ (l ^ (n - 1)) ∈ fixUnits (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) :=
    (kchar_eq_zero_iff hζ ((rad _ _).pow_mem hγr _)).1 fun σ => by
      rw [kchar_pow_left' hζ hγr]
      exact h σ
  obtain ⟨g, hg⟩ := (InfiniteGalois.mem_bot_iff_fixed (k := RatFunc k) (K := maxUnram (LX k) (RatFunc k))
    ((γ ^ (l ^ (n - 1)) : (maxUnram (LX k) (RatFunc k))ˣ) : maxUnram (LX k) (RatFunc k))).2
    (fun σ => hfix σ (Subgroup.mem_top σ))
  have hg' : algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k)) g =
      (γ : maxUnram (LX k) (RatFunc k)) ^ (l ^ (n - 1)) := by
    rw [← Units.val_pow_eq_pow_val]
    exact hg
  have hl : l.Prime := Fact.out
  have hgl : g ^ l = RatFunc.X := by
    apply (algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k))).injective
    rw [map_pow, hg', ← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, hγ]
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hl.ne_zero] at hgl
    exact RatFunc.X_ne_zero hgl.symm
  have hdeg : ∀ j : ℕ, RatFunc.intDegree (g ^ j) = j * RatFunc.intDegree g := by
    intro j
    induction j with
    | zero => rw [pow_zero, RatFunc.intDegree_one]; simp
    | succ j ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ hg0) hg0, ih]
      push_cast
      ring
  have h1 := hdeg l
  rw [hgl, RatFunc.intDegree_X] at h1
  have hd : (l : ℤ) ∣ 1 := ⟨_, h1⟩
  have hl1 : (l : ℤ) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg l) hd
  exact hl.ne_one (by exact_mod_cast hl1)

variable {N : ℕ} [NeZero N] {ζ : maxUnram (LX k) (RatFunc k)} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))), σ ζ = ζ) {γ : (maxUnram (LX k) (RatFunc k))ˣ}
  (hγ : (γ : maxUnram (LX k) (RatFunc k)) ^ N = algebraMap (RatFunc k) _ RatFunc.X)
  {σ₁ : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k)))} (h1 : kchar hζ γ σ₁ = 1)
include hζΓ hγ h1

end Kc

section H1Gen

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N]
  {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 (LX k) (RatFunc k)) M)

end H1Gen

section GmH1

variable (k : Type) [Field k] [IsAlgClosed k]

end GmH1

end RamanujanPetersson.EtCompact

end

end


