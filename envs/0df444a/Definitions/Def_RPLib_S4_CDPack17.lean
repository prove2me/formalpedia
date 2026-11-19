-- Prove2me | Definitions.Def_RPLib_S4_CDPack17
-- name    : RPLib_S4_CDPack17
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:16:09.100904+00:00
-- url     : https://prove2.me/theorems/6922f644-0b7a-437a-89e3-3ec110009324
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 17 of 71
-- statement:
--   Part 17 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_PlaceVal`: The Jacobian (unit S4-JacComplete), part `PlaceVal` (dictionary D1, generic valuation theory)
--   * `Def_RP_JacRRFam_A`: Riemann-Roch over an arbitrary constant field, part A (unit S4-JacRRFam)
--   * `Def_RP_JacRRFam_C`: Places over an arbitrary field, part C: dimensions of quotients of Dedekind domains
--   * `Def_RP_JacRRFam_D`: Places over an arbitrary field, part D: Dedekind domains with finite-dimensional quotients
--   * `Def_RP_JacRRFam_E`: Places over an arbitrary field, part E: function fields over `K` and the product formula
--   * `Def_RP_JacRRFam_F`: Places over an arbitrary field, part F: divisors, the product formula, the constant field
--   * `Def_RP_JacComplete_PlaceF`: The Jacobian (unit S4-JacComplete), part `PlaceF` (dictionary D1 for a function field `F / K(x)`)
--   * `Def_RP_JacComplete_Sep`: The Jacobian (unit S4-JacComplete), part `Sep` (tools for separating elements; Mathlib only)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S3_RRA
import Definitions.Def_RPLib_S3_PlacesC

/-!
# Curve-duality library package, part 17 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_PlaceVal`: The Jacobian (unit S4-JacComplete), part `PlaceVal` (dictionary D1, generic valuation theory)
* `Def_RP_JacRRFam_A`: Riemann-Roch over an arbitrary constant field, part A (unit S4-JacRRFam)
* `Def_RP_JacRRFam_C`: Places over an arbitrary field, part C: dimensions of quotients of Dedekind domains
* `Def_RP_JacRRFam_D`: Places over an arbitrary field, part D: Dedekind domains with finite-dimensional quotients
* `Def_RP_JacRRFam_E`: Places over an arbitrary field, part E: function fields over `K` and the product formula
* `Def_RP_JacRRFam_F`: Places over an arbitrary field, part F: divisors, the product formula, the constant field
* `Def_RP_JacComplete_PlaceF`: The Jacobian (unit S4-JacComplete), part `PlaceF` (dictionary D1 for a function field `F / K(x)`)
* `Def_RP_JacComplete_Sep`: The Jacobian (unit S4-JacComplete), part `Sep` (tools for separating elements; Mathlib only)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_PlaceVal =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PlaceVal` (dictionary D1, generic valuation theory)

* `val_le_one_of_isIntegral`: `w ≤ 1` on the image of `S` and `y` integral over `S` give `w y ≤ 1`;
* `val_eq_of_isEquiv`: two equivalent `ℤᵐ⁰`-valuations with `exp (-1)` uniformizers are equal;
* `valuation_eq_of_le`: if `w ≤ 1` on a Dedekind domain `R ⊆ F` and `w = 1` off the prime `p`, then `v_p = w`;
* **`exists_heightOneSpectrum_valuation_eq`**: a normalized discrete valuation `w ≤ 1` on `R` is `v_p` for
  `p = {r | w r < 1}`.
-/

set_option autoImplicit false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.JacComplete

section PlaceVal

theorem val_le_one_of_isIntegral {F S : Type*} [Field F] [CommRing S] [Algebra S F] (w : Valuation F ℤᵐ⁰)
    (hS : ∀ s : S, w (algebraMap S F s) ≤ 1) {y : F} (hy : IsIntegral S y) : w y ≤ 1 := by
  obtain ⟨f, hm, hf⟩ := hy
  by_cases hn : f.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hm hn, eval₂_one] at hf
    exact absurd hf one_ne_zero
  simp only [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one,
    one_mul, add_eq_zero_iff_eq_neg] at hf
  apply_fun w at hf
  simp only [Valuation.map_neg, map_pow] at hf
  contrapose! hf
  refine ne_of_lt (w.map_sum_lt ?_ ?_)
  · simp [hn, (hf.trans' (zero_lt_one)).ne']
  · simp only [Finset.mem_range, map_mul, map_pow]
    intro _ hi
    exact mul_lt_of_le_one_of_lt (hS _) <| pow_lt_pow_right₀ hf hi

/-- Equivalent `ℤᵐ⁰`-valuations with `exp (-1)` uniformizers are equal. -/
theorem val_eq_of_isEquiv {F : Type*} [Field F] {v w : Valuation F ℤᵐ⁰} (h : v.IsEquiv w)
    {π : F} (hπ : v π = WithZero.exp (-1 : ℤ)) {ϖ : F} (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) : v = w := by
  have hπ0 : π ≠ 0 := (Valuation.ne_zero_iff v).1 (by rw [hπ]; exact WithZero.exp_ne_zero)
  have key : ∀ f : F, f ≠ 0 → w f = w π ^ (-(WithZero.log (v f))) := by
    intro f hf
    have hvf : v f = v (π ^ (-(WithZero.log (v f)))) := by
      rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul,
        show -WithZero.log (v f) * (-1 : ℤ) = WithZero.log (v f) by ring]
      exact (WithZero.exp_log ((Valuation.ne_zero_iff v).2 hf)).symm
    rw [h.eq_iff.1 hvf, map_zpow₀]
  have hwπ0 : w π ≠ 0 := (Valuation.ne_zero_iff w).2 hπ0
  have hwπ : w π = WithZero.exp (-1 : ℤ) := by
    have hl : w π = WithZero.exp (WithZero.log (w π)) := (WithZero.exp_log hwπ0).symm
    have hlt : w π < 1 := by
      have : v π < 1 := by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
      exact h.lt_one_iff_lt_one.1 this
    have hneg : WithZero.log (w π) < 0 := by
      rw [hl, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      exact hlt
    have hϖ0 : ϖ ≠ 0 := (Valuation.ne_zero_iff w).1 (by rw [hϖ]; exact WithZero.exp_ne_zero)
    have e := key ϖ hϖ0
    rw [hϖ, hl, ← WithZero.exp_zsmul, smul_eq_mul, WithZero.exp_inj] at e
    have hml : WithZero.log (v ϖ) * WithZero.log (w π) = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hml with ⟨_, h2⟩ | ⟨_, h2⟩
    · omega
    · rw [hl, h2]
  ext f
  by_cases hf : f = 0
  · rw [hf, map_zero, map_zero]
  rw [key f hf, hwπ, ← WithZero.exp_zsmul, smul_eq_mul,
    show -WithZero.log (v f) * (-1 : ℤ) = WithZero.log (v f) by ring]
  exact (WithZero.exp_log ((Valuation.ne_zero_iff v).2 hf)).symm

/-- If `w ≤ 1` on `R` and `w = 1` off `p`, then `v_p = w` (a DVR is maximal among proper valuation subrings). -/
theorem valuation_eq_of_le {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (p : HeightOneSpectrum R) (w : Valuation F ℤᵐ⁰) {ϖ : F}
    (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) (hle : ∀ r : R, w (algebraMap R F r) ≤ 1)
    (hlt : ∀ r : R, r ∉ p.asIdeal → w (algebraMap R F r) = 1) : p.valuation F = w := by
  have hsub : HeightOneSpectrum.valuationSubringAtPrime F p ≤ w.valuationSubring := by
    rintro x ⟨a, s, hs, rfl⟩
    rw [Valuation.mem_valuationSubring_iff, map_mul, map_inv₀, hlt s hs, inv_one, mul_one]
    exact hle a
  have hne : w.valuationSubring ≠ ⊤ := by
    intro htop
    have hmem : ϖ⁻¹ ∈ w.valuationSubring := by rw [htop]; exact ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hϖ, ← WithZero.exp_neg, neg_neg,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
    omega
  have heq := ValuationSubring.eq_of_le_of_ne_top _ hsub hne
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at heq
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer F
  exact val_eq_of_isEquiv ((Valuation.isEquiv_iff_valuationSubring _ _).2 heq) hπ hϖ

/-- **A normalized discrete valuation `≤ 1` on a Dedekind domain `R` is the valuation of a height-one prime.** -/
theorem exists_heightOneSpectrum_valuation_eq {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (w : Valuation F ℤᵐ⁰) {ϖ : F} (hϖ : w ϖ = WithZero.exp (-1 : ℤ))
    (hle : ∀ r : R, w (algebraMap R F r) ≤ 1) : ∃ p : HeightOneSpectrum R, p.valuation F = w := by
  let I : Ideal R :=
    { carrier := {r | w (algebraMap R F r) < 1}
      add_mem' := fun {a b} ha hb => by
        show w (algebraMap R F (a + b)) < 1
        rw [map_add]
        exact lt_of_le_of_lt (w.map_add _ _) (max_lt ha hb)
      zero_mem' := by
        show w (algebraMap R F 0) < 1
        rw [map_zero, map_zero]
        exact zero_lt_one
      smul_mem' := fun c x hx => by
        show w (algebraMap R F (c • x)) < 1
        rw [smul_eq_mul, map_mul, map_mul]
        exact mul_lt_of_le_one_of_lt (hle c) hx }
  have hmemI : ∀ r : R, r ∈ I ↔ w (algebraMap R F r) < 1 := fun r => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmemI, map_one, map_one]
      exact lt_irrefl 1
    · intro a b hab
      rw [hmemI, map_mul, map_mul] at hab
      rw [hmemI, hmemI]
      rcases lt_or_eq_of_le (hle a) with ha | ha
      · exact Or.inl ha
      rcases lt_or_eq_of_le (hle b) with hb | hb
      · exact Or.inr hb
      rw [ha, hb, one_mul] at hab
      exact absurd hab (lt_irrefl 1)
  have hϖ0 : ϖ ≠ 0 := (Valuation.ne_zero_iff w).1 (by rw [hϖ]; exact WithZero.exp_ne_zero)
  have hne : I ≠ ⊥ := by
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) ϖ
    have hb0 : algebraMap R F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    intro hbot
    have ha : a ∈ I := by
      rw [hmemI]
      have e : algebraMap R F a = ϖ * algebraMap R F b := by
        rw [← hab]
        field_simp
      rw [e, map_mul, hϖ]
      have h1 : WithZero.exp (-1 : ℤ) * w (algebraMap R F b) ≤ WithZero.exp (-1 : ℤ) := by
        first
          | exact mul_le_of_le_one_right' (hle b)
          | exact mul_le_of_le_one_right zero_le' (hle b)
      exact lt_of_le_of_lt h1 (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    rw [hbot, Ideal.mem_bot] at ha
    rw [ha, map_zero, zero_div] at hab
    exact hϖ0 hab.symm
  refine ⟨⟨I, hprime, hne⟩, valuation_eq_of_le _ w hϖ hle fun r hr => ?_⟩
  exact le_antisymm (hle r) (not_lt.1 hr)

end PlaceVal

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacRRFam_A =====
section

/-!
# Riemann-Roch over an arbitrary constant field, part A (unit S4-JacRRFam)

The abstract repartition calculus of `RamanujanPetersson.RR` (lib/S3/RR_A, RR_B) counts with
`AddSubgroup.relIndex` over a FINITE field.  Here the counting layer is redone over an ARBITRARY
field `K` (for instance a non-perfect function field `K = k(V)`) with the `ℕ∞`-valued codimension
`cd H H' = dim_K H' / (H ∩ H')`.  The definitions of part A of S3 (`Data`, `ball`, `AD`, `adeles`,
`Fs`, `LD`, `ell`, `div`, `degD`) are reused unchanged.

Main results: the codimension calculus (`cd_add`, `cd_split`, `cd_comap`, `cd_map_of_injective`,
`cd_eq_zero_iff`, `cd_of_le_fd`, `fd_of_cd`), the axioms `Data.AxiomsK0` / `Data.AxiomsK`
(local index `cd (ball i n) (ball i (n+1)) = deg i`), and the global index computation
`cd_AD_le`, `finite_LDK`, `ell_sub_leK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero Module

namespace RamanujanPetersson.RR

/-! ### The codimension of two subspaces -/

section Codim

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The codimension of `H ∩ H'` in `H'`, as an element of `ℕ∞` (`⊤` when infinite). -/
noncomputable def cd (H H' : Submodule K V) : ℕ∞ :=
  Cardinal.toENat (Module.rank K (H' ⧸ H.comap H'.subtype))

theorem cd_ker {W : Type*} [AddCommGroup W] [Module K W] (g : V →ₗ[K] W) (H' : Submodule K V) :
    cd (LinearMap.ker g) H' = Cardinal.toENat (Module.rank K (H'.map g)) := by
  have e1 : (LinearMap.ker g).comap H'.subtype = LinearMap.ker (g.domRestrict H') :=
    (LinearMap.ker_domRestrict H' g).symm
  have h := (g.domRestrict H').quotKerEquivRange.lift_rank_eq
  rw [LinearMap.range_domRestrict, ← e1] at h
  have h2 := congrArg Cardinal.toENat h
  simp only [Cardinal.toENat_lift] at h2
  exact h2

theorem cd_eq_map (H H' : Submodule K V) :
    cd H H' = Cardinal.toENat (Module.rank K (H'.map H.mkQ)) := by
  rw [← cd_ker, Submodule.ker_mkQ]

theorem cd_inf_right (H H' : Submodule K V) : cd (H ⊓ H') H' = cd H H' := by
  unfold cd
  rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]

theorem cd_sup_left (H X : Submodule K V) : cd H (H ⊔ X) = cd H X := by
  rw [cd_eq_map, cd_eq_map, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]

theorem cd_comap {W : Type*} [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (B : Submodule K W)
    (H' : Submodule K V) : cd (B.comap f) H' = cd B (H'.map f) := by
  rw [cd_eq_map B, ← Submodule.map_comp, ← cd_ker, LinearMap.ker_comp, Submodule.ker_mkQ]

theorem cd_map_of_injective {W : Type*} [AddCommGroup W] [Module K W] (f : V →ₗ[K] W)
    (hf : Function.Injective f) (H H' : Submodule K V) : cd (H.map f) (H'.map f) = cd H H' := by
  rw [← cd_comap, Submodule.comap_map_eq_of_injective hf]

theorem cd_eq_zero_iff {H H' : Submodule K V} : cd H H' = 0 ↔ H' ≤ H := by
  rw [cd_eq_map, Cardinal.toENat_eq_zero, Submodule.rank_eq_zero, ← LinearMap.le_ker_iff_map,
    Submodule.ker_mkQ]

@[simp] theorem cd_self (H : Submodule K V) : cd H H = 0 := cd_eq_zero_iff.2 le_rfl

/-- Additivity of codimension along `H1 ≤ H2 ≤ H3`. -/
theorem cd_add {H1 H2 H3 : Submodule K V} (h12 : H1 ≤ H2) (h23 : H2 ≤ H3) :
    cd H1 H2 + cd H2 H3 = cd H1 H3 := by
  rw [cd_eq_map, cd_eq_map, cd_eq_map]
  have hq : H1 ≤ H2.comap LinearMap.id := by rw [Submodule.comap_id]; exact h12
  set φ : (V ⧸ H1) →ₗ[K] (V ⧸ H2) := H1.mapQ H2 LinearMap.id hq
  set S := H3.map H1.mkQ with hS
  have hr : LinearMap.range (φ.domRestrict S) = H3.map H2.mkQ := by
    rw [LinearMap.range_domRestrict, hS, ← Submodule.map_comp, Submodule.mapQ_mkQ,
      LinearMap.comp_id]
  have hk : LinearMap.ker (φ.domRestrict S) = (H2.map H1.mkQ).comap S.subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mapQ, Submodule.comap_id]
  have hle : H2.map H1.mkQ ≤ S := Submodule.map_mono h23
  have h := LinearMap.rank_range_add_rank_ker (φ.domRestrict S)
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hle).rank_eq] at h
  rw [← h, map_add, add_comm]

/-- `cd H H' = cd (H ⊓ C) (H' ⊓ C) + cd (H ⊔ C) (H' ⊔ C)` for `H ≤ H'`. -/
theorem cd_split {H H' : Submodule K V} (C : Submodule K V) (h : H ≤ H') :
    cd H H' = cd (H ⊓ C) (H' ⊓ C) + cd (H ⊔ C) (H' ⊔ C) := by
  have h1 : H ≤ H ⊔ (H' ⊓ C) := le_sup_left
  have h2 : H ⊔ (H' ⊓ C) ≤ H' := sup_le h inf_le_left
  rw [← cd_add h1 h2]
  congr 1
  · rw [cd_sup_left, ← cd_inf_right H (H' ⊓ C), ← inf_assoc, inf_eq_left.2 h]
  · have hmod : H ⊔ (H' ⊓ C) = (H ⊔ C) ⊓ H' := by rw [inf_comm]; exact (sup_inf_assoc_of_le C h).symm
    rw [hmod, cd_inf_right, ← cd_sup_left (H ⊔ C) H']
    congr 1
    apply le_antisymm
    · exact sup_le (sup_le (h.trans le_sup_left) le_sup_right) le_sup_left
    · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)

/-- For `H ≤ H'` with `H'` finite-dimensional, `cd H H' = dim H' - dim H`. -/
theorem cd_of_le_fd {H H' : Submodule K V} (h : H ≤ H') [FiniteDimensional K H'] :
    finrank K H ≤ finrank K H' ∧ cd H H' = ((finrank K H' - finrank K H : ℕ) : ℕ∞) := by
  have h1 := Submodule.finrank_quotient_add_finrank (H.comap H'.subtype)
  rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq] at h1
  refine ⟨by omega, ?_⟩
  unfold cd
  rw [← Module.finrank_eq_rank, map_natCast]
  congr 1
  omega

/-- If `H ≤ H'`, `H` is finite-dimensional and `cd H H' < ⊤`, then `H'` is finite-dimensional. -/
theorem fd_of_cd {H H' : Submodule K V} (h : H ≤ H') [FiniteDimensional K H] (hc : cd H H' ≠ ⊤) :
    FiniteDimensional K H' := by
  have h1 := rank_quotient_add_rank_of_divisionRing (H.comap H'.subtype)
  rw [(Submodule.comapSubtypeEquivOfLe h).rank_eq] at h1
  have hq : Module.rank K (H' ⧸ H.comap H'.subtype) < Cardinal.aleph0 := by
    unfold cd at hc
    rw [Ne, Cardinal.toENat_eq_top, not_le] at hc
    exact hc
  have hH : Module.rank K H < Cardinal.aleph0 := Module.rank_lt_aleph0 K H
  have hH' : Module.rank K H' < Cardinal.aleph0 := h1 ▸ Cardinal.add_lt_aleph0 hq hH
  exact Module.rank_lt_aleph0_iff.1 hH'

theorem enat_add_eq {m n : ℕ} {b : ℕ∞} (h : (m : ℕ∞) + b = n) :
    m ≤ n ∧ b = ((n - m : ℕ) : ℕ∞) := by
  have hb : b ≠ ⊤ := by
    rintro rfl
    simp at h
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hb
  have : m + k = n := by exact_mod_cast h
  refine ⟨by omega, ?_⟩
  congr 1
  omega

end Codim

/-! ### The axioms over an arbitrary field and the global index -/

namespace Data

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F] (d : Data K F ι)

theorem cd_AD_single (D : ι →₀ ℤ) (i : ι) :
    cd (d.AD D) (d.AD (D + Finsupp.single i 1)) = cd (d.ball i (D i)) (d.ball i (D i + 1)) := by
  classical
  set D' := D + Finsupp.single i 1 with hD'
  have hsi : ∀ j, j ≠ i → D' j = D j := fun j hj => by
    simp [hD', Ne.symm hj]
  have hii : D' i = D i + 1 := by simp [hD']
  let ev : (ι → F) →ₗ[K] F := LinearMap.proj i
  have hAD : d.AD D = (d.ball i (D i)).comap ev ⊓ d.AD D' := by
    ext α
    simp only [Submodule.mem_inf, Submodule.mem_comap, mem_AD, mem_ball, ev, LinearMap.proj_apply]
    constructor
    · intro h
      refine ⟨h i, fun j => (h j).trans (exp_le_exp.2 ?_)⟩
      by_cases hj : j = i
      · subst hj; rw [hii]; omega
      · rw [hsi j hj]
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; exact h1
      · simpa [hsi j hj] using h2 j
  have hmap : (d.AD D').map ev = d.ball i (D i + 1) := by
    ext f
    simp only [Submodule.mem_map, mem_AD, mem_ball, ev, LinearMap.proj_apply]
    constructor
    · rintro ⟨α, hα, rfl⟩; simpa [hii] using hα i
    · intro hf
      refine ⟨Pi.single i f, fun j => ?_, by simp⟩
      by_cases hj : j = i
      · subst hj; simpa [hii] using hf
      · simp [hj]
  rw [hAD, cd_inf_right, cd_comap, hmap]

/-- The local axioms over an arbitrary field `K`: places exist and have positive degree, the
local index `dim (ball i (n+1) / ball i n) = deg i`, the product formula and `dim L(0) < ∞`. -/
structure AxiomsK0 : Prop where
  nonempty : Nonempty ι
  deg_pos : ∀ i, 0 < d.deg i
  localIndex : ∀ i (n : ℤ), cd (d.ball i n) (d.ball i (n + 1)) = d.deg i
  deg_div : ∀ f : F, f ≠ 0 → d.degD (d.div f) = 0
  finite_L0 : FiniteDimensional K (d.LD 0)

/-- The axioms over an arbitrary field: the local axioms plus the input for Riemann's inequality
(as in `Data.Axioms`). -/
structure AxiomsK : Prop extends AxiomsK0 d where
  riemannInput : ∃ B : ι →₀ ℤ, 0 ≤ B ∧ 0 < d.degD B ∧ ∃ C : ι →₀ ℤ, 0 ≤ C ∧
    ∃ c : ℤ, ∀ n : ℕ, (n : ℤ) * d.degD B - c ≤ d.ell (n • B + C)

variable {d}

theorem cd_AD_add_single_nat (hd : d.AxiomsK0) (D : ι →₀ ℤ) (i : ι) (n : ℕ) :
    cd (d.AD D) (d.AD (D + Finsupp.single i (n : ℤ))) = ((n * d.deg i : ℕ) : ℕ∞) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : D + Finsupp.single i ((n + 1 : ℕ) : ℤ) =
        (D + Finsupp.single i (n : ℤ)) + Finsupp.single i 1 := by
      rw [Nat.cast_succ, Finsupp.single_add, add_assoc]
    rw [e, ← cd_add (d.AD_mono (le_add_of_nonneg_right
        (Finsupp.single_nonneg.2 (Nat.cast_nonneg _))))
      (d.AD_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one))), ih,
      d.cd_AD_single, hd.localIndex]
    push_cast
    ring

theorem cd_AD_add (hd : d.AxiomsK0) {E : ι →₀ ℤ} (hE : 0 ≤ E) (D : ι →₀ ℤ) :
    cd (d.AD D) (d.AD (D + E)) = ((d.degD E).toNat : ℕ∞) := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero => simp
  | single_add a b f ha hb ih =>
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    have hb0 : 0 ≤ b := by have := hE a; simpa [hfa] using this
    have hf0 : 0 ≤ f := fun j => by
      by_cases hj : j = a
      · subst hj; simp [hfa]
      · have := hE j; simpa [Finsupp.single_apply, Ne.symm hj] using this
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
    rw [← add_assoc, ← cd_add (d.AD_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.2 hb0)))
      (d.AD_mono (le_add_of_nonneg_right hf0)), cd_AD_add_single_nat hd, ih hf0, ← Nat.cast_add,
      degD_add, degD_single]
    congr 1
    have hdf := d.degD_nonneg hf0
    have hm : ((k : ℤ) * (d.deg a : ℤ)) = ((k * d.deg a : ℕ) : ℤ) := by push_cast; ring
    rw [hm]
    generalize k * d.deg a = m
    omega

/-- `dim A(D') / A(D) = deg D' - deg D`. -/
theorem cd_AD_le (hd : d.AxiomsK0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    cd (d.AD D) (d.AD D') = ((d.degD D' - d.degD D).toNat : ℕ∞) := by
  have := cd_AD_add hd (sub_nonneg.2 h) D
  rwa [add_sub_cancel, degD_sub] at this

theorem cd_LD [Nonempty ι] (D E : ι →₀ ℤ) :
    cd (d.LD D) (d.LD E) = cd (d.AD D ⊓ d.Fs) (d.AD E ⊓ d.Fs) := by
  rw [← d.map_LD, ← d.map_LD, cd_map_of_injective _ d.const_injective]

theorem cd_LD_add (hd : d.AxiomsK0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    cd (d.LD D) (d.LD D') + cd (d.AD D ⊔ d.Fs) (d.AD D' ⊔ d.Fs) =
      ((d.degD D' - d.degD D).toNat : ℕ∞) := by
  have := hd.nonempty
  rw [cd_LD, ← cd_split _ (d.AD_mono h), cd_AD_le hd h]

/-- `L(D)` is finite-dimensional. -/
theorem finite_LDK (hd : d.AxiomsK0) (D : ι →₀ ℤ) : FiniteDimensional K (d.LD D) := by
  have := hd.finite_L0
  have h1 : (0 : ι →₀ ℤ) ≤ D ⊔ 0 := le_sup_right
  have h2 : D ≤ D ⊔ 0 := le_sup_left
  have hne : cd (d.LD 0) (d.LD (D ⊔ 0)) ≠ ⊤ := by
    intro h0
    have := cd_LD_add hd h1
    rw [h0, top_add] at this
    exact ENat.top_ne_natCast _ this
  have : FiniteDimensional K (d.LD (D ⊔ 0)) := fd_of_cd (d.LD_mono h1) hne
  exact Submodule.finiteDimensional_of_le (d.LD_mono h2)

theorem ell_le_of_leK (hd : d.AxiomsK0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    d.ell D ≤ d.ell D' ∧ cd (d.LD D) (d.LD D') = ((d.ell D' - d.ell D : ℕ) : ℕ∞) := by
  have := finite_LDK hd D'
  exact cd_of_le_fd (d.LD_mono h)

/-- `ℓ(D') - ℓ(D) ≤ deg D' - deg D` for `D ≤ D'`, and the codimension of `A(D) + F` in `A(D') + F`. -/
theorem ell_sub_leK (hd : d.AxiomsK0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    (d.ell D' : ℤ) - d.ell D ≤ d.degD D' - d.degD D ∧
    cd (d.AD D ⊔ d.Fs) (d.AD D' ⊔ d.Fs) =
      (((d.degD D' - d.degD D).toNat - (d.ell D' - d.ell D) : ℕ) : ℕ∞) := by
  obtain ⟨hle, hr⟩ := ell_le_of_leK hd h
  have := cd_LD_add hd h
  rw [hr] at this
  obtain ⟨h1, h2⟩ := enat_add_eq this
  refine ⟨?_, h2⟩
  have := d.degD_mono h
  omega

end Data

end RamanujanPetersson.RR

end

-- ===== S4.Def_RP_JacRRFam_C =====
section

/-!
# Places over an arbitrary field, part C: dimensions of quotients of Dedekind domains

For a Dedekind domain `S` that is an algebra over a field `K`, `dq K I = dim_K (S ⧸ I)` (in `ℕ∞`)
is additive on products of nonzero ideals (`dq_mul`), so `dim_K S/(a) = Σ_P cnt_P(a) deg P`
(`finrank_quot_span`). This replaces the cardinality counting of S3-Places (which needs a finite
field). Also: `dim_K Oinf/(y) = -intDegree y` for the valuation ring at infinity of `K(x)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.PlacesK

open RamanujanPetersson.RR (cd cd_add cd_sup_left cd_comap cd_eq_zero_iff cd_eq_map)
open RamanujanPetersson.Places (Oinf piInf ord cnt ord_algebraMap mem_Oinf_iff' coe_piInf
  X_ne_zero' span_piInf_isMaximal residue_bijective piInf_ne_zero)

section DimQuot

variable (K : Type*) [Field K] {S : Type*} [CommRing S] [Algebra K S]

/-- `dim_K (S ⧸ I)` in `ℕ∞`. -/
noncomputable def dq (I : Ideal S) : ℕ∞ := cd (I.restrictScalars K) ⊤

variable {K}

theorem dq_eq_rank (I : Ideal S) : dq K I = Cardinal.toENat (Module.rank K (S ⧸ I)) := by
  unfold dq
  rw [cd_eq_map, Submodule.map_top, Submodule.range_mkQ, rank_top,
    (Submodule.Quotient.restrictScalarsEquiv K I).rank_eq]

theorem dq_top : dq K (⊤ : Ideal S) = 0 := by
  unfold dq; exact cd_eq_zero_iff.2 fun x _ => Submodule.mem_top

theorem dq_anti {I J : Ideal S} (h : I ≤ J) : dq K J ≤ dq K I := by
  have h' : I.restrictScalars K ≤ J.restrictScalars K := fun x hx => h hx
  unfold dq
  rw [← cd_add h' le_top]
  exact le_add_self

variable [IsDedekindDomain S]

theorem dq_mul_prime {I P : Ideal S} (hI' : I ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    dq K (I * P) = dq K I + dq K P := by
  have hI : I ≠ 0 := by rwa [Ideal.zero_eq_bot]
  have hmax : P.IsMaximal := hP.isMaximal hP0
  have hle : I * P ≤ I := Ideal.mul_le_left
  have hlt : I * P < I := by
    refine lt_of_le_of_ne hle fun h => hP.ne_top ?_
    have h2 : I * P = I * ⊤ := by rw [Ideal.mul_top]; exact h
    exact mul_left_cancel₀ hI h2
  obtain ⟨x, hxI, hxIP⟩ := SetLike.exists_of_lt hlt
  have hsup : Ideal.span {x} ⊔ I * P = I := by
    have hJle : Ideal.span {x} ⊔ I * P ≤ I :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).2 hxI) hle
    obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 hJle
    have hPQ : P ≤ Q := by
      have h1 : I * Q ∣ I * P := Ideal.dvd_iff_le.2 (le_sup_right.trans hQ.le)
      exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left hI).1 h1)
    by_cases hQt : Q = ⊤
    · rw [hQ, hQt, Ideal.mul_top]
    · have hPQ' := hmax.eq_of_le hQt hPQ
      have hx' : x ∈ Ideal.span {x} ⊔ I * P :=
        Submodule.mem_sup_left (Ideal.mem_span_singleton_self x)
      rw [hQ, ← hPQ'] at hx'
      exact absurd hx' hxIP
  -- the `K`-linear map `s ↦ x * s`
  set φ : S →ₗ[K] S := LinearMap.mulLeft K x with hφ
  have hrange : I.restrictScalars K = (I * P).restrictScalars K ⊔ LinearMap.range φ := by
    apply le_antisymm
    · intro y hy
      have hy' : y ∈ Ideal.span {x} ⊔ I * P := hsup.symm ▸ hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [add_comm]
      exact Submodule.add_mem_sup hb ⟨s, by simp [hφ, mul_comm]⟩
    · refine sup_le (fun y hy => hle hy) ?_
      rintro _ ⟨s, rfl⟩
      exact I.mul_mem_right s hxI
  have hcomap : ((I * P).restrictScalars K).comap φ = P.restrictScalars K := by
    ext s
    simp only [Submodule.mem_comap, Submodule.restrictScalars_mem, hφ, LinearMap.mulLeft_apply]
    constructor
    · intro hs
      by_contra hsP
      obtain ⟨t, i, hi, hti⟩ := hmax.exists_inv hsP
      apply hxIP
      have e : x = t * (x * s) + x * i := by
        calc x = x * (t * s + i) := by rw [hti, mul_one]
          _ = t * (x * s) + x * i := by ring
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ t hs) (Ideal.mul_mem_mul hxI hi)
    · intro hs
      exact Ideal.mul_mem_mul hxI hs
  have h12 : (I * P).restrictScalars K ≤ I.restrictScalars K := fun y hy => hle hy
  unfold dq
  rw [← cd_add h12 le_top, add_comm]
  congr 1
  rw [hrange, cd_sup_left, LinearMap.range_eq_map, ← cd_comap, hcomap]

theorem dq_mul {I J : Ideal S} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : dq K (I * J) = dq K I + dq K J := by
  have key : ∀ J : Ideal S, J ≠ ⊥ → ∀ I : Ideal S, I ≠ ⊥ → dq K (I * J) = dq K I + dq K J := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime J ?_ ?_ ?_
    · intro h; exact absurd Ideal.zero_eq_bot h
    · intro x hx _ I _
      rw [Ideal.isUnit_iff.1 hx, Ideal.mul_top, dq_top, add_zero]
    · intro a p ha hp ih _ I hI
      have hp0 : p ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact hp.ne_zero
      have ha' : a ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact ha
      have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hp0).1 hp
      have hI0 : I ≠ 0 := by rwa [Ideal.zero_eq_bot]
      have hIa : I * a ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact mul_ne_zero hI0 ha
      rw [show I * (p * a) = (I * a) * p by ring, dq_mul_prime hIa hpP hp0, ih ha' I hI,
        mul_comm p a, dq_mul_prime ha' hpP hp0, ← add_assoc]
  exact key J hJ I hI

theorem dq_pow {P : Ideal S} (hP : P ≠ ⊥) (n : ℕ) : dq K (P ^ n) = n * dq K P := by
  induction n with
  | zero => simp [dq_top]
  | succ n ih =>
    have hP0 : P ≠ 0 := by rwa [Ideal.zero_eq_bot]
    have hn : P ^ n ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact pow_ne_zero n hP0
    rw [pow_succ, dq_mul hn hP, ih]
    push_cast; ring

theorem dq_prod {ι : Type*} (s : Finset ι) (f : ι → Ideal S) (hf : ∀ i ∈ s, f i ≠ ⊥) :
    dq K (∏ i ∈ s, f i) = ∑ i ∈ s, dq K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dq_top]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      dq_mul (hf a (Finset.mem_insert_self a s))
        (by
          rw [← Ideal.zero_eq_bot]
          exact Finset.prod_ne_zero_iff.2 fun i hi => by
            rw [Ideal.zero_eq_bot]; exact hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end DimQuot

end RamanujanPetersson.PlacesK

end

-- ===== S4.Def_RP_JacRRFam_D =====
section

/-!
# Places over an arbitrary field, part D: Dedekind domains with finite-dimensional quotients

`FDQ K S`: every `S ⧸ (a)`, `a ≠ 0`, is finite-dimensional over `K`. Then `deg K P = dim_K S/P > 0`,
`ord`, `divS` (Fintype-free copies of S3-Places), and `dim_K S/(a) = Σ_P cnt_P(a) deg P`
(`finrank_quot_span`). For `Oinf K`: `dim_K Oinf/(y) = -intDegree y` (`finrank_quot_Oinf`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.PlacesK

open RamanujanPetersson.Places (Oinf piInf ord cnt deg degS mem_Oinf_iff' coe_piInf X_ne_zero'
  span_piInf_isMaximal residue_bijective piInf_ne_zero)

section Generic

variable (K : Type*) [Field K] (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra K S]

/-- Nonzero principal quotients are finite-dimensional over `K`. -/
class FDQ : Prop where
  finite : ∀ a : S, a ≠ 0 → Module.Finite K (S ⧸ Ideal.span {a})

variable {K S}

theorem moduleFinite_residue [FDQ K S] (P : HeightOneSpectrum S) :
    Module.Finite K (S ⧸ P.asIdeal) := by
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  have := FDQ.finite (K := K) a ha0
  have hle : Ideal.span {a} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 haP
  exact Module.Finite.of_surjective ((Ideal.Quotient.factorₐ K hle).toLinearMap)
    (Ideal.Quotient.factor_surjective hle)

theorem dq_eq_finrank {I : Ideal S} (h : Module.Finite K (S ⧸ I)) :
    dq K I = (finrank K (S ⧸ I) : ℕ∞) := by
  rw [dq_eq_rank, ← Module.finrank_eq_rank]
  simp

theorem dq_asIdeal [FDQ K S] (P : HeightOneSpectrum S) : dq K P.asIdeal = (deg K P : ℕ∞) :=
  dq_eq_finrank (moduleFinite_residue P)

theorem deg_pos [FDQ K S] (P : HeightOneSpectrum S) : 0 < deg K P := by
  have := moduleFinite_residue (K := K) P
  have : Nontrivial (S ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  exact Module.finrank_pos

variable {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L]

theorem ord_algebraMap (P : HeightOneSpectrum S) {a : S} (ha : a ≠ 0) :
    ord P (algebraMap S L a) = cnt P a := by
  rw [ord, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg ha,
    WithZero.log_exp, neg_neg, cnt]

theorem ord_mul (P : HeightOneSpectrum S) {f g : L} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f * g) = ord P f + ord P g := by
  rw [ord, ord, ord, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hf)
    ((Valuation.ne_zero_iff _).mpr hg)]; ring

theorem ord_div (P : HeightOneSpectrum S) {f g : L} (hf : f ≠ 0) (hg : g ≠ 0) :
    ord P (f / g) = ord P f - ord P g := by
  rw [ord, ord, ord, map_div₀, WithZero.log_div ((Valuation.ne_zero_iff _).mpr hf)
    ((Valuation.ne_zero_iff _).mpr hg)]; ring

theorem finite_cnt {a : S} (ha : a ≠ 0) : {P : HeightOneSpectrum S | cnt P a ≠ 0}.Finite := by
  have h := Filter.eventually_cofinite.mp (Associates.finite_factors (I := Ideal.span {a})
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]))
  refine h.subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq, cnt] at hP ⊢
  exact_mod_cast hP

theorem finite_ord (f : L) : {P : HeightOneSpectrum S | ord P f ≠ 0}.Finite := by
  by_cases hf : f = 0
  · simp [hf, ord]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hf
  have ha' : algebraMap S L a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr ha0
  have hb' : algebraMap S L b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).mpr hb0
  refine ((finite_cnt ha0).union (finite_cnt hb0)).subset fun P hP => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hP ⊢
  rw [ord_div P ha' hb', ord_algebraMap P ha0, ord_algebraMap P hb0] at hP
  by_contra hcon
  push Not at hcon
  rw [hcon.1, hcon.2] at hP
  simp at hP

variable (S) in
/-- The divisor of `f` restricted to the places of `S`. -/
noncomputable def divS (f : L) : HeightOneSpectrum S →₀ ℤ :=
  Finsupp.ofSupportFinite (fun P => ord P f) (finite_ord f)

@[simp] theorem divS_apply (f : L) (P : HeightOneSpectrum S) : divS S f P = ord P f := rfl

theorem degS_sub (D E : HeightOneSpectrum S →₀ ℤ) : degS K (D - E) = degS K D - degS K E := by
  unfold degS
  rw [Finsupp.sum_sub_index]
  intro P a b; ring

theorem divS_div {f g : L} (hf : f ≠ 0) (hg : g ≠ 0) : divS S (f / g) = divS S f - divS S g := by
  ext P; simp [ord_div P hf hg]

/-- `dim_K S/(a) = Σ_P cnt_P(a) deg P`, in `ℕ∞`. -/
theorem dq_span_eq [FDQ K S] {a : S} (ha : a ≠ 0) :
    dq K (Ideal.span {a}) = ((∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg K P : ℕ) : ℕ∞) := by
  have hI : Ideal.span {a} ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hfac := Ideal.finprod_heightOneSpectrum_factorization hI
  rw [finprod_eq_prod_of_mulSupport_subset (s := (finite_cnt ha).toFinset)] at hfac
  · conv_lhs => rw [← hfac]
    rw [dq_prod _ _ fun P _ => by
      simp only [HeightOneSpectrum.maxPowDividing]
      rw [← Ideal.zero_eq_bot]; exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact P.ne_bot)]
    push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    simp only [HeightOneSpectrum.maxPowDividing]
    rw [dq_pow P.ne_bot, dq_asIdeal, cnt]
  · intro P hP
    simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
    intro h0
    apply hP
    simp [HeightOneSpectrum.maxPowDividing, cnt] at h0 ⊢
    simp [h0]

theorem finrank_quot_span [FDQ K S] {a : S} (ha : a ≠ 0) :
    finrank K (S ⧸ Ideal.span {a}) = ∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg K P := by
  have h := dq_span_eq (K := K) ha
  rw [dq_eq_finrank (FDQ.finite a ha)] at h
  exact_mod_cast h

theorem degS_divS_algebraMap {a : S} (ha : a ≠ 0) :
    degS K (divS S (algebraMap S L a)) =
      ((∑ P ∈ (finite_cnt ha).toFinset, cnt P a * deg K P : ℕ) : ℤ) := by
  unfold degS
  rw [Finsupp.sum_of_support_subset (s := (finite_cnt ha).toFinset)]
  · push_cast
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [divS_apply, ord_algebraMap P ha]
  · intro P hP
    simp only [Finsupp.mem_support_iff, divS_apply, ord_algebraMap P ha] at hP
    simp only [Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
    exact_mod_cast hP
  · intro P _; simp

theorem finite_of_dq_eq {I : Ideal S} {n : ℕ} (h : dq K I = n) :
    Module.Finite K (S ⧸ I) ∧ finrank K (S ⧸ I) = n := by
  rw [dq_eq_rank, Cardinal.toENat_eq_natCast] at h
  exact ⟨Module.rank_lt_aleph0_iff.1 (h ▸ Cardinal.natCast_lt_aleph0), Module.finrank_eq_of_rank_eq h⟩

end Generic

section OinfDim

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

/-- The order at infinity of a nonzero element of `Oinf` is `-intDegree`. -/
theorem span_eq_pow {y : Oinf K} (hy : y ≠ 0) :
    Ideal.span {y} = Ideal.span {piInf K} ^ (-(y : RatFunc K).intDegree).toNat := by
  set n := (-(y : RatFunc K).intDegree).toNat
  have hy' : (y : RatFunc K) ≠ 0 := fun h => hy (Subtype.ext h)
  have hdeg := (mem_Oinf_iff' K hy').mp y.2
  have hn : (n : ℤ) = -(y : RatFunc K).intDegree := Int.toNat_of_nonneg (by omega)
  have hXn : (RatFunc.X ^ n : RatFunc K).intDegree = n := by
    rw [← RatFunc.algebraMap_X, ← map_pow, RatFunc.intDegree_polynomial, Polynomial.natDegree_X_pow]
  have hu0 : (y : RatFunc K) * RatFunc.X ^ n ≠ 0 := mul_ne_zero hy' (pow_ne_zero _ (X_ne_zero' K))
  have hudeg : ((y : RatFunc K) * RatFunc.X ^ n).intDegree = 0 := by
    rw [RatFunc.intDegree_mul hy' (pow_ne_zero _ (X_ne_zero' K)), hXn]
    omega
  have hu : (y : RatFunc K) * RatFunc.X ^ n ∈ Oinf K := (mem_Oinf_iff' K hu0).mpr hudeg.le
  have hui : ((y : RatFunc K) * RatFunc.X ^ n)⁻¹ ∈ Oinf K :=
    (mem_Oinf_iff' K (inv_ne_zero hu0)).mpr (by rw [RatFunc.intDegree_inv, hudeg]; simp)
  let u : Oinf K := ⟨_, hu⟩
  have h1 : u * ⟨_, hui⟩ = 1 := by
    ext
    show ((y : RatFunc K) * RatFunc.X ^ n) * ((y : RatFunc K) * RatFunc.X ^ n)⁻¹ = 1
    exact mul_inv_cancel₀ hu0
  have hunit : IsUnit u := isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  have hyu : y = u * piInf K ^ n := by
    ext
    simp only [u, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_piInf]
    rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (X_ne_zero' K)), mul_one]
  rw [hyu, Ideal.span_singleton_pow, Ideal.span_singleton_mul_left_unit hunit]

theorem span_piInf_ne_bot : Ideal.span {piInf K} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact piInf_ne_zero K

theorem dq_span_piInf : dq K (Ideal.span {piInf K}) = 1 := by
  have hb := residue_bijective K
  rw [← Ideal.Quotient.algebraMap_eq] at hb
  let e := LinearEquiv.ofBijective (Algebra.linearMap K (Oinf K ⧸ Ideal.span {piInf K})) hb
  rw [dq_eq_rank, ← e.rank_eq, rank_self]
  simp

variable {K}

/-- `dim_K Oinf/(y) = -intDegree y`, in `ℕ∞`. -/
theorem dq_span_Oinf {y : Oinf K} (hy : y ≠ 0) :
    dq K (Ideal.span {y}) = ((-(y : RatFunc K).intDegree).toNat : ℕ∞) := by
  rw [span_eq_pow K hy, dq_pow (span_piInf_ne_bot K), dq_span_piInf, mul_one]

theorem finrank_quot_Oinf {y : Oinf K} (hy : y ≠ 0) :
    Module.Finite K (Oinf K ⧸ Ideal.span {y}) ∧
      finrank K (Oinf K ⧸ Ideal.span {y}) = (-(y : RatFunc K).intDegree).toNat :=
  finite_of_dq_eq (dq_span_Oinf hy)

end OinfDim

end RamanujanPetersson.PlacesK

end

-- ===== S4.Def_RP_JacRRFam_E =====
section

/-!
# Places over an arbitrary field, part E: function fields over `K` and the product formula

For a function field `F / K(x)` over an arbitrary field `K`: the rings `Rfin`, `Rinf` of S3-Places have
finite-dimensional quotients (`FDQ`), `dim_K Rfin/(a) = deg_x N(a)`, `dim_K Rinf/(c) = -deg_x N(c)`
(Smith normal form over the PIDs `K[X]` and `Oinf K`), hence the product formula
`degS_fin_add_degS_inf` with no finiteness assumption on `K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.PlacesK

open RamanujanPetersson.Places (Oinf piInf ord cnt deg degS mem_Oinf_iff' Rfin Rinf)

section Smith

variable (K : Type*) [Field K] {R : Type*} [CommRing R] [IsPrincipalIdealRing R]
  [IsDedekindDomain R] [Algebra K R]
  {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra R S] [Algebra K S] [IsScalarTower K R S]
  [Module.Free R S] [Module.Finite R S]

/-- Smith normal form: `S/(f)` is finite-dimensional with `dim_K S/(f) = dim_K R/(N f)`. -/
theorem dq_span_eq_dq_norm (hR : ∀ d : R, d ≠ 0 → Module.Finite K (R ⧸ Ideal.span {d}))
    {f : S} (hf : f ≠ 0) :
    Module.Finite K (S ⧸ Ideal.span {f}) ∧
      dq K (Ideal.span {f}) = dq K (Ideal.span {Algebra.norm R f}) := by
  classical
  let b := Module.Free.chooseBasis R S
  have hI : Ideal.span {f} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.2 hf
  have : ∀ i, Module.Finite K (R ⧸ Ideal.span {(Ideal.span {f}).smithCoeffs b hI i}) :=
    fun i => hR _ (Ideal.smithCoeffs_ne_zero b _ hI i)
  have hfin : Module.Finite K (S ⧸ Ideal.span {f}) :=
    Module.Finite.equiv (Ideal.quotientEquivDirectSum K b hI).symm
  refine ⟨hfin, ?_⟩
  rw [dq_eq_finrank hfin, Ideal.finrank_quotient_eq_sum K hI b,
    Ideal.span_singleton_eq_span_singleton.2 (associated_norm_prod_smith b hf),
    ← Ideal.prod_span_singleton,
    dq_prod _ _ fun i _ => Ideal.span_singleton_eq_bot.not.2 (Ideal.smithCoeffs_ne_zero b _ hI i),
    Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => (dq_eq_finrank (hR _ (Ideal.smithCoeffs_ne_zero b _ hI i))).symm

end Smith

theorem moduleFinite_polyQuot {K : Type*} [Field K] {d : K[X]} (hd : d ≠ 0) :
    Module.Finite K (K[X] ⧸ Ideal.span {d}) :=
  PowerBasis.finite (AdjoinRoot.powerBasis hd)

section FunctionFieldSetup

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

instance fdq_Rfin : FDQ K (Rfin K F) where
  finite _ ha := (dq_span_eq_dq_norm K (R := K[X]) (fun _ hd => moduleFinite_polyQuot hd) ha).1

instance fdq_Rinf : FDQ K (Rinf K F) where
  finite _ hc := (dq_span_eq_dq_norm K (R := Oinf K) (fun _ hd => (finrank_quot_Oinf hd).1) hc).1

theorem norm_bridge_fin (a : Rfin K F) :
    algebraMap K[X] (RatFunc K) (Algebra.norm K[X] a) =
      Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F a) := by
  have := IsIntegralClosure.isLocalization K[X] (RatFunc K) F (Rfin K F)
  exact (Algebra.norm_localization K[X] (nonZeroDivisors K[X]) (Rₘ := RatFunc K) (Sₘ := F) a).symm

theorem norm_bridge_inf (c : Rinf K F) :
    ((Algebra.norm (Oinf K) c : Oinf K) : RatFunc K) =
      Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F c) := by
  have := IsIntegralClosure.isLocalization (Oinf K) (RatFunc K) F (Rinf K F)
  exact (Algebra.norm_localization (Oinf K) (nonZeroDivisors (Oinf K)) (Rₘ := RatFunc K) (Sₘ := F) c).symm

variable {K F}

/-- Finite part: `deg (div a)|_fin = deg_x N(a)`. -/
theorem degS_fin {a : Rfin K F} (ha : a ≠ 0) :
    degS K (divS (Rfin K F) (algebraMap (Rfin K F) F a)) =
      (Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F a)).intDegree := by
  have h1 := finrank_quot_span (K := K) (S := Rfin K F) ha
  have h2 := finrank_quotient_span_eq_natDegree_norm (F := K)
    (Module.Free.chooseBasis K[X] (Rfin K F)) ha
  rw [degS_divS_algebraMap ha, ← h1, h2, ← norm_bridge_fin, RatFunc.intDegree_polynomial]

/-- Infinite part: `deg (div c)|_inf = -deg_x N(c)`. -/
theorem degS_inf {c : Rinf K F} (hc : c ≠ 0) :
    degS K (divS (Rinf K F) (algebraMap (Rinf K F) F c)) =
      -(Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F c)).intDegree := by
  have hN : Algebra.norm (Oinf K) c ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc
  have hN' : ((Algebra.norm (Oinf K) c : Oinf K) : RatFunc K) ≠ 0 := fun h => hN (Subtype.ext h)
  have h1 := finrank_quot_span (K := K) (S := Rinf K F) hc
  have h2 := (dq_span_eq_dq_norm K (R := Oinf K) (fun _ hd => (finrank_quot_Oinf hd).1) hc).2
  rw [dq_eq_finrank (FDQ.finite c hc), dq_span_Oinf hN] at h2
  have h3 : finrank K (Rinf K F ⧸ Ideal.span {c}) =
      (-((Algebra.norm (Oinf K) c : Oinf K) : RatFunc K).intDegree).toNat := by exact_mod_cast h2
  have hle := (mem_Oinf_iff' K hN').mp (Algebra.norm (Oinf K) c).2
  rw [degS_divS_algebraMap hc, ← h1, h3, ← norm_bridge_inf]
  omega

/-- The product formula, split into the finite and the infinite places. -/
theorem degS_fin_add_degS_inf {f : F} (hf : f ≠ 0) :
    degS K (divS (Rfin K F) f) + degS K (divS (Rinf K F) f) = 0 := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (Rfin K F) f
  obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective (Rinf K F) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hf hab.symm
  have hc0 : c ≠ 0 := by rintro rfl; simp at hcd; exact hf hcd.symm
  have inj1 := IsFractionRing.injective (Rfin K F) F
  have inj2 := IsFractionRing.injective (Rinf K F) F
  have ha' : algebraMap (Rfin K F) F a ≠ 0 := (map_ne_zero_iff _ inj1).mpr ha0
  have hb' : algebraMap (Rfin K F) F b ≠ 0 := (map_ne_zero_iff _ inj1).mpr hb0
  have hc' : algebraMap (Rinf K F) F c ≠ 0 := (map_ne_zero_iff _ inj2).mpr hc0
  have hd' : algebraMap (Rinf K F) F d ≠ 0 := (map_ne_zero_iff _ inj2).mpr hd0
  have e1 : Algebra.norm (RatFunc K) f * Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F b) =
      Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F a) := by
    rw [← map_mul, ← hab, div_mul_cancel₀ _ hb']
  have e2 : Algebra.norm (RatFunc K) f * Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F d) =
      Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F c) := by
    rw [← map_mul, ← hcd, div_mul_cancel₀ _ hd']
  have nf : Algebra.norm (RatFunc K) f ≠ 0 := Algebra.norm_ne_zero_iff.mpr hf
  have nb : Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F b) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb'
  have nd : Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F d) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hd'
  have i1 := congrArg RatFunc.intDegree e1
  have i2 := congrArg RatFunc.intDegree e2
  rw [RatFunc.intDegree_mul nf nb] at i1
  rw [RatFunc.intDegree_mul nf nd] at i2
  have p1 : degS K (divS (Rfin K F) f) =
      (Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F a)).intDegree -
        (Algebra.norm (RatFunc K) (algebraMap (Rfin K F) F b)).intDegree := by
    rw [← hab, divS_div ha' hb', degS_sub, degS_fin ha0, degS_fin hb0]
  have p2 : degS K (divS (Rinf K F) f) =
      -(Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F c)).intDegree +
        (Algebra.norm (RatFunc K) (algebraMap (Rinf K F) F d)).intDegree := by
    rw [← hcd, divS_div hc' hd', degS_sub, degS_inf hc0, degS_inf hd0]; ring
  rw [p1, p2]
  omega

end FunctionFieldSetup

end RamanujanPetersson.PlacesK

end

-- ===== S4.Def_RP_JacRRFam_F =====
section

/-!
# Places over an arbitrary field, part F: divisors, the product formula, the constant field

Fintype-free copies of S3-Places for a function field `F / K(x)` over an arbitrary field `K`
(reusing the S3 definitions `Place`, `Divisor`, `Place.deg`, `Place.ord`, `Divisor.deg`, `constField`):
`div`, `deg_div` (product formula), `finrank_constField_dvd`, `finiteDimensional_constField`,
`mem_constField_of_ord_nonneg` (no poles ⇒ constant), `ord_eq_zero_of_mem_constField`, `div_eq_zero_iff`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.PlacesK

open RamanujanPetersson.Places (Oinf piInf ord cnt deg degS mem_Oinf_iff' Rfin Rinf Place Divisor
  constField valuation_le_one_of_neg_log_nonneg neg_log_nonneg_of_valuation_le_one
  neg_log_nonneg_algebraMap min_neg_log_le_neg_log_add)

section Divisors

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable {K F}

theorem Place.deg_pos (P : Place K F) : 0 < P.deg := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.PlacesK.deg_pos (K := K) P, _root_.RamanujanPetersson.PlacesK.deg_pos (K := K) P]

theorem Place.ord_mul (P : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f * g) = P.ord f + P.ord g := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.PlacesK.ord_mul P hf hg, _root_.RamanujanPetersson.PlacesK.ord_mul P hf hg]

theorem Place.ord_div (P : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    P.ord (f / g) = P.ord f - P.ord g := by
  rcases P with P | P
  exacts [_root_.RamanujanPetersson.PlacesK.ord_div P hf hg, _root_.RamanujanPetersson.PlacesK.ord_div P hf hg]

theorem Divisor.deg_add (D E : Divisor K F) : Places.Divisor.deg (D + E) = D.deg + E.deg := by
  unfold Places.Divisor.deg
  rw [Finsupp.sum_add_index'] <;> intros <;> ring

theorem Divisor.deg_neg (D : Divisor K F) : Places.Divisor.deg (-D) = -D.deg := by
  unfold Places.Divisor.deg
  rw [Finsupp.sum_neg_index (fun _ => by ring), Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem Divisor.deg_sub (D E : Divisor K F) : Places.Divisor.deg (D - E) = D.deg - E.deg := by
  rw [sub_eq_add_neg, Divisor.deg_add, Divisor.deg_neg, sub_eq_add_neg]

theorem Divisor.deg_single (P : Place K F) (n : ℤ) : Places.Divisor.deg (Finsupp.single P n : Divisor K F) = n * P.deg := by
  unfold Places.Divisor.deg
  rw [Finsupp.sum_single_index (by ring)]

theorem Divisor.deg_sumElim (D : HeightOneSpectrum (Rfin K F) →₀ ℤ)
    (E : HeightOneSpectrum (Rinf K F) →₀ ℤ) :
    Places.Divisor.deg (D.sumElim E : Divisor K F) = degS K D + degS K E := by
  unfold Places.Divisor.deg
  rw [Finsupp.sum_sumElim]
  rfl

/-- The principal divisor of `f` (the zero divisor for `f = 0`). -/
noncomputable def div (f : F) : Divisor K F := (divS (Rfin K F) f).sumElim (divS (Rinf K F) f)

@[simp] theorem div_apply (f : F) (P : Place K F) : div f P = P.ord f := by
  rcases P with P | P <;> rfl

theorem div_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : (div (f * g) : Divisor K F) = div f + div g := by
  ext P
  simp only [div_apply, Finsupp.coe_add, Pi.add_apply, Place.ord_mul P hf hg]

theorem div_div {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : (div (f / g) : Divisor K F) = div f - div g := by
  ext P
  simp only [div_apply, Finsupp.coe_sub, Pi.sub_apply, Place.ord_div P hf hg]

/-- **Product formula**: a nonzero function has as many zeros as poles, counted with degrees. -/
theorem deg_div {f : F} (hf : f ≠ 0) : Places.Divisor.deg (div f : Divisor K F) = 0 := by
  rw [div, Divisor.deg_sumElim]
  exact degS_fin_add_degS_inf hf

end Divisors

section ConstantField

theorem moduleFinite_of_algHom (K : Type*) [Field K] {k S : Type*} [Field k] [Algebra K k]
    [CommRing S] [Algebra K S] (φ : k →ₐ[K] S) (P : Ideal S) [P.IsMaximal] [Module.Finite K (S ⧸ P)] :
    Module.Finite K k ∧ finrank K k ∣ finrank K (S ⧸ P) := by
  let : Field (S ⧸ P) := Ideal.Quotient.field P
  let ψ : k →ₐ[K] S ⧸ P := (Ideal.Quotient.mkₐ K P).comp φ
  let : Algebra k (S ⧸ P) := ψ.toRingHom.toAlgebra
  have : IsScalarTower K k (S ⧸ P) := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have : Module.Finite k (S ⧸ P) := Module.Finite.of_restrictScalars_finite K k (S ⧸ P)
  have : Module.Finite K k :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom K k (S ⧸ P)).toLinearMap
      (algebraMap k (S ⧸ P)).injective
  exact ⟨inferInstance, Dvd.intro _ (Module.finrank_mul_finrank K k (S ⧸ P))⟩

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem algebraMap_Oinf_Rinf_injective : Function.Injective (algebraMap (Oinf K) (Rinf K F)) := by
  intro a b h
  have h2 : algebraMap (Oinf K) F a = algebraMap (Oinf K) F b := congrArg Subtype.val h
  rw [IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) F,
    IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) F b] at h2
  exact Subtype.ext ((algebraMap (RatFunc K) F).injective h2)

theorem isIntegral_of_mem_constField (c : constField K F) : IsIntegral K (c : F) :=
  (mem_algebraicClosure_iff.mp c.2).isIntegral

/-- Constants are regular at the finite places. -/
def constToRfin : constField K F →ₐ[K] Rfin K F where
  toFun c := ⟨(c : F), (isIntegral_of_mem_constField K F c).tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Constants are regular at the infinite places. -/
def constToRinf : constField K F →ₐ[K] Rinf K F where
  toFun c := ⟨(c : F), (isIntegral_of_mem_constField K F c).tower_top⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem not_isField_Rinf : ¬ IsField (Rinf K F) := by
  rw [← Algebra.IsIntegral.isField_iff_isField (algebraMap_Oinf_Rinf_injective K F)]
  exact IsDiscreteValuationRing.not_isField _

/-- There is at least one place over `x = ∞`. -/
theorem nonempty_infPlace : Nonempty (HeightOneSpectrum (Rinf K F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Rinf K F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (not_isField_Rinf K F)⟩⟩

theorem finrank_constField_dvd (P : Place K F) : finrank K (constField K F) ∣ P.deg := by
  rcases P with P | P
  · haveI := P.isMaximal
    haveI := moduleFinite_residue (K := K) P
    exact (moduleFinite_of_algHom K (constToRfin K F) P.asIdeal).2
  · haveI := P.isMaximal
    haveI := moduleFinite_residue (K := K) P
    exact (moduleFinite_of_algHom K (constToRinf K F) P.asIdeal).2

instance finiteDimensional_constField : FiniteDimensional K (constField K F) := by
  obtain ⟨P⟩ := nonempty_infPlace K F
  have := P.isMaximal
  have := moduleFinite_residue (K := K) P
  exact (moduleFinite_of_algHom K (constToRinf K F) P.asIdeal).1

/-- A place of degree one forces the full constant field to be `K`. -/
theorem constField_eq_bot_of_deg_one {P : Place K F} (h : P.deg = 1) : constField K F = ⊥ :=
  IntermediateField.finrank_eq_one_iff.mp (Nat.dvd_one.mp (h ▸ finrank_constField_dvd K F P))

end ConstantField

section NoPoles

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem isIntegral_poly_of_ord_nonneg {f : F}
    (h : ∀ P : HeightOneSpectrum (Rfin K F), 0 ≤ ord P f) : IsIntegral K[X] f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) f
    (fun P => valuation_le_one_of_neg_log_nonneg P (h P))
  exact a.2

theorem isIntegral_Oinf_of_ord_nonneg {f : F}
    (h : ∀ P : HeightOneSpectrum (Rinf K F), 0 ≤ ord P f) : IsIntegral (Oinf K) f := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := F) f
    (fun P => valuation_le_one_of_neg_log_nonneg P (h P))
  exact a.2

/-- A polynomial in `x` that is regular at `x = ∞` is a constant. -/
theorem mem_range_of_mem_Oinf {p : K[X]} (h : algebraMap K[X] (RatFunc K) p ∈ Oinf K) :
    algebraMap K[X] (RatFunc K) p ∈ Set.range (algebraMap K (RatFunc K)) := by
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  have hne : algebraMap K[X] (RatFunc K) p ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))]
  have h2 := (mem_Oinf_iff' K hne).mp h
  rw [RatFunc.intDegree_polynomial] at h2
  have hdeg : p.natDegree = 0 := by omega
  refine ⟨p.coeff 0, ?_⟩
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq,
    ← eq_C_of_natDegree_eq_zero hdeg]

/-- Integral over `K[x]` and over the valuation ring at `∞` implies integral over `K`. -/
theorem isIntegral_of_isIntegral_poly_Oinf {f : F} (h1 : IsIntegral K[X] f)
    (h2 : IsIntegral (Oinf K) f) : IsIntegral K f := by
  have e1 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc K) h1
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc K) h2
  have hl : minpoly (RatFunc K) f ∈ lifts (algebraMap K (RatFunc K)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have hc2 : (minpoly (RatFunc K) f).coeff n ∈ Oinf K := by
      rw [e2, coeff_map]
      exact SetLike.coe_mem _
    rw [e1, coeff_map] at hc2 ⊢
    exact mem_range_of_mem_Oinf K hc2
  obtain ⟨q, hq, -, hmon⟩ := lifts_and_degree_eq_and_monic hl (minpoly.monic h1.tower_top)
  refine ⟨q, hmon, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap (RatFunc K), hq, minpoly.aeval]

/-- **A function without poles is a constant** (Riemann-Roch's `L(0) = k`). -/
theorem mem_constField_of_ord_nonneg {f : F} (h : ∀ P : Place K F, 0 ≤ P.ord f) :
    f ∈ constField K F :=
  mem_algebraicClosure_iff.mpr (isIntegral_of_isIntegral_poly_Oinf K F
    (isIntegral_poly_of_ord_nonneg K F fun P => h (Sum.inl P))
    (isIntegral_Oinf_of_ord_nonneg K F fun P => h (Sum.inr P))).isAlgebraic

/-- Constants have no poles. -/
theorem ord_nonneg_of_mem_constField {f : F} (hf : f ∈ constField K F) (P : Place K F) :
    0 ≤ P.ord f := by
  rcases P with P | P
  · show 0 ≤ -WithZero.log (P.valuation F f)
    exact neg_log_nonneg_algebraMap (K := F) P (constToRfin K F ⟨f, hf⟩)
  · show 0 ≤ -WithZero.log (P.valuation F f)
    exact neg_log_nonneg_algebraMap (K := F) P (constToRinf K F ⟨f, hf⟩)

theorem Place.ord_one (P : Place K F) : P.ord (1 : F) = 0 := by
  have h := Place.ord_mul P (one_ne_zero (α := F)) (one_ne_zero (α := F))
  rw [mul_one] at h
  omega

theorem Place.ord_add (P : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (P.ord f) (P.ord g) ≤ P.ord (f + g) := by
  rcases P with P | P
  exacts [min_neg_log_le_neg_log_add P hf hg hfg, min_neg_log_le_neg_log_add P hf hg hfg]

theorem Place.ord_neg (P : Place K F) (f : F) : P.ord (-f) = P.ord f := by
  rcases P with P | P
  · show -WithZero.log (P.valuation F (-f)) = -WithZero.log (P.valuation F f)
    rw [Valuation.map_neg]
  · show -WithZero.log (P.valuation F (-f)) = -WithZero.log (P.valuation F f)
    rw [Valuation.map_neg]

/-- Nonzero constants have neither zeros nor poles. -/
theorem ord_eq_zero_of_mem_constField {f : F} (hf : f ∈ constField K F) (hf0 : f ≠ 0)
    (P : Place K F) : P.ord f = 0 := by
  have h1 := ord_nonneg_of_mem_constField K F hf P
  have h2 := ord_nonneg_of_mem_constField K F (inv_mem hf) P
  have h3 : P.ord (f * f⁻¹) = P.ord f + P.ord f⁻¹ := Place.ord_mul P hf0 (inv_ne_zero hf0)
  rw [mul_inv_cancel₀ hf0, Place.ord_one] at h3
  omega

/-- Multiplying by a nonzero constant does not change orders. -/
theorem ord_const_mul {c f : F} (hc : c ∈ constField K F) (hc0 : c ≠ 0) (hf : f ≠ 0) (P : Place K F) :
    P.ord (c * f) = P.ord f := by
  rw [Place.ord_mul P hc0 hf, ord_eq_zero_of_mem_constField K F hc hc0, zero_add]

/-- `div f = 0` exactly for the nonzero constants. -/
theorem div_eq_zero_iff {f : F} (hf : f ≠ 0) :
    (div f : Divisor K F) = 0 ↔ f ∈ constField K F := by
  constructor
  · intro h
    apply mem_constField_of_ord_nonneg
    intro P
    have h' := congrArg (fun D : Divisor K F => D P) h
    simp only [div_apply, Finsupp.coe_zero, Pi.zero_apply] at h'
    omega
  · intro h
    ext P
    rw [div_apply, Finsupp.coe_zero, Pi.zero_apply, ord_eq_zero_of_mem_constField K F h hf P]

end NoPoles

end RamanujanPetersson.PlacesK

end

-- ===== S4.Def_RP_JacComplete_PlaceF =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PlaceF` (dictionary D1 for a function field `F / K(x)`)

* `placeVal P : Valuation F ℤᵐ⁰` (the valuation of a place), `ord_eq_neg_log`;
* `placeVal_algebraMap` (trivial on `K^×`), `exists_placeVal_unif` (normalized);
* `placeVal_inl_x_le` / `one_lt_placeVal_inr_x`: finite places see `x` as integral, infinite ones as a pole;
* **`placeVal_injective`** and **`exists_placeVal_eq`**: the places of `F` are exactly the normalized discrete
  valuations of `F` trivial on `K^×` (independent of the coordinate `x`);
* **`placeEquiv σ`** for `σ : F ≃ₐ[K] F'` (two function-field structures): a bijection of places with
  `ord_placeEquiv : (placeEquiv σ P).ord (σ f) = P.ord f`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Oinf piInf Rfin Rinf Place span_piInf_isMaximal mem_Oinf_iff')

section PlaceF

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- The valuation of `F` attached to a place. -/
noncomputable def placeVal : Place K F → Valuation F ℤᵐ⁰ :=
  Sum.elim (fun P => P.valuation F) (fun Q => Q.valuation F)

@[simp] theorem placeVal_inl (P : HeightOneSpectrum (Rfin K F)) :
    placeVal (Sum.inl P : Place K F) = P.valuation F := rfl

@[simp] theorem placeVal_inr (Q : HeightOneSpectrum (Rinf K F)) :
    placeVal (Sum.inr Q : Place K F) = Q.valuation F := rfl

theorem ord_eq_neg_log (P : Place K F) (f : F) : P.ord f = -WithZero.log (placeVal P f) := by
  rcases P with P | P <;> rfl

theorem placeVal_le_one_of_isIntegral (P : Place K F) {y : F} (hy : IsIntegral K y) :
    placeVal P y ≤ 1 := by
  rcases P with P | Q
  · exact P.valuation_le_one (K := F) (⟨y, hy.tower_top⟩ : Rfin K F)
  · exact Q.valuation_le_one (K := F) (⟨y, hy.tower_top⟩ : Rinf K F)

/-- A place is trivial on the constants. -/
theorem placeVal_algebraMap (P : Place K F) {c : K} (hc : c ≠ 0) :
    placeVal P (algebraMap K F c) = 1 := by
  have h1 := placeVal_le_one_of_isIntegral P (isIntegral_algebraMap (R := K) (A := F) (x := c))
  have h2 := placeVal_le_one_of_isIntegral P (isIntegral_algebraMap (R := K) (A := F) (x := c⁻¹))
  have hne : placeVal P (algebraMap K F c) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero (algebraMap K F)).2 hc)
  rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 hne)] at h2
  exact le_antisymm h1 h2

theorem exists_placeVal_unif (P : Place K F) : ∃ ϖ : F, placeVal P ϖ = WithZero.exp (-1 : ℤ) := by
  rcases P with P | Q
  · exact P.valuation_exists_uniformizer F
  · exact Q.valuation_exists_uniformizer F

theorem placeVal_inl_x_le (P : HeightOneSpectrum (Rfin K F)) :
    placeVal (Sum.inl P : Place K F) (algebraMap K[X] F X) ≤ 1 :=
  P.valuation_le_one (K := F) (⟨algebraMap K[X] F X, isIntegral_algebraMap⟩ : Rfin K F)

theorem piInf_mem_comap (Q : HeightOneSpectrum (Rinf K F)) :
    piInf K ∈ Q.asIdeal.comap (algebraMap (Oinf K) (Rinf K F)) := by
  have := Q.isPrime
  have hne : Q.asIdeal.comap (algebraMap (Oinf K) (Rinf K F)) ≠ ⊥ := by
    obtain ⟨y, hyQ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hy0 hyQ (integralClosure.isIntegral y)
  have hmax := Ideal.IsPrime.isMaximal (Ideal.comap_isPrime (algebraMap (Oinf K) (Rinf K F)) Q.asIdeal) hne
  rw [(IsLocalRing.eq_maximalIdeal hmax).trans (IsLocalRing.eq_maximalIdeal (span_piInf_isMaximal K)).symm]
  exact Ideal.subset_span rfl

theorem one_lt_placeVal_inr_x (Q : HeightOneSpectrum (Rinf K F)) :
    1 < placeVal (Sum.inr Q : Place K F) (algebraMap K[X] F X) := by
  have hlt : Q.valuation F (algebraMap (Rinf K F) F (algebraMap (Oinf K) (Rinf K F) (piInf K))) < 1 :=
    (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) Q
      (algebraMap (Oinf K) (Rinf K F) (piInf K))).2 (piInf_mem_comap Q)
  have e : algebraMap (Rinf K F) F (algebraMap (Oinf K) (Rinf K F) (piInf K)) = (algebraMap K[X] F X)⁻¹ := by
    rw [← IsScalarTower.algebraMap_apply (Oinf K) (Rinf K F) F,
      IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) F]
    show algebraMap (RatFunc K) F (1 / RatFunc.X) = _
    rw [one_div, map_inv₀, ← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F]
  rw [e, map_inv₀] at hlt
  have hX : algebraMap K[X] F X ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply K[X] (RatFunc K) F, RatFunc.algebraMap_X]
    exact (_root_.map_ne_zero _).2 RatFunc.X_ne_zero
  have hx0 : Q.valuation F (algebraMap K[X] F X) ≠ 0 := (Valuation.ne_zero_iff _).2 hX
  exact (inv_lt_one₀ (zero_lt_iff.2 hx0)).1 hlt

theorem algebraMap_eq_aeval (p : K[X]) : algebraMap K[X] F p = aeval (algebraMap K[X] F X) p := by
  have h := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom K K[X] F) (X : K[X]) p
  rw [Polynomial.aeval_X_left_apply] at h
  simpa using h.symm

section Range

variable (w : Valuation F ℤᵐ⁰) (hK : ∀ c : K, c ≠ 0 → w (algebraMap K F c) = 1)
include hK

theorem val_const_le (c : K) : w (algebraMap K F c) ≤ 1 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, map_zero]; exact zero_le'
  · exact (hK c hc).le

theorem val_aeval_le_one {y : F} (hy : w y ≤ 1) (p : K[X]) : w (aeval y p) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine w.map_sum_le fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  exact mul_le_one' (val_const_le w hK _) (pow_le_one' hy _)

theorem val_aeval_of_one_lt {y : F} (hy : 1 < w y) {p : K[X]} (hp : p ≠ 0) :
    w (aeval y p) = w y ^ p.natDegree := by
  have hlead : w (p.coeff p.natDegree • y ^ p.natDegree) = w y ^ p.natDegree := by
    rw [Algebra.smul_def, map_mul, map_pow, coeff_natDegree, hK _ (leadingCoeff_ne_zero.2 hp), one_mul]
  have hy0 : w y ^ p.natDegree ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hy))
  rw [aeval_eq_sum_range, Finset.sum_range_succ, Valuation.map_add_eq_of_lt_right, hlead]
  rw [hlead]
  refine w.map_sum_lt hy0 fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Algebra.smul_def, map_mul, map_pow]
  calc w (algebraMap K F (p.coeff i)) * w y ^ i ≤ w y ^ i := by
        first
          | exact mul_le_of_le_one_left' (val_const_le w hK _)
          | exact mul_le_of_le_one_left zero_le' (val_const_le w hK _)
    _ < w y ^ p.natDegree := pow_lt_pow_right₀ hy hi

theorem val_Oinf_le_one (hx : 1 < w (algebraMap K[X] F X)) (s : Oinf K) :
    w (algebraMap (Oinf K) F s) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) F]
  set f : RatFunc K := algebraMap (Oinf K) (RatFunc K) s with hfdef
  by_cases hf : f = 0
  · rw [hf, map_zero, map_zero]; exact zero_le'
  have hdeg := (mem_Oinf_iff' K hf).1 s.2
  unfold RatFunc.intDegree at hdeg
  rw [← RatFunc.num_div_denom f, map_div₀, ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F,
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) F, map_div₀, algebraMap_eq_aeval f.num,
    algebraMap_eq_aeval f.denom, val_aeval_of_one_lt w hK hx (RatFunc.num_ne_zero hf),
    val_aeval_of_one_lt w hK hx f.denom_ne_zero]
  exact div_le_one_of_le₀ (pow_le_pow_right₀ hx.le (by omega)) zero_le'

/-- **Every normalized discrete valuation of `F` trivial on `K^×` is a place.** -/
theorem exists_placeVal_eq {ϖ : F} (hϖ : w ϖ = WithZero.exp (-1 : ℤ)) :
    ∃ P : Place K F, placeVal P = w := by
  by_cases hx : w (algebraMap K[X] F X) ≤ 1
  · have hS : ∀ p : K[X], w (algebraMap K[X] F p) ≤ 1 := fun p => by
      rw [algebraMap_eq_aeval]; exact val_aeval_le_one w hK hx p
    obtain ⟨P, hP⟩ := exists_heightOneSpectrum_valuation_eq (R := Rfin K F) w hϖ
      (fun r => by
        have hr : IsIntegral K[X] (r : F) := by
          first
            | exact r.2
            | exact mem_integralClosure_iff.1 r.2
        exact val_le_one_of_isIntegral w hS hr)
    exact ⟨Sum.inl P, hP⟩
  · rw [not_le] at hx
    obtain ⟨Q, hQ⟩ := exists_heightOneSpectrum_valuation_eq (R := Rinf K F) w hϖ
      (fun r => by
        have hr : IsIntegral (Oinf K) (r : F) := by
          first
            | exact r.2
            | exact mem_integralClosure_iff.1 r.2
        exact val_le_one_of_isIntegral w (val_Oinf_le_one w hK hx) hr)
    exact ⟨Sum.inr Q, hQ⟩

end Range

/-- **Places are determined by their valuations.** -/
theorem placeVal_injective : Function.Injective (placeVal : Place K F → Valuation F ℤᵐ⁰) := by
  rintro (P | Q) (P' | Q') h
  · exact congrArg Sum.inl
      (HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) (Valuation.IsEquiv.of_eq h))
  · have h1 := placeVal_inl_x_le P
    rw [h] at h1
    exact absurd h1 (not_le.2 (one_lt_placeVal_inr_x Q'))
  · have h1 := placeVal_inl_x_le P'
    rw [← h] at h1
    exact absurd h1 (not_le.2 (one_lt_placeVal_inr_x Q))
  · exact congrArg Sum.inr
      (HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := F) (Valuation.IsEquiv.of_eq h))

section Equiv

variable {F' : Type*} [Field F'] [Algebra K F'] [Algebra K[X] F'] [Algebra (RatFunc K) F']
  [IsScalarTower K[X] (RatFunc K) F'] [IsScalarTower K K[X] F'] [FunctionField K F']
  [Algebra.IsSeparable (RatFunc K) F']

theorem exists_placeVal_comap (σ : F ≃ₐ[K] F') (P : Place K F) :
    ∃ P' : Place K F', placeVal P' = (placeVal P).comap (σ.symm : F' →+* F) := by
  obtain ⟨ϖ, hϖ⟩ := exists_placeVal_unif P
  refine exists_placeVal_eq _ (fun c hc => ?_) (ϖ := σ ϖ) ?_
  · rw [Valuation.comap_apply]
    have e : (σ.symm : F' →+* F) (algebraMap K F' c) = algebraMap K F c := σ.symm.commutes c
    rw [e]; exact placeVal_algebraMap P hc
  · rw [Valuation.comap_apply]
    have e : (σ.symm : F' →+* F) (σ ϖ) = ϖ := σ.symm_apply_apply ϖ
    rw [e, hϖ]

/-- The place of `F'` corresponding to a place of `F` under `σ`. -/
noncomputable def placeMap (σ : F ≃ₐ[K] F') (P : Place K F) : Place K F' :=
  (exists_placeVal_comap σ P).choose

theorem placeVal_placeMap (σ : F ≃ₐ[K] F') (P : Place K F) :
    placeVal (placeMap σ P) = (placeVal P).comap (σ.symm : F' →+* F) :=
  (exists_placeVal_comap σ P).choose_spec

theorem ord_placeMap (σ : F ≃ₐ[K] F') (P : Place K F) (f : F) : (placeMap σ P).ord (σ f) = P.ord f := by
  rw [ord_eq_neg_log, ord_eq_neg_log, placeVal_placeMap, Valuation.comap_apply]
  have e : (σ.symm : F' →+* F) (σ f) = f := σ.symm_apply_apply f
  rw [e]

/-- **Places do not depend on the function-field structure.** -/
noncomputable def placeEquiv (σ : F ≃ₐ[K] F') : Place K F ≃ Place K F' where
  toFun := placeMap σ
  invFun := placeMap σ.symm
  left_inv P := placeVal_injective <| by
    rw [placeVal_placeMap, placeVal_placeMap]
    ext f
    rw [Valuation.comap_apply, Valuation.comap_apply]
    have e : (σ.symm : F' →+* F) ((σ.symm.symm : F →+* F') f) = f := σ.symm_apply_apply f
    rw [e]
  right_inv P := placeVal_injective <| by
    rw [placeVal_placeMap, placeVal_placeMap]
    ext f
    rw [Valuation.comap_apply, Valuation.comap_apply]
    have e : (σ.symm.symm : F →+* F') ((σ.symm : F' →+* F) f) = f := σ.apply_symm_apply f
    rw [e]

@[simp] theorem placeEquiv_apply (σ : F ≃ₐ[K] F') (P : Place K F) : placeEquiv σ P = placeMap σ P := rfl

theorem ord_placeEquiv (σ : F ≃ₐ[K] F') (P : Place K F) (f : F) :
    (placeEquiv σ P).ord (σ f) = P.ord f :=
  ord_placeMap σ P f

theorem ord_placeEquiv_symm (σ : F ≃ₐ[K] F') (P : Place K F') (f : F) :
    ((placeEquiv σ).symm P).ord f = P.ord (σ f) := by
  conv_rhs => rw [← (placeEquiv σ).apply_symm_apply P]
  rw [ord_placeEquiv]

end Equiv

end PlaceF

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacComplete_Sep =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Sep` (tools for separating elements; Mathlib only)

* `finiteDimensional_adjoin_of_transcendental`: if `F` is finite over `K⟮x⟯` and `h` is transcendental
  over `K`, then `F` is finite over `K⟮h⟯` (transcendence degree one);
* `eq_zero_of_sum_pow_mul`: if a valuation has `v h = exp (-1)`, the elements `1, h, ..., h^(p-1)`
  are linearly independent over the `p`-th powers.
-/

set_option autoImplicit false

open IntermediateField Polynomial Cardinal
open scoped WithZero

universe u

namespace RamanujanPetersson.JacComplete

section Fin

variable {K : Type*} {F : Type u} [Field K] [Field F] [Algebra K F]

/-- Transcendence degree one: `F` finite over `K⟮x⟯` and `h` transcendental give `F` finite over `K⟮h⟯`. -/
theorem finiteDimensional_adjoin_of_transcendental {x h : F} [FiniteDimensional K⟮x⟯ F]
    (hh : Transcendental K h) : FiniteDimensional K⟮h⟯ F := by
  open scoped algebraAdjoinAdjoin in
  have h1 : Algebra.IsAlgebraic (Algebra.adjoin K ({x} : Set F)) F :=
    IntermediateField.isAlgebraic_adjoin_iff_top.1 (Algebra.IsAlgebraic.of_finite K⟮x⟯ F)
  have h2 : Algebra.trdeg K F ≤ #({x} : Set F) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K ({x} : Set F)
  have hind : AlgebraicIndependent K (fun _ : PUnit.{u+1} => h) := algebraicIndependent_unique_type_iff.2 hh
  have hb : IsTranscendenceBasis K (fun _ : PUnit.{u+1} => h) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite
      (h2.trans (by rw [Cardinal.mk_singleton, Cardinal.mk_punit]))
  have halg := hb.isAlgebraic_field
  have hr : Set.range (fun _ : PUnit.{u+1} => h) = {h} := Set.range_const
  rw [hr] at halg
  have hxi : IsIntegral K⟮h⟯ x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let L : IntermediateField K⟮h⟯ F := K⟮h⟯⟮x⟯
  have hL : FiniteDimensional K⟮h⟯ L := IntermediateField.adjoin.finiteDimensional hxi
  have hle : K⟮x⟯ ≤ L.restrictScalars K :=
    IntermediateField.adjoin_simple_le_iff.2 (IntermediateField.mem_adjoin_simple_self K⟮h⟯ x)
  letI : Algebra K⟮x⟯ L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K⟮x⟯ L F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional L F := Module.Finite.of_restrictScalars_finite K⟮x⟯ L F
  exact Module.Finite.trans L F

end Fin

section Val

variable {F : Type*} [Field F]

/-- The value of `h ^ r * c ^ p` when `v h = exp (-1)` and `c ≠ 0`. -/
theorem val_pow_mul_pow (v : Valuation F ℤᵐ⁰) {h c : F} (hv : v h = WithZero.exp (-1 : ℤ)) (hc : c ≠ 0)
    (r p : ℕ) : ∃ n : ℤ, v (h ^ r * c ^ p) = WithZero.exp (-(r : ℤ) + p * n) := by
  have h0 : v c ≠ 0 := (Valuation.ne_zero_iff v).2 hc
  refine ⟨WithZero.log (v c), ?_⟩
  rw [map_mul, map_pow, map_pow, hv, ← WithZero.exp_log h0, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
    ← WithZero.exp_add, WithZero.log_exp]
  congr 1
  simp only [nsmul_eq_mul, mul_neg, mul_one]

/-- **Independence over `p`-th powers.** If `v h = exp (-1)` then `Σ_{r < p} h^r c_r^p = 0` forces all
`c_r = 0`. -/
theorem eq_zero_of_sum_pow_mul (p : ℕ) [hp : Fact p.Prime] (v : Valuation F ℤᵐ⁰) {h : F}
    (hv : v h = WithZero.exp (-1 : ℤ)) (c : Fin p → F) (hc : ∑ r : Fin p, h ^ (r : ℕ) * c r ^ p = 0) :
    ∀ r, c r = 0 := by
  classical
  have hh0 : h ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  by_contra hne
  push_neg at hne
  obtain ⟨r0, hr0⟩ := hne
  have hpos : (Finset.univ : Finset (Fin p)).Nonempty := ⟨r0, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun r : Fin p => v (h ^ (r : ℕ) * c r ^ p)) hpos
  have hfne : ∀ r, c r ≠ 0 → v (h ^ (r : ℕ) * c r ^ p) ≠ 0 := fun r hr =>
    (Valuation.ne_zero_iff v).2 (mul_ne_zero (pow_ne_zero _ hh0) (pow_ne_zero _ hr))
  have hcj : c j ≠ 0 := by
    intro h0
    have hle := hj r0 (Finset.mem_univ _)
    rw [h0, zero_pow hp.out.ne_zero, mul_zero, map_zero] at hle
    exact hfne r0 hr0 (le_antisymm hle zero_le')
  have hlt : ∀ i ∈ (Finset.univ : Finset (Fin p)) \ {j},
      v (h ^ (i : ℕ) * c i ^ p) < v (h ^ (j : ℕ) * c j ^ p) := by
    intro i hi
    have hij : i ≠ j := by simpa using hi
    refine lt_of_le_of_ne (hj i (Finset.mem_univ _)) ?_
    by_cases hci : c i = 0
    · rw [hci, zero_pow hp.out.ne_zero, mul_zero, map_zero]
      exact (hfne j hcj).symm
    obtain ⟨a, ha⟩ := val_pow_mul_pow v hv hci (i : ℕ) p
    obtain ⟨b, hb⟩ := val_pow_mul_pow v hv hcj (j : ℕ) p
    rw [ha, hb, Ne, WithZero.exp_inj]
    intro heq
    have hd : (p : ℤ) ∣ (j : ℤ) - (i : ℤ) := ⟨b - a, by linear_combination heq⟩
    have hz := Int.eq_zero_of_abs_lt_dvd hd (by
      rw [abs_lt]
      have := i.isLt
      have := j.isLt
      constructor <;> omega)
    exact hij (Fin.ext (by omega))
  have hsum := Valuation.map_sum_eq_of_lt v (Finset.mem_univ j) hlt
  rw [hc, map_zero] at hsum
  exact hfne j hcj hsum.symm

end Val

end RamanujanPetersson.JacComplete

end


