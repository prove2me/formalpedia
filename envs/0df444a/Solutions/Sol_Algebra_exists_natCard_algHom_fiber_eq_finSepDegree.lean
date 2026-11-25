-- Prove2me | solution 1 for Algebra.exists_natCard_algHom_fiber_eq_finSepDegree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:54:12.004946+00:00
-- url     : https://prove2.me/submissions/23818d1f-78d6-4a8e-9140-5c45ecc2562e

import Mathlib

set_option autoImplicit false

universe u

/-!
# S4-IsogDegA, file Fib1: generic fibre count, part 1 (finite dimensionality, fibres, upper bound)
-/


open Polynomial

namespace RamanujanPetersson.IsogDegA

section FinDim

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

omit [IsDomain R] [IsDomain B] [IsFractionRing R K] in
include R B in
/-- If `B` is a finite `R`-algebra (domains), then `Frac B` is finite dimensional over `Frac R`. -/
theorem finiteDimensional_of_finite : FiniteDimensional K L := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := B)
  set S : Set L := (algebraMap B L) '' (s : Set B) with hSdef
  have hint : ∀ x ∈ S, IsIntegral K x := by
    rintro _ ⟨b, -, rfl⟩
    have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
    exact (hb.map (IsScalarTower.toAlgHom R B L)).tower_top
  have hfin : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hB : ∀ c : B, algebraMap B L c ∈ IntermediateField.adjoin K S := by
    intro c
    have hc : c ∈ Submodule.span R (s : Set B) := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K S ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R K L]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
  have htop : IntermediateField.adjoin K S = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact div_mem (hB a) (hB b)
  rw [htop] at hfin
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end FinDim

section Fibre

variable (k : Type*) [Field k]
variable {R : Type*} (B : Type*) [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]

/-- The `k`-points of `Spec B` lying over the `k`-point `χ` of `Spec R`. -/
abbrev fiber (χ : R →ₐ[k] k) : Type _ :=
  {ψ : B →ₐ[k] k // ψ.comp (IsScalarTower.toAlgHom k R B) = χ}

variable {k B}

theorem fiber_apply_algebraMap {χ : R →ₐ[k] k} (ψ : fiber k B χ) (r : R) :
    ψ.1 (algebraMap R B r) = χ r := by
  have h := congrArg (fun φ : R →ₐ[k] k => φ r) ψ.2
  simpa using h

theorem fiber_aeval {χ : R →ₐ[k] k} (ψ : fiber k B χ) (β : B) (g : R[X]) :
    ψ.1 (aeval β g) = eval₂ (χ : R →+* k) (ψ.1 β) g := by
  rw [aeval_def]
  refine (Polynomial.hom_eval₂ g (algebraMap R B) (ψ.1 : B →+* k) β).trans ?_
  congr 1
  ext r
  exact fiber_apply_algebraMap ψ r

/-- Two points of the fibre agreeing at `β` agree, provided every generator of `B` over `R` has a
`q`-power that is (up to a unit at `χ`) a polynomial in `β`. -/
theorem fiber_ext {χ : R →ₐ[k] k} (s : Set B) (hs : Submodule.span R s = ⊤) (β : B)
    (q : ℕ) [ExpChar k q]
    (hgen : ∀ b ∈ s, ∃ n : ℕ, ∃ c : R, ∃ h : R[X],
      χ c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h)
    (ψ₁ ψ₂ : fiber k B χ) (hβ : ψ₁.1 β = ψ₂.1 β) : ψ₁ = ψ₂ := by
  have hgen' : ∀ b ∈ s, ψ₁.1 b = ψ₂.1 b := by
    intro b hb
    obtain ⟨n, c, h, hc, hbh⟩ := hgen b hb
    have e1 := congrArg ψ₁.1 hbh
    have e2 := congrArg ψ₂.1 hbh
    rw [map_mul, map_pow, fiber_apply_algebraMap, fiber_aeval] at e1 e2
    rw [hβ] at e1
    have h3 : ψ₁.1 b ^ q ^ n = ψ₂.1 b ^ q ^ n := mul_left_cancel₀ hc (e1.trans e2.symm)
    apply iterateFrobenius_inj k q n
    simpa [iterateFrobenius_def] using h3
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  have hx : x ∈ Submodule.span R s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen' y hy
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul r y _ hy =>
    rw [Algebra.smul_def, map_mul, map_mul, fiber_apply_algebraMap, fiber_apply_algebraMap, hy]

/-- Upper bound: the fibre injects into the roots of `f0` mod `χ`. -/
theorem card_fiber_le {χ : R →ₐ[k] k} (s : Set B) (hs : Submodule.span R s = ⊤) (β : B)
    (q : ℕ) [ExpChar k q]
    (hgen : ∀ b ∈ s, ∃ n : ℕ, ∃ c : R, ∃ h : R[X],
      χ c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h)
    (f0 : R[X]) (hf0 : f0.Monic) (hβ0 : aeval β f0 = 0) :
    Finite (fiber k B χ) ∧ Nat.card (fiber k B χ) ≤ f0.natDegree := by
  classical
  set p : k[X] := f0.map (χ : R →+* k) with hpdef
  have hp : p ≠ 0 := (hf0.map _).ne_zero
  let F : fiber k B χ → p.roots.toFinset := fun ψ => ⟨ψ.1 β, by
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot, hpdef, eval_map, ← fiber_aeval, hβ0,
      map_zero]⟩
  have hF : Function.Injective F := fun ψ₁ ψ₂ h =>
    fiber_ext s hs β q hgen ψ₁ ψ₂ (congrArg Subtype.val h)
  refine ⟨Finite.of_injective F hF, ?_⟩
  calc Nat.card (fiber k B χ) ≤ Nat.card p.roots.toFinset := Nat.card_le_card_of_injective F hF
    _ = p.roots.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ = f0.natDegree := hf0.natDegree_map _

end Fibre

end RamanujanPetersson.IsogDegA

/-!
# S4-IsogDegA, file Fib2: generic fibre count, part 2 (lower bound via going-up, exact count)
-/


open Polynomial

namespace RamanujanPetersson.IsogDegA

section Lower

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {R B : Type*} [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] [Algebra.IsIntegral R B]

/-- Lower bound, pointwise: every root `α` of `f0 mod χ` is the value at `β` of a point of the
fibre over `χ`, provided `f0` divides every polynomial relation of `β`. -/
theorem exists_fiber_of_root (χ : R →ₐ[k] k) (β : B) (f0 : R[X])
    (hdvd : ∀ g : R[X], aeval β g = 0 → f0 ∣ g) (α : k)
    (hα : eval₂ (χ : R →+* k) α f0 = 0) : ∃ ψ : fiber k B χ, ψ.1 β = α := by
  classical
  set ev : R[X] →+* k := eval₂RingHom (χ : R →+* k) α with hev
  have hevC : ∀ c : k, ev (C (algebraMap k R c)) = c := fun c => by
    simp [hev]
  have hsurj : Function.Surjective ev := fun c => ⟨_, hevC c⟩
  have hPmax : (RingHom.ker ev).IsMaximal := RingHom.ker_isMaximal_of_surjective ev hsurj
  let _ : Algebra R[X] B := (aeval β).toRingHom.toAlgebra
  have halg : ∀ g : R[X], algebraMap R[X] B g = aeval β g := fun _ => rfl
  have hcomp : (algebraMap R[X] B).comp (C : R →+* R[X]) = algebraMap R B := by
    ext r; simp [halg]
  have hint : Algebra.IsIntegral R[X] B := by
    refine ⟨fun x => ?_⟩
    have h0 : ((algebraMap R[X] B).comp (C : R →+* R[X])).IsIntegral := by
      rw [hcomp]; exact fun y => Algebra.IsIntegral.isIntegral (R := R) y
    exact RingHom.IsIntegral.tower_top (f := (C : R →+* R[X])) (g := algebraMap R[X] B) h0 x
  have hker : RingHom.ker (algebraMap R[X] B) ≤ RingHom.ker ev := by
    intro g hg
    rw [RingHom.mem_ker, halg] at hg
    obtain ⟨h, rfl⟩ := hdvd g hg
    rw [RingHom.mem_ker, map_mul]
    simp [hev, hα]
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker ev) hker
  -- key: modulo `Q`, `aeval β g` is the constant `ev g`
  have hkey : ∀ g : R[X], Ideal.Quotient.mk Q (aeval β g) =
      algebraMap k (B ⧸ Q) (ev g) := by
    intro g
    have hmem : g - C (algebraMap k R (ev g)) ∈ RingHom.ker ev := by
      rw [RingHom.mem_ker, map_sub, hevC, sub_self]
    rw [← hQ, Ideal.mem_comap, halg, map_sub] at hmem
    rw [Ideal.Quotient.eq.mpr hmem, aeval_C, ← IsScalarTower.algebraMap_apply]
    rfl
  have hR : ∀ r : R, Ideal.Quotient.mk Q (algebraMap R B r) = algebraMap k (B ⧸ Q) (χ r) := by
    intro r
    have := hkey (C r)
    rwa [aeval_C, show ev (C r) = χ r by simp [hev]] at this
  -- `B ⧸ Q` is integral, hence equal to `k`
  have hintk : Algebra.IsIntegral k (B ⧸ Q) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) b
    refine ⟨p.map (χ : R →+* k), hpm.map _, ?_⟩
    rw [eval₂_map]
    have hc : (algebraMap k (B ⧸ Q)).comp (χ : R →+* k) =
        (Ideal.Quotient.mk Q).comp (algebraMap R B) := by
      ext r; exact (hR r).symm
    rw [hc, ← hom_eval₂, hp, map_zero]
  have hbij : Function.Bijective (algebraMap k (B ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] B ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ Q)) hbij
  let ψ : B →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k Q)
  have hψ : ∀ b : B, e (ψ b) = Ideal.Quotient.mk Q b := fun b => by
    simp [ψ]
  have hψg : ∀ g : R[X], ψ (aeval β g) = ev g := by
    intro g
    apply e.injective
    rw [hψ, hkey]
    rfl
  refine ⟨⟨ψ, ?_⟩, ?_⟩
  · ext r
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    have := hψg (C r)
    rwa [aeval_C, show ev (C r) = χ r by simp [hev]] at this
  · have := hψg X
    rwa [aeval_X, show ev X = α by simp [hev]] at this

/-- Exact count: if moreover `f0 mod χ` is separable, the fibre has exactly `deg f0` points. -/
theorem card_fiber_eq (χ : R →ₐ[k] k) (s : Set B) (hs : Submodule.span R s = ⊤) (β : B)
    (q : ℕ) [ExpChar k q]
    (hgen : ∀ b ∈ s, ∃ n : ℕ, ∃ c : R, ∃ h : R[X],
      χ c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h)
    (f0 : R[X]) (hf0 : f0.Monic) (hβ0 : aeval β f0 = 0)
    (hdvd : ∀ g : R[X], aeval β g = 0 → f0 ∣ g) (hsep : (f0.map (χ : R →+* k)).Separable) :
    Finite (fiber k B χ) ∧ Nat.card (fiber k B χ) = f0.natDegree := by
  classical
  obtain ⟨hfin, hle⟩ := card_fiber_le s hs β q hgen f0 hf0 hβ0
  refine ⟨hfin, le_antisymm hle ?_⟩
  set p : k[X] := f0.map (χ : R →+* k) with hpdef
  have hp : p ≠ 0 := (hf0.map _).ne_zero
  have hroot : ∀ α ∈ p.roots.toFinset, ∃ ψ : fiber k B χ, ψ.1 β = α := by
    intro α hα
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot, hpdef, eval_map] at hα
    exact exists_fiber_of_root χ β f0 hdvd α hα
  choose G hG using hroot
  let G' : p.roots.toFinset → fiber k B χ := fun α => G α.1 α.2
  have hG' : Function.Injective G' := by
    intro a b hab
    apply Subtype.ext
    rw [← hG a.1 a.2, ← hG b.1 b.2]
    exact congrArg (fun ψ : fiber k B χ => ψ.1 β) hab
  calc f0.natDegree = p.natDegree := (hf0.natDegree_map _).symm
    _ = Multiset.card p.roots := IsAlgClosed.card_roots_eq_natDegree.symm
    _ = p.roots.toFinset.card := (Multiset.toFinset_card_of_nodup (nodup_roots hsep)).symm
    _ = Nat.card p.roots.toFinset := (Nat.card_eq_finsetCard _).symm
    _ ≤ Nat.card (fiber k B χ) := Nat.card_le_card_of_injective G' hG'

end Lower

end RamanujanPetersson.IsogDegA

/-!
# S4-IsogDegA, file Fib3: generic fibre count, part 3 (choice of a generic primitive element)
-/


open Polynomial IntermediateField

namespace RamanujanPetersson.IsogDegA

section Adjoin

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem adjoin_simple_mul_eq {e : K} (he : e ≠ 0) (θ : L) :
    K⟮algebraMap K L e * θ⟯ = K⟮θ⟯ := by
  apply le_antisymm
  · rw [adjoin_simple_le_iff]
    exact mul_mem (IntermediateField.algebraMap_mem _ e) (mem_adjoin_simple_self K θ)
  · rw [adjoin_simple_le_iff]
    have h : algebraMap K L e⁻¹ * (algebraMap K L e * θ) ∈ K⟮algebraMap K L e * θ⟯ :=
      mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_simple_self K _)
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one, one_mul] at h

theorem minpoly_mul_eq {e : K} (he : e ≠ 0) {θ : L} (hθ : IsIntegral K θ) :
    minpoly K (algebraMap K L e * θ) = (minpoly K θ).scaleRoots e := by
  have hθ' : IsIntegral K (algebraMap K L e * θ) := isIntegral_algebraMap.mul hθ
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hθ')
    ((monic_scaleRoots_iff e).2 (minpoly.monic hθ)) ?_ ?_).symm
  · exact minpoly.dvd K _ (scaleRoots_aeval_eq_zero (minpoly.aeval K θ))
  · refine le_of_eq ?_
    rw [natDegree_scaleRoots, ← adjoin.finrank hθ, ← adjoin.finrank hθ', adjoin_simple_mul_eq he]

theorem exists_adjoin_eq_separableClosure [FiniteDimensional K L] :
    ∃ θ : L, K⟮θ⟯ = separableClosure K L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K (separableClosure K L)
  exact ⟨α.1, by rw [← lift_adjoin_simple, hα, lift_top]⟩

end Adjoin

section Lift

variable {R K L : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

theorem exists_monic_lift_minpoly {θ : L} (hθ : IsIntegral K θ) :
    ∃ d : R, d ≠ 0 ∧ ∃ f0 : R[X], f0.Monic ∧
      f0.map (algebraMap R K) = minpoly K (algebraMap R L d * θ) := by
  classical
  have hp : (minpoly K θ).Monic := minpoly.monic hθ
  obtain ⟨f0, hf1, -, hf2⟩ := lifts_and_natDegree_eq_and_monic
    (IsLocalization.scaleRoots_commonDenom_mem_lifts (nonZeroDivisors R) (minpoly K θ)
      (by rw [hp.leadingCoeff]; exact one_mem _)) ((monic_scaleRoots_iff _).2 hp)
  set D := IsLocalization.commonDenom (nonZeroDivisors R) (minpoly K θ).support (minpoly K θ).coeff
  have hD : algebraMap R K D ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors D.2
  refine ⟨D, nonZeroDivisors.ne_zero D.2, f0, hf2, ?_⟩
  rw [hf1, IsScalarTower.algebraMap_apply R K L, minpoly_mul_eq hD hθ]

omit [IsDomain R] in
/-- A monic lift of a minimal polynomial divides every polynomial relation. -/
theorem dvd_of_aeval_eq_zero {B : Type*} [CommRing B] [Algebra R B] [Algebra B L]
    [IsScalarTower R B L] (β : B) (f0 : R[X]) (hf0 : f0.Monic)
    (hmap : f0.map (algebraMap R K) = minpoly K (algebraMap B L β)) (g : R[X])
    (hg : aeval β g = 0) : f0 ∣ g := by
  have h1 : minpoly K (algebraMap B L β) ∣ g.map (algebraMap R K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, hg, map_zero]
  have h2 : (g %ₘ f0).map (algebraMap R K) = 0 := by
    rw [map_modByMonic _ hf0, (modByMonic_eq_zero_iff_dvd (hf0.map _)).2 (hmap ▸ h1)]
  have h3 : g %ₘ f0 = 0 :=
    map_injective _ (IsFractionRing.injective R K) (by rw [h2, Polynomial.map_zero])
  exact (modByMonic_eq_zero_iff_dvd hf0).1 h3

/-- Separability of `f0` over `Frac R` spreads out: it holds modulo every `χ` with `χ a ≠ 0`. -/
theorem exists_sep_witness (k : Type*) [Field k] (f0 : R[X])
    (hsep : (f0.map (algebraMap R K)).Separable) :
    ∃ a : R, a ≠ 0 ∧ ∀ χ : R →+* k, χ a ≠ 0 → (f0.map χ).Separable := by
  classical
  obtain ⟨u, v, huv⟩ := hsep
  obtain ⟨bu, hbu, hu⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) u
  obtain ⟨bv, hbv, hv⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) v
  set U := IsLocalization.integerNormalization (nonZeroDivisors R) u
  set V := IsLocalization.integerNormalization (nonZeroDivisors R) v
  have hu' : U.map (algebraMap R K) = C (algebraMap R K bu) * u := by
    rw [hu, ← smul_eq_C_mul, algebraMap_smul]
  have hv' : V.map (algebraMap R K) = C (algebraMap R K bv) * v := by
    rw [hv, ← smul_eq_C_mul, algebraMap_smul]
  have key : (C (bu * bv) : R[X]) = C bv * U * f0 + C bu * V * derivative f0 := by
    apply map_injective (algebraMap R K) (IsFractionRing.injective R K)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hu', hv',
      ← derivative_map, map_mul]
    linear_combination (-(C (algebraMap R K bu) * C (algebraMap R K bv))) * huv
  refine ⟨bu * bv, mul_ne_zero (nonZeroDivisors.ne_zero hbu) (nonZeroDivisors.ne_zero hbv), ?_⟩
  intro χ hχ
  have hk := congrArg (Polynomial.map χ) key
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hk
  have hinv : C (χ (bu * bv))⁻¹ * C (χ (bu * bv)) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hχ, C_1]
  rw [Separable, derivative_map]
  refine ⟨C (χ (bu * bv))⁻¹ * (C (χ bv) * U.map χ), C (χ (bu * bv))⁻¹ * (C (χ bu) * V.map χ), ?_⟩
  linear_combination (-C (χ (bu * bv))⁻¹) * hk + hinv

end Lift

section Generic

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

variable (R B K L) in
/-- A generic element: `β ∈ B` generating the separable closure, with a monic lift over `R` of its
minimal polynomial. -/
theorem exists_generic_element :
    ∃ β : B, ∃ f0 : R[X], f0.Monic ∧ f0.map (algebraMap R K) = minpoly K (algebraMap B L β) ∧
      K⟮algebraMap B L β⟯ = separableClosure K L := by
  have : FiniteDimensional K L := finiteDimensional_of_finite (R := R) (B := B)
  obtain ⟨θ0, hθ0⟩ := exists_adjoin_eq_separableClosure (K := K) (L := L)
  obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective (A := B) θ0
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hne := Ideal.comap_ne_bot_of_integral_mem hc0 (Ideal.mem_span_singleton_self c)
    (Algebra.IsIntegral.isIntegral (R := R) c)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hr
  obtain ⟨c', hc'⟩ := hr
  have hcL : algebraMap B L c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  have hrK : algebraMap R K r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hr0)
  have hθ : algebraMap B L (b * c') = algebraMap K L (algebraMap R K r) * θ0 := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R B L, ← hc', ← hbc,
      map_mul, map_mul]
    first | (field_simp; ring) | field_simp
  have hθint : IsIntegral K (algebraMap B L (b * c')) :=
    ((Algebra.IsIntegral.isIntegral (R := R) (b * c')).map
      (IsScalarTower.toAlgHom R B L)).tower_top
  obtain ⟨d, hd, f0, hf0, hmap⟩ := exists_monic_lift_minpoly (R := R) hθint
  have hdK : algebraMap R K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hd)
  refine ⟨algebraMap R B d * (b * c'), f0, hf0, ?_, ?_⟩
  · rw [map_mul, ← IsScalarTower.algebraMap_apply]; exact hmap
  · rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K L,
      adjoin_simple_mul_eq hdK, hθ, adjoin_simple_mul_eq hrK, hθ0]

end Generic

end RamanujanPetersson.IsogDegA

/-!
# S4-IsogDegA, file Fib4: the generic fibre has `finSepDegree` points (O1 headline)

`B` finite over `R` (domains, `k`-algebras, `k` algebraically closed), `K = Frac R`, `L = Frac B`.
Over a dense open set of `k`-points `χ` of `Spec R` (those with `χ a ≠ 0`), the fibre of
`Spec B → Spec R` has exactly `[L : K]_s` points.
-/


open Polynomial IntermediateField

namespace RamanujanPetersson.IsogDegA

section Headline

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

/-- Every element of `B` has a `q`-power which, up to a nonzero constant, is a polynomial in a
generic element. -/
theorem exists_pow_eq_aeval (q : ℕ) [ExpChar K q] (β : B)
    (hβ : K⟮algebraMap B L β⟯ = separableClosure K L) (b : B) :
    ∃ n : ℕ, ∃ c : R, ∃ h : R[X], c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h := by
  have : FiniteDimensional K L := finiteDimensional_of_finite (R := R) (B := B)
  have : ExpChar (separableClosure K L) q :=
    expChar_of_injective_algebraMap (algebraMap K _).injective q
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem (separableClosure K L) q (algebraMap B L b)
  obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
  have hθint : IsIntegral K (algebraMap B L β) :=
    ((Algebra.IsIntegral.isIntegral (R := R) β).map (IsScalarTower.toAlgHom R B L)).tower_top
  have hmem : algebraMap B L b ^ q ^ n ∈ Algebra.adjoin K {algebraMap B L β} := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic, hβ, ← hy]
    exact y.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨hK, hhK⟩ := (AlgHom.mem_range _).1 hmem
  obtain ⟨c, hc, hH⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) hK
  refine ⟨n, c, IsLocalization.integerNormalization (nonZeroDivisors R) hK,
    nonZeroDivisors.ne_zero hc, ?_⟩
  apply IsFractionRing.injective B L
  calc algebraMap B L (algebraMap R B c * b ^ q ^ n)
      = algebraMap R L c * algebraMap B L b ^ q ^ n := by
        rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    _ = aeval (algebraMap B L β)
          ((IsLocalization.integerNormalization (nonZeroDivisors R) hK).map (algebraMap R K)) := by
        rw [hH, ← algebraMap_smul K c hK, smul_eq_C_mul, aeval_mul, aeval_C, hhK,
          ← IsScalarTower.algebraMap_apply]
    _ = _ := by rw [aeval_map_algebraMap, aeval_algebraMap_apply]

variable (k : Type*) [Field k] [IsAlgClosed k] [Algebra k R] [Algebra k B] [IsScalarTower k R B]

variable (K L) in
/-- **O1 headline.** There is `a ≠ 0` in `R` such that over every `k`-point `χ` with `χ a ≠ 0` the
fibre has exactly `Field.finSepDegree K L` points. -/
theorem exists_card_fiber_eq_finSepDegree :
    ∃ a : R, a ≠ 0 ∧ ∀ χ : R →ₐ[k] k, χ a ≠ 0 →
      Finite (fiber k B χ) ∧ Nat.card (fiber k B χ) = Field.finSepDegree K L := by
  classical
  have : FiniteDimensional K L := finiteDimensional_of_finite (R := R) (B := B)
  obtain ⟨q, hq⟩ := ExpChar.exists k
  have : ExpChar K q := expChar_of_injective_ringHom
    (f := (algebraMap R K).comp (algebraMap k R)) (RingHom.injective _) q
  obtain ⟨β, f0, hf0, hmap, hadj⟩ := exists_generic_element R B K L
  have hθint : IsIntegral K (algebraMap B L β) :=
    ((Algebra.IsIntegral.isIntegral (R := R) β).map (IsScalarTower.toAlgHom R B L)).tower_top
  have hsep : (f0.map (algebraMap R K)).Separable := by
    rw [hmap]
    have h : algebraMap B L β ∈ separableClosure K L := hadj ▸ mem_adjoin_simple_self K _
    exact h
  obtain ⟨a1, ha1, hsepχ⟩ := exists_sep_witness (K := K) k f0 hsep
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := B)
  have hg := fun b : B => exists_pow_eq_aeval (R := R) (K := K) (L := L) q β hadj b
  choose n c h hc hch using hg
  refine ⟨a1 * ∏ b ∈ s, c b, mul_ne_zero ha1 (Finset.prod_ne_zero_iff.2 fun b _ => hc b), ?_⟩
  intro χ hχ
  rw [map_mul, map_prod] at hχ
  have hχ1 : χ a1 ≠ 0 := left_ne_zero_of_mul hχ
  have hχ2 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hχ)
  have hβ0 : aeval β f0 = 0 := by
    have h0 : aeval (algebraMap B L β) (f0.map (algebraMap R K)) = 0 := by
      rw [hmap]; exact minpoly.aeval K _
    rw [aeval_map_algebraMap, aeval_algebraMap_apply] at h0
    exact IsFractionRing.injective B L (h0.trans (map_zero _).symm)
  have hdeg : f0.natDegree = Field.finSepDegree K L := by
    rw [← hf0.natDegree_map (algebraMap R K), hmap, ← adjoin.finrank hθint, hadj,
      Field.finSepDegree_eq K L]
    rfl
  rw [← hdeg]
  exact card_fiber_eq χ (s : Set B) hs β q (fun b hb => ⟨n b, c b, h b, hχ2 b hb, hch b⟩) f0 hf0
    hβ0 (dvd_of_aeval_eq_zero (K := K) (L := L) β f0 hf0 hmap) (hsepχ χ hχ1)

end Headline

end RamanujanPetersson.IsogDegA

theorem solution
    (k R B K L : Type u) [Field k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] [Module.Finite R B]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R B L] :
    ∃ a : R, a ≠ 0 ∧ ∀ χ : R →ₐ[k] k, χ a ≠ 0 →
      Finite {ψ : B →ₐ[k] k // ψ.comp (IsScalarTower.toAlgHom k R B) = χ} ∧
      Nat.card {ψ : B →ₐ[k] k // ψ.comp (IsScalarTower.toAlgHom k R B) = χ} =
        Field.finSepDegree K L := by
  exact RamanujanPetersson.IsogDegA.exists_card_fiber_eq_finSepDegree (R := R) (B := B) (K := K)
    (L := L) (k := k)
