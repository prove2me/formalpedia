-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaOnto
-- name    : RPLib_S4_TameInertiaOnto
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:54:48.812138+00:00
-- url     : https://prove2.me/theorems/f31ed7e9-ae80-4d90-91fa-85f4aff23a81
-- title:
--   The tame character reaches every $N$-th root of unity
-- statement:
--   At a nonzero prime $Q$ of the pro-chart lying over a place $x$ of $R_0$ at which some $a \in A$ has a pole, with $N$ a unit and $\zeta \in K_U$ a primitive $N$-th root of unity: using a pole element $f$ of order $N n + 1$, the Abhyankar polynomial $X^{N(p+1)} - f X^N + 1$ (roots in $K_U$), the small root $w$ of $X^{p+1} - f X + 1$ and $z^N = w$, the file produces $Z \in K_U$ with $Z^N$ fixed by every element of $\operatorname{Gal}(K_U/K)$ stabilising $Q$ and an element $g \in I(Q)$ with $$g(Z) = \zeta Z.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   S. S. Abhyankar, Coverings of algebraic curves, Amer. J. Math. 79 (1957), 825-856; J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter IV, Section 2; A. Grothendieck, J. P. Murre, The Tame Fundamental Group of a Formal Neighbourhood of a Divisor with Normal Crossings on a Scheme, Lecture Notes in Math. 208, Springer (1971)

import Mathlib
import Definitions.Def_RPLib_S4_TameInertiaCount
import Definitions.Def_RPLib_S4_TameInertiaPole
import Definitions.Def_RPLib_S4_TameInertiaLift
import Definitions.Def_RPLib_S4_KummerRam
import Definitions.Def_RPLib_S4_TameInertiaStab

/-!
# Tame inertia, part Onto: the tame character reaches every `N`-th root of unity (S4-PD item (2), T8)

At a boundary prime `Q` of the pro-chart (a pole `a ∈ A` at `x = Q ∩ R0`), take the pole element `f` of order
`N n + 1` (`exists_pole_mod`), the Abhyankar polynomial `abhy p N f` (roots in `K_U`), a finite Galois level `L ≤ K_U`
containing its roots and `ζ`, the small root `w` of `X^(p+1) - f X + 1` and `z^N = w`. The count
`exists_inertia_smul_eq` at `P = Q ∩ B_L` and the inertia lift `exists_inertia_lift` give
`exists_inertia_zeta_mul`: some `Z ∈ K_U` with `Z^N` fixed by every element of `Pi1` stabilising `Q` (in particular
by `I(Q)`, `stab_of_mem_inertia`) and `g ∈ I(Q)` with `g Z = ζ Z`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain WithZero

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer Swan

noncomputable section

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **T8.** At a boundary prime with a pole, some `Z ∈ K_U` has `Z^N` fixed by the stabiliser of `Q` (so by the
inertia group `I(Q)`) and an inertia element `g` with `g Z = ζ Z`, for any `N`-th root of unity `ζ ∈ K_U` (`N` a unit). -/
theorem exists_inertia_zeta_mul {Q : Ideal (proChart A K R0)} (hQ : IsBdryPrime A K R0 Q)
    [Ring.HasFiniteQuotients R0] {p : ℕ} [Fact p.Prime] [CharP K p] {N : ℕ} (hN0 : 0 < N)
    (hN : IsUnit (N : A)) {ζ : maxUnram A K} (hζ : ζ ^ N = 1)
    (x : HeightOneSpectrum R0) (hx : x.asIdeal = Q.comap (algebraMap R0 (proChart A K R0)))
    {a : A} (ha : 1 < x.valuation K (algebraMap A K a)) :
    ∃ Z : maxUnram A K, Z ≠ 0 ∧ (∀ σ : Pi1 A K, (∀ b : proChart A K R0, σ • b ∈ Q ↔ b ∈ Q) → σ (Z ^ N) = Z ^ N) ∧
      ∃ g ∈ Q.inertia (Pi1 A K), g Z = ζ * Z := by
  classical
  haveI := hQ.1
  have : Nontrivial A := (algebraMap A K).domain_nontrivial
  have hp : 0 < p := (Fact.out : p.Prime).pos
  -- the pole element `f` of order `N n + 1`
  obtain ⟨f, n, -, hfv⟩ := exists_pole_mod x (N - 1) ha
  have hNN : N - 1 + 1 = N := Nat.sub_add_cancel hN0
  rw [hNN] at hfv
  have hcN : Nat.Coprime (N * n + 1) N := by
    have h := coprime_pole_order (N - 1) n
    rwa [hNN] at h
  -- the level `L`
  obtain ⟨s, hsdef⟩ : ∃ s : Finset (AlgebraicClosure K), s = insert (ζ : AlgebraicClosure K)
      (((abhy p N f).map (algebraMap A K)).aroots (AlgebraicClosure K)).toFinset := ⟨_, rfl⟩
  have hroot : ∀ y : AlgebraicClosure K, aeval y (abhy p N f) = 0 → y ∈ s := by
    intro y hy
    rw [hsdef, Finset.mem_insert, Multiset.mem_toFinset]
    refine Or.inr (mem_aroots.2 ⟨((abhy_monic hp hN0 f).map (algebraMap A K)).ne_zero, ?_⟩)
    rw [aeval_map_algebraMap]
    exact hy
  obtain ⟨L, hL, hsL⟩ := exists_unramSet_of_finite A K s (by
    intro y hy
    rw [hsdef, Finset.mem_insert, Multiset.mem_toFinset] at hy
    rcases hy with rfl | hy
    · exact ζ.2
    · have h := (mem_aroots.1 hy).2
      rw [aeval_map_algebraMap] at h
      exact mem_maxUnram_abhy hp hN f h)
  have hsL' : ∀ y ∈ s, y ∈ L := fun y hy => hsL (IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 hy))
  haveI : FiniteDimensional K L := hL.1
  haveI : IsGalois K L := hL.2.1
  have hLU : L ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hL
  haveI : IsFractionRing (integralClosure R0 L) L := integralClosure.isFractionRing_of_finite_extension (A := R0) K L
  haveI : IsDedekindDomain (integralClosure R0 L) := integralClosure.isDedekindDomain (A := R0) (K := K) (L := L)
  haveI : Module.Finite R0 (integralClosure R0 L) := IsIntegralClosure.finite R0 K L (integralClosure R0 L)
  haveI : IsGaloisGroup (L ≃ₐ[K] L) R0 (integralClosure R0 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) R0 (integralClosure R0 L) K L
  haveI : Module.IsTorsionFree R0 (integralClosure R0 L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_integralClosure_injective R0 L)
  haveI : Ring.HasFiniteQuotients (integralClosure R0 L) := Ring.HasFiniteQuotients.of_module_finite R0 _
  -- the prime `P` of `B_L` under `Q`
  obtain ⟨P0, hP0def⟩ : ∃ P0 : Ideal (integralClosure R0 L), P0 = Q.comap (inclU R0 hLU) := ⟨_, rfl⟩
  have hPp : P0.IsPrime := by rw [hP0def]; exact Ideal.IsPrime.comap _
  have hP0 : P0 ≠ ⊥ := by
    haveI : Nontrivial R0 := (algebraMap R0 K).domain_nontrivial
    obtain ⟨y, hyQ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    have h1 : Q.comap (algebraMap R0 (proChart A K R0)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem hy0 hyQ (Algebra.IsIntegral.isIntegral y)
    obtain ⟨r, hrQ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    refine (Submodule.ne_bot_iff _).2 ⟨algebraMap R0 (integralClosure R0 L) r, ?_, ?_⟩
    · rw [hP0def, Ideal.mem_comap, AlgHom.commutes]
      exact hrQ
    · intro h
      exact hr0 (algebraMap_integralClosure_injective R0 L (h.trans (map_zero _).symm))
  let P : HeightOneSpectrum (integralClosure R0 L) := ⟨P0, hPp, hP0⟩
  haveI : Finite (integralClosure R0 L ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient hP0
  have hP : P.asIdeal = Q.comap (inclU R0 hLU) := hP0def
  have hxP : P.under R0 = x := by
    refine HeightOneSpectrum.ext ?_
    ext r
    show algebraMap R0 (integralClosure R0 L) r ∈ P0 ↔ r ∈ x.asIdeal
    rw [hP0def, Ideal.mem_comap, AlgHom.commutes, hx, Ideal.mem_comap]
  -- valuations of `f`
  have hf0 : algebraMap A K f ≠ 0 := by
    intro h
    rw [h, map_zero] at hfv
    exact exp_ne_zero hfv.symm
  have hav : adicAdd (P.under R0) (algebraMap A K f) = ((-((N * n + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [hxP, adicAdd_apply, negLogV_of_ne x hf0, hfv, log_exp]
  have hF : 1 < P.valuation L (algebraMap K L (algebraMap A K f)) :=
    one_lt_valuation_level hLU x hx P hP (by
      rw [hfv, ← exp_zero, exp_lt_exp]
      exact_mod_cast Nat.succ_pos _)
  -- the trinomial splits in `L`
  have hudL : udField A K (abhy p N f) ≤ L := by
    show IntermediateField.adjoin K _ ≤ L
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    refine hsL' y (hroot y ?_)
    have h := (mem_rootSet.1 hy).2
    rwa [aeval_map_algebraMap] at h
  have hs1 : (((abhy p 1 f).map (algebraMap A K)).map (algebraMap K L)).Splits := by
    refine IntermediateField.splits_of_splits (IsAlgClosed.splits _) fun y hy => ?_
    exact hudL (udField_abhy_one_le hp hN0 f (IntermediateField.subset_adjoin K _ hy))
  have hs : (trin p (algebraMap K L (algebraMap A K f))).Splits := by
    rw [← map_abhy_one]
    exact hs1
  -- the small root `w` and `z^N = w`
  obtain ⟨w, ⟨hw, hwv⟩, -⟩ := trin_existsUnique_small (P.valuation L) hp hF hs
  have hw' := (trin_isRoot_iff p _ w).1 hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (w : AlgebraicClosure K) hN0
  have hzr : aeval z (abhy p N f) = 0 := by
    have h := congrArg L.val hw'
    rw [map_add, map_sub, map_mul, map_pow, map_one, map_zero, AlgHom.commutes] at h
    rw [aeval_abhy, hz, IsScalarTower.algebraMap_apply A K (AlgebraicClosure K)]
    exact h
  let zL : L := ⟨z, hsL' z (hroot z hzr)⟩
  have hzN : zL ^ N = w := L.val.injective (by rw [map_pow]; exact hz)
  let ζL : L := ⟨(ζ : AlgebraicClosure K), hsL' _ (by rw [hsdef]; exact Finset.mem_insert_self _ _)⟩
  have hζN : ζL ^ N = 1 := L.val.injective (by
    have h := congrArg (maxUnram A K).val hζ
    rw [map_pow, map_one] at h
    rw [map_pow, map_one]
    exact h)
  -- the count at level `L` and the lift
  obtain ⟨τ, hτI, hτz⟩ := exists_inertia_smul_eq (R := R0) (G := L ≃ₐ[K] L) (fun _ _ => rfl) P hp hN0 hcN hav
    hF hs (fun σ => σ.commutes _) hw hwv hzN hζN
  have hτ' : τ ∈ (Q.comap (inclU R0 hLU)).inertia (L ≃ₐ[K] L) := by
    rw [← hP]
    exact hτI
  obtain ⟨g, hgI, hg⟩ := exists_inertia_lift hLU hτ'
  have hzL0 : zL ≠ 0 := fun h => hw0 (by rw [← hzN, h, zero_pow hN0.ne'])
  refine ⟨IntermediateField.inclusion hLU zL, (map_ne_zero_iff _ (IntermediateField.inclusion hLU).injective).2 hzL0,
    fun σ hσ => ?_, g, hgI, ?_⟩
  · rw [← map_pow (IntermediateField.inclusion hLU) zL N, hzN]
    exact fix_of_stab_small hLU P hP hp hF hs hw hwv hσ
  · have hτz' : τ zL = ζL * zL := hτz
    rw [hg, hτz', map_mul]
    rfl

end

end TameInertia
end RamanujanPetersson


