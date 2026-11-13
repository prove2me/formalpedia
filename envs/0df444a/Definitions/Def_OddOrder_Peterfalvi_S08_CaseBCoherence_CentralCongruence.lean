-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence_CentralCongruence
-- name    : OddOrder_Peterfalvi_S08_CaseBCoherence_CentralCongruence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:56:44.51379+00:00
-- url     : https://prove2.me/theorems/745e21f3-949e-412e-843c-954af2e55aac
-- title:
--   Peterfalvi §8 case (B): central congruence and coefficient bounds
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §8, the (6.8.2) branch of the (6.8) coherence capstone. This is the case-(B) ($Z=W_2$, $W_2$ prime central) analogue of the case-(A)/Frobenius central-commutator program.
--
--   Main results: `SibleyDadeHypothesis.peterfalvi_67_central` (the case-(B) (6.7) adapter), `restrict_extension_Yset_charValue_cong_caseB` (the (6.7)-congruence for $\eta^{\tau_1}$), `card_H_dvd_card_W2_mul_regCharCoeff` (the integration core $|H|\mid|W_2|a$) and `inner_tau_alpha_dvd_index` ($\langle\alpha^\tau,\psi\rangle$ is an integer divisible by $|H:W_2|$).
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBCoherence/CentralCongruence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBCoherence/CentralCongruence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCore
import Definitions.Def_OddOrder_Peterfalvi_S07_CoherenceGalois

namespace OddOrder.RepresentationTheory

open ClassFunction

open scoped OddOrder.AlgInt

variable {G : Type*} [Group G]

/-- **Integer trichotomy from divisibility and a strict `< 2a²` norm bound** (Peterfalvi (6.8.2.2)
quadratic endgame).  The `< 2a²` variant of `eq_zero_or_edge_of_dvd_of_normBound` (which uses the
`≤ 1 + a²` bound of the Frobenius (6.8.1) case): in case (B) the source norm is `|L:Z| + |H:Z|²`
with `|L:Z| < |H:Z|²` (the `W₁`-fixed-point-free bound), giving `‖α^τ‖² < 2|H:Z|²`.

Writing `b = a·x` (`a = |H:Z|`), the bound forces `(x−1)² + (m−1)x² < 2`, hence `≤ 1`, so
`x ∈ {0, 1}` (and `x = 1` needs `m = 2`); `x = −1` is excluded since `4a² + (m−1)a² ≥ 2a²`. -/
theorem eq_zero_or_edge_of_dvd_of_normLt {a b m : ℤ}
    (ha : 2 ≤ a) (hm : 2 ≤ m) (hdvd : a ∣ b)
    (hnorm : (b - a) ^ 2 + (m - 1) * b ^ 2 < 2 * a ^ 2) :
    b = 0 ∨ (b = a ∧ m = 2) := by
  obtain ⟨x, rfl⟩ := hdvd
  have ha0 : (0 : ℤ) < a := by linarith
  have hb2 : (a * x) ^ 2 < 2 * a ^ 2 := by
    nlinarith [sq_nonneg (a * x - a), mul_nonneg (by linarith : (0 : ℤ) ≤ m - 2) (sq_nonneg (a *
        x))]
  have hx2 : x ^ 2 ≤ 1 := by
    by_contra h
    push Not at h
    have hx2' : 2 ≤ x ^ 2 := h
    nlinarith [hb2, mul_pos ha0 ha0, mul_le_mul_of_nonneg_left hx2' (le_of_lt (mul_pos ha0 ha0))]
  have hxlo : -1 ≤ x := by nlinarith [hx2, sq_nonneg (x + 1)]
  have hxhi : x ≤ 1 := by nlinarith [hx2, sq_nonneg (x - 1)]
  interval_cases x
  · exfalso; nlinarith [hnorm, ha, hm, mul_pos ha0 ha0]
  · left; ring
  · right
    refine ⟨by ring, ?_⟩
    nlinarith [hnorm, ha, hm, mul_pos ha0 ha0]

/-- **Galois action commutes with induction.**  For a ring automorphism `σ` of `ℂ` (the cyclotomic
Galois action of Peterfalvi (1.9)) and `θ : ClassFunction ↥H ℂ`,
`σ(Ind_H^G θ) = Ind_H^G (σθ)`.  Indeed `Ind_H^G θ (g) = |H|⁻¹ ∑_x induceTerm θ x g` and `σ` is a
ring homomorphism that fixes the rational coefficient `|H|⁻¹` (`map_natCast`/`map_inv₀`) and acts
termwise on the `θ`-values (`induceTerm` is `θ ⟨x⁻¹gx,·⟩` or `0`, both `σ`-equivariant).

This is the engine behind the Galois-closure of the `Y = S(H')` family (each `Ind_H^L (linear χ)`
maps to `Ind_H^L (linear (σ∘χ))`), one of the hypotheses of
`IsCoherent.extension_constant_on_sharp_of_prime` (Peterfalvi (6.8.2.1)).  Stated in the general
`ClassFunction` namespace (it is not §8-specific) and upstreamable to `InducedCharacter`. -/
theorem ClassFunction.mapRingEquiv_induce {H : Subgroup G} [Fintype G]
    [Invertible (Nat.card H : ℂ)] (σ : ℂ ≃+* ℂ) (θ : ClassFunction ↥H ℂ) :
    mapRingEquiv σ (induce H θ) = induce H (mapRingEquiv σ θ) := by
  ext g
  rw [mapRingEquiv_apply, induce_apply, induce_apply, map_mul, map_sum]
  have hcoef : σ (⅟(Nat.card H : ℂ)) = ⅟(Nat.card H : ℂ) := by
    simp [invOf_eq_inv, map_inv₀, map_natCast]
  rw [hcoef]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : x⁻¹ * g * x ∈ H
  · rw [induceTerm_of_mem _ hx, induceTerm_of_mem _ hx, mapRingEquiv_apply]
  · rw [induceTerm_of_not_mem _ hx, induceTerm_of_not_mem _ hx, map_zero]

/-- **Galois twist of a linear character.**  For `σ : ℂ ≃+* ℂ` and a linear character
`χ : H →* ℂˣ`, the `σ`-image of the class function `linearIrreducibleCharacter χ` is again a linear
character, namely the one of the `σ`-twisted units homomorphism `(Units.map σ) ∘ χ`.  This is the
linear-character case of the Galois-twist `character_galoisTwist` (`σ ∘ χ_ρ`), specialized so it
feeds `mapRingEquiv_induce` directly. -/
theorem ClassFunction.mapRingEquiv_linearIrreducibleCharacter {H : Type*} [Group H]
    (σ : ℂ ≃+* ℂ) (χ : H →* ℂˣ) :
    mapRingEquiv σ (linearIrreducibleCharacter χ : ClassFunction H ℂ)
      = (linearIrreducibleCharacter ((Units.map (σ.toRingHom.toMonoidHom)).comp χ) :
          ClassFunction H ℂ) := by
  ext h
  rw [mapRingEquiv_apply, linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply,
    MonoidHom.comp_apply, Units.coe_map]
  rfl

/-- **Induction from a subgroup of a normal subgroup is supported on that normal subgroup.**
If `H' ≤ N` with `N ◁ G`, then `(Ind_{H'}^G θ).support ⊆ N`: a nonzero value at `g` needs some
conjugate `x⁻¹gx ∈ H' ⊆ N`, and `N` normal then forces `g ∈ N`.  Generalizes
`support_induce_subset_of_normal` (the `H' = N` case) to non-normal source subgroups, as needed for
`Ind_{W₂}^L` with `W₂ ⊆ H ◁ L` in Peterfalvi (6.8.2.2). -/
theorem ClassFunction.support_induce_subset_of_le_normal {G : Type*} [Group G] [Fintype G]
    {N H' : Subgroup G} [N.Normal] [Invertible (Nat.card ↥H' : ℂ)]
    (hH'N : H' ≤ N) (θ : ClassFunction ↥H' ℂ) :
    (ClassFunction.induce H' θ).support ⊆ (N : Set G) := by
  intro g hg
  by_contra hgN
  apply hg
  rw [ClassFunction.induce_apply]
  have hterm : ∀ x : G, ClassFunction.induceTerm H' θ x g = 0 := by
    intro x
    have hnotmem : x⁻¹ * g * x ∉ H' := by
      intro hmem
      apply hgN
      have hconj := ‹N.Normal›.conj_mem (x⁻¹ * g * x) (hH'N hmem) x
      have heq : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
      rwa [heq] at hconj
    rw [ClassFunction.induceTerm_of_not_mem _ hnotmem]
  rw [Finset.sum_eq_zero (fun x _ => hterm x), mul_zero]

/-- **The sum of a nontrivial irreducible character over the group is zero.**  By orthonormality
`⟨φ, 1⟩ = 0` for `φ ≠ 1`, and `⟨φ, 1⟩ = |Γ|⁻¹ ∑_g φ(g)` (the trivial character is constant `1`). -/
theorem sum_apply_eq_zero_of_ne_trivial {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {φ : IrreducibleCharacter Γ}
    (hφ : φ ≠ trivialIrreducibleCharacter Γ) :
    ∑ g : Γ, (φ : ClassFunction Γ ℂ) g = 0 := by
  have h := irreducibleCharacter_inner φ (trivialIrreducibleCharacter Γ)
  rw [if_neg hφ, ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum] at h
  simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter, trivialClassFunction_apply,
    star_one, mul_one] at h
  have hS : (Nat.card Γ : ℂ) * (⅟(Nat.card Γ : ℂ) * ∑ g : Γ, (φ : ClassFunction Γ ℂ) g) = 0 := by
    rw [h, mul_zero]
  rwa [← mul_assoc, mul_invOf_self, one_mul] at hS

/-- **Reverse of `Cong.of_int`: an algebraic-integer congruence between rational integers is an
ordinary `ℤ`-divisibility.**  If `(j : ℂ) ≡ (k : ℂ) [ALGMOD n]` with `j, k, n : ℤ` and `n ≠ 0`, then
`n ∣ j - k` in `ℤ`.  By `cong_def` the quotient `(j - k)/n` is an algebraic integer; being rational,
it is an ordinary integer (`isIntegral_rat_imp_int`), so `n ∣ j - k`.

This converts the (6.7) `ALGMOD |H|` congruence (applied to the rational-integer difference
`ψ(1) − ψ(z) = |W₂|·a`) into the divisibility `|H| ∣ |W₂|·a` of Peterfalvi (6.8.2.2). -/
theorem dvd_of_intCast_algMod {n j k : ℤ} (hn : (n : ℂ) ≠ 0)
    (h : (j : ℂ) ≡ (k : ℂ) [ALGMOD n]) : n ∣ j - k := by
  rw [OddOrder.AlgInt.cong_def] at h
  set q : ℚ := ((j : ℚ) - (k : ℚ)) / (n : ℚ) with hqdef
  have hqcast : (q : ℂ) = ((j : ℂ) - (k : ℂ)) / (n : ℂ) := by rw [hqdef]; push_cast; ring
  rw [← hqcast] at h
  obtain ⟨m, hm⟩ := OddOrder.RepresentationTheory.isIntegral_rat_imp_int h
  have hn0 : n ≠ 0 := Int.cast_ne_zero.mp hn
  have hnℚ : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn0
  have hqm : q = (m : ℚ) := by exact_mod_cast hm
  rw [hqdef, div_eq_iff hnℚ] at hqm
  refine ⟨m, ?_⟩
  have hQ : ((j - k : ℤ) : ℚ) = ((n * m : ℤ) : ℚ) := by push_cast; linear_combination hqm
  exact_mod_cast hQ

/-- **Regular-character decomposition value (Peterfalvi (6.8.2.2) core relation).**  If `f` is a
class function constant on `Γ^#` and `φ` is a nontrivial *linear* irreducible character
(`φ(1) = 1`), then `f(1) − f(z) = |Γ|·⟨f, φ⟩` for any `z ≠ 1`.  This is the substance of
`Res_Z ψ = a·ρ_Z + b·1_Z` with `a = ⟨Res_Z ψ, φ⟩`, `ψ(1) − ψ(z) = a·|Z|`, computed directly from
the inner product via `∑_g φ(g) = 0` (`sum_apply_eq_zero_of_ne_trivial`) and the `Γ^#`-constancy. -/
theorem apply_one_sub_apply_eq_card_mul_inner {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {φ : IrreducibleCharacter Γ}
    (hφ1 : (φ : ClassFunction Γ ℂ) 1 = 1) (hφ : φ ≠ trivialIrreducibleCharacter Γ)
    (f : ClassFunction Γ ℂ) {z : Γ} (hconst : ∀ a : Γ, a ≠ 1 → f a = f z) :
    f 1 - f z = (Nat.card Γ : ℂ) * ClassFunction.inner f (φ : ClassFunction Γ ℂ) := by
  classical
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum, ← mul_assoc,
    mul_invOf_self, one_mul,
    ← Finset.add_sum_erase Finset.univ (fun g => f g * star ((φ : ClassFunction Γ ℂ) g))
      (Finset.mem_univ (1 : Γ)),
    hφ1, star_one, mul_one]
  have hstar : ∑ g ∈ Finset.univ.erase (1 : Γ), star ((φ : ClassFunction Γ ℂ) g) = -1 := by
    have h0 : ∑ g : Γ, star ((φ : ClassFunction Γ ℂ) g) = 0 := by
      rw [← star_sum, sum_apply_eq_zero_of_ne_trivial hφ, star_zero]
    rw [← Finset.add_sum_erase Finset.univ (fun g => star ((φ : ClassFunction Γ ℂ) g))
        (Finset.mem_univ (1 : Γ)), hφ1, star_one] at h0
    linear_combination h0
  have hsum : ∑ g ∈ Finset.univ.erase (1 : Γ), (f g * star ((φ : ClassFunction Γ ℂ) g)) = -f z := by
    rw [Finset.sum_congr rfl (fun g hg => by rw [hconst g (Finset.ne_of_mem_erase hg)]),
      ← Finset.mul_sum, hstar, mul_neg, mul_one]
  rw [hsum]; ring

end OddOrder.RepresentationTheory

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.1) input — the `Y = S(H')` family is closed under the cyclotomic Galois action.**
For any `σ : ℂ ≃+* ℂ`, the `σ`-image of an `η ∈ Y` is again in `Y`.  Indeed every `η ∈ Y` is
`Ind_H^L (linear χ)` with `χ ≠ 1` (`exists_linear_source_of_mem_Yset`); `σ` commutes with induction
(`mapRingEquiv_induce`) and twists the linear source to `(Units.map σ) ∘ χ`
(`mapRingEquiv_linearIrreducibleCharacter`), which is still a nontrivial linear character
(`σ` injective), so the image is `Ind_H^L (linear ((Units.map σ) ∘ χ)) ∈ Y`.

This is the `hSu` hypothesis of `S07.IsCoherent.extension_constant_on_sharp_of_prime`, used to
establish Peterfalvi (6.8.2.1) (`η^{τ₁}` constant on `Z^#`) for the Sibley `Y`-coherence. -/
theorem SibleyDadeHypothesis.Yset_mapRingEquiv_mem (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (σ : ℂ ≃+* ℂ) {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Yset) :
    ClassFunction.mapRingEquiv σ φ ∈ hyp.Yset := by
  obtain ⟨χ, hχ_ne, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hφ
  rw [ClassFunction.mapRingEquiv_induce, ClassFunction.mapRingEquiv_linearIrreducibleCharacter]
  refine hyp.induce_linearIrreducibleCharacter_mem_Yset ?_
  intro hχ'
  refine hχ_ne ?_
  have hinj : Function.Injective (Units.map (σ.toRingHom.toMonoidHom : ℂ →* ℂ)) :=
    Units.map_injective (f := (σ.toRingHom.toMonoidHom : ℂ →* ℂ)) σ.injective
  ext h
  have key : Units.map (σ.toRingHom.toMonoidHom : ℂ →* ℂ) (χ h) = 1 := by
    have h0 := DFunLike.congr_fun hχ' h
    simpa [MonoidHom.comp_apply] using h0
  have hh : χ h = 1 := hinj (key.trans (map_one _).symm)
  simpa using hh

/-- **(6.8.2.1) input — `hZA`.**  Every nontrivial element of `⁅H, H⁆` maps into
`H^# = sharpImage H`.
Since `⁅H, H⁆ ≤ H`, a nontrivial `z ∈ ⁅H, H⁆` lands in `H` with `(z : G) ≠ 1`. -/
theorem SibleyDadeHypothesis.coe_mem_sharpImage_of_mem_commutator
    (_hyp : SibleyDadeHypothesis G L H) {z : ↥L} (hz : z ∈ ⁅H, H⁆) (hz1 : z ≠ 1) :
    (L.subtype z) ∈ sharpImage H := by
  have hzH : z ∈ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro p hp q hq
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem hp hq) (H.inv_mem hp)) (H.inv_mem hq)
    exact hle hz
  refine ⟨Subgroup.mem_map_of_mem L.subtype hzH, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hc
  exact hz1 (by simpa using hc)

/-- **(6.8.2.1) input — `hηx`.**  A `Y = S(H')` character is constant on `⁅H, H⁆`: `η z = η 1`
for `z ∈ ⁅H, H⁆`.  Indeed `η = Ind_H^L (linear χ)`, and for `z ∈ ⁅H, H⁆ ⊆ H` (with `H ◁ L`) every
conjugate `g⁻¹zg` lies in `⁅H, H⁆` (normal in `L`), on which the linear source `χ` is trivial
(`ℂˣ` abelian ⟹ `⁅H,H⁆ ≤ ker χ`); so every `induceTerm` is `1` and `η z = |L:H| = |W₁| = η 1`. -/
theorem SibleyDadeHypothesis.Yset_apply_eq_apply_one_of_mem_commutator
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ ⁅H, H⁆) : η z = η 1 := by
  obtain ⟨χ, _hχ_ne, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hη
  rw [hyp.induce_apply_one_eq_card_W1_of_degree_one _ (linearIrreducibleCharacter_apply_one χ),
    ClassFunction.induce_apply]
  -- ⅟|H| * ∑ g, induceTerm H (linear χ) g z = |W₁|
  have hcomm_normal : (⁅H, H⁆ : Subgroup ↥L).Normal :=
    Subgroup.commutator_normal H H
  have hterm : ∀ g : ↥L,
      ClassFunction.induceTerm H (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ) g z = 1 := by
    intro g
    have hgcomm : g⁻¹ * z * g ∈ ⁅H, H⁆ := by
      have := hcomm_normal.conj_mem z hz g⁻¹
      simpa [mul_assoc] using this
    have hgH : g⁻¹ * z * g ∈ H := by
      have hle : ⁅H, H⁆ ≤ H := by
        rw [Subgroup.commutator_le]
        intro p hp q hq
        rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem hp hq) (H.inv_mem hp)) (H.inv_mem hq)
      exact hle hgcomm
    rw [ClassFunction.induceTerm_of_mem _ hgH, linearIrreducibleCharacter_apply]
    -- `χ ⟨g⁻¹zg, hgH⟩ = 1`: the element lies in the commutator of `↥H`, killed by the abelian `χ`.
    have hmap : (commutator ↥H).map H.subtype = ⁅H, H⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hmem : (⟨g⁻¹ * z * g, hgH⟩ : ↥H) ∈ commutator ↥H := by
      have hin : (g⁻¹ * z * g : ↥L) ∈ (commutator ↥H).map H.subtype := by
        rw [hmap]; exact hgcomm
      obtain ⟨w, hw, hweq⟩ := Subgroup.mem_map.mp hin
      have hweq' : w = (⟨g⁻¹ * z * g, hgH⟩ : ↥H) := Subtype.ext hweq
      rwa [hweq'] at hw
    have hker : χ (⟨g⁻¹ * z * g, hgH⟩ : ↥H) = 1 := by
      have hbot : commutator ℂˣ = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        exact Subgroup.mem_centralizer_iff.mpr (fun y _ => mul_comm y x)
      have hle : (commutator ↥H).map χ ≤ commutator ℂˣ := by
        rw [commutator_def, Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      rw [hbot] at hle
      exact Subgroup.mem_bot.mp (hle (Subgroup.mem_map_of_mem χ hmem))
    rw [hker, Units.val_one]
  rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, ← Nat.card_eq_fintype_card]
  have hLcard : (Nat.card ↥L : ℂ) = (Nat.card ↥hyp.W1 : ℂ) * (Nat.card ↥H : ℂ) := by
    rw [← hyp.index_H_eq_card_W1, ← Nat.cast_mul, Subgroup.index_mul_card]
  rw [hLcard, mul_comm (Nat.card ↥hyp.W1 : ℂ) (Nat.card ↥H : ℂ), ← mul_assoc,
    invOf_mul_self, one_mul]

/-- **Peterfalvi (6.8.2.1), case (B):** the `Y = S(H')`-coherence extension is constant on `W₂^#`.
For `η ∈ Y` and `x, y ∈ W₂^#` (with `W₂` of prime order and `W₂ ⊆ ⁅H, H⁆`),
`η^{τ₁}(y) = η^{τ₁}(x)`.

Assembled from the general `S07.IsCoherent.extension_constant_on_sharp_of_prime`: `W₂` prime is
`hZp`; `hSu` (`Yset_mapRingEquiv_mem`), `hZA` (`coe_mem_sharpImage_of_mem_commutator` via
`W₂ ⊆ ⁅H,H⁆`), `hηx` (`Yset_apply_eq_apply_one_of_mem_commutator`) are the case-(B) discharges;
`hSirr`/`hlat`/`hpair` come from the `Y`-coherence structure (`isIrreducibleCharacter_of_mem_Yset`,
`extension_mem_ZIrr`, `two_le_Yset_ncard`); `hspan` from
`zSpan_S_support_subset_of_apply_one_eq_zero`
(via `Y ⊆ S`). -/
theorem SibleyDadeHypothesis.coherentYset_extension_const_on_W2
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hprime : (Nat.card W2).Prime) (hW2 : W2 ≤ ⁅H, H⁆)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {x y : ↥L} (hx : x ∈ W2) (hx1 : x ≠ 1) (hy : y ∈ W2) (hy1 : y ≠ 1) :
    hyp.coherentYset.extension η (y : G) = hyp.coherentYset.extension η (x : G) := by
  have hspan : ∀ φ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Yset, φ 1 = 0 →
      φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    fun φ hφ h1 =>
      hyp.zSpan_S_support_subset_of_apply_one_eq_zero
        ((Submodule.span_mono hyp.Yset_subset_S) hφ) h1
  exact OddOrder.Peterfalvi.S07.IsCoherent.extension_constant_on_sharp_of_prime
    hyp.coherentYset
    (le_refl _)
    (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ)
    hspan
    (fun σ φ hφ => hyp.Yset_mapRingEquiv_mem σ hφ)
    (fun φ hφ => hyp.coherentYset.extension_mem_ZIrr φ (Submodule.subset_span hφ))
    hη
    (Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega) η)
    hprime
    (fun z hz hz1 => hyp.coe_mem_sharpImage_of_mem_commutator (hW2 hz) hz1)
    hx hx1 (hyp.Yset_apply_eq_apply_one_of_mem_commutator hη (hW2 hx)) hy hy1

/-- **(6.8.2.2) input — the support of `α = Ind_{W₂}^L φ − c·η₁`.**  When `α` vanishes at `1`
(the degree-balancing condition `Ind_{W₂}^L φ (1) = c · η₁(1)`, met by `c = [H:W₂]`), the
difference is supported on `H^# = sharpImage H`: `Ind_{W₂}^L φ` is supported on `H` (since
`W₂ ⊆ H ◁ L`, `support_induce_subset_of_le_normal`), `η₁ ∈ Y` is supported on `H`
(`support_induce_subset_of_normal`), and `α 1 = 0` removes the identity.  This is the
`Supp(α) ⊆ H^#` step of Peterfalvi (6.8.2.2). -/
theorem SibleyDadeHypothesis.support_indW2_sub_smul_subset_sharpImage
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Invertible (Nat.card ↥W2 : ℂ)]
    (φ : ClassFunction ↥W2 ℂ) {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (c : ℂ)
    (h1 : ClassFunction.induce W2 φ (1 : ↥L) = c * η₁ (1 : ↥L)) :
    (ClassFunction.induce W2 φ - c • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  obtain ⟨χ, _hχne, rfl⟩ := hyp.exists_linear_source_of_mem_Yset hη₁
  -- both pieces are supported on `H`
  have hindW2 : (ClassFunction.induce W2 φ).support ⊆ (H : Set ↥L) :=
    ClassFunction.support_induce_subset_of_le_normal hW2H φ
  have hη₁supp : (ClassFunction.induce H (linearIrreducibleCharacter χ : ClassFunction ↥H
      ℂ)).support
      ⊆ (H : Set ↥L) :=
    ClassFunction.support_induce_subset_of_normal H _
  intro x hx
  rw [ClassFunction.mem_support] at hx
  have hxH : x ∈ H := by
    by_contra hxnotH
    have h1' : ClassFunction.induce W2 φ x = 0 := by
      by_contra h; exact hxnotH (hindW2 (ClassFunction.mem_support.mpr h))
    have h2' : (ClassFunction.induce H (linearIrreducibleCharacter χ : ClassFunction ↥H ℂ)) x = 0 :=
        by
      by_contra h; exact hxnotH (hη₁supp (ClassFunction.mem_support.mpr h))
    exact hx (by simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
      h1', h2', mul_zero, sub_zero])
  have hxne : x ≠ 1 := by
    intro hx1
    refine hx ?_
    simp only [hx1, ClassFunction.sub_apply, ClassFunction.smul_apply, h1, sub_self]
  change (x : G) ∈ sharpImage H
  exact ⟨Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩, fun hx1G => hxne (Subtype.ext hx1G)⟩

/-- **(6.8.2.2) reciprocity step.**  For `α = Ind_{W₂}^L φ − c·η₁` with `α(1) = 0` and any
`ψ ∈ CF(G)`,
`⟨α^τ, ψ⟩ = ⟨φ, Res_{W₂} Res_L ψ⟩ − c·⟨η₁, Res_L ψ⟩`.
This is the move `⟨α^τ, ψ⟩ = ⟨α, Res_L ψ⟩ = ⟨φ, Res_Z ψ⟩ − |H:Z|⟨η₁, Res_L ψ⟩` of Peterfalvi
(6.8.2.2): the Dade reciprocity `inner_tau_eq_inner_restrict` (valid since `Supp(α) ⊆ H^#`,
`support_indW2_sub_smul_subset_sharpImage`), additivity (`inner_sub_left`/`inner_smul_left`), and
Frobenius reciprocity `inner_induce_eq_inner_restrict` for `Ind_{W₂}^L`. -/
theorem SibleyDadeHypothesis.inner_tau_indW2_sub_smul_eq
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [Fintype ↥W2] (hW2H : W2 ≤ H) [Invertible (Nat.card ↥W2 : ℂ)]
    (φ : ClassFunction ↥W2 ℂ) {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (c : ℂ)
    (h1 : ClassFunction.induce W2 φ (1 : ↥L) = c * η₁ (1 : ↥L)) (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 φ - c • η₁)) ψ
      = ClassFunction.inner φ (ClassFunction.restrict W2 (ClassFunction.restrict L ψ))
        - c * ClassFunction.inner η₁ (ClassFunction.restrict L ψ) := by
  rw [hyp.inner_tau_eq_inner_restrict
        (hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ c h1) ψ,
    ClassFunction.inner_sub_left, ClassFunction.inner_smul_left,
    ClassFunction.inner_induce_eq_inner_restrict]

/-- **The `Y`-coherence image of an `η ∈ Y` is `±` an irreducible character of `G`.**  Since `η` is
irreducible (`isIrreducibleCharacter_of_mem_Yset`, so `⟨η,η⟩ = 1`) and the coherence extension is
norm-preserving on `Z[Y]` (`extension_inner_eq`) with image in `ZIrr G` (`extension_mem_ZIrr`), the
image `η^{τ₁}` has squared norm `1`, hence equals `ε·ξ` for `ε = ±1` and `ξ ∈ Irr G`
(`exists_zsmul_irreducibleCharacter_of_inner_self_one`, Peterfalvi (5.9.a)).

This is the reduction that lets the (6.7) congruence for the *virtual* character `η^{τ₁}` be read
off the single irreducible `ξ` (which inherits `η^{τ₁}`'s `W₂^#`-constancy up to sign), in
Peterfalvi (6.8.2.2). -/
theorem SibleyDadeHypothesis.coherentYset_extension_eq_zsmul_irreducible
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ∃ (ε : ℤ) (ξ : IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧
        hyp.coherentYset.extension η = ε • (ξ : ClassFunction G ℂ) := by
  have hηirr : IsIrreducibleCharacter η := hyp.isIrreducibleCharacter_of_mem_Yset hη
  have hηnorm : ClassFunction.inner η η = 1 := by
    have h := irreducibleCharacter_inner (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hηirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηspan : η ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Yset := Submodule.subset_span hη
  have hextnorm : ClassFunction.inner (hyp.coherentYset.extension η)
      (hyp.coherentYset.extension η) = 1 := by
    rw [hyp.coherentYset.extension_inner_eq η η hηspan hηspan, hηnorm]
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one
    (hyp.coherentYset.extension_mem_ZIrr η hηspan) hextnorm

/-- **Centralizer of a central element is everything (in `G`, intersected with `L`).**  If
`w ∈ Z(↥L)`, then `L ⊓ C_G((w : G)) = L`: every element of `L` commutes with `(w : G)`.  In the
(6.8)(c2) case-(B), `W₂ ⊆ Z(↥L)` (the math-(B) condition `W₂ ⊆ Z(H)` plus `W = W₁ ⊔ W₂` cyclic, so
`W₂` also commutes with `W₁`), so this gives the centralizer-card constancy on `W₂^#`
(`|N_G(Ĥ) ⊓ C_G(w)| = |L|` for all `w ∈ W₂^#`) — the second half of `peterfalvi_67_of_odd`'s
`hconst`, the analogue of the Frobenius `inf_centralizer_centralCommutator_map`. -/
theorem SibleyDadeHypothesis.inf_centralizer_eq_of_mem_center
    (_hyp : SibleyDadeHypothesis G L H) {w : ↥L} (hwc : w ∈ Subgroup.center ↥L) :
    (L : Subgroup G) ⊓ Subgroup.centralizer ({(w : G)} : Set G) = L := by
  rw [inf_eq_left]
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Subgroup.mem_center_iff] at hwc
  have h := congrArg L.subtype (hwc ⟨g, hg⟩)
  simpa using h

open scoped OddOrder.AlgInt in
/-- **(6.8.2.2) case-(B) (6.7) adapter.**  The case-(B) analogue of
`peterfalvi_67_centralCommutator`: when `Z ≤ H` is a subgroup that is *central in `↥L`*
(`Z ≤ Z(↥L)` — in (6.8.2.2) this is `Z = W₂` under the math-(B) condition `W₂ ⊆ Z(H)` with `W`
cyclic), the (6.7) congruence

`ρ.character z ≡ ρ.character 1  (mod |H|)`

holds for `z ∈ Z^#` and any irreducible `ρ` whose character is constant on
`Z^# = (Z.map L.subtype)^#` (the only character-theoretic input, deferred to the caller — in
(6.8.2.2) it is `η₁^{τ₁}`).

The structural hypotheses of `peterfalvi_67_of_odd` are discharged at `P := Ĥ = H.map L.subtype`
(Sylow in `G` by `sylow_map_subtype_of_coprime`, with `N_G(Ĥ) = L` by `normalizer_map_subtype_eq`)
and `Z := Z.map L.subtype`: `hZP` (`Z ≤ H`), `hZnormal` (central ⇒ normal), `hti`/`hodd`
(`H^#` TI / `|L|` odd), `hPz` (`Ĥ ≤ L ≤ C_G(z)` since `z` is central), and the `|C_L(·)|`-constancy
clause of `hconst` (both sides `= |L|` by `inf_centralizer_eq_of_mem_center`).  The modulus
`|Ĥ| = |H|` via `card_map_of_injective`.  This is the (6.8)(c2) coprimality-only analogue of the
(6.8.1) Frobenius adapter; the Sylow is supplied by the `cases` side condition
`gcd(|H|,|W₁|) = 1`. -/
theorem SibleyDadeHypothesis.peterfalvi_67_central (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcen : Z ≤ Subgroup.center ↥L)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {z : G} (hz : z ∈ Z.map L.subtype) (hz1 : z ≠ 1)
    (hψconst : ∀ w ∈ Z.map L.subtype, w ≠ 1 → ρ.character w = ρ.character z) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card ↥H : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  classical
  obtain ⟨Q, hQeq⟩ := hyp.sylow_map_subtype_of_coprime hcop hp hHp
  have hNorm : Subgroup.normalizer ((Q : Subgroup G) : Set G) = L := by
    rw [hQeq]; exact hyp.normalizer_map_subtype_eq
  have hcard : Nat.card (Q : Subgroup G) = Nat.card ↥H := by
    rw [hQeq]; exact Subgroup.card_map_of_injective L.subtype_injective
  -- `Z` is normal in `↥L`: central subgroups are normal.
  have hZnorm : Z.Normal := ⟨fun n hn g => by
    have hc : g * n = n * g := (Subgroup.mem_center_iff.mp (hZcen hn)) g
    have hgn : g * n * g⁻¹ = n := by rw [hc]; exact mul_inv_cancel_right n g
    rw [hgn]; exact hn⟩
  -- structural hypotheses of `peterfalvi_67_of_odd`
  have hZP : Z.map L.subtype ≤ (Q : Subgroup G) := by
    rw [hQeq]; exact Subgroup.map_mono hZH
  have hZnormal : ((Z.map L.subtype).subgroupOf
      (Subgroup.normalizer ((Q : Subgroup G) : Set G))).Normal := by
    rw [hNorm,
      show (Z.map L.subtype).subgroupOf L = Z from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact hZnorm
  have hti : OddOrder.GroupTheory.IsTISubset (((Q : Subgroup G) : Set G) \ {1})
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [hNorm, show ((Q : Subgroup G) : Set G) \ {1} = sharpImage H by rw [hQeq]; rfl]
    exact hyp.H_sharp_ti
  have hodd : Odd (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
    rw [hNorm]; exact hyp.card_L_odd
  obtain ⟨z₀, hz₀Z, hz₀eq⟩ := Subgroup.mem_map.mp hz
  have hz₀z : (z₀ : G) = z := hz₀eq
  have hPz : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    have hbz : (L : Subgroup G) ⊓ Subgroup.centralizer ({(z₀ : G)} : Set G) = L :=
      hyp.inf_centralizer_eq_of_mem_center (hZcen hz₀Z)
    rw [hz₀z] at hbz
    calc (Q : Subgroup G) ≤ L := by rw [hQeq]; exact Subgroup.map_subtype_le H
      _ ≤ Subgroup.centralizer ({z} : Set G) := inf_eq_left.mp hbz
  have hconst : ∀ ⦃w : G⦄, w ∈ Z.map L.subtype → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G)) := by
    intro w hw hw1
    refine ⟨hψconst w hw hw1, ?_⟩
    obtain ⟨w₀, hw₀Z, hw₀eq⟩ := Subgroup.mem_map.mp hw
    have hw₀w : (w₀ : G) = w := hw₀eq
    rw [hNorm, ← hw₀w, ← hz₀z,
      hyp.inf_centralizer_eq_of_mem_center (hZcen hw₀Z),
      hyp.inf_centralizer_eq_of_mem_center (hZcen hz₀Z)]
  have key := OddOrder.RepresentationTheory.peterfalvi_67_of_odd ρ Q hZP hZnormal hti hodd
    hz hz1 hPz hconst
  rwa [hcard] at key

open scoped OddOrder.AlgInt in
/-- **(6.8.2.2) case-(B) (6.7)-congruence for `η^{τ₁}`** (mmd 04.8 L186 →).  For `η ∈ Y` and
`z ∈ W₂^#`, `Res^G_L(η^{τ₁})(z) ≡ Res^G_L(η^{τ₁})(1) (mod |H|)`.  Wires the case-(B) (6.7) adapter
`peterfalvi_67_central` to `η^{τ₁}`: write `η^{τ₁} = ε•ξ` (`ε = ±1`, `ξ` irreducible from norm `1`,
`coherentYset_extension_eq_zsmul_irreducible`); unpack `ξ = ρ.character` (`ρ` irreducible,
`ξ.isIrreducible`).  The const-on-`W₂^#` of `η^{τ₁}` (`coherentYset_extension_const_on_W2`,
(6.8.2.1)) transfers to `ρ.character` (cancel `ε`), feeding the adapter to get
`ξ(z) ≡ ξ(1) (mod |H|)`; scale by `ε` (`Cong.smul_left`) for `η^{τ₁}(z) ≡ η^{τ₁}(1)`.

`W₂` is prime, `W₂ ⊆ ⁅H,H⁆` (the `cases` (c2) side conditions) and central in `↥L`
(`W₂ ⊆ Z(↥L)`, the math-(B) `W₂ ⊆ Z(H)` with `W` cyclic — deferred to the caller). -/
theorem SibleyDadeHypothesis.restrict_extension_Yset_charValue_cong_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ W2) (hz1 : z ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      ≡ (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
        [ALGMOD (Nat.card ↥H : ℤ)] := by
  classical
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  obtain ⟨ε, ξ, hε, hηtε⟩ := hyp.coherentYset_extension_eq_zsmul_irreducible hη
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεint : IsIntegral ℤ (ε : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ε))
  have hsmul : ∀ g : G,
      (hyp.coherentYset.extension η) g = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [hηtε, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  have : ρ.IsIrreducible := hρ
  have hzGmem : (L.subtype z) ∈ W2.map L.subtype :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hzG1 : (L.subtype z) ≠ 1 := fun h => hz1 (L.subtype_injective (by simpa using h))
  have hψconst : ∀ w ∈ W2.map L.subtype, w ≠ 1 →
      ρ.character w = ρ.character (L.subtype z) := by
    intro w hw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; simp)
    have hRw : (hyp.coherentYset.extension η) (L.subtype w₀)
        = (hyp.coherentYset.extension η) (L.subtype z) :=
      hyp.coherentYset_extension_const_on_W2 hprime hW2comm hη hz hz1 hw₀ hw₀1
    rw [← congrFun hξρ (L.subtype w₀), ← congrFun hξρ (L.subtype z)]
    apply mul_left_cancel₀ hεne
    rw [← hsmul (L.subtype w₀), ← hsmul (L.subtype z)]
    exact hRw
  have hcong := hyp.peterfalvi_67_central hcop hp hHp hW2H hW2cen ρ hzGmem hzG1 hψconst
  rw [← congrFun hξρ (L.subtype z), ← congrFun hξρ 1] at hcong
  have hcong2 := hcong.smul_left hεint
  simp only [← hsmul] at hcong2
  exact hcong2

open scoped OddOrder.AlgInt in
/-- **(6.8.2.2) integration core: `|H| ∣ |W₂|·a`.**  For `ψ = η^{τ₁}` (`η ∈ Y`) and a nontrivial
*linear* `φ ∈ Irr W₂`, the regular-character coefficient `a = ⟨Res^L_{W₂} Res^G_L ψ, φ⟩` (an integer
`m`) satisfies `|H| ∣ |W₂|·m`.

This is the number-theoretic heart of Peterfalvi (6.8.2.2) ("`a ≡ 0 (mod |H:Z|)`"): pick `z₀ ∈ W₂^#`
(exists since `|W₂|` is prime); `ψ` (hence `Res_{W₂} Res_L ψ =: f`) is constant on `W₂^#`
(`coherentYset_extension_const_on_W2`), so the regular-character relation
`apply_one_sub_apply_eq_card_mul_inner` gives `f(1) − f(z₀) = |W₂|·m`; the (6.7) congruence
`restrict_extension_Yset_charValue_cong_caseB` gives `f(z₀) ≡ f(1) (mod |H|)`, i.e.
`f(1) − f(z₀) ≡ 0`; since that difference equals the rational integer `|W₂|·m`, the reverse bridge
`dvd_of_intCast_algMod` yields `|H| ∣ |W₂|·m`.  The caller cancels `|W₂|` (using
`|H| = |H:W₂|·|W₂|`)
for `|H:W₂| ∣ m`. -/
theorem SibleyDadeHypothesis.card_H_dvd_card_W2_mul_regCharCoeff
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2) {m : ℤ}
    (hm : ClassFunction.inner
            (ClassFunction.restrict W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)))
            (φ : ClassFunction ↥W2 ℂ) = (m : ℂ)) :
    (Nat.card ↥H : ℤ) ∣ (Nat.card ↥W2 : ℤ) * m := by
  classical
  set f : ClassFunction ↥W2 ℂ :=
    ClassFunction.restrict W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)) with hfdef
  -- a witness `z₀ ∈ W₂^#` (`|W₂|` prime ⇒ nontrivial).
  have : Nontrivial ↥W2 := Finite.one_lt_card_iff_nontrivial.mp hprime.one_lt
  obtain ⟨z₀, hz₀1⟩ := exists_ne (1 : ↥W2)
  -- `f` is constant on `W₂^#`.
  have hfconst : ∀ a : ↥W2, a ≠ 1 → f a = f z₀ := by
    intro a ha
    have hmemA : (W2.subtype a) ∈ W2 := SetLike.coe_mem a
    have hmemZ : (W2.subtype z₀) ∈ W2 := SetLike.coe_mem z₀
    have hA1 : (W2.subtype a) ≠ 1 := fun h => ha (W2.subtype_injective (by simpa using h))
    have hZ1 : (W2.subtype z₀) ≠ 1 := fun h => hz₀1 (W2.subtype_injective (by simpa using h))
    have hc := hyp.coherentYset_extension_const_on_W2 hprime hW2comm hη hmemZ hZ1 hmemA hA1
    simp only [hfdef, ClassFunction.restrict_apply]
    exact hc
  -- regular-character relation `f(1) − f(z₀) = |W₂|·m`.
  have hreg := apply_one_sub_apply_eq_card_mul_inner hφ1 hφ f (z := z₀) hfconst
  rw [hm] at hreg
  -- the value identities relating `f` to `Res_L ψ`.
  have hfz : f z₀ = (ClassFunction.restrict L (hyp.coherentYset.extension η)) (W2.subtype z₀) :=
    ClassFunction.restrict_apply W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)) z₀
  have hf1 : f 1 = (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1 :=
    ClassFunction.restrict_apply W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
  have hZ1 : (W2.subtype z₀) ≠ 1 := fun h => hz₀1 (W2.subtype_injective (by simpa using h))
  -- (6.7) congruence `f(z₀) ≡ f(1) (mod |H|)`.
  have hcong := hyp.restrict_extension_Yset_charValue_cong_caseB hcop hp hHp hprime hW2comm hW2cen
      hη
    (z := W2.subtype z₀) (SetLike.coe_mem z₀) hZ1
  rw [← hfz, ← hf1] at hcong
  -- `f(1) − f(z₀) ≡ 0 (mod |H|)`.
  have hsub : f 1 - f z₀ ≡ 0 [ALGMOD (Nat.card ↥H : ℤ)] := by
    have h := OddOrder.AlgInt.Cong.sub hcong.symm (OddOrder.AlgInt.Cong.refl (Nat.card ↥H : ℤ) (f
        z₀))
    simpa using h
  rw [hreg] at hsub
  -- convert to the integer congruence and apply the reverse bridge.
  have hcong_int : ((Nat.card ↥W2 * m : ℤ) : ℂ) ≡ ((0 : ℤ) : ℂ) [ALGMOD (Nat.card ↥H : ℤ)] := by
    have heq : ((Nat.card ↥W2 * m : ℤ) : ℂ) = (Nat.card ↥W2 : ℂ) * (m : ℂ) := by push_cast; ring
    rw [heq]; simpa using hsub
  have hHne : ((Nat.card ↥H : ℤ) : ℂ) ≠ 0 := by
    have h1 : (Nat.card ↥H : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    exact_mod_cast h1
  have hdvd := dvd_of_intCast_algMod hHne hcong_int
  rwa [sub_zero] at hdvd

/-- **(6.8.2.2) `|H:W₂| ∣ a`** (Peterfalvi (6.8.2.2): "`a ≡ 0 (mod |H:Z|)`").  Cancelling `|W₂|`
from the integration core `card_H_dvd_card_W2_mul_regCharCoeff` (`|H| ∣ |W₂|·m`) via the index
factorization `|H| = |H:W₂|·|W₂|` (`index_mul_card` on `W₂.subgroupOf H`, `subgroupOfEquivOfLe`):
the regular-character coefficient `m = ⟨Res_{W₂} Res_L η^{τ₁}, φ⟩` is divisible by the relative
index
`[H:W₂] = (W₂.subgroupOf H).index`.  This is the textbook's `a ≡ 0 (mod |H:Z|)`. -/
theorem SibleyDadeHypothesis.index_W2_dvd_regCharCoeff
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [Fintype ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2) {m : ℤ}
    (hm : ClassFunction.inner
            (ClassFunction.restrict W2 (ClassFunction.restrict L (hyp.coherentYset.extension η)))
            (φ : ClassFunction ↥W2 ℂ) = (m : ℂ)) :
    ((W2.subgroupOf H).index : ℤ) ∣ m := by
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have hdvd :=
    hyp.card_H_dvd_card_W2_mul_regCharCoeff hcop hp hHp hprime hW2comm hW2cen hη φ hφ1 hφ hm
  -- `|H| = |W₂| · |H:W₂|`
  have hcardeq : (Nat.card ↥H : ℤ) = (Nat.card ↥W2 : ℤ) * ((W2.subgroupOf H).index : ℤ) := by
    have h1 := Subgroup.index_mul_card (W2.subgroupOf H)
    have h2 : Nat.card ↥(W2.subgroupOf H) = Nat.card ↥W2 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2H).toEquiv
    rw [h2] at h1
    rw [← h1]; push_cast; ring
  rw [hcardeq] at hdvd
  have hW2ne : (Nat.card ↥W2 : ℤ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  exact (mul_dvd_mul_iff_left hW2ne).mp hdvd

open scoped OddOrder.AlgInt in
/-- **(6.8.2.2): `⟨α^τ, ψ⟩` is an integer `≡ 0 (mod |H:W₂|)`** for `ψ = η'^{τ₁} ∈ 𝒴^{τ₁}`.
With `α = Ind^L_{W₂}φ − |H:W₂|·η₁` (`φ` nontrivial linear, `η₁ ∈ Y` the anchor), the Dade
reciprocity
`inner_tau_indW2_sub_smul_eq` gives `⟨α^τ, ψ⟩ = ⟨φ, Res^L_{W₂} Res^G_L ψ⟩ − |H:W₂|·⟨η₁, Res^G_L ψ⟩`.

The degree relation `c = |H:W₂|` is computed:
`Ind_{W₂}φ(1) = [L:W₂]·φ(1) = [H:W₂]·|W₁| = |H:W₂|·η₁(1)`
(`induce_apply_one` + `relIndex_mul_index` + `index_H_eq_card_W1` + `Yset_apply_one`). The first
inner
product equals the integer `a = m` (`⟨φ, Res⟩ = star⟨Res, φ⟩ = m`, `inner_conj_symm`, `m` from
`mem_ZIrr_inner_int`), divisible by `[H:W₂]` (`index_W2_dvd_regCharCoeff`); the second is an integer
`b'` (`mem_ZIrr_inner_int` + flip).  Hence `⟨α^τ, ψ⟩ = m − [H:W₂]·b'`, an integer divisible by
`[H:W₂]`. -/
theorem SibleyDadeHypothesis.inner_tau_alpha_dvd_index
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    {η' : ClassFunction ↥L ℂ} (hη' : η' ∈ hyp.Yset) :
    ∃ n : ℤ,
      ClassFunction.inner
          (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁))
          (hyp.coherentYset.extension η') = (n : ℂ)
        ∧ ((W2.subgroupOf H).index : ℤ) ∣ n := by
  classical
  have : Fintype ↥W2 := Fintype.ofFinite _
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  set ψ := hyp.coherentYset.extension η' with hψ
  -- degree relation `Ind_{W₂}φ(1) = |H:W₂|·η₁(1)`.
  have h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  have hrecip := hyp.inner_tau_indW2_sub_smul_eq hW2H (φ : ClassFunction ↥W2 ℂ) hη₁
    ((W2.subgroupOf H).index : ℂ) h1 ψ
  -- ZIrr chain and the integer `m`.
  have hψZ : ψ ∈ ZIrr G := hyp.coherentYset.extension_mem_ZIrr η' (Submodule.subset_span hη')
  have hResLZ : ClassFunction.restrict L ψ ∈ ZIrr ↥L := ClassFunction.restrict_mem_ZIrr L hψZ
  have hResWZ : ClassFunction.restrict W2 (ClassFunction.restrict L ψ) ∈ ZIrr ↥W2 :=
    ClassFunction.restrict_mem_ZIrr W2 hResLZ
  obtain ⟨m, hm⟩ := mem_ZIrr_inner_int φ hResWZ
  have hφRes : ClassFunction.inner (φ : ClassFunction ↥W2 ℂ)
      (ClassFunction.restrict W2 (ClassFunction.restrict L ψ)) = (m : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hm]; simp
  have hdvdm := hyp.index_W2_dvd_regCharCoeff hcop hp hHp hprime hW2comm hW2cen hη' φ hφ1 hφ hm
  -- the integer `b' = ⟨η₁, Res_L ψ⟩`.
  have hη₁irr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  obtain ⟨b', hb'⟩ := mem_ZIrr_inner_int (⟨η₁, hη₁irr⟩ : IrreducibleCharacter ↥L) hResLZ
  rw [show ((⟨η₁, hη₁irr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = η₁ from rfl] at hb'
  have hη₁Res : ClassFunction.inner η₁ (ClassFunction.restrict L ψ) = (b' : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hb']; simp
  refine ⟨m - (W2.subgroupOf H).index * b', ?_, ?_⟩
  · rw [hrecip, hφRes, hη₁Res]; push_cast; ring
  · exact dvd_sub hdvdm (dvd_mul_right ((W2.subgroupOf H).index : ℤ) b')

end OddOrder.Peterfalvi.S08


