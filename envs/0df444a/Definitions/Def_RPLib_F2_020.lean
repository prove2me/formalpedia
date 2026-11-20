-- Prove2me | Definitions.Def_RPLib_F2_020
-- name    : RPLib_F2_020
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T10:13:59.40341+00:00
-- url     : https://prove2.me/theorems/678ee502-9297-404c-8a0c-7ee4c132043d
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 020 of 70
-- statement:
--   File 020 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Tsen_Zero`: S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property
--   * `S4.Def_RP_CdOne_Coh`: S4-PD (3a), part 1: elementary degree-2 group cohomology
--   * `S4.Def_RP_CdOne_Lc`: S4-PD (3), group layer part 1: locally constant cochains and the index lemma
--   * `S4.Def_RP_PerfectCx_Z1Ex`: S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`
--   * `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
--   * `S4.Def_RP_ThetaCube_GrB`: S4-ThetaCube, file GrB (D-C1, part 8): the Gram matrix on `J^3`
--   * `S4.Def_RP_DegPoly_Cube`: Degree polynomiality, part 3: the quadratic relation from the cube relation (unit S4-DegPoly)
--   * `S4.Def_RP_ThetaCube_Hook`: S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`
--   * `S4.Def_RP_ThetaCube_GrC`: S4-ThetaCube, file GrC (D-C1, part 9): the cube divisor is principal up to `2`
--   * `S4.Def_RP_ThetaCube_Surj3`: S4-ThetaCube, file Surj3 (D-C1, part 10): `Φ3 : X1^n ⟶ J^3` is surjective and dominant
--   * `S4.Def_RP_JacFrob_BrSig`: S4-JacFrob, part BrSig (bridge 6): the bridge intertwines the two Frobenius actions
--   * `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
--   * `S4.Def_RP_JacFrob_TanP`: S4-JacFrob, part TanP: `q`-th roots in `Sym^g` (generic)
--   * `S4.Def_RP_JacFrob_TanG`: S4-JacFrob, part TanG: the differential of `mor φ` (generic)
--   * `S4.Def_RP_JacFrob_Tan`: S4-JacFrob, part Tan: **`dπ_J = 1`**
--   * `S4.Def_RP_JacAlg_Norm`: Core B algebra, part 2: `P_π` is monic of degree `2g` and `deg F = ∏ F(a)` (Milne 10.22, L5/L6)
--   * `S4.Def_RP_JacAlg_Multiset`: Core B algebra, part 3: the multiset lemma with RH (A6, L7)
--   * `S4.Def_RP_JacAlg_Zeta`: Core B algebra, part 4: the zeta link (A5) and the roots of `P_π` (A6 applied)
--   * `S4.Def_RP_JacAlg_Div`: Core B algebra, part 5: divisibility (unit S4-JacAlg, lemma L2 = route A1)
--   * `S4.Def_RP_CoreB_Zeta`: Core B, O4: the zeta link
--   * `S4.Def_RP_CoreB_Div`: Core B, O5 (CB1): `Pic(X̄)[l^∞]` is `l`-divisible
--   * `S4.Def_RP_CdOne_KumVal`: S4-PD (3)(iii)(K), part V: primes and valuations along finite levels `M ≤ L` of `K̄ / K`
--   * `S4.Def_RP_CdOne_KumOrb`: S4-PD (3)(iii)(K), part O: Galois orbits of primes and valuations mod `n`
--   * `S4.Def_RP_CdOne_KumGrp`: S4-PD (3)(iii)(K), part G: the decomposition group of a finite level
--   * `S4.Def_RP_CdOne_KumDesc`: S4-PD (3)(iii)(K), part D: valuations of a Kummer element are constant mod `n` on `Hgrp`-orbits
--   * `S4.Def_RP_CdOne_KumLev`: S4-PD (3)(iii)(K), part L: level lemmas for the Kummer-closure descent
--   * `S4.Def_RP_Tsen_RatFunc`: S4-PD (1), T2: Tsen's theorem for `k(t)`
--   * `S4.Def_RP_Tsen_Norm`: S4-PD (1), T3: finite extensions of `C₁` fields are `C₁` (the norm form)
--   * `S4.Def_RP_Tsen`: S4-PD (1): Tsen's theorem
--   * `S4.Def_RP_CdOne_Br`: S4-PD (3a), part 2: `Br(L/K) = 0` for a Galois `p`-extension of a C1 field
--   * `S4.Def_RP_CdOne_Emb`: S4-PD (3b): the central embedding problem with kernel `μ_l`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_019

/-!
# Ramanujan-Petersson curve library (flat edition), file 020 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Tsen_Zero`: S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property
* `S4.Def_RP_CdOne_Coh`: S4-PD (3a), part 1: elementary degree-2 group cohomology
* `S4.Def_RP_CdOne_Lc`: S4-PD (3), group layer part 1: locally constant cochains and the index lemma
* `S4.Def_RP_PerfectCx_Z1Ex`: S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`
* `S4.Def_RP_ThetaCube_GrA`: S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
* `S4.Def_RP_ThetaCube_GrB`: S4-ThetaCube, file GrB (D-C1, part 8): the Gram matrix on `J^3`
* `S4.Def_RP_DegPoly_Cube`: Degree polynomiality, part 3: the quadratic relation from the cube relation (unit S4-DegPoly)
* `S4.Def_RP_ThetaCube_Hook`: S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`
* `S4.Def_RP_ThetaCube_GrC`: S4-ThetaCube, file GrC (D-C1, part 9): the cube divisor is principal up to `2`
* `S4.Def_RP_ThetaCube_Surj3`: S4-ThetaCube, file Surj3 (D-C1, part 10): `Φ3 : X1^n ⟶ J^3` is surjective and dominant
* `S4.Def_RP_JacFrob_BrSig`: S4-JacFrob, part BrSig (bridge 6): the bridge intertwines the two Frobenius actions
* `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
* `S4.Def_RP_JacFrob_TanP`: S4-JacFrob, part TanP: `q`-th roots in `Sym^g` (generic)
* `S4.Def_RP_JacFrob_TanG`: S4-JacFrob, part TanG: the differential of `mor φ` (generic)
* `S4.Def_RP_JacFrob_Tan`: S4-JacFrob, part Tan: **`dπ_J = 1`**
* `S4.Def_RP_JacAlg_Norm`: Core B algebra, part 2: `P_π` is monic of degree `2g` and `deg F = ∏ F(a)` (Milne 10.22, L5/L6)
* `S4.Def_RP_JacAlg_Multiset`: Core B algebra, part 3: the multiset lemma with RH (A6, L7)
* `S4.Def_RP_JacAlg_Zeta`: Core B algebra, part 4: the zeta link (A5) and the roots of `P_π` (A6 applied)
* `S4.Def_RP_JacAlg_Div`: Core B algebra, part 5: divisibility (unit S4-JacAlg, lemma L2 = route A1)
* `S4.Def_RP_CoreB_Zeta`: Core B, O4: the zeta link
* `S4.Def_RP_CoreB_Div`: Core B, O5 (CB1): `Pic(X̄)[l^∞]` is `l`-divisible
* `S4.Def_RP_CdOne_KumVal`: S4-PD (3)(iii)(K), part V: primes and valuations along finite levels `M ≤ L` of `K̄ / K`
* `S4.Def_RP_CdOne_KumOrb`: S4-PD (3)(iii)(K), part O: Galois orbits of primes and valuations mod `n`
* `S4.Def_RP_CdOne_KumGrp`: S4-PD (3)(iii)(K), part G: the decomposition group of a finite level
* `S4.Def_RP_CdOne_KumDesc`: S4-PD (3)(iii)(K), part D: valuations of a Kummer element are constant mod `n` on `Hgrp`-orbits
* `S4.Def_RP_CdOne_KumLev`: S4-PD (3)(iii)(K), part L: level lemmas for the Kummer-closure descent
* `S4.Def_RP_Tsen_RatFunc`: S4-PD (1), T2: Tsen's theorem for `k(t)`
* `S4.Def_RP_Tsen_Norm`: S4-PD (1), T3: finite extensions of `C₁` fields are `C₁` (the norm form)
* `S4.Def_RP_Tsen`: S4-PD (1): Tsen's theorem
* `S4.Def_RP_CdOne_Br`: S4-PD (3a), part 2: `Br(L/K) = 0` for a Galois `p`-extension of a C1 field
* `S4.Def_RP_CdOne_Emb`: S4-PD (3b): the central embedding problem with kernel `μ_l`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Tsen_Zero =====
section

set_option autoImplicit false

/-!
# S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property

* `exists_common_zero`: over an algebraically closed field `k`, `m` polynomials in `n > m` variables without constant
  term have a common nonzero zero (Krull's height theorem + the Nullstellensatz).
* `IsC1 K`: every polynomial in `n` variables over `K` with total degree `< n` and constant term `0` has a nonzero zero.
  (`IsC1.exists_zero_of_isHomogeneous`: the classical `C₁` property for forms.)
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

section Zero

variable {k : Type*} [Field k]

theorem finiteRingKrullDim_mvPolynomial_fin (n : ℕ) :
    FiniteRingKrullDim (MvPolynomial (Fin n) k) := by
  rw [FiniteRingKrullDim, Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top]
  have h := ringKrullDim_mvPolynomial_fin (k := k) n
  rw [ringKrullDim] at h
  rw [h]
  exact ⟨WithBot.natCast_ne_bot n, by
    intro h'
    have : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by simpa using h'
    exact ENat.natCast_ne_top n (WithBot.coe_injective this)⟩

/-- Evaluation after the translation `X j ↦ X j - a j`. -/
theorem eval_translate {n : ℕ} (a x : Fin n → k) (p : MvPolynomial (Fin n) k) :
    eval x (aeval (fun j => X j - C (a j)) p) = eval (fun j => x j - a j) p := by
  have h := congrArg (fun φ : MvPolynomial (Fin n) k →ₐ[k] k => φ p)
    (MvPolynomial.comp_aeval (fun j => (X j - C (a j) : MvPolynomial (Fin n) k)) (aeval x))
  simp only [AlgHom.comp_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply] at h
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  exact h

/-- **Common zeros.** Over an algebraically closed field, `m` polynomials without constant term in `n > m` variables
have a common nonzero zero. -/
theorem exists_common_zero [IsAlgClosed k] {n m : ℕ} (hmn : m < n) (f : Fin m → MvPolynomial (Fin n) k)
    (hf : ∀ i, constantCoeff (f i) = 0) : ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, eval x (f i) = 0 := by
  classical
  by_contra hne
  push Not at hne
  have := finiteRingKrullDim_mvPolynomial_fin (k := k) n
  obtain ⟨M, hM, hMh⟩ := Ideal.exists_isMaximal_height (R := MvPolynomial (Fin n) k)
  obtain ⟨a, rfl⟩ := eq_vanishingIdeal_singleton_of_isMaximal k hM
  set τ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k := aeval (fun j => X j - C (a j))
  set s : Finset (MvPolynomial (Fin n) k) := Finset.univ.image (fun i => τ (f i))
  -- the zero locus of `span s` is `{a}`
  have hZ : zeroLocus k (Ideal.span (s : Set (MvPolynomial (Fin n) k))) = {a} := by
    ext x
    rw [zeroLocus_span, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hxa
      have hsub : (fun j => x j - a j) ≠ 0 := by
        intro h0
        apply hxa
        funext j
        have := congrFun h0 j
        simpa [sub_eq_zero] using this
      obtain ⟨i, hi⟩ := hne _ hsub
      apply hi
      have := hx (τ (f i)) (by simp [s])
      rw [aeval_eq_eval, eval_translate] at this
      exact this
    · rintro rfl p hp
      simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hp
      obtain ⟨i, rfl⟩ := hp
      rw [aeval_eq_eval, eval_translate]
      have : (fun j => x j - x j) = (0 : Fin n → k) := by funext j; simp
      rw [this, eval_zero]
      exact hf i
  have hrad : (Ideal.span (s : Set (MvPolynomial (Fin n) k))).radical = vanishingIdeal k {a} := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k), hZ]
  have hmin : vanishingIdeal k {a} ∈ (Ideal.span (s : Set (MvPolynomial (Fin n) k))).minimalPrimes := by
    refine ⟨⟨hM.isPrime, hrad ▸ Ideal.le_radical⟩, ?_⟩
    rintro q ⟨hq, hsq⟩ _
    rw [← hrad]
    exact (Ideal.IsPrime.radical_le_iff hq).2 hsq
  have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h2 : s.card ≤ m := by
    simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := fun i => τ (f i)))
  rw [ringKrullDim_mvPolynomial_fin] at hMh
  have h3 : (vanishingIdeal k {a}).height = (n : ℕ∞) := by exact_mod_cast hMh
  rw [h3] at h1
  have h4 : n ≤ s.card := by exact_mod_cast h1
  omega

end Zero

end RamanujanPetersson.Tsen


end

-- ===== S4.Def_RP_CdOne_Coh =====
section

/-!
# S4-PD (3a), part 1: elementary degree-2 group cohomology

Explicit, additive computations behind `Br(L/K) = 0` over a C1 field (no `FiniteCyclic`, any universes):
* `d₁ b`, the coboundary of a 1-cochain; `isCoboundary₂_of_sub` transfers coboundary-ness along `f - d₁ b`.
* `isCoboundary₂_of_cyclic`: if `σ` generates the finite group `G` and every `σ`-fixed element of `A` is a norm
  `∑_{t < ord σ} σ ^ t • c`, every 2-cocycle is a coboundary.
* `exists_inflated` (degree-2 inflation-restriction): for `N ◁ G` with `H¹(N, A) = 0` and `f|N×N` a coboundary,
  `f - d₁ b` is invariant under right multiplication by `N` in both variables and takes `N`-fixed values.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The coboundary of a 1-cochain. -/
def d₁ (b : G → A) : G × G → A := fun p => p.1 • b p.2 - b (p.1 * p.2) + b p.1

@[simp] theorem d₁_apply (b : G → A) (g h : G) : d₁ b (g, h) = g • b h - b (g * h) + b g := rfl

theorem d₁_add (b b' : G → A) : d₁ (b + b') = d₁ b + d₁ b' := by
  funext p; simp only [d₁, Pi.add_apply, smul_add]; abel

theorem eq_of_sub_eq {a b c d : A} (h : c = d) (he : a - b = c - d) : a = b := by
  rw [← sub_eq_zero, he, h, sub_self]

theorem isCocycle₂_d₁ (b : G → A) : IsCocycle₂ (d₁ b) := by
  intro g h j
  simp only [d₁_apply, smul_add, smul_sub, mul_smul, mul_assoc]
  abel

theorem isCocycle₂_sub_d₁ {f : G × G → A} (hf : IsCocycle₂ f) (b : G → A) : IsCocycle₂ (f - d₁ b) := by
  intro g h j
  have h1 := hf g h j
  have h2 := isCocycle₂_d₁ b g h j
  simp only [Pi.sub_apply, smul_sub]
  exact eq_of_sub_eq (congrArg₂ HSub.hSub h1 h2) (by abel)

theorem isCoboundary₂_of_sub {f : G × G → A} (b : G → A) (h : IsCoboundary₂ (f - d₁ b)) :
    IsCoboundary₂ f := by
  obtain ⟨x, hx⟩ := h
  refine ⟨b + x, fun g h => ?_⟩
  have := hx g h
  simp only [Pi.sub_apply, d₁_apply, Pi.add_apply, smul_add] at this ⊢
  rw [eq_sub_iff_add_eq] at this
  rw [← this]; abel

/-! ## The cyclic case -/

section Cyclic

variable [Finite G] {σ : G} (hσ : ∀ g : G, ∃ i : ℕ, σ ^ i = g)

/-- The exponent of `g` in `[0, ord σ)`. -/
noncomputable def idx (g : G) : ℕ := (hσ g).choose % orderOf σ

include hσ in
theorem pow_idx (g : G) : σ ^ idx hσ g = g := by
  rw [idx, pow_mod_orderOf, (hσ g).choose_spec]

theorem idx_lt (g : G) : idx hσ g < orderOf σ :=
  Nat.mod_lt _ (isOfFinOrder_of_finite σ).orderOf_pos

theorem idx_pow {i : ℕ} (hi : i < orderOf σ) : idx hσ (σ ^ i) = i := by
  have h := pow_idx hσ (σ ^ i)
  rw [(isOfFinOrder_of_finite σ).pow_inj_mod, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt (idx_lt hσ _)] at h
  exact h

/-- A normalized cocycle on a cyclic group: `F (σ^i, σ^j) = [i + j ≥ m] a`. -/
theorem cyclic_normal_form {F : G × G → A} (hF : IsCocycle₂ F) (hF11 : F (1, 1) = 0)
    (hF0 : ∀ k, k + 1 < orderOf σ → F (σ ^ k, σ) = 0) (i j : ℕ) (hi : i < orderOf σ) (hj : j < orderOf σ) :
    F (σ ^ i, σ ^ j) = if orderOf σ ≤ i + j then F (σ ^ (orderOf σ - 1), σ) else 0 := by
  induction j with
  | zero =>
    rw [if_neg (show ¬ orderOf σ ≤ i + 0 by omega), pow_zero, map_one_snd_of_isCocycle₂ hF (σ ^ i), hF11,
      smul_zero]
  | succ j ih =>
    have hc := hF (σ ^ i) (σ ^ j) σ
    rw [← pow_add, ← pow_succ, hF0 j (by omega), smul_zero, zero_add, ih (by omega)] at hc
    rw [← hc]
    by_cases h1 : i + j + 1 < orderOf σ
    · rw [hF0 _ h1, if_neg (show ¬ orderOf σ ≤ i + j by omega),
        if_neg (show ¬ orderOf σ ≤ i + (j + 1) by omega), add_zero]
    · by_cases h2 : i + j + 1 = orderOf σ
      · rw [if_neg (show ¬ orderOf σ ≤ i + j by omega), if_pos (show orderOf σ ≤ i + (j + 1) by omega),
          add_zero, show i + j = orderOf σ - 1 by omega]
      · obtain ⟨r, hr⟩ : ∃ r, i + j = orderOf σ + r := ⟨i + j - orderOf σ, by omega⟩
        rw [if_pos (show orderOf σ ≤ i + j by omega), if_pos (show orderOf σ ≤ i + (j + 1) by omega), hr,
          pow_add, pow_orderOf_eq_one, one_mul, hF0 r (by omega), zero_add]

theorem sum_pow_smul_add (c : A) (i j : ℕ) :
    σ ^ i • ∑ t ∈ Finset.range j, σ ^ t • c + ∑ t ∈ Finset.range i, σ ^ t • c =
      ∑ t ∈ Finset.range (i + j), σ ^ t • c := by
  simp only [Finset.sum_range_add, Finset.smul_sum, ← mul_smul, ← pow_add]
  exact add_comm _ _

include hσ in
theorem isCoboundary₂_of_cyclic {f : G × G → A} (hf : IsCocycle₂ f)
    (hnorm : ∀ a : A, σ • a = a → ∃ c : A, ∑ t ∈ Finset.range (orderOf σ), σ ^ t • c = a) :
    IsCoboundary₂ f := by
  classical
  have hm0 : 0 < orderOf σ := (isOfFinOrder_of_finite σ).orderOf_pos
  obtain ⟨b, hb⟩ : ∃ b : G → A, ∀ g, b g = f (1, 1) - ∑ t ∈ Finset.range (idx hσ g), f (σ ^ t, σ) :=
    ⟨_, fun _ => rfl⟩
  have hFc : IsCocycle₂ (f - d₁ b) := isCocycle₂_sub_d₁ hf b
  have hb1 : b 1 = f (1, 1) := by
    have h0 : idx hσ 1 = 0 := by simpa using idx_pow hσ (i := 0) hm0
    rw [hb, h0, Finset.sum_range_zero, sub_zero]
  have hF11 : (f - d₁ b) (1, 1) = 0 := by
    simp only [Pi.sub_apply, d₁_apply, one_smul, mul_one, hb1]; abel
  have hF0 : ∀ k, k + 1 < orderOf σ → (f - d₁ b) (σ ^ k, σ) = 0 := by
    intro k hk
    have h1 : idx hσ σ = 1 := by simpa using idx_pow hσ (i := 1) (by omega)
    have hbσ : b σ = 0 := by
      rw [hb, h1, Finset.sum_range_one, pow_zero, map_one_fst_of_isCocycle₂ hf σ, sub_self]
    have hk1 : idx hσ (σ ^ k * σ) = k + 1 := by rw [← pow_succ]; exact idx_pow hσ hk
    have hk0 : idx hσ (σ ^ k) = k := idx_pow hσ (by omega)
    rw [Pi.sub_apply, d₁_apply, hbσ, smul_zero, hb (σ ^ k * σ), hb (σ ^ k), hk1, hk0, Finset.sum_range_succ]
    abel
  have hnf := cyclic_normal_form hFc hF11 hF0
  -- the invariant element `a = F (σ ^ (m - 1), σ)`
  have hσa : σ • (f - d₁ b) (σ ^ (orderOf σ - 1), σ) = (f - d₁ b) (σ ^ (orderOf σ - 1), σ) := by
    by_cases hm1 : orderOf σ = 1
    · rw [orderOf_eq_one_iff.mp hm1, one_smul]
    · have hc := hFc σ (σ ^ (orderOf σ - 1)) σ
      have e1 : σ * σ ^ (orderOf σ - 1) = 1 := by
        rw [← pow_succ', Nat.sub_add_cancel hm0, pow_orderOf_eq_one]
      have e2 : σ ^ (orderOf σ - 1) * σ = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hm0, pow_orderOf_eq_one]
      have e3 := hnf 1 (orderOf σ - 1) (by omega) (by omega)
      rw [pow_one, if_pos (show orderOf σ ≤ 1 + (orderOf σ - 1) by omega)] at e3
      rw [e1, e2, map_one_fst_of_isCocycle₂ hFc σ, hF11, zero_add, e3,
        map_one_snd_of_isCocycle₂ hFc σ, hF11, smul_zero, add_zero] at hc
      exact hc.symm
  obtain ⟨c, hcn⟩ := hnorm _ hσa
  obtain ⟨b', hb'⟩ : ∃ b' : G → A, ∀ g, b' g = ∑ t ∈ Finset.range (idx hσ g), σ ^ t • c :=
    ⟨_, fun _ => rfl⟩
  apply isCoboundary₂_of_sub b
  refine ⟨b', fun g h => ?_⟩
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < orderOf σ ∧ σ ^ i = g := ⟨_, idx_lt hσ g, pow_idx hσ g⟩
  obtain ⟨j, hj, rfl⟩ : ∃ j, j < orderOf σ ∧ σ ^ j = h := ⟨_, idx_lt hσ h, pow_idx hσ h⟩
  rw [hnf i j hi hj, ← pow_add, hb', hb', hb', idx_pow hσ hi, idx_pow hσ hj]
  by_cases hij : orderOf σ ≤ i + j
  · obtain ⟨r, hr⟩ : ∃ r, i + j = orderOf σ + r := ⟨i + j - orderOf σ, by omega⟩
    rw [if_pos hij, hr, pow_add, pow_orderOf_eq_one, one_mul, idx_pow hσ (by omega : r < orderOf σ),
      sub_add_eq_add_sub, sum_pow_smul_add, hr, Finset.sum_range_add, hcn]
    simp only [pow_add, pow_orderOf_eq_one, one_mul, add_sub_cancel_right]
  · rw [if_neg hij, idx_pow hσ (by omega : i + j < orderOf σ), sub_add_eq_add_sub, sum_pow_smul_add,
      sub_self]

end Cyclic

/-! ## Inflation-restriction in degree 2 -/

section InfRes

variable (N : Subgroup G) [hN : N.Normal]

/-- A representative of the coset `g N`. -/
noncomputable def rep (g : G) : G := (QuotientGroup.mk g : G ⧸ N).out

theorem rep_inv_mul_mem (g : G) : (rep N g)⁻¹ * g ∈ N :=
  QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

theorem rep_eq_of_mem {g g' : G} (h : g⁻¹ * g' ∈ N) : rep N g = rep N g' := by
  unfold rep; rw [QuotientGroup.eq.mpr h]

theorem rep_mul_mem (g : G) {n : G} (hn : n ∈ N) : rep N (g * n) = rep N g :=
  rep_eq_of_mem N (by simpa [mul_assoc] using N.inv_mem hn)

theorem rep_mem_of_mem {n : G} (hn : n ∈ N) : rep N n ∈ N := by
  have h := N.mul_mem (rep_inv_mul_mem N n) (N.inv_mem hn)
  rw [mul_inv_cancel_right] at h
  simpa using N.inv_mem h

theorem rep_of_mem {n : G} (hn : n ∈ N) : rep N n = rep N 1 :=
  rep_eq_of_mem N (by simpa using N.inv_mem hn)

include hN in
theorem conj_mem' {n : G} (hn : n ∈ N) (h : G) : h⁻¹ * n * h ∈ N := by
  simpa using hN.conj_mem n hn h⁻¹

include hN in
theorem rep_mem_mul {n : G} (hn : n ∈ N) (h : G) : rep N (n * h) = rep N h := by
  refine rep_eq_of_mem N ?_
  have := conj_mem' N (N.inv_mem hn) h
  convert this using 1; group

theorem exists_zero_on_sub {f : G × G → A}
    (hNf : IsCoboundary₂ (fun p : N × N => f ((p.1 : G), (p.2 : G)))) :
    ∃ b : G → A, ∀ n ∈ N, ∀ n' ∈ N, (f - d₁ b) (n, n') = 0 := by
  classical
  obtain ⟨β, hβ⟩ := hNf
  refine ⟨fun g => if h : g ∈ N then β ⟨g, h⟩ else 0, fun n hn n' hn' => ?_⟩
  have e : n • β ⟨n', hn'⟩ - β ⟨n * n', N.mul_mem hn hn'⟩ + β ⟨n, hn⟩ = f (n, n') :=
    hβ ⟨n, hn⟩ ⟨n', hn'⟩
  simp only [Pi.sub_apply, d₁_apply, dif_pos hn, dif_pos hn', dif_pos (N.mul_mem hn hn')]
  rw [e, sub_self]

theorem exists_zero_right {f : G × G → A} (hf : IsCocycle₂ f)
    (h0 : ∀ n ∈ N, ∀ n' ∈ N, f (n, n') = 0) :
    ∃ b : G → A, ∀ g, ∀ n ∈ N, (f - d₁ b) (g, n) = 0 := by
  refine ⟨fun g => -f (rep N g, (rep N g)⁻¹ * g), fun g n hn => ?_⟩
  have hbn : f (rep N n, (rep N n)⁻¹ * n) = 0 :=
    h0 _ (rep_mem_of_mem N hn) _ (rep_inv_mul_mem N n)
  have hgn : rep N (g * n) = rep N g := rep_mul_mem N g hn
  have hc := hf (rep N g) ((rep N g)⁻¹ * g) n
  rw [mul_inv_cancel_left, h0 _ (rep_inv_mul_mem N g) _ hn, smul_zero, zero_add,
    mul_assoc ((rep N g)⁻¹) g n] at hc
  simp only [Pi.sub_apply, d₁_apply, hgn, hbn, neg_zero, smul_zero]
  rw [← hc]; abel

include hN in
theorem exists_zero_both {f : G × G → A} (hf : IsCocycle₂ f) (h1 : ∀ g, ∀ n ∈ N, f (g, n) = 0)
    (hH1 : ∀ φ : N → A, IsCocycle₁ φ → IsCoboundary₁ φ) :
    ∃ b : G → A, (∀ g, ∀ n ∈ N, (f - d₁ b) (g, n) = 0) ∧ ∀ n ∈ N, ∀ h, (f - d₁ b) (n, h) = 0 := by
  classical
  have hfR : ∀ g h, ∀ n ∈ N, f (g, h * n) = f (g, h) := by
    intro g h n hn
    have := hf g h n
    rw [h1 _ n hn, h1 h n hn, smul_zero, zero_add, zero_add] at this
    exact this.symm
  have hcoc : ∀ k : G, IsCocycle₁ (fun n : N => f ((n : G), k)) := by
    intro k n n'
    have hc := hf n n' k
    rw [h1 _ _ n'.2, add_zero] at hc
    have e : f ((n : G), (n' : G) * k) = f (n, k) := by
      rw [show (n' : G) * k = k * (k⁻¹ * n' * k) by group]
      exact hfR _ _ _ (conj_mem' N n'.2 k)
    rw [e] at hc
    exact hc
  choose c hc using fun k : G => hH1 _ (hcoc k)
  have hc' : ∀ k, ∀ n ∈ N, n • c k - c k = f (n, k) := fun k n hn => hc k ⟨n, hn⟩
  refine ⟨fun h => c (rep N h) - c (rep N 1), fun g n hn => ?_, fun n hn h => ?_⟩
  · simp only [Pi.sub_apply, d₁_apply, rep_of_mem N hn, rep_mul_mem N g hn, sub_self, smul_zero,
      h1 g n hn]
    abel
  · have hfn : f (n, h) = f (n, rep N h) := by
      conv_lhs => rw [← mul_inv_cancel_left (rep N h) h]
      exact hfR _ _ _ (rep_inv_mul_mem N h)
    have hf1 : f (n, rep N 1) = 0 := h1 n _ (rep_mem_of_mem N (one_mem N))
    simp only [Pi.sub_apply, d₁_apply, rep_of_mem N hn, rep_mem_mul N hn, sub_self, add_zero, smul_sub]
    have h0' : n • c (rep N 1) - c (rep N 1) = 0 := by rw [hc' _ n hn, hf1]
    rw [hfn, ← hc' _ n hn]
    exact eq_of_sub_eq h0' (by abel)

include hN in
theorem invariant_of_zero {F : G × G → A} (hF : IsCocycle₂ F) (hR : ∀ g, ∀ n ∈ N, F (g, n) = 0)
    (hL : ∀ n ∈ N, ∀ h, F (n, h) = 0) (g h : G) {n : G} (hn : n ∈ N) :
    F (g * n, h) = F (g, h) ∧ F (g, h * n) = F (g, h) ∧ n • F (g, h) = F (g, h) := by
  have hright : ∀ g h, ∀ n ∈ N, F (g, h * n) = F (g, h) := by
    intro g h n hn
    have := hF g h n
    rw [hR _ n hn, hR h n hn, smul_zero, zero_add, zero_add] at this
    exact this.symm
  have hleft : ∀ g h, ∀ n ∈ N, F (g * n, h) = F (g, h) := by
    intro g h n hn
    have := hF g n h
    rw [hR g n hn, hL n hn h, smul_zero, zero_add, add_zero,
      show n * h = h * (h⁻¹ * n * h) by group] at this
    rw [this]; exact hright _ _ _ (conj_mem' N hn h)
  refine ⟨hleft g h n hn, hright g h n hn, ?_⟩
  have := hF n g h
  rw [hL n hn g, hL n hn (g * h), add_zero, add_zero, show n * g = g * (g⁻¹ * n * g) by group,
    hleft _ _ _ (conj_mem' N hn g)] at this
  exact this.symm

include hN in
/-- Degree-2 inflation-restriction: `f` is cohomologous to a cocycle inflated from `G ⧸ N` with values in `A^N`. -/
theorem exists_inflated {f : G × G → A} (hf : IsCocycle₂ f)
    (hH1 : ∀ φ : N → A, IsCocycle₁ φ → IsCoboundary₁ φ)
    (hNf : IsCoboundary₂ (fun p : N × N => f ((p.1 : G), (p.2 : G)))) :
    ∃ b : G → A, IsCocycle₂ (f - d₁ b) ∧ ∀ g h : G, ∀ n ∈ N,
      (f - d₁ b) (g * n, h) = (f - d₁ b) (g, h) ∧ (f - d₁ b) (g, h * n) = (f - d₁ b) (g, h) ∧
        n • (f - d₁ b) (g, h) = (f - d₁ b) (g, h) := by
  obtain ⟨b0, hb0⟩ := exists_zero_on_sub N hNf
  have hf0 := isCocycle₂_sub_d₁ hf b0
  obtain ⟨b1, hb1⟩ := exists_zero_right N hf0 hb0
  have hf1 := isCocycle₂_sub_d₁ hf0 b1
  obtain ⟨b2, hb2R, hb2L⟩ := exists_zero_both N hf1 hb1 hH1
  have hf2 := isCocycle₂_sub_d₁ hf1 b2
  have e : f - d₁ (b0 + b1 + b2) = f - d₁ b0 - d₁ b1 - d₁ b2 := by
    rw [d₁_add, d₁_add]; abel
  refine ⟨b0 + b1 + b2, ?_, fun g h n hn => ?_⟩
  · rw [e]; exact hf2
  · rw [e]; exact invariant_of_zero N hf2 hb2R hb2L g h hn

end InfRes

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_Lc =====
section

/-!
# S4-PD (3), group layer part 1: locally constant cochains and the index lemma

For a compact topological group `P` acting on `A` (locally constant action, `LcAct`):
* `lc_dite`, `lc_sum`, `lc_d₁`: closure properties of locally constant cochains;
* `exists_open_inv`: a locally constant function on `P × P` is invariant under right multiplication by an open
  subgroup in each variable (finite level); `exists_openNormal_le`, `actKer`, `isOpen_actKer`;
* `index_lemma`: for an open subgroup `H` whose index is invertible on `A`, a locally constant 2-cocycle whose
  restriction to `H × H` is the coboundary of a locally constant cochain is a locally constant coboundary on `P`
  (normalise to `f(g, n) = 0` for `n ∈ H`, then average over the left cosets `P ⧸ H`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology Filter Topology

section LcBasic

variable {X : Type*} [TopologicalSpace X]

/-- Extension by zero from a clopen set is locally constant. -/
theorem lc_dite {S : Set X} [DecidablePred (· ∈ S)] (hS : IsClopen S) {Z : Type*} [Zero Z] (u : S → Z)
    (hu : IsLocallyConstant u) :
    IsLocallyConstant (fun x => if h : x ∈ S then u ⟨x, h⟩ else 0) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ S
  · have h1 : ∀ᶠ y in 𝓝 x, y ∈ S := hS.isOpen.mem_nhds hx
    have h2 : ∀ᶠ (y' : S) in 𝓝 ⟨x, hx⟩, ∀ h : y'.1 ∈ S, u ⟨y'.1, h⟩ = u ⟨x, hx⟩ := by
      filter_upwards [(IsLocallyConstant.iff_eventually_eq u).1 hu ⟨x, hx⟩] with y' hy' h
      exact hy'
    have h3 : ∀ᶠ y in 𝓝 x, ∀ h : y ∈ S, u ⟨y, h⟩ = u ⟨x, hx⟩ := by
      rw [← (hS.isOpen.isOpenEmbedding_subtypeVal).map_nhds_eq ⟨x, hx⟩]
      exact Filter.eventually_map.2 h2
    filter_upwards [h1, h3] with y hy hq
    rw [dif_pos hy, dif_pos hx]
    exact hq hy
  · have h1 : ∀ᶠ y in 𝓝 x, y ∉ S := hS.isClosed.isOpen_compl.mem_nhds hx
    filter_upwards [h1] with y hy
    rw [dif_neg hy, dif_neg hx]

/-- Finite sums of locally constant functions are locally constant. -/
theorem lc_sum {ι : Type*} [Fintype ι] {B : Type*} [AddCommMonoid B] (u : ι → X → B)
    (hu : ∀ i, IsLocallyConstant (u i)) : IsLocallyConstant (fun x => ∑ i, u i x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ᶠ y in 𝓝 x, ∀ i, u i y = u i x :=
    Filter.eventually_all.2 (fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hu i) x)
  filter_upwards [this] with y hy
  exact Finset.sum_congr rfl (fun i _ => hy i)

end LcBasic

variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  {A : Type*} [AddCommGroup A] [DistribMulAction P A]

/-- `P` acts locally constantly on `A` (a continuous action on a discrete module). -/
def LcAct (P A : Type*) [Group P] [TopologicalSpace P] [AddCommGroup A] [DistribMulAction P A] : Prop :=
  ∀ a : A, IsLocallyConstant fun g : P => g • a

/-- `f` is the coboundary of a locally constant 1-cochain. -/
def IsLcCob (f : P × P → A) : Prop :=
  ∃ b : P → A, IsLocallyConstant b ∧ ∀ g h : P, f (g, h) = d₁ b (g, h)

theorem smul_zsmul' (g : P) (x : ℤ) (a : A) : g • (x • a) = x • (g • a) :=
  map_zsmul (DistribSMul.toAddMonoidHom A g) x a

theorem lc_smul_comp (hact : LcAct P A) {b : P → A} (hb : IsLocallyConstant b) :
    IsLocallyConstant fun p : P × P => p.1 • b p.2 := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, h⟩
  have h1 := (IsLocallyConstant.iff_eventually_eq _).1 (hact (b h)) g
  have h2 := (IsLocallyConstant.iff_eventually_eq _).1 hb h
  rw [nhds_prod_eq]
  filter_upwards [h1.prod_mk h2] with p hp
  rw [hp.2, hp.1]

theorem lc_d₁ (hact : LcAct P A) {b : P → A} (hb : IsLocallyConstant b) : IsLocallyConstant (d₁ b) := by
  have h1 := lc_smul_comp hact hb
  have h2 : IsLocallyConstant fun p : P × P => b (p.1 * p.2) := hb.comp_continuous continuous_mul
  have h3 : IsLocallyConstant fun p : P × P => b p.1 := hb.comp_continuous continuous_fst
  exact (h1.sub h2).add h3

/-- An open subgroup of a compact group contains an open normal subgroup. -/
theorem exists_openNormal_le [CompactSpace P] (W : Subgroup P) (hW : IsOpen (W : Set P)) :
    ∃ N : Subgroup P, N.Normal ∧ IsOpen (N : Set P) ∧ N ≤ W := by
  obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    ⟨W.isClosed_of_isOpen hW, hW⟩ W.one_mem
  exact ⟨N.toSubgroup, N.isNormal', N.isOpen', fun x hx => hN hx⟩

/-- The kernel of the action. -/
def actKer (P A : Type*) [Group P] [AddCommGroup A] [DistribMulAction P A] : Subgroup P where
  carrier := {x | ∀ a : A, x • a = a}
  one_mem' := fun a => one_smul P a
  mul_mem' := fun {x y} hx hy a => by rw [mul_smul, hy, hx]
  inv_mem' := fun {x} hx a => by rw [inv_smul_eq_iff, hx]

theorem mem_actKer {x : P} : x ∈ actKer P A ↔ ∀ a : A, x • a = a := Iff.rfl

/-! ## Coset representatives for a (not necessarily normal) subgroup -/

/-- A representative of the left coset `g H`. -/
noncomputable def crep (H : Subgroup P) (g : P) : P := (QuotientGroup.mk g : P ⧸ H).out

theorem crep_inv_mul_mem (H : Subgroup P) (g : P) : (crep H g)⁻¹ * g ∈ H :=
  QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

/-! ## The index lemma -/

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_PerfectCx_Z1Ex =====
section

/-!
# S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`

For a subgroup `Γ` of a topological group `G` and representations `ρ`, `σ` of `G`, an equivariant linear map
`q : M → N` induces `z1Map : Z¹(Γ, M) → Z¹(Γ, N)` (locally constant cocycles, the `S4-CurveCoh` convention).

* `H2Van ρ Γ K`: locally constant 2-cocycles with values in the submodule `K` are coboundaries of locally constant
  `K`-valued cochains (cochains on `Γ`, the `h2_eq_zero` shape);
* `z1Map_surjective`: if `q` is surjective and `H2Van` holds for `ker q`, then `z1Map` is surjective
  (lift a cocycle along a set-theoretic section, its coboundary lies in `ker q`, correct by a `ker q`-valued cochain);
* `H2All k G Γ l n`: `H² = 0` for every finite `lⁿ`-torsion representation with open kernel (the output shape of
  `h2_pi1geo_eq_zero` / `h2_closed_eq_zero`); `h2Van_of_all` passes it to subrepresentations, and
  `z1Map_surjective_of_all` is the exactness statement used for `E_Γ = Z¹(Γ; A)` and `E_s = Z¹(I_s; A)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N) (Γ : Subgroup G)

/-- The kernel of an equivariant map, as a subrepresentation. -/
def kerRep (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m)) : Subrepresentation ρ where
  toSubmodule := LinearMap.ker q
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hq, hv, map_zero]

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_ThetaCube_GrA =====
section

/-!
# S4-ThetaCube, file GrA (D-C1, part 7): dominant pull-backs for the Gram matrix
* `fpull_eq_ffMap`, `fpull_comp_dom`: along dominant maps `fpull` is the field map `ffMap`;
* `surjective_hom_of_nonempty`, `surjective_fst_left`, `surjective_snd_left`; `surjective_prj`, `isDominant_prj`;
* `qb b` (the three projections `J^3 ⟶ J`), `isDominant_qb`, `Phi3_qb`;
* **`ffMap_Phi3_fpull`**: `Φ3^# (q_b^# G) = ψ_{b}^# G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Dom

variable {C P Y : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral Y]

end Dom

section GrA

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem surjective_snd_left (A B : Over (Spec (.of K))) [Nonempty A.left] : Surjective (snd A B).left := by
  have := surjective_hom_of_nonempty A
  show Surjective (Limits.pullback.snd A.hom B.hom)
  infer_instance

variable (P0 : Place K F)

end GrA

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_GrB =====
section

/-!
# S4-ThetaCube, file GrB (D-C1, part 8): the Gram matrix on `J^3`
* `sum_blk_tauS`, `sum_blk_fiber`: block sums;
* `grJ d S m fR`: `Σ_{b ∈ S} q_b^# trJ d (f_l f_l') + Σ_i f_l(m_i) f_l'(m_i)` on `J^3`;
* **`ffMap_det_grJ`**: `Φ3^# det (grJ) = (det_k)^2` (`det M^2 = det (Mᵀ M)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

theorem sum_blk_tauS {M : Type*} [AddCommMonoid M] (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3))
    (φ : Fin n → M) : ∑ k ∈ blk n β S, φ k = ∑ j, φ (tauS n β S j) := by
  rw [blk, ← Finset.sum_coe_sort (Finset.univ.filter (fun k => β k ∈ S)),
    ← (Finset.univ.filter (fun k => β k ∈ S)).equivFin.symm.sum_comp]
  rfl

theorem sum_blk_fiber {M : Type*} [AddCommMonoid M] (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3))
    (φ : Fin n → M) : ∑ b ∈ S, ∑ k ∈ blk n β {b}, φ k = ∑ k ∈ blk n β S, φ k := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := blk n β S) (t := S) (g := β)
    (fun k hk => (Finset.mem_filter.mp hk).2)]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [blk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => ⟨h ▸ hb, h⟩, fun h => h.2⟩

section GrB

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end GrB

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_DegPoly_Cube =====
section

/-!
# Degree polynomiality, part 3: the quadratic relation from the cube relation (unit S4-DegPoly)

The input `hquad` of `deg_poly_of_quad` in the form the theorem of the cube gives it (Milne, Abelian Varieties,
Cor. 5.4 and the proof of Lemma 10.12): if `Q : R → N` on an abelian group satisfies `Q 0 = 0`, the cube relation
`Q (a+b+e) - Q (a+b) - Q (a+e) - Q (b+e) + Q a + Q b + Q e = 0` and `Q (-a) = Q a` (`D` symmetric), then
`Q (n • a + b) = n² • Q a + n • B a b + Q b` with `B a b = Q (a + b) - Q a - Q b`. `quad_of_cube` states it for
`c : R → M` up to numerical equivalence (`numKer I`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.DegPoly

section Quad

variable {R N : Type*} [AddCommGroup R] [AddCommGroup N]

variable {Q : R → N}

theorem polar_comm (a b : R) : polar Q a b = polar Q b a := by
  simp only [polar, add_comm a b]
  abel

theorem polar_add_left
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (a e b : R) : polar Q (a + e) b = polar Q a b + polar Q e b := by
  unfold polar
  rw [← sub_eq_zero]
  convert hcube a e b using 1
  abel

/-- `a ↦ B a b` as an additive map. -/
def polarHom (hQ0 : Q 0 = 0)
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (b : R) : R →+ N where
  toFun a := polar Q a b
  map_zero' := by simp [polar, hQ0]
  map_add' a e := polar_add_left hcube a e b

theorem polar_self (hQ0 : Q 0 = 0)
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (hsym : ∀ a, Q (-a) = Q a) (a : R) : polar Q a a = (2 : ℤ) • Q a := by
  have h1 : polar Q (-a) a = -polar Q a a := (polarHom hQ0 hcube a).map_neg a
  have h2 : polar Q (-a) a = Q 0 - Q (-a) - Q a := by simp only [polar, neg_add_cancel]
  rw [hQ0, hsym] at h2
  have h3 : polar Q a a = -(0 - Q a - Q a) := by rw [← h2, h1, neg_neg]
  rw [h3, two_smul]
  abel

theorem quad_step (hQ0 : Q 0 = 0)
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (hsym : ∀ a, Q (-a) = Q a) (m : ℤ) (a b : R) :
    Q ((m + 1) • a + b) = Q (m • a + b) + (2 * m + 1) • Q a + polar Q a b := by
  have hx : (m + 1) • a + b = (m • a + b) + a := by rw [add_smul, one_smul]; abel
  have hp : Q ((m • a + b) + a) = Q (m • a + b) + Q a + polar Q (m • a + b) a := by
    simp only [polar]
    abel
  have hz : polar Q (m • a) a = m • polar Q a a := map_zsmul (polarHom hQ0 hcube a) m a
  rw [hx, hp, polar_add_left hcube, hz, polar_self hQ0 hcube hsym, polar_comm b a, smul_smul,
    add_smul, one_smul, mul_comm m 2]
  abel

/-- **The quadratic relation** from the cube relation and symmetry. -/
theorem quad_of_cube_fun (hQ0 : Q 0 = 0)
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (hsym : ∀ a, Q (-a) = Q a) (n : ℤ) (a b : R) :
    Q (n • a + b) = n ^ 2 • Q a + n • polar Q a b + Q b := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [quad_step hQ0 hcube hsym, ih]
    simp only [add_sq, add_smul, mul_smul, one_pow, mul_one, one_smul]
    abel
  | pred i ih =>
    have hs := quad_step hQ0 hcube hsym (-(i : ℤ) - 1) a b
    rw [sub_add_cancel, ih] at hs
    have h : Q ((-(i : ℤ) - 1) • a + b) = ((-(i : ℤ)) ^ 2 • Q a + (-(i : ℤ)) • polar Q a b + Q b) -
        (2 * (-(i : ℤ) - 1) + 1) • Q a - polar Q a b := by
      rw [hs]
      abel
    rw [h]
    simp only [sub_sq, neg_sq, add_smul, sub_smul, mul_smul, one_pow, mul_one, one_smul, neg_smul, two_smul]
    abel

end Quad

variable {M : Type*} [AddCommGroup M] {g : ℕ}

/-- **Input for `deg_poly_of_quad`** from the cube relation, `0^* D ≡ 0` and `[-1]^* D ≡ D`, all up to numerical
equivalence. -/
theorem quad_of_cube (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ) {R : Type*} [Ring R] (c : R → M)
    (hzero : c 0 ∈ numKer I) (hsym : ∀ a, c (-a) - c a ∈ numKer I)
    (hcube : ∀ a b e : R,
      c (a + b + e) - c (a + b) - c (a + e) - c (b + e) + c a + c b + c e ∈ numKer I)
    (a b : R) : ∃ e : M, ∀ n : ℤ, c (n * a + b) - (n ^ 2 • c a + n • e + c b) ∈ numKer I := by
  refine ⟨c (a + b) - c a - c b, fun n => ?_⟩
  have hQ0 : ((c 0 : M) : M ⧸ numKer I) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hzero
  have hQs : ∀ x : R, ((c (-x) : M) : M ⧸ numKer I) = ((c x : M) : M ⧸ numKer I) :=
    fun x => QuotientAddGroup.eq_iff_sub_mem.mpr (hsym x)
  have hQc : ∀ x y z : R, ((c (x + y + z) : M) : M ⧸ numKer I) - (c (x + y) : M ⧸ numKer I) -
      (c (x + z) : M ⧸ numKer I) - (c (y + z) : M ⧸ numKer I) + (c x : M ⧸ numKer I) +
      (c y : M ⧸ numKer I) + (c z : M ⧸ numKer I) = 0 := by
    intro x y z
    have h := (QuotientAddGroup.eq_zero_iff _).mpr (hcube x y z)
    simpa only [QuotientAddGroup.mk_add, QuotientAddGroup.mk_sub] using h
  have hmain := quad_of_cube_fun (Q := fun x => ((c x : M) : M ⧸ numKer I)) hQ0 hQc hQs n a b
  simp only [polar] at hmain
  rw [← QuotientAddGroup.eq_zero_iff, ← zsmul_eq_mul]
  simp only [QuotientAddGroup.mk_add, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_zsmul]
  rw [hmain, sub_self]

end RamanujanPetersson.DegPoly


end

-- ===== S4.Def_RP_ThetaCube_Hook =====
section

/-!
# S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`

For one translate `x0 ∉ W` and `c G := (polyEnd π G)^* D'` (`cD`):
* `hzero_D`, `hproj_D`, **`hD_D`** (`(D'^g) > 0` by multilinear expansion), `hsym_D` (exact);
* `CubePrincipal P0 x0`: a positive multiple of the cube divisor on `J^3` is principal;
* **`hcube_D`** and **`quad_D`** (the output of `DegPoly.quad_of_cube`), conditional on `CubePrincipal P0 x0`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

theorem polyEnd_neg (π : A ⟶ A) (G : ℤ[X]) : IsogDegB.polyEnd π (-G) = (IsogDegB.polyEnd π G)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← IsogDegB.polyEnd_add, neg_add_cancel, polyEnd_zero])

end Poly

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (hg : 0 < genusFK K F) (g : ℕ)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_GrC =====
section

/-!
# S4-ThetaCube, file GrC (D-C1, part 9): the cube divisor is principal up to `2`
* `eq_zero_of_pullback_surj`: pull-back along a dominant surjection from `X1^n` is injective on Weil divisors;
* `div_sq_eq`: `div (f ^ 2) = div f + div f`;
* **`cubePrincipal_gram`**: `h := Π_S det (grJ S) ^ (±1)` has `div h = 2 • cubeZ` (`Φ3^# h = Π_S det_k ^ (±2)`,
  `cube_PP`), so `CubePrincipal P0 x0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

theorem div_sq_eq {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {f : X.functionField} (hf : f ≠ 0) :
    JacDivisors.div X (f ^ 2) = JacDivisors.div X f + JacDivisors.div X f := by
  rw [sq, JacDivisors.div_mul hf hf]

section GrC

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end GrC

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Surj3 =====
section

/-!
# S4-ThetaCube, file Surj3 (D-C1, part 10): `Φ3 : X1^n ⟶ J^3` is surjective and dominant
* `exists_coords`: coordinates on a block with a prescribed sum of places;
* `exists_pt_Phi3`: Jacobi inversion on each block (`#blk {b} = g`): every `K`-point of `J^3` is `p ≫ Φ3`;
* **`surjective_Phi3`**, **`isDominant_Phi3`** (closed image, contains every closed point, `J^3` Jacobson).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Surj3

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

open Classical in
/-- Coordinates on a block `s` with `Σ_{k ∈ s} [a k] = Σ_i [t i]` (`#s = N`). -/
theorem exists_coords {I : Type*} (s : Finset I) {N : ℕ} (hc : s.card = N) (t : Fin N → Place K F)
    (q : Place K F) :
    ∃ a : I → Place K F, ∑ k ∈ s, Finsupp.single (a k) (1 : ℤ) = ∑ i, Finsupp.single (t i) (1 : ℤ) := by
  let e : {x // x ∈ s} ≃ Fin N := s.equivFin.trans (finCongr hc)
  refine ⟨fun k => if hk : k ∈ s then t (e ⟨k, hk⟩) else q, ?_⟩
  rw [← Finset.sum_coe_sort s]
  exact Fintype.sum_equiv e _ _ fun x => by simp only [dif_pos x.2]

end Surj3

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_JacFrob_BrSig =====
section

/-!
# S4-JacFrob, part BrSig (bridge 6): the bridge intertwines the two Frobenius actions

* `sig_incF`: on a level, `σ` is the level Frobenius `frobF`;
* `plE_contB`: `frob⁻¹ (contB j P) = contB j (σ⁻¹ P)`;
* `psiD_actD`, **`Psi_piBar`**: `Ψ ∘ π = σ_* ∘ Ψ` on `Pic(X-bar)`; `Psi_symm_sigPic`, `Psi0Equiv_piBar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places ZetaSB RamanujanPetersson.JacComplete

section BrSig

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

theorem isLeft_sigPl_symm (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    ((sigPl Fq F Ω hk).symm P).isLeft = P.isLeft := by
  rcases P with w | w <;> rfl

theorem ord_sigPl_symm (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) (f : Fbar Fq F Ω) :
    ((sigPl Fq F Ω hk).symm P).ord f = P.ord (sig Fq F Ω hk f) := by
  have h := ord_sigPl Fq F Ω hk ((sigPl Fq F Ω hk).symm P) (sig Fq F Ω hk f)
  rw [Equiv.apply_symm_apply, AlgEquiv.symm_apply_apply] at h
  exact h.symm

/-- On a level, `σ` is the level Frobenius. -/
theorem sig_incF (j : ℕ) (f : Fc Fq F Ω (lev j)) :
    sig Fq F Ω hk (incF Fq F Ω j f) = incF Fq F Ω j (frobF (isConstExt_Fc Fq F Ω hk (lev j)) f) := by
  have hy : ((incF Fq F Ω j f : Fbar Fq F Ω) : Ω) ∈ Fc Fq F Ω (lev j) := by
    rw [coe_incF]; exact f.2
  have he : (⟨((incF Fq F Ω j f : Fbar Fq F Ω) : Ω), hy⟩ : Fc Fq F Ω (lev j)) = f :=
    Subtype.ext (coe_incF Fq F Ω j f)
  apply Subtype.ext
  rw [coe_sig_of_mem Fq F Ω hk _ hy, he, coe_incF]

end BrSig

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Val2 =====
section

/-!
# S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`

Generic:
* `ptOf_comp_xMap`, `symPt_comp_symMap`, `ptSet_comp_symMap`: the support of `y ∘ symMap f` is `(supp y) ∘ f`;
* `thetaK`, `psiJ_kpt`: `psiJ (kpt y) = [Z(y|S_g)] - [Θ]`; `cls_of_kpt`, `cls_mor`, `cls_mor_hom`: classes of `a` and `a ≫ mor φ hφ`.

For `J = J_{F-bar}` over `k-bar`:
* `PhiR_eq_pow`: `Φ b = (σ⁻¹ b)^q` on `Rfin`; `ptP_comp_PhiR`: the place of `χ ∘ Φ` is `σ_*` of the place of `χ`;
* `comp_PhiR_injective`, `Zdiv_image_PhiR`, `Zdiv_ptSet_PhiS`: `Z(y ∘ Φ_S) = σ_* Z(y)`;
* `cTheta = σ_*[Θ] - [Θ] ∈ Pic⁰`; **`jacPicEquiv_piJ0`**: `[a ≫ π_J⁰] = σ_*[a] + cTheta`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory IsDedekindDomain
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR
open RamanujanPetersson.PicDescent

universe u

section SymPt

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

theorem ptOf_comp_xMap (a : Fin g → (B' →ₐ[k] k)) (f : B →ₐ[k] B') :
    (ptOf a).comp (xMap f) = ptOf (fun i => (a i).comp f) :=
  algHom_ext_inc fun i => by
    rw [AlgHom.comp_assoc, xMap_inc, ← AlgHom.comp_assoc, ptOf_inc, ptOf_inc]

theorem symPt_comp_symMap (a : Fin g → (B' →ₐ[k] k)) (f : B →ₐ[k] B') :
    (symPt a).comp (symMap (g := g) f) = symPt (fun i => (a i).comp f) := by
  ext x
  show ptOf a (xMap f (x : XPow k B g)) = ptOf (fun i => (a i).comp f) (x : XPow k B g)
  rw [← AlgHom.comp_apply, ptOf_comp_xMap]

open Classical in
theorem ptSet_comp_symMap [IsAlgClosed k] (y : SymRing k B' g →ₐ[k] k) (f : B →ₐ[k] B') :
    ptSet (y.comp (symMap (g := g) f)) = (ptSet y).image (fun χ => χ.comp f) := by
  rw [← symPt_liftTuple y, symPt_comp_symMap, ptSet_symPt, ptSet_symPt, Finset.image_image]
  rfl

end SymPt

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

set_option synthInstance.maxHeartbeats 100000 in
theorem PhiR_eq_pow (b : Places.Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :
    PhiR Fq F Ω hk b = (sigRfin Fq F Ω hk).symm b ^ Fintype.card Fq :=
  Subtype.ext (by rw [coe_PhiR, Phi_apply', SubmonoidClass.coe_pow]; rfl)

set_option synthInstance.maxHeartbeats 100000 in
theorem ptP_comp_PhiR (χ : Places.Rfin (kbar Fq Ω) (Fbar Fq F Ω) →ₐ[kbar Fq Ω] kbar Fq Ω) :
    (Sum.inl (ptP (χ.comp (PhiR Fq F Ω hk))) : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) =
      sigPl Fq F Ω hk (Sum.inl (ptP χ)) := by
  show _ = Sum.inl (pullH (sigRfin Fq F Ω hk).symm (ptP χ))
  refine congrArg Sum.inl (HeightOneSpectrum.ext (Ideal.ext fun b => ?_))
  rw [mem_ptP, pullH_asIdeal, Ideal.mem_comap, mem_ptP, AlgHom.comp_apply, PhiR_eq_pow, map_pow,
    pow_eq_zero_iff Fintype.card_ne_zero]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
theorem comp_PhiR_injective :
    Function.Injective fun χ : Places.Rfin (kbar Fq Ω) (Fbar Fq F Ω) →ₐ[kbar Fq Ω] kbar Fq Ω =>
      χ.comp (PhiR Fq F Ω hk) := fun χ χ' h => by
  have h1 : χ.comp (PhiR Fq F Ω hk) = χ'.comp (PhiR Fq F Ω hk) := h
  have h2 : (Sum.inl (ptP (χ.comp (PhiR Fq F Ω hk))) : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) =
      Sum.inl (ptP (χ'.comp (PhiR Fq F Ω hk))) := by rw [h1]
  rw [ptP_comp_PhiR, ptP_comp_PhiR] at h2
  exact ptP_injective (Sum.inl_injective ((sigPl Fq F Ω hk).injective h2))

open Classical in
set_option synthInstance.maxHeartbeats 100000 in
theorem Zdiv_image_PhiR (T : Finset (Places.Rfin (kbar Fq Ω) (Fbar Fq F Ω) →ₐ[kbar Fq Ω] kbar Fq Ω)) :
    Zdiv (T.image fun χ => χ.comp (PhiR Fq F Ω hk)) = sigD Fq F Ω hk (Zdiv T) := by
  unfold Zdiv
  rw [Finset.sum_image fun χ _ χ' _ h => comp_PhiR_injective Fq F Ω hk h, map_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [ptP_comp_PhiR]
  exact (Finsupp.equivMapDomain_single _ _ _).symm

set_option synthInstance.maxHeartbeats 100000 in
theorem Zdiv_ptSet_PhiS (y : SymRing (kbar Fq Ω) (Places.Rfin (kbar Fq Ω) (Fbar Fq F Ω))
      (genusFK (kbar Fq Ω) (Fbar Fq F Ω)) →ₐ[kbar Fq Ω] kbar Fq Ω) :
    Zdiv (ptSet (y.comp (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))))) =
      sigD Fq F Ω hk (Zdiv (ptSet y)) :=
  (congrArg Zdiv (ptSet_comp_symMap y (PhiR Fq F Ω hk))).trans (Zdiv_image_PhiR Fq F Ω hk _)

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Hom =====
section

/-!
# S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects

Generic (JacComplete context): `ptW` (a `K`-point of `J` inside `jX0(D(φ u0))` comes from a `K`-point of
`S_g[1/u0][1/φ u0]`), `UJ W` (the dense open `fst⁻¹W ∩ snd⁻¹W ∩ μ⁻¹W` of `J × J`), and `isMonHom_of_cls`:
a map `ψ : J ⟶ J` acting on the classes of the `K`-points over a dense open `W` through an additive map `s`
is a homomorphism of group objects. For `J = J_{F-bar}`: **`isMonHom_piJ`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem comp_left_apply {A B C : Over (Spec (.of K))} (a : A ⟶ B) (g : B ⟶ C) (x : A.left) :
    (a ≫ g).left x = g.left (a.left x) := by
  rw [Over.comp_left]
  rfl

theorem comp_left_cp {B C : Over (Spec (.of K))} (a : 𝟙_ (Over (Spec (.of K))) ⟶ B) (g : B ⟶ C) :
    (a ≫ g).left (IsLocalRing.closedPoint K) = g.left (a.left (IsLocalRing.closedPoint K)) := by
  rw [Over.comp_left]
  rfl

theorem nonempty_preimage_over {A B : Over (Spec (.of K))} (g : A ⟶ B) (t : B ⟶ A) (h : t ≫ g = 𝟙 B)
    (W : B.left.Opens) (hW : (W : Set B.left).Nonempty) :
    ((g.left ⁻¹ᵁ W : A.left.Opens) : Set A.left).Nonempty := by
  obtain ⟨w, hw⟩ := hW
  refine ⟨t.left w, ?_⟩
  show g.left (t.left w) ∈ W
  rw [← comp_left_apply, h]
  exact hw

variable (s : PicK K F ≃+ PicK K F)

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_TanP =====
section

/-!
# S4-JacFrob, part TanP: `q`-th roots in `Sym^g` (generic)

`k` algebraically closed of characteristic `p`, `q = p^n`.
* `xMap_pow_root`: if every `f b` is a `q`-th power, so is every `xMap f x` (`k` perfect, Frobenius additive);
* `symMap_pow_root`: if moreover `X'^g` is a domain, every `symMap f x` is the `q`-th power of an invariant
  (`(σ • u)^q = u^q` forces `σ • u = u`);
* `snd_pow_char`: in `K[ε]`, `(x^q).snd = 0`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacFrob

open RamanujanPetersson.JacSym

section PowRoot

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B]
  {B' : Type*} [CommRing B'] [Algebra k B'] {g : ℕ}
variable (p n : ℕ) [Fact p.Prime] [CharP k p]

theorem xMap_pow_root [IsDomain (XPow k B' g)] (f : B →ₐ[k] B') (hf : ∀ b, ∃ c, f b = c ^ p ^ n)
    (x : XPow k B g) : ∃ u, xMap f x = u ^ p ^ n := by
  have : CharP (XPow k B' g) p := charP_of_injective_algebraMap (algebraMap k (XPow k B' g)).injective p
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r b =>
    choose c hc using fun i => hf (b i)
    obtain ⟨r', hr'⟩ := IsAlgClosed.exists_pow_nat_eq r (pow_pos (Fact.out : p.Prime).pos n)
    refine ⟨r' • ∏ i, inc i (c i), ?_⟩
    rw [smul_pow, hr', ← Finset.prod_pow, map_smul, xMap_tprod, ← prod_inc]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hc i, map_pow]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv, add_pow_char_pow]⟩

theorem symMap_pow_root [IsDomain (XPow k B' g)] (f : B →ₐ[k] B') (hf : ∀ b, ∃ c, f b = c ^ p ^ n)
    (x : SymRing k B g) : ∃ y : SymRing k B' g, symMap f x = y ^ p ^ n := by
  have : CharP (XPow k B' g) p := charP_of_injective_algebraMap (algebraMap k (XPow k B' g)).injective p
  obtain ⟨u, hu⟩ := xMap_pow_root p n f hf (x : XPow k B g)
  have hinj : ∀ v w : XPow k B' g, v ^ p ^ n = w ^ p ^ n → v = w := fun v w h => by
    have h0 : (v - w) ^ p ^ n = 0 := by rw [sub_pow_char_pow, h, sub_self]
    exact sub_eq_zero.1 (IsNilpotent.eq_zero ⟨_, h0⟩)
  refine ⟨⟨u, (mem_symRing u).2 fun σ => hinj _ _ ?_⟩, Subtype.ext ?_⟩
  · rw [perm_smul_def, ← map_pow, ← hu, ← perm_smul_def, ← xMap_smul, smul_symRing]
  · rw [symMap_coe, SubmonoidClass.coe_pow]
    exact hu

end PowRoot

theorem snd_pow_char {K : Type*} [Field K] (p : ℕ) [CharP K p] (n : ℕ) (hn : n ≠ 0) (x : DualNumber K) :
    (x ^ p ^ n).snd = 0 := by
  rw [TrivSqZeroExt.snd_pow, nsmul_eq_mul, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn, zero_mul]

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_TanG =====
section

/-!
# S4-JacFrob, part TanG: the differential of `mor φ` (generic)

For `φ : S_g →ₐ S_g` with `φ u0 ≠ 0` and `W = jX0(D(φ u0)) ⊆ J`:
* `eJ_over`: `eJ φ` lies over `Spec K` via `Spec (algebraMap K BRing)`;
* `exists_lift_DS`: a `K[ε]`-point of `J` whose closed point lies in `W` comes from a `K`-algebra map `BRing φ → K[ε]`;
* `comp_mor_const`: if every `f : BRing φ →ₐ[K] K[ε]` kills the `ε`-part of `φ(S_g)`, such a point composed with
  `mor φ` is constant;
* `tan_eq_one_of_const`: a constant tangent vector is `1`;
* **`dφ_eq_one`**: then `dψ = 1` for `ψ = mor φ · (translation)` a homomorphism.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section TanG

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem tan_eq_one_of_const {A : Over (Spec (.of K))} [GrpObj A] (t : IsogDegB.Tan A)
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ A) (h : t.1 = toUnit _ ≫ e) : t = 1 := by
  have he : e = 1 := by
    rw [← IsogDegB.tan_spec t, h, ← Category.assoc, toUnit_unique (IsogDegB.ι0 K ≫ toUnit _) (𝟙 _),
      Category.id_comp]
  exact Subtype.ext (h.trans (by rw [he, MonObj.comp_one]; rfl))

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

end TanG

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Tan =====
section

/-!
# S4-JacFrob, part Tan: **`dπ_J = 1`**

`Φ_S = symMap Φ_R` with `Φ_R b = (σ⁻¹ b)^q`, so every element of `Φ_S(S_g)` is a `q`-th power (`PhiS_pow_root`) and
every `K[ε]`-point of `D(Φ_S u0)` kills its `ε`-part (`snd_PhiS`, `q = 0` in `k-bar`). Hence `π_J` is constant on
tangent vectors: **`dφ_piJ : dφ π_J = 1`** (the hypothesis `hπ` of `IsogDegB.dφ_polyEnd`, `polyEnd_separable`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end Gen

section Tan

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

set_option synthInstance.maxHeartbeats 100000 in
/-- Every element of `Φ_S(S_g)` is a `q`-th power. -/
theorem PhiS_pow_root (n : ℕ) [Fact (ringChar Fq).Prime] [CharP (kbar Fq Ω) (ringChar Fq)]
    (hq : Fintype.card Fq = ringChar Fq ^ n)
    (s : SymRing (kbar Fq Ω) (Places.Rfin (kbar Fq Ω) (Fbar Fq F Ω)) (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) :
    ∃ y, PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω)) s = y ^ ringChar Fq ^ n :=
  symMap_pow_root (ringChar Fq) n (PhiR Fq F Ω hk)
    (fun b => ⟨(sigRfin Fq F Ω hk).symm b, by rw [PhiR_eq_pow, hq]⟩) s

end Tan

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacAlg_Norm =====
section

/-!
# Core B algebra, part 2: `P_π` is monic of degree `2g` and `deg F = ∏ F(a)` (Milne 10.22, L5/L6)

For `D : DegreeData π g p`, `P_π = D.charPoly` (`P_π(n) = deg(n - π)`).
* `charPoly_monic`, `charPoly_natDegree`: `P_π` is monic of degree `2g`. Proof: for `a = 2^(2g)` the pencil
  `b ↦ deg(a - bX)` is a polynomial of degree `≤ 2g` which equals `Σ_k p_k a^k b^(2g-k)` at the `2g+1`
  divisors `b = 2^j` of `a`; at `b = 0` it gives `a^(2g) = p_(2g) a^(2g)`.
* `deg_eq_prod_roots`: over any algebraically closed field `K` of characteristic `0`,
  `deg F = ∏_{a ∈ roots P_π} F(a)` for every `F ∈ ℤ[X]` (Milne Lemma 10.22, without multivariable
  polynomial functions: induction on `deg F` with the pencil `s ↦ deg(F - F(s))`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial Finset

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

theorem natAbs_pow_cast {K : Type*} [CommRing K] (b : ℤ) :
    (((b.natAbs ^ (2 * g) : ℕ)) : K) = (b : K) ^ (2 * g) := by
  rw [Nat.cast_pow, pow_mul, pow_mul]
  congr 1
  rw [← Int.cast_natCast (R := K), ← Int.cast_pow, Int.natAbs_sq b, Int.cast_pow]

/-- `deg(b n - b X) = b^(2g) P_π(n)`. -/
theorem deg_mul_sub (b n : ℤ) :
    (D.deg (((b * n : ℤ) : ℤ[X]) - (b : ℤ[X]) * X) : ℚ) = (b : ℚ) ^ (2 * g) * D.charPoly.eval (n : ℚ) := by
  have : (((b * n : ℤ) : ℤ[X]) - (b : ℤ[X]) * X) = (b : ℤ[X]) * ((n : ℤ[X]) - X) := by push_cast; ring
  rw [this, D.deg_mul, D.deg_intCast, charPoly_eval, Nat.cast_mul, natAbs_pow_cast]

/-- The comparison polynomial `V(b) = Σ_k p_k a^k b^(2g-k)` (`= b^(2g) P(a/b)` for `b ≠ 0`). -/
noncomputable def homPoly (a : ℚ) : ℚ[X] :=
  ∑ k ∈ range (2 * g + 1), C (D.charPoly.coeff k * a ^ k) * X ^ (2 * g - k)

theorem homPoly_eval (a b : ℚ) :
    (D.homPoly a).eval b = ∑ k ∈ range (2 * g + 1), D.charPoly.coeff k * a ^ k * b ^ (2 * g - k) := by
  simp [homPoly, eval_finsetSum]

theorem homPoly_natDegree_le (a : ℚ) : (D.homPoly a).natDegree ≤ 2 * g := by
  unfold homPoly
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

theorem homPoly_eval_zero (a : ℚ) : (D.homPoly a).eval 0 = D.charPoly.coeff (2 * g) * a ^ (2 * g) := by
  rw [homPoly_eval, Finset.sum_eq_single (2 * g)]
  · simp
  · intro k hk hne
    have : 2 * g - k ≠ 0 := by
      have := Finset.mem_range.mp hk; omega
    simp [zero_pow this]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

theorem homPoly_eval_mul (b n : ℚ) :
    (D.homPoly (b * n)).eval b = b ^ (2 * g) * D.charPoly.eval n := by
  rw [homPoly_eval, eval_eq_sum_range' (n := 2 * g + 1) (Nat.lt_succ_of_le D.charPoly_natDegree_le),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ 2 * g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have : b ^ (2 * g) = b ^ k * b ^ (2 * g - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [this, mul_pow]; ring

theorem charPoly_coeff_top : D.charPoly.coeff (2 * g) = 1 := by
  set a : ℤ := 2 ^ (2 * g) with ha
  set T : ℚ[X] := D.polyOf (-X) (a : ℤ[X]) with hT
  have hTeval : ∀ b : ℤ, T.eval (b : ℚ) = (D.deg ((a : ℤ[X]) - (b : ℤ[X]) * X) : ℚ) := by
    intro b
    rw [hT, polyOf_eval]
    congr 2
    rw [zsmul_eq_mul]; ring
  have hTV : T = D.homPoly (a : ℚ) := by
    apply eq_of_degree_sub_lt_of_eval_finset_eq ((range (2 * g + 1)).image fun j => ((2 : ℚ) ^ j))
    · rw [Finset.card_image_of_injective _ (pow_right_injective₀ (by norm_num) (by norm_num))]
      rw [card_range]
      refine (degree_sub_le _ _).trans_lt ?_
      refine max_lt ?_ ?_
      · exact (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr (D.polyOf_natDegree_le _ _))).trans_lt
          (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))
      · exact (degree_le_natDegree.trans (WithBot.coe_le_coe.mpr (D.homPoly_natDegree_le _))).trans_lt
          (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hj' : j ≤ 2 * g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hab : a = 2 ^ j * 2 ^ (2 * g - j) := by rw [ha, ← pow_add, Nat.add_sub_cancel' hj']
      have h1 := hTeval (2 ^ j)
      have h2 := D.deg_mul_sub (2 ^ j) (2 ^ (2 * g - j))
      rw [← hab] at h2
      push_cast at h1 h2
      rw [h1, h2, show ((a : ℤ) : ℚ) = (2 : ℚ) ^ j * 2 ^ (2 * g - j) by rw [hab]; push_cast; ring,
        homPoly_eval_mul]
  have h0 := congrArg (fun P : ℚ[X] => P.eval 0) hTV
  rw [homPoly_eval_zero, show (0 : ℚ) = ((0 : ℤ) : ℚ) by simp, hTeval] at h0
  simp only [Int.cast_zero, zero_mul, sub_zero] at h0
  rw [D.deg_intCast, natAbs_pow_cast] at h0
  have hane : ((a : ℤ) : ℚ) ^ (2 * g) ≠ 0 := pow_ne_zero _ (by rw [ha]; positivity)
  have := mul_right_cancel₀ hane (h0.symm.trans (one_mul _).symm)
  exact this

theorem charPoly_natDegree : D.charPoly.natDegree = 2 * g :=
  le_antisymm D.charPoly_natDegree_le
    (le_natDegree_of_ne_zero (by rw [D.charPoly_coeff_top]; exact one_ne_zero))

theorem charPoly_monic : D.charPoly.Monic := by
  rw [Monic, leadingCoeff, D.charPoly_natDegree, D.charPoly_coeff_top]

section Roots

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

omit [IsAlgClosed K] in
theorem eval_map_algebraMap_intCast (Q : ℚ[X]) (s : ℤ) :
    (Q.map (algebraMap ℚ K)).eval (s : K) = algebraMap ℚ K (Q.eval (s : ℚ)) := by
  rw [← map_intCast (algebraMap ℚ K) s, eval_map, eval₂_at_apply]

omit [CharZero K] [IsAlgClosed K] in
theorem eval_map_intCast (F : ℤ[X]) (s : ℤ) :
    (F.map (Int.castRingHom K)).eval (s : K) = ((F.eval s : ℤ) : K) := by
  rw [show (s : K) = Int.castRingHom K s by simp, eval_map, eval₂_at_apply]; simp

theorem charPoly_map_eval (x : K) :
    (D.charPoly.map (algebraMap ℚ K)).eval x =
      ((D.charPoly.map (algebraMap ℚ K)).roots.map fun a => x - a).prod := by
  have hm : (D.charPoly.map (algebraMap ℚ K)).Monic := D.charPoly_monic.map _
  have hc : Multiset.card (D.charPoly.map (algebraMap ℚ K)).roots =
      (D.charPoly.map (algebraMap ℚ K)).natDegree := IsAlgClosed.card_roots_eq_natDegree
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc]
  rw [eval_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp

theorem card_roots_charPoly : Multiset.card (D.charPoly.map (algebraMap ℚ K)).roots = 2 * g := by
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map, D.charPoly_natDegree]

/-- Milne Lemma 10.22 for `ℤ[π]`: `deg F = ∏_{a ∈ roots P_π} F(a)` in any algebraically closed `K ⊇ ℚ`. -/
theorem deg_eq_prod_roots (F : ℤ[X]) :
    (D.deg F : K) = ((D.charPoly.map (algebraMap ℚ K)).roots.map
      fun a => (F.map (Int.castRingHom K)).eval a).prod := by
  induction hd : F.natDegree using Nat.strong_induction_on generalizing F with
  | _ d IH =>
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0] at hd
    rw [eq_C_of_natDegree_eq_zero hd]
    have h := D.deg_C_mul (F.coeff 0) 1
    rw [mul_one, D.deg_one, mul_one] at h
    rw [h, natAbs_pow_cast]
    simp only [Polynomial.map_C, eval_C, Multiset.map_const', Multiset.prod_replicate,
      D.card_roots_charPoly, Int.coe_castRingHom]
  · have hinj : Function.Injective (Int.castRingHom K) := Int.cast_injective
    set FK := F.map (Int.castRingHom K) with hFK
    set PK := D.charPoly.map (algebraMap ℚ K) with hPK
    set R := D.polyOf 1 F with hR
    have key : ∀ s : ℤ, (R.map (algebraMap ℚ K)).eval (((-(F.eval s) : ℤ)) : K) =
        (PK.roots.map fun a => FK.eval (s : K) - FK.eval a).prod := by
      intro s
      set G := (F - C (F.eval s)) /ₘ (X - C s) with hGdef
      have hG : (X - C s) * G = F - C (F.eval s) :=
        mul_divByMonic_eq_iff_isRoot.mpr (by simp [IsRoot])
      have hGdeg : G.natDegree < d := by
        rw [hGdef, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_sub_C, natDegree_X_sub_C, hd]
        omega
      have IHG := IH _ hGdeg G rfl
      have h1 : (D.deg (F - C (F.eval s)) : ℚ) = R.eval ((-(F.eval s) : ℤ) : ℚ) := by
        rw [hR, polyOf_eval, zsmul_one, Int.cast_neg, sub_eq_add_neg, add_comm, eq_intCast C]
      have hneg : -(X - C s) = ((s : ℤ[X]) - X) := by rw [eq_intCast C]; ring
      have h2 : D.deg (F - C (F.eval s)) = D.deg ((s : ℤ[X]) - X) * D.deg G := by
        rw [← hG, D.deg_mul, ← hneg, D.deg_neg]
      have h3 : (D.deg ((s : ℤ[X]) - X) : K) = PK.eval (s : K) := by
        rw [hPK, eval_map_algebraMap_intCast, charPoly_eval, map_natCast]
      have hGa : ∀ a : K, (s - a) * (G.map (Int.castRingHom K)).eval a = FK.eval (s : K) - FK.eval a := by
        intro a
        have := congrArg (fun P : ℤ[X] => (P.map (Int.castRingHom K)).eval a) hG
        simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C, eval_mul, eval_sub, eval_X,
          eval_C] at this
        rw [hFK, eval_map_intCast]
        simp only [eq_intCast] at this ⊢
        linear_combination -this
      rw [eval_map_algebraMap_intCast, ← h1, map_natCast, h2, Nat.cast_mul, h3, IHG, charPoly_map_eval,
        ← Multiset.prod_map_mul]
      congr 1
      exact Multiset.map_congr rfl fun a _ => hGa a
    have hpoly : (R.map (algebraMap ℚ K)).comp (-FK) =
        (PK.roots.map fun a => FK - C (FK.eval a)).prod := by
      apply eq_of_infinite_eval_eq
      apply Set.Infinite.mono _ (Set.infinite_range_of_injective (Int.cast_injective (α := K)))
      rintro _ ⟨s, rfl⟩
      simp only [Set.mem_setOf_eq, eval_comp, eval_neg, eval_multiset_prod, Multiset.map_map,
        Function.comp_def, eval_sub, eval_C]
      rw [hFK, eval_map_intCast, ← Int.cast_neg, key s, eval_map_intCast]
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root FK (by
      rw [hFK, degree_map_eq_of_injective hinj, degree_eq_natDegree (by rintro rfl; simp at hd; omega), hd]
      exact_mod_cast hpos.ne')
    have hc' := congrArg (eval c) hpoly
    simp only [eval_comp, eval_neg, hc.eq_zero, neg_zero, eval_multiset_prod, Multiset.map_map,
      Function.comp_def, eval_sub, eval_C, zero_sub] at hc'
    rw [show (PK.roots.map fun x => -eval x FK) = (PK.roots.map fun x => eval x FK).map Neg.neg by
      rw [Multiset.map_map]; rfl, Multiset.prod_map_neg, Multiset.card_map, D.card_roots_charPoly, pow_mul,
      neg_one_sq, one_pow, one_mul] at hc'
    rw [← hc', show (0 : K) = ((0 : ℤ) : K) by simp, eval_map_algebraMap_intCast, hR, polyOf_eval,
      zero_smul, zero_add, map_natCast]

end Roots

end DegreeData

end RamanujanPetersson.JacAlg


end

-- ===== S4.Def_RP_JacAlg_Multiset =====
section

/-!
# Core B algebra, part 3: the multiset lemma with RH (A6, L7)

If `∏_{a ∈ A} (1 - a^m) = ∏_{b ∈ B} (1 - b^m)` for every `m ≥ 1`, the `a` are nonzero and every `b`
has `‖b‖ = r > 1`, then `A = B` (`multiset_eq_of_prod_one_sub_pow`; RH enters as `‖b‖ = r`).

Method (group rings, no analysis): put `onePoly Y = ∏_{y ∈ Y} (1 - [y])` in `ℤ[H]`.
1. `onePoly_eq_of_prod_eq`: the identity for all `m ≥ 1` gives `onePoly A = onePoly B` in `ℤ[ℂˣ]`
   (S3-ExpSum's exponential-polynomial uniqueness).
2. Push to `ℤ[Multiplicative ℝ]` along `z ↦ log ‖z‖` (a domain): `eq_replicate_of_onePoly_eq` shows
   `∏ (1 - [y]) = (1 - [c])^n` with `c > 0` forces `Y = {c, ..., c}` (lowest-term arguments
   `onePoly_coeff_inf`, `onePoly_coeff_of_lt`, then cancel one factor and induct).
3. So `‖a‖ = r` for all `a`, and the coefficients at `‖t‖ = r` are `-count t A = -count t B`.
Without RH this fails: `{2, 3, 5, 1/30}` and `{1/2, 1/3, 1/5, 30}`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open MonoidAlgebra

section Graded

variable {H : Type*} [CommGroup H] [DecidableEq H]

/-- `∏_{y ∈ Y} (1 - [y])` in the group ring `ℤ[H]`. -/
noncomputable def onePoly (Y : Multiset H) : MonoidAlgebra ℤ H :=
  (Y.map fun y => (1 - MonoidAlgebra.single y (1 : ℤ))).prod

omit [DecidableEq H] in
theorem onePoly_zero : onePoly (0 : Multiset H) = 1 := by simp [onePoly]

omit [DecidableEq H] in
theorem onePoly_cons (y : H) (Y : Multiset H) :
    onePoly (y ::ₘ Y) = (1 - MonoidAlgebra.single y (1 : ℤ)) * onePoly Y := by
  simp [onePoly]

theorem coeff_one_apply (t : H) : (1 : MonoidAlgebra ℤ H).coeff t = if t = 1 then 1 else 0 := by
  rw [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp only [eq_comm]

omit [DecidableEq H] in
theorem coeff_one_sub_mul (y t : H) (P : MonoidAlgebra ℤ H) :
    ((1 - MonoidAlgebra.single y (1 : ℤ)) * P).coeff t = P.coeff t - P.coeff (y⁻¹ * t) := by
  rw [sub_mul, one_mul, MonoidAlgebra.coeff_sub, Finsupp.sub_apply,
    MonoidAlgebra.coeff_single_mul_apply, one_mul]

variable (φ : H → ℝ) (hφ : ∀ x y, φ (x * y) = φ x + φ y)
include hφ

omit [DecidableEq H] in
theorem grade_one : φ 1 = 0 := by
  have := hφ 1 1
  rw [one_mul] at this
  linarith

omit [DecidableEq H] in
theorem grade_inv_mul (y t : H) : φ (y⁻¹ * t) = φ t - φ y := by
  have := hφ y (y⁻¹ * t)
  rw [mul_inv_cancel_left] at this
  linarith

/-- Lowest terms when every `φ y ≥ μ > 0`: below `μ` only the constant `1`, at height `μ` the
coefficient of `t` is `-count t Y`. -/
theorem onePoly_coeff_of_lt {μ : ℝ} (hμ : 0 < μ) (Y : Multiset H) (hY : ∀ y ∈ Y, μ ≤ φ y) :
    (∀ t, φ t < μ → (onePoly Y).coeff t = if t = 1 then 1 else 0) ∧
    (∀ t, φ t = μ → (onePoly Y).coeff t = -(Y.count t : ℤ)) := by
  induction Y using Multiset.induction_on with
  | empty =>
    refine ⟨fun t _ => by rw [onePoly_zero, coeff_one_apply], fun t ht => ?_⟩
    have h1 : t ≠ 1 := by
      intro h
      rw [h, grade_one φ hφ] at ht
      linarith
    simp [onePoly_zero, coeff_one_apply, h1]
  | cons y Y ih =>
    have hy := hY y (Multiset.mem_cons.2 (Or.inl rfl))
    obtain ⟨ih1, ih2⟩ := ih (fun z hz => hY z (Multiset.mem_cons_of_mem hz))
    rw [onePoly_cons]
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have hne : y⁻¹ * t ≠ 1 := by
        intro h
        have := congrArg φ h
        rw [grade_inv_mul φ hφ, grade_one φ hφ] at this
        linarith
      rw [coeff_one_sub_mul, ih1 t ht,
        ih1 (y⁻¹ * t) (by rw [grade_inv_mul φ hφ]; linarith), if_neg hne, sub_zero]
    · rw [coeff_one_sub_mul, ih2 t ht, ih1 (y⁻¹ * t) (by rw [grade_inv_mul φ hφ]; linarith),
        Multiset.count_cons]
      by_cases h : t = y
      · subst h
        simp only [inv_mul_cancel, if_true]
        push_cast
        ring
      · have hne : y⁻¹ * t ≠ 1 := by
          rw [ne_eq, inv_mul_eq_one]
          exact fun h' => h h'.symm
        simp [h, hne]

/-- The lowest term of `onePoly Y` when no `φ y` is `0`: it sits at height `σ ≤ 0`, and `σ = 0`
only when every `φ y > 0`. -/
theorem onePoly_coeff_inf (Y : Multiset H) (hY : ∀ y ∈ Y, φ y ≠ 0) :
    ∃ σ : ℝ, σ ≤ 0 ∧ (σ = 0 → ∀ y ∈ Y, 0 < φ y) ∧ (∃ t, φ t = σ ∧ (onePoly Y).coeff t ≠ 0) ∧
      ∀ t, φ t < σ → (onePoly Y).coeff t = 0 := by
  induction Y using Multiset.induction_on with
  | empty =>
    refine ⟨0, le_rfl, fun _ y hy => by simp at hy, ⟨1, grade_one φ hφ, ?_⟩, fun t ht => ?_⟩
    · simp [onePoly_zero]
    · have h1 : t ≠ 1 := by
        intro h
        rw [h, grade_one φ hφ] at ht
        exact lt_irrefl _ ht
      simp [onePoly_zero, coeff_one_apply, h1]
  | cons y Y ih =>
    obtain ⟨σ, hσ, h0, ⟨t₀, ht₀, hc⟩, hlow⟩ :=
      ih (fun z hz => hY z (Multiset.mem_cons_of_mem hz))
    rcases lt_or_gt_of_ne (hY y (Multiset.mem_cons.2 (Or.inl rfl))) with hneg | hpos
    · refine ⟨φ y + σ, by linarith, fun h => by linarith, ⟨y * t₀, by rw [hφ, ht₀], ?_⟩,
        fun t ht => ?_⟩
      · rw [onePoly_cons, coeff_one_sub_mul, inv_mul_cancel_left,
          hlow (y * t₀) (by rw [hφ, ht₀]; linarith), zero_sub, neg_ne_zero]
        exact hc
      · rw [onePoly_cons, coeff_one_sub_mul, hlow t (by linarith),
          hlow (y⁻¹ * t) (by rw [grade_inv_mul φ hφ]; linarith), sub_zero]
    · refine ⟨σ, hσ, fun h z hz => ?_, ⟨t₀, ht₀, ?_⟩, fun t ht => ?_⟩
      · rcases Multiset.mem_cons.1 hz with rfl | hz
        · exact hpos
        · exact h0 h z hz
      · rw [onePoly_cons, coeff_one_sub_mul,
          hlow (y⁻¹ * t₀) (by rw [grade_inv_mul φ hφ, ht₀]; linarith), sub_zero]
        exact hc
      · rw [onePoly_cons, coeff_one_sub_mul, hlow t ht,
          hlow (y⁻¹ * t) (by rw [grade_inv_mul φ hφ]; linarith), sub_zero]

end Graded

/-! ### Step 2: in `ℤ[Multiplicative ℝ]`, `∏ (1 - [y]) = (1 - [c])^n` forces `Y = {c, ..., c}` -/

section Real

theorem toAdd_hom : ∀ x y : (Multiplicative ℝ), Multiplicative.toAdd (x * y) =
    Multiplicative.toAdd x + Multiplicative.toAdd y := fun _ _ => rfl

theorem one_sub_single_ne_zero (c : (Multiplicative ℝ)) (hc : c ≠ 1) :
    (1 - MonoidAlgebra.single c (1 : ℤ) : MonoidAlgebra ℤ (Multiplicative ℝ)) ≠ 0 := by
  intro h
  have := congrArg (fun f : MonoidAlgebra ℤ (Multiplicative ℝ) => f.coeff 1) h
  simp [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single,
    hc] at this

theorem rep_coeff_of_lt {c : (Multiplicative ℝ)} (hc : 0 < Multiplicative.toAdd c) (n : ℕ) (t : (Multiplicative ℝ))
    (ht : Multiplicative.toAdd t < Multiplicative.toAdd c) :
    (onePoly (Multiset.replicate n c)).coeff t = if t = 1 then 1 else 0 :=
  (onePoly_coeff_of_lt _ toAdd_hom hc _
    (fun y hy => by rw [Multiset.eq_of_mem_replicate hy])).1 t ht

theorem rep_coeff_self {c : (Multiplicative ℝ)} (hc : 0 < Multiplicative.toAdd c) (n : ℕ) :
    (onePoly (Multiset.replicate n c)).coeff c = -(n : ℤ) := by
  rw [(onePoly_coeff_of_lt _ toAdd_hom hc _
    (fun y hy => by rw [Multiset.eq_of_mem_replicate hy])).2 c rfl, Multiset.count_replicate_self]

theorem ne_one_of_toAdd_ne {t : (Multiplicative ℝ)} (ht : Multiplicative.toAdd t ≠ 0) : t ≠ 1 := by
  rintro rfl
  exact ht rfl

theorem eq_replicate_of_onePoly_eq {c : (Multiplicative ℝ)} (hc : 0 < Multiplicative.toAdd c) :
    ∀ (k : ℕ) (Y : Multiset (Multiplicative ℝ)) (n : ℕ), Multiset.card Y = k →
      onePoly Y = onePoly (Multiset.replicate n c) → Y = Multiset.replicate n c := by
  have hc1 : c ≠ 1 := ne_one_of_toAdd_ne hc.ne'
  intro k
  induction k with
  | zero =>
    intro Y n hk h
    rw [Multiset.card_eq_zero] at hk
    subst hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · exfalso
      have e := rep_coeff_self hc n
      rw [← h, onePoly_zero, coeff_one_apply, if_neg hc1] at e
      omega
  | succ k ih =>
    intro Y n hk h
    have hY0 : ∀ y ∈ Y, Multiplicative.toAdd y ≠ 0 := by
      intro y hy hy0
      have hy1 : y = 1 := by rw [← ofAdd_toAdd y, hy0, ofAdd_zero]
      have h0 : onePoly Y = 0 := by
        unfold onePoly
        apply Multiset.prod_eq_zero
        rw [Multiset.mem_map]
        refine ⟨y, hy, ?_⟩
        show (1 : MonoidAlgebra ℤ (Multiplicative ℝ)) - MonoidAlgebra.single y 1 = 0
        rw [hy1, ← MonoidAlgebra.one_def, sub_self]
      have e := rep_coeff_of_lt hc n 1 (by simpa using hc)
      rw [← h, h0, if_pos rfl] at e
      simp at e
    have hpos : ∀ y ∈ Y, 0 < Multiplicative.toAdd y := by
      obtain ⟨σ, hσ, h0, ⟨t₀, ht₀, hcoef⟩, -⟩ := onePoly_coeff_inf _ toAdd_hom Y hY0
      rcases hσ.lt_or_eq with hlt | heq
      · exfalso
        have ht1 : t₀ ≠ 1 := ne_one_of_toAdd_ne (by rw [ht₀]; exact hlt.ne)
        have e := rep_coeff_of_lt hc n t₀ (by rw [ht₀]; linarith)
        rw [← h, if_neg ht1] at e
        exact hcoef e
      · exact h0 heq
    have hYne : Y ≠ 0 := by
      intro h0
      rw [h0] at hk
      simp at hk
    obtain ⟨y₀, hy₀, hmin⟩ := Finset.exists_min_image Y.toFinset Multiplicative.toAdd
      (Multiset.toFinset_nonempty.2 hYne)
    rw [Multiset.mem_toFinset] at hy₀
    have hμ := hpos y₀ hy₀
    obtain ⟨hY1, hY2⟩ := onePoly_coeff_of_lt _ toAdd_hom hμ Y
      (fun y hy => hmin y (Multiset.mem_toFinset.2 hy))
    have hy₀c : (onePoly Y).coeff y₀ ≠ 0 := by
      rw [hY2 y₀ rfl, neg_ne_zero, Nat.cast_ne_zero]
      exact Multiset.count_ne_zero.2 hy₀
    have hy₀1 : y₀ ≠ 1 := ne_one_of_toAdd_ne hμ.ne'
    rcases lt_trichotomy (Multiplicative.toAdd y₀) (Multiplicative.toAdd c) with hlt | heq | hgt
    · exfalso
      apply hy₀c
      rw [h, rep_coeff_of_lt hc n y₀ hlt, if_neg hy₀1]
    · have hyc : y₀ = c := Multiplicative.toAdd.injective heq
      subst hyc
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
        rcases n with _ | n'
        · exfalso
          apply hy₀c
          rw [h, rep_coeff_self hc 0]
          simp
        · exact ⟨n', rfl⟩
      have hYe := Multiset.cons_erase hy₀
      rw [← hYe, onePoly_cons, Multiset.replicate_succ, onePoly_cons] at h
      have h' := mul_left_cancel₀ (one_sub_single_ne_zero _ hc1) h
      have hcard : Multiset.card (Y.erase y₀) = k := by
        rw [Multiset.card_erase_of_mem hy₀, hk]
        rfl
      rw [← hYe, ih _ _ hcard h', Multiset.replicate_succ]
    · exfalso
      have h1 := hY1 c hgt
      rw [h, rep_coeff_self hc n, if_neg hc1, neg_eq_zero, Nat.cast_eq_zero] at h1
      subst h1
      apply hy₀c
      rw [h, Multiset.replicate_zero, onePoly_zero, coeff_one_apply, if_neg hy₀1]

end Real

/-! ### Steps 1 and 3: from `ℂ` to the group rings and back -/

section Complex

/-- Evaluation `[z] ↦ z^m` on `ℤ[ℂˣ]`. -/
noncomputable def evPow (m : ℕ) : MonoidAlgebra ℤ ℂˣ →ₐ[ℤ] ℂ :=
  MonoidAlgebra.lift ℤ ℂ ℂˣ ((powMonoidHom m).comp (Units.coeHom ℂ))

theorem evPow_onePoly (m : ℕ) (Y : Multiset ℂˣ) :
    evPow m (onePoly Y) = (Y.map fun y : ℂˣ => 1 - (y : ℂ) ^ m).prod := by
  rw [onePoly, map_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro y _
  simp [evPow, MonoidAlgebra.lift_single]

theorem evPow_apply (m : ℕ) (f : MonoidAlgebra ℤ ℂˣ) :
    evPow m f = ∑ w ∈ f.coeff.support, (f.coeff w : ℂ) * (w : ℂ) ^ m := by
  rw [evPow, MonoidAlgebra.lift_apply', Finsupp.sum]
  simp

theorem eq_zero_of_evPow (f : MonoidAlgebra ℤ ℂˣ) (h : ∀ m : ℕ, 1 ≤ m → evPow m f = 0) :
    f = 0 := by
  classical
  let cf : ℂ → ℂ := fun z => if hz : z = 0 then 0 else (f.coeff (Units.mk0 z hz) : ℂ)
  have hcf : ∀ w : ℂˣ, cf w = (f.coeff w : ℂ) := fun w => by simp [cf, w.ne_zero]
  have key := RamanujanPetersson.ExpSum.expSum_coeff_eq_zero_of_ne_zero
    (f.coeff.support.map ⟨Units.val, Units.val_injective⟩) cf (fun m hm => by
      rw [Finset.sum_map]
      simp only [Function.Embedding.coeFn_mk, hcf]
      rw [← evPow_apply]
      exact h m hm)
  rw [← MonoidAlgebra.coeff_eq_zero]
  ext w
  by_contra hw
  have e := key (w : ℂ) (Finset.mem_map_of_mem _ (Finsupp.mem_support_iff.2 hw)) w.ne_zero
  rw [hcf, Int.cast_eq_zero] at e
  exact hw e

/-- Step 1: the identity for all `m ≥ 1` is an identity in `ℤ[ℂˣ]`. -/
theorem onePoly_eq_of_prod_eq (A B : Multiset ℂˣ)
    (h : ∀ m : ℕ, 1 ≤ m →
      (A.map fun a : ℂˣ => 1 - (a : ℂ) ^ m).prod = (B.map fun b : ℂˣ => 1 - (b : ℂ) ^ m).prod) :
    onePoly A = onePoly B := by
  rw [← sub_eq_zero]
  apply eq_zero_of_evPow
  intro m hm
  rw [map_sub, evPow_onePoly, evPow_onePoly, h m hm, sub_self]

/-- `z ↦ log ‖z‖` as a hom `ℂˣ →* Multiplicative ℝ`. -/
noncomputable def logNorm : ℂˣ →* Multiplicative ℝ where
  toFun z := Multiplicative.ofAdd (Real.log ‖(z : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero), ofAdd_add]

theorem logNorm_hom (x y : ℂˣ) :
    Real.log ‖((x * y : ℂˣ) : ℂ)‖ = Real.log ‖(x : ℂ)‖ + Real.log ‖(y : ℂ)‖ := by
  rw [Units.val_mul, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 x.ne_zero) (norm_ne_zero_iff.2 y.ne_zero)]

theorem mapDomain_onePoly (Y : Multiset ℂˣ) :
    MonoidAlgebra.mapDomainRingHom ℤ logNorm (onePoly Y) = onePoly (Y.map logNorm) := by
  rw [onePoly, onePoly, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro y _
  simp only [Function.comp_apply, map_sub, map_one]
  congr 1
  exact MonoidAlgebra.mapDomain_single

/-- **A6 over `ℂˣ`.** -/
theorem units_multiset_eq (A B : Multiset ℂˣ) {r : ℝ} (hr : 1 < r)
    (hB : ∀ b ∈ B, ‖(b : ℂ)‖ = r)
    (h : ∀ m : ℕ, 1 ≤ m →
      (A.map fun a : ℂˣ => 1 - (a : ℂ) ^ m).prod = (B.map fun b : ℂˣ => 1 - (b : ℂ) ^ m).prod) :
    A = B := by
  have h1 := onePoly_eq_of_prod_eq A B h
  have hμ : 0 < Real.log r := Real.log_pos hr
  have hc : 0 < Multiplicative.toAdd (Multiplicative.ofAdd (Real.log r)) := hμ
  have hBc : B.map logNorm =
      Multiset.replicate (Multiset.card B) (Multiplicative.ofAdd (Real.log r)) := by
    rw [Multiset.eq_replicate]
    refine ⟨Multiset.card_map _ _, fun x hx => ?_⟩
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    show Multiplicative.ofAdd (Real.log ‖(b : ℂ)‖) = _
    rw [hB b hb]
  have h2 : onePoly (A.map logNorm) =
      onePoly (Multiset.replicate (Multiset.card B) (Multiplicative.ofAdd (Real.log r))) := by
    rw [← hBc, ← mapDomain_onePoly, ← mapDomain_onePoly, h1]
  have hA := eq_replicate_of_onePoly_eq hc _ _ _ rfl h2
  have hAeq : ∀ a ∈ A, Real.log ‖(a : ℂ)‖ = Real.log r := by
    intro a ha
    have e := Multiset.eq_of_mem_replicate (hA ▸ Multiset.mem_map_of_mem logNorm ha)
    exact congrArg Multiplicative.toAdd e
  have hBeq : ∀ b ∈ B, Real.log ‖(b : ℂ)‖ = Real.log r := fun b hb => by rw [hB b hb]
  ext t
  by_cases ht : Real.log ‖(t : ℂ)‖ = Real.log r
  · have eA := (onePoly_coeff_of_lt (fun z : ℂˣ => Real.log ‖(z : ℂ)‖) logNorm_hom hμ A
      (fun a ha => (hAeq a ha).ge)).2 t ht
    have eB := (onePoly_coeff_of_lt (fun z : ℂˣ => Real.log ‖(z : ℂ)‖) logNorm_hom hμ B
      (fun b hb => (hBeq b hb).ge)).2 t ht
    rw [h1, eB, neg_inj, Nat.cast_inj] at eA
    exact eA.symm
  · rw [Multiset.count_eq_zero.2 (fun ht' => ht (hAeq t ht')),
      Multiset.count_eq_zero.2 (fun ht' => ht (hBeq t ht'))]

/-- **A6 (L7), the multiset lemma with RH.** If `∏_{a ∈ A} (1 - a^m) = ∏_{b ∈ B} (1 - b^m)` for all
`m ≥ 1`, `0 ∉ A` and `‖b‖ = r > 1` for every `b ∈ B`, then `A = B`. -/
theorem multiset_eq_of_prod_one_sub_pow (A B : Multiset ℂ) {r : ℝ} (hr : 1 < r)
    (hA : (0 : ℂ) ∉ A) (hB : ∀ b ∈ B, ‖b‖ = r)
    (h : ∀ m : ℕ, 1 ≤ m → (A.map fun a => 1 - a ^ m).prod = (B.map fun b => 1 - b ^ m).prod) :
    A = B := by
  classical
  let u : ℂ → ℂˣ := fun z => if hz : z = 0 then 1 else Units.mk0 z hz
  have hu : ∀ S : Multiset ℂ, (0 : ℂ) ∉ S → (S.map u).map (fun w : ℂˣ => (w : ℂ)) = S := by
    intro S hS
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id S]
    apply Multiset.map_congr rfl
    intro z hz
    have hz0 : z ≠ 0 := fun h0 => hS (h0 ▸ hz)
    simp [u, hz0]
  have hB0 : (0 : ℂ) ∉ B := by
    intro h0
    have e := hB 0 h0
    rw [norm_zero] at e
    linarith
  have hprod : ∀ S : Multiset ℂ, (0 : ℂ) ∉ S → ∀ m : ℕ,
      ((S.map u).map fun a : ℂˣ => 1 - (a : ℂ) ^ m).prod = (S.map fun a => 1 - a ^ m).prod := by
    intro S hS m
    rw [Multiset.map_map]
    conv_rhs => rw [← hu S hS, Multiset.map_map, Multiset.map_map]
    rfl
  have key := units_multiset_eq (A.map u) (B.map u) hr
    (fun b hb => by
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hb
      have hz0 : z ≠ 0 := fun h0 => hB0 (h0 ▸ hz)
      simp [u, hz0, hB z hz])
    (fun m hm => by rw [hprod A hA, hprod B hB0]; exact h m hm)
  rw [← hu A hA, ← hu B hB0, key]

/-- The same with `‖b‖ = √q`, `q > 1` (the RH shape of S3-ZetaSB). -/
theorem multiset_eq_of_prod_one_sub_pow_sqrt (A B : Multiset ℂ) {q : ℝ} (hq : 1 < q)
    (hA : (0 : ℂ) ∉ A) (hB : ∀ b ∈ B, ‖b‖ = Real.sqrt q)
    (h : ∀ m : ℕ, 1 ≤ m → (A.map fun a => 1 - a ^ m).prod = (B.map fun b => 1 - b ^ m).prod) :
    A = B := by
  refine multiset_eq_of_prod_one_sub_pow A B ?_ hA hB h
  rw [← Real.sqrt_one]
  exact Real.sqrt_lt_sqrt zero_le_one hq

end Complex

end RamanujanPetersson.JacAlg


end

-- ===== S4.Def_RP_JacAlg_Zeta =====
section

/-!
# Core B algebra, part 4: the zeta link (A5) and the roots of `P_π` (A6 applied)

* `deg_one_sub_X_pow`: `deg(1 - π^m) = ∏_j (1 - a_j^m)` over the roots `a_j` of `P_π` (A5).
* `card_ker_one_sub_X_pow`: `#Ker(1 - π^m) = deg(1 - π^m)` (D3, `p ∤ 1`).
* `roots_charPoly_eq`, `charPoly_map_eq_prod`: with `h_m = ∏_i (1 - ω_i^m)` and RH `|ω_i| = √q`, the complex
  roots of `P_π` are the `ω_i` and `P_π = ∏_i (X - ω_i)` (A6 via `multiset_eq_of_prod_one_sub_pow_sqrt`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

section Roots

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- A5: `deg(1 - π^m) = ∏_j (1 - a_j^m)` over the roots `a_j` of `P_π` in `K`. -/
theorem deg_one_sub_X_pow (m : ℕ) :
    (D.deg (1 - X ^ m) : K) =
      ((D.charPoly.map (algebraMap ℚ K)).roots.map fun a => 1 - a ^ m).prod := by
  rw [D.deg_eq_prod_roots]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp

/-- `deg π = ∏_j a_j`. -/
theorem deg_X_eq_prod_roots :
    (D.deg X : K) = (D.charPoly.map (algebraMap ℚ K)).roots.prod := by
  rw [D.deg_eq_prod_roots]
  congr 1
  conv_rhs => rw [← Multiset.map_id (D.charPoly.map (algebraMap ℚ K)).roots]
  apply Multiset.map_congr rfl
  intro a _
  simp

/-- If `π` is injective, `0` is not a root of `P_π`. -/
theorem zero_not_mem_roots (hπ : Function.Injective π) :
    (0 : K) ∉ (D.charPoly.map (algebraMap ℚ K)).roots := by
  intro h0
  have h := D.deg_X_eq_prod_roots (K := K)
  rw [Multiset.prod_eq_zero h0, Nat.cast_eq_zero] at h
  exact D.deg_X_ne_zero hπ h

end Roots

/-- (D3) for `1 - π^m`: `deg(1 - π^m) = #Ker(1 - π^m)` (here `p ≠ 1`, so `p ∤ 1`). -/
theorem card_ker_one_sub_X_pow (hp : p ≠ 1) (m : ℕ) (hm : 1 ≤ m) :
    D.deg (1 - X ^ m) = Nat.card (LinearMap.ker (aeval π (1 - X ^ m : ℤ[X]))) := by
  refine D.deg_eq_card_ker _ ?_
  rw [coeff_sub, coeff_one_zero, coeff_X_pow, if_neg (by omega), sub_zero]
  intro h
  exact hp (by exact_mod_cast Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h)

/-- A6 applied: if `deg(1 - π^m) = ∏_i (1 - ω_i^m)` for all `m ≥ 1`, `|ω_i| = √q` with `q > 1` (RH) and
`π` is injective, then the complex roots of `P_π` are exactly the `ω_i`. -/
theorem roots_charPoly_eq (hπ : Function.Injective π) {q : ℝ} (hq : 1 < q) (ω : Multiset ℂ)
    (hω : ∀ w ∈ ω, ‖w‖ = Real.sqrt q)
    (h : ∀ m : ℕ, 1 ≤ m → (D.deg (1 - X ^ m) : ℂ) = (ω.map fun w => 1 - w ^ m).prod) :
    (D.charPoly.map (algebraMap ℚ ℂ)).roots = ω :=
  multiset_eq_of_prod_one_sub_pow_sqrt _ ω hq (D.zero_not_mem_roots hπ) hω
    (fun m hm => by rw [← D.deg_one_sub_X_pow, h m hm])

/-- CB2 over `ℂ`: `P_π = ∏_i (X - ω_i)`. -/
theorem charPoly_map_eq_prod (hπ : Function.Injective π) {q : ℝ} (hq : 1 < q) (ω : Multiset ℂ)
    (hω : ∀ w ∈ ω, ‖w‖ = Real.sqrt q)
    (h : ∀ m : ℕ, 1 ≤ m → (D.deg (1 - X ^ m) : ℂ) = (ω.map fun w => 1 - w ^ m).prod) :
    D.charPoly.map (algebraMap ℚ ℂ) = (ω.map fun w => X - C w).prod := by
  rw [← D.roots_charPoly_eq hπ hq ω hω h]
  exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (D.charPoly_monic.map _)
    IsAlgClosed.card_roots_eq_natDegree).symm

end DegreeData

end RamanujanPetersson.JacAlg


end

-- ===== S4.Def_RP_JacAlg_Div =====
section

/-!
# Core B algebra, part 5: divisibility (unit S4-JacAlg, lemma L2 = route A1)

S4-CoreA writes `A[l^∞] ≃ (ℚ_l/ℤ_l)^s × Φ` with `Φ` finite and `l`-primary. Here `D` stands for the divisible
part and `Φ` for the finite part, both abstract:
* `card_tors_eq_mul`: `#(D × Φ)[n] = #D[n] * #Φ[n]` (through any `G ≃+ D × Φ`);
* `subsingleton_of_card_tors_eq`: if `#G[l] = #D[l]` (finite) and `Φ` is `l`-primary then `Φ = 0` (CB1);
* `DegreeData.card_tors`: `#A[n] = n^(2g)` for `p ∤ n` (the other half of A1, from (D2) + (D3)).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

/-- The `n`-torsion `G[n]` of an additive group, as a type. -/
abbrev Tors (G : Type*) [AddCommGroup G] (n : ℕ) : Type _ := {x : G // n • x = 0}

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

include D in
/-- `#A[n] = n^(2g)` for `p ∤ n` (A1, first half, as torsion of `A`). -/
theorem card_tors (n : ℕ) (hn : ¬ (p : ℤ) ∣ n) : Nat.card (Tors A n) = n ^ (2 * g) := by
  rw [← D.card_ker_natCast n hn]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1, (mem_ker_natCast (π := π) n x.1).mpr x.2⟩
      invFun := fun y => ⟨y.1, (mem_ker_natCast (π := π) n y.1).mp y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end DegreeData

end RamanujanPetersson.JacAlg


end

-- ===== S4.Def_RP_CoreB_Zeta =====
section

/-!
# Core B, O4: the zeta link

* `multiset_eq_of_powerSum_le`: `#c ≤ #ω`, `0 ∉ ω` and equal power sums force `c = ω`.
* `coe_piBar0_pow`, `card_ker_one_sub_X_pow_piBar0`: `ker (1 - π^m) = Pic⁰(X̄)^(π^m)`.
* `piBar0_injective`: the Frobenius is injective on `Pic⁰(X̄)`.
* `zeta_link D`: for degree data `D` on `ℤ[π]`, `gD = g` and `χ_D = P0` with `P0 ∈ ℤ[X]` the zeta polynomial
  `Π (X - ω_i)` (for any `c` with `#c ≤ 2g` and the point-count formula).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places

lemma multiset_eq_of_powerSum_le {c ω : Multiset ℂ} (hc : Multiset.card c ≤ Multiset.card ω) (h0 : (0 : ℂ) ∉ ω)
    (h : ∀ m : ℕ, 1 ≤ m → (c.map (· ^ m)).sum = (ω.map (· ^ m)).sum) : c = ω := by
  have hz : ∀ m : ℕ, 1 ≤ m → ((c.filter fun a => ¬ a ≠ 0).map (· ^ m)).sum = 0 := fun m hm => by
    refine Multiset.sum_eq_zero fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
    rw [not_not.1 (Multiset.mem_filter.1 hy).2]
    exact zero_pow (by omega)
  have hf : c.filter (· ≠ 0) = ω := by
    refine ExpSum.multiset_eq_of_powerSum_eq _ _ (fun h => (Multiset.mem_filter.1 h).2 rfl) h0 fun m hm => ?_
    rw [← h m hm]
    conv_rhs => rw [← Multiset.filter_add_not (· ≠ 0) c]
    rw [Multiset.map_add, Multiset.sum_add, hz m hm, add_zero]
  have hfc : c.filter (· ≠ 0) = c :=
    Multiset.eq_of_le_of_card_le (Multiset.filter_le _ c) (by rw [hf]; exact hc)
  exact hfc.symm.trans hf

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_CoreB_Div =====
section

/-!
# Core B, O5 (CB1): `Pic(X̄)[l^∞]` is `l`-divisible

* `not_ringChar_dvd`: `p ∤ l` for a prime `l ∤ q`.
* `torsEquiv`: `Aℓ[l] ≃ Pic⁰(X̄)[l]`.
* `divisible_Aℓ` (CB1): `#Pic⁰(X̄)[l] = l^(2g)` (degree data) and CoreA's `tate_rank_Pic` give divisibility.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.CoreA

theorem not_ringChar_dvd (Fq : Type*) [Field Fq] [Fintype Fq] (l : ℕ) [Fact l.Prime]
    (hlq : ¬ l ∣ Fintype.card Fq) : ¬ ((ringChar Fq : ℕ) : ℤ) ∣ (l : ℤ) := by
  intro h
  have h1 : ringChar Fq ∣ l := Int.natCast_dvd_natCast.1 h
  rcases (Nat.dvd_prime (Fact.out : l.Prime)).1 h1 with h2 | h2
  · exact CharP.ringChar_ne_one h2
  · apply hlq
    rw [← h2]
    exact (CharP.cast_eq_zero_iff Fq (ringChar Fq) _).1 (FiniteField.cast_card_eq_zero Fq)

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- `Aℓ[l] ≃ Pic⁰(X̄)[l]`. -/
noncomputable def torsEquiv (l : ℕ) [hl : Fact l.Prime] :
    {x : Aℓ Ω hk l // l • x = 0} ≃ Tors (PicBar0 Ω hk) l where
  toFun x := ⟨⟨x.1.1, primary_le_PicBar0 hk hl.out.ne_zero x.1.2⟩, by
    have h0 : l • (x.1.1 : PicBar Ω hk) = 0 := congrArg Subtype.val x.2
    ext; exact h0⟩
  invFun y := ⟨⟨y.1.1, by
      have h0 : l • (y.1.1 : PicBar Ω hk) = 0 := congrArg Subtype.val y.2
      exact AddCommGroup.mem_primaryComponent.2 ⟨1, by rw [pow_one]; exact h0⟩⟩, by
    have h0 : l • (y.1.1 : PicBar Ω hk) = 0 := congrArg Subtype.val y.2
    ext; exact h0⟩
  left_inv _ := rfl
  right_inv _ := rfl

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_CdOne_KumVal =====
section

/-!
# S4-PD (3)(iii)(K), part V: primes and valuations along finite levels `M ≤ L` of `K̄ / K`

`B_M = integralClosure A M` for an intermediate field `M` of `K̄ / K`.
* `underI h w`: the prime of `B_M` under a prime `w` of `B_L` (`h : M ≤ L`), `mem_underI`, `underI_trans`;
* `val_underI`: for `L ∈ unramSet A K` (unramified over `A`), `v_{under w}(x) = v_w(x)` for `x ∈ M`;
* `log_val_mul`, `finite_log_val_ne_zero`: additivity and finite support of `w ↦ log v_w(x)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IsDedekindDomain RamanujanPetersson.Kummer

noncomputable section

section Gen

variable {B F : Type*} [CommRing B] [IsDedekindDomain B] [Field F] [Algebra B F] [IsFractionRing B F]

theorem log_val_mul (w : HeightOneSpectrum B) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    WithZero.log (w.valuation F (x * y)) = WithZero.log (w.valuation F x) + WithZero.log (w.valuation F y) := by
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]

/-- `w ↦ log v_w(x)` has finite support. -/
theorem finite_log_val_ne_zero (x : F) :
    {w : HeightOneSpectrum B | WithZero.log (w.valuation F x) ≠ 0}.Finite := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  by_cases hn : n = 0
  · subst hn
    simp
  refine ((Ideal.finite_factors (I := Ideal.span {n}) (by simpa using hn)).union
    (Ideal.finite_factors (I := Ideal.span {d}) (by simpa using hd0))).subset ?_
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, Ideal.dvd_span_singleton] at hc
  apply hw
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.2 hc.1, HeightOneSpectrum.intValuation_eq_one_iff.2 hc.2,
    div_one, WithZero.log_one]

end Gen

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

/-- The prime of `B_M` under a prime of `B_L`, for `M ≤ L`. -/
def underI {M L : IntermediateField K (AlgebraicClosure K)} (h : M ≤ L)
    [IsDedekindDomain (integralClosure A M)] [IsDedekindDomain (integralClosure A L)]
    (w : HeightOneSpectrum (integralClosure A L)) : HeightOneSpectrum (integralClosure A M) where
  asIdeal := w.asIdeal.comap (incl A K h)
  isPrime := by
    have := w.isPrime
    exact Ideal.IsPrime.comap _
  ne_bot := by
    intro h0
    apply (w.under A).ne_bot
    change Ideal.comap (algebraMap A (integralClosure A L)) w.asIdeal = ⊥
    have hc : algebraMap A (integralClosure A L) =
        ((incl A K h : integralClosure A M →+* integralClosure A L)).comp (algebraMap A (integralClosure A M)) :=
      RingHom.ext fun a => ((incl A K h).commutes a).symm
    have h0' : Ideal.comap ((incl A K h : integralClosure A M →+* integralClosure A L)) w.asIdeal = ⊥ := h0
    rw [hc, ← Ideal.comap_comap, h0']
    exact Ideal.comap_bot_of_injective _ (algebraMap_integralClosure_injective A M)

variable {M M' L : IntermediateField K (AlgebraicClosure K)}

theorem mem_underI (h : M ≤ L) [IsDedekindDomain (integralClosure A M)] [IsDedekindDomain (integralClosure A L)]
    (w : HeightOneSpectrum (integralClosure A L)) (x : integralClosure A M) :
    x ∈ (underI A h w).asIdeal ↔ incl A K h x ∈ w.asIdeal := Iff.rfl

theorem underI_trans (h₁ : M ≤ M') (h₂ : M' ≤ L) [IsDedekindDomain (integralClosure A M)]
    [IsDedekindDomain (integralClosure A M')] [IsDedekindDomain (integralClosure A L)]
    (w : HeightOneSpectrum (integralClosure A L)) :
    underI A h₁ (underI A h₂ w) = underI A (h₁.trans h₂) w := by
  ext1
  ext x
  exact Iff.rfl

/-- **Valuations along an unramified top level**: `v_{under w}(x) = v_w(x)` for `x ∈ M ≤ L ∈ unramSet`. -/
theorem val_underI (h : M ≤ L) (hL : L ∈ unramSet A K)
    (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField)
    [IsDedekindDomain (integralClosure A M)] [IsFractionRing (integralClosure A M) M]
    [IsDedekindDomain (integralClosure A L)] [IsFractionRing (integralClosure A L) L]
    (w : HeightOneSpectrum (integralClosure A L)) (x : M) :
    (underI A h w).valuation M x = w.valuation L (IntermediateField.inclusion h x) := by
  letI : Algebra (integralClosure A M) (integralClosure A L) := (incl A K h).toRingHom.toAlgebra
  letI : SMul (integralClosure A M) (integralClosure A L) := Algebra.toSMul
  letI : Algebra M L := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : Algebra (integralClosure A M) L :=
    ((algebraMap M L).comp (algebraMap (integralClosure A M) M)).toAlgebra
  have : @IsScalarTower (integralClosure A M) M L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : @IsScalarTower (integralClosure A M) (integralClosure A L) L Algebra.toSMul Algebra.toSMul
      Algebra.toSMul := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower A (integralClosure A M) (integralClosure A L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext (Subtype.ext rfl))
  have : Module.IsTorsionFree (integralClosure A M) (integralClosure A L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : integralClosure A L => ((z : L) : AlgebraicClosure K)) hxy))
  have : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := A) x).tower_top⟩
  have he : w.asIdeal.ramificationIdx (integralClosure A M) = 1 := by
    have h1 := ramificationIdx_eq_one A hL hperf w.asIdeal w.ne_bot
    rw [Ideal.ramificationIdx_tower (R := A) (w.under (integralClosure A M)).asIdeal w.asIdeal] at h1
    exact Nat.dvd_one.1 ⟨_, h1.symm.trans (mul_comm _ _)⟩
  have he' : (w.under (integralClosure A M)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (integralClosure A M)).ne_bot]
    exact he
  have hval := HeightOneSpectrum.valuation_liesOver L (w.under (integralClosure A M)) w x
  rw [he', pow_one] at hval
  have hu : underI A h w = w.under (integralClosure A M) := by
    ext1
    rfl
  rw [hu]
  exact hval

end

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_KumOrb =====
section

/-!
# S4-PD (3)(iii)(K), part O: Galois orbits of primes and valuations mod `n`

`R → B` with a finite group `G` acting on the Dedekind domain `B` with invariants `R` (`Algebra.IsInvariant`),
`F = Frac B` with a compatible `G`-action.
* `smul_eq_pullH`: `w' = g • w` as ideals ⇒ `w' = pullH g⁻¹ w`;
* `dvd_sub_of_under_eq`: if `g • b / b` has `n`-divisible valuations for every `g`, then two primes of `B` over the
  same prime of `R` give congruent valuations of `b` mod `n` (transitivity of `G` on the fibre).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IsDedekindDomain
open scoped Pointwise

variable {R B : Type*} [CommRing R] [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {G : Type*} [Group G] [MulSemiringAction G B]

/-- `w' = g • w` as ideals means `w' = pullH g⁻¹ w`. -/
theorem smul_eq_pullH (g : G) (w w' : HeightOneSpectrum B) (h : w'.asIdeal = g • w.asIdeal) :
    w' = PicDescent.pullH (MulSemiringAction.toRingEquiv G B g⁻¹) w := by
  ext1
  rw [h, Ideal.pointwise_smul_def, PicDescent.pullH_asIdeal]
  have h1 : MulSemiringAction.toRingHom G B g =
      ((MulSemiringAction.toRingEquiv G B g : B ≃+* B) : B →+* B) := rfl
  rw [h1, Ideal.map_comap_of_equiv]
  rfl

variable [Finite G] [SMulCommClass G R B] [Algebra.IsInvariant R B G]
  {F : Type*} [Field F] [Algebra B F] [IsFractionRing B F] [MulSemiringAction G F]

/-- **Valuations are constant mod `n` on a fibre** when every `g • b / b` has `n`-divisible valuations. -/
theorem dvd_sub_of_under_eq (hcomp : ∀ (g : G) (x : B), algebraMap B F (g • x) = g • algebraMap B F x)
    (n : ℤ) (b : F)
    (hb : ∀ (g : G) (w : HeightOneSpectrum B),
      n ∣ WithZero.log (w.valuation F (g • b)) - WithZero.log (w.valuation F b))
    (w w' : HeightOneSpectrum B) (h : w.asIdeal.under R = w'.asIdeal.under R) :
    n ∣ WithZero.log (w.valuation F b) - WithZero.log (w'.valuation F b) := by
  have := w.isPrime
  have := w'.isPrime
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R B G w.asIdeal w'.asIdeal h
  have hw' := smul_eq_pullH g w w' hg
  have hv : w'.valuation F b = w.valuation F (g⁻¹ • b) := by
    rw [hw']
    exact PicDescent.valuation_pullH (MulSemiringAction.toRingEquiv G B g⁻¹)
      (MulSemiringAction.toRingEquiv G F g⁻¹) (fun x => hcomp g⁻¹ x) w b
  rw [hv]
  have h2 := dvd_neg.2 (hb g⁻¹ w)
  rwa [neg_sub] at h2

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_KumGrp =====
section

/-!
# S4-PD (3)(iii)(K), part G: the decomposition group of a finite level

For a normal finite level `ML ≤ K_U` and an intermediate field `E` of `K_U / E₀`:
* `resML`: restriction `π₁(U) → Gal(ML/K)`, `resML_apply`; `toPi1`: `Gal(K_U/E₀) → π₁(U)`;
* `Hgrp`: the image of `Gal(K_U/E)` in `Gal(ML/K)`; `exists_of_mem_Hgrp`, `Hgrp_fix` (it fixes `ML ∩ E`) and
  `mem_of_Hgrp_fix` (its fixed elements lie in `E`, by infinite Galois theory).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IntermediateField RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh

noncomputable section

variable {K : Type} [Field K] (A : Type) [CommRing A] [Algebra A K]

/-- Restriction of `π₁(U)` to a normal finite level `ML ≤ K_U`. -/
def resML {ML : IntermediateField K (AlgebraicClosure K)} (hLU : ML ≤ maxUnram A K) [Normal K ML] :
    Pi1 A K →* (ML ≃ₐ[K] ML) :=
  letI : Algebra ML (maxUnram A K) := (IntermediateField.inclusion hLU).toAlgebra
  haveI : IsScalarTower K ML (maxUnram A K) := IsScalarTower.of_algHom (IntermediateField.inclusion hLU)
  AlgEquiv.restrictNormalHom ML

theorem resML_apply {ML : IntermediateField K (AlgebraicClosure K)} (hLU : ML ≤ maxUnram A K) [Normal K ML]
    (σ : Pi1 A K) (y : ML) : ((resML A hLU σ y : ML) : AlgebraicClosure K) =
      ((σ (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K) := by
  letI : Algebra ML (maxUnram A K) := (IntermediateField.inclusion hLU).toAlgebra
  haveI : IsScalarTower K ML (maxUnram A K) := IsScalarTower.of_algHom (IntermediateField.inclusion hLU)
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes σ ML y)

/-- `Gal(K_U/E₀) → π₁(U)` (forget `E₀`-linearity). -/
def toPi1 (E₀ : IntermediateField K (maxUnram A K)) : (maxUnram A K ≃ₐ[E₀] maxUnram A K) →* Pi1 A K where
  toFun ρ := ρ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

variable (E₀ : IntermediateField K (maxUnram A K)) (E : IntermediateField E₀ (maxUnram A K))
  {ML : IntermediateField K (AlgebraicClosure K)} (hLU : ML ≤ maxUnram A K) [Normal K ML]

/-- The image of `Gal(K_U/E)` in `Gal(ML/K)`. -/
def Hgrp : Subgroup (ML ≃ₐ[K] ML) := (E.fixingSubgroup.map (toPi1 A E₀)).map (resML A hLU)

theorem exists_of_mem_Hgrp {τ : ML ≃ₐ[K] ML} (hτ : τ ∈ Hgrp A E₀ E hLU) :
    ∃ ρ ∈ E.fixingSubgroup, ∀ y : ML, ((τ y : ML) : AlgebraicClosure K) =
      ((ρ (IntermediateField.inclusion hLU y) : maxUnram A K) : AlgebraicClosure K) := by
  obtain ⟨σ, ⟨ρ, hρ, rfl⟩, rfl⟩ := hτ
  exact ⟨ρ, hρ, fun y => resML_apply A hLU _ y⟩

/-- `Hgrp` fixes `ML ∩ E`. -/
theorem Hgrp_fix {τ : ML ≃ₐ[K] ML} (hτ : τ ∈ Hgrp A E₀ E hLU) {x : ML}
    (hx : ∃ e : E, ((e : maxUnram A K) : AlgebraicClosure K) = x) : τ x = x := by
  obtain ⟨ρ, hρ, hτρ⟩ := exists_of_mem_Hgrp A E₀ E hLU hτ
  obtain ⟨e, he⟩ := hx
  have hxe : IntermediateField.inclusion hLU x = (e : maxUnram A K) := Subtype.ext he.symm
  apply Subtype.ext
  rw [hτρ, hxe, (mem_fixingSubgroup_iff _ _).1 hρ e e.2, he]

/-- The elements of `ML` fixed by `Hgrp` lie in `E` (infinite Galois theory for `K_U / E₀`). -/
theorem mem_of_Hgrp_fix [IsGalois E₀ (maxUnram A K)] {x : ML} (hx : ∀ τ ∈ Hgrp A E₀ E hLU, τ x = x) :
    ∃ e : E, ((e : maxUnram A K) : AlgebraicClosure K) = x := by
  have hmem : IntermediateField.inclusion hLU x ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, mem_fixedField_iff]
    intro ρ hρ
    have h1 := hx (resML A hLU (toPi1 A E₀ ρ)) ⟨toPi1 A E₀ ρ, ⟨ρ, hρ, rfl⟩, rfl⟩
    apply Subtype.ext
    have h2 := resML_apply A hLU (toPi1 A E₀ ρ) x
    rw [h1] at h2
    exact h2.symm
  exact ⟨⟨_, hmem⟩, rfl⟩

end

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_KumDesc =====
section

/-!
# S4-PD (3)(iii)(K), part D: valuations of a Kummer element are constant mod `n` on `Hgrp`-orbits

`ME ≤ ML` finite levels of `K_U` with `ME = ML ∩ E`; `Hgrp` acts on `B_ML` with invariants `B_ME`
(`Algebra.IsInvariant`, from `mem_of_Hgrp_fix`), so `dvd_sub_of_under_eq` applies:
* `orbit_dvd`: if `τ b / b` has `n`-divisible valuations for every `τ ∈ Hgrp`, then `v_w(b) ≡ v_{w'}(b) mod n`
  whenever `w, w'` lie over the same prime of `B_ME`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IntermediateField IsDedekindDomain RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh

noncomputable section

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  (E₀ : IntermediateField K (maxUnram A K)) (E : IntermediateField E₀ (maxUnram A K))
  {ML ME : IntermediateField K (AlgebraicClosure K)} (hLU : ML ≤ maxUnram A K) [Normal K ML] [FiniteDimensional K ML]

set_option synthInstance.maxHeartbeats 400000 in
theorem orbit_dvd [IsGalois E₀ (maxUnram A K)] (hle : ME ≤ ML)
    (hME : ∀ x : ML, (x : AlgebraicClosure K) ∈ ME ↔ ∃ e : E, ((e : maxUnram A K) : AlgebraicClosure K) = x)
    [IsDedekindDomain (integralClosure A ME)] [IsFractionRing (integralClosure A ME) ME]
    [IsDedekindDomain (integralClosure A ML)] [IsFractionRing (integralClosure A ML) ML]
    (n : ℤ) (b : ML)
    (hb : ∀ τ ∈ Hgrp A E₀ E hLU, ∀ w : HeightOneSpectrum (integralClosure A ML),
      n ∣ WithZero.log (w.valuation ML (τ b)) - WithZero.log (w.valuation ML b))
    (w w' : HeightOneSpectrum (integralClosure A ML)) (h : underI A hle w = underI A hle w') :
    n ∣ WithZero.log (w.valuation ML b) - WithZero.log (w'.valuation ML b) := by
  let H := Hgrp A E₀ E hLU
  letI : MulSemiringAction H ML := MulSemiringAction.compHom ML H.subtype
  haveI : SMulCommClass H A ML := ⟨fun g a x => map_smul ((g : ML ≃ₐ[K] ML).restrictScalars A) a x⟩
  letI : MulSemiringAction H (integralClosure A ML) := inferInstance
  letI : Algebra (integralClosure A ME) (integralClosure A ML) := (incl A K hle).toRingHom.toAlgebra
  letI : SMul (integralClosure A ME) (integralClosure A ML) := Algebra.toSMul
  haveI : SMulCommClass H (integralClosure A ME) (integralClosure A ML) := ⟨fun g e x => by
    apply Subtype.ext
    change (g : ML ≃ₐ[K] ML) (((incl A K hle e : integralClosure A ML) : ML) * (x : ML)) =
      ((incl A K hle e : integralClosure A ML) : ML) * (g : ML ≃ₐ[K] ML) (x : ML)
    rw [map_mul, Hgrp_fix A E₀ E hLU g.2 ((hME _).1 ((e : ME)).2)]⟩
  haveI : Algebra.IsInvariant (integralClosure A ME) (integralClosure A ML) H := ⟨fun x hx => by
    have hfix : ∀ τ ∈ H, τ (x : ML) = (x : ML) := fun τ hτ => congrArg Subtype.val (hx ⟨τ, hτ⟩)
    have hmem : ((x : ML) : AlgebraicClosure K) ∈ ME := (hME _).2 (mem_of_Hgrp_fix A E₀ E hLU hfix)
    have hint : IsIntegral A (⟨(x : ML), hmem⟩ : ME) := by
      have h1 : IsIntegral A (x : ML) := x.2
      exact (isIntegral_algHom_iff ((IntermediateField.inclusion hle).restrictScalars A)
        (IntermediateField.inclusion hle).injective).1 h1
    exact ⟨⟨⟨(x : ML), hmem⟩, hint⟩, Subtype.ext rfl⟩⟩
  exact dvd_sub_of_under_eq (R := integralClosure A ME) (G := H) (fun _ _ => rfl) n b
    (fun g w => hb g.1 g.2 w) w w' (congrArg HeightOneSpectrum.asIdeal h)

end

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_KumLev =====
section

/-!
# S4-PD (3)(iii)(K), part L: level lemmas for the Kummer-closure descent

* `exists_underI_eq`: every prime of `B_M` lies under a prime of `B_L` (`M ≤ L`);
* `hgrp_dvd`: for a Kummer element `b` of a Galois extension `L/E` inside `K_U` (every `σ b / b` an `l`-th power in
  `L`, stated as `σ b = c ^ l * b`) and a finite unramified level `ML ∋ b`, every `τ ∈ Hgrp` changes the valuations of `b` by multiples of `l`;
* `constLevel_le_map`: the constant level `K(𝔽_{p^m})` lies in every `E ⊇ E₀ = constFieldU`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open IntermediateField IsDedekindDomain RamanujanPetersson.Kummer RamanujanPetersson.CurveCoh

noncomputable section

variable {K : Type} [Field K] (A : Type) [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

/-- Every prime of `B_M` lies under a prime of `B_L`. -/
theorem exists_underI_eq {M L : IntermediateField K (AlgebraicClosure K)} (h : M ≤ L)
    [IsDedekindDomain (integralClosure A M)] [IsDedekindDomain (integralClosure A L)]
    (P : HeightOneSpectrum (integralClosure A M)) : ∃ w, underI A h w = P := by
  letI : Algebra (integralClosure A M) (integralClosure A L) := (incl A K h).toRingHom.toAlgebra
  letI : SMul (integralClosure A M) (integralClosure A L) := Algebra.toSMul
  have : IsScalarTower A (integralClosure A M) (integralClosure A L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext (Subtype.ext rfl))
  have : Module.IsTorsionFree (integralClosure A M) (integralClosure A L) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : integralClosure A L => ((z : L) : AlgebraicClosure K)) hxy))
  have : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := A) x).tower_top⟩
  obtain ⟨w, hw⟩ := PicDescent.exists_under_eq (A := integralClosure A M) (B := integralClosure A L) P
  refine ⟨w, ?_⟩
  rw [← hw]
  ext1
  rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- `τ ∈ Hgrp` moves the valuations of a Kummer element `b` by multiples of `l`. -/
theorem hgrp_dvd (hperf : ∀ (p : Ideal A) [p.IsMaximal], PerfectField p.ResidueField)
    (E₀ : IntermediateField K (maxUnram A K)) (E : IntermediateField E₀ (maxUnram A K))
    (L : IntermediateField E (maxUnram A K)) [Normal E L] (l : ℕ)
    {ML : IntermediateField K (AlgebraicClosure K)} (hLU : ML ≤ maxUnram A K) [Normal K ML]
    (hML : ML ∈ unramSet A K)
    [IsDedekindDomain (integralClosure A ML)] [IsFractionRing (integralClosure A ML) ML]
    (b : L) (hb0 : b ≠ 0) (hb : ∀ σ : L ≃ₐ[E] L, ∃ c : L, σ b = c ^ l * b)
    (bL : ML) (hbL : (bL : AlgebraicClosure K) = ((b : maxUnram A K) : AlgebraicClosure K))
    {τ : ML ≃ₐ[K] ML} (hτ : τ ∈ Hgrp A E₀ E hLU) (w : HeightOneSpectrum (integralClosure A ML)) :
    (l : ℤ) ∣ WithZero.log (w.valuation ML (τ bL)) - WithZero.log (w.valuation ML bL) := by
  obtain ⟨ρ, hρ, hτρ⟩ := exists_of_mem_Hgrp A E₀ E hLU hτ
  let σ : L ≃ₐ[E] L := (E.fixingSubgroupEquiv ⟨ρ, hρ⟩).restrictNormal L
  obtain ⟨c, hc'⟩ := hb σ
  have hβ0 : (bL : AlgebraicClosure K) ≠ 0 := by
    rw [hbL]
    simpa using hb0
  have hbL0 : bL ≠ 0 := by
    intro h
    apply hβ0
    rw [h, ZeroMemClass.coe_zero]
  have hτ0 : τ bL ≠ 0 := (map_ne_zero τ).2 hbL0
  have hx : IntermediateField.inclusion hLU bL = (b : maxUnram A K) := Subtype.ext hbL
  have h3 : ((σ b : L) : maxUnram A K) = ρ (b : maxUnram A K) :=
    AlgEquiv.restrictNormal_apply L _ b
  have hτb : ((τ bL : ML) : AlgebraicClosure K) =
      ((c : maxUnram A K) : AlgebraicClosure K) ^ l * (bL : AlgebraicClosure K) := by
    rw [hτρ, hx, ← h3, hc', hbL]
    simp only [IntermediateField.coe_mul, IntermediateField.coe_pow]
  obtain ⟨q, hq⟩ : ∃ q : ML, q = τ bL / bL := ⟨_, rfl⟩
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact div_ne_zero hτ0 hbL0
  have hα : ((c : maxUnram A K) : AlgebraicClosure K) ^ l = (q : AlgebraicClosure K) := by
    rw [hq, IntermediateField.coe_div, hτb, mul_div_cancel_right₀ _ hβ0]
  have hdiv := dvd_log_valuation_of_mem_maxUnram A hML hperf (c : maxUnram A K).2 hα w
  have hτq : τ bL = q * bL := by rw [hq, div_mul_cancel₀ _ hbL0]
  rw [hτq, log_val_mul w hq0 hbL0, add_sub_cancel_right]
  exact hdiv

/-- `x ^ k = x` gives `x ^ (k ^ j) = x`. -/
theorem pow_pow_eq_self {F : Type*} [Monoid F] {y : F} {k : ℕ} (hy : y ^ k = y) (j : ℕ) : y ^ (k ^ j) = y := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, pow_mul, ih, hy]

variable {p : ℕ} [Fact p.Prime] [CharP K p]

end

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_Tsen_RatFunc =====
section

set_option autoImplicit false

/-!
# S4-PD (1), T2: Tsen's theorem for `k(t)`

* `exists_zero_polynomial`: `k` algebraically closed, `F ∈ k[t][x₀,…,x_{n-1}]` with total degree `< n` and no constant
  term has a nonzero zero in `k[t]ⁿ` (substitute `xᵢ = ∑_{j ≤ N} a_{ij} tʲ`, count unknowns against the coefficients of
  the powers of `t`, and apply `exists_common_zero`).
* `exists_clear_denom`: common denominators for a multivariate polynomial over a fraction field.
* `isC1_ratFunc`: `RatFunc k` is `C₁` (strong form `IsC1`).
-/

namespace RamanujanPetersson.Tsen

open Polynomial

section Core

variable {k : Type*} [Field k]

/-- The generic substitution `xᵢ = ∑_{j ≤ N} a_{(i,j)} tʲ`, with the `a`'s as variables. -/
noncomputable def subVar (n N : ℕ) (i : Fin n) : (MvPolynomial (Fin (n * (N + 1))) k)[X] :=
  ∑ j : Fin (N + 1), C (MvPolynomial.X (finProdFinEquiv (i, j))) * X ^ (j : ℕ)

/-- `F` after the generic substitution, a polynomial in `t` over the polynomial ring of the unknowns. -/
noncomputable def subPoly (n N : ℕ) (F : MvPolynomial (Fin n) k[X]) :
    (MvPolynomial (Fin (n * (N + 1))) k)[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom MvPolynomial.C) (subVar n N) F

/-- The substitution at a point `a` of the unknowns. -/
noncomputable def specVar (n N : ℕ) (a : Fin (n * (N + 1)) → k) (i : Fin n) : k[X] :=
  ∑ j : Fin (N + 1), C (a (finProdFinEquiv (i, j))) * X ^ (j : ℕ)

theorem map_subPoly (n N : ℕ) (F : MvPolynomial (Fin n) k[X]) (a : Fin (n * (N + 1)) → k) :
    (subPoly n N F).map (MvPolynomial.eval a) = MvPolynomial.eval (specVar n N a) F := by
  unfold subPoly
  rw [← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left]
  have h1 : (Polynomial.mapRingHom (MvPolynomial.eval a)).comp
      (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin (n * (N + 1))) (R := k))) = RingHom.id k[X] := by
    rw [Polynomial.mapRingHom_comp]
    have : (MvPolynomial.eval a).comp (MvPolynomial.C (σ := Fin (n * (N + 1))) (R := k)) = RingHom.id k := by
      ext c; simp
    rw [this, Polynomial.mapRingHom_id]
  have h2 : (Polynomial.mapRingHom (MvPolynomial.eval a)) ∘ subVar n N = specVar n N a := by
    funext i
    simp [subVar, specVar, Polynomial.map_sum]
  rw [h1, h2]
  rfl

theorem coeff_specVar (n N : ℕ) (a : Fin (n * (N + 1)) → k) (i : Fin n) (j : Fin (N + 1)) :
    (specVar n N a i).coeff j = a (finProdFinEquiv (i, j)) := by
  simp only [specVar, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (Fin.ext h.symm)
  · simp

theorem natDegree_subVar_le (n N : ℕ) (i : Fin n) : (subVar (k := k) n N i).natDegree ≤ N := by
  unfold subVar
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp j.isLt)

theorem natDegree_subPoly_le (n N c : ℕ) (F : MvPolynomial (Fin n) k[X])
    (hc : ∀ m, (F.coeff m).natDegree ≤ c) :
    (subPoly n N F).natDegree ≤ N * F.totalDegree + c := by
  unfold subPoly
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 : (Polynomial.mapRingHom (MvPolynomial.C (σ := Fin (n * (N + 1))) (R := k))
      (F.coeff m)).natDegree ≤ c := Polynomial.natDegree_map_le.trans (hc m)
  have hsum : ∑ i, m i ≤ F.totalDegree := by
    have := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.sum_fintype _ _ (by simp)] at this
  have h2 : (∏ i, subVar (k := k) n N i ^ m i).natDegree ≤ N * F.totalDegree := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ i, (subVar (k := k) n N i ^ m i).natDegree ≤ ∑ i, m i * N :=
          Finset.sum_le_sum fun i _ =>
            Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (natDegree_subVar_le n N i))
      _ = N * ∑ i, m i := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ N * F.totalDegree := Nat.mul_le_mul_left _ hsum
  omega

theorem constantCoeff_coeff_subPoly (n N : ℕ) (F : MvPolynomial (Fin n) k[X])
    (hF : MvPolynomial.constantCoeff F = 0) (m : ℕ) :
    MvPolynomial.constantCoeff ((subPoly n N F).coeff m) = 0 := by
  have h := congrArg (fun p => Polynomial.coeff p m) (map_subPoly n N F 0)
  simp only [Polynomial.coeff_map] at h
  have h0 : specVar n N (0 : Fin (n * (N + 1)) → k) = 0 := by
    funext i; simp [specVar]
  rw [h0, MvPolynomial.eval_zero, MvPolynomial.eval_zero] at h
  rw [h]
  simp [hF]

/-- **Core of Tsen's theorem.** Over `k[t]`, `k` algebraically closed: a polynomial in `n` variables of total degree
`< n` without constant term has a nonzero zero in `k[t]ⁿ`. -/
theorem exists_zero_polynomial [IsAlgClosed k] {n : ℕ} (F : MvPolynomial (Fin n) k[X])
    (hdeg : F.totalDegree < n) (hF : MvPolynomial.constantCoeff F = 0) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧ MvPolynomial.eval x F = 0 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, ∀ m, (F.coeff m).natDegree ≤ c :=
    ⟨F.support.sup fun m => (F.coeff m).natDegree, fun m => by
      by_cases hm : m ∈ F.support
      · exact Finset.le_sup (f := fun m => (F.coeff m).natDegree) hm
      · rw [MvPolynomial.notMem_support_iff.mp hm]; simp⟩
  have hcount : (c + 1) * F.totalDegree + c + 1 < n * (c + 1 + 1) := by
    have h1 : (F.totalDegree + 1) * (c + 2) ≤ n * (c + 2) := Nat.mul_le_mul_right _ hdeg
    nlinarith [h1]
  let P : Fin ((c + 1) * F.totalDegree + c + 1) → MvPolynomial (Fin (n * (c + 1 + 1))) k :=
    fun m => (subPoly n (c + 1) F).coeff m
  obtain ⟨a, ha, haP⟩ := exists_common_zero hcount P
    (fun m => constantCoeff_coeff_subPoly n (c + 1) F hF m)
  refine ⟨specVar n (c + 1) a, ?_, ?_⟩
  · intro h0
    apply ha
    funext p
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    have := congrArg (fun q => Polynomial.coeff q j) (congrFun h0 i)
    simpa [coeff_specVar] using this
  · ext m
    rw [← map_subPoly, Polynomial.coeff_map]
    by_cases hm : m < (c + 1) * F.totalDegree + c + 1
    · simpa [P] using haP ⟨m, hm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_subPoly_le n (c + 1) c F hc).trans_lt (by omega))]
      simp

end Core

/-- Common denominators: a multivariate polynomial over a fraction field becomes integral after multiplying by one
nonzero element. -/
theorem exists_clear_denom {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {σ : Type*} (f : MvPolynomial σ K) :
    ∃ (b : A) (F : MvPolynomial σ A), b ≠ 0 ∧
      ∀ m, algebraMap A K (F.coeff m) = algebraMap A K b * f.coeff m := by
  classical
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A) (f.support.image fun m => f.coeff m)
  have hall : ∀ m, ∃ r : A, algebraMap A K r = b • f.coeff m := by
    intro m
    by_cases hm : m ∈ f.support
    · exact RingHom.mem_rangeS.mp (hint _ (Finset.mem_image_of_mem _ hm))
    · exact ⟨0, by rw [MvPolynomial.notMem_support_iff.mp hm, smul_zero, map_zero]⟩
  choose r hr using hall
  refine ⟨b, ∑ m' ∈ f.support, MvPolynomial.monomial m' (r m'), nonZeroDivisors.ne_zero hb, ?_⟩
  intro m
  have hc : (∑ m' ∈ f.support, MvPolynomial.monomial m' (r m')).coeff m =
      if m ∈ f.support then r m else 0 := by
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial]
  rw [hc]
  split_ifs with hm
  · exact (hr m).trans (Algebra.smul_def _ _)
  · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero, map_zero]

/-- **Tsen's theorem for `k(t)`** (strong `C₁` form). -/
theorem isC1_ratFunc (k : Type*) [Field k] [IsAlgClosed k] : IsC1 (RatFunc k) := by
  intro n f hdeg hconst
  obtain ⟨b, F, hb, hF⟩ := exists_clear_denom (A := k[X]) f
  have hinj := IsFractionRing.injective k[X] (RatFunc k)
  have hsupp : F.support ⊆ f.support := by
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h0
    apply hm
    apply hinj
    rw [hF, h0, mul_zero, map_zero]
  have hdegF : F.totalDegree < n := by
    refine lt_of_le_of_lt ?_ hdeg
    unfold MvPolynomial.totalDegree
    exact Finset.sup_mono hsupp
  have hconstF : MvPolynomial.constantCoeff F = 0 := by
    apply hinj
    have e1 : MvPolynomial.constantCoeff F = F.coeff 0 := congrFun MvPolynomial.constantCoeff_eq F
    have e2 : MvPolynomial.constantCoeff f = f.coeff 0 := congrFun MvPolynomial.constantCoeff_eq f
    rw [e1, hF, ← e2, hconst, mul_zero, map_zero]
  obtain ⟨x, hx0, hx⟩ := exists_zero_polynomial F hdegF hconstF
  refine ⟨fun i => algebraMap k[X] (RatFunc k) (x i), ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    apply hinj
    simpa using congrFun h i
  · have hmap : MvPolynomial.map (algebraMap k[X] (RatFunc k)) F =
        MvPolynomial.C (algebraMap k[X] (RatFunc k) b) * f := by
      ext m
      rw [MvPolynomial.coeff_map, hF, MvPolynomial.coeff_C_mul]
    have h1 : MvPolynomial.eval (fun i => algebraMap k[X] (RatFunc k) (x i))
        (MvPolynomial.map (algebraMap k[X] (RatFunc k)) F) =
        algebraMap k[X] (RatFunc k) (MvPolynomial.eval x F) := by
      rw [MvPolynomial.eval_map]
      have := MvPolynomial.eval₂_comp_left (algebraMap k[X] (RatFunc k)) (RingHom.id _) x F
      rw [RingHom.comp_id] at this
      exact this.symm
    rw [hmap, hx, map_zero, map_mul, MvPolynomial.eval_C] at h1
    exact (mul_eq_zero.mp h1).resolve_left (fun h => hb (hinj (h.trans (map_zero _).symm)))

end RamanujanPetersson.Tsen


end

-- ===== S4.Def_RP_Tsen_Norm =====
section

set_option autoImplicit false

/-!
# S4-PD (1), T3: finite extensions of `C₁` fields are `C₁` (the norm form)

* `coeffMap g z`: apply a `K`-linear functional `g : L → K` to every coefficient of `z`; it commutes with evaluation at
  `K`-points (`eval_coeffMap`) and does not raise the total degree.
* `totalDegree_bind₁_le`, `totalDegree_det_le`: degree bounds for linear substitution and determinants.
* `exists_normForm`: for `L/K` with basis `b` (`e` elements) and `f ∈ L[x₀,…,x_{n-1}]` there is
  `P ∈ K[y_{(i,j)}]` with `totalDegree P ≤ e * totalDegree f` and `P(y) = N_{L/K}(f(∑ⱼ y_{(i,j)} bⱼ))`.
* `IsC1.of_finite`: `L/K` finite and `K` is `C₁` imply `L` is `C₁`.
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

section CoeffMap

variable {σ K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Apply a `K`-linear functional to every coefficient. -/
noncomputable def coeffMap (g : L →ₗ[K] K) (z : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ d ∈ z.support, monomial d (g (z.coeff d))

theorem totalDegree_coeffMap_le (g : L →ₗ[K] K) (z : MvPolynomial σ L) :
    (coeffMap g z).totalDegree ≤ z.totalDegree :=
  totalDegree_finsetSum_le fun _ hd => (totalDegree_monomial_le _ _).trans (le_totalDegree hd)

theorem eval_coeffMap (g : L →ₗ[K] K) (z : MvPolynomial σ L) (y : σ → K) :
    eval y (coeffMap g z) = g (eval (fun i => algebraMap K L (y i)) z) := by
  have hp : ∀ d : σ →₀ ℕ, ∏ i ∈ d.support, (algebraMap K L (y i)) ^ d i =
      algebraMap K L (∏ i ∈ d.support, y i ^ d i) := by
    intro d; rw [map_prod]; simp [map_pow]
  rw [coeffMap, map_sum, MvPolynomial.eval_eq (fun i => algebraMap K L (y i)) z, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.eval_monomial, hp d, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul,
    mul_comm]
  rfl

end CoeffMap

theorem totalDegree_bind₁_le {σ τ R : Type*} [CommRing R] (g : σ → MvPolynomial τ R) (f : MvPolynomial σ R)
    (hg : ∀ i, (g i).totalDegree ≤ 1) : (bind₁ g f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  calc d i * (g i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = d i := mul_one _

theorem totalDegree_det_le {σ R : Type*} [CommRing R] {e : ℕ} (M : Matrix (Fin e) (Fin e) (MvPolynomial σ R))
    (D : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ D) : M.det.totalDegree ≤ e * D := by
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro τ _
  refine (totalDegree_mul _ _).trans ?_
  have h1 : ((Equiv.Perm.sign τ : ℤ) : MvPolynomial σ R).totalDegree = 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial σ R), totalDegree_C]
  rw [h1, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (M (τ i) i).totalDegree ≤ ∑ _i : Fin e, D := Finset.sum_le_sum fun i _ => hM _ _
    _ = e * D := by simp

section NormForm

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- **The norm form.** `P(y) = N_{L/K}(f(∑ⱼ y_{(i,j)} bⱼ))` is a polynomial of degree `≤ e · deg f` over `K`. -/
theorem exists_normForm {e : ℕ} (b : Module.Basis (Fin e) K L) {n : ℕ} (f : MvPolynomial (Fin n) L) :
    ∃ P : MvPolynomial (Fin (n * e)) K, P.totalDegree ≤ e * f.totalDegree ∧
      ∀ y : Fin (n * e) → K,
        eval y P = Algebra.norm K (eval (fun i => ∑ j, y (finProdFinEquiv (i, j)) • b j) f) := by
  classical
  let g : Fin n → MvPolynomial (Fin (n * e)) L :=
    fun i => ∑ j : Fin e, C (b j) * X (finProdFinEquiv (i, j))
  have hg : ∀ i, (g i).totalDegree ≤ 1 := by
    intro i
    refine totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  let z := bind₁ g f
  have hz : ∀ y : Fin (n * e) → K, eval (fun p => algebraMap K L (y p)) z =
      eval (fun i => ∑ j, y (finProdFinEquiv (i, j)) • b j) f := by
    intro y
    refine (eval₂Hom_bind₁ (RingHom.id L) (fun p => algebraMap K L (y p)) g f).trans ?_
    show eval _ f = eval _ f
    refine congrArg (fun x : Fin n → L => eval x f) (funext fun i => ?_)
    show eval _ (g i) = _
    simp only [g, map_sum, map_mul, eval_C, eval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  let M : Matrix (Fin e) (Fin e) (MvPolynomial (Fin (n * e)) K) :=
    fun i j => coeffMap ((b.coord i).comp (LinearMap.mulRight K (b j))) z
  refine ⟨M.det, ?_, ?_⟩
  · refine (totalDegree_det_le M z.totalDegree fun i j => totalDegree_coeffMap_le _ _).trans ?_
    exact Nat.mul_le_mul_left _ (totalDegree_bind₁_le g f hg)
  · intro y
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det b]
    congr 1
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]
    show eval y (coeffMap _ z) = _
    rw [eval_coeffMap, hz]
    rfl

/-- **Lang.** A finite extension of a `C₁` field is `C₁`. -/
theorem IsC1.of_finite (hK : IsC1 K) : IsC1 L := by
  classical
  intro n f hdeg hconst
  obtain ⟨e, b, hepos⟩ : ∃ e, ∃ _ : Module.Basis (Fin e) K L, 0 < e :=
    ⟨_, Module.finBasis K L, Module.finrank_pos⟩
  obtain ⟨P, hPdeg, hP⟩ := exists_normForm b f
  have hdegP : P.totalDegree < n * e :=
    lt_of_le_of_lt hPdeg (by rw [mul_comm n e]; exact Nat.mul_lt_mul_of_pos_left hdeg hepos)
  have hconstP : constantCoeff P = 0 := by
    rw [← MvPolynomial.eval_zero, hP]
    simp [MvPolynomial.eval_zero', hconst]
  obtain ⟨y, hy0, hy⟩ := hK (n * e) P hdegP hconstP
  rw [hP, Algebra.norm_eq_zero_iff] at hy
  refine ⟨fun i => ∑ j, y (finProdFinEquiv (i, j)) • b j, ?_, hy⟩
  intro hx
  apply hy0
  funext p
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
  exact Fintype.linearIndependent_iff.mp b.linearIndependent _ (congrFun hx i) j

end NormForm

end RamanujanPetersson.Tsen


end

-- ===== S4.Def_RP_Tsen =====
section

set_option autoImplicit false

/-!
# S4-PD (1): Tsen's theorem

* `IsC1.of_algebraic`: an algebraic extension of a `C₁` field is `C₁` (adjoin the coefficients, `IsC1.of_finite`).
* `tsen`: **Tsen's theorem.** Every algebraic extension of `k(t)`, `k` algebraically closed, is `C₁`
  (strong form `IsC1`: polynomials in `n` variables of total degree `< n` without constant term have a nonzero zero).
* `IsC1.norm_surjective`: over a `C₁` field the norm of every finite extension is surjective.
* `tsen_norm_surjective`: the norm of a finite extension of an algebraic extension of `k(t)` is surjective.
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

/-- An algebraic extension of a `C₁` field is `C₁`. -/
theorem IsC1.of_algebraic {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (hK : IsC1 K) : IsC1 L := by
  classical
  intro n f hdeg hconst
  let F := IntermediateField.adjoin K (f.coeffs : Set L)
  have : Finite (f.coeffs : Set L) := (Finset.finite_toSet _).to_subtype
  have : FiniteDimensional K F := IntermediateField.finiteDimensional_adjoin
    fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hF : IsC1 F := IsC1.of_finite hK
  have hinj : Function.Injective (algebraMap F L) := (algebraMap F L).injective
  obtain ⟨f', hf'⟩ : f ∈ Set.range (MvPolynomial.map (algebraMap F L)) :=
    MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun c hc =>
      ⟨⟨c, IntermediateField.subset_adjoin K _ hc⟩, rfl⟩
  have hdeg' : f'.totalDegree < n := by
    have h1 : (MvPolynomial.map (algebraMap F L) f').totalDegree = f'.totalDegree := by
      unfold MvPolynomial.totalDegree
      rw [MvPolynomial.support_map_of_injective _ hinj]
    rw [← h1, hf']
    exact hdeg
  have hconst' : constantCoeff f' = 0 := by
    apply hinj
    rw [← MvPolynomial.constantCoeff_map, hf', hconst, map_zero]
  obtain ⟨x, hx0, hx⟩ := hF n f' hdeg' hconst'
  refine ⟨fun i => algebraMap F L (x i), ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    exact hinj ((congrFun h i).trans (map_zero _).symm)
  · rw [← hf', MvPolynomial.eval_map]
    have h2 := MvPolynomial.eval₂_comp_left (algebraMap F L) (RingHom.id _) x f'
    rw [RingHom.comp_id] at h2
    refine h2.symm.trans ?_
    rw [show MvPolynomial.eval₂ (RingHom.id F) x f' = eval x f' from rfl, hx, map_zero]

/-- **Tsen's theorem.** An algebraic extension of the rational function field `k(t)` over an algebraically closed
field `k` is `C₁`. -/
theorem tsen (k : Type*) [Field k] [IsAlgClosed k] (L : Type*) [Field L] [Algebra (RatFunc k) L]
    [Algebra.IsAlgebraic (RatFunc k) L] : IsC1 L :=
  (isC1_ratFunc k).of_algebraic

/-- Over a `C₁` field, the norm of a finite extension is surjective. -/
theorem IsC1.norm_surjective {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hK : IsC1 K) : Function.Surjective (Algebra.norm K : L → K) := by
  classical
  intro a
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, Algebra.norm_zero]⟩
  obtain ⟨e, b, hepos⟩ : ∃ e, ∃ _ : Module.Basis (Fin e) K L, 0 < e :=
    ⟨_, Module.finBasis K L, Module.finrank_pos⟩
  obtain ⟨P, hPdeg, hP⟩ := exists_normForm b (X 0 : MvPolynomial (Fin 1) L)
  rw [totalDegree_X, mul_one] at hPdeg
  let Q : MvPolynomial (Fin (1 * e + 1)) K :=
    rename Fin.castSucc P - C a * X (Fin.last (1 * e)) ^ e
  have hQdeg : Q.totalDegree < 1 * e + 1 := by
    show (rename Fin.castSucc P - C a * X (Fin.last (1 * e)) ^ e).totalDegree < 1 * e + 1
    have h1 : (rename Fin.castSucc P).totalDegree ≤ e := (totalDegree_rename_le _ _).trans hPdeg
    have h2 : (C a * X (Fin.last (1 * e)) ^ e : MvPolynomial (Fin (1 * e + 1)) K).totalDegree ≤ e := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_pow _ _).trans ?_
      rw [totalDegree_X, mul_one]
    have := (totalDegree_sub _ _).trans (max_le h1 h2)
    omega
  have hP0 : constantCoeff P = 0 := by
    rw [← MvPolynomial.eval_zero, hP]
    simp [Algebra.norm_zero]
  have hQconst : constantCoeff Q = 0 := by
    simp [Q, MvPolynomial.constantCoeff_rename, hP0, zero_pow hepos.ne']
  obtain ⟨w, hw0, hw⟩ := hK _ Q hQdeg hQconst
  set x : L := ∑ j, w (Fin.castSucc (finProdFinEquiv (0, j))) • b j with hx
  have hnorm : Algebra.norm K x = a * w (Fin.last _) ^ e := by
    have h3 : eval w Q = Algebra.norm K x - a * w (Fin.last _) ^ e := by
      simp only [Q, map_sub, map_mul, map_pow, eval_C, eval_X, MvPolynomial.eval_rename, hP]
      try rfl
    rw [h3] at hw
    exact sub_eq_zero.mp hw
  have ht : w (Fin.last _) ≠ 0 := by
    intro ht
    rw [ht, zero_pow hepos.ne', mul_zero, Algebra.norm_eq_zero_iff] at hnorm
    apply hw0
    funext p
    induction p using Fin.lastCases with
    | last => exact ht
    | cast q =>
      obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective q
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact Fintype.linearIndependent_iff.mp b.linearIndependent _ hnorm j
  refine ⟨x * algebraMap K L (w (Fin.last _))⁻¹, ?_⟩
  rw [map_mul, Algebra.norm_algebraMap, hnorm, Module.finrank_eq_card_basis b, Fintype.card_fin, inv_pow,
    mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht), mul_one]

end RamanujanPetersson.Tsen


end

-- ===== S4.Def_RP_CdOne_Br =====
section

/-!
# S4-PD (3a), part 2: `Br(L/K) = 0` for a Galois `p`-extension of a C1 field

`br_eq_zero`: if `K` is C1 and `L/K` is finite Galois with `Gal(L/K)` a `p`-group, every multiplicative 2-cocycle
`Gal(L/K)² → Lˣ` is a coboundary. Induction on `[L : K]`: a central subgroup `N` of order `p`, the cyclic case
for `L / L^N` (norm surjectivity from C1), Hilbert 90 on `N`, inflation-restriction, and descent to `Gal(L^N/K)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe v

namespace RamanujanPetersson.CdOne

open groupCohomology IntermediateField RamanujanPetersson.Tsen

section Mul

variable {G M : Type*} [Monoid G] [CommGroup M] [MulDistribMulAction G M]

/-- `Additive M` with the action induced by the multiplicative action of `G` on `M`. -/
abbrev addAct : DistribMulAction G (Additive M) where
  smul g a := Additive.ofMul (g • a.toMul)
  one_smul a := by show Additive.ofMul ((1 : G) • a.toMul) = a; rw [one_smul]; rfl
  mul_smul g h a := by
    show Additive.ofMul ((g * h) • a.toMul) = Additive.ofMul (g • (h • a.toMul)); rw [mul_smul]
  smul_zero g := by show Additive.ofMul (g • (1 : M)) = Additive.ofMul 1; rw [smul_one]
  smul_add g a b := by
    show Additive.ofMul (g • (a.toMul * b.toMul)) = Additive.ofMul (g • a.toMul * g • b.toMul)
    rw [smul_mul']

attribute [local instance] addAct

theorem isCocycle₂_ofMul {f : G × G → M} (hf : IsMulCocycle₂ f) :
    IsCocycle₂ (fun q => Additive.ofMul (f q)) := fun g h j => hf g h j

theorem isMulCoboundary₂_of_ofMul {f : G × G → M} (h : IsCoboundary₂ (fun q => Additive.ofMul (f q))) :
    IsMulCoboundary₂ f := by
  obtain ⟨x, hx⟩ := h
  exact ⟨fun g => (x g).toMul, fun g h => hx g h⟩

end Mul

attribute [local instance] addAct

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- `Gal(L / L^N) ≃* N`. -/
noncomputable def galFixedEquiv (N : Subgroup Gal(L/K)) : Gal(L/fixedField N) ≃* N :=
  (fixingSubgroupEquiv (fixedField N)).symm.trans (MulEquiv.subgroupCongr (fixingSubgroup_fixedField N))

theorem galFixedEquiv_apply (N : Subgroup Gal(L/K)) (τ : Gal(L/fixedField N)) (y : L) :
    ((galFixedEquiv N τ : N) : Gal(L/K)) y = τ y := rfl

/-- Hilbert 90 for a subgroup `N` acting on `Lˣ` (through `Gal(L / L^N)`). -/
theorem h1_subgroup (N : Subgroup Gal(L/K)) (φ : N → Additive Lˣ) (hφ : IsCocycle₁ φ) : IsCoboundary₁ φ := by
  set e := galFixedEquiv N
  have hact : ∀ (τ : Gal(L/fixedField N)) (u : Lˣ), ((e τ : N) : Gal(L/K)) • u = τ • u :=
    fun τ u => Units.ext rfl
  have hφ' : IsMulCocycle₁ (fun τ : Gal(L/fixedField N) => (φ (e τ)).toMul) := by
    intro τ τ'
    show (φ (e (τ * τ'))).toMul = τ • (φ (e τ')).toMul * (φ (e τ)).toMul
    rw [map_mul, hφ (e τ) (e τ'), ← hact]
    rfl
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hφ'
  refine ⟨Additive.ofMul β, fun n => ?_⟩
  obtain ⟨τ, rfl⟩ := e.surjective n
  have := hβ τ
  rw [← hact] at this
  exact congrArg Additive.ofMul this

/-- A `z`-fixed element is a "norm" `∏_{t < ord z} z^t(y)` when the norm to `L^⟨z⟩` is surjective. -/
theorem exists_prod_pow_eq [IsGalois K L] (z : Gal(L/K))
    (hsurj : Function.Surjective (Algebra.norm (fixedField (Subgroup.zpowers z)) : L → _)) (x : L)
    (hx : z x = x) : ∃ y : L, ∏ t ∈ Finset.range (orderOf z), (z ^ t) y = x := by
  classical
  set N := Subgroup.zpowers z
  have hxN : x ∈ fixedField N := by
    rw [mem_fixedField_iff]
    intro g hg
    have hst : N ≤ MulAction.stabilizer Gal(L/K) x :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hx)
    exact MulAction.mem_stabilizer_iff.mp (hst hg)
  obtain ⟨y, hy⟩ := hsurj ⟨x, hxN⟩
  refine ⟨y, ?_⟩
  have h1 := Algebra.norm_eq_prod_automorphisms (fixedField N) y
  rw [hy] at h1
  change x = ∏ σ : Gal(L/fixedField N), σ y at h1
  rw [h1]
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  calc ∏ t ∈ Finset.range (orderOf z), (z ^ t) y = ∏ i : Fin (orderOf z), (z ^ (i : ℕ)) y :=
        (Fin.prod_univ_eq_prod_range (fun t => (z ^ t) y) _).symm
    _ = ∏ n : N, (n : Gal(L/K)) y :=
        Fintype.prod_equiv (finEquivZPowers hfin) _ _ (fun i => by rw [finEquivZPowers_apply])
    _ = ∏ σ : Gal(L/fixedField N), σ y := by
        convert (Fintype.prod_equiv (galFixedEquiv N) (fun τ : Gal(L/fixedField N) => τ y) (fun n : N => (n : Gal(L/K)) y)
          (fun τ => rfl)).symm

/-- The cyclic step: the restriction of a cocycle to `⟨z⟩` is a coboundary. -/
theorem isCoboundary₂_zpowers [IsGalois K L] (z : Gal(L/K))
    (hsurj : Function.Surjective (Algebra.norm (fixedField (Subgroup.zpowers z)) : L → _))
    {f : Gal(L/K) × Gal(L/K) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsCoboundary₂ (fun q : Subgroup.zpowers z × Subgroup.zpowers z =>
      Additive.ofMul (f ((q.1 : Gal(L/K)), (q.2 : Gal(L/K))))) := by
  set N := Subgroup.zpowers z
  set σ : N := ⟨z, Subgroup.mem_zpowers z⟩
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  have hord : orderOf σ = orderOf z := Subgroup.orderOf_mk z _
  have hσ : ∀ g : N, ∃ i : ℕ, σ ^ i = g := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.mp (hfin.mem_powers_iff_mem_zpowers.mpr hg)
    exact ⟨k, Subtype.ext (by simpa [σ] using hk)⟩
  have hfc : IsCocycle₂ (fun q : N × N => Additive.ofMul (f ((q.1 : Gal(L/K)), (q.2 : Gal(L/K))))) :=
    fun g h j => hf g h j
  refine isCoboundary₂_of_cyclic hσ hfc (fun a ha => ?_)
  have hza : z ((a.toMul : Lˣ) : L) = ((a.toMul : Lˣ) : L) :=
    congrArg (fun u : Additive Lˣ => ((u.toMul : Lˣ) : L)) ha
  obtain ⟨y, hy⟩ := exists_prod_pow_eq z hsurj _ hza
  have hy0 : y ≠ 0 := by
    rintro rfl
    refine (a.toMul).ne_zero ?_
    rw [← hy]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hfin.orderOf_pos) (map_zero _)
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_sum, Units.coe_prod, hord, ← hy]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- Descent: a cocycle inflated from `Gal(L/K) ⧸ N` with values in `(Lˣ)^N` is a coboundary when
`Br(L^N / K) = 0`. -/
theorem isCoboundary₂_descend [IsGalois K L] (N : Subgroup Gal(L/K)) [N.Normal]
    {F : Gal(L/K) × Gal(L/K) → Additive Lˣ} (hF : IsCocycle₂ F)
    (hinv : ∀ g h : Gal(L/K), ∀ n ∈ N, F (g * n, h) = F (g, h) ∧ F (g, h * n) = F (g, h) ∧
      n • F (g, h) = F (g, h))
    (hE : ∀ fb : Gal(fixedField N/K) × Gal(fixedField N/K) → (fixedField N)ˣ, IsMulCocycle₂ fb →
      IsMulCoboundary₂ fb) :
    IsCoboundary₂ F := by
  set E := fixedField N
  set res := AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E
  have hres : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective L
  set lift := Function.surjInv hres
  have hlift : ∀ σ, res (lift σ) = σ := Function.surjInv_eq hres
  have hker : ∀ g g', res g = res g' → g⁻¹ * g' ∈ N := by
    intro g g' h
    have : g⁻¹ * g' ∈ res.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [IntermediateField.restrictNormalHom_ker, fixingSubgroup_fixedField] at this
    exact this
  have hFres : ∀ g g' h h', res g = res g' → res h = res h' → F (g, h) = F (g', h') := by
    intro g g' h h' hg hh
    rw [show g' = g * (g⁻¹ * g') by group, show h' = h * (h⁻¹ * h') by group,
      (hinv g _ _ (hker g g' hg)).1, (hinv g h _ (hker h h' hh)).2.1]
  have hval : ∀ g h, (((F (g, h)).toMul : Lˣ) : L) ∈ E := by
    intro g h
    rw [mem_fixedField_iff]
    intro n hn
    exact congrArg (fun u : Additive Lˣ => ((u.toMul : Lˣ) : L)) (hinv g h n hn).2.2
  let fb : Gal(E/K) × Gal(E/K) → Eˣ := fun q =>
    Units.mk0 ⟨(((F (lift q.1, lift q.2)).toMul : Lˣ) : L), hval _ _⟩
      (fun h0 => (F (lift q.1, lift q.2)).toMul.ne_zero (congrArg Subtype.val h0))
  have hact : ∀ (σ : Gal(E/K)) (e : E), ((σ e : E) : L) = (lift σ) (e : L) := by
    intro σ e
    conv_lhs => rw [← hlift σ]
    exact AlgEquiv.restrictNormalHom_apply E (lift σ) e
  have hfb : IsMulCocycle₂ fb := by
    intro σ τ ρ
    have e1 : F (lift (σ * τ), lift ρ) = F (lift σ * lift τ, lift ρ) :=
      hFres _ _ _ _ (by rw [map_mul, hlift, hlift, hlift]) rfl
    have e2 : F (lift σ, lift (τ * ρ)) = F (lift σ, lift τ * lift ρ) :=
      hFres _ _ _ _ rfl (by rw [map_mul, hlift, hlift, hlift])
    have key := congrArg (fun u : Additive Lˣ => ((u.toMul : Lˣ) : L)) (hF (lift σ) (lift τ) (lift ρ))
    apply Units.ext; apply Subtype.ext
    show (((F (lift (σ * τ), lift ρ)).toMul : Lˣ) : L) * (((F (lift σ, lift τ)).toMul : Lˣ) : L) =
      ((σ ((fb (τ, ρ) : Eˣ) : E) : E) : L) * (((F (lift σ, lift (τ * ρ))).toMul : Lˣ) : L)
    rw [hact, e1, e2]
    exact key
  obtain ⟨x, hx⟩ := hE fb hfb
  set ιu : Eˣ →* Lˣ := Units.map (algebraMap E L).toMonoidHom
  have hιu : ∀ (g : Gal(L/K)) (u : Eˣ), ιu ((res g : Gal(E/K)) • u : Eˣ) = g • ιu u := fun g u =>
    Units.ext (AlgEquiv.restrictNormalHom_apply E g (u : E))
  have hιf : ∀ σ τ, ιu (fb (σ, τ)) = (F (lift σ, lift τ)).toMul := fun _ _ => Units.ext rfl
  refine ⟨fun g => Additive.ofMul (ιu (x (res g))), fun g h => ?_⟩
  have := congrArg ιu (hx (res g) (res h))
  rw [map_mul, map_div, hιu, hιf, ← map_mul res g h,
    hFres (lift (res g)) g (lift (res h)) h (hlift _) (hlift _)] at this
  exact congrArg Additive.ofMul this

end Galois

/-- **`Br(L/K) = 0`** for a finite Galois `p`-extension `L` of a C1 field `K`: every multiplicative
2-cocycle `Gal(L/K)² → Lˣ` is a coboundary. -/
theorem br_eq_zero_aux {K : Type*} [Field K] (hK : IsC1 K) (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      Module.finrank K L ≤ n → IsPGroup p Gal(L/K) →
      ∀ f : Gal(L/K) × Gal(L/K) → Lˣ, IsMulCocycle₂ f → IsMulCoboundary₂ f := by
  induction n with
  | zero =>
    intro L _ _ _ _ hn
    have := Module.finrank_pos (R := K) (M := L)
    omega
  | succ n ih =>
    intro L _ _ _ _ hn hG f hf
    by_cases htriv : Subsingleton Gal(L/K)
    · refine ⟨fun _ => f (1, 1), fun g h => ?_⟩
      rw [Subsingleton.elim g 1, Subsingleton.elim h 1]
      simp
    rw [not_subsingleton_iff_nontrivial] at htriv
    -- a central element of order `p`
    have := hG.center_nontrivial
    have hc : p ∣ Nat.card (Subgroup.center Gal(L/K)) :=
      ((hG.to_subgroup _).card_eq_or_dvd).resolve_left Finite.one_lt_card.ne'
    obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' p hc
    set z : Gal(L/K) := (z0 : Gal(L/K))
    have hzc : z ∈ Subgroup.center Gal(L/K) := z0.2
    have hzp : orderOf z = p := by rw [Subgroup.orderOf_coe]; exact hz0
    set N := Subgroup.zpowers z
    have hNn : N.Normal := ⟨fun m hm g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
      have hcomm : Commute g z := Subgroup.mem_center_iff.mp hzc g
      rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers z k⟩
    set E := fixedField N
    have hE1 : IsC1 E := IsC1.of_finite hK
    have hsurj : Function.Surjective (Algebra.norm E : L → E) := IsC1.norm_surjective hE1
    -- degrees
    have hdeg : Module.finrank K E < Module.finrank K L := by
      have h1 := Module.finrank_mul_finrank K E L
      have h2 : Module.finrank E L = p := by
        rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hzp]
      have h3 := Module.finrank_pos (R := K) (M := E)
      have h4 := hp.out.two_le
      rw [h2] at h1
      nlinarith
    have hGE : IsPGroup p Gal(E/K) :=
      hG.of_surjective (AlgEquiv.restrictNormalHom E) (AlgEquiv.restrictNormalHom_surjective L)
    -- the three steps
    have hNf := isCoboundary₂_zpowers z hsurj hf
    obtain ⟨b, hbc, hbinv⟩ := exists_inflated N (isCocycle₂_ofMul hf) (h1_subgroup N) hNf
    apply isMulCoboundary₂_of_ofMul
    apply isCoboundary₂_of_sub b
    exact isCoboundary₂_descend N hbc hbinv (fun fb hfb => ih E (by omega) hGE fb hfb)

theorem br_eq_zero {K : Type*} [Field K] (hK : IsC1 K) (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (hG : IsPGroup p Gal(L/K))
    (f : Gal(L/K) × Gal(L/K) → Lˣ) (hf : IsMulCocycle₂ f) : IsMulCoboundary₂ f :=
  br_eq_zero_aux hK p _ L le_rfl hG f hf

end RamanujanPetersson.CdOne


end

-- ===== S4.Def_RP_CdOne_Emb =====
section

/-!
# S4-PD (3b): the central embedding problem with kernel `μ_l`

Let `E` be a C1 field containing a primitive `l`-th root of unity `ζ`, and `L/E` a finite Galois `l`-extension.
For a 2-cocycle `f : Gal(L/E)² → ZMod l` (trivial action), `Br(L/E) = 0` (`br_eq_zero`) gives `β : Gal(L/E) → Lˣ`
with `dβ = ζ^f`, and Hilbert 90 gives `b ∈ Lˣ` with `σ b / b = β(σ)^l` (`exists_kummer_data`). For any extension
`Ω ⊇ L` of `E` containing an `l`-th root `y` of `a·b` (`a ∈ Eˣ` free, used later to remove ramification), the
inflation of `f` to `Gal(Ω/E)` is the coboundary of `γ(σ) = log_ζ (β(σ|L) y / σ y)` (`emb_coboundary`), and `γ(σ)`
only depends on `σ|L` and `σ y`. `emb_solve` packages both steps.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CdOne

open groupCohomology IntermediateField RamanujanPetersson.Tsen

theorem pow_val_add {M : Type*} [Monoid M] {z : M} {l : ℕ} [NeZero l] (hz : z ^ l = 1) (a b : ZMod l) :
    z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) l, pow_add, pow_mul, hz, one_pow, mul_one]

theorem cg_key {G : Type*} [CommGroup G] (P Q R S U Y W : G) (hW : W = P * S / U) :
    U * (R * Y / S) = P / Q * R * (Q * Y / W) := by
  subst hW
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

theorem cg_pow {G : Type*} [CommGroup G] (X A B S : G) (hS : S = A * (X * B)) :
    X * (A * B) / S = 1 := by
  subst hS
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one]
  abel

section Kummer

variable {E : Type*} [Field E]

/-- The image of a nonzero `ζ : E` in `Lˣ`. -/
noncomputable def unitOf (L : Type*) [Field L] [Algebra E L] (ζ : E) (h : ζ ≠ 0) : Lˣ :=
  Units.mk0 (algebraMap E L ζ) ((map_ne_zero _).mpr h)

variable {L : Type*} [Field L] [Algebra E L]

theorem unitOf_val (ζ : E) (h : ζ ≠ 0) : ((unitOf L ζ h : Lˣ) : L) = algebraMap E L ζ := rfl

theorem smul_unitOf (σ : Gal(L/E)) (ζ : E) (h : ζ ≠ 0) : σ • unitOf L ζ h = unitOf L ζ h :=
  Units.ext (σ.commutes ζ)

/-- Step (i): `Br(L/E) = 0` and Hilbert 90 produce the Kummer data `(β, b)`. -/
theorem exists_kummer_data [FiniteDimensional E L] [IsGalois E L] (hE : IsC1 E) (l : ℕ) [Fact l.Prime]
    (hG : IsPGroup l Gal(L/E)) {ζ : E} (hζ : IsPrimitiveRoot ζ l) (hζ0 : ζ ≠ 0)
    (f : Gal(L/E) × Gal(L/E) → ZMod l) (hf : ∀ g h j, f (g * h, j) + f (g, h) = f (h, j) + f (g, h * j)) :
    ∃ (β : Gal(L/E) → Lˣ) (b : Lˣ),
      (∀ σ τ, σ • β τ / β (σ * τ) * β σ = unitOf L ζ hζ0 ^ (f (σ, τ)).val) ∧
        ∀ σ, σ • b / b = β σ ^ l := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hz : unitOf L ζ hζ0 ^ l = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, unitOf_val, ← map_pow, hζ.pow_eq_one, map_one, Units.val_one])
  have hc : IsMulCocycle₂ (fun q : Gal(L/E) × Gal(L/E) => unitOf L ζ hζ0 ^ (f q).val) := by
    intro g h j
    simp only
    rw [smul_pow', smul_unitOf, ← pow_val_add hz, ← pow_val_add hz, hf]
  obtain ⟨β, hβ⟩ := br_eq_zero hE l L hG _ hc
  have hφ : IsMulCocycle₁ (fun σ : Gal(L/E) => β σ ^ l) := by
    intro g h
    have h1 : (g • β h / β (g * h) * β g) ^ l = 1 := by
      rw [hβ g h, ← pow_mul, mul_comm, pow_mul, hz, one_pow]
    rw [mul_pow, div_pow, ← smul_pow', div_mul_eq_mul_div, div_eq_one] at h1
    exact h1.symm
  obtain ⟨b, hb⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hφ
  exact ⟨β, b, hβ, hb⟩

end Kummer

section Emb

variable {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]

end Emb
end RamanujanPetersson.CdOne

end


