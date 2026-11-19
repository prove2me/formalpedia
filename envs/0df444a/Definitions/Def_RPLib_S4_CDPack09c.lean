-- Prove2me | Definitions.Def_RPLib_S4_CDPack09c
-- name    : RPLib_S4_CDPack09c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:24:24.739677+00:00
-- url     : https://prove2.me/theorems/1cbbdbe5-0c26-49bb-bc5e-da850b93003a
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 9c of 71
-- statement:
--   Part 9c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CP4a_Bres`: S4-CP4a, part e3a: the constant residue map of a boundary prime
--   * `Def_RP_CP4a_Bdry`: S4-CP4a, part e3b: fixed boundary points of the true Frobenius permutation (generic chart `R0`)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack09

/-!
# Curve-duality library package, part 9c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CP4a_Bres`: S4-CP4a, part e3a: the constant residue map of a boundary prime
* `Def_RP_CP4a_Bdry`: S4-CP4a, part e3b: fixed boundary points of the true Frobenius permutation (generic chart `R0`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_Bres =====
section

/-!
# S4-CP4a, part e3a: the constant residue map of a boundary prime

* `exists_frob_pow_of_finite`: two embeddings of a finite field `k ⊇ k0` into a field that agree on `k0`
  differ by a power of the `#k0`-Frobenius.
* `bres Q hQ : R0 →+* K_U`: `r ↦` the constant congruent to `r` modulo the boundary prime `Q` (via `resEquiv`),
  with `bres_spec`, `bres_eq`, `bres_isConst`, `bres_ker`, `bres_const`.
* Transport: `bres_smul` (`bres (σ Q) = σ ∘ bres Q`), `bres_geo` (`π₁^geo` does not change it), `bres_frob_pow`
  (`bres (φ^j Q) = Frob_q^j ∘ bres Q` for a Frobenius lift `φ`).
* `bres_conj`: equal residue maps force `π₁^geo`-conjugate primes (`exists_pi1geo_smul`).
* `exists_bres_eq`: every `k0`-compatible `χ : R0 →+* K_U` with nonzero kernel is `bres Q` of a boundary prime
  (lying over, `exists_frob_pow_of_finite`, then `φ^j`).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

open scoped Pointwise

noncomputable section

section FinFrob

/-- Two embeddings of a finite field `k ⊇ k0` into a field that agree on `k0` differ by a power of the
`#k0`-Frobenius. -/
theorem exists_frob_pow_of_finite {k0 k M : Type} [Field k0] [Fintype k0] [Field k] [Finite k] [Algebra k0 k]
    [Field M] (f g : k →+* M) (hfg : ∀ a : k0, f (algebraMap k0 k a) = g (algebraMap k0 k a)) :
    ∃ j : ℕ, ∀ x, g x = f x ^ (Fintype.card k0 ^ j) := by
  classical
  let _ : Fintype k := Fintype.ofFinite k
  have hn1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hX : (X ^ Fintype.card k - X : M[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero M hn1
  have hroot : ∀ (u : k →+* M) (x : k), u x ∈ (X ^ Fintype.card k - X : M[X]).roots.toFinset := by
    intro u x
    rw [Multiset.mem_toFinset, mem_roots hX, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow,
      FiniteField.pow_card, sub_self]
  have hsub : Finset.univ.image f ⊆ (X ^ Fintype.card k - X : M[X]).roots.toFinset := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    exact hroot f x
  have hcard : (X ^ Fintype.card k - X : M[X]).roots.toFinset.card ≤ (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ]
    calc _ ≤ Multiset.card (X ^ Fintype.card k - X : M[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ Fintype.card k - X : M[X]).natDegree := card_roots' _
      _ = Fintype.card k := FiniteField.X_pow_card_sub_X_natDegree_eq M hn1
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hg : ∀ x, ∃ y, f y = g x := by
    intro x
    have h := hroot g x
    rw [← heq] at h
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h
    exact ⟨y, hy⟩
  choose h hh using hg
  let hA : k →ₐ[k0] k :=
    { toFun := h
      map_one' := f.injective (by rw [hh, map_one, map_one])
      map_mul' := fun x y => f.injective (by rw [hh, map_mul, map_mul, hh, hh])
      map_zero' := f.injective (by rw [hh, map_zero, map_zero])
      map_add' := fun x y => f.injective (by rw [hh, map_add, map_add, hh, hh])
      commutes' := fun a => f.injective (by rw [hh, hfg]) }
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgHom_pow k0 k).2 hA
  refine ⟨j.1, fun x => ?_⟩
  have hx : (FiniteField.frobeniusAlgHom k0 k ^ j.1) x = hA x := DFunLike.congr_fun hj x
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate] at hx
  rw [← hh x]
  change f (hA x) = _
  rw [← hx, map_pow]

end FinFrob

section Bres

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
  {p e : ℕ} [hp : Fact p.Prime] [CharP K p] (he : 0 < e)
  (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
  (hgood : ∀ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q →
    Finite (R0 ⧸ Q.under R0) ∧ ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)

/-- The constant residue map at a boundary prime `Q`: `r ↦` the constant congruent to `r` mod `Q`. -/
def bres (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) : R0 →+* maxUnram A K :=
  haveI := hQ.1
  haveI := (hgood Q hQ).1
  ((integralClosure R0 (maxUnram A K)).val.toRingHom.comp (constSub A K R0 p e).subtype).comp
    ((resEquiv A K R0 p e he hζ Q (hgood Q hQ).2).symm.toRingHom.comp
      ((Ideal.Quotient.mk Q).comp (algebraMap R0 (proChart A K R0))))

theorem bres_spec (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    ∃ c ∈ constSub A K R0 p e, ((c : proChart A K R0) : maxUnram A K) = bres he hζ hgood Q hQ r ∧
      algebraMap R0 (proChart A K R0) r - c ∈ Q := by
  haveI := hQ.1
  haveI := (hgood Q hQ).1
  refine ⟨((resEquiv A K R0 p e he hζ Q (hgood Q hQ).2).symm
    (Ideal.Quotient.mk Q (algebraMap R0 (proChart A K R0) r)) : proChart A K R0), Subtype.prop _, rfl, ?_⟩
  have h := (resEquiv A K R0 p e he hζ Q (hgood Q hQ).2).apply_symm_apply
    (Ideal.Quotient.mk Q (algebraMap R0 (proChart A K R0) r))
  rw [resEquiv_apply] at h
  exact Ideal.Quotient.eq.1 h.symm

theorem bres_eq (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) {r : R0} {c : proChart A K R0}
    (hc : c ∈ constSub A K R0 p e) (h : algebraMap R0 (proChart A K R0) r - c ∈ Q) :
    bres he hζ hgood Q hQ r = (c : maxUnram A K) := by
  obtain ⟨c0, hc0, h0, h0Q⟩ := bres_spec he hζ hgood Q hQ r
  rw [← h0]
  have h1 : c0 - c ∈ Q := by
    have h2 := Q.sub_mem h h0Q
    rwa [sub_sub_sub_cancel_left] at h2
  rw [const_eq_of_sub_mem he hQ.1.ne_top hc0 hc h1]

theorem bres_congr {Q Q' : Ideal (proChart A K R0)} (hQQ : Q = Q') (hQ : IsBdryPrime A K R0 Q)
    (hQ' : IsBdryPrime A K R0 Q') : bres he hζ hgood Q hQ = bres he hζ hgood Q' hQ' := by
  subst hQQ
  rfl

theorem bres_isConst (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    IsConst (p ^ e) (bres he hζ hgood Q hQ r) := by
  obtain ⟨c, hc, hcr, -⟩ := bres_spec he hζ hgood Q hQ r
  rw [← hcr]
  exact hc

theorem bres_ker (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    bres he hζ hgood Q hQ r = 0 ↔ r ∈ Q.under R0 := by
  constructor
  · intro h
    obtain ⟨c, -, hcr, hcQ⟩ := bres_spec he hζ hgood Q hQ r
    have hc0 : c = 0 := Subtype.ext (hcr.trans h)
    rw [hc0, sub_zero] at hcQ
    exact hcQ
  · intro h
    have h2 := bres_eq he hζ hgood Q hQ (zero_mem (constSub A K R0 p e)) (r := r) (by rw [sub_zero]; exact h)
    rw [h2]
    rfl

theorem bres_const (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) {r : R0}
    (hr : IsConst (p ^ e) (algebraMap R0 (maxUnram A K) r)) :
    bres he hζ hgood Q hQ r = algebraMap R0 (maxUnram A K) r := by
  have h2 := bres_eq he hζ hgood Q hQ (c := algebraMap R0 (proChart A K R0) r) hr (by rw [sub_self]; exact zero_mem _)
  rw [h2]
  rfl

theorem bres_smul (σ : Pi1 A K) (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    bres he hζ hgood (σ • Q) (isBdryPrime_smul A K R0 σ hQ) r = σ (bres he hζ hgood Q hQ r) := by
  obtain ⟨c, hc, hcr, hcQ⟩ := bres_spec he hζ hgood Q hQ r
  rw [← hcr]
  have h2 := Ideal.smul_mem_pointwise_smul σ _ Q hcQ
  rw [smul_sub, smul_algebraMap] at h2
  exact bres_eq he hζ hgood (σ • Q) _ ((mem_constSub.1 hc).map σ) h2

theorem bres_geo {g : Pi1 A K} (hg : g ∈ pi1geo A K (p ^ e)) (Q : Ideal (proChart A K R0))
    (hQ : IsBdryPrime A K R0 Q) :
    bres he hζ hgood (g • Q) (isBdryPrime_smul A K R0 g hQ) = bres he hζ hgood Q hQ :=
  RingHom.ext fun r => (bres_smul he hζ hgood g Q hQ r).trans
    ((mem_pi1geo A K _ g).1 hg _ (bres_isConst he hζ hgood Q hQ r))

theorem bres_frob {φ : Pi1 A K} (hφ : IsFrobLift A K (p ^ e) φ) (Q : Ideal (proChart A K R0))
    (hQ : IsBdryPrime A K R0 Q) (r : R0) :
    bres he hζ hgood (φ • Q) (isBdryPrime_smul A K R0 φ hQ) r = bres he hζ hgood Q hQ r ^ (p ^ e) :=
  (bres_smul he hζ hgood φ Q hQ r).trans (hφ _ (bres_isConst he hζ hgood Q hQ r))

set_option synthInstance.maxHeartbeats 200000 in
theorem bres_frob_pow {φ : Pi1 A K} (hφ : IsFrobLift A K (p ^ e) φ) (Q : Ideal (proChart A K R0))
    (hQ : IsBdryPrime A K R0 Q) (j : ℕ) (r : R0) :
    bres he hζ hgood (φ ^ j • Q) (isBdryPrime_smul A K R0 _ hQ) r = bres he hζ hgood Q hQ r ^ ((p ^ e) ^ j) := by
  induction j with
  | zero =>
    rw [bres_congr he hζ hgood ((congrArg (fun g : Pi1 A K => g • Q) (pow_zero φ)).trans (one_smul (Pi1 A K) Q)) _ hQ, pow_zero, pow_one]
  | succ j ih =>
    rw [bres_congr he hζ hgood ((congrArg (fun g : Pi1 A K => g • Q) (pow_succ' φ j)).trans (mul_smul φ (φ ^ j) Q)) _
      (isBdryPrime_smul A K R0 φ (isBdryPrime_smul A K R0 _ hQ)),
      bres_frob he hζ hgood hφ (φ ^ j • Q) (isBdryPrime_smul A K R0 _ hQ), ih, ← pow_mul,
      pow_succ]

set_option synthInstance.maxHeartbeats 200000 in
theorem bres_conj (Q Q' : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q) (hQ' : IsBdryPrime A K R0 Q')
    (h : bres he hζ hgood Q hQ = bres he hζ hgood Q' hQ') : ∃ g ∈ pi1geo A K (p ^ e), Q' = g • Q := by
  haveI := hQ.1
  haveI := hQ'.1
  haveI := (hgood Q hQ).1
  refine exists_pi1geo_smul he hζ (hgood Q hQ).2 fun r c hc hrc => ?_
  obtain ⟨c', -, hc'r, hc'Q⟩ := bres_spec he hζ hgood Q' hQ' r
  have hcc : c' = c := Subtype.ext (hc'r.trans ((RingHom.congr_fun h r).symm.trans
    (bres_eq he hζ hgood Q hQ hc hrc)))
  rw [← hcc]
  exact hc'Q

theorem algebraMap_proChart_injective : Function.Injective (algebraMap R0 (proChart A K R0)) := by
  intro x y hxy
  have h1 : algebraMap R0 (maxUnram A K) x = algebraMap R0 (maxUnram A K) y := congrArg Subtype.val hxy
  rw [IsScalarTower.algebraMap_apply R0 K (maxUnram A K), IsScalarTower.algebraMap_apply R0 K (maxUnram A K) y] at h1
  exact IsFractionRing.injective R0 K ((algebraMap K (maxUnram A K)).injective h1)

set_option synthInstance.maxHeartbeats 200000 in
/-- **Surjectivity**: a `k0`-compatible `χ : R0 →+* K_U` with nonzero kernel is the residue map of a boundary
prime. -/
theorem exists_bres_eq {φ : Pi1 A K} (hφ : IsFrobLift A K (p ^ e) φ) {k0 : Type} [Field k0] [Fintype k0]
    [Algebra k0 R0] (hq0 : Fintype.card k0 = p ^ e) (χ : R0 →+* maxUnram A K)
    (hχ : ∀ a : k0, χ (algebraMap k0 R0 a) = algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a))
    (hker : RingHom.ker χ ≠ ⊥) :
    ∃ (Q : Ideal (proChart A K R0)) (hQ : IsBdryPrime A K R0 Q), bres he hζ hgood Q hQ = χ := by
  have hinj := algebraMap_proChart_injective (A := A) (K := K) (R0 := R0)
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨Q, -, hQp, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker χ)
    (⊥ : Ideal (proChart A K R0)) (fun x hx => by
      have h0 : algebraMap R0 (proChart A K R0) x = 0 := Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)
      rw [hinj (h0.trans (map_zero _).symm)]
      exact zero_mem _)
  have hQ : IsBdryPrime A K R0 Q := ⟨hQp, fun h0 => hker (by
    rw [← hQP, h0]
    ext x
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩)⟩
  haveI := hQp
  haveI := (hgood Q hQ).1
  have hunder : Q.under R0 = RingHom.ker χ := hQP
  haveI : (Q.under R0).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R0 ⧸ Q.under R0))
  letI := Ideal.Quotient.field (Q.under R0)
  have hconst : ∀ a : k0, IsConst (p ^ e) (algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a)) := fun a =>
    ⟨1, one_pos, by rw [pow_one, ← map_pow, ← map_pow, ← hq0, FiniteField.pow_card]⟩
  have H1 : ∀ a ∈ Q.under R0, bres he hζ hgood Q hQ a = 0 := fun a ha => (bres_ker he hζ hgood Q hQ a).2 ha
  have H2 : ∀ a ∈ Q.under R0, χ a = 0 := fun a ha => (RingHom.mem_ker).1 (hunder ▸ ha)
  have hfg : ∀ a : k0, Ideal.Quotient.lift (Q.under R0) (bres he hζ hgood Q hQ) H1
      (algebraMap k0 (R0 ⧸ Q.under R0) a) = Ideal.Quotient.lift (Q.under R0) χ H2 (algebraMap k0 (R0 ⧸ Q.under R0) a) := by
    intro a
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, hχ,
      bres_const he hζ hgood Q hQ (hconst a)]
  obtain ⟨j, hj⟩ := exists_frob_pow_of_finite _ _ hfg
  refine ⟨φ ^ j • Q, isBdryPrime_smul A K R0 _ hQ, RingHom.ext fun r => ?_⟩
  rw [bres_frob_pow he hζ hgood hφ Q hQ j r]
  have h3 := hj (Ideal.Quotient.mk _ r)
  rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk, hq0] at h3
  exact h3.symm

end Bres

end

end RamanujanPetersson.CP4a

end

-- ===== S4.Def_RP_CP4a_Bdry =====
section

/-!
# S4-CP4a, part e3b: fixed boundary points of the true Frobenius permutation (generic chart `R0`)

* `trueTau D ψ`, `trueH D ψ`, `trueTau_spec` (`ψ⁻¹ • P s = h_s • P (τ s)`), `trueCompat`: the boundary permutation of
  `ψ` WITH its defining property (`BdryData.frobTau` is a bare choice without it).
* `sres D s := bres (P s)`: injective (`sres_injective`); `sres (τ s) = (sres s)^q` for `ψ = φ⁻¹` (`sres_trueTau`).
* `iterate_trueTau_eq_iff`: `τ^m s = s ↔ sres s` has values in `𝔽_{q^m}`.
* `levelField k0 M m` (`x^{q^m} = x`), `card_levelField`, `finrank_levelField` (`= m`).
* `card_fix_eq`: `#{s | τ^m s = s} = #Hom_{k0}(R0, 𝔽_{q^m})`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CP4a

open CurveCoh GalCover Kummer

open scoped Pointwise

noncomputable section

section True

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ}
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  {S : Type} (D : BdryData A K q R0 S)

theorem bdry_exists_true (ψ : Pi1 A K) (s : S) :
    ∃ t, ∃ g ∈ pi1geo A K q, ψ⁻¹ • D.P s = g • D.P t :=
  D.cover _ (D.B_smul ψ⁻¹ _ (D.mem s))

/-- The boundary permutation of `ψ`, with its defining property `trueTau_spec`. -/
def trueTau (ψ : Pi1 A K) : S → S := fun s => (bdry_exists_true D ψ s).choose

/-- The correcting elements of `trueTau`. -/
def trueH (ψ : Pi1 A K) : S → pi1geo A K q := fun s =>
  ⟨(bdry_exists_true D ψ s).choose_spec.choose, (bdry_exists_true D ψ s).choose_spec.choose_spec.1⟩

theorem trueTau_spec (ψ : Pi1 A K) (s : S) :
    ψ⁻¹ • D.P s = ((trueH D ψ s : pi1geo A K q) : Pi1 A K) • D.P (trueTau D ψ s) :=
  (bdry_exists_true D ψ s).choose_spec.choose_spec.2

theorem trueCompat (ψ : Pi1 A K) : BdryCompat (pi1geo A K q) D.inertia ψ (trueTau D ψ) (trueH D ψ) := by
  intro s x hx
  have hx' : (x : Pi1 A K) ∈ (D.P s).inertia (Pi1 A K) := hx
  have h1 := conj_mem_inertia_smul A K R0 ψ⁻¹ hx'
  rw [inv_inv] at h1
  exact inv_conj_mem_inertia A K R0 (trueTau_spec D ψ s) h1

end True

section Level

variable (k0 M : Type) [Field k0] [Fintype k0] [Field M] [Algebra k0 M]

/-- `𝔽_{q^m}` inside `M`: the solutions of `x^{q^m} = x`, `q = #k0`. -/
def levelField (m : ℕ) : IntermediateField k0 M :=
  Subalgebra.toIntermediateField (AlgHom.equalizer (FiniteField.frobeniusAlgHom k0 M ^ m) (AlgHom.id k0 M))
    (fun x hx => by
      rw [AlgHom.mem_equalizer] at hx ⊢
      rw [map_inv₀, hx]
      rfl)

variable {k0 M}

theorem mem_levelField {m : ℕ} {x : M} : x ∈ levelField k0 M m ↔ x ^ (Fintype.card k0 ^ m) = x := by
  show x ∈ AlgHom.equalizer _ _ ↔ _
  rw [AlgHom.mem_equalizer, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]
  rfl

theorem card_levelField {m : ℕ} (hm : 0 < m) {ζ : M} (hζ : IsPrimitiveRoot ζ (Fintype.card k0 ^ m - 1)) :
    Nat.card (levelField k0 M m) = Fintype.card k0 ^ m := by
  classical
  have hq1 : 1 < Fintype.card k0 ^ m := Nat.one_lt_pow hm.ne' Fintype.one_lt_card
  have hn : 0 < Fintype.card k0 ^ m - 1 := by omega
  have hset : ((levelField k0 M m : Set M)) =
      ↑(insert 0 (nthRootsFinset (Fintype.card k0 ^ m - 1) (1 : M))) := by
    ext x
    simp only [SetLike.mem_coe, Finset.coe_insert, Set.mem_insert_iff, mem_nthRootsFinset hn,
      mem_levelField]
    constructor
    · intro hx
      by_cases h0 : x = 0
      · exact Or.inl h0
      · exact Or.inr (pow_pred_eq_one hq1.le hx h0)
    · rintro (h0 | h1)
      · rw [h0, zero_pow (by omega)]
      · calc x ^ Fintype.card k0 ^ m = x ^ (Fintype.card k0 ^ m - 1) * x := by
              rw [← pow_succ, Nat.sub_add_cancel hq1.le]
          _ = x := by rw [h1, one_mul]
  have h0 : (0 : M) ∉ nthRootsFinset (Fintype.card k0 ^ m - 1) (1 : M) := by
    rw [mem_nthRootsFinset hn, zero_pow (by omega)]
    exact zero_ne_one
  have hc : Nat.card (levelField k0 M m) = Nat.card ((levelField k0 M m : Set M)) := rfl
  rw [hc, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_insert_of_notMem h0,
    IsPrimitiveRoot.card_nthRootsFinset hζ]
  omega

theorem finrank_levelField {m : ℕ} (hm : 0 < m) {ζ : M} (hζ : IsPrimitiveRoot ζ (Fintype.card k0 ^ m - 1)) :
    Module.finrank k0 (levelField k0 M m) = m := by
  have hc := card_levelField hm hζ
  have : Finite (levelField k0 M m) := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  let _ : Fintype (levelField k0 M m) := Fintype.ofFinite _
  have h2 := Module.card_eq_pow_finrank (K := k0) (V := levelField k0 M m)
  rw [← Nat.card_eq_fintype_card, hc] at h2
  exact (Nat.pow_right_injective (Fintype.one_lt_card (α := k0)) h2).symm

/-- A `k0`-compatible ring hom with values in `𝔽_{q^m}`, as a `k0`-algebra hom. -/
def toLevelHom {R0 : Type} [CommRing R0] [Algebra k0 R0] {m : ℕ} (χ : R0 →+* M)
    (hmem : ∀ r, χ r ∈ levelField k0 M m) (hχ : ∀ a, χ (algebraMap k0 R0 a) = algebraMap k0 M a) :
    R0 →ₐ[k0] levelField k0 M m :=
  { χ.codRestrict (levelField k0 M m) hmem with commutes' := fun a => Subtype.ext (hχ a) }

end Level


section Sres

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
  [IsDomain R0] [IsIntegrallyClosed R0] [IsFractionRing R0 K]
  {p e : ℕ} [Fact p.Prime] [CharP K p] (he : 0 < e)
  (hζ : ∀ a, 0 < a → ∃ ζ : maxUnram A K, IsPrimitiveRoot ζ ((p ^ e) ^ a - 1))
  (hgood : ∀ Q : Ideal (proChart A K R0), IsBdryPrime A K R0 Q →
    Finite (R0 ⧸ Q.under R0) ∧ ∃ d, Nat.card (R0 ⧸ Q.under R0) = (p ^ e) ^ d)
  {q : ℕ} {S : Type} (D : BdryData A K q R0 S) (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q)

/-- The residue map at the boundary point `s`. -/
def sres (s : S) : R0 →+* maxUnram A K :=
  bres he hζ hgood (D.P s) ((hDB _).1 (D.mem s))

set_option synthInstance.maxHeartbeats 200000 in
theorem sres_injective (hq : q = p ^ e) : Function.Injective (sres he hζ hgood D hDB) := by
  subst hq
  intro s t hst
  obtain ⟨g, hg, hgt⟩ := bres_conj he hζ hgood _ _ ((hDB _).1 (D.mem s)) ((hDB _).1 (D.mem t)) hst
  exact D.disj s t g hg hgt

set_option synthInstance.maxHeartbeats 200000 in
/-- `sres (τ s) = Frob_q ∘ sres s` for the true boundary permutation of `φ⁻¹`. -/
theorem sres_trueTau (hq : q = p ^ e) {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) (s : S) (r : R0) :
    sres he hζ hgood D hDB (trueTau D φ⁻¹ s) r = sres he hζ hgood D hDB s r ^ q := by
  subst hq
  have hs := (hDB _).1 (D.mem s)
  have ht := (hDB _).1 (D.mem (trueTau D φ⁻¹ s))
  have h1 := bres_geo he hζ hgood (trueH D φ⁻¹ s).2 (D.P (trueTau D φ⁻¹ s)) ht
  have h2 : ((trueH D φ⁻¹ s : pi1geo A K (p ^ e)) : Pi1 A K) • D.P (trueTau D φ⁻¹ s) = φ • D.P s :=
    (trueTau_spec D φ⁻¹ s).symm.trans (congrArg (fun g : Pi1 A K => g • D.P s) (inv_inv φ))
  have h3 := bres_congr he hζ hgood h2 (isBdryPrime_smul A K R0 _ ht) (isBdryPrime_smul A K R0 φ hs)
  show bres he hζ hgood (D.P (trueTau D φ⁻¹ s)) ht r = bres he hζ hgood (D.P s) hs r ^ (p ^ e)
  rw [← h1, h3, bres_frob he hζ hgood hφ (D.P s) hs]

theorem sres_iterate (hq : q = p ^ e) {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) (m : ℕ) (s : S) (r : R0) :
    sres he hζ hgood D hDB ((trueTau D φ⁻¹)^[m] s) r = sres he hζ hgood D hDB s r ^ (q ^ m) := by
  induction m with
  | zero => rw [Function.iterate_zero_apply, pow_zero, pow_one]
  | succ m ih =>
    rw [Function.iterate_succ_apply', sres_trueTau he hζ hgood D hDB hq hφ, ih, ← pow_mul, pow_succ]

/-- `τ^m s = s` iff the residue map at `s` has values in `𝔽_{q^m}`. -/
theorem iterate_trueTau_eq_iff (hq : q = p ^ e) {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) (m : ℕ) (s : S) :
    (trueTau D φ⁻¹)^[m] s = s ↔
      ∀ r, sres he hζ hgood D hDB s r ^ (q ^ m) = sres he hζ hgood D hDB s r := by
  constructor
  · intro h r
    rw [← sres_iterate he hζ hgood D hDB hq hφ m s r, h]
  · intro h
    apply sres_injective he hζ hgood D hDB hq
    ext r
    rw [sres_iterate he hζ hgood D hDB hq hφ m s r, h r]

include he hζ hgood hDB in
set_option synthInstance.maxHeartbeats 200000 in
/-- **`#{s | τ^m s = s} = #Hom_{k0}(R0, 𝔽_{q^m})`** for the true boundary permutation of `φ⁻¹`. -/
theorem card_fix_eq (hq : q = p ^ e) {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) {k0 : Type} [Field k0]
    [Fintype k0] [Algebra k0 R0] [Algebra k0 (maxUnram A K)] (hq0 : Fintype.card k0 = q)
    (hcomp : ∀ a : k0, algebraMap k0 (maxUnram A K) a = algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a))
    (r0 : R0) (hr0 : ∀ N : ℕ, 2 ≤ N → r0 ^ N ≠ r0) [Fintype S] [DecidableEq S] (m : ℕ) (hm : 0 < m) :
    (Finset.univ.filter fun s => (trueTau D φ⁻¹)^[m] s = s).card =
      Nat.card (R0 →ₐ[k0] levelField k0 (maxUnram A K) m) := by
  have hmem : ∀ s, (trueTau D φ⁻¹)^[m] s = s → ∀ r,
      sres he hζ hgood D hDB s r ∈ levelField k0 (maxUnram A K) m := fun s hs r =>
    mem_levelField.2 (by rw [hq0]; exact (iterate_trueTau_eq_iff he hζ hgood D hDB hq hφ m s).1 hs r)
  have hconstR : ∀ a : k0, IsConst (p ^ e) (algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a)) := by
    intro a
    rw [← hcomp]
    exact ⟨1, one_pos, by rw [pow_one, ← hq, ← hq0, ← map_pow, FiniteField.pow_card]⟩
  have hconst : ∀ s a, sres he hζ hgood D hDB s (algebraMap k0 R0 a) = algebraMap k0 (maxUnram A K) a := by
    intro s a
    show bres he hζ hgood (D.P s) ((hDB _).1 (D.mem s)) (algebraMap k0 R0 a) = _
    rw [bres_const he hζ hgood (D.P s) ((hDB _).1 (D.mem s)) (hconstR a), hcomp]
  let Φ : {s // (trueTau D φ⁻¹)^[m] s = s} → (R0 →ₐ[k0] levelField k0 (maxUnram A K) m) :=
    fun s => toLevelHom (sres he hζ hgood D hDB s.1) (hmem s.1 s.2) (hconst s.1)
  have hinj : Function.Injective Φ := by
    intro s t hst
    apply Subtype.ext
    apply sres_injective he hζ hgood D hDB hq
    apply RingHom.ext
    intro r
    exact congrArg (fun f : R0 →ₐ[k0] levelField k0 (maxUnram A K) m =>
      ((f r : levelField k0 (maxUnram A K) m) : maxUnram A K)) hst
  have hsurj : Function.Surjective Φ := by
    intro ψ
    let χ : R0 →+* maxUnram A K := ((levelField k0 (maxUnram A K) m).val.comp ψ).toRingHom
    have hχ : ∀ a : k0, χ (algebraMap k0 R0 a) = algebraMap R0 (maxUnram A K) (algebraMap k0 R0 a) := by
      intro a
      rw [← hcomp]
      exact ((levelField k0 (maxUnram A K) m).val.comp ψ).commutes a
    have hχmem : ∀ r, χ r ∈ levelField k0 (maxUnram A K) m := fun r => (ψ r).2
    have hker : RingHom.ker χ ≠ ⊥ := by
      intro h0
      have hinjχ : Function.Injective χ := (RingHom.injective_iff_ker_eq_bot χ).2 h0
      have h1q : 1 < q := by rw [← hq0]; exact Fintype.one_lt_card
      have hq1 : 2 ≤ q ^ m :=
        calc 2 ≤ q := h1q
          _ = q ^ 1 := (pow_one q).symm
          _ ≤ q ^ m := Nat.pow_le_pow_right (by omega) hm
      apply hr0 (q ^ m) hq1
      apply hinjχ
      rw [map_pow]
      have h := mem_levelField.1 (hχmem r0)
      rwa [hq0] at h
    have hφ' : IsFrobLift A K (p ^ e) φ := by rw [← hq]; exact hφ
    obtain ⟨Q, hQ, hQχ⟩ := exists_bres_eq he hζ hgood hφ' (hq0.trans hq) χ hχ hker
    obtain ⟨s, g, hg, hQs⟩ := D.cover Q ((hDB Q).2 hQ)
    have hg' : g ∈ pi1geo A K (p ^ e) := by rw [← hq]; exact hg
    have hs := (hDB _).1 (D.mem s)
    have hsχ : sres he hζ hgood D hDB s = χ :=
      ((bres_geo he hζ hgood hg' (D.P s) hs).symm.trans
        (bres_congr he hζ hgood hQs hQ (isBdryPrime_smul A K R0 g hs)).symm).trans hQχ
    have hfix : (trueTau D φ⁻¹)^[m] s = s := by
      rw [iterate_trueTau_eq_iff he hζ hgood D hDB hq hφ m s]
      intro r
      rw [hsχ, ← hq0]
      exact mem_levelField.1 (hχmem r)
    refine ⟨⟨s, hfix⟩, ?_⟩
    apply AlgHom.ext
    intro r
    apply Subtype.ext
    show sres he hζ hgood D hDB s r = ((ψ r : levelField k0 (maxUnram A K) m) : maxUnram A K)
    exact (RingHom.congr_fun hsχ r).trans rfl
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)

end Sres

end

end RamanujanPetersson.CP4a

end


