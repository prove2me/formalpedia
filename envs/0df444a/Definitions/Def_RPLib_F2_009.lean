-- Prove2me | Definitions.Def_RPLib_F2_009
-- name    : RPLib_F2_009
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T07:34:08.222199+00:00
-- url     : https://prove2.me/theorems/75fea605-5b29-4be1-8ef5-b7fb44423fe1
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 009 of 70
-- statement:
--   File 009 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_GenFib`: S4-JacLaw, file O9c (G3 Fib): sections `q(x)` with reduced zero sets
--   * `S4.Def_RP_JacSymA_A`: S4-JacSymA, file A: the coordinate ring of `X^g`, the `S_g`-action and the chart `Sym^g`
--   * `S4.Def_RP_JacSymA_B`: S4-JacSymA, file B: the `k`-points of the chart `Sym^g X` (lemma L8 of S4_COREB_ROUTE.md)
--   * `S4.Def_RP_JacSymA_C`: S4-JacSymA, file C: points of the chart are effective divisors (L8, divisor form)
--   * `S4.Def_RP_JacSymA_D`: S4-JacSymA, file D: `X^g` is integral
--   * `S4.Def_RP_JacSymB_Poly`: S4-JacSymB, file A (L10): `Sym^g A^1 = A^g`
--   * `S4.Def_RP_JacSymB_Map`: S4-JacSymB, file B: functoriality of `X^g` and `Sym^g`; surjections stay surjective on invariants
--   * `S4.Def_RP_JacSymB_Noeth`: S4-JacSymB, file C: finiteness of `X^g` and `Sym^g X`; points of `A^g`
--   * `S4.Def_RP_JacSymB_SymLoc`: S4-JacSymB, file F4: `Sym^g` commutes with localization at a norm (L12)
--   * `S4.Def_RP_JacLaw_Span`: S4-JacLaw, file O1: `Sym^g(B)` is spanned by norms (polarization over an infinite field)
--   * `S4.Def_RP_JacSymB_GenPoly`: S4-JacSymB, file H2b: the generic polynomial `E(w) = ∏_l (1 - w_l X)` (L12, valuative criterion)
--   * `S4.Def_RP_JacLaw_Crit`: S4-JacLaw, file O2: the morphism criterion for maps into `Sym^n`
--   * `S4.Def_RP_JacLaw_LinAlg`: S4-JacLaw, file O3: linear algebra for the negation step
--   * `S4.Def_RP_JacLaw_Gram`: S4-JacLaw O5: the trace matrix of a point of `Sym^d` and its kernel line
--   * `S4.Def_RP_JacLaw_Pres`: S4-JacLaw, file O4b: the Δ-ratio presentation of `B ⧸ (s)`
--   * `S4.Def_RP_JacLaw_Fam`: S4-JacLaw, file O6b: the Δ-ratio presentation in families
--   * `S4.Def_RP_JacLaw_Diag`: S4-JacLaw, file O4a: diagonalising a finite commutative algebra by one element
--   * `S4.Def_RP_JacLaw_MonPts`: S4-JacLaw, file O6c: monic generic polynomial, the zero set of a section, exact division
--   * `S4.Def_RP_JacLaw_Good`: S4-JacLaw, file O6d-1: choice data for `ν` and the good open `D(good)` of `Sym^d`
--   * `S4.Def_RP_JacLaw_Nu`: S4-JacLaw, file O6d-2: the negation map `ν : D(good) → Sym^g`
--   * `S4.Def_RP_JacLaw_Add`: S4-JacLaw, file O7: addition `Sym^d × Sym^e → Sym^(d+e)`
--   * `S4.Def_RP_JacLaw_Uniq`: S4-JacLaw, file O8a: uniqueness of `ν`, supports of points, padding and sum maps
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_006

/-!
# Ramanujan-Petersson curve library (flat edition), file 009 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_GenFib`: S4-JacLaw, file O9c (G3 Fib): sections `q(x)` with reduced zero sets
* `S4.Def_RP_JacSymA_A`: S4-JacSymA, file A: the coordinate ring of `X^g`, the `S_g`-action and the chart `Sym^g`
* `S4.Def_RP_JacSymA_B`: S4-JacSymA, file B: the `k`-points of the chart `Sym^g X` (lemma L8 of S4_COREB_ROUTE.md)
* `S4.Def_RP_JacSymA_C`: S4-JacSymA, file C: points of the chart are effective divisors (L8, divisor form)
* `S4.Def_RP_JacSymA_D`: S4-JacSymA, file D: `X^g` is integral
* `S4.Def_RP_JacSymB_Poly`: S4-JacSymB, file A (L10): `Sym^g A^1 = A^g`
* `S4.Def_RP_JacSymB_Map`: S4-JacSymB, file B: functoriality of `X^g` and `Sym^g`; surjections stay surjective on invariants
* `S4.Def_RP_JacSymB_Noeth`: S4-JacSymB, file C: finiteness of `X^g` and `Sym^g X`; points of `A^g`
* `S4.Def_RP_JacSymB_SymLoc`: S4-JacSymB, file F4: `Sym^g` commutes with localization at a norm (L12)
* `S4.Def_RP_JacLaw_Span`: S4-JacLaw, file O1: `Sym^g(B)` is spanned by norms (polarization over an infinite field)
* `S4.Def_RP_JacSymB_GenPoly`: S4-JacSymB, file H2b: the generic polynomial `E(w) = ∏_l (1 - w_l X)` (L12, valuative criterion)
* `S4.Def_RP_JacLaw_Crit`: S4-JacLaw, file O2: the morphism criterion for maps into `Sym^n`
* `S4.Def_RP_JacLaw_LinAlg`: S4-JacLaw, file O3: linear algebra for the negation step
* `S4.Def_RP_JacLaw_Gram`: S4-JacLaw O5: the trace matrix of a point of `Sym^d` and its kernel line
* `S4.Def_RP_JacLaw_Pres`: S4-JacLaw, file O4b: the Δ-ratio presentation of `B ⧸ (s)`
* `S4.Def_RP_JacLaw_Fam`: S4-JacLaw, file O6b: the Δ-ratio presentation in families
* `S4.Def_RP_JacLaw_Diag`: S4-JacLaw, file O4a: diagonalising a finite commutative algebra by one element
* `S4.Def_RP_JacLaw_MonPts`: S4-JacLaw, file O6c: monic generic polynomial, the zero set of a section, exact division
* `S4.Def_RP_JacLaw_Good`: S4-JacLaw, file O6d-1: choice data for `ν` and the good open `D(good)` of `Sym^d`
* `S4.Def_RP_JacLaw_Nu`: S4-JacLaw, file O6d-2: the negation map `ν : D(good) → Sym^g`
* `S4.Def_RP_JacLaw_Add`: S4-JacLaw, file O7: addition `Sym^d × Sym^e → Sym^(d+e)`
* `S4.Def_RP_JacLaw_Uniq`: S4-JacLaw, file O8a: uniqueness of `ν`, supports of points, padding and sum maps
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_GenFib =====
section

/-!
# S4-JacLaw, file O9c (G3 Fib): sections `q(x)` with reduced zero sets

`xB = x ∈ B` (the chart coordinate), `n = rank_{K[X]} B = [F : K(x)]`.
* `finrank_quot_poly`: `dim_K B/(q(x)) = deg q · n`.
* `exactPoleH_poly`: `q(x)` has exact pole divisor `poleDiv q(x)` at infinity (no zeros there).
* `exists_fib_card`: for all but finitely many `c` the fibre `x = c` has exactly `n` points (IsogDegA).
* `exists_fib_data`: for a finset `Λ` of good values, `s = ∏_{c∈Λ} (x - c)` has exact pole divisor of degree
  `|Λ| n` and exactly `|Λ| n` zeros, namely the points with `x ∈ Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.RR

section Fib

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

/-- `q(x)` has no zero at infinity. -/
theorem ord_inf_poly_nonpos {q : K[X]} (hq : q ≠ 0) (P : HeightOneSpectrum (Places.Rinf K F)) :
    Places.ord P (incB K F (algebraMap K[X] (Places.Rfin K F) q)) ≤ 0 := by
  have hq' : algebraMap K[X] (RatFunc K) q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hq
  set r : RatFunc K := (algebraMap K[X] (RatFunc K) q)⁻¹ with hr
  have hr0 : r ≠ 0 := inv_ne_zero hq'
  have hrO : r ∈ Places.Oinf K := by
    rw [Places.mem_Oinf_iff' K hr0, hr, RatFunc.intDegree_inv, RatFunc.intDegree_polynomial]
    omega
  set t : Places.Rinf K F := algebraMap (Places.Oinf K) (Places.Rinf K F) ⟨r, hrO⟩ with ht
  have ht0 : t ≠ 0 := by
    intro h
    apply hr0
    have h1 : (⟨r, hrO⟩ : Places.Oinf K) = 0 :=
      PlacesK.algebraMap_Oinf_Rinf_injective K F (h.trans (map_zero _).symm)
    exact congrArg Subtype.val h1
  have htF : algebraMap (Places.Rinf K F) F t = algebraMap (RatFunc K) F r := by
    rw [ht, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (Places.Oinf K) (RatFunc K) F]
    rfl
  have hprod : incB K F (algebraMap K[X] (Places.Rfin K F) q) * algebraMap (Places.Rinf K F) F t = 1 := by
    rw [incB_poly, htF, hr, ← map_mul, mul_inv_cancel₀ hq', map_one]
  have hs0 : incB K F (algebraMap K[X] (Places.Rfin K F) q) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have htF0 : algebraMap (Places.Rinf K F) F t ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have h1 := PlacesK.ord_mul P hs0 htF0
  rw [hprod, PlacesK.ord_algebraMap P ht0] at h1
  have h2 : Places.ord P (1 : F) = 0 := by simp [Places.ord]
  rw [h2] at h1
  omega

/-- `q(x)` has exact pole divisor `poleDiv q(x)` at infinity. -/
theorem exactPoleH_poly {q : K[X]} (hq : q ≠ 0) :
    ExactPoleH (algebraMap K[X] (Places.Rfin K F) q)
      (poleDiv (K := K) (incB K F (algebraMap K[X] (Places.Rfin K F) q))) := by
  intro P
  have := ord_inf_poly_nonpos (F := F) hq P
  simp only [poleDiv, Finsupp.sup_apply, Finsupp.neg_apply, PlacesK.div_apply, Places.Place.ord_inr,
    Finsupp.coe_zero, Pi.zero_apply]
  omega

theorem deg_poleDiv_poly {q : K[X]} (hq : q ≠ 0) :
    (poleDiv (K := K) (incB K F (algebraMap K[X] (Places.Rfin K F) q))).deg =
      ((q.natDegree * finrank K[X] (Places.Rfin K F) : ℕ) : ℤ) := by
  have hf : algebraMap K[X] (Places.Rfin K F) q ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_poly_injective).2 hq
  rw [← finrank_quot_poly hq]
  exact (finrank_quot_of_exactPoleH hf (isInf_poleDiv _) (exactPoleH_poly hq)).symm

section AlgClosed

variable [IsAlgClosed K]

/-- **Generic fibres of `x`.** For all `c` off the roots of some `a ≠ 0` the fibre `x = c` has `n` points. -/
theorem exists_fib_card : ∃ a : K[X], a ≠ 0 ∧ ∀ c : K, a.eval c ≠ 0 →
    {φ : Places.Rfin K F →ₐ[K] K | φ (xB K F) = c}.Finite ∧
      Nat.card {φ : Places.Rfin K F →ₐ[K] K // φ (xB K F) = c} = finrank K[X] (Places.Rfin K F) := by
  obtain ⟨a, ha, h⟩ := IsogDegA.exists_card_fiber_eq_finSepDegree (R := K[X]) (B := Places.Rfin K F)
    (RatFunc K) F K
  refine ⟨a, ha, fun c hc => ?_⟩
  have hχ : (Polynomial.aeval c : K[X] →ₐ[K] K) a ≠ 0 := by rwa [coe_aeval_eq_eval]
  obtain ⟨hfin, hcard⟩ := h (Polynomial.aeval c) hχ
  let E : IsogDegA.fiber K (Places.Rfin K F) (Polynomial.aeval c) ≃
      {φ : Places.Rfin K F →ₐ[K] K // φ (xB K F) = c} := Equiv.subtypeEquivRight (fib_iff c)
  have hrank : Field.finSepDegree (RatFunc K) F = finrank K[X] (Places.Rfin K F) := by
    rw [Field.finSepDegree_eq_finrank_of_isSeparable]
    exact (IsIntegralClosure.rank K[X] (RatFunc K) F (Places.Rfin K F)).symm
  refine ⟨?_, ?_⟩
  · have : Finite {φ : Places.Rfin K F →ₐ[K] K // φ (xB K F) = c} := Finite.of_equiv _ E
    exact Set.finite_coe_iff.1 this
  · rw [← Nat.card_congr E, hcard, hrank]

/-- **Sections `∏ (x - c)` over good values.** -/
theorem exists_fib_data : ∃ a : K[X], a ≠ 0 ∧ ∀ Λ : Finset K, (∀ c ∈ Λ, a.eval c ≠ 0) →
    ∃ s : Places.Rfin K F, ∃ Z : Finset (Places.Rfin K F →ₐ[K] K),
      s ≠ 0 ∧ ExactPoleH s (poleDiv (K := K) (incB K F s)) ∧
      (poleDiv (K := K) (incB K F s)).deg = ((Λ.card * finrank K[X] (Places.Rfin K F) : ℕ) : ℤ) ∧
      (∀ φ, φ ∈ Z ↔ φ s = 0) ∧ (∀ φ, φ ∈ Z ↔ φ (xB K F) ∈ Λ) ∧
      Z.card = Λ.card * finrank K[X] (Places.Rfin K F) := by
  obtain ⟨a, ha, h⟩ := exists_fib_card (K := K) (F := F)
  refine ⟨a, ha, fun Λ hΛ => ?_⟩
  set q : K[X] := ∏ c ∈ Λ, (X - C c) with hq
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => X_sub_C_ne_zero c
  have hqdeg : q.natDegree = Λ.card := by
    rw [hq, natDegree_prod _ _ fun c _ => X_sub_C_ne_zero c]
    simp
  have hs0 : algebraMap K[X] (Places.Rfin K F) q ≠ 0 :=
    (map_ne_zero_iff _ algebraMap_poly_injective).2 hq0
  have hzero : ∀ φ : Places.Rfin K F →ₐ[K] K,
      φ (algebraMap K[X] (Places.Rfin K F) q) = 0 ↔ φ (xB K F) ∈ Λ := by
    intro φ
    rw [apply_poly, hq, eval_prod, Finset.prod_eq_zero_iff]
    simp [sub_eq_zero]
  have hfinΛ : {φ : Places.Rfin K F →ₐ[K] K | φ (xB K F) ∈ Λ}.Finite := by
    have : {φ : Places.Rfin K F →ₐ[K] K | φ (xB K F) ∈ Λ} =
        ⋃ c ∈ Λ, {φ : Places.Rfin K F →ₐ[K] K | φ (xB K F) = c} := by
      ext φ; simp
    rw [this]
    exact Set.Finite.biUnion Λ.finite_toSet fun c hc => (h c (hΛ c hc)).1
  set Z := hfinΛ.toFinset with hZ
  have hmem : ∀ φ, φ ∈ Z ↔ φ (xB K F) ∈ Λ := fun φ => by rw [hZ, Set.Finite.mem_toFinset]; rfl
  refine ⟨algebraMap K[X] (Places.Rfin K F) q, Z, hs0, exactPoleH_poly hq0, ?_, fun φ => by rw [hmem, hzero],
    hmem, ?_⟩
  · rw [deg_poleDiv_poly hq0, hqdeg]
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun φ : Places.Rfin K F →ₐ[K] K => φ (xB K F)) (t := Λ)
      (fun φ hφ => (hmem φ).1 hφ)]
    refine Finset.sum_const_nat fun c hc => ?_
    have hc' := h c (hΛ c hc)
    have e2 : Nat.card {φ : Places.Rfin K F →ₐ[K] K // φ (xB K F) = c} = hc'.1.toFinset.card :=
      Nat.card_eq_card_finite_toFinset hc'.1
    rw [← hc'.2, e2]
    congr 1
    ext φ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hmem]
    constructor
    · rintro ⟨-, e⟩; exact e
    · intro e; exact ⟨e ▸ hc, e⟩

end AlgClosed

end Fib

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacSymA_A =====
section

/-!
# S4-JacSymA, file A: the coordinate ring of `X^g`, the `S_g`-action and the chart `Sym^g`

For a commutative `k`-algebra `B` (the coordinate ring of an affine chart `X = Spec B` of a curve), the coordinate
ring of `X^g` is the tensor power `XPow k B g = ⨂[k] _ : Fin g, B`. The symmetric group `S_g = Perm (Fin g)` acts by
permuting the tensor factors, and the affine chart of `Sym^g X` is `Spec (SymRing k B g)` with
`SymRing k B g = (⨂ B)^(S_g)`. A `g`-tuple of `k`-points of `B` is the same as a `k`-point of `XPow k B g`.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

variable (k : Type*) [CommRing k] (B : Type*) [CommRing B] [Algebra k B] (g : ℕ)

variable {k B g}

/-- `S_g` acts on `X^g` by ring automorphisms. -/
noncomputable instance : MulSemiringAction (Equiv.Perm (Fin g)) (XPow k B g) where
  smul σ x := permHom σ x
  one_smul x := by
    change permHom 1 x = x
    rw [permHom_one]; rfl
  mul_smul σ τ x := by
    change permHom (σ * τ) x = permHom σ (permHom τ x)
    rw [permHom_mul]; rfl
  smul_zero σ := map_zero (permHom σ)
  smul_add σ := map_add (permHom σ)
  smul_one σ := map_one (permHom σ)
  smul_mul σ := map_mul (permHom σ)

theorem perm_smul_def (σ : Equiv.Perm (Fin g)) (x : XPow k B g) : σ • x = permHom σ x := rfl

instance : SMulCommClass (Equiv.Perm (Fin g)) k (XPow k B g) where
  smul_comm σ c x := by simp only [perm_smul_def, map_smul]

variable (k B g)

/-- The coordinate ring of the affine chart `Sym^g X`: the `S_g`-invariants of `X^g`. -/
noncomputable abbrev SymRing : Subalgebra k (XPow k B g) :=
  FixedPoints.subalgebra k (XPow k B g) (Equiv.Perm (Fin g))

variable {k B g}

theorem mem_symRing (x : XPow k B g) : x ∈ SymRing k B g ↔ ∀ σ : Equiv.Perm (Fin g), σ • x = x :=
  Iff.rfl

/-- `S_g` acts on `X^g / Sym^g` with the invariants as base ring (Mathlib's `Algebra.IsInvariant`). -/
instance isInvariant : Algebra.IsInvariant (SymRing k B g) (XPow k B g) (Equiv.Perm (Fin g)) where
  isInvariant x hx := ⟨⟨x, (mem_symRing x).2 hx⟩, rfl⟩

/-- `X^g` is integral over `Sym^g` (the quotient map `X^g → Sym^g` is finite). -/
instance isIntegral : Algebra.IsIntegral (SymRing k B g) (XPow k B g) :=
  Algebra.IsInvariant.isIntegral (SymRing k B g) (XPow k B g) (Equiv.Perm (Fin g))

theorem smul_symRing (σ : Equiv.Perm (Fin g)) (x : SymRing k B g) : σ • (x : XPow k B g) = x :=
  x.2 σ

/-! ### `k`-points of `X^g` are `g`-tuples of `k`-points of `X` -/

/-- The multilinear map `(b_i) ↦ ∏ a_i (b_i)`. -/
noncomputable def ptML (a : Fin g → (B →ₐ[k] k)) : MultilinearMap k (fun _ : Fin g => B) k :=
  (MultilinearMap.mkPiAlgebra k (Fin g) k).compLinearMap (fun i => (a i).toLinearMap)

theorem ptML_apply (a : Fin g → (B →ₐ[k] k)) (b : Fin g → B) : ptML a b = ∏ i, a i (b i) := by
  simp [ptML, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- The `k`-point of `X^g` with coordinates `a_1, ..., a_g`: `b_1 ⊗ ... ⊗ b_g ↦ ∏ a_i (b_i)`. -/
noncomputable def ptOf (a : Fin g → (B →ₐ[k] k)) : XPow k B g →ₐ[k] k :=
  PiTensorProduct.liftAlgHom (ptML a) (by rw [ptML_apply]; simp)
    (fun x y => by rw [ptML_apply, ptML_apply, ptML_apply, ← Finset.prod_mul_distrib]; simp)

@[simp] theorem ptOf_tprod (a : Fin g → (B →ₐ[k] k)) (b : Fin g → B) :
    ptOf a (PiTensorProduct.tprod k b) = ∏ i, a i (b i) := by
  rw [ptOf, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod, ptML_apply]

/-- The inclusion of the `i`-th factor `B → X^g`, `b ↦ 1 ⊗ ... ⊗ b ⊗ ... ⊗ 1`. -/
noncomputable def inc (i : Fin g) : B →ₐ[k] XPow k B g :=
  PiTensorProduct.singleAlgHom (R := k) (A := fun _ : Fin g => B) i

theorem ptOf_inc (a : Fin g → (B →ₐ[k] k)) (i : Fin g) : (ptOf a).comp (inc i) = a i := by
  ext b
  simp only [inc, AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply, ptOf_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem algHom_ext_inc {f h : XPow k B g →ₐ[k] k} (H : ∀ i, f.comp (inc i) = h.comp (inc i)) : f = h :=
  PiTensorProduct.algHom_ext H

/-- `k`-points of `X^g` are `g`-tuples of `k`-points of `X`. -/
noncomputable def ptsEquiv : (Fin g → (B →ₐ[k] k)) ≃ (XPow k B g →ₐ[k] k) where
  toFun := ptOf
  invFun ψ i := ψ.comp (inc i)
  left_inv a := by
    funext i
    exact ptOf_inc a i
  right_inv ψ := by
    apply algHom_ext_inc
    intro i
    exact ptOf_inc (fun j => ψ.comp (inc j)) i

theorem ptsEquiv_apply (a : Fin g → (B →ₐ[k] k)) : ptsEquiv a = ptOf a := rfl

theorem ptsEquiv_symm_apply (ψ : XPow k B g →ₐ[k] k) (i : Fin g) :
    ptsEquiv.symm ψ i = ψ.comp (inc i) := rfl

/-- Permuting the factors permutes the coordinates of a point. -/
theorem ptOf_comp_permHom (a : Fin g → (B →ₐ[k] k)) (τ : Equiv.Perm (Fin g)) :
    (ptOf a).comp (permHom τ) = ptOf (a ∘ τ) := by
  apply AlgHom.toLinearMap_injective
  refine PiTensorProduct.ext (MultilinearMap.ext fun b => ?_)
  simp only [LinearMap.compMultilinearMap_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    permHom_tprod, ptOf_tprod, Function.comp_apply]
  exact (Equiv.prod_comp τ (fun i => a i (b (τ.symm i)))).symm.trans (by simp)

theorem ptOf_smul (a : Fin g → (B →ₐ[k] k)) (τ : Equiv.Perm (Fin g)) (x : XPow k B g) :
    ptOf a (τ • x) = ptOf (a ∘ τ) x := by
  rw [perm_smul_def, ← ptOf_comp_permHom]; rfl

/-- Points of `Sym^g` coming from `g`-tuples: restrict `ptOf a` to the invariants. -/
noncomputable def symPt (a : Fin g → (B →ₐ[k] k)) : SymRing k B g →ₐ[k] k :=
  (ptOf a).comp (SymRing k B g).val

theorem symPt_comp_perm (a : Fin g → (B →ₐ[k] k)) (τ : Equiv.Perm (Fin g)) :
    symPt (a ∘ τ) = symPt a := by
  ext x
  simp only [symPt, AlgHom.comp_apply, Subalgebra.coe_val]
  rw [← ptOf_smul, smul_symRing]

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymA_B =====
section

/-!
# S4-JacSymA, file B: the `k`-points of the chart `Sym^g X` (lemma L8 of S4_COREB_ROUTE.md)

For `k` algebraically closed, every `k`-point of `Sym^g = Spec (⨂ B)^(S_g)` lifts to a `k`-point of `X^g` (lying over,
`X^g` is integral over `Sym^g`), and two lifts differ by a permutation (`Algebra.IsInvariant.exists_smul_of_under_eq`).
Hence `k`-points of `Sym^g` are unordered `g`-tuples of `k`-points of `X`: `symPtsEquiv`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson.JacSym

/-- Two `k`-points with the same kernel are equal. -/
theorem algHom_eq_of_ker_eq {k A : Type*} [Field k] [CommRing A] [Algebra k A] {f h : A →ₐ[k] k}
    (H : RingHom.ker f = RingHom.ker h) : f = h := by
  ext x
  have hx : x - algebraMap k A (f x) ∈ RingHom.ker f := by simp [RingHom.mem_ker]
  rw [H, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply] at hx
  exact (sub_eq_zero.1 hx).symm

/-- The multiset of a tuple. -/
def mset {α : Type*} {n : ℕ} (a : Fin n → α) : Sym α n := ⟨Finset.univ.val.map a, by simp⟩

theorem mset_coe {α : Type*} {n : ℕ} (a : Fin n → α) : (mset a : Multiset α) = Finset.univ.val.map a := rfl

theorem mset_comp_perm {α : Type*} {n : ℕ} (a : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    mset (a ∘ σ) = mset a := by
  apply Sym.coe_injective
  rw [mset_coe, mset_coe, ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Tuples with the same multiset of entries differ by a permutation. -/
theorem exists_perm_of_mset_eq {α : Type*} {n : ℕ} (f h : Fin n → α) (hfh : mset f = mset h) :
    ∃ σ : Equiv.Perm (Fin n), h = f ∘ σ := by
  classical
  have e1 : ∀ (u : Fin n → α) (x : α),
      Fintype.card {i // u i = x} = Multiset.count x (Finset.univ.val.map u) := by
    intro u x
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun i _ => eq_comm)
  have hc : ∀ x, Fintype.card {i // h i = x} = Fintype.card {i // f i = x} := by
    intro x
    rw [e1, e1, ← mset_coe, ← mset_coe, hfh]
  refine ⟨Equiv.ofFiberEquiv (fun x => Fintype.equivOfCardEq (hc x)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

theorem symPt_apply (a : Fin g → (B →ₐ[k] k)) (x : SymRing k B g) : symPt a x = ptOf a (x : XPow k B g) :=
  rfl

/-- Transitivity: tuples with the same point of `Sym^g` differ by a permutation. -/
theorem exists_perm_of_symPt_eq (a a' : Fin g → (B →ₐ[k] k)) (h : symPt a = symPt a') :
    ∃ σ : Equiv.Perm (Fin g), a' = a ∘ σ := by
  have := RingHom.ker_isPrime (ptOf a)
  have := RingHom.ker_isPrime (ptOf a')
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (SymRing k B g) (XPow k B g)
    (Equiv.Perm (Fin g)) (RingHom.ker (ptOf a)) (RingHom.ker (ptOf a')) (by
      ext x
      simp only [Ideal.under, Ideal.mem_comap, RingHom.mem_ker]
      have hx := congrArg (fun f => f x) h
      simp only [symPt_apply] at hx
      change ptOf a (x : XPow k B g) = 0 ↔ ptOf a' (x : XPow k B g) = 0
      rw [hx])
  refine ⟨σ⁻¹, ptsEquiv.injective (algHom_eq_of_ker_eq ?_)⟩
  rw [ptsEquiv_apply, hσ]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, RingHom.mem_ker, RingHom.mem_ker, ptOf_smul,
    ptsEquiv_apply]

theorem mset_eq_of_symPt_eq (a a' : Fin g → (B →ₐ[k] k)) (h : symPt a = symPt a') : mset a = mset a' := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_symPt_eq a a' h
  exact (mset_comp_perm a σ).symm

theorem symPt_eq_of_mset_eq (a a' : Fin g → (B →ₐ[k] k)) (h : mset a = mset a') : symPt a = symPt a' := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_mset_eq a a' h
  exact (symPt_comp_perm a σ).symm

/-- Lifting (needs `k` algebraically closed): every `k`-point of `Sym^g` is the image of a `k`-point of `X^g`. -/
theorem exists_lift [IsAlgClosed k] (φ : SymRing k B g →ₐ[k] k) :
    ∃ ψ : XPow k B g →ₐ[k] k, ψ.comp (SymRing k B g).val = φ := by
  have := RingHom.ker_isPrime φ
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := XPow k B g)
    (RingHom.ker φ) ⊥ (by
      intro x hx
      have : x = 0 := Subtype.ext hx
      simp [this])
  have key : ∀ a : SymRing k B g,
      Ideal.Quotient.mk P (a : XPow k B g) = algebraMap k (XPow k B g ⧸ P) (φ a) := by
    intro a
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
    have h1 : a - algebraMap k (SymRing k B g) (φ a) ∈ RingHom.ker φ := by simp [RingHom.mem_ker]
    rw [← hPc, Ideal.mem_comap] at h1
    simpa using h1
  have hint : Algebra.IsIntegral k (XPow k B g ⧸ P) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := SymRing k B g) x
    refine ⟨p.map (φ : SymRing k B g →+* k), hpm.map _, ?_⟩
    have hc : (algebraMap k (XPow k B g ⧸ P)).comp (φ : SymRing k B g →+* k) =
        (Ideal.Quotient.mk P).comp (algebraMap (SymRing k B g) (XPow k B g)) :=
      RingHom.ext fun a => (key a).symm
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hp, map_zero]
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := XPow k B g ⧸ P)
  let e : k ≃ₐ[k] XPow k B g ⧸ P := AlgEquiv.ofBijective (Algebra.ofId k (XPow k B g ⧸ P)) hbij
  refine ⟨(e.symm : XPow k B g ⧸ P →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  ext a
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Subalgebra.coe_val]
  rw [key a]
  exact e.symm_apply_apply (φ a)

variable [IsAlgClosed k]

/-- A chosen ordered lift of a `k`-point of `Sym^g`. -/
noncomputable def liftTuple (φ : SymRing k B g →ₐ[k] k) : Fin g → (B →ₐ[k] k) :=
  ptsEquiv.symm (Classical.choose (exists_lift φ))

theorem symPt_liftTuple (φ : SymRing k B g →ₐ[k] k) : symPt (liftTuple φ) = φ := by
  rw [symPt, liftTuple, ← ptsEquiv_apply, Equiv.apply_symm_apply]
  exact Classical.choose_spec (exists_lift φ)

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymA_C =====
section

/-!
# S4-JacSymA, file C: points of the chart are effective divisors (L8, divisor form)

For `B` of finite type over an algebraically closed field `k`, the `k`-points of `Spec B` are its maximal ideals
(Nullstellensatz). If `B` is a Dedekind domain that is not a field (an affine chart of a smooth curve), these are the
height-one primes, i.e. the prime divisors supported on the chart. Combined with `symPtsEquiv` (file B): the
`k`-points of `Sym^g = Spec (⨂ B)^(S_g)` are the effective divisors of degree `g` supported on the chart.
-/

set_option autoImplicit false

open IsDedekindDomain

namespace RamanujanPetersson.JacSym

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

theorem ker_isMaximal (φ : B →ₐ[k] k) : (RingHom.ker φ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective φ (fun c => ⟨algebraMap k B c, by simp⟩)

/-- Nullstellensatz: for `B` of finite type over algebraically closed `k`, every maximal ideal is the kernel of a
`k`-point. -/
theorem exists_algHom_ker_eq [IsAlgClosed k] [Algebra.FiniteType k B] (m : Ideal B) [m.IsMaximal] :
    ∃ φ : B →ₐ[k] k, RingHom.ker φ = m := by
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B ⧸ m)
  let e : k ≃ₐ[k] B ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ m)) hbij
  refine ⟨(e.symm : B ⧸ m →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- `k`-points of `Spec B` are the maximal ideals of `B` (`B` of finite type over algebraically closed `k`). -/
noncomputable def ptMaxEquiv [IsAlgClosed k] [Algebra.FiniteType k B] : (B →ₐ[k] k) ≃ MaximalSpectrum B :=
  Equiv.ofBijective (fun φ => ⟨RingHom.ker φ, ker_isMaximal φ⟩)
    ⟨fun φ φ' h => algHom_eq_of_ker_eq (congrArg MaximalSpectrum.asIdeal h), fun m => by
      have := m.isMaximal
      obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) m.asIdeal
      exact ⟨φ, MaximalSpectrum.ext hφ⟩⟩

theorem ptMaxEquiv_asIdeal [IsAlgClosed k] [Algebra.FiniteType k B] (φ : B →ₐ[k] k) :
    (ptMaxEquiv φ).asIdeal = RingHom.ker φ := rfl

/-- For a Dedekind domain `B` of finite type over algebraically closed `k` that is not a field (an affine chart of a
smooth curve), `k`-points of `Spec B` are the prime divisors `HeightOneSpectrum B` supported on the chart. -/
noncomputable def ptDivEquiv [IsAlgClosed k] [Algebra.FiniteType k B] [IsDedekindDomain B] (hB : ¬ IsField B) :
    (B →ₐ[k] k) ≃ HeightOneSpectrum B :=
  ptMaxEquiv.trans (HeightOneSpectrum.equivMaximalSpectrum hB).symm

theorem ptDivEquiv_asIdeal [IsAlgClosed k] [Algebra.FiniteType k B] [IsDedekindDomain B] (hB : ¬ IsField B)
    (φ : B →ₐ[k] k) : (ptDivEquiv hB φ).asIdeal = RingHom.ker φ := rfl

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymA_D =====
section

/-!
# S4-JacSymA, file D: `X^g` is integral

For `k` algebraically closed and `B` a finitely generated `k`-algebra that is a domain (an affine chart of an
integral curve), the coordinate ring `XPow k B g = ⨂[k] B` of `X^g` is a domain. Proof: `B ⊗[k] A` is a domain for
every `k`-algebra domain `A` (coordinates in a `k`-basis of `A`, evaluation at `k`-points of `B` and the
Nullstellensatz), and `X^(n+1) → B ⊗ X^n` is injective (it has the left inverse `B ⊗ X^n → X^(n+1)`).
-/

set_option autoImplicit false

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

section liftFam

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}
  {S : Type*} [CommRing S] [Algebra k S]

/-- The multilinear map `(b_i) ↦ ∏ f_i (b_i)` into a commutative `k`-algebra `S`. -/
noncomputable def famML (f : Fin n → (B →ₐ[k] S)) : MultilinearMap k (fun _ : Fin n => B) S :=
  (MultilinearMap.mkPiAlgebra k (Fin n) S).compLinearMap (fun i => (f i).toLinearMap)

theorem famML_apply (f : Fin n → (B →ₐ[k] S)) (b : Fin n → B) : famML f b = ∏ i, f i (b i) := by
  simp [famML, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- The algebra map `X^n → S`, `b_1 ⊗ ... ⊗ b_n ↦ ∏ f_i (b_i)`, of a family of algebra maps `B → S`. -/
noncomputable def liftFam (f : Fin n → (B →ₐ[k] S)) : XPow k B n →ₐ[k] S :=
  PiTensorProduct.liftAlgHom (famML f) (by rw [famML_apply]; simp)
    (fun x y => by rw [famML_apply, famML_apply, famML_apply, ← Finset.prod_mul_distrib]; simp)

@[simp] theorem liftFam_tprod (f : Fin n → (B →ₐ[k] S)) (b : Fin n → B) :
    liftFam f (PiTensorProduct.tprod k b) = ∏ i, f i (b i) := by
  rw [liftFam, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod, famML_apply]

theorem liftFam_inc (f : Fin n → (B →ₐ[k] S)) (i : Fin n) : (liftFam f).comp (inc i) = f i := by
  ext b
  simp only [inc, AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply, liftFam_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem liftFam_inc_apply (f : Fin n → (B →ₐ[k] S)) (i : Fin n) (b : B) : liftFam f (inc i b) = f i b := by
  rw [← AlgHom.comp_apply, liftFam_inc]

end liftFam

section cons

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}

/-- `B ⊗ X^n → X^(n+1)`: the first factor goes to slot `0`, the others to slots `1, ..., n`. -/
noncomputable def consHom : B ⊗[k] XPow k B n →ₐ[k] XPow k B (n + 1) :=
  Algebra.TensorProduct.lift (inc 0) (liftFam (fun j : Fin n => inc j.succ)) (fun _ _ => Commute.all _ _)

/-- `X^(n+1) → B ⊗ X^n`, `b_0 ⊗ b_1 ⊗ ... ⊗ b_n ↦ b_0 ⊗ (b_1 ⊗ ... ⊗ b_n)`. -/
noncomputable def unconsHom : XPow k B (n + 1) →ₐ[k] B ⊗[k] XPow k B n :=
  liftFam (fun i : Fin (n + 1) => Fin.cases (motive := fun _ => B →ₐ[k] B ⊗[k] XPow k B n)
    (Algebra.TensorProduct.includeLeft (S := k)) (fun j => Algebra.TensorProduct.includeRight.comp (inc j)) i)

theorem consHom_comp_unconsHom :
    (consHom (k := k) (B := B) (n := n)).comp unconsHom = AlgHom.id k (XPow k B (n + 1)) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change consHom.comp (unconsHom.comp (inc i)) = (AlgHom.id k _).comp (inc i)
  rw [unconsHom, liftFam_inc]
  refine Fin.cases ?_ (fun j => ?_) i
  · ext b; simp [consHom]
  · ext b; simp [consHom, liftFam_inc_apply]

theorem unconsHom_injective : Function.Injective (unconsHom (k := k) (B := B) (n := n)) := fun x y hxy => by
  have h := congrArg (consHom (k := k) (B := B) (n := n)) hxy
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, consHom_comp_unconsHom, AlgHom.id_apply, AlgHom.id_apply] at h
  exact h

end cons

section domain

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

/-- Nullstellensatz: a function on `Spec B` vanishing at every `k`-point is zero. -/
theorem eq_zero_of_forall_pt (c : B) (hc : ∀ x : B →ₐ[k] k, x c = 0) : c = 0 := by
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hj : (⊥ : Ideal B).jacobson = ⊥ := IsJacobsonRing.out' ⊥ Ideal.isPrime_bot.isRadical
  have hc' : c ∈ (⊥ : Ideal B).jacobson := by
    refine Ideal.mem_sInf.2 ?_
    rintro m ⟨-, hm⟩
    have := hm
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) m
    rw [← hφ, RingHom.mem_ker]
    exact hc φ
  rw [hj] at hc'
  exact (Submodule.mem_bot _).1 hc'

variable {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]

/-- Evaluation of the first factor at a `k`-point `x`: `B ⊗ A → A`, `c ⊗ a ↦ x(c) a`. -/
noncomputable def evPt (x : B →ₐ[k] k) : B ⊗[k] A →ₐ[k] A :=
  (Algebra.TensorProduct.lid k A).toAlgHom.comp (Algebra.TensorProduct.map x (AlgHom.id k A))

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] [IsDomain A] in
theorem repr_evPt (x : B →ₐ[k] k) (f : B ⊗[k] A) (i : Module.Free.ChooseBasisIndex k A) :
    (Module.Free.chooseBasis k A).repr (evPt x f) i =
      x ((Algebra.TensorProduct.basis B (Module.Free.chooseBasis k A)).repr f i) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul c a => simp [evPt, Algebra.TensorProduct.basis_repr_tmul]
  | add f h hf hh => simp [hf, hh]

/-- `B ⊗[k] A` is a domain for every `k`-algebra domain `A` (`k` algebraically closed, `B` a f.g. domain). -/
theorem isDomain_tensor : IsDomain (B ⊗[k] A) := by
  set E := Algebra.TensorProduct.basis B (Module.Free.chooseBasis k A)
  obtain ⟨i₀⟩ := (Module.Free.chooseBasis k A).index_nonempty
  have : Nontrivial (B ⊗[k] A) := nontrivial_of_ne _ _ (E.ne_zero i₀)
  have : NoZeroDivisors (B ⊗[k] A) := by
    refine ⟨fun {f h} hfh => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hf, hh⟩ := hcon
    obtain ⟨i, hi⟩ : ∃ i, E.repr f i ≠ 0 := by
      by_contra H; push Not at H; exact hf (E.repr.injective (by ext i; simp [H]))
    obtain ⟨j, hj⟩ : ∃ j, E.repr h j ≠ 0 := by
      by_contra H; push Not at H; exact hh (E.repr.injective (by ext j; simp [H]))
    obtain ⟨x, hx⟩ : ∃ x : B →ₐ[k] k, x (E.repr f i * E.repr h j) ≠ 0 := by
      by_contra H; push Not at H; exact mul_ne_zero hi hj (eq_zero_of_forall_pt _ H)
    rw [map_mul] at hx
    have h1 : evPt x f ≠ 0 := fun h0 => left_ne_zero_of_mul hx (by rw [← repr_evPt, h0]; simp)
    have h2 : evPt x h ≠ 0 := fun h0 => right_ne_zero_of_mul hx (by rw [← repr_evPt, h0]; simp)
    exact mul_ne_zero h1 h2 (by rw [← map_mul, hfh, map_zero])
  exact NoZeroDivisors.to_isDomain _

variable (k B) in
/-- `X^g` is integral: `XPow k B g` is a domain (`k` algebraically closed, `B` a f.g. `k`-domain). -/
theorem isDomain_xPow (g : ℕ) : IsDomain (XPow k B g) := by
  induction g with
  | zero =>
    have hinv : (Algebra.ofId k (XPow k B 0)).comp (liftFam (S := k) Fin.elim0) = AlgHom.id k _ :=
      PiTensorProduct.algHom_ext (fun i => i.elim0)
    exact Function.Injective.isDomain (liftFam (k := k) (B := B) (S := k) (n := 0) Fin.elim0)
      (Function.LeftInverse.injective (g := Algebra.ofId k (XPow k B 0))
        (fun x => DFunLike.congr_fun hinv x))
  | succ n ih =>
    have := ih
    have := isDomain_tensor (k := k) (B := B) (A := XPow k B n)
    exact Function.Injective.isDomain _ unconsHom_injective

instance (g : ℕ) : IsDomain (XPow k B g) := isDomain_xPow k B g

end domain

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_Poly =====
section

/-!
# S4-JacSymB, file A (L10): `Sym^g A^1 = A^g`

`X^g` for `X = A^1` is the polynomial ring in `g` variables (`polyEquiv`), `S_g`-equivariantly (`toMv_smul`), so
`Sym^g A^1 = Spec (k[X]^⊗g)^(S_g)` is the spectrum of the symmetric polynomials, which by the fundamental theorem of
symmetric polynomials is again a polynomial ring in `g` variables (`symPolyEquiv`).
-/

set_option autoImplicit false

open scoped TensorProduct
open Polynomial

namespace RamanujanPetersson.JacSym

section Poly

variable (k : Type*) [CommRing k] (g : ℕ)

/-- `k[X]^⊗g → k[X_1, ..., X_g]`, the `i`-th factor going to the `i`-th variable. -/
noncomputable def toMv : XPow k k[X] g →ₐ[k] MvPolynomial (Fin g) k :=
  liftFam (fun i => Polynomial.aeval (MvPolynomial.X i))

/-- `k[X_1, ..., X_g] → k[X]^⊗g`, `X_i ↦ 1 ⊗ ... ⊗ X ⊗ ... ⊗ 1`. -/
noncomputable def ofMv : MvPolynomial (Fin g) k →ₐ[k] XPow k k[X] g :=
  MvPolynomial.aeval (fun i => inc i Polynomial.X)

theorem toMv_inc (i : Fin g) (p : k[X]) : toMv k g (inc i p) = Polynomial.aeval (MvPolynomial.X i) p := by
  rw [toMv, liftFam_inc_apply]

theorem toMv_comp_ofMv : (toMv k g).comp (ofMv k g) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [ofMv, toMv_inc]

theorem ofMv_comp_toMv : (ofMv k g).comp (toMv k g) = AlgHom.id k _ := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply Polynomial.algHom_ext
  change ofMv k g (toMv k g (inc i Polynomial.X)) = inc i Polynomial.X
  simp [ofMv, toMv_inc]

/-- `X^g = A^g` for `X = A^1`. -/
noncomputable def polyEquiv : XPow k k[X] g ≃ₐ[k] MvPolynomial (Fin g) k :=
  AlgEquiv.ofAlgHom (toMv k g) (ofMv k g) (toMv_comp_ofMv k g) (ofMv_comp_toMv k g)

theorem polyEquiv_apply (x : XPow k k[X] g) : polyEquiv k g x = toMv k g x := rfl

theorem toMv_injective : Function.Injective (toMv k g) := (polyEquiv k g).injective

variable {k g}

theorem permHom_comp_inc {B : Type*} [CommRing B] [Algebra k B] (σ : Equiv.Perm (Fin g)) (i : Fin g) :
    (permHom σ).comp (inc i) = (inc (σ i) : B →ₐ[k] XPow k B g) := by
  ext b
  simp only [inc, AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply, permHom_tprod]
  congr 1
  funext j
  simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_apply, Equiv.symm_apply_eq]

theorem toMv_comp_permHom (σ : Equiv.Perm (Fin g)) :
    (toMv k g).comp (permHom σ) = (MvPolynomial.rename σ).comp (toMv k g) := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply Polynomial.algHom_ext
  change toMv k g (permHom σ (inc i Polynomial.X)) = MvPolynomial.rename σ (toMv k g (inc i Polynomial.X))
  rw [← AlgHom.comp_apply (permHom σ) (inc i), permHom_comp_inc, toMv_inc, toMv_inc]
  simp

theorem toMv_smul (σ : Equiv.Perm (Fin g)) (x : XPow k k[X] g) :
    toMv k g (σ • x) = MvPolynomial.rename σ (toMv k g x) := by
  rw [perm_smul_def, ← AlgHom.comp_apply, toMv_comp_permHom, AlgHom.comp_apply]

theorem mem_symRing_iff_isSymmetric (x : XPow k k[X] g) :
    x ∈ SymRing k k[X] g ↔ (toMv k g x).IsSymmetric := by
  rw [mem_symRing, MvPolynomial.IsSymmetric]
  refine forall_congr' fun σ => ?_
  rw [← toMv_smul, (toMv_injective k g).eq_iff]

variable (k g)

theorem map_symRing_eq :
    (SymRing k k[X] g).map (toMv k g) = MvPolynomial.symmetricSubalgebra (Fin g) k := by
  ext p
  rw [Subalgebra.mem_map, MvPolynomial.mem_symmetricSubalgebra]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_symRing_iff_isSymmetric x).1 hx
  · intro hp
    refine ⟨ofMv k g p, (mem_symRing_iff_isSymmetric _).2 ?_, ?_⟩
    · rwa [← AlgHom.comp_apply, toMv_comp_ofMv, AlgHom.id_apply]
    · rw [← AlgHom.comp_apply, toMv_comp_ofMv, AlgHom.id_apply]

/-- `Sym^g A^1` is the spectrum of the symmetric polynomials. -/
noncomputable def symEquiv : SymRing k k[X] g ≃ₐ[k] MvPolynomial.symmetricSubalgebra (Fin g) k :=
  ((polyEquiv k g).subalgebraMap (SymRing k k[X] g)).trans (Subalgebra.equivOfEq _ _ (map_symRing_eq k g))

/-- **L10** `Sym^g A^1 = A^g`: the fundamental theorem of symmetric polynomials. -/
noncomputable def symPolyEquiv : SymRing k k[X] g ≃ₐ[k] MvPolynomial (Fin g) k :=
  (symEquiv k g).trans (MvPolynomial.esymmAlgEquiv (Fin g) k (Fintype.card_fin g)).symm

theorem symEquiv_apply (x : SymRing k k[X] g) : (symEquiv k g x : MvPolynomial (Fin g) k) = toMv k g x := rfl

end Poly

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_Map =====
section

/-!
# S4-JacSymB, file B: functoriality of `X^g` and `Sym^g`; surjections stay surjective on invariants

`xMap f : X^g → Y^g` and `symMap f : Sym^g → Sym^g` for an algebra map `f : B → B'`. Over a field, a surjective `f` has a
linear section `s`, and `s^⊗g` is `S_g`-equivariant, so `symMap f` is surjective in every characteristic.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

section Map

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

theorem prod_inc (c : Fin g → B) : ∏ i, inc i (c i) = (PiTensorProduct.tprod k c : XPow k B g) := by
  simp only [inc, PiTensorProduct.singleAlgHom_apply]
  rw [← PiTensorProduct.tprod_prod]
  congr 1
  exact Finset.univ_prod_mulSingle c

/-- `X^g → X'^g` induced by `f : B → B'`. -/
noncomputable def xMap (f : B →ₐ[k] B') : XPow k B g →ₐ[k] XPow k B' g := liftFam (fun i => (inc i).comp f)

theorem xMap_inc (f : B →ₐ[k] B') (i : Fin g) : (xMap f).comp (inc i) = (inc i).comp f := liftFam_inc _ i

@[simp] theorem xMap_tprod (f : B →ₐ[k] B') (b : Fin g → B) :
    xMap f (PiTensorProduct.tprod k b) = PiTensorProduct.tprod k (fun i => f (b i)) := by
  rw [xMap, liftFam_tprod, ← prod_inc]
  rfl

theorem xMap_comp_permHom (f : B →ₐ[k] B') (σ : Equiv.Perm (Fin g)) :
    (xMap f).comp (permHom σ) = (permHom σ).comp (xMap f) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change (xMap f).comp ((permHom σ).comp (inc i)) = (permHom σ).comp ((xMap f).comp (inc i))
  rw [permHom_comp_inc, xMap_inc, xMap_inc, ← AlgHom.comp_assoc, permHom_comp_inc]

theorem xMap_smul (f : B →ₐ[k] B') (σ : Equiv.Perm (Fin g)) (x : XPow k B g) :
    xMap f (σ • x) = σ • xMap f x := by
  rw [perm_smul_def, perm_smul_def, ← AlgHom.comp_apply, xMap_comp_permHom, AlgHom.comp_apply]

/-- `Sym^g X → Sym^g X'` induced by `f : B → B'` (on coordinate rings, `Sym^g X' ← ...` contravariantly). -/
noncomputable def symMap (f : B →ₐ[k] B') : SymRing k B g →ₐ[k] SymRing k B' g :=
  ((xMap f).comp (SymRing k B g).val).codRestrict (SymRing k B' g) (fun x => by
    rw [mem_symRing]
    intro σ
    rw [AlgHom.comp_apply, ← xMap_smul]
    exact congrArg _ (smul_symRing σ x))

@[simp] theorem symMap_coe (f : B →ₐ[k] B') (x : SymRing k B g) : (symMap f x : XPow k B' g) = xMap f x := rfl

end Map

section Section

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

/-- `s^⊗g` for a linear map `s`. -/
noncomputable def secMap (s : B' →ₗ[k] B) : XPow k B' g →ₗ[k] XPow k B g := PiTensorProduct.map (fun _ => s)

theorem secMap_smul (s : B' →ₗ[k] B) (σ : Equiv.Perm (Fin g)) (x : XPow k B' g) :
    secMap s (σ • x) = σ • secMap s x := by
  rw [perm_smul_def, perm_smul_def]
  change ((secMap s).comp (permHom σ).toLinearMap) x = ((permHom σ).toLinearMap.comp (secMap s)) x
  congr 1
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro b
  simp [secMap, PiTensorProduct.map_tprod]

theorem xMap_secMap (f : B →ₐ[k] B') (s : B' →ₗ[k] B) (hs : ∀ b, f (s b) = b) (x : XPow k B' g) :
    xMap f (secMap s x) = x := by
  change ((xMap f).toLinearMap.comp (secMap s)) x = (LinearMap.id : XPow k B' g →ₗ[k] XPow k B' g) x
  congr 1
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro b
  simp [secMap, PiTensorProduct.map_tprod, hs]

/-- Surjections of algebras stay surjective on `S_g`-invariants (any characteristic). -/
theorem symMap_surjective (f : B →ₐ[k] B') (hf : Function.Surjective f) :
    Function.Surjective (symMap (g := g) f) := by
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ b, f (s b) = b := fun b => by simpa using LinearMap.congr_fun hs b
  intro y
  refine ⟨⟨secMap s (y : XPow k B' g), ?_⟩, ?_⟩
  · rw [mem_symRing]
    intro σ
    rw [← secMap_smul, smul_symRing]
  · apply Subtype.ext
    rw [symMap_coe]
    exact xMap_secMap f s hs' _

/-- Kernel of `X^g → X'^g` for a surjection: generated by the coordinate copies of `ker f`. -/
theorem ker_xMap_le (f : B →ₐ[k] B') (hf : Function.Surjective f) :
    RingHom.ker (xMap (g := g) f) ≤ Ideal.span (⋃ l : Fin g, inc l '' (RingHom.ker f : Set B)) := by
  classical
  set J : Ideal (XPow k B g) := Ideal.span (⋃ l : Fin g, inc l '' (RingHom.ker f : Set B))
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ b, f (s b) = b := fun b => by simpa using LinearMap.congr_fun hs b
  have key : (Ideal.Quotient.mkₐ k J).toLinearMap =
      (Ideal.Quotient.mkₐ k J).toLinearMap.comp ((secMap s).comp (xMap (g := g) f).toLinearMap) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro b
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, xMap_tprod,
      secMap, PiTensorProduct.map_tprod, Ideal.Quotient.mkₐ_eq_mk]
    rw [← prod_inc, ← prod_inc, map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Ideal.Quotient.eq, ← map_sub]
    refine Ideal.subset_span (Set.mem_iUnion.2 ⟨i, _, ?_, rfl⟩)
    change f _ = 0
    rw [map_sub, hs', sub_self]
  intro t ht
  have h := LinearMap.congr_fun key t
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, (RingHom.mem_ker).1 ht, map_zero,
    Ideal.Quotient.mkₐ_eq_mk] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h

end Section

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_Noeth =====
section

/-!
# S4-JacSymB, file C: finiteness of `X^g` and `Sym^g X`; points of `A^g`

`X^g` and `Sym^g X` are of finite type over `k` (Artin-Tate for the invariants), `X^g` is a finite `Sym^g X`-module,
`Sym^g X` is Noetherian, `symMap` is functorial, and the kernel of a `k`-point of a ring `≃ₐ` a polynomial ring in `g`
variables is generated by `g` elements.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Comp

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {B'' : Type*} [CommRing B''] [Algebra k B''] {g : ℕ}

theorem xMap_comp (f : B →ₐ[k] B') (f' : B' →ₐ[k] B'') :
    xMap (g := g) (f'.comp f) = (xMap f').comp (xMap f) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change (xMap (f'.comp f)).comp (inc i) = ((xMap f').comp (xMap f)).comp (inc i)
  rw [xMap_inc, AlgHom.comp_assoc, xMap_inc, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, xMap_inc]

theorem symMap_comp (f : B →ₐ[k] B') (f' : B' →ₐ[k] B'') :
    symMap (g := g) (f'.comp f) = (symMap f').comp (symMap f) := by
  ext x
  change xMap (f'.comp f) (x : XPow k B g) = xMap f' (xMap f x)
  rw [xMap_comp]
  rfl

theorem finiteType_xPow [Algebra.FiniteType k B] : Algebra.FiniteType k (XPow k B g) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)
  refine ⟨⟨Finset.univ.biUnion (fun i : Fin g => s.image (inc i)), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r b =>
    refine Subalgebra.smul_mem _ ?_ r
    rw [← prod_inc]
    refine prod_mem fun i _ => ?_
    have hb : b i ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
    have h1 : inc i (b i) ∈ (Algebra.adjoin k (s : Set B)).map (inc i) := Subalgebra.mem_map.2 ⟨b i, hb, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine Algebra.adjoin_mono ?_ h1
    rintro y ⟨z, hz, rfl⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, Finset.mem_image.2 ⟨z, hz, rfl⟩⟩
  | add x y hx hy => exact add_mem hx hy

end Comp

section Noeth

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] {g : ℕ}

instance : Algebra.FiniteType k (XPow k B g) := finiteType_xPow

instance : Algebra.FiniteType (SymRing k B g) (XPow k B g) :=
  Algebra.FiniteType.of_restrictScalars_finiteType (R := k) (S := SymRing k B g) (A := XPow k B g)

instance moduleFinite_symRing : Module.Finite (SymRing k B g) (XPow k B g) := Algebra.IsIntegral.finite

instance finiteType_symRing : Algebra.FiniteType k (SymRing k B g) :=
  ⟨fg_of_fg_of_fg (A := k) (B := SymRing k B g) (C := XPow k B g) Algebra.FiniteType.out
    Module.Finite.fg_top Subtype.val_injective⟩

instance isNoetherianRing_symRing : IsNoetherianRing (SymRing k B g) :=
  Algebra.FiniteType.isNoetherianRing k _

instance isNoetherianRing_xPow : IsNoetherianRing (XPow k B g) :=
  Algebra.FiniteType.isNoetherianRing k _

end Noeth

section Point

variable {k : Type*} [Field k] {g : ℕ}

/-- The kernel of a `k`-point of a ring isomorphic to `k[X_1, ..., X_g]` is generated by `g` elements. -/
theorem ker_eq_span_of_equiv {R : Type*} [CommRing R] [Algebra k R] (e : R ≃ₐ[k] MvPolynomial (Fin g) k)
    (ψ : R →ₐ[k] k) :
    RingHom.ker ψ = Ideal.span (Set.range fun j : Fin g =>
      e.symm (MvPolynomial.X j) - algebraMap k R (ψ (e.symm (MvPolynomial.X j)))) := by
  set I := Ideal.span (Set.range fun j : Fin g =>
      e.symm (MvPolynomial.X j) - algebraMap k R (ψ (e.symm (MvPolynomial.X j))))
  have hq : (Ideal.Quotient.mkₐ k I).comp (e.symm : MvPolynomial (Fin g) k →ₐ[k] R) =
      ((Algebra.ofId k (R ⧸ I)).comp ψ).comp (e.symm : MvPolynomial (Fin g) k →ₐ[k] R) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply]
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hq' : ∀ r : R, Ideal.Quotient.mk I r = algebraMap k (R ⧸ I) (ψ r) := fun r => by
    have h := DFunLike.congr_fun hq (e r)
    have he : (e.symm : MvPolynomial (Fin g) k →ₐ[k] R) (e r) = r := e.symm_apply_apply r
    simp only [AlgHom.comp_apply, he, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply] at h
    exact h
  apply le_antisymm
  · intro r hr
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq', (RingHom.mem_ker).1 hr, map_zero]
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker]

end Point

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_SymLoc =====
section

/-!
# S4-JacSymB, file F4: `Sym^g` commutes with localization at a norm (L12)

If `B → B'` is injective and `B' = B[1/w]`, then `Sym^g B' = (Sym^g B)[1/N w]` with `N w = ∏_l w_l` (over a field `k`).
So the chart maps `Spec Sym^g B_A' → Spec Sym^g B_A` are open immersions.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section SymLoc

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

theorem xMap_id : xMap (g := g) (AlgHom.id k B) = AlgHom.id k (XPow k B g) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change (xMap (AlgHom.id k B)).comp (inc i) = (AlgHom.id k _).comp (inc i)
  rw [xMap_inc]
  rfl

theorem symMap_id : symMap (g := g) (AlgHom.id k B) = AlgHom.id k (SymRing k B g) := by
  ext x
  change xMap (AlgHom.id k B) (x : XPow k B g) = x
  rw [xMap_id]
  rfl

theorem secMap_xMap (f : B →ₐ[k] B') (s : B' →ₗ[k] B) (hs : ∀ b, s (f b) = b) (x : XPow k B g) :
    secMap s (xMap f x) = x := by
  change ((secMap s).comp (xMap f).toLinearMap) x = (LinearMap.id : XPow k B g →ₗ[k] XPow k B g) x
  congr 1
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro b
  simp [secMap, PiTensorProduct.map_tprod, hs]

theorem xMap_injective (f : B →ₐ[k] B') (hf : Function.Injective f) : Function.Injective (xMap (g := g) f) := by
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (by exact hf))
  have hs' : ∀ b, s (f b) = b := fun b => by simpa using LinearMap.congr_fun hs b
  intro x y hxy
  rw [← secMap_xMap f s hs' x, hxy, secMap_xMap f s hs' y]

theorem symMap_injective (f : B →ₐ[k] B') (hf : Function.Injective f) : Function.Injective (symMap (g := g) f) :=
  fun x y hxy => Subtype.ext (xMap_injective f hf (by
    have := congrArg (fun z : SymRing k B' g => (z : XPow k B' g)) hxy
    simpa only [symMap_coe] using this))

variable (k) in
/-- The norm `N w = ∏_l w_l`, an `S_g`-invariant. -/
noncomputable def normS (w : B) : SymRing k B g :=
  ⟨∏ l, inc l w, (mem_symRing _).mpr fun σ => by
    rw [perm_smul_def, map_prod]
    exact Fintype.prod_equiv σ _ _ fun l => AlgHom.congr_fun (permHom_comp_inc σ l) w⟩

theorem normS_coe (w : B) : (normS k (g := g) w : XPow k B g) = ∏ l, inc l w := rfl

theorem normS_mul (a b : B) : normS k (g := g) (a * b) = normS k a * normS k b := by
  apply Subtype.ext
  simp only [normS_coe, MulMemClass.coe_mul, map_mul, Finset.prod_mul_distrib]

theorem normS_one : normS k (g := g) (1 : B) = 1 := by
  apply Subtype.ext
  simp only [normS_coe, map_one, Finset.prod_const_one, OneMemClass.coe_one]

theorem xMap_prod_inc (f : B →ₐ[k] B') (w : B) : xMap (g := g) f (∏ l, inc l w) = ∏ l, inc l (f w) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun l _ => AlgHom.congr_fun (xMap_inc f l) w

theorem symMap_normS (f : B →ₐ[k] B') (w : B) : symMap (g := g) f (normS k w) = normS k (f w) := by
  apply Subtype.ext
  rw [symMap_coe, normS_coe, normS_coe, xMap_prod_inc]

/-- `X'^g = X^g[1/N w]` on elements. -/
theorem exists_xMap_eq (f : B →ₐ[k] B') (w : B) (hs : ∀ b' : B', ∃ (n : ℕ) (b : B), f b = f w ^ n * b')
    (t : XPow k B' g) : ∃ (n : ℕ) (u : XPow k B g), xMap f u = (∏ l, inc l (f w)) ^ n * t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r b' =>
    choose n b hb using fun l => hs (b' l)
    refine ⟨∑ l, n l, r • PiTensorProduct.tprod k (fun l => w ^ (∑ l, n l - n l) * b l), ?_⟩
    rw [map_smul, xMap_tprod, mul_smul_comm, ← prod_inc, ← prod_inc, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← map_pow, ← map_mul, map_mul f, map_pow f, hb l, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))]
  | add t1 t2 h1 h2 =>
    obtain ⟨n1, u1, hu1⟩ := h1
    obtain ⟨n2, u2, hu2⟩ := h2
    refine ⟨n1 + n2, (∏ l, inc l w) ^ n2 * u1 + (∏ l, inc l w) ^ n1 * u2, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, hu1, hu2, xMap_prod_inc]
    ring

/-- `Sym^g B' = (Sym^g B)[1/N w]` when `B' = B[1/w]` (`B → B'` injective). -/
theorem isLocalization_symMap (f : B →ₐ[k] B') (hf : Function.Injective f) (w : B) (hu : IsUnit (f w))
    (hs : ∀ b' : B', ∃ (n : ℕ) (b : B), f b = f w ^ n * b') :
    letI := (symMap (g := g) f).toRingHom.toAlgebra
    IsLocalization.Away (normS k (g := g) w) (SymRing k B' g) := by
  letI := (symMap (g := g) f).toRingHom.toAlgebra
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · change IsUnit (symMap f (normS k w))
    rw [symMap_normS]
    obtain ⟨v, hv⟩ := hu
    refine ⟨⟨normS k (f w), normS k (↑v⁻¹ : B'), ?_, ?_⟩, rfl⟩
    · rw [← normS_mul, ← hv, Units.mul_inv, normS_one]
    · rw [← normS_mul, ← hv, Units.inv_mul, normS_one]
  · intro s
    obtain ⟨n, u, hu'⟩ := exists_xMap_eq f w hs (s : XPow k B' g)
    have h1 : (∏ l, inc l (f w)) ^ n * (s : XPow k B' g) =
        ((normS k (g := g) (f w) ^ n * s : SymRing k B' g) : XPow k B' g) := by
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, normS_coe]
    have hinv : u ∈ SymRing k B g := by
      rw [mem_symRing]
      intro σ
      apply xMap_injective f hf
      rw [xMap_smul, hu', h1, smul_symRing]
    refine ⟨n, ⟨u, hinv⟩, ?_⟩
    change s * symMap f (normS k w) ^ n = symMap f ⟨u, hinv⟩
    apply Subtype.ext
    rw [symMap_normS, symMap_coe]
    change _ = xMap f u
    rw [hu', h1, mul_comm]
  · intro a b hab
    exact ⟨0, by rw [pow_zero, one_mul, one_mul]; exact symMap_injective f hf hab⟩

end SymLoc

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacLaw_Span =====
section

/-!
# S4-JacLaw, file O1: `Sym^g(B)` is spanned by norms (polarization over an infinite field)

For an infinite field `k` and any commutative `k`-algebra `B`, the symmetric tensors
`SymRing k B g ⊆ ⨂^g B` are the `k`-span of the norms `N(w) = ∏_l w_l = w ⊗ ... ⊗ w`.
Proof: a functional `ℓ` killing every `w ⊗ ... ⊗ w` gives, for `w = Σ_j x_j b_j`, a polynomial identity in
the `x_j`; over an infinite field all its coefficients vanish, i.e. `ℓ` kills every orbit sum of basis
tensors; a symmetric tensor is a combination of orbit sums.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym

section Span

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

theorem normS_coe_eq_tprod (w : B) :
    (normS k (g := g) w : XPow k B g) = PiTensorProduct.tprod k (fun _ : Fin g => w) := by
  have h : (fun _ : Fin g => w) = ∏ i, Pi.mulSingle i w :=
    (Finset.univ_prod_mulSingle (fun _ : Fin g => w)).symm
  rw [normS_coe, h, PiTensorProduct.tprod_prod]
  rfl

theorem sum_single_apply {ι : Type*} [DecidableEq ι] (f : Fin g → ι) (a : ι) :
    (∑ i, Finsupp.single (f i) 1 : ι →₀ ℕ) a = Multiset.count a (Finset.univ.val.map f) := by
  rw [Finsupp.finsetSum_apply, Multiset.count_map]
  simp only [Finsupp.single_apply, Finset.sum_boole, Nat.cast_id]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun i _ => eq_comm)

theorem mset_eq_of_sum_single_eq {ι : Type*} [DecidableEq ι] (f h : Fin g → ι)
    (hfh : (∑ i, Finsupp.single (f i) 1 : ι →₀ ℕ) = ∑ i, Finsupp.single (h i) 1) : mset f = mset h := by
  apply Sym.coe_injective
  rw [mset_coe, mset_coe]
  ext a
  rw [← sum_single_apply, ← sum_single_apply, hfh]

theorem repr_permHom {ι : Type*} (b : Module.Basis ι k B) (σ : Equiv.Perm (Fin g)) (x : XPow k B g)
    (p : Fin g → ι) :
    (Basis.piTensorProduct (fun _ : Fin g => b)).repr (permHom σ x) p =
      (Basis.piTensorProduct (fun _ : Fin g => b)).repr x (p ∘ σ) := by
  classical
  set bT := Basis.piTensorProduct (fun _ : Fin g => b)
  have key : (Finsupp.lapply p).comp (bT.repr.toLinearMap.comp (permHom σ).toLinearMap) =
      (Finsupp.lapply (p ∘ σ)).comp bT.repr.toLinearMap := by
    refine bT.ext fun q => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, Finsupp.lapply_apply]
    have hq : permHom σ (bT q) = bT (q ∘ σ.symm) := by
      simp only [bT, Basis.piTensorProduct_apply, permHom_tprod, Function.comp_apply]
    rw [hq, Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
    have hiff : q ∘ σ.symm = p ↔ q = p ∘ σ := by
      constructor
      · rintro rfl; funext i; simp
      · rintro rfl; funext i; simp
    simp only [hiff]
  exact LinearMap.congr_fun key x

/-- Polarization: a permutation-invariant tensor is a combination of `w ⊗ ... ⊗ w`. -/
theorem mem_span_tprod_of_fixed [Infinite k] (t : XPow k B g)
    (ht : ∀ σ : Equiv.Perm (Fin g), permHom σ t = t) :
    t ∈ Submodule.span k (Set.range fun w : B => PiTensorProduct.tprod k (fun _ : Fin g => w)) := by
  classical
  set W := Submodule.span k (Set.range fun w : B => PiTensorProduct.tprod k (fun _ : Fin g => w))
  by_contra hnot
  obtain ⟨ℓ, hℓt, hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hℓW : ∀ w : B, ℓ (PiTensorProduct.tprod k (fun _ : Fin g => w)) = 0 := by
    intro w
    have h1 : ℓ (PiTensorProduct.tprod k (fun _ : Fin g => w)) ∈ W.map ℓ :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨w, rfl⟩)
    rwa [hW, Submodule.mem_bot] at h1
  set b := Module.Basis.ofVectorSpace k B
  set bT := Basis.piTensorProduct (fun _ : Fin g => b)
  set c := bT.repr t
  set J := c.support.biUnion (fun f => Finset.univ.image f)
  set F := Fintype.piFinset (fun _ : Fin g => J)
  have hsF : c.support ⊆ F := by
    intro f hf
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩
  set κ : (Fin g → Module.Basis.ofVectorSpaceIndex k B) → (Module.Basis.ofVectorSpaceIndex k B →₀ ℕ) :=
    fun f => ∑ i, Finsupp.single (f i) 1
  set P : MvPolynomial (Module.Basis.ofVectorSpaceIndex k B) k :=
    ∑ f ∈ F, MvPolynomial.C (ℓ (bT f)) * ∏ i, MvPolynomial.X (f i)
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero]
    have hw := hℓW (∑ j ∈ J, x j • b j)
    rw [MultilinearMap.map_sum_finset (PiTensorProduct.tprod k) (fun _ j => x j • b j)
      (fun _ : Fin g => J)] at hw
    simp only [MultilinearMap.map_smul_univ, map_sum, map_smul, smul_eq_mul] at hw
    rw [← hw]
    simp only [P, map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [mul_comm]
    simp only [bT, Basis.piTensorProduct_apply]
  have hcoeff : ∀ f0, ∑ f ∈ F.filter (fun f => κ f = κ f0), ℓ (bT f) = 0 := by
    intro f0
    have h0 := congrArg (MvPolynomial.coeff (κ f0)) hP
    rw [MvPolynomial.coeff_zero] at h0
    rw [← h0, Finset.sum_filter]
    simp only [P, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hm : (∏ i, MvPolynomial.X (f i) : MvPolynomial (Module.Basis.ofVectorSpaceIndex k B) k) =
        MvPolynomial.monomial (κ f) 1 := (MvPolynomial.monomial_sum_one _ _).symm
    rw [hm, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial]
  have hinv : ∀ f f0, κ f = κ f0 → c f = c f0 := by
    intro f f0 hff
    obtain ⟨σ, hσ⟩ := exists_perm_of_mset_eq f0 f (mset_eq_of_sum_single_eq f0 f hff.symm)
    rw [hσ]
    show bT.repr t (f0 ∘ σ) = bT.repr t f0
    rw [← repr_permHom, ht]
  apply hℓt
  have ht' : ℓ t = ∑ f ∈ F, c f * ℓ (bT f) := by
    conv_lhs => rw [← bT.linearCombination_repr t]
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    simp only [map_smul, smul_eq_mul]
    rw [Finsupp.sum]
    exact Finset.sum_subset hsF fun f _ hf => by
      rw [Finsupp.notMem_support_iff.mp hf, zero_mul]
  rw [ht', ← Finset.sum_fiberwise_of_maps_to (g := κ) (t := F.image κ)
    (fun f hf => Finset.mem_image_of_mem κ hf)]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨f0, -, rfl⟩ := Finset.mem_image.mp he
  rw [Finset.sum_congr rfl fun f hf => by rw [hinv f f0 (Finset.mem_filter.mp hf).2], ← Finset.mul_sum,
    hcoeff f0, mul_zero]

/-- **O1**: over an infinite field, `Sym^g(B)` is the `k`-span of the norms `N(w)`. -/
theorem span_normS [Infinite k] : Submodule.span k (Set.range (normS k (B := B) (g := g))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx := mem_span_tprod_of_fixed (x : XPow k B g) (fun σ => (mem_symRing _).mp x.2 σ)
  have hrange : (Set.range fun w : B => PiTensorProduct.tprod k (fun _ : Fin g => w)) =
      (SymRing k B g).val.toLinearMap '' Set.range (normS k (B := B) (g := g)) := by
    rw [← Set.range_comp]
    ext y
    simp only [Set.mem_range, Function.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val,
      normS_coe_eq_tprod]
  rw [hrange, Submodule.span_image] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  rwa [← hyx']

end Span

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacSymB_GenPoly =====
section

/-!
# S4-JacSymB, file H2b: the generic polynomial `E(w) = ∏_l (1 - w_l X)` (L12, valuative criterion)

For `w ∈ B`, `E(w) = ∏_l (1 - inc_l(w) X) ∈ X^g(B)[X]` has symmetric coefficients, so it comes from
`genPoly w ∈ Sym^g(B)[X]`. Facts: naturality in `B`; `E(w)(t) = N(1 - t w)`; the Taylor identity
`N(1 - t a) · E(b) = E(a)(X + t)` when `(1 - t a) b = a`; and `reflect g E(w) = ∏_l (X - w_l)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section GenPoly

open Polynomial

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

/-- `E(w) = ∏_l (1 - w_l X)` over `X^g(B)`. -/
noncomputable def genE (w : B) : (XPow k B g)[X] := ∏ l, (1 - C (inc l w) * X)

theorem map_permHom_genE (σ : Equiv.Perm (Fin g)) (w : B) :
    (genE (k := k) (g := g) w).map (permHom σ).toRingHom = genE w := by
  have h : ∀ l : Fin g, (permHom σ) (inc (k := k) l w) = inc (σ l) w := fun l => by
    rw [← AlgHom.comp_apply, permHom_comp_inc]
  simp only [genE, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h]
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

theorem genE_coeff_mem (w : B) (j : ℕ) : (genE (k := k) (g := g) w).coeff j ∈ SymRing k B g := by
  rw [mem_symRing]
  intro σ
  rw [perm_smul_def]
  have := congrArg (fun p => p.coeff j) (map_permHom_genE (k := k) σ w)
  simp only [coeff_map] at this
  exact this

theorem genE_mem_lifts (w : B) : genE (k := k) (g := g) w ∈ lifts (SymRing k B g).val.toRingHom := by
  rw [lifts_iff_coeff_lifts]
  intro j
  exact ⟨⟨_, genE_coeff_mem w j⟩, rfl⟩

/-- `E(w)` with coefficients in `Sym^g(B)`. -/
noncomputable def genPoly (w : B) : (SymRing k B g)[X] :=
  Classical.choose ((mem_lifts _).mp (genE_mem_lifts (k := k) (g := g) w))

theorem map_genPoly (w : B) : (genPoly (k := k) (g := g) w).map (SymRing k B g).val.toRingHom = genE w :=
  Classical.choose_spec ((mem_lifts _).mp (genE_mem_lifts (k := k) (g := g) w))

theorem map_val_injective : Function.Injective (Polynomial.map (SymRing k B g).val.toRingHom) :=
  Polynomial.map_injective _ fun _ _ h => Subtype.ext h

theorem coeff_genPoly (w : B) (j : ℕ) :
    ((genPoly (k := k) (g := g) w).coeff j : XPow k B g) = (genE w).coeff j := by
  rw [← map_genPoly w, coeff_map]
  rfl

theorem symMap_genPoly {B' : Type*} [CommRing B'] [Algebra k B'] (f : B →ₐ[k] B') (w : B) :
    (genPoly (k := k) (g := g) w).map (symMap f).toRingHom = genPoly (f w) := by
  apply map_val_injective
  rw [Polynomial.map_map, map_genPoly]
  have e : (SymRing k B' g).val.toRingHom.comp (symMap (g := g) f).toRingHom =
      (xMap f).toRingHom.comp (SymRing k B g).val.toRingHom := RingHom.ext fun _ => rfl
  rw [e, ← Polynomial.map_map, map_genPoly]
  simp only [genE, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← AlgHom.comp_apply, xMap_inc, AlgHom.comp_apply]

theorem genPoly_eval (w : B) (t : k) :
    (genPoly (k := k) (g := g) w).eval (algebraMap k _ t) = normS k (1 - algebraMap k B t * w) := by
  apply Subtype.val_injective
  have h1 : ((genPoly (k := k) (g := g) w).eval (algebraMap k (SymRing k B g) t)).1 =
      (genE w).eval (algebraMap k (XPow k B g) t) := by
    rw [← map_genPoly w, eval_map]
    exact (eval₂_hom (SymRing k B g).val.toRingHom (algebraMap k (SymRing k B g) t)).symm
  rw [h1, normS_coe, genE, eval_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, map_sub, map_one, map_mul, AlgHom.commutes]
  ring

/-- The Taylor identity: if `(1 - t a) b = a` then `N(1 - t a) · E(b) = E(a)(X + t)`. -/
theorem genPoly_taylor (a b : B) (t : k) (h : (1 - algebraMap k B t * a) * b = a) :
    C (normS k (g := g) (1 - algebraMap k B t * a)) * genPoly b =
      taylor (algebraMap k (SymRing k B g) t) (genPoly a) := by
  apply map_val_injective
  rw [Polynomial.map_mul, map_C, map_genPoly, map_taylor, map_genPoly]
  change C (∏ l, inc l (1 - algebraMap k B t * a)) * genE b = taylor (algebraMap k (XPow k B g) t) (genE a)
  rw [genE, genE, taylor_apply, prod_comp, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  have hz : (1 - algebraMap k (XPow k B g) t * inc l a) * inc l b = inc l a := by
    have := congrArg (inc (k := k) (g := g) l) h
    simpa only [map_mul, map_sub, map_one, AlgHom.commutes] using this
  have hz' : (1 - C (algebraMap k (XPow k B g) t) * C (inc l a)) * C (inc l b) = C (inc l a) := by
    simpa only [map_mul, map_sub, map_one] using congrArg C hz
  simp only [map_sub, map_one, map_mul, AlgHom.commutes, sub_comp, one_comp, mul_comp, C_comp, X_comp]
  linear_combination (-X) * hz'

theorem reflect_prod_one_sub {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (f : ι → R) :
    reflect s.card (∏ i ∈ s, (1 - C (f i) * X)) = ∏ i ∈ s, (X - C (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflect_one]
  | insert a s ha ih =>
    have hdeg : (∏ i ∈ s, (1 - C (f i) * X)).natDegree ≤ s.card := by
      refine (natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => (?_ : (1 - C (f i) * X).natDegree ≤ 1)).trans (by simp)
      compute_degree!
    have h1 : reflect 1 (1 - C (f a) * X) = X - C (f a) := by
      rw [reflect_sub, reflect_one, show (C (f a) * X : R[X]) = C (f a) * X ^ 1 by rw [pow_one],
        reflect_C_mul_X_pow, revAt_le (le_refl 1)]
      simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      show s.card + 1 = 1 + s.card from add_comm _ _, reflect_mul _ _ (by compute_degree!) hdeg, ih, h1]

theorem reflect_genE (w : B) : reflect g (genE (k := k) (g := g) w) = ∏ l : Fin g, (X - C (inc l w)) := by
  have := reflect_prod_one_sub (Finset.univ : Finset (Fin g)) (fun l => (inc l w : XPow k B g))
  rwa [Finset.card_univ, Fintype.card_fin] at this

end GenPoly

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacLaw_Crit =====
section

/-!
# S4-JacLaw, file O2: the morphism criterion for maps into `Sym^n`

`R` reduced of finite type over an algebraically closed field `k`. A map `μ` from the `k`-points of `R` to the
`k`-points of `Sym^n(B)` comes from a (unique) `k`-algebra map `Sym^n(B) → R` as soon as the pullback of every
norm `N(w)` is a function in `R`. Reason: `R` embeds into functions on its `k`-points (Nullstellensatz), and the
norms span `Sym^n(B)` (file O1). Also: values of `N(w)` and of the generic polynomial `E(w)` at a point `symPt a`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym Polynomial

section Crit

variable {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]

/-- Evaluation of `R` at its `k`-points. -/
noncomputable def evPts : R →ₐ[k] ((R →ₐ[k] k) → k) := AlgHom.pi (fun x => x)

theorem evPts_apply (r : R) (x : R →ₐ[k] k) : evPts (k := k) r x = x r := rfl

/-- Nullstellensatz for reduced rings: a function vanishing at all `k`-points is zero. -/
theorem evPts_injective [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R] :
    Function.Injective (evPts (k := k) (R := R)) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hj : (⊥ : Ideal R).jacobson = ⊥ := IsJacobsonRing.out' ⊥ Ideal.isRadical_bot
  have hc' : c ∈ (⊥ : Ideal R).jacobson := by
    refine Ideal.mem_sInf.2 ?_
    rintro m ⟨-, hm⟩
    have := hm
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) m
    rw [← hφ, RingHom.mem_ker]
    exact congr_fun hc φ
  rw [hj] at hc'
  exact (Submodule.mem_bot _).1 hc'

variable {S : Type*} [CommRing S] [Algebra k S]

/-- Maps into `R` are determined by their compositions with the `k`-points of `R`. -/
theorem algHom_ext_pts [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R] {φ ψ : S →ₐ[k] R}
    (h : ∀ x : R →ₐ[k] k, x.comp φ = x.comp ψ) : φ = ψ := by
  ext s
  apply evPts_injective (k := k)
  funext x
  exact AlgHom.congr_fun (h x) s

/-- Pullback of functions along a map of `k`-points. -/
noncomputable def pullPts (μ : (R →ₐ[k] k) → (S →ₐ[k] k)) : S →ₐ[k] ((R →ₐ[k] k) → k) := AlgHom.pi μ

theorem pullPts_apply (μ : (R →ₐ[k] k) → (S →ₐ[k] k)) (s : S) (x : R →ₐ[k] k) : pullPts μ s x = μ x s := rfl

variable {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}

theorem range_pullPts_le [IsAlgClosed k] (μ : (R →ₐ[k] k) → (SymRing k B n →ₐ[k] k))
    (hμ : ∀ w : B, ∃ r : R, ∀ x, x r = μ x (normS k w)) (s : SymRing k B n) :
    pullPts μ s ∈ (evPts (k := k) (R := R)).range := by
  let T : Submodule k (SymRing k B n) :=
    (Subalgebra.toSubmodule (evPts (k := k) (R := R)).range).comap (pullPts μ).toLinearMap
  have hT : Submodule.span k (Set.range (normS k (B := B) (g := n))) ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨r, hr⟩ := hμ w
    exact ⟨r, funext hr⟩
  have hs : s ∈ T := hT (by rw [span_normS]; trivial)
  exact hs

/-- **O2, morphism criterion**: the `k`-algebra map `Sym^n(B) → R` inducing `μ` on `k`-points. -/
noncomputable def liftPts [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R]
    (μ : (R →ₐ[k] k) → (SymRing k B n →ₐ[k] k)) (hμ : ∀ w : B, ∃ r : R, ∀ x, x r = μ x (normS k w)) :
    SymRing k B n →ₐ[k] R :=
  (AlgEquiv.ofInjective (evPts (k := k) (R := R)) evPts_injective).symm.toAlgHom.comp
    ((pullPts μ).codRestrict _ (range_pullPts_le μ hμ))

theorem evPts_liftPts [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R]
    (μ : (R →ₐ[k] k) → (SymRing k B n →ₐ[k] k)) (hμ : ∀ w : B, ∃ r : R, ∀ x, x r = μ x (normS k w))
    (s : SymRing k B n) : evPts (k := k) (liftPts μ hμ s) = pullPts μ s := by
  rw [← AlgEquiv.ofInjective_apply (evPts (k := k) (R := R)) evPts_injective]
  simp only [liftPts, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  rfl

theorem comp_liftPts [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R]
    (μ : (R →ₐ[k] k) → (SymRing k B n →ₐ[k] k)) (hμ : ∀ w : B, ∃ r : R, ∀ x, x r = μ x (normS k w))
    (x : R →ₐ[k] k) : x.comp (liftPts μ hμ) = μ x := by
  ext s
  exact congr_fun (evPts_liftPts μ hμ s) x

/-- The norm `N(w)` at the point `a_1 + ... + a_n`. -/
theorem symPt_normS (a : Fin n → (B →ₐ[k] k)) (w : B) : symPt a (normS k w) = ∏ l, a l w := by
  rw [symPt_apply, normS_coe, map_prod]
  exact Finset.prod_congr rfl fun l _ => AlgHom.congr_fun (ptOf_inc a l) w

end Crit

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_LinAlg =====
section

/-!
# S4-JacLaw, file O3: linear algebra for the negation step

* `crossVec M`: the cofactor vector of an `m × (m+1)` matrix (`M *ᵥ crossVec M = 0`, entries are signed maximal
  minors, compatible with ring maps). Over a field, if `crossVec M' ≠ 0` for `M'` made of `m` rows of `M` and
  `ker M ≠ 0`, then `ker M = K ∙ crossVec M'` (Cramer's rule for the kernel line).
* `det_fromCols_eq`: if `V = Aα F + Z E` then `det [Aα | V] = det [Aα | Z] · det E` (block triangular).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Matrix

section Cross

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The cofactor vector of an `m × (m+1)` matrix. -/
def crossVec (M : Matrix (Fin m) (Fin (m + 1)) R) : Fin (m + 1) → R :=
  fun j => (-1) ^ (j : ℕ) * (M.submatrix id j.succAbove).det

theorem det_cons (M : Matrix (Fin m) (Fin (m + 1)) R) (v : Fin (m + 1) → R) :
    (Matrix.of (Fin.cons v (fun i => M i) : Fin (m + 1) → Fin (m + 1) → R)).det =
      ∑ j, v j * crossVec M j := by
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : (Matrix.of (Fin.cons v (fun i => M i) : Fin (m + 1) → Fin (m + 1) → R)).submatrix Fin.succ
      j.succAbove = M.submatrix id j.succAbove := by
    ext a b
    simp
  rw [hs, crossVec, Matrix.of_apply, Fin.cons_zero]
  ring

theorem mulVec_crossVec (M : Matrix (Fin m) (Fin (m + 1)) R) : M *ᵥ crossVec M = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [← det_cons M (M i)]
  refine Matrix.det_zero_of_row_eq (i := 0) (j := i.succ) (Fin.succ_ne_zero i).symm ?_
  funext l
  simp

theorem crossVec_map {S : Type*} [CommRing S] (f : R →+* S) (M : Matrix (Fin m) (Fin (m + 1)) R) :
    crossVec (M.map f) = fun j => f (crossVec M j) := by
  funext j
  simp only [crossVec, map_mul, map_pow, map_neg, map_one, RingHom.map_det]
  rfl

end Cross

section Field

variable {K : Type*} [Field K] {m p : ℕ}

theorem surjective_of_crossVec_ne_zero (M : Matrix (Fin m) (Fin (m + 1)) K) (hc : crossVec M ≠ 0) :
    Function.Surjective M.mulVecLin := by
  obtain ⟨j, hj⟩ : ∃ j, crossVec M j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  have hdet : (M.submatrix id j.succAbove).det ≠ 0 := by
    intro h0
    apply hj
    rw [crossVec, h0, mul_zero]
  have hsurj : Function.Surjective (M.submatrix id j.succAbove).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨Fin.insertNth j 0 x, ?_⟩
  rw [← hx]
  funext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id]
  rw [Fin.sum_univ_succAbove _ j, Fin.insertNth_apply_same, mul_zero, zero_add]
  simp only [Fin.insertNth_apply_succAbove]

theorem finrank_ker_of_crossVec_ne_zero (M : Matrix (Fin m) (Fin (m + 1)) K) (hc : crossVec M ≠ 0) :
    Module.finrank K (LinearMap.ker M.mulVecLin) = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [LinearMap.range_eq_top.mpr (surjective_of_crossVec_ne_zero M hc), finrank_top] at h
  simp only [Module.finrank_fin_fun] at h
  omega

theorem ker_eq_span_crossVec_self (M : Matrix (Fin m) (Fin (m + 1)) K) (hc : crossVec M ≠ 0) :
    LinearMap.ker M.mulVecLin = K ∙ crossVec M := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact mulVec_crossVec M
  · rw [finrank_span_singleton hc, finrank_ker_of_crossVec_ne_zero M hc]

end Field

section Block

variable {R : Type*} [CommRing R] {a N : ℕ}

/-- Block-triangular determinant: `det [Aα | Aα F + Z E] = det [Aα | Z] · det E`. -/
theorem det_fromCols_eq (Aα : Matrix (Fin a ⊕ Fin N) (Fin a) R) (Z V : Matrix (Fin a ⊕ Fin N) (Fin N) R)
    (F : Matrix (Fin a) (Fin N) R) (E : Matrix (Fin N) (Fin N) R) (hV : V = Aα * F + Z * E) :
    (Matrix.fromCols Aα V).det = (Matrix.fromCols Aα Z).det * E.det := by
  have h : Matrix.fromCols Aα V = Matrix.fromCols Aα Z * Matrix.fromBlocks 1 F 0 E := by
    rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero, add_zero, hV]
  rw [h, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

end Block

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Gram =====
section

/-!
# S4-JacLaw O5: the trace matrix of a point of `Sym^d` and its kernel line

For `χ : Fin d → B` and `h : Fin (d+1) → B` the trace matrix `M[m, l] = tr(χ_m h_l)` has entries in
`S_d = SymRing k B d`. At the point `a_1 + ... + a_d` it equals `Eᵀ F` with `E[i, m] = a_i(χ_m)`,
`F[i, l] = a_i(h_l)`, so its cofactor vector is `det E • crossVec F` (`symPt_kerVec`). The section
`sPt = Σ_l c_l(A) h_l` vanishes at every `a_i`, and when one cofactor is nonzero every combination of
the `h_l` vanishing at all `a_i` is a multiple of it (`exists_eq_smul_sPt`).
Also: Nullstellensatz units (`isUnit_of_forall_ne_zero`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym Matrix

section CrossMul

variable {R : Type*} [CommRing R] {m : ℕ}

theorem crossVec_mul (E : Matrix (Fin m) (Fin m) R) (F : Matrix (Fin m) (Fin (m + 1)) R) :
    crossVec (E * F) = E.det • crossVec F := by
  funext j
  have hs : (E * F).submatrix id j.succAbove = E * F.submatrix id j.succAbove := by
    ext a b
    simp [Matrix.mul_apply]
  simp only [crossVec, Pi.smul_apply, smul_eq_mul, hs, Matrix.det_mul]
  ring

end CrossMul

section Unit

variable {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]

/-- Nullstellensatz: an element nonvanishing at every `k`-point is a unit. -/
theorem isUnit_of_forall_ne_zero [IsAlgClosed k] [Algebra.FiniteType k R] (r : R)
    (h : ∀ x : R →ₐ[k] k, x r ≠ 0) : IsUnit r := by
  by_contra hr
  obtain ⟨m, hm, hrm⟩ := Ideal.exists_le_maximal (Ideal.span {r}) (Ideal.span_singleton_ne_top hr)
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) m
  refine h φ ?_
  rw [← RingHom.mem_ker, hφ]
  exact hrm (Ideal.subset_span (Set.mem_singleton r))

end Unit

section Trace

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {d : ℕ}

variable (k) in
/-- The trace `tr w = Σ_l w_l`, an `S_d`-invariant. -/
noncomputable def traceS (w : B) : SymRing k B d :=
  ⟨∑ l, inc l w, (mem_symRing _).mpr fun σ => by
    rw [perm_smul_def, map_sum]
    exact Fintype.sum_equiv σ _ _ fun l => AlgHom.congr_fun (permHom_comp_inc σ l) w⟩

theorem symPt_traceS (a : Fin d → (B →ₐ[k] k)) (w : B) : symPt a (traceS k w) = ∑ l, a l w := by
  rw [symPt_apply]
  show ptOf a (∑ l, inc l w) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun l _ => AlgHom.congr_fun (ptOf_inc a l) w

variable (k) in
/-- The trace matrix `M[m, l] = tr(χ_m h_l)`. -/
noncomputable def traceMat (χ : Fin d → B) (h : Fin (d + 1) → B) :
    Matrix (Fin d) (Fin (d + 1)) (SymRing k B d) :=
  Matrix.of fun m l => traceS k (χ m * h l)

/-- The evaluation matrix `E[i, m] = a_i(f_m)`. -/
def evMat {n : ℕ} (a : Fin d → (B →ₐ[k] k)) (f : Fin n → B) : Matrix (Fin d) (Fin n) k :=
  Matrix.of fun i m => a i (f m)

theorem traceMat_map (a : Fin d → (B →ₐ[k] k)) (χ : Fin d → B) (h : Fin (d + 1) → B) :
    (traceMat k χ h).map (symPt a) = (evMat a χ)ᵀ * evMat a h := by
  ext m l
  simp only [traceMat, evMat, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, symPt_traceS, map_mul]

variable (k) in
/-- The kernel vector `c(A)`, entries in `S_d`. -/
noncomputable def kerVec (χ : Fin d → B) (h : Fin (d + 1) → B) : Fin (d + 1) → SymRing k B d :=
  crossVec (traceMat k χ h)

theorem symPt_kerVec (a : Fin d → (B →ₐ[k] k)) (χ : Fin d → B) (h : Fin (d + 1) → B) (l : Fin (d + 1)) :
    symPt a (kerVec k χ h l) = (evMat a χ).det * crossVec (evMat a h) l := by
  have h1 := congr_fun (crossVec_map (symPt a).toRingHom (traceMat k χ h)) l
  have h2 : (traceMat k χ h).map (symPt a).toRingHom = (evMat a χ)ᵀ * evMat a h :=
    traceMat_map a χ h
  rw [h2, crossVec_mul, det_transpose] at h1
  exact h1.symm

/-- The section `s_A = Σ_l c_l(A) h_l` at the point `a`. -/
noncomputable def sPt (a : Fin d → (B →ₐ[k] k)) (χ : Fin d → B) (h : Fin (d + 1) → B) : B :=
  ∑ l, symPt a (kerVec k χ h l) • h l

variable (a : Fin d → (B →ₐ[k] k)) (χ : Fin d → B) (h : Fin (d + 1) → B)

theorem apply_sPt (i : Fin d) : a i (sPt a χ h) = 0 := by
  have h0 : ∑ l, a i (h l) * crossVec (evMat a h) l = 0 := congr_fun (mulVec_crossVec (evMat a h)) i
  simp only [sPt, map_sum, map_smul, symPt_kerVec, smul_eq_mul]
  calc ∑ l, (evMat a χ).det * crossVec (evMat a h) l * a i (h l)
      = (evMat a χ).det * ∑ l, a i (h l) * crossVec (evMat a h) l := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = 0 := by rw [h0, mul_zero]

variable {a χ h}

theorem det_ne_zero_of_kerVec {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) :
    (evMat a χ).det ≠ 0 := by
  intro h0
  rw [symPt_kerVec, h0, zero_mul] at hl
  exact hl rfl

theorem crossVec_ne_zero_of_kerVec {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) :
    crossVec (evMat a h) ≠ 0 := by
  intro h0
  rw [symPt_kerVec, h0, Pi.zero_apply, mul_zero] at hl
  exact hl rfl

/-- The points of a good `A` are distinct. -/
theorem injective_of_kerVec {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  exact det_ne_zero_of_kerVec hl
    (Matrix.det_zero_of_row_eq hne (funext fun m => by simp [evMat, hij]))

theorem sPt_ne_zero (hli : LinearIndependent k h) {l0 : Fin (d + 1)}
    (hl : symPt a (kerVec k χ h l0) ≠ 0) : sPt a χ h ≠ 0 :=
  fun h0 => hl (Fintype.linearIndependent_iff.1 hli _ h0 l0)

/-- **The kernel line.** A combination of the `h_l` vanishing at every `a_i` is a multiple of `s_A`. -/
theorem exists_eq_smul_sPt {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) (y : Fin (d + 1) → k)
    (hy : ∀ i, a i (∑ l, y l • h l) = 0) : ∃ t : k, ∑ l, y l • h l = t • sPt a χ h := by
  have hc := crossVec_ne_zero_of_kerVec hl
  have hE := det_ne_zero_of_kerVec hl
  have hmem : y ∈ LinearMap.ker (evMat a h).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    have := hy i
    simp only [map_sum, map_smul, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, evMat, Matrix.of_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [ker_eq_span_crossVec_self _ hc, Submodule.mem_span_singleton] at hmem
  obtain ⟨t, ht⟩ := hmem
  refine ⟨t * ((evMat a χ).det)⁻¹, ?_⟩
  rw [← ht]
  simp only [sPt, symPt_kerVec, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  field_simp

theorem mem_span_sPt {l0 : Fin (d + 1)} (hl : symPt a (kerVec k χ h l0) ≠ 0) {f : B}
    (hf : f ∈ Submodule.span k (Set.range h)) (hz : ∀ i, a i f = 0) : f ∈ k ∙ sPt a χ h := by
  obtain ⟨y, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hf
  obtain ⟨t, ht⟩ := exists_eq_smul_sPt hl y hz
  rw [ht]
  exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)

end Trace

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Pres =====
section

/-!
# S4-JacLaw, file O4b: the Δ-ratio presentation of `B ⧸ (s)`

`L' , L ⊆ B` finite-dimensional `k`-subspaces with `s • L' ⊆ L`, bases `α` of `L'` and `β` of `L`
(indexed by `Fin a ⊕ Fin N`), and `e : Fin N → L`. `presDet = Δ_1 = det_β [s α | e]`.
* `linIndep_mk_of_presDet`: if `L ∩ (s) = s L'` and `Δ_1 ≠ 0`, the images of `e` in `B ⧸ (s)` are independent.
* `presDet_ne_zero_of_linIndep`: conversely (`B` a domain, `s ≠ 0`), independence of the images gives `Δ_1 ≠ 0`.
* `det_pres_charpoly`: if `Δ_1 ≠ 0`, the images of `e` form a basis and `w e_i ∈ L`, then
  `det [s α | X e - w e] = Δ_1 · charpoly (mult. by w on B ⧸ (s))` (all columns in `β`-coordinates).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Polynomial Module Matrix

section Pres

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
variable (s : B) {L L' : Submodule k B} (hsL : ∀ y ∈ L', s * y ∈ L)
variable {a N : ℕ} (α : Basis (Fin a) k L') (β : Basis (Fin a ⊕ Fin N) k L)
variable {e : Fin N → B} (he : ∀ i, e i ∈ L)

/-- The family `s α_b, e_i` in `L`. -/
noncomputable def presFam : Fin a ⊕ Fin N → L :=
  Sum.elim (fun b => ⟨s * α b, hsL _ (α b).2⟩) (fun i => ⟨e i, he i⟩)

/-- `Δ_1 = det_β [s α | e]`. -/
noncomputable def presDet : k := β.det (presFam s hsL α he)

theorem coe_presFam_sum (G : Fin a ⊕ Fin N → k) :
    ((∑ r, G r • presFam s hsL α he r : L) : B) =
      ∑ b, G (Sum.inl b) • (s * (α b : B)) + ∑ i, G (Sum.inr i) • e i := by
  rw [Fintype.sum_sum_type]
  simp [presFam]

theorem presDet_ne_zero_iff :
    presDet s hsL α β he ≠ 0 ↔ LinearIndependent k (presFam s hsL α he) := by
  have : FiniteDimensional k L := Module.Finite.of_basis β
  constructor
  · intro h
    exact (β.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr h)).1
  · intro h
    have hsp := h.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis β).symm
    exact (β.is_basis_iff_det.mp ⟨h, hsp⟩).ne_zero

theorem linIndep_mk_of_presDet (hP : ∀ z ∈ L, z ∈ Ideal.span {s} → ∃ y ∈ L', z = s * y)
    (h : presDet s hsL α β he ≠ 0) :
    LinearIndependent k (fun i => Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i)) := by
  have hli := (presDet_ne_zero_iff s hsL α β he).mp h
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg
  have hz : (∑ i, g i • e i) ∈ Ideal.span {s} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk k, map_sum]
    simpa only [map_smul] using hg
  have hzL : (∑ i, g i • e i) ∈ L := Submodule.sum_mem _ fun i _ => L.smul_mem _ (he i)
  obtain ⟨y, hy, hyz⟩ := hP _ hzL hz
  set c := α.repr ⟨y, hy⟩
  have hyc : y = ∑ b, c b • (α b : B) := by
    have h2 := congrArg Subtype.val (α.sum_repr ⟨y, hy⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    exact h2.symm
  have key := hli (Sum.elim (fun b => -c b) g) (by
    apply Subtype.ext
    rw [coe_presFam_sum]
    simp only [Sum.elim_inl, Sum.elim_inr, ZeroMemClass.coe_zero]
    rw [hyz, hyc, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [mul_smul_comm, neg_smul, neg_add_cancel])
  intro i
  simpa using key (Sum.inr i)

theorem presDet_ne_zero_of_linIndep [IsDomain B] (hs : s ≠ 0)
    (h : LinearIndependent k (fun i => Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i))) :
    presDet s hsL α β he ≠ 0 := by
  rw [presDet_ne_zero_iff, Fintype.linearIndependent_iff]
  rw [Fintype.linearIndependent_iff] at h
  intro G hG
  have hB := congrArg Subtype.val hG
  rw [coe_presFam_sum, ZeroMemClass.coe_zero] at hB
  have hmk := congrArg (Ideal.Quotient.mkₐ k (Ideal.span {s})) hB
  have hs0 : Ideal.Quotient.mkₐ k (Ideal.span {s}) s = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self s
  simp only [map_add, map_sum, map_smul, map_mul, hs0, zero_mul, smul_zero, Finset.sum_const_zero, zero_add,
    map_zero] at hmk
  have hr := h _ hmk
  simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hB
  have hl : ∑ b, G (Sum.inl b) • α b = 0 := by
    apply Subtype.ext
    have : s * ∑ b, G (Sum.inl b) • (α b : B) = 0 := by
      rw [Finset.mul_sum]; simpa only [mul_smul_comm] using hB
    simpa using (mul_eq_zero.mp this).resolve_left hs
  have hl' := (Fintype.linearIndependent_iff.mp α.linearIndependent) _ hl
  rintro (b | i)
  · exact hl' b
  · exact hr i

variable (w : B) (hw : ∀ i, w * e i ∈ L)

theorem det_pres_charpoly [Module.Finite k (B ⧸ Ideal.span {s})] (h : presDet s hsL α β he ≠ 0) (bC : Basis (Fin N) k (B ⧸ Ideal.span {s}))
    (hbC : ∀ i, bC i = Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i)) :
    (fromCols ((β.toMatrix fun b => (⟨s * α b, hsL _ (α b).2⟩ : L)).map C)
      ((β.toMatrix fun i => (⟨e i, he i⟩ : L)).map C * scalar (Fin N) (X : k[X]) -
        (β.toMatrix fun i => (⟨w * e i, hw i⟩ : L)).map C)).det =
      C (presDet s hsL α β he) *
        LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)) := by
  have : FiniteDimensional k L := Module.Finite.of_basis β
  have hli := (presDet_ne_zero_iff s hsL α β he).mp h
  set u := presFam s hsL α he
  let bu : Basis (Fin a ⊕ Fin N) k L :=
    Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (Module.finrank_eq_card_basis β).symm).ge
  have hbu : ⇑bu = u := Basis.coe_mk _ _
  set Aα := β.toMatrix fun b => (⟨s * α b, hsL _ (α b).2⟩ : L)
  set Zm := β.toMatrix fun i => (⟨e i, he i⟩ : L)
  set Wv : Fin N → L := fun i => ⟨w * e i, hw i⟩
  set G := bu.toMatrix Wv
  have hfc : β.toMatrix u = fromCols Aα Zm := by
    ext r (b | i) <;> simp [Basis.toMatrix_apply, u, presFam, Aα, Zm]
  have hW : β.toMatrix Wv = Aα * G.toRows₁ + Zm * G.toRows₂ := by
    rw [← fromCols_mul_fromRows, fromRows_toRows, ← hfc, ← hbu, β.toMatrix_mul_toMatrix]
  -- the matrix of multiplication by `w` on `B ⧸ (s)`
  have hs0 : Ideal.Quotient.mkₐ k (Ideal.span {s}) s = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self s
  have hmat : LinearMap.toMatrix bC bC
      (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)) = G.toRows₂ := by
    ext j i
    rw [LinearMap.toMatrix_apply]
    have hsum := congrArg Subtype.val (bu.sum_repr (Wv i))
    rw [hbu] at hsum
    have hsum' : w * e i = ∑ b, G (Sum.inl b) i • (s * (α b : B)) + ∑ j, G (Sum.inr j) i • e j := by
      rw [← coe_presFam_sum s hsL α he (fun r => G r i)]
      simpa [G, Basis.toMatrix_apply, Wv] using hsum.symm
    have hq : Ideal.Quotient.mkₐ k (Ideal.span {s}) w * bC i = ∑ j, G.toRows₂ j i • bC j := by
      rw [hbC, ← map_mul, hsum']
      simp only [map_add, map_sum, map_smul, map_mul, hs0, zero_mul, smul_zero, Finset.sum_const_zero,
        zero_add, hbC, toRows₂_apply]
    change bC.repr (Ideal.Quotient.mkₐ k (Ideal.span {s}) w * bC i) j = _
    rw [hq, bC.repr_sum_self]
  have hcp : LinearMap.charpoly
      (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)) = G.toRows₂.charpoly := by
    rw [← LinearMap.charpoly_toMatrix _ bC, hmat]
  have hV : Zm.map C * scalar (Fin N) (X : k[X]) - (β.toMatrix Wv).map C =
      Aα.map C * -(G.toRows₁.map C) + Zm.map C * charmatrix G.toRows₂ := by
    rw [hW, Matrix.map_add _ (map_add C), Matrix.map_mul, Matrix.map_mul, charmatrix, RingHom.mapMatrix_apply, Matrix.mul_sub,
      Matrix.mul_neg]
    abel
  rw [hV, det_fromCols_eq _ _ _ _ _ rfl, hcp, Matrix.charpoly, ← fromCols_map, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← hfc, ← Basis.det_apply]
  rfl

end Pres

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Fam =====
section

/-!
# S4-JacLaw, file O6b: the Δ-ratio presentation in families

`c : Fin n → S` (coefficients in a `k`-algebra `S`, e.g. the kernel vector in `S_d`) and `h : Fin n → B`
give at each `k`-point `x` of `S` the section `secAt c h x = Σ_l x(c_l) h_l`. With `h_l L' ⊆ L` the
presentation matrices of `O4b` (`Pres`) become matrices over `S` (`famPres`, `famDet`), polynomial in `c`,
whose values at `x` are `presDet` and the `Δ_{X - w}` determinant at `secAt c h x` (`map_famPres`,
`map_famDet`); with `det_pres_charpoly` this is `C presDet * charpoly` (`map_famDet_eq`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Polynomial Module Matrix

section Fam

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {n : ℕ} (c : Fin n → S) (h : Fin n → B)

/-- The section `Σ_l x(c_l) h_l` at the point `x`. -/
noncomputable def secAt (x : S →ₐ[k] k) : B := ∑ l, x (c l) • h l

variable {L L' : Submodule k B} (hhL : ∀ l, ∀ y ∈ L', h l * y ∈ L)

include hhL in
theorem secAt_mul_mem (x : S →ₐ[k] k) : ∀ y ∈ L', secAt c h x * y ∈ L := by
  intro y hy
  simp only [secAt, Finset.sum_mul, smul_mul_assoc]
  exact Submodule.sum_mem _ fun l _ => L.smul_mem _ (hhL l y hy)

variable {a N : ℕ} (α : Basis (Fin a) k L') (β : Basis (Fin a ⊕ Fin N) k L)
variable {e : Fin N → B} (he : ∀ i, e i ∈ L)

/-- The block `[s α]` with entries in `S`. -/
noncomputable def famBlock : Matrix (Fin a ⊕ Fin N) (Fin a) S :=
  Matrix.of fun r b => ∑ l, c l * algebraMap k S (β.repr ⟨h l * α b, hhL l _ (α b).2⟩ r)

theorem map_famBlock (x : S →ₐ[k] k) :
    (famBlock c h hhL α β).map x =
      β.toMatrix fun b => (⟨secAt c h x * α b, secAt_mul_mem c h hhL x _ (α b).2⟩ : L) := by
  ext r b
  have hsum : (⟨secAt c h x * α b, secAt_mul_mem c h hhL x _ (α b).2⟩ : L) =
      ∑ l, x (c l) • (⟨h l * α b, hhL l _ (α b).2⟩ : L) := by
    apply Subtype.ext
    simp [secAt, Finset.sum_mul, smul_mul_assoc]
  rw [Basis.toMatrix_apply, hsum, map_sum]
  simp only [famBlock, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]

/-- `Δ_1` in the family. -/
noncomputable def famPres : S :=
  (fromCols (famBlock c h hhL α β) ((β.toMatrix fun i => (⟨e i, he i⟩ : L)).map (algebraMap k S))).det

theorem map_famPres (x : S →ₐ[k] k) :
    x (famPres c h hhL α β he) = presDet (secAt c h x) (secAt_mul_mem c h hhL x) α β he := by
  rw [presDet, Basis.det_apply, famPres, AlgHom.map_det]
  congr 1
  ext r (b | i)
  · have := congr_fun (congr_fun (map_famBlock c h hhL α β x) r) b
    simp only [Matrix.map_apply] at this
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, fromCols_apply_inl, this,
      Basis.toMatrix_apply, presFam, Sum.elim_inl]
  · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, fromCols_apply_inr, Basis.toMatrix_apply,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, presFam, Sum.elim_inr]

variable (w : B) (hw : ∀ i, w * e i ∈ L)

/-- `Δ_{X - w}` in the family, a polynomial over `S`. -/
noncomputable def famDet : S[X] :=
  (fromCols ((famBlock c h hhL α β).map C)
    (((β.toMatrix fun i => (⟨e i, he i⟩ : L)).map C * scalar (Fin N) (X : k[X]) -
      (β.toMatrix fun i => (⟨w * e i, hw i⟩ : L)).map C).map (Polynomial.map (algebraMap k S)))).det

theorem map_famDet (x : S →ₐ[k] k) :
    (famDet c h hhL α β he w hw).map x.toRingHom =
      (fromCols ((β.toMatrix fun b => (⟨secAt c h x * α b, secAt_mul_mem c h hhL x _ (α b).2⟩ : L)).map C)
        ((β.toMatrix fun i => (⟨e i, he i⟩ : L)).map C * scalar (Fin N) (X : k[X]) -
          (β.toMatrix fun i => (⟨w * e i, hw i⟩ : L)).map C)).det := by
  rw [famDet, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext r (b | i)
  · have := congr_fun (congr_fun (map_famBlock c h hhL α β x) r) b
    simp only [Matrix.map_apply] at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fromCols_apply_inl, Polynomial.coe_mapRingHom,
      Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, this]
  · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fromCols_apply_inr, Polynomial.coe_mapRingHom,
      Polynomial.map_map]
    have hx : (x : S →+* k).comp (algebraMap k S) = RingHom.id k := by
      ext t; simp
    rw [AlgHom.toRingHom_eq_coe, hx, Polynomial.map_id]

theorem map_famDet_eq (x : S →ₐ[k] k) [Module.Finite k (B ⧸ Ideal.span {secAt c h x})]
    (hP : presDet (secAt c h x) (secAt_mul_mem c h hhL x) α β he ≠ 0)
    (bC : Basis (Fin N) k (B ⧸ Ideal.span {secAt c h x}))
    (hbC : ∀ i, bC i = Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) (e i)) :
    (famDet c h hhL α β he w hw).map x.toRingHom =
      C (x (famPres c h hhL α β he)) * LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {secAt c h x})
        (Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) w)) := by
  rw [map_famDet, map_famPres]
  exact det_pres_charpoly (secAt c h x) (secAt_mul_mem c h hhL x) α β he w hw hP bC hbC

end Fam

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Diag =====
section

/-!
# S4-JacLaw, file O4a: diagonalising a finite commutative algebra by one element

`C` a commutative `k`-algebra of finite dimension `N`, `w : C`, and `N` eigenvectors `v i` of multiplication by `w`
with pairwise distinct eigenvalues `lam i`. Then `v` is a basis (`eigBasis`), every `c : C` acts diagonally
(`mul_eigen : c * v j = eigChar j c • v j`), the `eigChar j : C →ₐ[k] k` are the only `k`-points of `C`
(`exists_eq_eigChar`), they separate elements (`eq_zero_of_eigChar`), and
`charpoly (lmul c) = ∏ j, (X - C (eigChar j c))` (`charpoly_lmul_eq`).
`exists_eigen_of_separable`: over an algebraically closed field a separable `charpoly (lmul w)` gives such data,
indexed by its roots. `prod_divByMonic_image`: exact division of products of linear factors.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open Polynomial Module

section Diag

variable {k : Type*} [Field k] {C : Type*} [CommRing C] [Algebra k C] [FiniteDimensional k C]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {w : C} {lam : ι → k} {v : ι → C} (hlam : Function.Injective lam) (hv : ∀ i, v i ≠ 0)
  (hwv : ∀ i, w * v i = lam i • v i) (hcard : Fintype.card ι = finrank k C)

omit [FiniteDimensional k C] [Fintype ι] [DecidableEq ι] in
include hlam hv hwv in
theorem linearIndependent_eigen : LinearIndependent k v :=
  Module.End.eigenvectors_linearIndependent' (Algebra.lmul k C w) lam hlam v fun i =>
    ⟨Module.End.mem_eigenspace_iff.mpr (by simpa using hwv i), hv i⟩

/-- The eigenvector basis. -/
noncomputable def eigBasis : Basis ι k C :=
  Basis.mk (linearIndependent_eigen hlam hv hwv)
    ((linearIndependent_eigen hlam hv hwv).span_eq_top_of_card_eq_finrank' hcard).ge

omit [DecidableEq ι] in
@[simp] theorem coe_eigBasis : ⇑(eigBasis hlam hv hwv hcard) = v := Basis.coe_mk _ _

theorem repr_v (j : ι) : (eigBasis hlam hv hwv hcard).repr (v j) = Finsupp.single j 1 := by
  have h := (eigBasis hlam hv hwv hcard).repr_self j
  rwa [coe_eigBasis] at h

include hlam hv hwv hcard in
theorem mul_w_eq (y : C) :
    w * y = ∑ i, (lam i * (eigBasis hlam hv hwv hcard).repr y i) • v i := by
  conv_lhs => rw [← (eigBasis hlam hv hwv hcard).sum_repr y]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_eigBasis, mul_smul_comm, hwv i, smul_smul, mul_comm]

include hlam hv hwv hcard in
theorem repr_mul_w (y : C) (i : ι) :
    (eigBasis hlam hv hwv hcard).repr (w * y) i = lam i * (eigBasis hlam hv hwv hcard).repr y i := by
  have h := (eigBasis hlam hv hwv hcard).repr_sum_self (fun i => lam i * (eigBasis hlam hv hwv hcard).repr y i)
  rw [coe_eigBasis, ← mul_w_eq hlam hv hwv hcard] at h
  exact congrFun h i

include hlam hv hwv hcard in
theorem mul_eigen_aux (c : C) (j : ι) :
    c * v j = (eigBasis hlam hv hwv hcard).repr (c * v j) j • v j := by
  set b := eigBasis hlam hv hwv hcard
  have hx : w * (c * v j) = lam j • (c * v j) := by
    rw [mul_left_comm, hwv j, mul_smul_comm]
  have hz : ∀ i, i ≠ j → b.repr (c * v j) i = 0 := by
    intro i hij
    have := repr_mul_w hlam hv hwv hcard (c * v j) i
    rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
    have h2 : (lam i - lam j) * b.repr (c * v j) i = 0 := by rw [sub_mul, ← this, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr fun h => hij (hlam h))
  conv_lhs => rw [← b.sum_repr (c * v j)]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [hz i hij, zero_smul]) (by simp), coe_eigBasis]

/-- The `k`-point of `C` given by the eigenline `k v j`. -/
noncomputable def eigChar (j : ι) : C →ₐ[k] k :=
  AlgHom.ofLinearMap
    ((Finsupp.lapply j).comp (((eigBasis hlam hv hwv hcard).repr : C →ₗ[k] ι →₀ k).comp
      (LinearMap.mulRight k (v j))))
    (by
      change (eigBasis hlam hv hwv hcard).repr (1 * v j) j = 1
      rw [one_mul, repr_v, Finsupp.single_eq_same])
    (by
      intro c c'
      change (eigBasis hlam hv hwv hcard).repr (c * c' * v j) j =
        (eigBasis hlam hv hwv hcard).repr (c * v j) j * (eigBasis hlam hv hwv hcard).repr (c' * v j) j
      set a := (eigBasis hlam hv hwv hcard).repr (c' * v j) j
      have h : c' * v j = a • v j := mul_eigen_aux hlam hv hwv hcard c' j
      rw [mul_assoc, h, mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm])

theorem eigChar_apply (j : ι) (c : C) :
    eigChar hlam hv hwv hcard j c = (eigBasis hlam hv hwv hcard).repr (c * v j) j := rfl

theorem mul_eigen (c : C) (j : ι) : c * v j = eigChar hlam hv hwv hcard j c • v j :=
  mul_eigen_aux hlam hv hwv hcard c j

theorem eigChar_w (j : ι) : eigChar hlam hv hwv hcard j w = lam j := by
  have h := mul_eigen hlam hv hwv hcard w j
  rw [hwv j] at h
  exact (smul_left_injective k (hv j) h).symm

theorem eigChar_injective : Function.Injective (eigChar hlam hv hwv hcard) := by
  intro i j h
  apply hlam
  rw [← eigChar_w hlam hv hwv hcard i, ← eigChar_w hlam hv hwv hcard j, h]

theorem exists_eq_eigChar (φ : C →ₐ[k] k) : ∃ j, φ = eigChar hlam hv hwv hcard j := by
  set b := eigBasis hlam hv hwv hcard
  have h1 : ∑ i, b.repr 1 i * φ (v i) = 1 := by
    have h0 : φ 1 = ∑ i, b.repr 1 i * φ (v i) := by
      conv_lhs => rw [← b.sum_repr 1]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, coe_eigBasis, smul_eq_mul]
    rw [← h0, map_one]
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero : ∑ i, b.repr 1 i * φ (v i) ≠ 0)
  have hφj : φ (v j) ≠ 0 := right_ne_zero_of_mul hj
  refine ⟨j, AlgHom.ext fun c => ?_⟩
  have := congrArg φ (mul_eigen hlam hv hwv hcard c j)
  rw [map_mul, map_smul, smul_eq_mul] at this
  exact mul_right_cancel₀ hφj this

theorem toMatrix_lmul_eq (c : C) :
    LinearMap.toMatrix (eigBasis hlam hv hwv hcard) (eigBasis hlam hv hwv hcard) (Algebra.lmul k C c) =
      Matrix.diagonal fun j => eigChar hlam hv hwv hcard j c := by
  ext i j
  rw [LinearMap.toMatrix_apply, coe_eigBasis]
  change (eigBasis hlam hv hwv hcard).repr (c * v j) i = _
  rw [mul_eigen hlam hv hwv hcard c j, map_smul, repr_v, Finsupp.smul_apply, Matrix.diagonal_apply,
    Finsupp.single_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem charpoly_lmul_eq (c : C) :
    LinearMap.charpoly (Algebra.lmul k C c) = ∏ j, (X - Polynomial.C (eigChar hlam hv hwv hcard j c)) := by
  rw [← LinearMap.charpoly_toMatrix (Algebra.lmul k C c) (eigBasis hlam hv hwv hcard), toMatrix_lmul_eq,
    Matrix.charpoly_diagonal]

end Diag

section Sep

variable {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] {C : Type*} [CommRing C] [Algebra k C] [FiniteDimensional k C]

/-- Eigen-data from a separable characteristic polynomial, indexed by its roots. -/
theorem exists_eigen_of_separable (w : C) (hsep : (LinearMap.charpoly (Algebra.lmul k C w)).Separable) :
    ∃ v : (LinearMap.charpoly (Algebra.lmul k C w)).roots.toFinset → C,
      (∀ μ, v μ ≠ 0) ∧ (∀ μ, w * v μ = (μ : k) • v μ) ∧
      Fintype.card (LinearMap.charpoly (Algebra.lmul k C w)).roots.toFinset = finrank k C := by
  set p := LinearMap.charpoly (Algebra.lmul k C w)
  have hex : ∀ μ : p.roots.toFinset, ∃ x : C, x ≠ 0 ∧ w * x = (μ : k) • x := by
    intro μ
    have hr : p.IsRoot μ := by
      have := μ.2
      rw [Multiset.mem_toFinset, mem_roots (LinearMap.charpoly_monic _).ne_zero] at this
      exact this
    obtain ⟨x, hx⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hr).exists_hasEigenvector
    exact ⟨x, hx.2, by simpa using Module.End.mem_eigenspace_iff.mp hx.1⟩
  choose v hv0 hv using hex
  refine ⟨v, hv0, hv, ?_⟩
  rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    LinearMap.charpoly_natDegree]

end Sep

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_MonPts =====
section

/-!
# S4-JacLaw, file O6c: monic generic polynomial, the zero set of a section, exact division

* `monPoly w ∈ Sym^d(B)[X]`: the monic polynomial `∏_l (X - w_l)` with symmetric coefficients
  (`map_symPt_monPoly`: its value at the point `a_1 + ... + a_d` is `∏_l (X - a_l(w))`).
* `exists_zeroSet`: for `s ∈ B` with `B/(s)` finite-dimensional over the algebraically closed `k` and
  one `w0` whose multiplication has separable characteristic polynomial, the `k`-points of `B` vanishing
  at `s` form a finset `Z` with `#Z = dim B/(s)` and `charpoly (w mod s) = ∏_{φ ∈ Z} (X - φ(w))`.
* `prod_divByMonic_sdiff`, `enumF` / `prod_enumF`, `prod_eq_sign_coeff_zero`: the exact division
  `∏_Z /ₘ ∏_A = ∏_{Z \ A}`, an enumeration of a finset, and `∏ u = (-1)^# · coeff 0 (∏ (X - u))`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym Polynomial Module

section MonPoly

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

/-- `∏_l (X - w_l)` over `X^g(B)`. -/
noncomputable def monE (w : B) : (XPow k B g)[X] := ∏ l, (X - C (inc l w))

theorem map_permHom_monE (σ : Equiv.Perm (Fin g)) (w : B) :
    (monE (k := k) (g := g) w).map (permHom σ).toRingHom = monE w := by
  have h : ∀ l : Fin g, (permHom σ) (inc (k := k) l w) = inc (σ l) w := fun l => by
    rw [← AlgHom.comp_apply, permHom_comp_inc]
  simp only [monE, Polynomial.map_prod, Polynomial.map_sub, map_C, map_X,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h]
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

theorem monE_coeff_mem (w : B) (j : ℕ) : (monE (k := k) (g := g) w).coeff j ∈ SymRing k B g := by
  rw [mem_symRing]
  intro σ
  rw [perm_smul_def]
  have := congrArg (fun p => p.coeff j) (map_permHom_monE (k := k) σ w)
  simp only [coeff_map] at this
  exact this

theorem monE_mem_lifts (w : B) : monE (k := k) (g := g) w ∈ lifts (SymRing k B g).val.toRingHom := by
  rw [lifts_iff_coeff_lifts]
  intro j
  exact ⟨⟨_, monE_coeff_mem w j⟩, rfl⟩

/-- `∏_l (X - w_l)` with coefficients in `Sym^g(B)`. -/
noncomputable def monPoly (w : B) : (SymRing k B g)[X] :=
  Classical.choose ((mem_lifts _).mp (monE_mem_lifts (k := k) (g := g) w))

theorem map_monPoly (w : B) : (monPoly (k := k) (g := g) w).map (SymRing k B g).val.toRingHom = monE w :=
  Classical.choose_spec ((mem_lifts _).mp (monE_mem_lifts (k := k) (g := g) w))

theorem monic_monE (w : B) : (monE (k := k) (g := g) w).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem monic_monPoly (w : B) : (monPoly (k := k) (g := g) w).Monic := by
  have hinj : Function.Injective (SymRing k B g).val.toRingHom := fun _ _ h => Subtype.ext h
  rw [hinj.monic_map_iff, map_monPoly]
  exact monic_monE w

/-- The monic generic polynomial at the point `a_1 + ... + a_g`. -/
theorem map_symPt_monPoly (a : Fin g → (B →ₐ[k] k)) (w : B) :
    (monPoly (k := k) (g := g) w).map (symPt a).toRingHom = ∏ l, (X - C (a l w)) := by
  have h : (symPt a).toRingHom = (ptOf a).toRingHom.comp (SymRing k B g).val.toRingHom := rfl
  rw [h, ← Polynomial.map_map, map_monPoly, monE, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Polynomial.map_sub, map_C, map_X]
  congr 2
  exact AlgHom.congr_fun (ptOf_inc a l) w

end MonPoly

section Zero

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B]

/-- **Zero set of a section.** If `B/(s)` is finite-dimensional and some `w0` has separable characteristic
polynomial on it, the `k`-points of `B` killing `s` are `dim B/(s)` many and diagonalise every `w`. -/
theorem exists_zeroSet (s : B) [FiniteDimensional k (B ⧸ Ideal.span {s})] (w0 : B)
    (hsep : (LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s})
      (Ideal.Quotient.mkₐ k (Ideal.span {s}) w0))).Separable) :
    ∃ Z : Finset (B →ₐ[k] k), (∀ φ, φ ∈ Z ↔ φ s = 0) ∧ Z.card = finrank k (B ⧸ Ideal.span {s}) ∧
      ∀ w, LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)) =
        ∏ φ ∈ Z, (X - C (φ w)) := by
  classical
  set I := Ideal.span {s}
  obtain ⟨v, hv0, hv, hcard⟩ := exists_eigen_of_separable (Ideal.Quotient.mkₐ k I w0) hsep
  have hlam : Function.Injective (fun μ : (LinearMap.charpoly (Algebra.lmul k (B ⧸ I)
      (Ideal.Quotient.mkₐ k I w0))).roots.toFinset => (μ : k)) := Subtype.val_injective
  set ψ := eigChar hlam hv0 hv hcard
  have hinj : Function.Injective fun j => (ψ j).comp (Ideal.Quotient.mkₐ k I) := by
    intro i j hij
    exact eigChar_injective hlam hv0 hv hcard (Ideal.Quotient.algHom_ext k hij)
  refine ⟨Finset.univ.image fun j => (ψ j).comp (Ideal.Quotient.mkₐ k I), fun φ => ?_, ?_, fun w => ?_⟩
  · constructor
    · intro hφ
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hφ
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self s), map_zero]
    · intro hφ
      have hI : ∀ a : B, a ∈ I → φ a = 0 := by
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, hφ, mul_zero]
      obtain ⟨j, hj⟩ := exists_eq_eigChar hlam hv0 hv hcard (Ideal.Quotient.liftₐ I φ hI)
      refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
      change (eigChar hlam hv0 hv hcard j).comp _ = φ
      rw [← hj, Ideal.Quotient.liftₐ_comp]
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
  · rw [charpoly_lmul_eq hlam hv0 hv hcard, Finset.prod_image fun x _ y _ h => hinj h]
    rfl

end Zero

section Div

/-- Exact division `∏_{φ ∈ Z} (X - u φ) /ₘ ∏_i (X - u (a i)) = ∏_{φ ∈ Z \ a} (X - u φ)`. -/
theorem prod_divByMonic_sdiff {R ι : Type*} [CommRing R] [DecidableEq ι] {d : ℕ} (Z : Finset ι)
    (a : Fin d → ι) (ha : Function.Injective a) (haZ : ∀ i, a i ∈ Z) (u : ι → R) :
    (∏ φ ∈ Z, (X - C (u φ))) /ₘ (∏ i, (X - C (u (a i)))) =
      ∏ φ ∈ Z \ Finset.univ.image a, (X - C (u φ)) := by
  have hsub : Finset.univ.image a ⊆ Z := by
    intro φ hφ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hφ
    exact haZ i
  have hprod : ∏ i, (X - C (u (a i))) = ∏ φ ∈ Finset.univ.image a, (X - C (u φ)) := by
    rw [Finset.prod_image fun x _ y _ h => ha h]
  rw [hprod, ← Finset.prod_sdiff hsub, mul_comm (∏ φ ∈ Z \ Finset.univ.image a, (X - C (u φ)))]
  exact mul_divByMonic_cancel_left _ (monic_prod_of_monic _ _ fun φ _ => monic_X_sub_C (u φ))

theorem prod_eq_sign_coeff_zero {R ι : Type*} [CommRing R] (T : Finset ι) (u : ι → R) :
    ∏ φ ∈ T, u φ = (-1) ^ T.card * (∏ φ ∈ T, (X - C (u φ))).coeff 0 := by
  rw [coeff_zero_eq_eval_zero, eval_prod]
  simp only [eval_sub, eval_X, eval_C, zero_sub]
  rw [Finset.prod_neg, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- An enumeration of a finset of known cardinality. -/
noncomputable def enumF {α : Type*} (T : Finset α) {n : ℕ} (h : T.card = n) : Fin n → α :=
  fun l => ((Fintype.equivFinOfCardEq ((Fintype.card_coe T).trans h)).symm l : α)

theorem enumF_mem {α : Type*} (T : Finset α) {n : ℕ} (h : T.card = n) (l : Fin n) : enumF T h l ∈ T :=
  ((Fintype.equivFinOfCardEq ((Fintype.card_coe T).trans h)).symm l).2

theorem enumF_injective {α : Type*} (T : Finset α) {n : ℕ} (h : T.card = n) : Function.Injective (enumF T h) :=
  fun _ _ hl => (Fintype.equivFinOfCardEq ((Fintype.card_coe T).trans h)).symm.injective (Subtype.ext hl)

theorem prod_enumF {α M : Type*} [CommMonoid M] (T : Finset α) {n : ℕ} (h : T.card = n) (f : α → M) :
    ∏ l, f (enumF T h l) = ∏ φ ∈ T, f φ := by
  rw [← Finset.prod_coe_sort T f]
  exact Fintype.prod_equiv (Fintype.equivFinOfCardEq ((Fintype.card_coe T).trans h)).symm _ _ fun _ => rfl

end Div

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Good =====
section

/-!
# S4-JacLaw, file O6d-1: choice data for `ν` and the good open `D(good)` of `Sym^d`

`NuData K F d` fixes, for `N = d + g`: an effective divisor `Hn` at infinity of degree `N`, a basis `h` of
`V_N = L(Hn) ∩ B`, test elements `χ`, an index `l0`, functionals `lam P'` killing `L(Hn - P')`, a divisor `H` at infinity
with elements `e_1..e_N ∈ L(H)`, and `w0 ∈ B`. The element `good ∈ Sym^d(B)` is the product of the
kernel coordinate `l0`, the `lam` values, `Δ_1` and the resultant of `Δ_{X - w0}` with its derivative.
At a point `y` of `Sym^d` with `y good ≠ 0`, the section `s = sec y` (the kernel line of `L(Hn - A)`)
has exact pole divisor `Hn` and `N` simple zeros, among them the `d` distinct points of `A`
(`zero_spec`, `map_det`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

theorem finiteType_away {k : Type*} [Field k] {S : Type*} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (r : S) : Algebra.FiniteType k (Localization.Away r) := by
  have : Algebra.FinitePresentation S (Localization.Away r) := IsLocalization.Away.finitePresentation r
  exact Algebra.FiniteType.trans (S := S) inferInstance Algebra.FiniteType.of_finitePresentation

/-- The zero set of `s` as a finset (empty if it is infinite). -/
noncomputable def zeroFin {k B : Type*} [Field k] [CommRing B] [Algebra k B] (s : B) : Finset (B →ₐ[k] k) := by
  classical
  exact if hf : {φ : B →ₐ[k] k | φ s = 0}.Finite then hf.toFinset else ∅

theorem zeroFin_eq {k B : Type*} [Field k] [CommRing B] [Algebra k B] {s : B} {Z : Finset (B →ₐ[k] k)}
    (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0) : zeroFin (k := k) s = Z := by
  have hf : {φ : B →ₐ[k] k | φ s = 0}.Finite := Z.finite_toSet.subset fun φ hφ => (hZ φ).2 hφ
  rw [zeroFin, dif_pos hf]
  ext φ
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hZ]

section Abs

/-! Abstract wrappers: over an abstract `B` the `Module.Free` instances on subspaces and quotients are found at once
(over `Places.Rfin K F` instance search fails or times out), so finiteness enters as an explicit argument. -/

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-- A basis of a finite-dimensional subspace indexed by `Fin n`, `n = finrank`. -/
noncomputable def finBasisSub (L : Submodule k B) (hL : FiniteDimensional k L) {n : ℕ} (hn : finrank k L = n) :
    Basis (Fin n) k L :=
  Module.finBasisOfFinrankEq k L hn

/-- **Zero set from a resultant.** If `P w = u w * charpoly(w on B/(s))` for all `w` and `P w0` is coprime to its
derivative (resultant `≠ 0`), then `s` has exactly `N = dim B/(s)` zeros and they diagonalise every `w`. -/
theorem exists_zeroSet_of_res [IsAlgClosed k] (s : B) (hfin : Module.Finite k (B ⧸ Ideal.span {s})) {N : ℕ}
    (hN : finrank k (B ⧸ Ideal.span {s}) = N) (P : B → k[X]) (u : B → k)
    (hP : ∀ w, P w = C (u w) * LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s})
      (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)))
    (w0 : B) (hres : resultant (P w0) (derivative (P w0)) N N ≠ 0) :
    ∃ Z : Finset (B →ₐ[k] k), (∀ φ, φ ∈ Z ↔ φ s = 0) ∧ Z.card = N ∧
      ∀ w, P w = C (u w) * ∏ φ ∈ Z, (X - C (φ w)) := by
  set χ0 := LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w0))
    with hχ0
  have hsep : χ0.Separable := by
    have hdeg : χ0.natDegree = N := by rw [hχ0, LinearMap.charpoly_natDegree, hN]
    have hmon : χ0.Monic := LinearMap.charpoly_monic _
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [eq_one_of_monic_natDegree_zero hmon (hdeg.trans h0)]; exact separable_one
    have hp : P w0 = C (u w0) * χ0 := hP w0
    have hpdeg : (P w0).natDegree ≤ N := by rw [hp]; exact (natDegree_C_mul_le _ _).trans hdeg.le
    obtain ⟨Q1, Q2, -, -, hPQ⟩ := exists_mul_add_mul_eq_C_resultant (m := N) (n := N) (P w0) (derivative (P w0))
      hpdeg ((natDegree_derivative_le (P w0)).trans (by omega)) (Or.inl hpos.ne')
    set r := resultant (P w0) (derivative (P w0)) N N
    have hcop : IsCoprime (P w0) (derivative (P w0)) := by
      refine ⟨C r⁻¹ * Q1, C r⁻¹ * Q2, ?_⟩
      calc C r⁻¹ * Q1 * P w0 + C r⁻¹ * Q2 * derivative (P w0) =
            C r⁻¹ * (P w0 * Q1 + derivative (P w0) * Q2) := by ring
        _ = 1 := by rw [hPQ, ← C_mul, inv_mul_cancel₀ hres, C_1]
    have hs : (P w0).Separable := hcop
    rw [hp] at hs
    exact hs.of_mul_right
  obtain ⟨Z, hZ, hcard, hchar⟩ := exists_zeroSet s w0 hsep
  exact ⟨Z, hZ, hcard.trans hN, fun w => by rw [hP w, hchar w]⟩

variable {S : Type*} [CommRing S] [Algebra k S]
variable {n : ℕ} (c : Fin n → S) (h : Fin n → B)
variable {L L' : Submodule k B} (hhL : ∀ l, ∀ y ∈ L', h l * y ∈ L)
variable {a N : ℕ} (α : Basis (Fin a) k L') (β : Basis (Fin a ⊕ Fin N) k L)
variable {e : Fin N → B} (he : ∀ i, e i ∈ L) (w : B) (hw : ∀ i, w * e i ∈ L)

/-- `map_famDet_eq` with the basis of the quotient built from linear independence. -/
theorem map_famDet_eq_li (x : S →ₐ[k] k) (hfin : Module.Finite k (B ⧸ Ideal.span {secAt c h x}))
    (hP : x (famPres c h hhL α β he) ≠ 0)
    (hli : LinearIndependent k fun i => Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) (e i))
    (hcard : finrank k (B ⧸ Ideal.span {secAt c h x}) = N) :
    (famDet c h hhL α β he w hw).map x.toRingHom =
      C (x (famPres c h hhL α β he)) * LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {secAt c h x})
        (Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) w)) := by
  rw [map_famPres] at hP
  exact map_famDet_eq c h hhL α β he w hw x hP
    (basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [Fintype.card_fin, hcard]))
    fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']

end Abs

section Good

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

instance finiteType_Rfin : Algebra.FiniteType K (Places.Rfin K F) :=
  Algebra.FiniteType.trans (S := K[X]) inferInstance inferInstance

instance finiteDimensional_Linf (H : Places.Divisor K F) : FiniteDimensional K (Linf K F H) := by
  have := finiteDimensional_LFK (K := K) (F := F) H
  exact Module.Finite.of_injective (((incB K F).toLinearMap.domRestrict (Linf K F H)).codRestrict (LFK K F H)
    fun b => b.2) fun a b hab => by
      have h' := congrArg Subtype.val hab
      exact Subtype.ext (incB_injective h')

variable (K F) in
/-- The (finitely many) infinite places. -/
noncomputable def infPl : Finset (HeightOneSpectrum (Places.Rinf K F)) := Set.finite_univ.toFinset

theorem mem_infPl (P : HeightOneSpectrum (Places.Rinf K F)) : P ∈ infPl K F := by
  simp [infPl]

variable [IsAlgClosed K]

variable (K F) in
/-- Choice data for the negation map `ν : Sym^d ⇢ Sym^g` (`N = d + g`). -/
structure NuData (d : ℕ) where
  Hn : Places.Divisor K F
  Hn_inf : IsInf Hn
  Hn_deg : Places.Divisor.deg Hn = ((d + genusFK K F : ℕ) : ℤ)
  h : Fin (d + 1) → Places.Rfin K F
  h_mem : ∀ l, h l ∈ Linf K F Hn
  h_li : LinearIndependent K h
  χ : Fin d → Places.Rfin K F
  l0 : Fin (d + 1)
  lam : HeightOneSpectrum (Places.Rinf K F) → (Fin (d + 1) → K) →ₗ[K] K
  lam_spec : ∀ P' (y : Fin (d + 1) → K),
    ∑ l, y l • h l ∈ Linf K F (Hn - ptInf P') → lam P' y = 0
  H : Places.Divisor K F
  H_inf : IsInf H
  H_deg : 2 * (genusFK K F : ℤ) - 1 ≤ Places.Divisor.deg (H - Hn)
  e : Fin (d + genusFK K F) → Places.Rfin K F
  e_mem : ∀ i, e i ∈ Linf K F H
  w0 : Places.Rfin K F

namespace NuData

variable {d : ℕ} (D : NuData K F d)

/-- `H_w = H + (w)_∞`. -/
noncomputable def Hw (w : Places.Rfin K F) : Places.Divisor K F := D.H + poleDiv (K := K) (incB K F w)

/-- `L_w = L(H_w) ∩ B`. -/
noncomputable abbrev Lw (w : Places.Rfin K F) : Submodule K (Places.Rfin K F) := Linf K F (D.Hw w)

/-- `L'_w = L(H_w - Hn) ∩ B`. -/
noncomputable abbrev Lp (w : Places.Rfin K F) : Submodule K (Places.Rfin K F) :=
  Linf K F (D.Hw w - D.Hn)

theorem isInf_Hw (w : Places.Rfin K F) : IsInf (D.Hw w) := D.H_inf.add (isInf_poleDiv w)

theorem isInf_Hw' (w : Places.Rfin K F) : IsInf (D.Hw w - D.Hn) :=
  (D.isInf_Hw w).sub D.Hn_inf

theorem deg_Hw' (w : Places.Rfin K F) :
    2 * (genusFK K F : ℤ) - 1 ≤ Places.Divisor.deg (D.Hw w - D.Hn) := by
  have h1 : D.Hw w - D.Hn =
      (D.H - D.Hn) + poleDiv (K := K) (incB K F w) := by
    rw [Hw]; abel
  rw [h1, PlacesK.Divisor.deg_add]
  linarith [D.H_deg, deg_poleDiv_nonneg (K := K) (incB K F w)]

theorem finrank_Lw (w : Places.Rfin K F) : finrank K (D.Lw w) = finrank K (D.Lp w) + (d + genusFK K F) := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have h1 := finrank_Linf_eq hk (D.isInf_Hw' w) (D.deg_Hw' w)
  have hdeg : Places.Divisor.deg (D.Hw w) =
      Places.Divisor.deg (D.Hw w - D.Hn) + ((d + genusFK K F : ℕ) : ℤ) := by
    rw [PlacesK.Divisor.deg_sub, D.Hn_deg]; ring
  have h2 := finrank_Linf_eq hk (D.isInf_Hw w) (by rw [hdeg]; linarith [D.deg_Hw' w])
  rw [hdeg] at h2
  zify
  push_cast at h1 h2 ⊢
  linarith

/-- A basis of `L'_w`. -/
noncomputable def α (w : Places.Rfin K F) : Basis (Fin (finrank K (D.Lp w))) K (D.Lp w) :=
  finBasisSub (D.Lp w) (finiteDimensional_Linf _) rfl

/-- A basis of `L_w` indexed by `Fin a ⊕ Fin N`. -/
noncomputable def β (w : Places.Rfin K F) : Basis (Fin (finrank K (D.Lp w)) ⊕ Fin (d + genusFK K F)) K (D.Lw w) :=
  (finBasisSub (D.Lw w) (finiteDimensional_Linf _) (D.finrank_Lw w)).reindex finSumFinEquiv.symm

theorem hhL (w : Places.Rfin K F) : ∀ l, ∀ y ∈ D.Lp w, D.h l * y ∈ D.Lw w := fun l y hy => by
  have := mul_mem_Linf (D.h_mem l) hy
  have e : D.Hn + (D.Hw w - D.Hn) = D.Hw w := by abel
  rwa [e] at this

theorem he (w : Places.Rfin K F) : ∀ i, D.e i ∈ D.Lw w := fun i =>
  Linf_mono (le_add_of_nonneg_right le_sup_right) (D.e_mem i)

theorem hw (w : Places.Rfin K F) : ∀ i, w * D.e i ∈ D.Lw w := fun i => by
  have := mul_mem_Linf (mem_Linf_poleDiv w) (D.e_mem i)
  rwa [add_comm] at this

/-- `Δ_1` for `L_w`, an element of `Sym^d(B)`. -/
noncomputable def pres (w : Places.Rfin K F) : SymRing K (Places.Rfin K F) d :=
  famPres (kerVec K D.χ D.h) D.h (D.hhL w) (D.α w) (D.β w) (D.he w)

/-- `Δ_{X - w}`, a polynomial over `Sym^d(B)`. -/
noncomputable def det (w : Places.Rfin K F) : (SymRing K (Places.Rfin K F) d)[X] :=
  famDet (kerVec K D.χ D.h) D.h (D.hhL w) (D.α w) (D.β w) (D.he w) w (D.hw w)

/-- The functional `lam P'` applied to the kernel vector. -/
noncomputable def lamS (P' : HeightOneSpectrum (Places.Rinf K F)) : SymRing K (Places.Rfin K F) d :=
  ∑ l, D.lam P' (fun j => if l = j then 1 else 0) • kerVec K D.χ D.h l

/-- The good element: `D(good)` is the domain of `ν` for this choice. -/
noncomputable def good : SymRing K (Places.Rfin K F) d :=
  kerVec K D.χ D.h D.l0 * (∏ P' ∈ infPl K F, D.lamS P') * D.pres D.w0 *
    resultant (D.det D.w0) (derivative (D.det D.w0)) (d + genusFK K F) (d + genusFK K F)

/-- The section `s = Σ_l y(c_l) h_l` at the point `y`. -/
noncomputable def sec (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) : Places.Rfin K F :=
  secAt (kerVec K D.χ D.h) D.h y

theorem sec_symPt (a : Fin d → (Places.Rfin K F →ₐ[K] K)) : D.sec (symPt a) = sPt a D.χ D.h := rfl

theorem sec_eq (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) : D.sec y = sPt (liftTuple y) D.χ D.h := by
  have := D.sec_symPt (liftTuple y)
  rwa [symPt_liftTuple] at this

theorem sec_mem (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) :
    D.sec y ∈ Linf K F (D.Hn) :=
  Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (D.h_mem l)

theorem lamS_apply (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) (P' : HeightOneSpectrum (Places.Rinf K F)) :
    y (D.lamS P') = D.lam P' (fun l => y (kerVec K D.χ D.h l)) := by
  rw [lamS, LinearMap.pi_apply_eq_sum_univ (D.lam P')]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem apply_sec (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) (i : Fin d) : liftTuple y i (D.sec y) = 0 := by
  rw [sec_eq]; exact apply_sPt _ _ _ i

variable {D} {y : SymRing K (Places.Rfin K F) d →ₐ[K] K}

theorem good_factors (hy : y D.good ≠ 0) : y (kerVec K D.χ D.h D.l0) ≠ 0 ∧ (∀ P', y (D.lamS P') ≠ 0) ∧
    y (D.pres D.w0) ≠ 0 ∧
    y (resultant (D.det D.w0) (derivative (D.det D.w0)) (d + genusFK K F) (d + genusFK K F)) ≠ 0 := by
  simp only [good, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hy
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hy
  exact ⟨h1, fun P' => h2 P' (mem_infPl P'), h3, h4⟩

theorem kerVec_ne (hy : y D.good ≠ 0) : symPt (liftTuple y) (kerVec K D.χ D.h D.l0) ≠ 0 := by
  rw [symPt_liftTuple]; exact (good_factors hy).1

theorem sec_ne_zero (hy : y D.good ≠ 0) : D.sec y ≠ 0 := by
  rw [sec_eq]; exact sPt_ne_zero D.h_li (kerVec_ne hy)

theorem injective_lift (hy : y D.good ≠ 0) : Function.Injective (liftTuple y) := injective_of_kerVec (kerVec_ne hy)

theorem sec_not_mem (hy : y D.good ≠ 0) (P' : HeightOneSpectrum (Places.Rinf K F)) :
    D.sec y ∉ Linf K F (D.Hn - ptInf P') := fun hm =>
  (good_factors hy).2.1 P' (by rw [lamS_apply]; exact D.lam_spec P' _ hm)

theorem exactPole (hy : y D.good ≠ 0) : ExactPoleH (D.sec y) D.Hn :=
  exactPoleH_of_not_mem (sec_ne_zero hy) (D.sec_mem y) (sec_not_mem hy)

theorem finrank_quot (hy : y D.good ≠ 0) :
    finrank K (Places.Rfin K F ⧸ Ideal.span {D.sec y}) = d + genusFK K F := by
  have h := finrank_quot_of_exactPoleH (sec_ne_zero hy) D.Hn_inf (exactPole hy)
  rw [D.Hn_deg] at h
  exact_mod_cast h

theorem finite_quot (hy : y D.good ≠ 0) : Module.Finite K (Places.Rfin K F ⧸ Ideal.span {D.sec y}) :=
  PlacesK.FDQ.finite _ (sec_ne_zero hy)

theorem hP (hy : y D.good ≠ 0) (w : Places.Rfin K F) :
    ∀ z ∈ D.Lw w, z ∈ Ideal.span {D.sec y} → ∃ y' ∈ D.Lp w, z = D.sec y * y' := by
  intro z hz hzs
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hzs
  refine ⟨t, mem_Linf_sub_of_mulH (sec_ne_zero hy) (exactPole hy) D.Hn_inf (D.isInf_Hw w) ?_, mul_comm _ _⟩
  rwa [mul_comm] at hz

theorem linIndep (hy : y D.good ≠ 0) :
    LinearIndependent K (fun i => Ideal.Quotient.mkₐ K (Ideal.span {D.sec y}) (D.e i)) := by
  have h3 := (good_factors hy).2.2.1
  rw [pres, map_famPres] at h3
  exact linIndep_mk_of_presDet (D.sec y) (secAt_mul_mem _ _ (D.hhL D.w0) y) (D.α D.w0) (D.β D.w0) (D.he D.w0)
    (hP hy D.w0) h3

theorem pres_ne_zero (hy : y D.good ≠ 0) (w : Places.Rfin K F) : y (D.pres w) ≠ 0 := by
  rw [pres, map_famPres]
  exact presDet_ne_zero_of_linIndep (D.sec y) _ (D.α w) (D.β w) (D.he w) (sec_ne_zero hy) (linIndep hy)

theorem res_ne (hy : y D.good ≠ 0) :
    resultant ((D.det D.w0).map y.toRingHom) (derivative ((D.det D.w0).map y.toRingHom)) (d + genusFK K F)
      (d + genusFK K F) ≠ 0 := by
  rw [derivative_map, resultant_map_map]
  exact (good_factors hy).2.2.2

/-- **The zero set at a good point**: `N` simple zeros of `s`, and `Δ_{X - w} = Δ_1 · ∏_{P ∈ Z(s)} (X - w(P))`. -/
theorem zero_spec (hy : y D.good ≠ 0) :
    (∀ φ : Places.Rfin K F →ₐ[K] K, φ ∈ zeroFin (D.sec y) ↔ φ (D.sec y) = 0) ∧
      (zeroFin (k := K) (D.sec y)).card = d + genusFK K F ∧
      ∀ w, (D.det w).map y.toRingHom = C (y (D.pres w)) * ∏ φ ∈ zeroFin (k := K) (D.sec y), (X - C (φ w)) := by
  obtain ⟨Z, hZ, hcard, hdet⟩ := exists_zeroSet_of_res (D.sec y) (finite_quot hy) (finrank_quot hy)
    (fun w => (D.det w).map y.toRingHom) (fun w => y (D.pres w))
    (fun w => map_famDet_eq_li (kerVec K D.χ D.h) D.h (D.hhL w) (D.α w) (D.β w) (D.he w) w (D.hw w) y
      (finite_quot hy) (pres_ne_zero hy w) (linIndep hy) (finrank_quot hy)) D.w0 (res_ne hy)
  rw [zeroFin_eq hZ]
  exact ⟨hZ, hcard, hdet⟩

theorem map_det (hy : y D.good ≠ 0) (w : Places.Rfin K F) :
    (D.det w).map y.toRingHom = C (y (D.pres w)) * ∏ φ ∈ zeroFin (k := K) (D.sec y), (X - C (φ w)) :=
  (zero_spec hy).2.2 w

theorem lift_mem_zeroFin (hy : y D.good ≠ 0) (i : Fin d) : liftTuple y i ∈ zeroFin (D.sec y) :=
  ((zero_spec hy).1 _).2 (D.apply_sec y i)

end NuData

end Good

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Nu =====
section

/-!
# S4-JacLaw, file O6d-2: the negation map `ν : D(good) → Sym^g`

For choice data `D : NuData K F d` (`N = d + g`), `D.Rg = Sym^d(B)[1/good]` is the coordinate ring of the basic
open `D(good)`. At a point `x` of it with image `y = yOf x` in `Sym^d`, `A = liftTuple y` are `d` distinct
points, `s = sec y` spans `L(N P∞ - A)` and has `N` simple zeros `zeroFin s ⊇ A`; `ν(A) = Z(s) - A` is the
finset `nuSet x` of `g` points. The norms `N(w)(ν(A)) = ∏_{P ∈ ν(A)} w(P)` are the regular functions
`nrm w = (-1)^g coeff_0 ((Δ_1⁻¹ Δ_{X-w}) /ₘ ∏_{i}(X - w(a_i)))` on `D(good)` (`apply_nrm`), so the morphism
criterion (`liftPts`) gives `nuMap : Sym^g(B) →ₐ D.Rg` with points `nuPt x = ν(A)` (`comp_nuMap`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

/-- Value at a point of `(-1)^#T coeff_0 ((u⁻¹ P) /ₘ M)` when `P = u ∏_Z (X - v)` and `M = ∏_a (X - v)` there. -/
theorem apply_divByMonic_coeff {k R ι : Type*} [Field k] [CommRing R] [Algebra k R] [DecidableEq ι]
    (x : R →ₐ[k] k) (u : Rˣ) (P M : R[X]) (hM : M.Monic) (Z : Finset ι) {n : ℕ} (a : Fin n → ι)
    (ha : Function.Injective a) (haZ : ∀ i, a i ∈ Z) (v : ι → k)
    (hP : P.map x.toRingHom = C (x u) * ∏ φ ∈ Z, (X - C (v φ)))
    (hMx : M.map x.toRingHom = ∏ i, (X - C (v (a i)))) :
    x ((-1) ^ (Z \ Finset.univ.image a).card * ((C (↑u⁻¹ : R) * P) /ₘ M).coeff 0) =
      ∏ φ ∈ Z \ Finset.univ.image a, v φ := by
  have h1 : x.toRingHom ↑u⁻¹ * x u = 1 := by
    change x ↑u⁻¹ * x u = 1
    rw [← map_mul, Units.inv_mul, map_one]
  have hP' : (C (↑u⁻¹ : R) * P).map x.toRingHom = ∏ φ ∈ Z, (X - C (v φ)) := by
    rw [Polynomial.map_mul, Polynomial.map_C, hP, ← mul_assoc, ← C_mul, h1, C_1, one_mul]
  have hc : x (((C (↑u⁻¹ : R) * P) /ₘ M).coeff 0) =
      (((C (↑u⁻¹ : R) * P) /ₘ M).map x.toRingHom).coeff 0 := (Polynomial.coeff_map _ _).symm
  rw [map_mul, map_pow, map_neg, map_one, hc, Polynomial.map_divByMonic _ hM, hP', hMx,
    prod_divByMonic_sdiff Z a ha haZ v]
  exact (prod_eq_sign_coeff_zero _ v).symm

section Nu

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

variable {d : ℕ} (D : NuData K F d)

/-- The coordinate ring of the good open `D(good) ⊂ Sym^d`. -/
abbrev Rg : Type _ := Localization.Away D.good

instance (priority := high) finiteType_Rg : Algebra.FiniteType K D.Rg := finiteType_away D.good

/-- The point of `Sym^d` below a point of `D(good)`. -/
noncomputable def yOf (x : D.Rg →ₐ[K] K) : SymRing K (Places.Rfin K F) d →ₐ[K] K :=
  x.comp (IsScalarTower.toAlgHom K _ D.Rg)

theorem yOf_apply (x : D.Rg →ₐ[K] K) (s : SymRing K (Places.Rfin K F) d) :
    D.yOf x s = x (algebraMap _ D.Rg s) := rfl

theorem yOf_good (x : D.Rg →ₐ[K] K) : D.yOf x D.good ≠ 0 := by
  rw [yOf_apply]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := D.Rg) D.good).map x).ne_zero

theorem isUnit_pres (w : Places.Rfin K F) : IsUnit (algebraMap _ D.Rg (D.pres w)) :=
  isUnit_of_forall_ne_zero (k := K) _ fun x => pres_ne_zero (D.yOf_good x) w

/-- The regular function `N(w) ∘ ν` on `D(good)`. -/
noncomputable def nrm (w : Places.Rfin K F) : D.Rg :=
  (-1) ^ genusFK K F * ((C (↑(D.isUnit_pres w).unit⁻¹ : D.Rg) * (D.det w).map (algebraMap _ D.Rg)) /ₘ
    (monPoly (k := K) (g := d) w).map (algebraMap _ D.Rg)).coeff 0

open Classical in
/-- `ν(A) = Z(s) - A` at the point `x` of `D(good)`. -/
noncomputable def nuSet (x : D.Rg →ₐ[K] K) : Finset (Places.Rfin K F →ₐ[K] K) :=
  zeroFin (k := K) (D.sec (D.yOf x)) \ Finset.univ.image (liftTuple (D.yOf x))

theorem image_sub_zeroFin (x : D.Rg →ₐ[K] K) [DecidableEq (Places.Rfin K F →ₐ[K] K)] :
    Finset.univ.image (liftTuple (D.yOf x)) ⊆ zeroFin (k := K) (D.sec (D.yOf x)) := by
  intro φ hφ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hφ
  exact lift_mem_zeroFin (D.yOf_good x) i

theorem card_nuSet (x : D.Rg →ₐ[K] K) : (D.nuSet x).card = genusFK K F := by
  classical
  have hy := D.yOf_good x
  rw [nuSet, Finset.card_sdiff_of_subset (D.image_sub_zeroFin x), (zero_spec hy).2.1,
    Finset.card_image_of_injective _ (injective_lift hy), Finset.card_univ, Fintype.card_fin]
  omega

theorem comp_algebraMap (x : D.Rg →ₐ[K] K) :
    x.toRingHom.comp (algebraMap (SymRing K (Places.Rfin K F) d) D.Rg) = (D.yOf x).toRingHom :=
  RingHom.ext fun _ => rfl

theorem map_det_Rg (x : D.Rg →ₐ[K] K) (w : Places.Rfin K F) :
    ((D.det w).map (algebraMap _ D.Rg)).map x.toRingHom =
      C (x ↑(D.isUnit_pres w).unit) * ∏ φ ∈ zeroFin (k := K) (D.sec (D.yOf x)), (X - C (φ w)) := by
  rw [Polynomial.map_map, comp_algebraMap, map_det (D.yOf_good x) w, yOf_apply, IsUnit.unit_spec]

theorem map_monPoly_Rg (x : D.Rg →ₐ[K] K) (w : Places.Rfin K F) :
    ((monPoly (k := K) (g := d) w).map (algebraMap _ D.Rg)).map x.toRingHom =
      ∏ i, (X - C (liftTuple (D.yOf x) i w)) := by
  have h1 := map_symPt_monPoly (k := K) (liftTuple (D.yOf x)) w
  rw [symPt_liftTuple] at h1
  rw [Polynomial.map_map, comp_algebraMap, h1]

/-- The point `ν(A) ∈ Sym^g` at the point `x` of `D(good)`. -/
noncomputable def nuPt (x : D.Rg →ₐ[K] K) : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K :=
  symPt (enumF (D.nuSet x) (D.card_nuSet x))

theorem nuPt_normS (x : D.Rg →ₐ[K] K) (w : Places.Rfin K F) :
    D.nuPt x (normS K w) = ∏ φ ∈ D.nuSet x, φ w := by
  rw [nuPt, symPt_normS]
  exact prod_enumF (D.nuSet x) (D.card_nuSet x) (fun φ => φ w)

end NuData

end Nu

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Add =====
section

/-!
# S4-JacLaw, file O7: addition `Sym^d × Sym^e → Sym^(d+e)`

`addMap : Sym^(d+e)(B) →ₐ Sym^d(B) ⊗ Sym^e(B)` is the `k`-algebra map of the morphism `(A, A') ↦ A + A'`,
built by the morphism criterion `liftPts` (the norm `N(w)` pulls back to `N(w) ⊗ N(w)`). The tensor
product is a f.g. domain (`isDomain_tensor`), so `k`-points determine maps into it. Points: for tuples
`a`, `b` lifting the two factors of a point `x`, `x ∘ addMap = symPt (Fin.append a b)` (`comp_addMap_eq`);
`addMap` is symmetric (`comm_addMap`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym

section Ext

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}

/-- The norm at the point `a + b`. -/
theorem symPt_append {d e : ℕ} (a : Fin d → (B →ₐ[k] k)) (b : Fin e → (B →ₐ[k] k)) (w : B) :
    symPt (Fin.append a b) (normS k w) = symPt a (normS k w) * symPt b (normS k w) := by
  rw [symPt_normS, symPt_normS, symPt_normS, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

end Ext

section Tensor

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B] {d e : ℕ}

instance isDomain_symTensor : IsDomain (SymRing k B d ⊗[k] SymRing k B e) :=
  isDomain_tensor (k := k) (B := SymRing k B d) (A := SymRing k B e)

instance finiteType_symTensor : Algebra.FiniteType k (SymRing k B d ⊗[k] SymRing k B e) :=
  Algebra.FiniteType.trans (S := SymRing k B d) inferInstance inferInstance

end Tensor

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_Uniq =====
section

/-!
# S4-JacLaw, file O8a: uniqueness of `ν`, supports of points, padding and sum maps

* `ptSet y`: the support of a `k`-point `y` of `Sym^n` (a finset); `symPt_eq_of_image_eq` (reduced points with the same
  support are equal).
* `padMap φ c hd : Sym^d → R` with points `x ↦ φ(x) + c` and `sumMap φ ψ : Sym^(n+m) → R` with points
  `x ↦ φ(x) + ψ(x)`, both by the morphism criterion `liftPts`.
* `span_h`: the basis `h` of a `NuData` spans `L(Hn) ∩ B`; `nu_unique`: the zero set of the kernel section does not
  depend on the choice data, only on `Hn` and on any `d` of its zeros; `nuSet_eq_of_sub`: `ν(A') = Z \ A'` whenever
  `A' ⊆ Z = Z(s)` for a good section `s` with the same pole divisor.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section Pts

open Classical

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}

/-- The support of a `k`-point of `Sym^n`. -/
noncomputable def ptSet (y : SymRing k B n →ₐ[k] k) : Finset (B →ₐ[k] k) :=
  Finset.univ.image (liftTuple y)

theorem mem_ptSet (y : SymRing k B n →ₐ[k] k) (φ : B →ₐ[k] k) : φ ∈ ptSet y ↔ ∃ i, liftTuple y i = φ := by
  simp [ptSet]

end Pts

section Morph

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B]
  {R : Type*} [CommRing R] [Algebra k R] [IsReduced R] [Algebra.FiniteType k R]

end Morph

section Uniq

variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace NuData

variable {d : ℕ}

variable {D : NuData K F d} {y : SymRing K (Places.Rfin K F) d →ₐ[K] K}

end NuData

end Uniq

end RamanujanPetersson.JacLaw


end


