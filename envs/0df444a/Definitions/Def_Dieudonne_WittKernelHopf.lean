-- Prove2me | Definitions.Def_Dieudonne_WittKernelHopf
-- name    : Dieudonne_WittKernelHopf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/7ebbbd5e-4368-537e-861b-f897762622a1
-- title:
--   Coordinate Hopf algebra of the kernel of Fb−Fa
-- statement:
--   Fix a prime $p$, a commutative ring $k$ with $(p)=0$, natural numbers $n,a,b$ and an index type $J$. Inside `WittGroup.Coord k p n J` — the polynomial $k$-algebra on generators `X j i` ($j\in J$, $i\in\mathrm{Fin}\,n$), carrying the Hopf structure whose comultiplication, counit and antipode encode Witt addition, the zero vector and Witt negation on the $J$-fold power of the group of truncated Witt vectors of length $n$ — the element `relation k p n a b J j i` is $X_{j,i}^{p^{b}}-X_{j,i}^{p^{a}}$, and `ideal k p n a b J` is the ideal these span. Its meaning is pinned down by `ideal_le_ker_iff`: for a ring homomorphism $g$ out of the polynomial algebra, the ideal lies in $\ker g$ precisely when, for every $j$, the $c$-fold iterate of the coefficientwise $p$-th power map `frobeniusFun` satisfies $F^{b}=F^{a}$ on the image under $g$ of the universal truncated Witt vector `univ k p n j`. The instance `isHopfIdeal` provides the three fields of the project's predicate `IsHopfIdeal' k` for this ideal: it is annihilated by comultiplication followed by the quotient map on each tensor factor, annihilated by the counit, and pulled back into itself by the antipode. Consequently `Coord k p n a b J`, a reducible synonym for the quotient, is a commutative cocommutative Hopf algebra over $k$, and `π` is the resulting surjective bialgebra map, with $\pi(X_{j,i})^{p^{b}}=\pi(X_{j,i})^{p^{a}}$.
--
--   Further declarations record: the images $\pi(X_{j,i})$ generate `Coord` as a $k$-algebra and, when $a<b$, are integral over $k$ (roots of $T^{p^{b}}-T^{p^{a}}$), whence `Coord` is a finite $k$-module for finite $J$ (an instance keyed on `Fact (a < b)`); the tautological element `tauto … j` of `wittHom k p n (Coord …)`, with coefficients $\pi(X_{j,i})$, satisfying $F^{b}=F^{a}$ and $V^{n}=0$, together with its class `tautoClass` in the Dieudonné module obtained as the colimit over length, satisfying the same two identities; that the Witt coefficients of the `tauto` elements, indeed of all elements of `wittHom`, generate `Coord` over $k$; the functor of points `pointsEquiv`, an equivalence between $k$-algebra maps `Coord … → T` and families $(x_j)_{j\in J}$ of length-$n$ truncated Witt vectors over $T$ with $F^{b}x_j=F^{a}x_j$, with the coefficientwise formula; and, for nontrivial $k$, non-vanishing of $\pi(X_{j,i})$, exhibited by a point with one coordinate $1$ and the rest $0$. A group of auxiliary lemmas in the `TruncWitt` namespace computes iterates of `frobeniusFun`: on coefficients it is the $p^{c}$-th power, it commutes with coefficientwise ring maps, and it is additive, zero-preserving and sign-preserving when $p=0$ in the base.
--
--   **Relation to Mathlib.** Mathlib supplies `TruncatedWittVector`, `MvPolynomial`, the quotient-algebra machinery and `HopfAlgebra`; the coefficientwise Frobenius on truncated Witt vectors, the Witt group Hopf algebra `WittGroup.Coord`, Hopf ideals and quotient Hopf algebras, and Dieudonné modules are the project's own notions.
--
--   **Where it is used.** The finite Hopf algebras $\mathcal O(W_n^J[F^b-F^a])$ constructed here are the explicit test objects for the Dieudonné- and Honda-system description of finite commutative group schemes in characteristic $p$, which underlies the analysis of deformation conditions at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Dieudonne_WittKernelHopf.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_WittGroupHopf
import Definitions.Def_HopfAlgebra_HopfIdealQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Function
open scoped TensorProduct

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

omit hp in
@[simp] theorem coeff_frobeniusFun_iterate (c : ℕ) (x : TruncatedWittVector p n R) (i : Fin n) :
    (frobeniusFun^[c] x).coeff i = x.coeff i ^ p ^ c := by
  induction c generalizing x with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply', coeff_frobeniusFun, ih, ← pow_mul, ← pow_succ]

omit hp in
theorem frobeniusFun_iterate_mk (c : ℕ) (g : Fin n → R) :
    frobeniusFun^[c] (TruncatedWittVector.mk p g) = TruncatedWittVector.mk p fun i => g i ^ p ^ c :=
  TruncatedWittVector.ext fun i => by
    rw [coeff_frobeniusFun_iterate, TruncatedWittVector.coeff_mk, TruncatedWittVector.coeff_mk]

theorem map_frobeniusFun_iterate (f : R →+* S) (c : ℕ) (x : TruncatedWittVector p n R) :
    map f (frobeniusFun^[c] x) = frobeniusFun^[c] (map f x) :=
  TruncatedWittVector.ext fun i => by
    simp only [coeff_map, coeff_frobeniusFun_iterate, map_pow]

theorem frobeniusFun_iterate_add (hR : (p : R) = 0) (c : ℕ) (x y : TruncatedWittVector p n R) :
    frobeniusFun^[c] (x + y) = frobeniusFun^[c] x + frobeniusFun^[c] y := by
  induction c generalizing x y with
  | zero => rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, frobeniusFun_add hR]

theorem frobeniusFun_iterate_zero (c : ℕ) : frobeniusFun^[c] (0 : TruncatedWittVector p n R) = 0 := by
  induction c with
  | zero => rfl
  | succ c ih => rw [Function.iterate_succ_apply', ih, frobeniusFun_zero]

theorem frobeniusFun_iterate_neg (hR : (p : R) = 0) (c : ℕ) (x : TruncatedWittVector p n R) :
    frobeniusFun^[c] (-x) = -frobeniusFun^[c] x := by
  have h := frobeniusFun_iterate_add hR c (-x) x
  rw [neg_add_cancel, frobeniusFun_iterate_zero] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

end TruncWitt

namespace WittKernel

open WittGroup TruncWitt

variable (k : Type u) [CommRing k] (p : ℕ) (n a b : ℕ) (J : Type v)

noncomputable def relation (j : J) (i : Fin n) : WittGroup.Coord k p n J :=
  X j i ^ p ^ b - X j i ^ p ^ a

noncomputable def ideal : Ideal (WittGroup.Coord k p n J) :=
  Ideal.span (Set.range fun ji : J × Fin n => relation k p n a b J ji.1 ji.2)

variable {k p n a b J}

theorem relation_mem_ideal (j : J) (i : Fin n) : relation k p n a b J j i ∈ ideal k p n a b J :=
  Ideal.subset_span ⟨(j, i), rfl⟩

theorem ideal_le_iff {I : Ideal (WittGroup.Coord k p n J)} :
    ideal k p n a b J ≤ I ↔ ∀ j i, relation k p n a b J j i ∈ I := by
  constructor
  · exact fun h j i => h (relation_mem_ideal j i)
  · intro h
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨j, i⟩, rfl⟩
    exact h j i

variable [hp : Fact p.Prime]

theorem ringHom_X_pow {B : Type w} [CommRing B] (g : WittGroup.Coord k p n J →+* B) (j : J)
    (i : Fin n) (c : ℕ) :
    g (X j i) ^ p ^ c = (frobeniusFun^[c] (TruncWitt.map (p := p) g (univ k p n j))).coeff i := by
  rw [coeff_frobeniusFun_iterate, coeff_map, coeff_univ]

theorem ringHom_relation {B : Type w} [CommRing B] (g : WittGroup.Coord k p n J →+* B) (j : J)
    (i : Fin n) :
    g (relation k p n a b J j i) =
      (frobeniusFun^[b] (TruncWitt.map (p := p) g (univ k p n j))).coeff i -
        (frobeniusFun^[a] (TruncWitt.map (p := p) g (univ k p n j))).coeff i := by
  rw [relation, map_sub, map_pow, map_pow, ringHom_X_pow, ringHom_X_pow]

theorem ideal_le_ker_iff {B : Type w} [CommRing B] (g : WittGroup.Coord k p n J →+* B) :
    ideal k p n a b J ≤ RingHom.ker g ↔
      ∀ j, frobeniusFun^[b] (TruncWitt.map (p := p) g (univ k p n j)) =
        frobeniusFun^[a] (TruncWitt.map (p := p) g (univ k p n j)) := by
  rw [ideal_le_iff]
  simp only [RingHom.mem_ker, ringHom_relation, sub_eq_zero]
  exact ⟨fun h j => TruncatedWittVector.ext fun i => h j i,
    fun h j i => congrArg (TruncatedWittVector.coeff i) (h j)⟩

section HopfIdeal

variable [CharP k p]

variable (k p n a b J)

local notation "𝒪" => WittGroup.Coord k p n J
local notation "I" => ideal k p n a b J
local notation "πI" => (Ideal.Quotient.mk (ideal k p n a b J))

omit [CharP k p] in

theorem frobeniusFun_iterate_map_mk_univ (j : J) :
    frobeniusFun^[b] (TruncWitt.map (p := p) πI (univ k p n j)) =
      frobeniusFun^[a] (TruncWitt.map (p := p) πI (univ k p n j)) :=
  (ideal_le_ker_iff (πI : 𝒪 →+* 𝒪 ⧸ I)).1 (by rw [Ideal.mk_ker]) j

instance isHopfIdeal : (ideal k p n a b J).IsHopfIdeal' k where
  map_mkₐ_comul_eq_zero := by

    let h : 𝒪 →ₐ[k] (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).comp
        (Bialgebra.comulAlgHom k 𝒪)
    suffices hle : I ≤ RingHom.ker h.toRingHom by
      intro x hx
      exact hle hx
    rw [ideal_le_iff]
    intro j i
    rw [RingHom.mem_ker]

    set y : TruncatedWittVector p n (𝒪 ⧸ I) := TruncWitt.map (p := p) πI (univ k p n j) with hy
    let iL : (𝒪 ⧸ I) →+* (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
      (Algebra.TensorProduct.includeLeft : (𝒪 ⧸ I) →ₐ[k] _).toRingHom
    let iR : (𝒪 ⧸ I) →+* (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
      (Algebra.TensorProduct.includeRight : (𝒪 ⧸ I) →ₐ[k] _).toRingHom
    have hX : ∀ i, h.toRingHom (X j i) = (TruncWitt.map iL y + TruncWitt.map iR y).coeff i := by
      intro i
      let g : 𝒪 ⊗[k] 𝒪 →+* (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I) :=
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).toRingHom
      have h1 : h.toRingHom (X j i) = g (WittGroup.comul k p n J (X j i)) := rfl
      rw [h1, ringHom_comul_X]
      congr 2
      · refine TruncatedWittVector.ext fun i => ?_
        rw [TruncatedWittVector.coeff_mk, coeff_map, hy, coeff_map, coeff_univ]
        rfl
      · refine TruncatedWittVector.ext fun i => ?_
        rw [TruncatedWittVector.coeff_mk, coeff_map, hy, coeff_map, coeff_univ]
        rfl
    have hp0 : (p : (𝒪 ⧸ I) ⊗[k] (𝒪 ⧸ I)) = 0 := natCast_eq_zero_of_algebra k p _
    have hpow : ∀ c : ℕ, h.toRingHom (X j i) ^ p ^ c =
        (TruncWitt.map iL (frobeniusFun^[c] y) + TruncWitt.map iR (frobeniusFun^[c] y)).coeff i := by
      intro c
      rw [hX i, ← coeff_frobeniusFun_iterate, frobeniusFun_iterate_add hp0,
        map_frobeniusFun_iterate, map_frobeniusFun_iterate]
    change h.toRingHom (relation k p n a b J j i) = 0
    rw [relation, map_sub, map_pow, map_pow, hpow, hpow, hy, frobeniusFun_iterate_map_mk_univ,
      sub_self]
  counit_eq_zero := by
    suffices hle : I ≤ RingHom.ker (Bialgebra.counitAlgHom k 𝒪).toRingHom by
      intro x hx
      exact hle hx
    rw [ideal_le_iff]
    intro j i
    rw [RingHom.mem_ker]
    change Coalgebra.counit (R := k) (relation k p n a b J j i) = 0
    rw [relation, counit_def, map_sub, map_pow, map_pow, counit_X,
      zero_pow (pow_ne_zero _ hp.out.ne_zero), zero_pow (pow_ne_zero _ hp.out.ne_zero), sub_self]
  antipode_mem := by
    suffices hle : I ≤ (ideal k p n a b J).comap (WittGroup.antipode k p n J) by
      intro x hx
      have := hle hx
      rwa [Ideal.mem_comap, ← antipode_def] at this
    rw [ideal_le_iff]
    intro j i
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    set g : 𝒪 →+* 𝒪 ⧸ I := (πI).comp (WittGroup.antipode k p n J).toRingHom with hg
    set y : TruncatedWittVector p n (𝒪 ⧸ I) := TruncWitt.map (p := p) πI (univ k p n j) with hy
    have hX : ∀ i, g (X j i) = (-y).coeff i := by
      intro i
      rw [hg, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, antipode_X,
        ← coeff_map (p := p), map_neg, hy]
    have hp0 : (p : 𝒪 ⧸ I) = 0 := natCast_eq_zero_of_algebra k p _
    have hpow : ∀ c : ℕ, g (X j i) ^ p ^ c = (-(frobeniusFun^[c] y)).coeff i := by
      intro c
      rw [hX i, ← coeff_frobeniusFun_iterate, frobeniusFun_iterate_neg hp0]
    change g (relation k p n a b J j i) = 0
    rw [relation, map_sub, map_pow, map_pow, hpow, hpow, hy, frobeniusFun_iterate_map_mk_univ,
      sub_self]

end HopfIdeal

variable (k p n a b J)

abbrev Coord : Type (max u v) := WittGroup.Coord k p n J ⧸ ideal k p n a b J

variable [CharP k p]

noncomputable example : HopfAlgebra k (Coord k p n a b J) := inferInstance

example : Coalgebra.IsCocomm k (Coord k p n a b J) := inferInstance

noncomputable def π : WittGroup.Coord k p n J →ₐc[k] Coord k p n a b J :=
  HopfAlgebra.quotientBialgHom k (ideal k p n a b J)

variable {k p n a b J}

@[simp] theorem π_apply (x : WittGroup.Coord k p n J) :
    π k p n a b J x = Ideal.Quotient.mk (ideal k p n a b J) x := rfl

theorem π_toAlgHom :
    (π k p n a b J : WittGroup.Coord k p n J →ₐ[k] Coord k p n a b J) =
      Ideal.Quotient.mkₐ k (ideal k p n a b J) := rfl

theorem π_surjective : Surjective (π k p n a b J) := Ideal.Quotient.mk_surjective

theorem π_relation (j : J) (i : Fin n) : π k p n a b J (relation k p n a b J j i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (relation_mem_ideal j i)

theorem π_X_pow_eq (j : J) (i : Fin n) :
    π k p n a b J (X j i) ^ p ^ b = π k p n a b J (X j i) ^ p ^ a := by
  rw [← sub_eq_zero, ← map_pow, ← map_pow, ← map_sub]
  exact π_relation j i

theorem adjoin_range_π_X_eq_top :
    Algebra.adjoin k (Set.range fun ji : J × Fin n => π k p n a b J (X ji.1 ji.2)) = ⊤ := by
  have h1 : (Set.range fun ji : J × Fin n => π k p n a b J (X ji.1 ji.2)) =
      (π k p n a b J : WittGroup.Coord k p n J →ₐ[k] Coord k p n a b J) ''
        Set.range (fun ji : J × Fin n => (MvPolynomial.X ji : MvPolynomial (J × Fin n) k)) := by
    rw [← Set.range_comp]
    rfl
  rw [h1, Algebra.adjoin_image]
  have h2 : Algebra.adjoin k (Set.range fun ji : J × Fin n =>
      (MvPolynomial.X ji : MvPolynomial (J × Fin n) k)) = ⊤ := MvPolynomial.adjoin_range_X
  change Subalgebra.map _ (Algebra.adjoin k (Set.range fun ji : J × Fin n =>
      (MvPolynomial.X ji : MvPolynomial (J × Fin n) k))) = ⊤
  rw [h2, Algebra.map_top, AlgHom.range_eq_top]
  exact π_surjective

theorem isIntegral_π_X (hab : a < b) (j : J) (i : Fin n) : IsIntegral k (π k p n a b J (X j i)) := by
  have hlt : p ^ a < p ^ b := Nat.pow_lt_pow_right hp.out.one_lt hab
  refine ⟨Polynomial.X ^ p ^ b - Polynomial.X ^ p ^ a, ?_, ?_⟩
  · refine Polynomial.monic_X_pow_sub (lt_of_le_of_lt (Polynomial.degree_X_pow_le _) ?_)
    exact_mod_cast hlt
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X_pow]
    rw [sub_eq_zero]
    exact π_X_pow_eq j i

theorem moduleFinite [Finite J] (hab : a < b) : Module.Finite k (Coord k p n a b J) := by
  have hfg := fg_adjoin_of_finite (R := k)
    (s := Set.range fun ji : J × Fin n => π k p n a b J (X ji.1 ji.2)) (Set.finite_range _)
    (fun x hx => by
      obtain ⟨⟨j, i⟩, rfl⟩ := hx
      exact isIntegral_π_X hab j i)
  rw [adjoin_range_π_X_eq_top, Algebra.top_toSubmodule] at hfg
  exact Module.Finite.of_fg_top hfg

instance instModuleFinite [Finite J] [hab : Fact (a < b)] : Module.Finite k (Coord k p n a b J) :=
  moduleFinite hab.out

variable (k p n a b J)

noncomputable def tauto (j : J) : wittHom k p n (Coord k p n a b J) :=
  wittHomMap p n (π k p n a b J) (univHom j)

variable {k p n a b J}

@[simp] theorem coe_tauto (j : J) :
    (tauto k p n a b J j : TruncatedWittVector p n (Coord k p n a b J)) =
      TruncWitt.map (p := p) (Ideal.Quotient.mk (ideal k p n a b J)) (univ k p n j) := rfl

@[simp] theorem coeff_tauto (j : J) (i : Fin n) :
    (tauto k p n a b J j : TruncatedWittVector p n (Coord k p n a b J)).coeff i =
      π k p n a b J (X j i) := by
  rw [coe_tauto, coeff_map, coeff_univ, π_apply]

theorem frobenius_iterate_tauto (j : J) :
    (wittHomFrobenius k p n (Coord k p n a b J))^[b] (tauto k p n a b J j) =
      (wittHomFrobenius k p n (Coord k p n a b J))^[a] (tauto k p n a b J j) := by
  have key : ∀ (c : ℕ) (x : wittHom k p n (Coord k p n a b J)),
      (((wittHomFrobenius k p n (Coord k p n a b J))^[c] x : wittHom k p n (Coord k p n a b J)) :
        TruncatedWittVector p n (Coord k p n a b J)) = frobeniusFun^[c] (x : TruncatedWittVector p n _) := by
    intro c
    induction c with
    | zero => intro x; rfl
    | succ c ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', coe_wittHomFrobenius, ih]
  apply Subtype.ext
  rw [key, key, coe_tauto]
  exact frobeniusFun_iterate_map_mk_univ k p n a b J j

theorem verschiebung_iterate_tauto (j : J) :
    (wittHomVerschiebung k p n (Coord k p n a b J))^[n] (tauto k p n a b J j) = 0 :=
  wittHomVerschiebung_iterate_eq_zero _

variable (k p n a b J) in

noncomputable def tautoClass (j : J) : DieudonneModule k p (Coord k p n a b J) :=
  DieudonneModule.of k p (Coord k p n a b J) n (tauto k p n a b J j)

theorem tautoClass_def (j : J) :
    tautoClass k p n a b J j = DieudonneModule.of k p (Coord k p n a b J) n (tauto k p n a b J j) :=
  rfl

theorem frobenius_iterate_tautoClass (j : J) :
    (DieudonneModule.frobenius k p (Coord k p n a b J))^[b] (tautoClass k p n a b J j) =
      (DieudonneModule.frobenius k p (Coord k p n a b J))^[a] (tautoClass k p n a b J j) := by
  have key : ∀ (c : ℕ) (x : wittHom k p n (Coord k p n a b J)),
      (DieudonneModule.frobenius k p (Coord k p n a b J))^[c] (DieudonneModule.of k p _ n x) =
        DieudonneModule.of k p _ n ((wittHomFrobenius k p n (Coord k p n a b J))^[c] x) := by
    intro c
    induction c with
    | zero => intro x; rfl
    | succ c ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        DieudonneModule.frobenius_of]
  rw [tautoClass_def, key, key, frobenius_iterate_tauto]

theorem verschiebung_iterate_tautoClass (j : J) :
    (DieudonneModule.verschiebung k p (Coord k p n a b J))^[n] (tautoClass k p n a b J j) = 0 := by
  have key : ∀ (c : ℕ) (x : wittHom k p n (Coord k p n a b J)),
      (DieudonneModule.verschiebung k p (Coord k p n a b J))^[c] (DieudonneModule.of k p _ n x) =
        DieudonneModule.of k p _ n ((wittHomVerschiebung k p n (Coord k p n a b J))^[c] x) := by
    intro c
    induction c with
    | zero => intro x; rfl
    | succ c ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        DieudonneModule.verschiebung_of]
  rw [tautoClass_def, key, verschiebung_iterate_tauto, map_zero]

theorem adjoin_coeff_tauto_eq_top :
    Algebra.adjoin k {c : Coord k p n a b J | ∃ (j : J) (i : Fin n),
      (tauto k p n a b J j : TruncatedWittVector p n (Coord k p n a b J)).coeff i = c} = ⊤ := by
  refine top_le_iff.1 (le_trans (le_of_eq adjoin_range_π_X_eq_top.symm) (Algebra.adjoin_mono ?_))
  rintro _ ⟨⟨j, i⟩, rfl⟩
  exact ⟨j, i, coeff_tauto j i⟩

theorem adjoin_coeff_wittHom_eq_top :
    Algebra.adjoin k {c : Coord k p n a b J | ∃ (x : wittHom k p n (Coord k p n a b J)) (i : Fin n),
      (x : TruncatedWittVector p n (Coord k p n a b J)).coeff i = c} = ⊤ := by
  refine top_le_iff.1 (le_trans (le_of_eq adjoin_coeff_tauto_eq_top.symm) (Algebra.adjoin_mono ?_))
  rintro _ ⟨j, i, rfl⟩
  exact ⟨tauto k p n a b J j, i, rfl⟩

section Points

variable {T : Type w} [CommRing T] [Algebra k T]

noncomputable def pointsEquiv :
    (Coord k p n a b J →ₐ[k] T) ≃
      {x : J → TruncatedWittVector p n T // ∀ j, frobeniusFun^[b] (x j) = frobeniusFun^[a] (x j)} where
  toFun f := ⟨WittGroup.pointsEquiv (f.comp (π k p n a b J : WittGroup.Coord k p n J →ₐ[k] _)),
    fun j => by
      have hle : ideal k p n a b J ≤ RingHom.ker
          (f.comp (π k p n a b J : WittGroup.Coord k p n J →ₐ[k] _)).toRingHom := by
        intro x hx
        rw [RingHom.mem_ker]
        change f (π k p n a b J x) = 0
        rw [π_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
      have := (ideal_le_ker_iff _).1 hle j
      rwa [← pointsEquiv_eq_map_univ] at this⟩
  invFun x := Ideal.Quotient.liftₐ (ideal k p n a b J) (WittGroup.pointsEquiv.symm x.1)
    (fun y hy => (ideal_le_ker_iff (WittGroup.pointsEquiv.symm x.1 :
        WittGroup.Coord k p n J →ₐ[k] T).toRingHom).2 (fun j => by
      rw [← pointsEquiv_eq_map_univ, Equiv.apply_symm_apply]
      exact x.2 j) hy)
  left_inv f := by
    refine Ideal.Quotient.algHom_ext k ?_
    rw [Ideal.Quotient.liftₐ_comp, Equiv.symm_apply_apply]
    rfl
  right_inv x := by
    apply Subtype.ext
    change WittGroup.pointsEquiv _ = x.1
    conv_rhs => rw [← (WittGroup.pointsEquiv (R := k) (p := p) (n := n) (J := J)).apply_symm_apply x.1]
    congr 1

theorem pointsEquiv_apply_coeff (f : Coord k p n a b J →ₐ[k] T) (j : J) (i : Fin n) :
    ((pointsEquiv f).1 j).coeff i = f (π k p n a b J (X j i)) := by
  change (WittGroup.pointsEquiv _ j).coeff i = _
  rw [coeff_pointsEquiv]
  rfl

end Points

theorem π_X_ne_zero [Nontrivial k] (j : J) (i : Fin n) :
    π k p n a b J (X j i) ≠ 0 := by
  classical

  let x : J → TruncatedWittVector p n k := fun j' =>
    TruncatedWittVector.mk p fun i' => if j' = j ∧ i' = i then 1 else 0
  have hx : ∀ j', frobeniusFun^[b] (x j') = frobeniusFun^[a] (x j') := by
    intro j'
    refine TruncatedWittVector.ext fun i' => ?_
    simp only [coeff_frobeniusFun_iterate, x, TruncatedWittVector.coeff_mk]
    split_ifs
    · rw [one_pow, one_pow]
    · rw [zero_pow (pow_ne_zero _ hp.out.ne_zero), zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  let f : Coord k p n a b J →ₐ[k] k := pointsEquiv.symm ⟨x, hx⟩
  intro h
  have h1 : f (π k p n a b J (X j i)) = 1 := by
    rw [← pointsEquiv_apply_coeff, Equiv.apply_symm_apply]
    simp [x]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

end WittKernel

end Deformation


