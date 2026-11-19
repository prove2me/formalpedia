-- Prove2me | Definitions.Def_RPLib_S4_CDPack11
-- name    : RPLib_S4_CDPack11
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:11:54.003831+00:00
-- url     : https://prove2.me/theorems/3b5fafbd-1108-4283-a9e3-889f7fb5cb82
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 11 of 71
-- statement:
--   Part 11 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CoreA_ZInt`: S4-CoreA, parts Z1 + Z2: the inverse roots of the zeta function
--   * `Def_RP_CP4a_FE`: S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius
--   * `Def_RP_CoreA_Ord`: S4-CoreA part O1: the l-part of the order of an automorphism of an elementary abelian l-group
--   * `Def_RP_CoreA_Fin`: S4-CoreA part F1: `A[l]` is finite
--   * `Def_RP_CoreA_Val`: S4-CoreA part V1: norms of `x ^ n - 1` in an ultrametric normed field
--   * `Def_RP_CoreA_Div`: S4-CoreA part S1: the divisible part of an `l`-primary group with finite `A[l]`
--   * `Def_RP_CoreA_Basis`: S4-CoreA part S2a: compatible bases of `G[l^N]` for a divisible `l`-primary group
--   * `Def_RP_CoreA_Tate`: S4-CoreA part S2b: the Tate module coordinates and the matrix of an endomorphism
--   * `Def_RP_PicDescent_C2`: S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_PicDescentA
import Definitions.Def_RPLib_S4_CP4aNewton
import Definitions.Def_RPLib_S4_PicDescentC1

/-!
# Curve-duality library package, part 11 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CoreA_ZInt`: S4-CoreA, parts Z1 + Z2: the inverse roots of the zeta function
* `Def_RP_CP4a_FE`: S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius
* `Def_RP_CoreA_Ord`: S4-CoreA part O1: the l-part of the order of an automorphism of an elementary abelian l-group
* `Def_RP_CoreA_Fin`: S4-CoreA part F1: `A[l]` is finite
* `Def_RP_CoreA_Val`: S4-CoreA part V1: norms of `x ^ n - 1` in an ultrametric normed field
* `Def_RP_CoreA_Div`: S4-CoreA part S1: the divisible part of an `l`-primary group with finite `A[l]`
* `Def_RP_CoreA_Basis`: S4-CoreA part S2a: compatible bases of `G[l^N]` for a divisible `l`-primary group
* `Def_RP_CoreA_Tate`: S4-CoreA part S2b: the Tate module coordinates and the matrix of an endomorphism
* `Def_RP_PicDescent_C2`: S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CoreA_ZInt =====
section

/-!
# S4-CoreA, parts Z1 + Z2: the inverse roots of the zeta function

For a function field `F / Fq` with full constant field, `q = #Fq`, `g = genusF Fq F`, `A_n = numEff Fq F n`, and
ANY multiset `c ⊆ ℂ` with `N_m = 1 + q^m - Σ_i c_i^m` (`m ≥ 1`):
* `prod_eq_zeta_F` (Z1): `Π_i (1 - c_i X) = (1 - X)(1 - q X) Σ_n A_n X^n` in `ℂ⟦X⟧`;
* `exists_int_poly` (Z1): `Π_i (1 - c_i X)` has integer coefficients;
* `numEff_top'` (Z2): `(q - 1) A_{2g-2} = h (q^(g-1) - 1) + q^g - q^(g-1)` (`g ≥ 1`, `h = #Pic⁰`), from Riemann-Roch:
  a class of degree `2g - 2` has `ℓ = g` if it is canonical and `ℓ = g - 1` otherwise;
* **`card_eq_two_genus`** (Z2): if moreover `#c ≤ 2g`, then `#c = 2g`, `Π_i c_i = q^g`, and `Π_i (1 - c_i X)` is the
  image of an integer polynomial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.CoreA

open Places RR ZetaSB PicDescent

section PS

open PowerSeries

/-- Z1, abstract: Newton's identity and `b_k = 1 + Q^k - Σ c_i^k` force `Π (1 - c_i X) = (1 - X)(1 - Q X) Σ a_k X^k`. -/
theorem prod_eq_zeta (a b : ℕ → ℂ) (Q : ℂ) (c : Multiset ℂ) (ha0 : a 0 = 1)
    (hnewt : ∀ k : ℕ, ((k : ℂ) + 1) * a (k + 1) = ∑ j ∈ Finset.range (k + 1), b (j + 1) * a (k - j))
    (hb : ∀ k : ℕ, b (k + 1) = 1 + Q ^ (k + 1) - (c.map (· ^ (k + 1))).sum) :
    (c.map fun r => 1 - C r * X).prod = (1 - C 1 * X) * ((1 - C Q * X) * PowerSeries.mk a) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : PowerSeries ℂ, Z = PowerSeries.mk a := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : PowerSeries ℂ, G = PowerSeries.mk fun i => b (i + 1) := ⟨_, rfl⟩
  have hdZ : derivative ℂ Z = G * Z := by
    ext n
    rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hZ, coeff_mk]
    simp only [hG, coeff_mk]
    linear_combination hnewt n
  have hG' : G = PowerSeries.mk (fun i => (1 : ℂ) ^ (i + 1)) + PowerSeries.mk (fun i => Q ^ (i + 1)) -
      psumSeries c := by
    ext n
    simp only [hG, psumSeries, map_add, map_sub, coeff_mk, hb, one_pow]
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries ℂ, V = (1 - C Q * X) * Z := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : PowerSeries ℂ, W = (1 - C 1 * X) * V := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : PowerSeries ℂ, P = (c.map fun r => 1 - C r * X).prod := ⟨_, rfl⟩
  have hWd : derivative ℂ W = W * -psumSeries c := by
    have g1 := one_sub_mul_geom 1
    have gQ := one_sub_mul_geom Q
    rw [hW, hV, Derivation.leibniz, Derivation.leibniz, hdZ, deriv_one_sub, deriv_one_sub, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    rw [hG']
    linear_combination ((1 - C Q * X) * Z) * g1 + ((1 - C 1 * X) * Z) * gQ
  have hPd : derivative ℂ P = P * -psumSeries c := by
    rw [hP, deriv_prod]
    ring
  have hV0 : coeff 0 V = a 0 := by rw [hV, coeff_zero_one_sub_mul, hZ, coeff_mk]
  have hW0 : coeff 0 W = 1 := by rw [hW, coeff_zero_one_sub_mul, hV0, ha0]
  have hWP : W = P := eq_of_derivative_eq_mul W P _ hWd hPd (by rw [hW0, hP, coeff_zero_prod_one_sub])
  rw [← hP, ← hWP, hW, hV, hZ]

theorem map_mk_int (A : ℕ → ℤ) :
    PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.mk A) = PowerSeries.mk fun k => (A k : ℂ) := by
  ext k
  simp [coeff_map]

/-- Z1, integrality: a product `Π (1 - c_i X)` equal to `(1 - X)(1 - q X) Σ A_k X^k` with `A_k, q ∈ ℤ` comes from
an integer polynomial. -/
theorem exists_int_poly (A : ℕ → ℤ) (q : ℤ) (c : Multiset ℂ)
    (h : (c.map fun r => 1 - C r * X).prod =
      (1 - C 1 * X) * ((1 - C (q : ℂ) * X) * PowerSeries.mk fun k => (A k : ℂ))) :
    ∃ L : ℤ[X], L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod := by
  set S : PowerSeries ℤ := (1 - C 1 * X) * ((1 - C q * X) * PowerSeries.mk A) with hSdef
  have hS : PowerSeries.map (Int.castRingHom ℂ) S = (c.map fun r => 1 - C r * X).prod := by
    rw [h, hSdef, map_mul, map_mul, map_mk_int]
    simp [map_sub, PowerSeries.map_X]
  set p : ℂ[X] := (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod with hpdef
  refine ⟨trunc (p.natDegree + 1) S, ?_⟩
  ext k
  rw [Polynomial.coeff_map, coeff_trunc]
  split_ifs with hk
  · have h2 := congrArg (coeff k) hS
    rw [coeff_map, ← coe_prod_one_sub, ← hpdef, Polynomial.coeff_coe] at h2
    exact h2
  · have hlt : p.natDegree < k := by omega
    rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hlt]

end PS

/-- The coefficient of `X^#c` in `Π (1 - c_i X)` is `(-1)^#c Π c_i`. -/
theorem coeff_card_prod_one_sub (c : Multiset ℂ) :
    ((c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod).coeff (Multiset.card c) =
      (-1) ^ Multiset.card c * c.prod := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons r c ih =>
    have hlt : ((c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod).natDegree < Multiset.card c + 1 := by
      have := natDegree_prod_one_sub_le c
      omega
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Multiset.prod_cons,
      show (1 - Polynomial.C r * Polynomial.X) * (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod =
        (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod -
          Polynomial.C r * (Polynomial.X * (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod) by ring,
      Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, ih,
      Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    ring

section Concrete

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

open PowerSeries in
/-- Z1, concrete: `Π (1 - c_i X) = (1 - X)(1 - q X) Z(X)` with `Z(X) = Σ A_n X^n`. -/
theorem prod_eq_zeta_F (hk : constField Fq F = ⊥) (c : Multiset ℂ)
    (hc : ∀ m : ℕ, 1 ≤ m →
      (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) :
    (c.map fun r => 1 - C r * X).prod = (1 - C 1 * X) * ((1 - C (Fintype.card Fq : ℂ) * X) *
      PowerSeries.mk fun k => (numEff Fq F k : ℂ)) := by
  refine prod_eq_zeta (fun k => (numEff Fq F k : ℂ)) (fun j => (numPoints Fq F j : ℂ)) _ c
    (by simp [numEff_zero]) ?_ (fun k => hc (k + 1) (Nat.succ_pos k))
  intro k
  have h := newton_delta' Fq F k
  simp only [delta_eq_one Fq F hk, one_mul] at h
  have h' := congrArg (Nat.cast : ℕ → ℂ) h
  push_cast at h'
  linear_combination h'

theorem eq_zero_of_deg_eq_zero {D : Divisor Fq F} (hD : 0 ≤ D) (h0 : Divisor.deg D = 0) : D = 0 := by
  classical
  have h1 : D ∈ effDivs Fq F 0 := mem_effDivs.mpr ⟨hD, by simp [h0]⟩
  have h2 : (0 : Divisor Fq F) ∈ effDivs Fq F 0 := mem_effDivs.mpr ⟨le_rfl, by simp [Divisor.deg]⟩
  have h3 : (effDivs Fq F 0).card ≤ 1 := (numEff_zero (Fq := Fq) (F := F)).le
  exact Finset.card_le_one.mp h3 D h1 0 h2

/-- Every divisor of degree `n ≥ g` is equivalent to an effective one. -/
theorem exists_eff_of_deg' (hk : constField Fq F = ⊥) {n : ℕ} (hn : (genusF Fq F : ℤ) ≤ n)
    (D : Divisor Fq F) (hD : Divisor.deg D = n) :
    ∃ E ∈ effDivs Fq F n, cls Fq F E = cls Fq F D := by
  have h1 := riemann_inequalityF' hk D
  rw [hD] at h1
  have hpos : 0 < ellF Fq F D := by
    have : (0 : ℤ) < ellF Fq F D := by omega
    exact_mod_cast this
  obtain ⟨f, hfL, hf0⟩ := Data.exists_ne_zero_of_ell_pos hpos
  refine ⟨Places.div f + D, mem_effDivs.mpr ⟨(mem_LF hf0).mp hfL, ?_⟩, cls_div_add hf0 D⟩
  rw [Divisor.deg_add, Places.deg_div hf0, hD, zero_add]

theorem hcl_le' [DecidableEq (Divisor Fq F ⧸ princ Fq F)] (hk : constField Fq F = ⊥) {n n' : ℕ}
    (hn : (genusF Fq F : ℤ) ≤ n) (B : Divisor Fq F) (hB : Divisor.deg B = (n' : ℤ) - n) :
    hcl Fq F n' ≤ hcl Fq F n := by
  unfold hcl
  refine (Finset.card_le_card (t := ((effDivs Fq F n).image (cls Fq F)).image (· + cls Fq F B))
    fun c hc => ?_).trans Finset.card_image_le
  obtain ⟨E', hE', rfl⟩ := Finset.mem_image.mp hc
  have hdeg : Divisor.deg (E' - B) = n := by
    rw [Divisor.deg_sub, hB, (mem_effDivs.mp hE').2]
    ring
  obtain ⟨E, hE, hEc⟩ := exists_eff_of_deg' hk hn (E' - B) hdeg
  refine Finset.mem_image.mpr ⟨cls Fq F E, Finset.mem_image_of_mem _ hE, ?_⟩
  rw [hEc]
  simp only [cls, QuotientAddGroup.mk_sub, sub_add_cancel]

/-- A divisor in the canonical class has `ℓ = g`. -/
theorem ellF_of_cls_eq (hk : constField Fq F = ⊥) {W E : Divisor Fq F} (hW : IsCanonicalF Fq F W)
    (h : cls Fq F E = cls Fq F W) : ellF Fq F E = genusF Fq F := by
  obtain ⟨f, hf, hdiv⟩ := (mem_princ Fq F).mp (QuotientAddGroup.eq.mp h.symm)
  have hE : E = W + Places.div f := by rw [hdiv]; abel
  rw [hE]
  exact ellF_canonical hk (isCanonicalF_add_div hW hf)

/-- A divisor of degree `2g - 2` outside the canonical class has `ℓ = g - 1`. -/
theorem ellF_of_cls_ne (hk : constField Fq F = ⊥) {W E : Divisor Fq F} (hW : IsCanonicalF Fq F W)
    (hE : Divisor.deg E = 2 * (genusF Fq F : ℤ) - 2) (h : cls Fq F E ≠ cls Fq F W) :
    (ellF Fq F E : ℤ) = genusF Fq F - 1 := by
  have hRR := riemannRochF' hk hW E
  have h0 : ellF Fq F (W - E) = 0 := by
    by_contra hne
    obtain ⟨f, hfL, hf0⟩ := Data.exists_ne_zero_of_ell_pos (Nat.pos_of_ne_zero hne)
    have hnn := (mem_LF hf0).mp hfL
    have hdeg : Divisor.deg (Places.div f + (W - E)) = 0 := by
      rw [Divisor.deg_add, Places.deg_div hf0, Divisor.deg_sub, degF_canonical hk hW, hE]
      ring
    have hz := eq_zero_of_deg_eq_zero hnn hdeg
    rw [← add_sub_assoc] at hz
    apply h
    rw [← sub_eq_zero.mp hz, cls_div_add hf0]
  rw [h0, hE] at hRR
  push_cast at hRR
  linarith

/-- `(q - 1) A_{2g-2} = #(classes of degree 2g-2 with an effective member) (q^(g-1) - 1) + q^g - q^(g-1)`. -/
theorem numEff_top [DecidableEq (Divisor Fq F ⧸ princ Fq F)] (hk : constField Fq F = ⊥) {W : Divisor Fq F}
    (hW : IsCanonicalF Fq F W) (hg : 1 ≤ genusF Fq F) :
    ((Fintype.card Fq : ℤ) - 1) * numEff Fq F (2 * genusF Fq F - 2) =
      hcl Fq F (2 * genusF Fq F - 2) * ((Fintype.card Fq : ℤ) ^ (genusF Fq F - 1) - 1) +
        ((Fintype.card Fq : ℤ) ^ genusF Fq F - (Fintype.card Fq : ℤ) ^ (genusF Fq F - 1)) := by
  set n := 2 * genusF Fq F - 2 with hn
  set I := (effDivs Fq F n).image (cls Fq F) with hI
  have hWI : cls Fq F W ∈ I := by
    have hpos : 0 < ellF Fq F W := by rw [ellF_canonical hk hW]; omega
    obtain ⟨f, hfL, hf0⟩ := Data.exists_ne_zero_of_ell_pos hpos
    refine Finset.mem_image.mpr ⟨Places.div f + W, mem_effDivs.mpr ⟨(mem_LF hf0).mp hfL, ?_⟩, cls_div_add hf0 W⟩
    rw [Divisor.deg_add, Places.deg_div hf0, zero_add, degF_canonical hk hW, hn]
    omega
  have hterm : ∀ C ∈ I, ((((effDivs Fq F n).filter fun E => cls Fq F E = C).card : ℕ) : ℤ) *
      ((Fintype.card Fq : ℤ) - 1) = ((Fintype.card Fq : ℤ) ^ (genusF Fq F - 1) - 1) +
        if C = cls Fq F W then (Fintype.card Fq : ℤ) ^ genusF Fq F - (Fintype.card Fq : ℤ) ^ (genusF Fq F - 1)
        else 0 := by
    intro C hC
    obtain ⟨E0, hE0, rfl⟩ := Finset.mem_image.mp hC
    have h := card_fiber_mul hk hE0
    have hq0 : 1 ≤ Fintype.card Fq := Fintype.card_pos
    have hq1 : 1 ≤ Fintype.card Fq ^ ellF Fq F E0 := Nat.one_le_pow _ _ Fintype.card_pos
    zify [hq0, hq1] at h
    rw [h]
    have hdeg : Divisor.deg E0 = 2 * (genusF Fq F : ℤ) - 2 := by
      rw [(mem_effDivs.mp hE0).2, hn]
      omega
    split_ifs with hc
    · rw [ellF_of_cls_eq hk hW hc]
      ring
    · have h1 := ellF_of_cls_ne hk hW hdeg hc
      have h2 : ellF Fq F E0 = genusF Fq F - 1 := by omega
      rw [h2]
      ring
  rw [numEff, Finset.card_eq_sum_card_fiberwise (f := cls Fq F) (t := I) (fun E hE => Finset.mem_image_of_mem _ hE)]
  push_cast
  rw [mul_comm ((Fintype.card Fq : ℤ) - 1), Finset.sum_mul, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const,
    Finset.sum_ite_eq' I (cls Fq F W), if_pos hWI, nsmul_eq_mul, hcl, ← hI]

/-- For `g ≥ 2` every class of degree `2g - 2` has an effective member, so there are `h` of them. -/
theorem hcl_top [DecidableEq (Divisor Fq F ⧸ princ Fq F)] (hk : constField Fq F = ⊥) (hg : 2 ≤ genusF Fq F) :
    hcl Fq F (2 * genusF Fq F - 2) = Nat.card (Pic0 Fq F) := by
  obtain ⟨D1, hD1⟩ := exists_deg_one Fq F hk
  have h1 : 2 * (genusF Fq F : ℤ) - 1 ≤ ((2 * genusF Fq F - 1 : ℕ) : ℤ) := by omega
  rw [card_Pic0_eq_hcl hk h1]
  apply le_antisymm
  · exact hcl_le hk h1 ((-1 : ℤ) • D1) (by rw [deg_zsmul, hD1]; omega)
  · exact hcl_le' hk (by omega) D1 (by rw [hD1]; omega)

/-- Z2: `(q - 1) A_{2g-2} = h (q^(g-1) - 1) + q^g - q^(g-1)` for `g ≥ 1`, `h = #Pic⁰`. -/
theorem numEff_top' (hk : constField Fq F = ⊥) (hg : 1 ≤ genusF Fq F) :
    ((Fintype.card Fq : ℤ) - 1) * numEff Fq F (2 * genusF Fq F - 2) =
      Nat.card (Pic0 Fq F) * ((Fintype.card Fq : ℤ) ^ (genusF Fq F - 1) - 1) +
        ((Fintype.card Fq : ℤ) ^ genusF Fq F - (Fintype.card Fq : ℤ) ^ (genusF Fq F - 1)) := by
  classical
  obtain ⟨W, hW⟩ := exists_isCanonicalF (Fq := Fq) (F := F)
  rw [numEff_top hk hW hg]
  rcases Nat.lt_or_ge (genusF Fq F) 2 with h2 | h2
  · rw [show genusF Fq F - 1 = 0 by omega, pow_zero, sub_self, mul_zero, mul_zero]
  · rw [hcl_top hk h2]

/-- **Z2.** If `N_m = 1 + q^m - Σ c_i^m` for all `m ≥ 1` and `#c ≤ 2g`, then `#c = 2g`, `Π c_i = q^g`, and
`Π (1 - c_i X)` has integer coefficients. -/
theorem card_eq_two_genus (hk : constField Fq F = ⊥) (c : Multiset ℂ)
    (hc : ∀ m : ℕ, 1 ≤ m →
      (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum)
    (hcard : Multiset.card c ≤ 2 * genusF Fq F) :
    Multiset.card c = 2 * genusF Fq F ∧ c.prod = (Fintype.card Fq : ℂ) ^ genusF Fq F ∧
      ∃ L : ℤ[X], L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod := by
  classical
  have hP := prod_eq_zeta_F hk c hc
  have hL : ∃ L : ℤ[X], L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod :=
    exists_int_poly (fun k => (numEff Fq F k : ℤ)) (Fintype.card Fq : ℤ) c (by simpa using hP)
  rcases Nat.eq_zero_or_pos (genusF Fq F) with hg0 | hg1
  · have hc0 : c = 0 := Multiset.card_eq_zero.mp (by omega)
    subst hc0
    exact ⟨by simp [hg0], by simp [hg0], hL⟩
  have hq1 : 1 ≤ Fintype.card Fq := Fintype.card_pos
  have hp1 : ∀ e : ℕ, 1 ≤ Fintype.card Fq ^ e := fun e => Nat.one_le_pow _ _ Fintype.card_pos
  have hq : (Fintype.card Fq : ℂ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast (Fintype.one_lt_card (α := Fq)).ne')
  have key : ∀ n : ℕ, 2 * (genusF Fq F : ℤ) - 1 ≤ n →
      (numEff Fq F n : ℂ) * ((Fintype.card Fq : ℂ) - 1) =
        (Nat.card (Pic0 Fq F) : ℂ) * ((Fintype.card Fq : ℂ) ^ (n + 1 - genusF Fq F) - 1) := by
    intro n hn
    have h := congrArg (Nat.cast : ℕ → ℂ) (card_Pic0_mul hk hn)
    push_cast [Nat.cast_sub hq1, Nat.cast_sub (hp1 _)] at h
    exact h
  obtain ⟨g', hg'⟩ : ∃ g', genusF Fq F = g' + 1 := ⟨genusF Fq F - 1, by omega⟩
  have e2 := key (2 * g' + 1 + 1) (by omega)
  have e1 := key (2 * g' + 1) (by omega)
  have e0 := congrArg (Int.cast : ℤ → ℂ) (numEff_top' hk (by omega))
  rw [hg', show 2 * (g' + 1) - 2 = 2 * g' by omega, show g' + 1 - 1 = g' by omega] at e0
  rw [hg', show 2 * g' + 1 + 1 + 1 - (g' + 1) = g' + 2 by omega] at e2
  rw [hg', show 2 * g' + 1 + 1 - (g' + 1) = g' + 1 by omega] at e1
  push_cast at e0
  set p : ℂ[X] := (c.map fun r => 1 - Polynomial.C r * Polynomial.X).prod with hpdef
  have hcoef : p.coeff (2 * g' + 1 + 1) = (Fintype.card Fq : ℂ) ^ (g' + 1) := by
    have h2 := congrArg (PowerSeries.coeff (2 * g' + 1 + 1)) hP
    rw [← coe_prod_one_sub, ← hpdef, Polynomial.coeff_coe, coeff_succ_one_sub_mul, coeff_succ_one_sub_mul,
      coeff_succ_one_sub_mul] at h2
    simp only [PowerSeries.coeff_mk] at h2
    rw [h2]
    apply mul_left_cancel₀ hq
    linear_combination e2 - (1 + (Fintype.card Fq : ℂ)) * e1 + (Fintype.card Fq : ℂ) * e0
  have hpdeg : p.natDegree ≤ Multiset.card c := natDegree_prod_one_sub_le c
  have hcard' : Multiset.card c = 2 * genusF Fq F := by
    by_contra hne
    have hlt : p.natDegree < 2 * g' + 1 + 1 := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt] at hcoef
    exact (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) hcoef.symm
  refine ⟨hcard', ?_, hL⟩
  have h3 := coeff_card_prod_one_sub c
  have hev : (-1 : ℂ) ^ (2 * g' + 1 + 1) = 1 := Even.neg_one_pow ⟨g' + 1, by ring⟩
  rw [← hpdef, hcard', hg', show 2 * (g' + 1) = 2 * g' + 1 + 1 by ring, hcoef, hev, one_mul] at h3
  rw [hg', h3]

end Concrete

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CP4a_FE =====
section

/-!
# S4-CP4a, part a: RH equality, the functional equation, and traces of geometric Frobenius

* `zeta_RH_FE` (function fields with full constant field): the inverse zeta roots `c` (S3-ZetaSB `zeta_shape`)
  satisfy `#c = 2g`, `‖c_i‖ = √q` (RH equality, from `Π c_i = q^g` of CoreA `card_eq_two_genus`), `0 ∉ c`,
  `conj c = c`, the functional equation `{q / c_i} = {c_i}`, and `Π (X - c_i)` is the image of a monic `P0 ∈ ℤ[X]`.
* `det_mul_charpolyRev_of_mul_eq`: `G M = q` gives `det M · det(1 - X G) = (-1)^d · χ_M(q X)`.
* `exists_trace_pow_frob` (review R4): if `χ_M = P0`, `P0 = Π (X - c_i)` over `ℂ`, `{q / c_i} = {c_i}` and
  `G M = q` with `q` a unit, then `tr(M^(k+1))`, `tr(G^(k+1))` and `Σ c_i^(k+1)` are one integer `s k`.
  (`M` = arithmetic Frobenius `π` on `T_l`, `G = q π⁻¹` = geometric Frobenius on `H^1`.)
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

section Alg

/-- Nonnegative reals `≤ B` whose product is `B^#r` all equal `B`. -/
theorem eq_of_prod_eq_pow (B : ℝ) (hB : 0 < B) (r : Multiset ℝ) (h0 : ∀ x ∈ r, 0 ≤ x)
    (hle : ∀ x ∈ r, x ≤ B) :
    0 ≤ r.prod ∧ r.prod ≤ B ^ Multiset.card r ∧ (r.prod = B ^ Multiset.card r → ∀ x ∈ r, x = B) := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha0 := h0 a (Multiset.mem_cons_self a s)
    have haB := hle a (Multiset.mem_cons_self a s)
    obtain ⟨hs0, hsB, hseq⟩ := ih (fun x hx => h0 x (Multiset.mem_cons_of_mem hx))
      (fun x hx => hle x (Multiset.mem_cons_of_mem hx))
    have hBk : 0 < B ^ Multiset.card s := pow_pos hB _
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    refine ⟨mul_nonneg ha0 hs0, ?_, ?_⟩
    · calc a * s.prod ≤ B * B ^ Multiset.card s := mul_le_mul haB hsB hs0 hB.le
        _ = _ := mul_comm _ _
    · intro heq x hx
      have h1 : (B - a) * B ^ Multiset.card s + a * (B ^ Multiset.card s - s.prod) = 0 := by
        linear_combination -1 * heq
      have h2 : 0 ≤ (B - a) * B ^ Multiset.card s := mul_nonneg (by linarith) hBk.le
      have h3 : 0 ≤ a * (B ^ Multiset.card s - s.prod) := mul_nonneg ha0 (by linarith)
      have h4 : (B - a) * B ^ Multiset.card s = 0 := by linarith
      have haeq : a = B := by
        rcases mul_eq_zero.mp h4 with h | h
        · linarith
        · exact absurd h hBk.ne'
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact haeq
      · rw [haeq] at heq
        exact hseq (mul_left_cancel₀ hB.ne' (heq.trans (mul_comm _ _))) x hx

theorem norm_multiset_prod_eq (c : Multiset ℂ) : ‖c.prod‖ = (c.map (‖·‖)).prod := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

/-- RH equality: `‖c_i‖ ≤ B` and `‖Π c_i‖ = B^#c` force `‖c_i‖ = B`. -/
theorem norm_eq_of_norm_prod (c : Multiset ℂ) (B : ℝ) (hB : 0 < B) (hle : ∀ x ∈ c, ‖x‖ ≤ B)
    (hprod : ‖c.prod‖ = B ^ Multiset.card c) : ∀ x ∈ c, ‖x‖ = B := by
  have h := eq_of_prod_eq_pow B hB (c.map (‖·‖)) (fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg y)
    (fun x hx => by obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx; exact hle y hy)
  rw [Multiset.card_map, ← norm_multiset_prod_eq] at h
  exact fun x hx => h.2.2 hprod ‖x‖ (Multiset.mem_map_of_mem _ hx)

variable {K : Type*} [Field K]

theorem prod_one_sub_ne_zero (A : Multiset K) : (A.map fun a => 1 - Polynomial.C a * X).prod ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp [Polynomial.eval_multiset_prod] at this

theorem roots_prod_one_sub (A : Multiset K) (hA : (0 : K) ∉ A) :
    (A.map fun a => 1 - Polynomial.C a * X).prod.roots = A.map (·⁻¹) := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := fun h => hA (h ▸ Multiset.mem_cons_self a s)
    have hs : (0 : K) ∉ s := fun h => hA (Multiset.mem_cons_of_mem h)
    have hlin : (1 - Polynomial.C a * X : K[X]) = Polynomial.C (-a) * (X - Polynomial.C a⁻¹) := by
      have e : Polynomial.C (-a) * Polynomial.C a⁻¹ = (-1 : K[X]) := by
        rw [← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ ha, Polynomial.C_neg, Polynomial.C_1]
      rw [mul_sub, e, Polynomial.C_neg]
      ring
    have hne := prod_one_sub_ne_zero (a ::ₘ s)
    rw [Multiset.map_cons, Multiset.prod_cons] at hne ⊢
    rw [roots_mul hne, ih hs, hlin, roots_C_mul _ (neg_ne_zero.mpr ha), roots_X_sub_C, Multiset.map_cons,
      Multiset.singleton_add]

/-- `Π (1 - a X) = Π (1 - b X)` with no zero roots forces `A = B`. -/
theorem multiset_eq_of_prod_one_sub_eq (A B : Multiset K) (hA : (0 : K) ∉ A) (hB : (0 : K) ∉ B)
    (h : (A.map fun a => 1 - Polynomial.C a * X).prod = (B.map fun a => 1 - Polynomial.C a * X).prod) :
    A = B := by
  have h1 := congrArg Polynomial.roots h
  rw [roots_prod_one_sub A hA, roots_prod_one_sub B hB] at h1
  have h2 := congrArg (Multiset.map (·⁻¹)) h1
  simpa [Multiset.map_map, Function.comp_def] using h2

/-- `reflect` is an involution at a fixed degree bound. -/
theorem reflect_reflect {R : Type*} [Semiring R] (N : ℕ) (f : R[X]) : (f.reflect N).reflect N = f := by
  ext i
  rw [coeff_reflect, coeff_reflect, revAt_invol]

/-- `X^d Π (1/X - c_i) = Π (1 - c_i X)`, `d = #c`. -/
theorem reflect_prod_X_sub_C {R : Type*} [CommRing R] [IsDomain R] (c : Multiset R) :
    ((c.map fun r => X - Polynomial.C r).prod).reflect (Multiset.card c) =
      (c.map fun r => 1 - Polynomial.C r * X).prod := by
  induction c using Multiset.induction_on with
  | empty => simp [reflect_one]
  | cons a s ih =>
    have h1 : reflect 1 (X - Polynomial.C a : R[X]) = 1 - Polynomial.C a * X := by
      rw [reflect_sub, reflect_C, ← pow_one (X : R[X]), reflect_monomial]
      simp
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
      reflect_mul _ _ (natDegree_X_sub_C_le a) (natDegree_multiset_prod_X_sub_C_eq_card s).le, h1, ih,
      Multiset.map_cons, Multiset.prod_cons]

/-- Functional equation as a polynomial identity: if `{q / c_i} = {c_i}` and `0 ∉ c`, then
`Π (q X - c_i) = (Π (-c_i)) · Π (1 - c_i X)`. -/
theorem comp_prod_X_sub_C (c : Multiset K) (q : K) (h0 : (0 : K) ∉ c) :
    (c.map fun r => X - Polynomial.C r).prod.comp (Polynomial.C q * X) =
      Polynomial.C (c.map fun r => -r).prod *
        ((c.map fun x => q / x).map fun r => 1 - Polynomial.C r * X).prod := by
  induction c using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ≠ 0 := fun h => h0 (h ▸ Multiset.mem_cons_self a s)
    have hs : (0 : K) ∉ s := fun h => h0 (Multiset.mem_cons_of_mem h)
    have key : (Polynomial.C q * X - Polynomial.C a : K[X]) =
        Polynomial.C (-a) * (1 - Polynomial.C (q / a) * X) := by
      rw [mul_sub, mul_one, ← mul_assoc, ← Polynomial.C_mul]
      have : -a * (q / a) = -q := by field_simp
      rw [this, Polynomial.C_neg, Polynomial.C_neg]
      ring
    simp only [Multiset.map_cons, Multiset.prod_cons, mul_comp, sub_comp, X_comp, C_comp]
    rw [ih hs, key, Polynomial.C_mul]
    ring

theorem fe_comp (c : Multiset K) (q : K) (h0 : (0 : K) ∉ c) (hfe : c.map (fun x => q / x) = c) :
    (c.map fun r => X - Polynomial.C r).prod.comp (Polynomial.C q * X) =
      Polynomial.C ((c.map fun r => X - Polynomial.C r).prod.coeff 0) *
        (c.map fun r => 1 - Polynomial.C r * X).prod := by
  rw [comp_prod_X_sub_C c q h0, hfe, coeff_zero_eq_eval_zero, eval_multiset_prod]
  simp [Multiset.map_map, Function.comp_def]

/-- Complex roots of a real (integer) polynomial `Π (1 - c_i X)` are conjugation-stable. -/
theorem conj_stable (c : Multiset ℂ) (L : ℤ[X])
    (hL : L.map (Int.castRingHom ℂ) = (c.map fun r => 1 - Polynomial.C r * X).prod) (h0 : (0 : ℂ) ∉ c) :
    c.map (starRingEnd ℂ) = c := by
  have h := congrArg (Polynomial.map (starRingEnd ℂ)) hL
  rw [Polynomial.map_map, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ)) (Int.castRingHom ℂ), hL,
    Polynomial.map_multiset_prod, Multiset.map_map] at h
  have h' : (c.map fun r => 1 - Polynomial.C r * X).prod =
      ((c.map (starRingEnd ℂ)).map fun r => 1 - Polynomial.C r * X).prod := by
    rw [h, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp
  refine (multiset_eq_of_prod_one_sub_eq c _ h0 ?_ h').symm
  intro hm
  obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.mp hm
  exact h0 ((map_eq_zero _).mp hy0 ▸ hy)

/-- With `‖c_i‖ = √q` and conjugation-stable roots, `{q / c_i} = {c_i}`. -/
theorem fe_of_norm (c : Multiset ℂ) (q : ℝ) (hq : 0 < q) (hnorm : ∀ x ∈ c, ‖x‖ = Real.sqrt q)
    (hconj : c.map (starRingEnd ℂ) = c) : c.map (fun x => (q : ℂ) / x) = c := by
  conv_rhs => rw [← hconj]
  apply Multiset.map_congr rfl
  intro x hx
  have hx0 : x ≠ 0 := by
    intro h
    have := hnorm x hx
    rw [h, norm_zero] at this
    exact (Real.sqrt_pos.mpr hq).ne' this.symm
  have h2 : (starRingEnd ℂ) x * x = (q : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm x hx, Real.sq_sqrt hq.le]
  rw [div_eq_iff hx0]
  exact h2.symm

end Alg

section Mat

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- `G M = q` gives `det M · det(1 - X G) = (-1)^d χ_M(q X)`. -/
theorem det_mul_charpolyRev_of_mul_eq (M G : Matrix n n R) (q : R) (hGM : G * M = q • 1) :
    Polynomial.C M.det * G.charpolyRev =
      (-1) ^ Fintype.card n * M.charpoly.comp (Polynomial.C q * X) := by
  have e1 : (1 - (X : R[X]) • G.map Polynomial.C) * M.map Polynomial.C =
      -((Polynomial.C q * X) • (1 : Matrix n n R[X]) - M.map Polynomial.C) := by
    rw [sub_mul, one_mul, smul_mul_assoc, ← Matrix.map_mul, hGM]
    ext i j : 1
    by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring
  have e2 : M.charpoly.comp (Polynomial.C q * X) =
      det ((Polynomial.C q * X) • (1 : Matrix n n R[X]) - M.map Polynomial.C) := by
    change Polynomial.compRingHom (Polynomial.C q * X) (det (charmatrix M)) = _
    rw [RingHom.map_det]
    congr 1
    ext i j : 1
    by_cases h : i = j <;> simp [h, charmatrix_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [e2, ← det_neg, ← e1, det_mul, charpolyRev, mul_comm, ← RingHom.mapMatrix_apply, RingHom.map_det]
  rfl

/-- **Trace of geometric Frobenius (R4).** Let `χ_M = P0` with `P0 ∈ ℤ[X]` monic, `P0 = Π (X - c_i)` over `ℂ`,
`0 ∉ c`, `{q / c_i} = {c_i}`, and `G M = q` with `q` a unit. Then `d = #c` and `tr(M^(k+1))`, `tr(G^(k+1))`,
`Σ c_i^(k+1)` are the images of one integer `s k`. -/
theorem exists_trace_pow_frob [Nontrivial R] (M G : Matrix n n R) (q0 : ℕ) (hGM : G * M = (q0 : R) • 1)
    (hq : IsUnit (q0 : R)) (P0 : ℤ[X]) (hP0 : P0.Monic) (c : Multiset ℂ)
    (hc : P0.map (Int.castRingHom ℂ) = (c.map fun r => X - Polynomial.C r).prod)
    (hM : M.charpoly = P0.map (Int.castRingHom R)) (h0 : (0 : ℂ) ∉ c)
    (hfe : c.map (fun x => (q0 : ℂ) / x) = c) :
    Fintype.card n = Multiset.card c ∧ ∃ s : ℕ → ℤ, ∀ k : ℕ, trace (M ^ (k + 1)) = (s k : R) ∧
      trace (G ^ (k + 1)) = (s k : R) ∧ (c.map (· ^ (k + 1))).sum = (s k : ℂ) := by
  classical
  have hdeg : P0.natDegree = Multiset.card c := by
    have := congrArg Polynomial.natDegree hc
    rwa [hP0.natDegree_map, natDegree_multiset_prod_X_sub_C_eq_card] at this
  have hn : Fintype.card n = Multiset.card c := by
    rw [← charpoly_natDegree_eq_dim M, hM, hP0.natDegree_map, hdeg]
  have hL0 : (P0.reflect (Multiset.card c)).coeff 0 = 1 := by
    rw [coeff_reflect, revAt_zero, ← hdeg]
    exact hP0
  have hLM : M.charpolyRev = (P0.reflect (Multiset.card c)).map (Int.castRingHom R) := by
    rw [← reverse_charpoly, hM, Polynomial.reverse, hP0.natDegree_map, hdeg, reflect_map]
  have hLc : (P0.reflect (Multiset.card c)).map (Int.castRingHom ℂ) =
      (c.map fun r => 1 - Polynomial.C r * X).prod := by
    rw [← reflect_map, hc, reflect_prod_X_sub_C]
  have hdetM : IsUnit M.det := by
    have h := congrArg Matrix.det hGM
    rw [det_mul, det_smul, det_one, mul_one] at h
    exact isUnit_of_mul_isUnit_right (h ▸ hq.pow _)
  have hdet : M.det = (-1) ^ Fintype.card n * ((P0.coeff 0 : ℤ) : R) := by
    rw [det_eq_sign_charpoly_coeff, hM, coeff_map, eq_intCast]
  have hFEint : P0.comp (Polynomial.C (q0 : ℤ) * X) =
      Polynomial.C (P0.coeff 0) * P0.reflect (Multiset.card c) := by
    apply Polynomial.map_injective (Int.castRingHom ℂ) (RingHom.injective_int _)
    have h1 : ((P0.coeff 0 : ℤ) : ℂ) = ((c.map fun r => X - Polynomial.C r).prod).coeff 0 := by
      rw [← hc, coeff_map, eq_intCast]
    rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X, hLc, hc]
    simp only [eq_intCast, Int.cast_natCast]
    rw [h1]
    exact fe_comp c (q0 : ℂ) h0 hfe
  have hcomp : M.charpoly.comp (Polynomial.C (q0 : R) * X) =
      Polynomial.C ((P0.coeff 0 : ℤ) : R) * (P0.reflect (Multiset.card c)).map (Int.castRingHom R) := by
    have h := congrArg (Polynomial.map (Int.castRingHom R)) hFEint
    rw [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X] at h
    simp only [eq_intCast, Int.cast_natCast] at h
    rw [hM, h]
  have hLG : G.charpolyRev = (P0.reflect (Multiset.card c)).map (Int.castRingHom R) := by
    apply (Polynomial.isUnit_C.mpr hdetM).mul_left_cancel
    rw [det_mul_charpolyRev_of_mul_eq M G _ hGM, hcomp, hdet, Polynomial.C_mul, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_1]
    ring
  obtain ⟨s, hs⟩ := exists_trace_pow_eq_sum_pow M _ c hL0 hLM hLc
  obtain ⟨s', hs'⟩ := exists_trace_pow_eq_sum_pow G _ c hL0 hLG hLc
  have hss : s = s' := funext fun k => by
    have := (hs k).2.symm.trans (hs' k).2
    exact_mod_cast this
  subst hss
  exact ⟨hn, s, fun k => ⟨(hs k).1, (hs' k).1, (hs k).2⟩⟩

end Mat

section Concrete

open Places RR ZetaSB

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **RH equality + functional equation** for a function field with full constant field: the inverse zeta roots
`c` have `#c = 2g`, `‖c_i‖ = √q`, `Π c_i = q^g`, `N_m = 1 + q^m - Σ c_i^m`, `0 ∉ c`, `conj c = c`,
`{q / c_i} = {c_i}`, and `Π (X - c_i)` is the image of a monic integer polynomial. -/
theorem zeta_RH_FE (hk : constField Fq F = ⊥) :
    ∃ c : Multiset ℂ, Multiset.card c = 2 * genusF Fq F ∧
      (∀ x ∈ c, ‖x‖ = Real.sqrt (Fintype.card Fq)) ∧ c.prod = (Fintype.card Fq : ℂ) ^ genusF Fq F ∧
      (∀ m : ℕ, 1 ≤ m →
        (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) ∧
      (0 : ℂ) ∉ c ∧ c.map (starRingEnd ℂ) = c ∧ c.map (fun x => (Fintype.card Fq : ℂ) / x) = c ∧
      ∃ P0 : ℤ[X], P0.Monic ∧ P0.map (Int.castRingHom ℂ) = (c.map fun r => X - Polynomial.C r).prod := by
  obtain ⟨c, hcard, hle, hN⟩ := ZetaSB.zeta_shape Fq F hk
  obtain ⟨hcard2, hprod, L, hL⟩ := CoreA.card_eq_two_genus hk c hN hcard
  have hq : (0 : ℝ) < Fintype.card Fq := by exact_mod_cast Fintype.card_pos
  have hsq : 0 < Real.sqrt (Fintype.card Fq) := Real.sqrt_pos.mpr hq
  have hnorm : ∀ x ∈ c, ‖x‖ = Real.sqrt (Fintype.card Fq) := by
    refine norm_eq_of_norm_prod c _ hsq hle ?_
    rw [hprod, hcard2, norm_pow, Complex.norm_natCast, pow_mul, Real.sq_sqrt hq.le]
  have h0 : (0 : ℂ) ∉ c := by
    intro h
    have := hnorm 0 h
    rw [norm_zero] at this
    exact hsq.ne' this.symm
  have hconj := conj_stable c L hL h0
  have hfe : c.map (fun x => (Fintype.card Fq : ℂ) / x) = c := by
    have := fe_of_norm c (Fintype.card Fq) hq hnorm hconj
    simpa using this
  refine ⟨c, hcard2, hnorm, hprod, hN, h0, hconj, hfe, L.reflect (Multiset.card c), ?_, ?_⟩
  · have hmap : (L.reflect (Multiset.card c)).map (Int.castRingHom ℂ) =
        (c.map fun r => X - Polynomial.C r).prod := by
      rw [← reflect_map, hL, ← reflect_prod_X_sub_C, reflect_reflect]
    refine Polynomial.monic_of_injective (RingHom.injective_int (Int.castRingHom ℂ)) ?_
    rw [hmap]
    exact monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  · rw [← reflect_map, hL, ← reflect_prod_X_sub_C, reflect_reflect]

end Concrete

end RamanujanPetersson.CP4a

end

-- ===== S4.Def_RP_CoreA_Ord =====
section

/-!
# S4-CoreA part O1: the l-part of the order of an automorphism of an elementary abelian l-group

`V` finite with `l • V = 0`, `T` bijective additive, `#V = l ^ D`. Then some `N ≥ 1` has `T^[N] = id` and
`v_l(N) ≤ ⌈log_l D⌉` (`Nat.clog l D`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

open Polynomial

theorem exists_pow_eq_one_padicValNat_le {l : ℕ} [hl : Fact l.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod l) V] [Finite V] [Nontrivial V] (f : Module.End (ZMod l) V) (hT : Function.Bijective f) {D : ℕ}
    (hD : Nat.card V = l ^ D) :
    ∃ N : ℕ, 0 < N ∧ f ^ N = 1 ∧ padicValNat l N ≤ Nat.clog l D := by
  classical
  have hfu : IsUnit f := (Module.End.isUnit_iff f).mpr hT
  have : Finite (Module.End (ZMod l) V) :=
    Finite.of_injective (fun g : Module.End (ZMod l) V => (g : V → V)) DFunLike.coe_injective
  have : Finite (Module.End (ZMod l) V)ˣ := Finite.of_injective Units.val Units.val_injective
  have : CharP (Module.End (ZMod l) V) l := charP_of_injective_algebraMap' (ZMod l) l
  set u := hfu.unit with hu
  set n := Nat.card (Module.End (ZMod l) V)ˣ with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, M, hM, hnM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 l hl.out.ne_one
  have hM0 : M ≠ 0 := by rintro rfl; exact hM (dvd_zero l)
  have hun : u ^ n = 1 := pow_card_eq_one'
  set U : Module.End (ZMod l) V := f ^ M with hU
  have hUa : U ^ (l ^ a) = 1 := by
    have h1 : ((u ^ n : (Module.End (ZMod l) V)ˣ) : Module.End (ZMod l) V) = 1 := by rw [hun]; rfl
    rw [Units.val_pow_eq_pow_val, hnM] at h1
    rw [hU, ← pow_mul, mul_comm]
    simpa [hu] using h1
  have hnil : IsNilpotent (U - 1) := by
    refine ⟨l ^ a, ?_⟩
    rw [sub_pow_char_pow_of_commute l a (Commute.one_right U), hUa, one_pow, sub_self]
  have : Module.Finite (ZMod l) V := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod l) V = D := by
    let _ : Fintype V := Fintype.ofFinite V
    have hc : Fintype.card V = Fintype.card (ZMod l) ^ Module.finrank (ZMod l) V := Module.card_eq_pow_finrank
    rw [← Nat.card_eq_fintype_card, hD, ZMod.card] at hc
    exact (Nat.pow_right_injective hl.out.two_le hc).symm
  have hzero : (U - 1) ^ D = 0 := by
    have hch := IsNilpotent.charpoly_eq_X_pow_finrank hnil
    have hcay := LinearMap.aeval_self_charpoly (U - 1)
    rw [hch, hfin, map_pow, aeval_X] at hcay
    exact hcay
  set k := Nat.clog l D with hk
  have hDk : D ≤ l ^ k := Nat.le_pow_clog hl.out.one_lt D
  have hUk : U ^ (l ^ k) = 1 := by
    have h0 : (U - 1) ^ (l ^ k) = 0 := pow_eq_zero_of_le hDk hzero
    rw [sub_pow_char_pow_of_commute l k (Commute.one_right U), one_pow] at h0
    exact sub_eq_zero.mp h0
  refine ⟨M * l ^ k, Nat.mul_pos (Nat.pos_of_ne_zero hM0) (pow_pos hl.out.pos k), ?_, ?_⟩
  · rw [pow_mul, ← hU, hUk]
  · rw [padicValNat.mul hM0 (pow_ne_zero _ hl.out.ne_zero), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hM, zero_add]

/-- **O1.** `V` finite with `l • V = 0`, `T` bijective additive, `#V = l ^ D`: some `N ≥ 1` has `T^[N] = id` and
`v_l(N) ≤ ⌈log_l D⌉`. -/
theorem exists_iterate_eq_id_padicValNat_le {l : ℕ} [hl : Fact l.Prime] {V : Type*} [AddCommGroup V] [Finite V]
    (hV : ∀ x : V, l • x = 0) (T : V →+ V) (hT : Function.Bijective T) {D : ℕ} (hD : Nat.card V = l ^ D) :
    ∃ N : ℕ, 0 < N ∧ (∀ x, T^[N] x = x) ∧ padicValNat l N ≤ Nat.clog l D := by
  rcases subsingleton_or_nontrivial V with hs | hnt
  · exact ⟨1, Nat.one_pos, fun x => Subsingleton.elim _ _, by simp⟩
  let _ : Module (ZMod l) V := AddCommGroup.zmodModule hV
  obtain ⟨N, hN, hpow, hval⟩ := exists_pow_eq_one_padicValNat_le (T.toZModLinearMap l) hT hD
  refine ⟨N, hN, fun x => ?_, hval⟩
  have h := LinearMap.congr_fun hpow x
  rw [Module.End.pow_apply, Module.End.one_apply] at h
  exact h

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CoreA_Fin =====
section

/-!
# S4-CoreA part F1: `A[l]` is finite

`pi : A →+ A` with every point periodic, `#Fix(pi^m) = l ^ nu m` for `m ≥ 1`, and
`nu m ≤ C + e * v_l(m)`. Then `A[l]` is finite (with an explicit bound).
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

/-- Growth helper: `t * t ≤ 4 * 2 ^ t`. -/
theorem sq_le_four_mul_two_pow (t : ℕ) : t * t ≤ 4 * 2 ^ t := by
  induction t with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num
    · rw [pow_succ]
      nlinarith

/-- Absorption: `D ≤ C + e * ⌈log_l D⌉` forces `D ≤ C + e * (8 * (C + e) + 2)`. -/
theorem le_of_le_add_mul_clog {l : ℕ} (hl : 2 ≤ l) {C e D : ℕ} (h : D ≤ C + e * Nat.clog l D) :
    D ≤ C + e * (8 * (C + e) + 2) := by
  set k := Nat.clog l D with hk
  suffices hk' : k ≤ 8 * (C + e) + 2 by
    calc D ≤ C + e * k := h
      _ ≤ C + e * (8 * (C + e) + 2) := by gcongr
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · omega
  have hD : 1 < D := by
    by_contra hD
    have : k = 0 := Nat.clog_of_right_le_one (by omega) l
    omega
  have hlt : l ^ (k - 1) < D := by
    have := Nat.pow_pred_clog_lt_self (b := l) (by omega) hD
    rwa [← hk, Nat.pred_eq_sub_one] at this
  have h2l : 2 ^ (k - 1) ≤ l ^ (k - 1) := Nat.pow_le_pow_left hl _
  have hsq := sq_le_four_mul_two_pow (k - 1)
  clear_value k
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlt h2l hsq
  by_contra hcon
  rw [not_le] at hcon
  nlinarith

variable {A : Type*} [AddCommGroup A]

/-- Finite sets of `l`-torsion points have bounded size. -/
theorem card_le_of_torsion {l : ℕ} [hl : Fact l.Prime] (pi : A →+ A) (nu : ℕ → ℕ) (C e : ℕ)
    (hper : ∀ x : A, ∃ m, 0 < m ∧ pi^[m] x = x)
    (hfix : ∀ m, 0 < m → Nat.card {x : A // pi^[m] x = x} = l ^ nu m)
    (hnu : ∀ m, 0 < m → nu m ≤ C + e * padicValNat l m) (S : Finset A) (hS : ∀ x ∈ S, l • x = 0) :
    S.card ≤ l ^ (C + e * (8 * (C + e) + 2)) := by
  classical
  choose m hm0 hm using hper
  set N0 := ∏ x ∈ S, m x with hN0
  have hN0pos : 0 < N0 := Finset.prod_pos fun x _ => hm0 x
  have hSfix : ∀ x ∈ S, pi^[N0] x = x := fun x hx =>
    Function.IsPeriodicPt.trans_dvd (f := pi) (hm x) (Finset.dvd_prod_of_mem m hx)
  let V : AddSubgroup A :=
    { carrier := {v | l • v = 0 ∧ pi^[N0] v = v}
      add_mem' := fun {a b} ha hb =>
        ⟨by rw [smul_add, ha.1, hb.1, add_zero], by rw [iterate_map_add, ha.2, hb.2]⟩
      zero_mem' := ⟨smul_zero _, iterate_map_zero pi N0⟩
      neg_mem' := fun {a} ha => by
        refine ⟨by rw [smul_neg, ha.1, neg_zero], ?_⟩
        have h0 : pi^[N0] (-a) + pi^[N0] a = 0 := by
          rw [← iterate_map_add, neg_add_cancel, iterate_map_zero]
        rw [ha.2] at h0
        exact eq_neg_of_add_eq_zero_left h0 }
  have hmemV : ∀ v, v ∈ V ↔ l • v = 0 ∧ pi^[N0] v = v := fun v => Iff.rfl
  have hVpi : ∀ v ∈ V, pi v ∈ V := fun v hv => by
    rw [hmemV] at hv ⊢
    refine ⟨by rw [← map_nsmul, hv.1, map_zero], ?_⟩
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hv.2]
  let T : V →+ V := (pi.comp V.subtype).codRestrict V (fun v => hVpi v.1 v.2)
  have hTcoe : ∀ (n : ℕ) (v : V), ((T^[n] v : V) : A) = pi^[n] (v : A) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  have hTN0 : ∀ v : V, T^[N0] v = v := fun v => Subtype.ext (by rw [hTcoe]; exact v.2.2)
  have hTbij : Function.Bijective T := by
    obtain ⟨n, hn⟩ : ∃ n, N0 = n + 1 := ⟨N0 - 1, by omega⟩
    refine ⟨fun a b hab => ?_, fun v => ⟨T^[n] v, ?_⟩⟩
    · have := congrArg (T^[n]) hab
      rwa [← Function.iterate_succ_apply, ← Function.iterate_succ_apply, Nat.succ_eq_add_one, ← hn, hTN0,
        hTN0] at this
    · rw [← Function.iterate_succ_apply' T n v, Nat.succ_eq_add_one, ← hn, hTN0]
  have hfixN0 : Nat.card {x : A // pi^[N0] x = x} ≠ 0 := by
    rw [hfix N0 hN0pos]; exact pow_ne_zero _ hl.out.ne_zero
  have : Finite {x : A // pi^[N0] x = x} := Nat.finite_of_card_ne_zero hfixN0
  have : Finite V := Finite.of_injective (fun v : V => (⟨v.1, v.2.2⟩ : {x : A // pi^[N0] x = x}))
    (fun a b h => Subtype.ext (Subtype.mk.inj h))
  have hVl : ∀ v : V, l • v = 0 := fun v => Subtype.ext (by simpa using v.2.1)
  let _ : Module (ZMod l) V := AddCommGroup.zmodModule hVl
  have : Module.Finite (ZMod l) V := Module.Finite.of_finite
  set D := Module.finrank (ZMod l) V with hDdef
  have hcardV : Nat.card V = l ^ D := by
    let _ : Fintype V := Fintype.ofFinite V
    have hc : Fintype.card V = Fintype.card (ZMod l) ^ Module.finrank (ZMod l) V := Module.card_eq_pow_finrank
    rw [← Nat.card_eq_fintype_card, ZMod.card] at hc
    exact hc
  obtain ⟨N, hN, hTN, hval⟩ := exists_iterate_eq_id_padicValNat_le hVl T hTbij hcardV
  have hfixN : Nat.card {x : A // pi^[N] x = x} ≠ 0 := by
    rw [hfix N hN]; exact pow_ne_zero _ hl.out.ne_zero
  have : Finite {x : A // pi^[N] x = x} := Nat.finite_of_card_ne_zero hfixN
  have hVle : Nat.card V ≤ Nat.card {x : A // pi^[N] x = x} :=
    Nat.card_le_card_of_injective (fun v : V => (⟨v.1, by rw [← hTcoe, hTN]⟩ : {x : A // pi^[N] x = x}))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  rw [hcardV, hfix N hN] at hVle
  have hDnu : D ≤ nu N := (Nat.pow_le_pow_iff_right hl.out.one_lt).mp hVle
  have hDb : D ≤ C + e * (8 * (C + e) + 2) := by
    refine le_of_le_add_mul_clog hl.out.two_le ?_
    calc D ≤ nu N := hDnu
      _ ≤ C + e * padicValNat l N := hnu N hN
      _ ≤ C + e * Nat.clog l D := by gcongr
  have hSV : S.card ≤ Nat.card V := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_le_card_of_injective (fun x : S => (⟨x.1, (hmemV _).mpr ⟨hS x.1 x.2, hSfix x.1 x.2⟩⟩ : V))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  calc S.card ≤ Nat.card V := hSV
    _ = l ^ D := hcardV
    _ ≤ l ^ (C + e * (8 * (C + e) + 2)) := Nat.pow_le_pow_right hl.out.pos hDb

/-- **F1.** Under periodicity, the fixed-point counts `l ^ nu m` and the bound `nu m ≤ C + e v_l(m)`,
the `l`-torsion `A[l]` is finite. -/
theorem finite_torsion_of_fix_card {l : ℕ} [hl : Fact l.Prime] (pi : A →+ A) (nu : ℕ → ℕ) (C e : ℕ)
    (hper : ∀ x : A, ∃ m, 0 < m ∧ pi^[m] x = x)
    (hfix : ∀ m, 0 < m → Nat.card {x : A // pi^[m] x = x} = l ^ nu m)
    (hnu : ∀ m, 0 < m → nu m ≤ C + e * padicValNat l m) :
    {x : A | l • x = 0}.Finite := by
  by_contra hinf
  obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (l ^ (C + e * (8 * (C + e) + 2)) + 1)
  have := card_le_of_torsion pi nu C e hper hfix hnu t (fun x hx => hts hx)
  omega

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CoreA_Val =====
section

/-!
# S4-CoreA part V1: norms of `x ^ n - 1` in an ultrametric normed field

`K` a normed field with an ultrametric norm, `l` prime with `0 < ‖l‖ < 1`.
* `norm_pow_sub_one_eq`: `‖x - 1‖ < ‖n‖ → ‖x ^ n - 1‖ = ‖n‖ ‖x - 1‖`.
* `exists_norm_pow_sub_one_eq`: for `β` with no `β ^ N = 1` (`N ≥ 1`) and some `‖β ^ M - 1‖ < 1`, there are
  `d0 ≥ 1`, `r > 0` with `‖β ^ (d0 n) - 1‖ = r ‖n‖` for all `n ≥ 1` and `r ‖N‖ ≤ ‖β ^ N - 1‖` for all `N ≥ 1`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

open Finset

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_eq_one_of_norm_sub_one_lt_one {x : K} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  have hx : x = (x - 1) + 1 := by ring
  have hne : ‖x - 1‖ ≠ ‖(1 : K)‖ := by rw [norm_one]; exact h.ne
  rw [hx, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_right h.le]

theorem norm_geom_sum_le_one {x : K} (hx : ‖x‖ = 1) (n : ℕ) : ‖∑ i ∈ range n, x ^ i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun i _ => by rw [norm_pow, hx, one_pow])

theorem norm_pow_sub_one_le {x : K} (hx : ‖x‖ = 1) (n : ℕ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  rw [← geom_sum_mul, norm_mul]
  calc ‖∑ i ∈ range n, x ^ i‖ * ‖x - 1‖ ≤ 1 * ‖x - 1‖ :=
        mul_le_mul_of_nonneg_right (norm_geom_sum_le_one hx n) (norm_nonneg _)
    _ = ‖x - 1‖ := one_mul _

omit [IsUltrametricDist K] in
theorem geom_sum_eq_natCast_add (x : K) (n : ℕ) :
    ∑ i ∈ range n, x ^ i = (n : K) + ∑ i ∈ range n, (x ^ i - 1) := by
  rw [sum_sub_distrib]; simp

theorem norm_geom_sum_sub_le {x : K} (hx : ‖x‖ = 1) (n : ℕ) :
    ‖∑ i ∈ range n, (x ^ i - 1)‖ ≤ ‖x - 1‖ :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    (fun i _ => norm_pow_sub_one_le hx i)

/-- `‖x - 1‖ < ‖n‖` gives `‖x ^ n - 1‖ = ‖n‖ ‖x - 1‖`. -/
theorem norm_pow_sub_one_eq {x : K} {n : ℕ} (h : ‖x - 1‖ < ‖(n : K)‖) :
    ‖x ^ n - 1‖ = ‖(n : K)‖ * ‖x - 1‖ := by
  have hn1 : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
  have hx : ‖x‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one (lt_of_lt_of_le h hn1)
  have hT := lt_of_le_of_lt (norm_geom_sum_sub_le hx n) h
  have hS : ‖∑ i ∈ range n, x ^ i‖ = ‖(n : K)‖ := by
    rw [geom_sum_eq_natCast_add, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hT.ne',
      max_eq_left hT.le]
  rw [← geom_sum_mul, norm_mul, hS]

theorem norm_pow_sub_one_le_mul_max {x : K} (h : ‖x - 1‖ < 1) (n : ℕ) :
    ‖x ^ n - 1‖ ≤ ‖x - 1‖ * max ‖(n : K)‖ ‖x - 1‖ := by
  have hx := norm_eq_one_of_norm_sub_one_lt_one h
  rw [← geom_sum_mul, norm_mul, mul_comm, geom_sum_eq_natCast_add]
  exact mul_le_mul_of_nonneg_left
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl (norm_geom_sum_sub_le hx n)))
    (norm_nonneg _)

theorem norm_natCast_eq_one_of_not_dvd {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {n : ℕ}
    (hn : ¬ l ∣ n) : ‖(n : K)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one K n) (not_lt.mp fun hlt => ?_)
  obtain ⟨u, v, huv⟩ : IsCoprime (l : ℤ) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (hl.coprime_iff_not_dvd.mpr hn)
  have h1 : (u : K) * (l : K) + (v : K) * (n : K) = 1 := by
    have := congrArg (Int.cast : ℤ → K) huv
    push_cast at this
    exact this
  have hlt1 : ‖(u : K) * (l : K) + (v : K) * (n : K)‖ < 1 := by
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one K u)
        (norm_nonneg _) hl1
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (IsUltrametricDist.norm_intCast_le_one K v)
        (norm_nonneg _) hlt
  rw [h1, norm_one] at hlt1
  exact lt_irrefl _ hlt1

theorem norm_natCast_eq_pow_padicValNat {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) {N : ℕ} (hN : N ≠ 0) :
    ‖(N : K)‖ = ‖(l : K)‖ ^ padicValNat l N := by
  have := Fact.mk hl
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.ne_one
  have hn0 : n' ≠ 0 := by rintro rfl; exact hn' (dvd_zero l)
  rw [padicValNat.mul (pow_ne_zero _ hl.ne_zero) hn0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hn', add_zero, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow,
    norm_natCast_eq_one_of_not_dvd hl hl1 hn', mul_one]

theorem norm_pow_prime_pow_sub_one {l : ℕ} {z : K} (hz : ‖z - 1‖ < ‖(l : K)‖) (a : ℕ) :
    ‖z ^ (l ^ a) - 1‖ = ‖(l : K)‖ ^ a * ‖z - 1‖ := by
  have hl1 : ‖(l : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K l
  induction a with
  | zero => simp
  | succ a ih =>
    have hlt : ‖z ^ (l ^ a) - 1‖ < ‖(l : K)‖ := by
      rw [ih]
      calc ‖(l : K)‖ ^ a * ‖z - 1‖ ≤ 1 * ‖z - 1‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hl1) (norm_nonneg _)
        _ < ‖(l : K)‖ := by rw [one_mul]; exact hz
    rw [pow_succ l a, pow_mul, norm_pow_sub_one_eq hlt, ih, pow_succ ‖(l : K)‖ a]
    ring

/-- **V1.** -/
theorem exists_norm_pow_sub_one_eq {l : ℕ} (hl : l.Prime) (hl0 : (l : K) ≠ 0) (hl1 : ‖(l : K)‖ < 1) {β : K}
    (hβ : ∀ N : ℕ, 0 < N → β ^ N ≠ 1) {M : ℕ} (hM : 0 < M) (hM1 : ‖β ^ M - 1‖ < 1) :
    ∃ d0 : ℕ, 0 < d0 ∧ ∃ r : ℝ, 0 < r ∧ (∀ n : ℕ, 0 < n → ‖β ^ (d0 * n) - 1‖ = r * ‖(n : K)‖) ∧
      (∀ N : ℕ, 0 < N → r * ‖(N : K)‖ ≤ ‖β ^ N - 1‖) := by
  obtain ⟨x, hx⟩ : ∃ x, x = β ^ M := ⟨_, rfl⟩
  rw [← hx] at hM1
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = max ‖(l : K)‖ ‖x - 1‖ := ⟨_, rfl⟩
  have hρ1 : ρ < 1 := hρ ▸ max_lt hl1 hM1
  have hρ0 : 0 ≤ ρ := hρ ▸ le_max_of_le_left (norm_nonneg _)
  have hrj : ∀ j : ℕ, ‖x ^ (l ^ j) - 1‖ ≤ ρ ^ j * ‖x - 1‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hle : ‖x ^ (l ^ j) - 1‖ ≤ ‖x - 1‖ :=
        ih.trans (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hρ0 hρ1.le))
      have hlt1 : ‖x ^ (l ^ j) - 1‖ < 1 := lt_of_le_of_lt hle hM1
      calc ‖x ^ (l ^ (j + 1)) - 1‖ = ‖(x ^ (l ^ j)) ^ l - 1‖ := by rw [pow_succ l j, pow_mul]
        _ ≤ ‖x ^ (l ^ j) - 1‖ * max ‖(l : K)‖ ‖x ^ (l ^ j) - 1‖ := norm_pow_sub_one_le_mul_max hlt1 l
        _ ≤ (ρ ^ j * ‖x - 1‖) * ρ :=
            mul_le_mul ih (hρ ▸ max_le_max le_rfl hle) (le_max_of_le_left (norm_nonneg _))
              (mul_nonneg (pow_nonneg hρ0 j) (norm_nonneg _))
        _ = ρ ^ (j + 1) * ‖x - 1‖ := by ring
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hl0) hρ1
  obtain ⟨d0, hd0def⟩ : ∃ d0, d0 = M * l ^ J := ⟨_, rfl⟩
  have hd0 : 0 < d0 := hd0def ▸ Nat.mul_pos hM (pow_pos hl.pos J)
  have hz : β ^ d0 = x ^ (l ^ J) := by rw [hd0def, pow_mul, hx]
  have hzlt : ‖β ^ d0 - 1‖ < ‖(l : K)‖ := by
    rw [hz]
    calc ‖x ^ (l ^ J) - 1‖ ≤ ρ ^ J * ‖x - 1‖ := hrj J
      _ ≤ ρ ^ J := mul_le_of_le_one_right (pow_nonneg hρ0 J) hM1.le
      _ < ‖(l : K)‖ := hJ
  have hzpos : 0 < ‖β ^ d0 - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hβ d0 hd0))
  have key : ∀ n : ℕ, 0 < n → ‖(β ^ d0) ^ n - 1‖ = ‖β ^ d0 - 1‖ * ‖(n : K)‖ := by
    intro n hn
    obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.ne_one
    have hn'1 : ‖(n' : K)‖ = 1 := norm_natCast_eq_one_of_not_dvd hl hl1 hn'
    have ha := norm_pow_prime_pow_sub_one hzlt a
    have hlt : ‖(β ^ d0) ^ (l ^ a) - 1‖ < ‖(n' : K)‖ := by
      rw [ha, hn'1]
      calc ‖(l : K)‖ ^ a * ‖β ^ d0 - 1‖ ≤ 1 * ‖β ^ d0 - 1‖ :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hl1.le) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hzlt.trans hl1
    rw [pow_mul, norm_pow_sub_one_eq hlt, ha, hn'1, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow, hn'1]
    ring
  have hβ1 : ‖β‖ = 1 := by
    have h1 : ‖β ^ M‖ = 1 := norm_eq_one_of_norm_sub_one_lt_one (hx ▸ hM1)
    rw [norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hM.ne').mp h1
  refine ⟨d0, hd0, ‖β ^ d0 - 1‖, hzpos, fun n hn => by rw [pow_mul]; exact key n hn, fun N hN => ?_⟩
  have e1 : (β ^ N) ^ d0 = (β ^ d0) ^ N := by rw [← pow_mul, ← pow_mul, mul_comm]
  calc ‖β ^ d0 - 1‖ * ‖(N : K)‖ = ‖(β ^ N) ^ d0 - 1‖ := by rw [e1, key N hN]
    _ ≤ ‖β ^ N - 1‖ := norm_pow_sub_one_le (by rw [norm_pow, hβ1, one_pow]) d0

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CoreA_Div =====
section

/-!
# S4-CoreA part S1: the divisible part of an `l`-primary group with finite `A[l]`

`A` with every element killed by a power of `l` and `A[l]` finite. There is `k0` with
`l^k0 A = l^(k0+j) A` for all `j`; `D := l^k0 A` is divisible, `A = A[l^k0] + D`, `A ⧸ D` is finite,
every `A[l^k]` is finite, and `A[l] ⊆ D` forces `D = A`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

/-- `x ↦ n • x` as an additive endomorphism. -/
def smulHom (A : Type*) [AddCommGroup A] (n : ℕ) : A →+ A where
  toFun x := n • x
  map_zero' := smul_zero n
  map_add' x y := smul_add n x y

variable {A : Type*} [AddCommGroup A]

@[simp] theorem smulHom_apply (n : ℕ) (x : A) : smulHom A n x = n • x := rfl

theorem mem_range_smulHom {n : ℕ} {x : A} : x ∈ (smulHom A n).range ↔ ∃ a, n • a = x := by
  rw [AddMonoidHom.mem_range]; rfl

/-- Every `A[l^k]` is finite. -/
theorem finite_torsion_pow {l : ℕ} (hfin : {x : A | l • x = 0}.Finite) (k : ℕ) :
    {x : A | l ^ k • x = 0}.Finite := by
  induction k with
  | zero => exact Set.Finite.subset (Set.finite_singleton 0) (fun x hx => by simpa using hx)
  | succ k ih =>
    have hpre : {x : A | l ^ (k + 1) • x = 0} = (fun x : A => l • x) ⁻¹' {x : A | l ^ k • x = 0} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_preimage, pow_succ, mul_smul]
    rw [hpre]
    refine Set.Finite.preimage' ih (fun b _ => ?_)
    rcases (((fun x : A => l • x) ⁻¹' {b}).eq_empty_or_nonempty) with h | ⟨x0, hx0⟩
    · rw [h]; exact Set.finite_empty
    · refine Set.Finite.subset (hfin.image (fun t => x0 + t)) (fun x hx => ⟨x - x0, ?_, by abel⟩)
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx0
      simp only [Set.mem_setOf_eq, smul_sub, hx, hx0, sub_self]

/-- The chain `A[l] ∩ l^k A` stabilizes. -/
theorem exists_stable_torsion {l : ℕ} (hfin : {x : A | l • x = 0}.Finite) :
    ∃ k0 : ℕ, ∀ j : ℕ, ∀ y : A, l • y = 0 → (∃ a, l ^ k0 • a = y) → ∃ b, l ^ (k0 + j) • b = y := by
  let S : ℕ → Set A := fun k => {y | l • y = 0} ∩ {y | ∃ a, l ^ k • a = y}
  have hSfin : ∀ k, (S k).Finite := fun k => hfin.subset Set.inter_subset_left
  have hanti : ∀ k j, S (k + j) ⊆ S k := fun k j y ⟨hy, a, ha⟩ =>
    ⟨hy, l ^ j • a, by rw [← ha, smul_smul, ← pow_add, add_comm]⟩
  obtain ⟨k0, hk0⟩ : ∃ k0, (S k0).ncard = sInf (Set.range fun k => (S k).ncard) :=
    Nat.sInf_mem (Set.range_nonempty _)
  refine ⟨k0, fun j y hy hya => ?_⟩
  have hle : (S k0).ncard ≤ (S (k0 + j)).ncard := by
    rw [hk0]; exact Nat.sInf_le ⟨k0 + j, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le (hanti k0 j) hle (hSfin k0)
  have hmem : y ∈ S (k0 + j) := by rw [heq]; exact ⟨hy, hya⟩
  exact hmem.2

/-- `pi` maps `l^k A` into itself. -/
theorem map_mem_range_smulHom (pi : A →+ A) {n : ℕ} {x : A} (hx : x ∈ (smulHom A n).range) :
    pi x ∈ (smulHom A n).range := by
  obtain ⟨a, rfl⟩ := mem_range_smulHom.mp hx
  exact mem_range_smulHom.mpr ⟨pi a, (map_nsmul pi n a).symm⟩

section Stable

variable {l k0 : ℕ}
  (hk0 : ∀ j : ℕ, ∀ y : A, l • y = 0 → (∃ a, l ^ k0 • a = y) → ∃ b, l ^ (k0 + j) • b = y)
include hk0

/-- `l^k0 A ⊆ l^(k0+1) A` on elements killed by `l^m`. -/
theorem range_subset_succ (m : ℕ) : ∀ x : A, l ^ m • x = 0 → (∃ a, l ^ k0 • a = x) →
    ∃ b, l ^ (k0 + 1) • b = x := by
  induction m with
  | zero =>
    intro x hx _
    refine ⟨0, ?_⟩
    rw [pow_zero, one_smul] at hx
    rw [hx, smul_zero]
  | succ m ih =>
    intro x hx ⟨a, ha⟩
    have hy : l • (l ^ m • x) = 0 := by rw [smul_smul, ← pow_succ']; exact hx
    obtain ⟨c, hc⟩ := hk0 (m + 1) (l ^ m • x) hy ⟨l ^ m • a, by rw [← ha, smul_smul, smul_smul, mul_comm]⟩
    obtain ⟨b, hb⟩ := ih (x - l ^ (k0 + 1) • c)
      (by rw [smul_sub, smul_smul, ← pow_add, show m + (k0 + 1) = k0 + (m + 1) by ring, hc, sub_self])
      ⟨a - l • c, by rw [smul_sub, smul_smul, ← pow_succ, ha]⟩
    exact ⟨b + c, by rw [smul_add, hb, sub_add_cancel]⟩

variable (htors : ∀ x : A, ∃ k, l ^ k • x = 0)
include htors

theorem range_subset_add (j : ℕ) (x : A) (hx : ∃ a, l ^ k0 • a = x) : ∃ b, l ^ (k0 + j) • b = x := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    obtain ⟨b, hb⟩ := ih
    obtain ⟨m, hm⟩ := htors (l ^ k0 • b)
    obtain ⟨c, hc⟩ := range_subset_succ hk0 m (l ^ k0 • b) hm ⟨b, rfl⟩
    refine ⟨c, ?_⟩
    rw [← hb, show k0 + (j + 1) = j + (k0 + 1) by ring, pow_add, mul_smul, hc, ← mul_smul, ← pow_add,
      show j + k0 = k0 + j by ring]

/-- `D = l^k0 A` is divisible (by every `l^m`). -/
theorem divisible (m : ℕ) (y : A) (hy : y ∈ (smulHom A (l ^ k0)).range) :
    ∃ z ∈ (smulHom A (l ^ k0)).range, l ^ m • z = y := by
  obtain ⟨c, hc⟩ := range_subset_add hk0 htors m y (mem_range_smulHom.mp hy)
  exact ⟨l ^ k0 • c, mem_range_smulHom.mpr ⟨c, rfl⟩, by
    rw [← hc, smul_smul, ← pow_add, show m + k0 = k0 + m by ring]⟩

/-- `A = A[l^k0] + D`. -/
theorem decomp (x : A) : ∃ t d, l ^ k0 • t = 0 ∧ d ∈ (smulHom A (l ^ k0)).range ∧ x = t + d := by
  obtain ⟨c, hc⟩ := range_subset_add hk0 htors k0 (l ^ k0 • x) ⟨x, rfl⟩
  exact ⟨x - l ^ k0 • c, l ^ k0 • c, by rw [smul_sub, smul_smul, ← pow_add, hc, sub_self],
    mem_range_smulHom.mpr ⟨c, rfl⟩, (sub_add_cancel _ _).symm⟩

/-- `A ⧸ D` is finite. -/
theorem finite_quotient (hfin : {x : A | l • x = 0}.Finite) : Finite (A ⧸ (smulHom A (l ^ k0)).range) := by
  have : Finite {x : A | l ^ k0 • x = 0} := (finite_torsion_pow hfin k0).to_subtype
  refine Finite.of_surjective
    (fun t : {x : A | l ^ k0 • x = 0} => (QuotientAddGroup.mk (t : A) : A ⧸ (smulHom A (l ^ k0)).range)) ?_
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨t, d, ht, hd, rfl⟩ := decomp hk0 htors x
  exact ⟨⟨t, ht⟩, QuotientAddGroup.eq.mpr (by rwa [neg_add_cancel_left])⟩

/-- `A[l] ⊆ D` forces `D = A`. -/
theorem mem_of_torsion_le (hsub : ∀ x : A, l • x = 0 → x ∈ (smulHom A (l ^ k0)).range) (x : A) :
    x ∈ (smulHom A (l ^ k0)).range := by
  obtain ⟨m, hm⟩ := htors x
  induction m generalizing x with
  | zero =>
    rw [pow_zero, one_smul] at hm
    rw [hm]; exact AddSubgroup.zero_mem _
  | succ m ih =>
    have h1 : l • (l ^ m • x) = 0 := by rw [smul_smul, ← pow_succ']; exact hm
    obtain ⟨z, hz, hzx⟩ := divisible hk0 htors m (l ^ m • x) (hsub _ h1)
    have hxz := ih (x - z) (by rw [smul_sub, hzx, sub_self])
    have hx : x = (x - z) + z := (sub_add_cancel x z).symm
    rw [hx]
    exact AddSubgroup.add_mem _ hxz hz

end Stable

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CoreA_Basis =====
section

/-!
# S4-CoreA part S2a: compatible bases of `G[l^N]` for a divisible `l`-primary group

`G` divisible by `l` with `#G[l] = l ^ s`. A basis `b1` of `G[l]` (integer coordinates) lifts to compatible
families `tateBasis N` (`l • tateBasis (N+1) = tateBasis N`, `tateBasis 0 = 0`, `tateBasis 1 = b1`), and
`c ↦ ∑ c i • tateBasis N i` maps `ℤ ^ s` onto `G[l^N]` with kernel `l^N ℤ ^ s`. Also: compatible integer
sequences have `l`-adic limits.
-/

set_option autoImplicit false

namespace RamanujanPetersson.CoreA

section Lift

variable {l : ℕ} [hl : Fact l.Prime]

/-- A compatible integer sequence has an `l`-adic limit. -/
theorem exists_padicInt_compat (a : ℕ → ℤ) (ha : ∀ N, ((l ^ N : ℕ) : ℤ) ∣ a (N + 1) - a N) :
    ∃ z : ℤ_[l], ∀ N, PadicInt.toZModPow N z = (a N : ZMod (l ^ N)) := by
  have hchain : ∀ k j, ((l ^ k : ℕ) : ℤ) ∣ a (k + j) - a k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : ((l ^ k : ℕ) : ℤ) ∣ ((l ^ (k + j) : ℕ) : ℤ) := by
        exact_mod_cast pow_dvd_pow l (Nat.le_add_right k j)
      have e : a (k + (j + 1)) - a k = (a (k + j) - a k) + (a (k + j + 1) - a (k + j)) := by
        rw [show k + (j + 1) = k + j + 1 by ring]; ring
      rw [e]
      exact dvd_add ih (h1.trans (ha (k + j)))
  let f : ∀ k : ℕ, Polynomial ℤ →+* ZMod (l ^ k) := fun k =>
    Polynomial.eval₂RingHom (Int.castRingHom _) (a k : ZMod (l ^ k))
  have hf : ∀ (k1 k2 : ℕ) (hk : k1 ≤ k2),
      (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1))).comp (f k2) = f k1 := by
    intro k1 k2 hk
    apply Polynomial.ringHom_ext
    · intro c
      exact RingHom.congr_fun (RingHom.ext_int
        (((ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k1))).comp (f k2)).comp Polynomial.C)
        ((f k1).comp Polynomial.C)) c
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [RingHom.comp_apply, ZMod.castHom_apply]
      simp only [f, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rw [ZMod.cast_intCast (pow_dvd_pow l hk)]
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (dvd_sub_comm.mp (hchain k1 j))
  refine ⟨PadicInt.lift hf Polynomial.X, fun N => ?_⟩
  have := congrArg (fun g => g Polynomial.X) (PadicInt.lift_spec hf N)
  simpa [f] using this

end Lift

variable {G : Type*} [AddCommGroup G] {l : ℕ}

/-- Compatible lifts of a family `b1` along multiplication by `l`. -/
noncomputable def tateBasis (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) : ℕ → Fin s → G
  | 0 => 0
  | 1 => b1
  | (N + 2) => fun i => Classical.choose (hdiv (tateBasis hdiv b1 (N + 1) i))

section Basis

variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G)

theorem tateBasis_one : tateBasis hdiv b1 1 = b1 := rfl

theorem tateBasis_succ (hb1 : ∀ i, l • b1 i = 0) (N : ℕ) (i : Fin s) :
    l • tateBasis hdiv b1 (N + 1) i = tateBasis hdiv b1 N i := by
  cases N with
  | zero => exact hb1 i
  | succ N =>
    show l • Classical.choose (hdiv (tateBasis hdiv b1 (N + 1) i)) = _
    exact Classical.choose_spec (hdiv _)

theorem tateBasis_pow_smul (hb1 : ∀ i, l • b1 i = 0) (N k : ℕ) (i : Fin s) :
    l ^ N • tateBasis hdiv b1 (N + k) i = tateBasis hdiv b1 k i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show N + 1 + k = (N + k) + 1 by ring, pow_succ, mul_smul, tateBasis_succ hdiv b1 hb1, ih]

theorem tateBasis_pow_smul_self (hb1 : ∀ i, l • b1 i = 0) (N : ℕ) (i : Fin s) :
    l ^ N • tateBasis hdiv b1 N i = 0 := by
  have := tateBasis_pow_smul hdiv b1 hb1 N 0 i
  rw [add_zero] at this
  rw [this]; rfl

variable (hb1 : ∀ i, l • b1 i = 0)
  (h1inj : ∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i)
  (h1span : ∀ x : G, l • x = 0 → ∃ d : Fin s → ℤ, ∑ i, d i • b1 i = x)

include hb1 in
theorem smul_sum_tateBasis_succ (N : ℕ) (c : Fin s → ℤ) :
    l • ∑ i, c i • tateBasis hdiv b1 (N + 1) i = ∑ i, c i • tateBasis hdiv b1 N i := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_comm, tateBasis_succ hdiv b1 hb1]

include hb1 h1inj in
/-- Kernel of the integer coordinates at level `N` is `l^N ℤ^s`. -/
theorem dvd_of_sum_tateBasis_eq_zero (N : ℕ) (c : Fin s → ℤ)
    (hc : ∑ i, c i • tateBasis hdiv b1 N i = 0) (i : Fin s) : ((l ^ N : ℕ) : ℤ) ∣ c i := by
  induction N generalizing c i with
  | zero => simp
  | succ N ih =>
    have h0 : ∑ i, c i • tateBasis hdiv b1 N i = 0 := by
      rw [← smul_sum_tateBasis_succ hdiv b1 hb1, hc, smul_zero]
    have hd : ∀ j, ∃ d : ℤ, c j = ((l ^ N : ℕ) : ℤ) * d := fun j => ih c h0 j
    choose d hd using hd
    have h1 : ∑ i, d i • b1 i = 0 := by
      rw [← hc]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hd j, mul_comm, mul_smul, natCast_zsmul, show N + 1 = N + 1 from rfl,
        tateBasis_pow_smul hdiv b1 hb1 N 1 j, tateBasis_one]
    obtain ⟨e, he⟩ := h1inj d h1 i
    rw [hd i, he, pow_succ]
    exact ⟨e, by push_cast; ring⟩

include hb1 h1span in
/-- The integer coordinates at level `N` reach all of `G[l^N]`. -/
theorem exists_sum_tateBasis_eq (N : ℕ) (x : G) (hx : l ^ N • x = 0) :
    ∃ c : Fin s → ℤ, ∑ i, c i • tateBasis hdiv b1 N i = x := by
  induction N generalizing x with
  | zero =>
    rw [pow_zero, one_smul] at hx
    exact ⟨0, by simp [hx]⟩
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih (l • x) (by rw [smul_smul, ← pow_succ]; exact hx)
    obtain ⟨d, hd⟩ := h1span (x - ∑ i, c i • tateBasis hdiv b1 (N + 1) i)
      (by rw [smul_sub, smul_sum_tateBasis_succ hdiv b1 hb1, hc, sub_self])
    refine ⟨fun i => c i + ((l ^ N : ℕ) : ℤ) * d i, ?_⟩
    have e : ∀ i, (c i + ((l ^ N : ℕ) : ℤ) * d i) • tateBasis hdiv b1 (N + 1) i =
        c i • tateBasis hdiv b1 (N + 1) i + d i • b1 i := by
      intro i
      rw [add_smul, mul_comm, mul_smul, natCast_zsmul, tateBasis_pow_smul hdiv b1 hb1 N 1 i, tateBasis_one]
    simp only [e, Finset.sum_add_distrib, hd]
    abel

end Basis

/-- An elementary abelian `l`-group of order `l ^ s` has an integer-coordinate basis. -/
theorem exists_basis_aux [hl : Fact l.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod l) V] [Finite V] {s : ℕ}
    (hs : Nat.card V = l ^ s) :
    ∃ b : Fin s → V, (∀ d : Fin s → ℤ, ∑ i, d i • b i = 0 → ∀ i, (l : ℤ) ∣ d i) ∧
      (∀ x : V, ∃ d : Fin s → ℤ, ∑ i, d i • b i = x) := by
  classical
  have : Module.Finite (ZMod l) V := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod l) V = s := by
    let _ : Fintype V := Fintype.ofFinite V
    have hc : Fintype.card V = Fintype.card (ZMod l) ^ Module.finrank (ZMod l) V := Module.card_eq_pow_finrank
    rw [← Nat.card_eq_fintype_card, hs, ZMod.card] at hc
    exact (Nat.pow_right_injective hl.out.two_le hc).symm
  let B := Module.finBasisOfFinrankEq (ZMod l) V hfr
  have hz : ∀ d : Fin s → ℤ, ∑ i, ((d i : ZMod l)) • B i = ∑ i, d i • B i := fun d =>
    Finset.sum_congr rfl (fun i _ => Int.cast_smul_eq_zsmul _ _ _)
  refine ⟨fun i => B i, fun d hd i => ?_, fun x => ?_⟩
  · have h0 : ∑ i, ((d i : ZMod l)) • B i = 0 := by rw [hz]; exact hd
    have := Fintype.linearIndependent_iff.mp B.linearIndependent (fun i => (d i : ZMod l)) h0 i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  · refine ⟨fun i => ((B.repr x i).val : ℤ), ?_⟩
    rw [← hz]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (B.sum_repr x)
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- A basis of `G[l]` in integer coordinates. -/
theorem exists_level_one_basis [hl : Fact l.Prime] {s : ℕ} (hs : Nat.card (smulHom G l).ker = l ^ s) :
    ∃ b1 : Fin s → G, (∀ i, l • b1 i = 0) ∧
      (∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i) ∧
      (∀ x : G, l • x = 0 → ∃ d : Fin s → ℤ, ∑ i, d i • b1 i = x) := by
  classical
  have hmemT : ∀ x : G, x ∈ (smulHom G l).ker ↔ l • x = 0 := fun x => by
    rw [AddMonoidHom.mem_ker, smulHom_apply]
  have hT : ∀ x : (smulHom G l).ker, l • x = 0 := fun x => Subtype.ext (by
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact (hmemT _).mp x.2)
  have : Finite (smulHom G l).ker :=
    Nat.finite_of_card_ne_zero (by rw [hs]; exact pow_ne_zero _ hl.out.ne_zero)
  let _ : Module (ZMod l) (smulHom G l).ker := AddCommGroup.zmodModule hT
  obtain ⟨b, hinj, hspan⟩ := exists_basis_aux hs
  have hcoe : ∀ d : Fin s → ℤ, ((∑ i, d i • b i : (smulHom G l).ker) : G) = ∑ i, d i • (b i : G) := by
    intro d
    rw [AddSubgroup.val_finsetSum]
    exact Finset.sum_congr rfl (fun i _ => AddSubgroup.coe_zsmul _ _ _)
  refine ⟨fun i => (b i : G), fun i => (hmemT _).mp (b i).2, fun d hd i => ?_, fun x hx => ?_⟩
  · exact hinj d (Subtype.ext (by rw [hcoe]; exact hd)) i
  · obtain ⟨d, hd⟩ := hspan ⟨x, (hmemT x).mpr hx⟩
    exact ⟨d, by rw [← hcoe, hd]⟩

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_CoreA_Tate =====
section

/-!
# S4-CoreA part S2b: the Tate module coordinates and the matrix of an endomorphism

With `tateBasis` from S2a, `tateMap N : (Fin s → ZMod (l^N)) →+ G` is injective with range `G[l^N]`.
Every additive endomorphism `φ` of `G` has a unique matrix `M` over `ℤ_[l]` with
`φ (tateMap N c) = tateMap N (M.map (toZModPow N) *ᵥ c)` for all `N` (`IsTateMat`); this is compatible with
`1`, products, differences and powers.
-/

set_option autoImplicit false

open scoped Matrix

namespace RamanujanPetersson.CoreA

variable {G : Type*} [AddCommGroup G] {l : ℕ}

section Tate

variable (hdiv : ∀ y : G, ∃ z, l • z = y) {s : ℕ} (b1 : Fin s → G) (hb1 : ∀ i, l • b1 i = 0)

/-- Coordinates at level `N`: `c ↦ ∑ c i • tateBasis N i`. -/
noncomputable def tateMap (N : ℕ) : (Fin s → ZMod (l ^ N)) →+ G :=
  ∑ i, (ZMod.lift (l ^ N) ⟨zmultiplesHom G (tateBasis hdiv b1 N i), by
      rw [zmultiplesHom_apply, natCast_zsmul, tateBasis_pow_smul_self hdiv b1 hb1 N i]⟩).comp
    (Pi.evalAddMonoidHom (fun _ : Fin s => ZMod (l ^ N)) i)

theorem tateMap_intCast (N : ℕ) (c : Fin s → ℤ) :
    tateMap hdiv b1 hb1 N (fun i => (c i : ZMod (l ^ N))) = ∑ i, c i • tateBasis hdiv b1 N i := by
  simp [tateMap, AddMonoidHom.finsetSum_apply]

theorem exists_intCast {N : ℕ} (cb : Fin s → ZMod (l ^ N)) :
    ∃ c : Fin s → ℤ, cb = fun i => (c i : ZMod (l ^ N)) :=
  ⟨fun i => (cb i).cast, funext fun i => (ZMod.intCast_zmod_cast _).symm⟩

theorem tateMap_smul_eq_zero (N : ℕ) (cb : Fin s → ZMod (l ^ N)) : l ^ N • tateMap hdiv b1 hb1 N cb = 0 := by
  obtain ⟨c, rfl⟩ := exists_intCast cb
  rw [tateMap_intCast, Finset.smul_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [smul_comm, tateBasis_pow_smul_self hdiv b1 hb1, smul_zero]

variable (h1inj : ∀ d : Fin s → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i)
  (h1span : ∀ x : G, l • x = 0 → ∃ d : Fin s → ℤ, ∑ i, d i • b1 i = x)

include h1inj in
theorem tateMap_injective (N : ℕ) : Function.Injective (tateMap hdiv b1 hb1 N) := by
  refine (injective_iff_map_eq_zero _).mpr (fun cb hcb => ?_)
  obtain ⟨c, rfl⟩ := exists_intCast cb
  rw [tateMap_intCast] at hcb
  funext i
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_of_sum_tateBasis_eq_zero hdiv b1 hb1 h1inj N c hcb i)

include h1span in
theorem exists_tateMap_eq (N : ℕ) (x : G) (hx : l ^ N • x = 0) : ∃ cb, tateMap hdiv b1 hb1 N cb = x := by
  obtain ⟨c, hc⟩ := exists_sum_tateBasis_eq hdiv b1 hb1 h1span N x hx
  exact ⟨fun i => (c i : ZMod (l ^ N)), by rw [tateMap_intCast, hc]⟩

variable [Fact l.Prime]

/-- `M` is the matrix of `φ` on the Tate module. -/
def IsTateMat (φ : AddMonoid.End G) (M : Matrix (Fin s) (Fin s) ℤ_[l]) : Prop :=
  ∀ N (cb : Fin s → ZMod (l ^ N)),
    φ (tateMap hdiv b1 hb1 N cb) = tateMap hdiv b1 hb1 N (M.map (PadicInt.toZModPow N) *ᵥ cb)

include h1inj h1span in
theorem exists_isTateMat (φ : AddMonoid.End G) :
    ∃ M : Matrix (Fin s) (Fin s) ℤ_[l], IsTateMat hdiv b1 hb1 φ M := by
  have hφ : ∀ N j, l ^ N • φ (tateBasis hdiv b1 N j) = 0 := fun N j => by
    rw [← map_nsmul, tateBasis_pow_smul_self hdiv b1 hb1, map_zero]
  choose col hcol using fun N j => exists_sum_tateBasis_eq hdiv b1 hb1 h1span N _ (hφ N j)
  have hcompat : ∀ i j N, ((l ^ N : ℕ) : ℤ) ∣ col (N + 1) j i - col N j i := by
    intro i j N
    have h0 : ∑ i, (col (N + 1) j i - col N j i) • tateBasis hdiv b1 N i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← smul_sum_tateBasis_succ hdiv b1 hb1 N (col (N + 1) j), hcol (N + 1) j, hcol N j, ← map_nsmul,
        tateBasis_succ hdiv b1 hb1, sub_self]
    exact dvd_of_sum_tateBasis_eq_zero hdiv b1 hb1 h1inj N _ h0 i
  choose M hM using fun i j => exists_padicInt_compat (l := l) (fun N => col N j i) (hcompat i j)
  refine ⟨Matrix.of M, fun N cb => ?_⟩
  obtain ⟨c, rfl⟩ := exists_intCast cb
  have hv : (Matrix.of M).map (PadicInt.toZModPow N) *ᵥ (fun j => (c j : ZMod (l ^ N))) =
      fun i => ((∑ j, col N j i * c j : ℤ) : ZMod (l ^ N)) := by
    ext i
    simp [Matrix.mulVec, dotProduct, hM]
  rw [hv, tateMap_intCast, tateMap_intCast, map_sum]
  simp only [map_zsmul, ← hcol N, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [mul_comm]))

include h1inj in
theorem IsTateMat.unique {φ : AddMonoid.End G} {M M' : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (h' : IsTateMat hdiv b1 hb1 φ M') : M = M' := by
  ext i j
  rw [← PadicInt.ext_of_toZModPow]
  intro N
  have e := tateMap_injective hdiv b1 hb1 h1inj N ((h N (Pi.single j 1)).symm.trans (h' N (Pi.single j 1)))
  have := congrFun e i
  simpa [Matrix.mulVec_single_one] using this

theorem isTateMat_one : IsTateMat hdiv b1 hb1 (1 : AddMonoid.End G) (1 : Matrix (Fin s) (Fin s) ℤ_[l]) := by
  intro N cb
  have e : (1 : Matrix (Fin s) (Fin s) ℤ_[l]).map (PadicInt.toZModPow N) = 1 :=
    (PadicInt.toZModPow (p := l) N).mapMatrix.map_one
  rw [e, Matrix.one_mulVec]
  rfl

theorem IsTateMat.mul {φ χ : AddMonoid.End G} {M M' : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (h' : IsTateMat hdiv b1 hb1 χ M') :
    IsTateMat hdiv b1 hb1 (φ * χ) (M * M') := by
  intro N cb
  show φ (χ _) = _
  rw [h', h, Matrix.mulVec_mulVec, Matrix.map_mul]

theorem IsTateMat.sub {φ χ : AddMonoid.End G} {M M' : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (h' : IsTateMat hdiv b1 hb1 χ M') :
    IsTateMat hdiv b1 hb1 (φ - χ) (M - M') := by
  intro N cb
  have e : (M - M').map (PadicInt.toZModPow N) = M.map (PadicInt.toZModPow N) - M'.map (PadicInt.toZModPow N) :=
    (PadicInt.toZModPow (p := l) N).mapMatrix.map_sub M M'
  show φ _ - χ _ = _
  rw [h, h', e, Matrix.sub_mulVec, map_sub]

theorem IsTateMat.pow {φ : AddMonoid.End G} {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (n : ℕ) : IsTateMat hdiv b1 hb1 (φ ^ n) (M ^ n) := by
  induction n with
  | zero => simpa using isTateMat_one hdiv b1 hb1
  | succ n ih => simpa [pow_succ] using ih.mul hdiv b1 hb1 h

theorem IsTateMat.one_sub_pow {φ : AddMonoid.End G} {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (h : IsTateMat hdiv b1 hb1 φ M) (n : ℕ) : IsTateMat hdiv b1 hb1 (1 - φ ^ n) (1 - M ^ n) :=
  (isTateMat_one hdiv b1 hb1).sub hdiv b1 hb1 (h.pow hdiv b1 hb1 n)

end Tate

end RamanujanPetersson.CoreA

end

-- ===== S4.Def_RP_PicDescent_C2 =====
section

/-!
# S4-PicDescent, part C2: class numbers of the constant field extensions, `h_n = L_n(1)`

`F_n = Fc Fq F Ω n` over `L_n = Lc Fq Ω n` (`Ω` algebraically closed, `#L_n = q ^ n`).
* `numPoints_Fc`: `N_k(F_n) = N_{nk}(F)`.
* `classNumber_Fc`: for any multiset `c` with `N_m(F) = 1 + q^m - Σ c_i^m` (`m ≥ 1`),
  `#Pic⁰(F_n) = Π (1 - c_i ^ n)`.
* `Lpoly c n = Π (1 - c_i^n t)`, the `L`-polynomial of `F_n`; `classNumber_Fc_zeta`: with the zeta multiset of
  `F` (`|c_i| ≤ √q`, at most `2g` roots), `h_n = #Pic⁰(F_n) = L_n(1) = Π (1 - c_i ^ n)` for every `n ≥ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Polynomial

/-- `L_n(t) = Π_i (1 - c_i^n t)`. -/
noncomputable def Lpoly (c : Multiset ℂ) (n : ℕ) : ℂ[X] := (c.map fun z => 1 - C (z ^ n) * X).prod

theorem eval_one_Lpoly (c : Multiset ℂ) (n : ℕ) :
    (Lpoly c n).eval 1 = (c.map fun z => 1 - z ^ n).prod := by
  rw [Lpoly, eval_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun z _ => by simp

section ClassNumber

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω] [IsAlgClosed Ω]

theorem card_Lc_fintype (n : ℕ) [NeZero n] :
    Fintype.card (Lc Fq Ω n) = Fintype.card Fq ^ n := by
  rw [← Nat.card_eq_fintype_card, card_Lc Fq Ω (NeZero.ne n)]

/-- `N_k(F_n) = N_{nk}(F)`. -/
theorem numPoints_Fc (hk : Places.constField Fq F = ⊥) (n : ℕ) [NeZero n] {k : ℕ} (hk0 : k ≠ 0) :
    Places.numPoints (Lc Fq Ω n) (Fc Fq F Ω n) k = Places.numPoints Fq F (n * k) := by
  rw [numPoints_constExt (isConstExt_Fc Fq F Ω hk n) hk0, finrank_Lc Fq Ω (NeZero.ne n)]

variable {Fq F}

/-- The point counts of `F_n` in terms of a multiset `c` describing those of `F`. -/
theorem numPoints_Fc_formula (hk : Places.constField Fq F = ⊥) (c : Multiset ℂ)
    (hc : ∀ m : ℕ, 1 ≤ m →
      (Places.numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum)
    (n : ℕ) [NeZero n] (m : ℕ) (hm : 1 ≤ m) :
    (Places.numPoints (Lc Fq Ω n) (Fc Fq F Ω n) m : ℂ) =
      1 + (Fintype.card (Lc Fq Ω n) : ℂ) ^ m - ((c.map (· ^ n)).map (· ^ m)).sum := by
  have e1 : c.map (· ^ (n * m)) = (c.map (· ^ n)).map (· ^ m) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun z _ => pow_mul z n m
  rw [numPoints_Fc Fq F Ω hk n (by omega),
    hc (n * m) (Nat.one_le_iff_ne_zero.2 (mul_ne_zero (NeZero.ne n) (by omega))),
    card_Lc_fintype Fq Ω n, e1]
  push_cast
  ring

/-- **Class numbers of the constant field extensions**: `#Pic⁰(F_n) = Π (1 - c_i ^ n)`. -/
theorem classNumber_Fc (hk : Places.constField Fq F = ⊥) (c : Multiset ℂ)
    (hc : ∀ m : ℕ, 1 ≤ m →
      (Places.numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum)
    (n : ℕ) [NeZero n] :
    (Nat.card (Pic0 (Lc Fq Ω n) (Fc Fq F Ω n)) : ℂ) = (c.map fun z => 1 - z ^ n).prod := by
  rw [classNumber_eq_prod (constField_Fc Fq F Ω hk n) (c.map (· ^ n))
    (numPoints_Fc_formula Ω hk c hc n), Multiset.map_map]
  rfl

/-- **`h_n = L_n(1) = Π (1 - ω_i ^ n)`** for all constant field extensions `F_n`, with the zeta multiset
`ω` of `F` (`|ω_i| ≤ √q`, at most `2g` of them, `N_m(F) = 1 + q^m - Σ ω_i^m`); `Pic⁰(F_n)` is finite and
`N_m(F_n) = 1 + (q^n)^m - Σ (ω_i^n)^m`. -/
theorem classNumber_Fc_zeta (hk : Places.constField Fq F = ⊥) :
    ∃ c : Multiset ℂ, Multiset.card c ≤ 2 * RR.genusF Fq F ∧
      (∀ x ∈ c, ‖x‖ ≤ Real.sqrt (Fintype.card Fq)) ∧
      (∀ m : ℕ, 1 ≤ m →
        (Places.numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) ∧
      ∀ (n : ℕ) [NeZero n], Finite (Pic0 (Lc Fq Ω n) (Fc Fq F Ω n)) ∧
        (∀ m : ℕ, 1 ≤ m → (Places.numPoints (Lc Fq Ω n) (Fc Fq F Ω n) m : ℂ) =
          1 + ((Fintype.card Fq : ℂ) ^ n) ^ m - (c.map fun z => (z ^ n) ^ m).sum) ∧
        (Nat.card (Pic0 (Lc Fq Ω n) (Fc Fq F Ω n)) : ℂ) = (Lpoly c n).eval 1 ∧
        (Lpoly c n).eval 1 = (c.map fun z => 1 - z ^ n).prod := by
  obtain ⟨c, h1, h2, h3, -⟩ := classNumber_zeta hk
  refine ⟨c, h1, h2, h3, fun n _ => ⟨finite_Pic0 (constField_Fc Fq F Ω hk n), fun m hm => ?_, ?_,
    eval_one_Lpoly c n⟩⟩
  · rw [numPoints_Fc_formula Ω hk c h3 n m hm, card_Lc_fintype Fq Ω n, Multiset.map_map]
    push_cast
    rfl
  · rw [eval_one_Lpoly, classNumber_Fc Ω hk c h3 n]

end ClassNumber

end RamanujanPetersson.PicDescent

end


