-- Prove2me | Definitions.Def_RPLib_F2_038
-- name    : RPLib_F2_038
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T17:20:32.074283+00:00
-- url     : https://prove2.me/theorems/c412eda0-79d8-4116-8f67-94f245eff37f
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 038 of 70
-- statement:
--   File 038 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_PicDescent_E3`: S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers
--   * `S4.Def_RP_CoreA_Pic`: S4-CoreA part Pic (G1a): the Tate module of `Pic⁰(X̄)` is free of rank `2g`
--   * `S4.Def_RP_CoreA`: S4-CoreA (gate G1a): `T_l Pic⁰(X̄)` is free of rank `2g`, without a Jacobian (review R3)
--   * `S4.Def_RP_JacLaw_InstR`: S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l`
--   * `S4.Def_RP_JacFrob_Poly`: S4-JacFrob, part Poly: `ℤ[π] → End(J)` for `J = J_{F-bar}` and the kernel/degree bridge to `Pic⁰(X-bar)` (L23)
--   * `S4.Def_RP_CoreB_Zeta`: Core B, O4: the zeta link
--   * `S4.Def_RP_Cone_ResTr`: S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation
--   * `S4.Def_RP_Cone_TwNorm`: S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation
--   * `S4.Def_RP_Cone_ResAsmFin`: S4-PD E4S arithmetic ResA, part 4b: `exists_norm_tau_fin`
--   * `S4.Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
--   * `S4.Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_037

/-!
# Ramanujan-Petersson curve library (flat edition), file 038 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_PicDescent_E3`: S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers
* `S4.Def_RP_CoreA_Pic`: S4-CoreA part Pic (G1a): the Tate module of `Pic⁰(X̄)` is free of rank `2g`
* `S4.Def_RP_CoreA`: S4-CoreA (gate G1a): `T_l Pic⁰(X̄)` is free of rank `2g`, without a Jacobian (review R3)
* `S4.Def_RP_JacLaw_InstR`: S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l`
* `S4.Def_RP_JacFrob_Poly`: S4-JacFrob, part Poly: `ℤ[π] → End(J)` for `J = J_{F-bar}` and the kernel/degree bridge to `Pic⁰(X-bar)` (L23)
* `S4.Def_RP_CoreB_Zeta`: Core B, O4: the zeta link
* `S4.Def_RP_Cone_ResTr`: S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation
* `S4.Def_RP_Cone_TwNorm`: S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation
* `S4.Def_RP_Cone_ResAsmFin`: S4-PD E4S arithmetic ResA, part 4b: `exists_norm_tau_fin`
* `S4.Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
* `S4.Def_RP_PerfectCx`: S4-PD umbrella: the perfect complex and the cone in the S3 chart
-/

set_option autoImplicit false

-- ===== S4.Def_RP_PicDescent_E3 =====
section

/-!
# S4-PicDescent, part E3: `Pic(X̄)` as a direct limit, descent `Pic(X_m) = Pic(X̄)^(π^m)`, class numbers

`X̄ = F̄ ⊗ K` is modelled inside `Ω` (algebraically closed) as the union of the constant field extensions
`F_n = Fc Fq F Ω n`; the levels `lev j = (j+1)!` are cofinal for divisibility.
* `PicBar Ω hk`: the direct limit of `Pic(F_{lev j})` along the conorm maps `tr` (= `conNN`), i.e. `Pic(X̄)`;
* `piBar`: the arithmetic Frobenius `π` (`x ↦ x ^ q` on the constants) acting on `Pic(X̄)`;
* `degBar`, `PicBar0 = ker degBar` (`Pic⁰(X̄)`);
* `toBar m : Pic(F_m) →+ Pic(X̄)`, injective, with image `fixedBar m = Pic(X̄)^(π^m)`:
  **`picBarEquiv m : Pic(F_m) ≃+ Pic(X̄)^(π^m)`**, **`pic0BarEquiv m : Pic⁰(F_m) ≃+ Pic⁰(X̄)^(π^m)`**;
* the base level: `picBaseEquiv : Pic(F) ≃+ Pic(X̄)^π`, `pic0BaseEquiv : Pic⁰(F) ≃+ Pic⁰(X̄)^π`;
* `classNumber_bar`: `#Pic⁰(X̄)^(π^m) = h_m = L_m(1) = Π (1 - ω_i ^ m)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Bar

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

/-! ### The arithmetic Frobenius on `Pic(X̄)` -/

/-! ### Degree and `Pic⁰(X̄)` -/

/-! ### `Pic(F_m) → Pic(X̄)` and descent -/

section Descent

variable [IsAlgClosed Ω]

/-! ### The base level `m = 1` and class numbers -/

/-- **`h_m = #Pic⁰(X̄)^(π^m) = #Pic⁰(X_m) = L_m(1) = Π (1 - ω_i ^ m)`**, with the zeta multiset `ω` of `F`
(`|ω_i| ≤ √q`, at most `2g` of them, `N_k(F) = 1 + q^k - Σ ω_i^k`). -/
theorem classNumber_bar :
    ∃ c : Multiset ℂ, Multiset.card c ≤ 2 * RR.genusF Fq F ∧
      (∀ x ∈ c, ‖x‖ ≤ Real.sqrt (Fintype.card Fq)) ∧
      (∀ k : ℕ, 1 ≤ k →
        (Places.numPoints Fq F k : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ k - (c.map (· ^ k)).sum) ∧
      ∀ (m : ℕ) [NeZero m], Finite (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) ∧
        (Nat.card (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) : ℂ) = (Lpoly c m).eval 1 ∧
        (Lpoly c m).eval 1 = (c.map fun z => 1 - z ^ m).prod := by
  obtain ⟨c, h1, h2, h3, h4⟩ := classNumber_Fc_zeta Ω hk
  refine ⟨c, h1, h2, h3, fun m _ => ?_⟩
  obtain ⟨hf, -, hcard, hL⟩ := h4 m
  have := hf
  exact ⟨Finite.of_equiv _ (pic0BarEquiv Ω hk m).toEquiv, by rw [card_fixedBar0, hcard], hL⟩

end Descent

end Bar

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_CoreA_Pic =====
section

/-!
# S4-CoreA part Pic (G1a): the Tate module of `Pic⁰(X̄)` is free of rank `2g`

`A = Pic(X̄)[l^∞]` (`AddCommGroup.primaryComponent`, automatically inside `Pic⁰(X̄)`: `primary_le_PicBar0`),
`π = piBar` restricted to it (`piA`). The fixed points of `π ^ m` on `A` are the `l`-primary part of
`Pic⁰(X̄)^(π^m) = Pic⁰(X_m)`, of order `l ^ v_l(h_m)` (`card_fix_piA`, from `card_primaryComponent`).
With `card c = 2g`, `Π c_i = q^g` (`card_eq_two_genus`) and the valuation growth of `h_m = Π (1 - c_i^m)`
(`valuation_growth_padic`), the abstract `tate_rank` gives **`tate_rank_Pic`**: `T_l` of the divisible part of
`A` is free of rank `2g` over `ℤ_[l]`, with the Frobenius matrix `M`, `v det (1 - M^n)` equal to `v_l(h_n)` up to the
bounded contribution of the finite part `Phi = A ⧸ D`, and `Phi = 0 ↔ A` divisible `↔ #A[l] = l ^ 2g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial Matrix

namespace RamanujanPetersson.CoreA

open Places ZetaSB PicDescent RR

section Pic

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)

section Descent

variable [IsAlgClosed Ω]

/-- **G1a (Core A): `T_l Pic⁰(X̄)` is free of rank `2g`** (`l ≠ char`). `A = Pic(X̄)[l^∞]`, `D = l^k0 A` its divisible
part (`A ⧸ D = Phi` finite), `b1` an `F_l`-basis of `D[l]` with `2g` elements (so `T_l D ≅ ℤ_[l]^(2g)`), `M` the
matrix of `π` on `T_l D`; `v det (1 - M^n) ≤ v_l(h_n) ≤ v det (1 - M^n) + K0`, with equality for all `n` when
`Phi = 0`, and `Phi = 0 ↔ A` is `l`-divisible `↔ #A[l] = l ^ 2g`. -/
theorem tate_rank_Pic (l : ℕ) [hl : Fact l.Prime] (hq : ¬ l ∣ Fintype.card Fq) :
    ∃ (k0 : ℕ) (hdiv : ∀ y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ z, l • z = y)
      (b1 : Fin (2 * genusF Fq F) → (smulHom (Aℓ Ω hk l) (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0)
      (M : Matrix (Fin (2 * genusF Fq F)) (Fin (2 * genusF Fq F)) ℤ_[l]),
      (∀ d : Fin (2 * genusF Fq F) → ℤ, ∑ i, d i • b1 i = 0 → ∀ i, (l : ℤ) ∣ d i) ∧
      (∀ x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, l • x = 0 →
        ∃ d : Fin (2 * genusF Fq F) → ℤ, ∑ i, d i • b1 i = x) ∧
      IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M ∧
      Finite (Aℓ Ω hk l ⧸ (smulHom (Aℓ Ω hk l) (l ^ k0)).range) ∧
      (∃ K0, ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ padicValNat l (hBar Ω hk n) ∧
        padicValNat l (hBar Ω hk n) ≤ (1 - M ^ n).det.valuation + K0) ∧
      ((smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤ ↔ ∀ y : Aℓ Ω hk l, ∃ z, l • z = y) ∧
      (Nat.card {x : Aℓ Ω hk l // l • x = 0} = l ^ (2 * genusF Fq F) ↔
        (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) ∧
      ((smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤ →
        ∀ n, 0 < n → (1 - M ^ n).det.valuation = padicValNat l (hBar Ω hk n)) := by
  obtain ⟨c, hcard, -, hN, hfin⟩ := classNumber_bar (Ω := Ω) hk
  obtain ⟨hc2g, hprod, L, hL⟩ := card_eq_two_genus hk c hN hcard
  have hh : ∀ N, 0 < N → (hBar Ω hk N : ℂ) = (c.map fun z => 1 - z ^ N).prod := fun N hN0 => by
    have : NeZero N := ⟨hN0.ne'⟩
    obtain ⟨-, h1, h2⟩ := hfin N
    exact h1.trans h2
  have hh0 : ∀ N, 0 < N → hBar Ω hk N ≠ 0 := fun N hN0 => by
    have : NeZero N := ⟨hN0.ne'⟩
    have := (hfin N).1
    exact Nat.card_pos.ne'
  obtain ⟨⟨C₀, hnu⟩, hgrow⟩ :=
    valuation_growth_padic (l := l) hq (genusF Fq F) c hprod L hL (hBar Ω hk) hh hh0
  rw [hc2g] at hnu hgrow
  refine tate_rank (piA Ω hk l) (fun n => padicValNat l (hBar Ω hk n)) C₀ (2 * genusF Fq F) ?_ ?_ ?_ hnu hgrow
  · intro x
    obtain ⟨k, hx⟩ := AddCommGroup.mem_primaryComponent.mp x.2
    exact ⟨k, Subtype.ext (by rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact hx)⟩
  · intro x
    obtain ⟨m, hm, hx⟩ := exists_piBar_iterate_eq hk x.1
    exact ⟨m, hm, Subtype.ext (by rw [piA_iterate_coe]; exact hx)⟩
  · intro m hm
    have : NeZero m := ⟨hm.ne'⟩
    have := (hfin m).1
    exact card_fix_piA hk l m

end Descent

end Pic

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_CoreA =====
section

/-!
# S4-CoreA (gate G1a): `T_l Pic⁰(X̄)` is free of rank `2g`, without a Jacobian (review R3)

Umbrella file of the unit (namespace `RamanujanPetersson.CoreA`). `F / Fq` is a function field with
`constField Fq F = ⊥`, genus `g`, `q = #Fq`; `Ω` is algebraically closed over `F`; `l` is a prime with `l ∤ q`.
`A = Pic(X̄)[l^∞]` (`Aℓ Ω hk l`, inside `Pic⁰(X̄)`), `π = piA` the arithmetic Frobenius, `h_n = hBar Ω hk n =
#Pic⁰(X̄)^(π^n) = #Pic⁰(X_n) = Π (1 - ω_i ^ n)`.

Parts (each file below 150 user-s):
* abstract Core A for an `l`-primary group with a Frobenius: `Ord` (orders in `GL_D(F_l)`), `Fin` (`A[l]` finite),
  `Div` (divisible part `D = l^k0 A`, `A ⧸ D` finite), `Basis`/`Tate` (Tate coordinates `tateMap`, matrices
  `IsTateMat` over `ℤ_[l]`), `Det` (`#ker = l ^ v det`), `Grow` (`v det (1 - M^(d l^j))` grows by `s` per step),
  `Rank`, `Main` (**`tate_rank`**: rank `s = e`);
* zeta inputs: `ZInt` (**`card_eq_two_genus`**: `#ω = 2g`, `Π ω_i = q^g`, `Π (1 - ω_i X) ∈ ℤ[X]`),
  `Val`/`ValZ` (**`valuation_growth_padic`**: `v_l(h_N) ≤ C + 2g v_l(N)`, `v_l(h(d l^j)) = C' + 2g j`, in `ℂ_l`);
* `Pic`: `card_primaryComponent`, `piA`, `card_fix_piA` (`#A^(π^n) = l ^ v_l(h_n)`), **`tate_rank_Pic`**.

Main result here, **`tate_module_Pic`**: with `D = l^k0 A` divisible and `Phi = A ⧸ D` finite, the level maps
`tateMap N : (ℤ/l^N)^(2g) → D` are injective with image `D[l^N]` (so `T_l A = T_l D ≅ ℤ_[l]^(2g)`), `π` acts on
`T_l` by the matrix `M`, `v det (1 - M^n) ≤ v_l(h_n) ≤ v det (1 - M^n) + K0` (the `Phi` contribution), with
equality for all `n` when `Phi = 0`; and `Phi = 0 ↔ A` is `l`-divisible `↔ #A[l] = l ^ 2g` (the divisibility that
S4-CoreB supplies).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial Matrix

namespace RamanujanPetersson.CoreA

open Places ZetaSB PicDescent RR

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω] [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- **G1a: `T_l Pic⁰(X̄)` is free of rank `2g` over `ℤ_[l]`** (`l ∤ q`), with the Frobenius matrix `M`, the
valuation of `det (1 - M^n)` against `v_l(h_n)`, and `Phi = 0 ↔ A` divisible `↔ #A[l] = l ^ 2g`. -/
theorem tate_module_Pic (l : ℕ) [Fact l.Prime] (hq : ¬ l ∣ Fintype.card Fq) :
    ∃ (k0 : ℕ) (hdiv : ∀ y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ z, l • z = y)
      (b1 : Fin (2 * genusF Fq F) → (smulHom (Aℓ Ω hk l) (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0)
      (M : Matrix (Fin (2 * genusF Fq F)) (Fin (2 * genusF Fq F)) ℤ_[l]),
      (∀ N, Function.Injective (tateMap hdiv b1 hb1 N) ∧
        ∀ x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, l ^ N • x = 0 → ∃ cb, tateMap hdiv b1 hb1 N cb = x) ∧
      IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M ∧
      Finite (Aℓ Ω hk l ⧸ (smulHom (Aℓ Ω hk l) (l ^ k0)).range) ∧
      (∃ K0, ∀ n, 0 < n → (1 - M ^ n).det ≠ 0 ∧ (1 - M ^ n).det.valuation ≤ padicValNat l (hBar Ω hk n) ∧
        padicValNat l (hBar Ω hk n) ≤ (1 - M ^ n).det.valuation + K0) ∧
      ((smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤ ↔ ∀ y : Aℓ Ω hk l, ∃ z, l • z = y) ∧
      (Nat.card {x : Aℓ Ω hk l // l • x = 0} = l ^ (2 * genusF Fq F) ↔
        (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) ∧
      ((smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤ →
        ∀ n, 0 < n → (1 - M ^ n).det.valuation = padicValNat l (hBar Ω hk n)) := by
  obtain ⟨k0, hdiv, b1, hb1, M, h1inj, h1span, hrest⟩ := tate_rank_Pic (Ω := Ω) hk l hq
  exact ⟨k0, hdiv, b1, hb1, M, fun N => ⟨tateMap_injective hdiv b1 hb1 h1inj N,
    exists_tateMap_eq hdiv b1 hb1 h1span N⟩, hrest⟩

end RamanujanPetersson.CoreA


end

-- ===== S4.Def_RP_JacLaw_InstR =====
section

/-!
# S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l`

For points of `D(ωm)`, `D(ωr)`, `D(ωl)` (through `law_*` at `x ∘ nestK`).
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Inst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace LawData

variable (L : LawData K F)

section Rel

variable (x : Localization.Away L.ωm →ₐ[K] K) (xr : Localization.Away L.ωr →ₐ[K] K)
  (xl : Localization.Away L.ωl →ₐ[K] K)

theorem rel_r_m (hL : pL xr = pL x) (hR : pR xr = x.comp L.μm) : xr.comp L.ρr = pR x :=
  (L.r_nest xr).trans <| (L.law_r_m (x.comp (nestK (K := K) L.mU)) (xr.comp (nestK (K := K) L.rU))
    ((L.rB_L xr).trans (hL.trans (L.mB_L x).symm)) ((L.rB_R xr).trans (hR.trans (L.m_nest x)))).trans (L.mB_R x)

theorem rel_m_r (hL : pL x = pL xr) (hR : pR x = xr.comp L.ρr) : x.comp L.μm = pR xr :=
  (L.m_nest x).trans <| (L.law_m_r (x.comp (nestK (K := K) L.mU)) (xr.comp (nestK (K := K) L.rU))
    ((L.mB_L x).trans (hL.trans (L.rB_L xr).symm)) ((L.mB_R x).trans (hR.trans (L.r_nest xr)))).trans (L.rB_R xr)

theorem rel_l_m (hR : pR xl = pR x) (hL : pL xl = x.comp L.μm) : xl.comp L.lal = pL x :=
  (L.l_nest xl).trans <| (L.law_l_m (x.comp (nestK (K := K) L.mU)) (xl.comp (nestK (K := K) L.lU))
    ((L.lB_R xl).trans (hR.trans (L.mB_R x).symm)) ((L.lB_L xl).trans (hL.trans (L.m_nest x)))).trans (L.mB_L x)

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacFrob_Poly =====
section

/-!
# S4-JacFrob, part Poly: `ℤ[π] → End(J)` for `J = J_{F-bar}` and the kernel/degree bridge to `Pic⁰(X-bar)` (L23)

* `piBar_mem_PicBar0`, **`piBar0 : Module.End ℤ (PicBar0 Ω hk)`** (the arithmetic Frobenius on `Pic⁰(X-bar)`);
* `Psi0Equiv_symm_piJ` (`π_J` acts on `J(k-bar) ≃ PicBar0` as `piBar0`);
* **`cls_polyEnd_piJ`** (`F(π_J)` acts as `aeval piBar0 F`), **`polyEnd_mul_piJ`**, `polyEnd_X_piJ` (the ring map `ℤ[π] → End(J)`);
* **`kerPtsEquiv_piJ`** (`Ker F(π_J)(k-bar) ≃ ker (aeval piBar0 F)`), **`degree_polyEnd_piJ`**
  (`deg F(π_J) = #ker (aeval piBar0 F)` for `p ∤ F(0)`: the `deg_eq_card_ker` field of `JacAlg.DegreeData`).
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

variable {M : Type*} [AddCommGroup M]

end Gen

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

/-- **The arithmetic Frobenius `π` on `Pic⁰(X-bar)`** as a `ℤ`-linear endomorphism (the `π` of `JacAlg.DegreeData`). -/
noncomputable def piBar0 : Module.End ℤ (RamanujanPetersson.PicDescent.PicBar0 Ω hk) :=
  (((RamanujanPetersson.PicDescent.piBar Ω hk).comp (RamanujanPetersson.PicDescent.PicBar0 Ω hk).subtype).codRestrict
    (RamanujanPetersson.PicDescent.PicBar0 Ω hk) fun z => piBar_mem_PicBar0 Fq F Ω hk z z.2).toIntLinearMap

theorem coe_piBar0 (z : RamanujanPetersson.PicDescent.PicBar0 Ω hk) :
    (piBar0 Fq F Ω hk z : RamanujanPetersson.PicDescent.PicBar Ω hk) =
      RamanujanPetersson.PicDescent.piBar Ω hk (z : RamanujanPetersson.PicDescent.PicBar Ω hk) := rfl

end Spec

end RamanujanPetersson.JacFrob


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

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

theorem coe_piBar0_pow (m : ℕ) (z : PicBar0 Ω hk) :
    (((piBar0 Fq F Ω hk) ^ m) z : PicBar Ω hk) = (piBar Ω hk)^[m] (z : PicBar Ω hk) := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, coe_piBar0, ih, Function.iterate_succ_apply']

theorem card_ker_one_sub_X_pow_piBar0 (m : ℕ) :
    Nat.card (LinearMap.ker (aeval (piBar0 Fq F Ω hk) (1 - X ^ m : ℤ[X]))) =
      Nat.card (fixedBar Ω hk m ⊓ PicBar0 Ω hk : AddSubgroup (PicBar Ω hk)) := by
  have key : ∀ z : PicBar0 Ω hk, aeval (piBar0 Fq F Ω hk) (1 - X ^ m : ℤ[X]) z = 0 ↔
      (piBar Ω hk)^[m] (z : PicBar Ω hk) = z := fun z => by
    rw [map_sub, map_one, map_pow, aeval_X, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
      eq_comm, Subtype.ext_iff, coe_piBar0_pow]
  exact Nat.card_congr
    { toFun := fun z => ⟨(z.1 : PicBar Ω hk),
        AddSubgroup.mem_inf.2 ⟨(key z.1).1 (LinearMap.mem_ker.1 z.2), z.1.2⟩⟩
      invFun := fun w => ⟨⟨w.1, (AddSubgroup.mem_inf.1 w.2).2⟩,
        LinearMap.mem_ker.2 ((key _).2 (AddSubgroup.mem_inf.1 w.2).1)⟩
      left_inv := fun z => rfl
      right_inv := fun w => rfl }

theorem piBar0_injective : Function.Injective (piBar0 Fq F Ω hk) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨m, hm, hfix⟩ := CoreA.exists_piBar_iterate_eq hk (z : PicBar Ω hk)
  have h1 : piBar Ω hk (z : PicBar Ω hk) = 0 := by rw [← coe_piBar0, hz, ZeroMemClass.coe_zero]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Function.iterate_succ_apply, h1, Function.iterate_fixed (map_zero (piBar Ω hk)) k] at hfix
  exact Subtype.ext hfix.symm

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_Cone_ResTr =====
section

/-!
# S4-PD E4S arithmetic ResA, part 2: transport of normalised generators under geometric conjugation

* `inclU_restrict`, `exists_valuation_transport` (L3): if `τ` is the restriction of `g` to a normal level `L`, the
  place of `L` under `g • Q` is the transport of the place under `Q`, and `v_{gQ}(τ b) = v_Q(b)`.
* `norm_conj` (L4, one level): a generator normalised at `(L, Q)` conjugates by `x` (fixing `ζ_N`) to a generator
  normalised at `(L, x • Q)`.
* `NormAll`, `normAll_conj` (L4, S3 chart): the same at all constant levels `M ⊔ K(𝔽_{p^(e k)})`, `k₀ ∣ k`.
* `chi_eq_of_norm` (L5): two generators normalised at the same prime have the same value under every locally
  constant hom `Γ_H → ℤ/N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Transport

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

end Transport

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

end Conj

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable {p e : ℕ} [Fact p.Prime] [CharP F p]
variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **(L5)** Two generators normalised at the same boundary prime have the same value under every locally constant
hom `χ : Γ_H → ℤ/N`. -/
theorem chi_eq_of_norm {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (Γ : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hζΓ : ∀ σ ∈ Γ, σ ζN = ζN)
    (hΓ : ∀ σ, σ ∈ Γ ↔ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))}
    (hQ : IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    (J : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hJΓ : J ≤ Γ) (τ τ' : J) {k₀ k₀' : ℕ} (hk₀ : 0 < k₀)
    (hk₀' : 0 < k₀') (hn : NormAll p e hζN M Q J τ k₀) (hn' : NormAll p e hζN M Q J τ' k₀')
    (χ : Γ → ZMod N) (hχc : IsLocallyConstant χ) (hχ : ∀ σ σ', χ (σ * σ') = χ σ + χ σ') :
    χ ⟨τ, hJΓ τ.2⟩ = χ ⟨τ', hJΓ τ'.2⟩ := by
  obtain ⟨α, hαr, hαχ⟩ := exists_kchar_eq hζN hζΓ χ hχc hχ
  have hfixx : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (p ^ e),
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup →
      σ ((α : maxUnram (Places.Rfin Fq F) F) ^ N) = (α : maxUnram (Places.Rfin Fq F) F) ^ N := by
    intro σ hσg hσM
    exact (mem_rad _ _ α).1 hαr σ ((hΓ σ).2 ⟨by rw [hq]; exact hσg, hσM⟩)
  obtain ⟨k1, hk1, hx1⟩ := exists_sup_constLevel_of_fixed he hMU hfixx
  obtain ⟨m, hm_def⟩ : ∃ m, m = k₀ * k₀' * k1 := ⟨_, rfl⟩
  have hm : 0 < m := hm_def ▸ Nat.mul_pos (Nat.mul_pos hk₀ hk₀') hk1
  have hdvd0 : k₀ ∣ m := ⟨k₀' * k1, by rw [hm_def]; ring⟩
  have hdvd0' : k₀' ∣ m := ⟨k₀ * k1, by rw [hm_def]; ring⟩
  have hdvd1 : k1 ∣ m := ⟨k₀ * k₀', by rw [hm_def]; ring⟩
  have hLM : M ⊔ constLevel F p (e * m) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hm))
  have hLU : M ⊔ constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hLM
  have hFDL : FiniteDimensional F ↥(M ⊔ constLevel F p (e * m)) := hLM.1
  have : IsGalois F ↥(M ⊔ constLevel F p (e * m)) := hLM.2.1
  have hDedI : IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F) (L := ↥(M ⊔ constLevel F p (e * m)))
  have hFracI : IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)))
      ↥(M ⊔ constLevel F p (e * m)) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F _
  have hxL : (((α : maxUnram (Places.Rfin Fq F) F) ^ N : maxUnram (Places.Rfin Fq F) F) :
      AlgebraicClosure F) ∈ M ⊔ constLevel F p (e * m) :=
    sup_le_sup_left (constLevel_le_of_dvd (Nat.mul_pos he hm) (Nat.mul_dvd_mul_left e hdvd1)) M hx1
  let b : ↥(M ⊔ constLevel F p (e * m)) := ⟨_, hxL⟩
  let v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    ⟨Q.comap (inclU (Places.Rinf Fq F) hLU), Ideal.IsPrime.comap _ (hK := hQ.1), comap_inclU_ne_bot hLU hQ⟩
  have h1 := @hn m hm hdvd0 hLU hDedI hFracI v rfl α b (Subtype.ext rfl)
  have h2 := @hn' m hm hdvd0' hLU hDedI hFracI v rfl α b (Subtype.ext rfl)
  rw [← hαχ, ← hαχ]
  show kchar hζN (Γ := J) α τ = kchar hζN (Γ := J) α τ'
  rw [h1, h2]

end S3

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_TwNorm =====
section

/-!
# S4-PD (4), arithmetic twist part B1: normalised generators under twisted conjugation

The twisted forms of `kchar_conj`, `norm_conj`, `normAll_conj` and `chi_eq_of_norm` (`Def_RP_Cone_ResTr`): if `x`
acts on `ζ_N` by `x ζ_N = ζ_N ^ w` (e.g. a Frobenius lift, `w = q`), then conjugating a normalised generator by `x`
gives a generator `w`-normalised at `x • Q` (`NormAllTw`), and a `w`-normalised generator has `w` times the
`χ`-value of a normalised one at the same prime (`chi_eq_of_normTw`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section ConjTw

variable {K E : Type} [Field K] [Field E] [Algebra K E] {N : ℕ} [NeZero N] {ζ : E}

end ConjTw

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

end Conj

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable {p e : ℕ} [Fact p.Prime] [CharP F p]
variable (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- **Twisted (L5)**: a `w`-normalised generator has `w` times the `χ`-value of a normalised generator at the same
boundary prime, for every locally constant hom `χ : Γ_H → ℤ/N`. -/
theorem chi_eq_of_normTw {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (Γ : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hζΓ : ∀ σ ∈ Γ, σ ζN = ζN)
    (hΓ : ∀ σ, σ ∈ Γ ↔ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))}
    (hQ : IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q)
    (J : Subgroup (Pi1 (Places.Rfin Fq F) F)) (hJΓ : J ≤ Γ) (τ τ' : J) {k₀ k₀' : ℕ} (hk₀ : 0 < k₀)
    (hk₀' : 0 < k₀') {w : ZMod N} (hn : NormAllTw p e hζN M Q J τ k₀ w) (hn' : NormAll p e hζN M Q J τ' k₀')
    (χ : Γ → ZMod N) (hχc : IsLocallyConstant χ) (hχ : ∀ σ σ', χ (σ * σ') = χ σ + χ σ') :
    χ ⟨τ, hJΓ τ.2⟩ = w * χ ⟨τ', hJΓ τ'.2⟩ := by
  obtain ⟨α, hαr, hαχ⟩ := exists_kchar_eq hζN hζΓ χ hχc hχ
  have hfixx : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (p ^ e),
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup →
      σ ((α : maxUnram (Places.Rfin Fq F) F) ^ N) = (α : maxUnram (Places.Rfin Fq F) F) ^ N := by
    intro σ hσg hσM
    exact (mem_rad _ _ α).1 hαr σ ((hΓ σ).2 ⟨by rw [hq]; exact hσg, hσM⟩)
  obtain ⟨k1, hk1, hx1⟩ := exists_sup_constLevel_of_fixed he hMU hfixx
  obtain ⟨m, hm_def⟩ : ∃ m, m = k₀ * k₀' * k1 := ⟨_, rfl⟩
  have hm : 0 < m := hm_def ▸ Nat.mul_pos (Nat.mul_pos hk₀ hk₀') hk1
  have hdvd0 : k₀ ∣ m := ⟨k₀' * k1, by rw [hm_def]; ring⟩
  have hdvd0' : k₀' ∣ m := ⟨k₀ * k1, by rw [hm_def]; ring⟩
  have hdvd1 : k1 ∣ m := ⟨k₀ * k₀', by rw [hm_def]; ring⟩
  have hLM : M ⊔ constLevel F p (e * m) ∈ unramSet (Places.Rfin Fq F) F :=
    sup_mem_unramSet (Places.Rfin Fq F) F hM (constLevel_mem_unramSet (Places.Rfin Fq F) (Nat.mul_pos he hm))
  have hLU : M ⊔ constLevel F p (e * m) ≤ maxUnram (Places.Rfin Fq F) F := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hLM
  have hFDL : FiniteDimensional F ↥(M ⊔ constLevel F p (e * m)) := hLM.1
  have : IsGalois F ↥(M ⊔ constLevel F p (e * m)) := hLM.2.1
  have hDedI : IsDedekindDomain (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    integralClosure.isDedekindDomain (A := Places.Rinf Fq F) (K := F) (L := ↥(M ⊔ constLevel F p (e * m)))
  have hFracI : IsFractionRing (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m)))
      ↥(M ⊔ constLevel F p (e * m)) :=
    integralClosure.isFractionRing_of_finite_extension (A := Places.Rinf Fq F) F _
  have hxL : (((α : maxUnram (Places.Rfin Fq F) F) ^ N : maxUnram (Places.Rfin Fq F) F) :
      AlgebraicClosure F) ∈ M ⊔ constLevel F p (e * m) :=
    sup_le_sup_left (constLevel_le_of_dvd (Nat.mul_pos he hm) (Nat.mul_dvd_mul_left e hdvd1)) M hx1
  let b : ↥(M ⊔ constLevel F p (e * m)) := ⟨_, hxL⟩
  let v : HeightOneSpectrum (integralClosure (Places.Rinf Fq F) ↥(M ⊔ constLevel F p (e * m))) :=
    ⟨Q.comap (inclU (Places.Rinf Fq F) hLU), Ideal.IsPrime.comap _ (hK := hQ.1), comap_inclU_ne_bot hLU hQ⟩
  have h1 := @hn m hm hdvd0 hLU hDedI hFracI v rfl α b (Subtype.ext rfl)
  have h2 := @hn' m hm hdvd0' hLU hDedI hFracI v rfl α b (Subtype.ext rfl)
  rw [← hαχ, ← hαχ]
  show kchar hζN (Γ := J) α τ = w * kchar hζN (Γ := J) α τ'
  rw [h1, h2]

end S3

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResAsmFin =====
section

/-!
# S4-PD E4S arithmetic ResA, part 4b: `exists_norm_tau_fin`

`exists_norm_tau_sum` for `J t = I(Q t) ∩ ker π` in the S3 chart, with all level data (`d = |Gf|_{p'}`, roots of
unity, places, `x`) discharged (split from `Def_RP_Cone_ResAsm` for build time).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1600000 in
/-- `exists_norm_tau_sum` for `J t = I(Q t) ∩ ker π`, with the level data (`d = |Gf|_{p'}`, `ζ`, places, `x`)
discharged. -/
theorem exists_norm_tau_fin {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0)
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    {Gf : Type} [Group Gf] [Finite Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    {T : Type} [Fintype T] (Qt : T → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
    (hQt : ∀ t, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (Qt t))
    (hcover : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q → ∃ t,
      ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
        g ∈ (IntermediateField.restrict hMU).fixingSubgroup ∧ Q = g • Qt t)
    (hdisj : ∀ t t', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq),
      g ∈ (IntermediateField.restrict hMU).fixingSubgroup → Qt t' = g • Qt t → t = t')
    (Γ : Subgroup (Pi1 (Places.Rfin Fq F) F))
    (hΓ : ∀ σ, σ ∈ Γ ↔ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ∧
      σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hJΓ : ∀ t, Jt π (Qt t) ≤ Γ) :
    ∃ k₀, 0 < k₀ ∧ ∃ τ : ∀ t, Jt π (Qt t),
      (∀ t, TauProp (Qt t) (Jt π (Qt t)) N (τ t)) ∧
      (∀ t, NormAll p e hζN M (Qt t) (Jt π (Qt t)) (τ t) k₀) ∧
      ∀ χ : Γ → ZMod N, IsLocallyConstant χ → (∀ σ σ', χ (σ * σ') = χ σ + χ σ') →
        ∑ t, χ ⟨τ t, hJΓ t (τ t).2⟩ = 0 := by
  have hp : p.Prime := Fact.out
  have hc0 : Nat.card Gf ≠ 0 := Nat.card_pos.ne'
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.card Gf / p ^ Nat.factorization (Nat.card Gf) p := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    rw [hd_def]
    exact Nat.ordCompl_pos p hc0
  have hdF : (d : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p, hd_def]
    exact Nat.not_dvd_ordCompl hp hc0
  have hpd : p ^ Nat.factorization (Nat.card Gf) p * d = Nat.card Gf := by
    rw [hd_def]
    exact Nat.ordProj_mul_ordCompl_eq_self (Nat.card Gf) p
  have hNd : ((N * d : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_mul]
    exact mul_ne_zero hNF hdF
  haveI : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) hd0.ne'⟩
  obtain ⟨ζd, hζd, hζdg⟩ := CP4a.exists_zeta_geo hq he hNd
  have hne : ∀ t, (Qt t).comap (algebraMap (Places.Rinf Fq F)
      (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) ≠ ⊥ := by
    intro t
    have := (hQt t).1
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hQt t).2
    exact Ideal.comap_ne_bot_of_integral_mem hz0 hz (Algebra.IsIntegral.isIntegral z)
  obtain ⟨x, hx⟩ : ∃ x : T → HeightOneSpectrum (Places.Rinf Fq F), ∀ t, (x t).asIdeal =
      (Qt t).comap (algebraMap (Places.Rinf Fq F) (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) :=
    ⟨fun t => ⟨(Qt t).comap (algebraMap (Places.Rinf Fq F) (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))),
      Ideal.IsPrime.comap _ (hK := (hQt t).1), hne t⟩, fun _ => rfl⟩
  obtain ⟨k₀, hk₀, τ, hT, hn, hs⟩ := exists_norm_tau_sum hq he (CP4a.exists_zeta_level he)
    (CP4a.isUnit_cast_Rinf hNF) hζN hζNg hM hMU Qt hQt hcover hdisj Γ hΓ (fun t => Jt π (Qt t)) hJΓ
    (fun t σ => Subgroup.mem_inf.trans (and_congr Iff.rfl (MonoidHom.mem_ker.trans (eq_one_iff_fixM hMU hπM σ))))
    (fun _ => d) (fun _ => hd0) (fun _ => CP4a.isUnit_cast_Rfin hNd) (fun _ => CP4a.isUnit_cast_Rinf hNd)
    (fun _ => ζd) (fun _ => hζd)
    (fun t σ hσ => by
      haveI := (hQt t).1
      exact hζdg σ (Kummer.inertia_le_pi1geo he hq (hP := (hQt t).1) hσ))
    x hx (fun _ => (⟨algebraMap Fq[X] F X, isIntegral_algebraMap⟩ : Places.Rfin Fq F))
    (fun t => by
      have h := JacComplete.one_lt_placeVal_inr_x (K := Fq) (F := F) (x t)
      exact h)
    (fun _ => Nat.factorization (Nat.card Gf) p)
    (fun t σ hσ => by
      show σ ^ (p ^ Nat.factorization (Nat.card Gf) p * d) ∈ Jt π (Qt t)
      rw [hpd]
      exact Subgroup.mem_inf.2 ⟨Subgroup.pow_mem _ hσ _, by rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']⟩)
  refine ⟨k₀, hk₀, τ, hT, fun t => ?_, hs⟩
  intro k hk hdvd hLU hD hF v hv α b hαb
  exact @hn k hk hdvd hLU hD hF t v hv α b hαb

end S3

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResAsm2 =====
section

/-!
# S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart

Continues `Def_RP_Cone_ResAsm` (split for build time). With `τ t` the normalised generators of
`exists_norm_tau_fin` at the cover points `cosQA t`:

* `locGen_base`, `normAll_base`: the base-point data `σ s := τ (cosB s)`.
* `yconj_chi`: `χ (x_t σ x_t⁻¹) = χ (τ t)`; `yconj_exist`: existence at the conjugates.
* **`exists_resDat`**: under `PicDivX`, a `ResDat π π₁^geo I N (CosT π π₁^geo I)` (the input of `ResDat.toResHyp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

section Tau

variable {Gf : Type} [Group Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf) {S : Type}
  (P : S → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
  (hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (P s))
  (I : S → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hI : ∀ s, I s = Inert (P s))
  (τ : ∀ t : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I,
    Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))

set_option maxHeartbeats 400000 in
theorem normAll_base {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    {M : IntermediateField F (AlgebraicClosure F)} {k₀ : ℕ}
    (hn : ∀ t, NormAll p e hζN M (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) (τ t) k₀) (s : S) :
    NormAll p e hζN M (P s) (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s)))
      (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s)) k₀ := by
  have key : ∀ X, X = cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s) →
      NormAll p e hζN M X (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s)))
        (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I s)) k₀ := by
    rintro X rfl
    exact hn _
  exact key (P s) (cosQA_base π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P s).symm

end Tau

end S3

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx =====
section

/-!
# S4-PD umbrella: the perfect complex and the cone in the S3 chart

Items (1)-(3) are `Def_RP_Tsen`, `Def_RP_TameInertia`, `Def_RP_CdOne`; item (5) (the perfect `Λ[Γ]`-complex, mod `l^m`)
is `Def_RP_PerfectCx_RedPC` and its imports. This file closes item (4) in the S3 chart (`U = Spec Rfin`, boundary over `∞`):
* `h2Equiv_S3`: for `ρ = τ ∘ π` (`π` cut out by a finite unramified `M`), the cone's `H²` is `H²_c = V_Γ`, and the
  cone Frobenius of `φ⁻¹` (`φ` a Frobenius lift, true boundary permutation) is `q • ρ(φ⁻¹)` (`= V_Γ(-1)`).
* **`h2Equiv_lisse`**: the same for every lisse `ρ` (finite `V`, open kernel).
* `cone_h3_eq_zero`: the cone's `H³ = Π_s H²(Γ ⊓ I_s, -)` vanishes.
Explicit hypotheses: `PicDivU` (`cd_l ≤ 1`) and `PicDivX` (residue surjectivity), as in `CdOne` / `Cone_Exist`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace PerfectCx

noncomputable section

open CurveCoh Kummer CP4a Residue
open scoped Pointwise Polynomial

section Gen

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {q : ℕ}
  {R0 : Type} [CommRing R0] [Algebra R0 K] [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
/-- **Cone `H³ = 0`** in the S3 chart: `H²(π₁^geo ⊓ I_s, -) = 0` at every boundary point. -/
theorem cone_h3_eq_zero {l : ℕ} [Fact l.Prime] (hl : (l : F) ≠ 0) (hPicU : CdOne.PicDivU (Places.Rfin Fq F) F p l)
    {S : Type} (D : BdryData (Places.Rfin Fq F) F (Fintype.card Fq) (Places.Rinf Fq F) S) (s : S)
    (Λ : Type) [CommRing Λ] (n : ℕ) :
    H2All Λ (Pi1 (Places.Rfin Fq F) F) (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ D.inertia s) l n :=
  CdOne.h2All_geo_inf_inertia (Places.Rfin Fq F) Fq he hq (Kummer.perfect_Rfin Fq F) l
    (CP4a.isUnit_cast_Rfin hl) hPicU (D.P s) Λ n

end S3

end

end PerfectCx
end RamanujanPetersson


end


