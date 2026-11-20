-- Prove2me | Definitions.Def_RPLib_F2_064
-- name    : RPLib_F2_064
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T22:07:11.868048+00:00
-- url     : https://prove2.me/theorems/0a46b32b-a977-4c35-9d97-0382a97ed6ae
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 064 of 70
-- statement:
--   File 064 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_ThetaSquare_Curve5`: Unit S4-ThetaSquare, file Curve5: the pull-back `D_e` as a divisor, and the curve-level square (T4c (C), T5)
--   * `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
--   * `S4.Def_RP_ThetaCube_Gen`: S4-ThetaCube, file Gen (D-B4, part 6a): the line test at every point of the line
--   * `S4.Def_RP_ThetaCube_Asm1`: S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
--   * `S4.Def_RP_ThetaCube_NZS`: S4-ThetaCube, file NZS (D-C1, part 11): the determinants `det_k` are nonzero
--   * `S4.Def_RP_ThetaCube_TrNe`: S4-ThetaCube, file TrNe (D-C1, part 6): the open `ψ_S⁻¹ VJ` is nonempty
--   * `S4.Def_RP_ThetaCube_GrB`: S4-ThetaCube, file GrB (D-C1, part 8): the Gram matrix on `J^3`
--   * `S4.Def_RP_ThetaCube_Asm2`: S4-ThetaCube, file Asm2 (D-B4, part 6c): the pull-back of the cube divisor along `Φ3` and the assembly
--   * `S4.Def_RP_ThetaCube_GrC`: S4-ThetaCube, file GrC (D-C1, part 9): the cube divisor is principal up to `2`
--   * `S4.Def_RP_ThetaCube`: Unit S4-ThetaCube (Theta B, lemmas L40-L42 of `S4_COREB_ROUTE.md` section 3): umbrella
--   * `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Val3`: S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
--   * `S4.Def_RP_JacFrob_All`: S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`
--   * `S4.Def_RP_JacFrob_TanG`: S4-JacFrob, part TanG: the differential of `mor φ` (generic)
--   * `S4.Def_RP_JacFrob_Tan`: S4-JacFrob, part Tan: **`dπ_J = 1`**
--   * `S4.Def_RP_JacFrob_Poly`: S4-JacFrob, part Poly: `ℤ[π] → End(J)` for `J = J_{F-bar}` and the kernel/degree bridge to `Pic⁰(X-bar)` (L23)
--   * `S4.Def_RP_CoreB_Data`: Core B, O3 (L43): degree data for `ℤ[π]` on `Pic⁰(X-bar)`
--   * `S4.Def_RP_CoreB_Div`: Core B, O5 (CB1): `Pic(X̄)[l^∞]` is `l`-divisible
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_062

/-!
# Ramanujan-Petersson curve library (flat edition), file 064 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_ThetaSquare_Curve5`: Unit S4-ThetaSquare, file Curve5: the pull-back `D_e` as a divisor, and the curve-level square (T4c (C), T5)
* `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
* `S4.Def_RP_ThetaCube_Gen`: S4-ThetaCube, file Gen (D-B4, part 6a): the line test at every point of the line
* `S4.Def_RP_ThetaCube_Asm1`: S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
* `S4.Def_RP_ThetaCube_NZS`: S4-ThetaCube, file NZS (D-C1, part 11): the determinants `det_k` are nonzero
* `S4.Def_RP_ThetaCube_TrNe`: S4-ThetaCube, file TrNe (D-C1, part 6): the open `ψ_S⁻¹ VJ` is nonempty
* `S4.Def_RP_ThetaCube_GrB`: S4-ThetaCube, file GrB (D-C1, part 8): the Gram matrix on `J^3`
* `S4.Def_RP_ThetaCube_Asm2`: S4-ThetaCube, file Asm2 (D-B4, part 6c): the pull-back of the cube divisor along `Φ3` and the assembly
* `S4.Def_RP_ThetaCube_GrC`: S4-ThetaCube, file GrC (D-C1, part 9): the cube divisor is principal up to `2`
* `S4.Def_RP_ThetaCube`: Unit S4-ThetaCube (Theta B, lemmas L40-L42 of `S4_COREB_ROUTE.md` section 3): umbrella
* `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Val3`: S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
* `S4.Def_RP_JacFrob_All`: S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`
* `S4.Def_RP_JacFrob_TanG`: S4-JacFrob, part TanG: the differential of `mor φ` (generic)
* `S4.Def_RP_JacFrob_Tan`: S4-JacFrob, part Tan: **`dπ_J = 1`**
* `S4.Def_RP_JacFrob_Poly`: S4-JacFrob, part Poly: `ℤ[π] → End(J)` for `J = J_{F-bar}` and the kernel/degree bridge to `Pic⁰(X-bar)` (L23)
* `S4.Def_RP_CoreB_Data`: Core B, O3 (L43): degree data for `ℤ[π]` on `Pic⁰(X-bar)`
* `S4.Def_RP_CoreB_Div`: Core B, O5 (CB1): `Pic(X̄)[l^∞]` is `l`-divisible
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaSquare_Curve5 =====
section

/-!
# Unit S4-ThetaSquare, file Curve5: the pull-back `D_e` as a divisor, and the curve-level square (T4c (C), T5)

* `IsGoodFor P0 W0 e G`: the hypotheses under which `D_e = AJ^*(Θ translated by e)` is the reduced divisor `G`
  (`G ≥ 0` reduced of degree `g` with `ℓ(G) = 1`, the class of `e` is `[W0 - G] - (g-2)[P0]`, `f_e` avoids `Θ`, and for
  each `v ∈ G` the class `W0 - G + 2[v]` has `ℓ = 1` and contains the divisor of an `X0` point);
* **`Dc_kpt_eq`**: then `D_e (q) = G (kPl q)` at every `K`-point `q` of `X1`; `Dc_generic`: `D_e (η) = 0`;
* `sub_mem_PrincK`: `e1 e2 = e3 e4` forces `G1 + G2 - G3 - G4 ∈ PrincK`;
* **`square_curve`** (the curve-level theorem of the square): for good `e1, e2, e3, e4` with `e1 e2 = e3 e4`, the cycle
  `D_{e1} + D_{e2} - D_{e3} - D_{e4}` on `X1` is the principal divisor `G1 + G2 - G3 - G4` (on `K`-points, and `0` at `η`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve5

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **`D_e` on `K`-points** (Milne III.6.7 at the closed points): `D_e (q) = G (kPl q)`. -/
theorem Dc_kpt_eq (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) {e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F} (h : IsGoodFor P0 W0 e G)
    (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    Dc P0 e (q.left (IsLocalRing.closedPoint K)) = G (kPl q) := by
  by_cases hv : 1 ≤ G (kPl q)
  · obtain ⟨h2, yR, hy⟩ := h.ptX0 _ hv
    rw [Dc_eq_one hg P0 hW h.nonneg h.deg h.ell e h.cls h.avoid q hv h2 yR hy]
    have := h.red (kPl q)
    omega
  · have h0 : G (kPl q) = 0 := by
      have := Finsupp.le_def.1 h.nonneg (kPl q)
      simp only [Finsupp.coe_zero, Pi.zero_apply] at this
      omega
    rw [h0]
    exact Dc_eq_zero P0 hg e fun hm => hv ((mem_W_fe_iff hg P0 hW h.nonneg h.deg h.ell e h.cls q).1 hm)

end Curve5

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaCube_Test =====
section

/-!
# S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
At `z = p_{i0}` on the `i0`-th line through `p`:
* `cpull_detPP_kpt`: the determinant side is `ord_{p_{i0}}` of the slice;
* `ord_slice_const`: an all-constant slice has order `0` everywhere;
* `ord_slice_eq`: the order of a one-variable slice is `G (p_{i0})` once `G ∼ H - Zsl`, `ℓ(G) = 1`;
* `cube_side_mem`, `cube_side_not_mem`: the `Θ` side via `line_psiS_transl`, `Dc_kpt_eq`, `cpull_const_Theta`;
* **`test_mem`**, **`test_not_mem`**: the two sides agree at `z` (both avoid);
* `Zsl_eq`, `jacPic_psiE`, `cls_good_eq`, **`cls_test`**: the class bookkeeping `[G_S] = [H - Zsl_S]`.
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

section Test

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **The `Θ` side, `β i0 ∈ S`**: `D_{e_S} (p_{i0}) = G (p_{i0})`. -/
theorem cube_side_mem (hg : 0 < genusFK K F) {W0 G : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (n : ℕ)
    (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hS : β i0 ∈ S)
    (hgood : IsGoodFor P0 W0 ((p ≫ psiE P0 n β S i0) * x0) G) :
    Avoid ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0) ∧
      cpull ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0)
          ((p ≫ prj K F n i0).left (IsLocalRing.closedPoint K)) = G (kPl (p ≫ prj K F n i0)) := by
  rw [line_psiS_transl, if_pos hS]
  exact ⟨hgood.avoid, Dc_kpt_eq hg P0 hW hgood _⟩

end Test

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Gen =====
section

/-!
# S4-ThetaCube, file Gen (D-B4, part 6a): the line test at every point of the line
* `ord_slice_gen`: `ord_q (slice) = G q - H q + Zsl q` (no condition on `q`);
* **`test_mem_gen`**: the `β i0 ∈ S` test with the correction `- H q + Zsl q` (it cancels in the cube sum);
* **`ell_zero_of_not_mem_W`**: `deg D = g - 1`, `[e] = [W0 - D] - (g-1)[P0]`, `e ∉ W` give `ℓ(D) = 0`.
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

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **The per-`S` line test, `β i0 ∈ S`, at any point of the line**: both sides avoid and the determinant
side is the `Θ` side minus `H (p_{i0})` plus `Zsl (p_{i0})`. -/
theorem test_mem_gen (hg : 0 < genusFK K F) {W0 G : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (n : ℕ)
    (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hS : β i0 ∈ S)
    (hgood : IsGoodFor P0 W0 ((p ≫ psiE P0 n β S i0) * x0) G) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (j0 : Fin N) (hτ0 : τ j0 = i0)
    (hj0 : ∀ j, τ j = i0 → j = j0) (H : Places.Divisor K F) (hH : ∀ l, h l ∈ LFK K F H)
    (hH0 : ∀ a, a ≠ Sum.inl j0 → H (kPl (ptC K F n τ m p a)) = 0)
    (hinj : ∀ a b, a ≠ Sum.inl j0 → b ≠ Sum.inl j0 → kPl (ptC K F n τ m p a) = kPl (ptC K F n τ m p b) → a = b)
    (hli : LinearIndependent K h) (hcls : clsK K F G = clsK K F (H - Zsl K F n τ m p j0)) :
    Avoid (line K F n i0 p).left (JacDivisors.div (PP K F n).left (detPP K F n τ m h)) ∧
      Avoid ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0) ∧
      cpull (line K F n i0 p).left (JacDivisors.div (PP K F n).left (detPP K F n τ m h))
          ((p ≫ prj K F n i0).left (IsLocalRing.closedPoint K)) =
        cpull ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0)
          ((p ≫ prj K F n i0).left (IsLocalRing.closedPoint K)) - H (kPl (p ≫ prj K F n i0)) +
          Zsl K F n τ m p j0 (kPl (p ≫ prj K F n i0)) := by
  have hne := slice_ne_zero hg n τ m h i0 p j0 hτ0 hj0 H hH hH0 hinj hli
    ((ellFK_of_clsK_eq hcls).symm.trans hgood.ell).le
  obtain ⟨hτ, hm⟩ := reg_of_H n τ m h i0 p j0 hτ0 H hH hH0
  obtain ⟨hA1, e1⟩ := cpull_detPP_kpt hg n τ m h i0 p hτ hm hne
  obtain ⟨hA2, e2⟩ := cube_side_mem P0 hg hW n β S i0 p x0 hS hgood
  refine ⟨hA1, hA2, ?_⟩
  rw [e1, e2]
  exact ord_slice_gen hg n τ m h i0 p j0 hτ0 hj0 H hH hH0 hinj hne hgood.nonneg hgood.ell hcls _

end Gen

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Asm1 =====
section

/-!
# S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
* `tauS`, `j0S`: the enumeration of the block `{k | β k ∈ S}`;
* `HS`, `YS`, `Vp`, `VS`: the correction divisors; **`cancel_VS`**: their signed cube sum is `0`;
* **`test_S`**: off `bad i0`, both sides avoid and `cpull det_S = cpull Θ_S + VS_S (p_{i0})`.
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

section Asm1

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **The per-`S` line test with its correction**, off the bad set of direction `i0`. -/
theorem test_S (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (n : ℕ)
    (β : Fin n → Fin 3) (i0 : Fin n) (x0 cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (q0 : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)
    (hq0 : kPl q0 = P0) (hm0 : ∀ l, kPl (m l) ≠ P0) (hmm : ∀ l l', kPl (m l) = kPl (m l') → l = l')
    (hcK : ((Multiplicative.toAdd (jacPicEquiv K F cK) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hx0 : ((Multiplicative.toAdd (jacPicEquiv K F x0) : Pic0K K F) : PicK K F) =
      clsK K F (W0 + ∑ i, Finsupp.single (kPl (m i)) 1) -
        (2 * (genusFK K F : ℤ) + r - 2) • clsK K F (Finsupp.single P0 1))
    (hf : ∀ S : Finset (Fin 3), Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r → F)
    (hfH : ∀ S l, hf S l ∈ LFK K F (HS P0 n β S r)) (hli : ∀ S, LinearIndependent K (hf S))
    (S : Finset (Fin 3)) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hp : p.left (IsLocalRing.closedPoint K) ∉ bad P0 n β i0 x0 cK c2 (Matrix.vecCons q0 m)) :
    Avoid (line K F n i0 p).left (dS n β m hf S) ∧
      Avoid ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0) ∧
      cpull (line K F n i0 p).left (dS n β m hf S) ((p ≫ prj K F n i0).left (IsLocalRing.closedPoint K)) =
        cpull ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0)
          ((p ≫ prj K F n i0).left (IsLocalRing.closedPoint K)) + VS P0 n β S i0 p m (kPl (p ≫ prj K F n i0)) := by
  obtain ⟨hO, hP0, hpm, hpp⟩ := facts_of_not_mem_bad P0 n β i0 x0 cK c2 m q0 hq0 p hp
  by_cases hS : β i0 ∈ S
  · obtain ⟨G, hG⟩ := isGoodFor_of_mem P0 hg hW hcK hc2 _ (hO S)
    have hτ0 := tauS_j0S n β S i0 hS
    have hj0 : ∀ j, tauS n β S j = i0 → j = j0S n β S i0 hS := fun j h => tauS_inj n β S (h.trans hτ0.symm)
    have hne : ∀ a : Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r, a ≠ Sum.inl (j0S n β S i0 hS) →
        ∀ j, a = Sum.inl j → tauS n β S j ≠ i0 := by
      rintro a ha j rfl h
      exact ha (by rw [hj0 j h])
    have hmem : i0 ∈ Finset.univ.filter (fun k => β k ∈ S) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
    have hH : clsK K F (HS P0 n β S r) = ((genusFK K F : ℤ) + r +
        ((Finset.univ.filter (fun k => β k ∈ S)).erase i0).card) • clsK K F (Finsupp.single P0 1) := by
      rw [HS, clsK_zsmul_c, Finset.card_erase_of_mem hmem, Nat.cast_pred (Finset.card_pos.mpr ⟨i0, hmem⟩)]
      module
    have hcls := cls_test P0 n β S i0 p x0 (tauS n β S) m (j0S n β S i0 hS) hτ0 (tauS_inj n β S)
      (tauS_iff n β S) hx0 hH hG
    obtain ⟨a1, a2, e⟩ := test_mem_gen P0 hg hW n β S i0 p x0 hS hG (tauS n β S) m (hf S) (j0S n β S i0 hS) hτ0
      hj0 (HS P0 n β S r) (hfH S) (fun a ha => H0_ptC P0 n β S (tauS n β S) m p i0 hP0 hm0 a (hne a ha))
      (fun a b ha hb e => inj_ptC n (tauS n β S) m p i0 (tauS_inj n β S) hpm hpp hmm a b (hne a ha) (hne b hb) e)
      (hli S) hcls
    refine ⟨a1, a2, e.trans ?_⟩
    rw [Zsl_eq n β S (tauS n β S) m p i0 (j0S n β S i0 hS) hτ0 (tauS_inj n β S) (tauS_iff n β S), VS, if_pos hS,
      Vp, YS, Finsupp.sub_apply]
    ring
  · have hW' : pt (Jac K F) ((p ≫ psiE P0 n β S i0) * x0) ∉ W P0 := (hO S).1.1
    have hτ : ∀ j, tauS n β S j ≠ i0 := fun j h => hS (by rw [← h]; exact tauS_mem n β S j)
    have hi0 : i0 ∉ Finset.univ.filter (fun k => β k ∈ S) := fun h => hS (Finset.mem_filter.mp h).2
    have hd : (HS P0 n β S r - Zall K F n (tauS n β S) m p).deg = (genusFK K F : ℤ) - 1 := by
      rw [PlacesK.Divisor.deg_sub, deg_Zall, HS, Finsupp.smul_single_one, deg_single']
      ring
    have he : ((Multiplicative.toAdd (jacPicEquiv K F ((p ≫ psiE P0 n β S i0) * x0)) : Pic0K K F) : PicK K F) =
        clsK K F (W0 - (HS P0 n β S r - Zall K F n (tauS n β S) m p)) -
          ((genusFK K F : ℤ) - 1) • clsK K F (Finsupp.single P0 1) := by
      rw [map_mul, jacPic_psiE, toAdd_mul, toAdd_ofAdd, AddSubgroup.coe_add, AddSubmonoidClass.coe_finsetSum, hx0,
        Finset.erase_eq_of_notMem hi0]
      simp only [coe_ajCls]
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← clsK_sum,
        Zall_split n β S (tauS n β S) m p (tauS_inj n β S) (tauS_iff n β S), HS]
      simp only [clsK_sub, clsK_add, clsK_zsmul_c]
      module
    have hell := ell_zero_of_not_mem_W P0 hg hW _ hd he hW'
    obtain ⟨a1, a2, e⟩ := test_not_mem P0 hg n β S i0 p x0 hS hW' (tauS n β S) m (hf S) hτ (HS P0 n β S r) (hfH S)
      (fun a => H0_ptC P0 n β S (tauS n β S) m p i0 hP0 hm0 a (fun j _ => hτ j))
      (fun a b e => inj_ptC n (tauS n β S) m p i0 (tauS_inj n β S) hpm hpp hmm a b (fun j _ => hτ j)
        (fun j _ => hτ j) e) (hli S) hell
    refine ⟨a1, a2, e.trans ?_⟩
    rw [VS, if_neg hS, Finsupp.coe_zero, Pi.zero_apply, add_zero]

end Asm1

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_NZS =====
section

/-!
# S4-ThetaCube, file NZS (D-C1, part 11): the determinants `det_k` are nonzero
* `detPP_ne_of_slice`: a nonzero slice forces `det_k ≠ 0`;
* `detPP_ne_zero_at`: off the bad set of a direction `i0`, the slice is nonzero (the two branches of `test_S`);
* `exists_not_mem_bad`: a `K`-point off the bad set (`J`acobson, `bad ≠ univ`);
* **`detPP_ne_zero`**: `det_k ≠ 0` for every block `S` (hypotheses of `cube_PP`, `n > 0`).
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

section NZS

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **Off the bad set of `i0`, `det_k ≠ 0`** (the slice computations of `test_S`). -/
theorem detPP_ne_zero_at (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (n : ℕ)
    (β : Fin n → Fin 3) (i0 : Fin n) (x0 cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (q0 : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)
    (hq0 : kPl q0 = P0) (hm0 : ∀ l, kPl (m l) ≠ P0) (hmm : ∀ l l', kPl (m l) = kPl (m l') → l = l')
    (hcK : ((Multiplicative.toAdd (jacPicEquiv K F cK) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hx0 : ((Multiplicative.toAdd (jacPicEquiv K F x0) : Pic0K K F) : PicK K F) =
      clsK K F (W0 + ∑ i, Finsupp.single (kPl (m i)) 1) -
        (2 * (genusFK K F : ℤ) + r - 2) • clsK K F (Finsupp.single P0 1))
    (hf : ∀ S : Finset (Fin 3), Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r → F)
    (hfH : ∀ S l, hf S l ∈ LFK K F (HS P0 n β S r)) (hli : ∀ S, LinearIndependent K (hf S))
    (S : Finset (Fin 3)) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hp : p.left (IsLocalRing.closedPoint K) ∉ bad P0 n β i0 x0 cK c2 (Matrix.vecCons q0 m)) :
    detPP K F n (tauS n β S) m (hf S) ≠ 0 := by
  obtain ⟨hO, hP0, hpm, hpp⟩ := facts_of_not_mem_bad P0 n β i0 x0 cK c2 m q0 hq0 p hp
  by_cases hS : β i0 ∈ S
  · obtain ⟨G, hG⟩ := isGoodFor_of_mem P0 hg hW hcK hc2 _ (hO S)
    have hτ0 := tauS_j0S n β S i0 hS
    have hj0 : ∀ j, tauS n β S j = i0 → j = j0S n β S i0 hS := fun j h => tauS_inj n β S (h.trans hτ0.symm)
    have hne : ∀ a : Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r, a ≠ Sum.inl (j0S n β S i0 hS) →
        ∀ j, a = Sum.inl j → tauS n β S j ≠ i0 := by
      rintro a ha j rfl h
      exact ha (by rw [hj0 j h])
    have hmem : i0 ∈ Finset.univ.filter (fun k => β k ∈ S) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩
    have hH : clsK K F (HS P0 n β S r) = ((genusFK K F : ℤ) + r +
        ((Finset.univ.filter (fun k => β k ∈ S)).erase i0).card) • clsK K F (Finsupp.single P0 1) := by
      rw [HS, clsK_zsmul_c, Finset.card_erase_of_mem hmem, Nat.cast_pred (Finset.card_pos.mpr ⟨i0, hmem⟩)]
      module
    have hcls := cls_test P0 n β S i0 p x0 (tauS n β S) m (j0S n β S i0 hS) hτ0 (tauS_inj n β S)
      (tauS_iff n β S) hx0 hH hG
    have hH0 : ∀ a, a ≠ Sum.inl (j0S n β S i0 hS) →
        HS P0 n β S r (kPl (ptC K F n (tauS n β S) m p a)) = 0 :=
      fun a ha => H0_ptC P0 n β S (tauS n β S) m p i0 hP0 hm0 a (hne a ha)
    have hsl := slice_ne_zero hg n (tauS n β S) m (hf S) i0 p (j0S n β S i0 hS) hτ0 hj0 (HS P0 n β S r) (hfH S)
      hH0 (fun a b ha hb e => inj_ptC n (tauS n β S) m p i0 (tauS_inj n β S) hpm hpp hmm a b (hne a ha)
        (hne b hb) e) (hli S) ((ellFK_of_clsK_eq hcls).symm.trans hG.ell).le
    obtain ⟨hτ, hm⟩ := reg_of_H n (tauS n β S) m (hf S) i0 p (j0S n β S i0 hS) hτ0 (HS P0 n β S r) (hfH S) hH0
    exact detPP_ne_of_slice hg n _ m _ i0 p hτ hm hsl
  · have hW' : pt (Jac K F) ((p ≫ psiE P0 n β S i0) * x0) ∉ W P0 := (hO S).1.1
    have hτ : ∀ j, tauS n β S j ≠ i0 := fun j h => hS (by rw [← h]; exact tauS_mem n β S j)
    have hi0 : i0 ∉ Finset.univ.filter (fun k => β k ∈ S) := fun h => hS (Finset.mem_filter.mp h).2
    have hd : (HS P0 n β S r - Zall K F n (tauS n β S) m p).deg = (genusFK K F : ℤ) - 1 := by
      rw [PlacesK.Divisor.deg_sub, deg_Zall, HS, Finsupp.smul_single_one, deg_single']
      ring
    have he : ((Multiplicative.toAdd (jacPicEquiv K F ((p ≫ psiE P0 n β S i0) * x0)) : Pic0K K F) : PicK K F) =
        clsK K F (W0 - (HS P0 n β S r - Zall K F n (tauS n β S) m p)) -
          ((genusFK K F : ℤ) - 1) • clsK K F (Finsupp.single P0 1) := by
      rw [map_mul, jacPic_psiE, toAdd_mul, toAdd_ofAdd, AddSubgroup.coe_add, AddSubmonoidClass.coe_finsetSum, hx0,
        Finset.erase_eq_of_notMem hi0]
      simp only [coe_ajCls]
      rw [Finset.sum_sub_distrib, Finset.sum_const, ← clsK_sum,
        Zall_split n β S (tauS n β S) m p (tauS_inj n β S) (tauS_iff n β S), HS]
      simp only [clsK_sub, clsK_add, clsK_zsmul_c]
      module
    have hell := ell_zero_of_not_mem_W P0 hg hW _ hd he hW'
    have hH0 : ∀ a, HS P0 n β S r (kPl (ptC K F n (tauS n β S) m p a)) = 0 :=
      fun a => H0_ptC P0 n β S (tauS n β S) m p i0 hP0 hm0 a (fun j _ => hτ j)
    have hsl := slice_ne_zero_const hg n (tauS n β S) m (hf S) i0 p hτ (HS P0 n β S r) (hfH S) hH0
      (fun a b e => inj_ptC n (tauS n β S) m p i0 (tauS_inj n β S) hpm hpp hmm a b (fun j _ => hτ j)
        (fun j _ => hτ j) e) (hli S) hell
    exact detPP_ne_of_slice hg n _ m _ i0 p (fun j _ l => ord_nonneg_of_mem_LFK (hfH S l) (hH0 (Sum.inl j)))
      (fun i l => ord_nonneg_of_mem_LFK (hfH S l) (hH0 (Sum.inr i))) hsl

/-- **`det_k ≠ 0` for every block `S`** (hypotheses of `cube_PP`, `0 < n`). -/
theorem detPP_ne_zero (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (n : ℕ)
    (hn : 0 < n) (β : Fin n → Fin 3) (x0 cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (q0 : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)
    (hq0 : kPl q0 = P0) (hm0 : ∀ l, kPl (m l) ≠ P0) (hmm : ∀ l l', kPl (m l) = kPl (m l') → l = l')
    (hcK : ((Multiplicative.toAdd (jacPicEquiv K F cK) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hx0 : ((Multiplicative.toAdd (jacPicEquiv K F x0) : Pic0K K F) : PicK K F) =
      clsK K F (W0 + ∑ i, Finsupp.single (kPl (m i)) 1) -
        (2 * (genusFK K F : ℤ) + r - 2) • clsK K F (Finsupp.single P0 1))
    (hx0g : pt (Jac K F) x0 ∈ Ogood P0 cK c2)
    (hf : ∀ S : Finset (Fin 3), Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r → F)
    (hfH : ∀ S l, hf S l ∈ LFK K F (HS P0 n β S r)) (hli : ∀ S, LinearIndependent K (hf S))
    (S : Finset (Fin 3)) : detPP K F n (tauS n β S) m (hf S) ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_not_mem_bad P0 hg n β ⟨0, hn⟩ x0 cK c2 (Matrix.vecCons q0 m) hx0g
  exact detPP_ne_zero_at P0 hg hW n β ⟨0, hn⟩ x0 cK c2 m q0 hq0 hm0 hmm hcK hc2 hx0 hf hfH hli S p hp

end NZS

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrNe =====
section

/-!
# S4-ThetaCube, file TrNe (D-C1, part 6): the open `ψ_S⁻¹ VJ` is nonempty
* `VJ_nonempty`: `VJ P0 d` is a nonempty open of `J` (`J` irreducible, `W ≠ J`, translated chart);
* `exists_blocks`: a map `a` with `Σ_{k ∈ s} [a k] = Zdiv T` when `#s = #T`;
* **`psiS_VJ_nonempty`**: `ψ_S⁻¹ VJ ≠ ∅` when `#blk = g` and `[d] = [Θ] - g[P0]`;
* **`trPP_blk`**: the block trace identity `ψ_S^* trJ d f = Σ_{k ∈ blk} pr_k^* f`, unconditionally.
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

section TrNe

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **The block trace identity on `X1^n`**, unconditionally (`#blk = g`, `[d] = [Θ] - g[P0]`). -/
theorem trPP_blk (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3))
    (hS : (blk n β S).card = genusFK K F) (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hd : ((Multiplicative.toAdd (jacPicEquiv K F d) : Pic0K K F) : PicK K F) =
      thetaK K F - (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1)) (f : Places.Rfin K F) :
    fpull (psiS P0 n β S).left (trJ d f) =
      ∑ k ∈ blk n β S, fpull (prj K F n k).left (phiX K F (incB K F f)) :=
  trPP_open P0 hg n β S hS d hd f (psiS_VJ_nonempty P0 hg n β S hS d hd)

end TrNe

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

section GrB

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **`Φ3^# det (grJ) = (det_k)^2`** (`#blk {b} = g` for `b ∈ S`, `[d] = [Θ] - g[P0]`, `f_l` regular at the `m_i`). -/
theorem ffMap_det_grJ (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) [IsDominant (Phi3 P0 n β).left]
    (S : Finset (Fin 3)) (hS : ∀ b ∈ S, (blk n β {b}).card = genusFK K F) (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hd : ((Multiplicative.toAdd (jacPicEquiv K F d) : Pic0K K F) : PicK K F) =
      thetaK K F - (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1)) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (fR : Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r → Places.Rfin K F)
    (hm : ∀ i l, 0 ≤ (kPl (m i)).ord (incB K F (fR l))) :
    (ffMap (Phi3 P0 n β).left).hom (grJ K F d S m fR).det =
      detPP K F n (tauS n β S) m (fun l => incB K F (fR l)) ^ 2 := by
  set M : Matrix (Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r)
      (Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r) (PP K F n).left.functionField :=
    Matrix.of fun a l => fpull (zPP K F n (tauS n β S) m a) (phiX K F (incB K F (fR l)))
  have hc : ∀ i l, (ffMap (Phi3 P0 n β).left).hom
      (fpull (toUnit (Jac K F ⊗ (Jac K F ⊗ Jac K F)) ≫ m i).left (phiX K F (incB K F (fR l)))) =
        M (Sum.inr i) l := by
    intro i l
    rw [← fpull_eq_ffMap]
    have hreg := (regAt_fpull (Phi3 P0 n β).left (toUnit (Jac K F ⊗ (Jac K F ⊗ Jac K F)) ≫ m i).left
      ((regAt_iff _ _).mpr (exists_stalk_of_ord hg (m i) _ (hm i l)
        (toUnit_comp_apply (m i) ((Phi3 P0 n β).left (genericPoint (PP K F n).left)))))).2
    rw [hreg, ← Over.comp_left, ← Category.assoc,
      toUnit_unique (Phi3 P0 n β ≫ toUnit (Jac K F ⊗ (Jac K F ⊗ Jac K F))) (toUnit (PP K F n))]
    rfl
  have hk : ∀ k l l', fpull (prj K F n k).left (phiX K F (incB K F (fR l * fR l'))) =
      fpull (prj K F n k).left (phiX K F (incB K F (fR l))) *
        fpull (prj K F n k).left (phiX K F (incB K F (fR l'))) := by
    intro k l l'
    rw [fpull_eq_ffMap, fpull_eq_ffMap, fpull_eq_ffMap, map_mul, map_mul, map_mul]
  have hent : (ffMap (Phi3 P0 n β).left).hom.mapMatrix (grJ K F d S m fR) = M.transpose * M := by
    ext l l'
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [grJ, Matrix.of_apply]
    rw [map_add, map_sum, map_sum, Matrix.mul_apply, Fintype.sum_sum_type]
    congr 1
    · have e1 : ∑ j, M.transpose l (Sum.inl j) * M (Sum.inl j) l' =
          ∑ k ∈ blk n β S, fpull (prj K F n k).left (phiX K F (incB K F (fR l * fR l'))) := by
        rw [sum_blk_tauS]
        exact Finset.sum_congr rfl fun j _ => (hk (tauS n β S j) l l').symm
      refine Eq.trans ?_ e1.symm
      rw [← sum_blk_fiber]
      exact Finset.sum_congr rfl fun b hb =>
        (ffMap_Phi3_fpull P0 n β b _).trans (trPP_blk P0 hg n β {b} (hS b hb) d hd _)
    · exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hc, hc, Matrix.transpose_apply]
  calc (ffMap (Phi3 P0 n β).left).hom (grJ K F d S m fR).det
      = (M.transpose * M).det := by rw [RingHom.map_det, hent]
    _ = M.det ^ 2 := by rw [Matrix.det_mul, Matrix.det_transpose, sq]

end GrB

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Asm2 =====
section

/-!
# S4-ThetaCube, file Asm2 (D-B4, part 6c): the pull-back of the cube divisor along `Φ3` and the assembly
* `cpull_PB`: `cpull` of `Φ3^* cubeZ` along any curve into `X1^n` is the signed sum of the seven `Θ` sides;
* **`cube_PP`**: `Φ3^* cubeZ` is the signed sum of the seven determinant divisors `dS` (by `eq_zero_of_lines`).
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

section Asm2

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **The cube relation on `X1^n`** (D-B4): `Φ3^* cubeZ` is the signed sum of the determinant divisors. -/
theorem cube_PP (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (n : ℕ)
    (β : Fin n → Fin 3) (x0 cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (q0 : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)
    (hq0 : kPl q0 = P0) (hm0 : ∀ l, kPl (m l) ≠ P0) (hmm : ∀ l l', kPl (m l) = kPl (m l') → l = l')
    (hcK : ((Multiplicative.toAdd (jacPicEquiv K F cK) : Pic0K K F) : PicK K F) =
        clsK K F W0 - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (hx0 : ((Multiplicative.toAdd (jacPicEquiv K F x0) : Pic0K K F) : PicK K F) =
      clsK K F (W0 + ∑ i, Finsupp.single (kPl (m i)) 1) -
        (2 * (genusFK K F : ℤ) + r - 2) • clsK K F (Finsupp.single P0 1))
    (hx0g : pt (Jac K F) x0 ∈ Ogood P0 cK c2)
    (hf : ∀ S : Finset (Fin 3), Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r → F)
    (hfH : ∀ S l, hf S l ∈ LFK K F (HS P0 n β S r)) (hli : ∀ S, LinearIndependent K (hf S))
    [IsDominant (Phi3 P0 n β).left] :
    JacDivisors.pullback (Phi3 P0 n β).left (cubeZ P0 x0) =
      dS n β m hf {0, 1, 2} - dS n β m hf {0, 1} - dS n β m hf {0, 2} - dS n β m hf {1, 2} +
        dS n β m hf {0} + dS n β m hf {1} + dS n β m hf {2} := by
  have hd : ∀ S, dS n β m hf S ∈ weilDivisors (PP K F n).left := fun S => div_mem_weilDivisors _
  have hd7 : dS n β m hf {0, 1, 2} - dS n β m hf {0, 1} - dS n β m hf {0, 2} - dS n β m hf {1, 2} +
      dS n β m hf {0} + dS n β m hf {1} + dS n β m hf {2} ∈ weilDivisors (PP K F n).left :=
    (weilDivisors _).add_mem ((weilDivisors _).add_mem ((weilDivisors _).add_mem ((weilDivisors _).sub_mem
      ((weilDivisors _).sub_mem ((weilDivisors _).sub_mem (hd _) (hd _)) (hd _)) (hd _)) (hd _)) (hd _)) (hd _)
  have hPB := JacDivisors.pullback_mem_weilDivisors (Phi3 P0 n β).left (cubeZ P0 x0)
  refine (sub_eq_zero.mp (eq_zero_of_lines ((weilDivisors _).sub_mem hd7 hPB)
    (fun i => bad P0 n β i x0 cK c2 (Matrix.vecCons q0 m)) (fun i => isClosed_bad P0 n β i x0 cK c2 _)
    (fun i => bad_ne_univ P0 n β i x0 cK c2 _ hg hx0g) (fun i => isSat_bad P0 n β i x0 cK c2 _)
    fun i p hp => ?_)).symm
  have t := fun S => test_S P0 hg hW n β i x0 cK c2 m q0 hq0 hm0 hmm hcK hc2 hx0 hf hfH hli S p hp
  obtain ⟨aPB, ePB⟩ := cpull_PB P0 hg n β x0 (line K F n i p) (t {0, 1, 2}).2.1 (t {0, 1}).2.1 (t {0, 2}).2.1
    (t {1, 2}).2.1 (t {0}).2.1 (t {1}).2.1 (t {2}).2.1
  have a7 := avoid_cube7 (line K F n i p).left (t {0, 1, 2}).1 (t {0, 1}).1 (t {0, 2}).1 (t {1, 2}).1
    (t {0}).1 (t {1}).1 (t {2}).1
  refine ⟨avoid_sub _ a7 aPB, ?_⟩
  rw [cpull_sub _ hd7 hPB a7 aPB, cpull_cube7 _ (hd {0, 1, 2}) (hd {0, 1}) (hd {0, 2}) (hd {1, 2}) (hd {0})
    (hd {1}) (hd {2}) (t {0, 1, 2}).1 (t {0, 1}).1 (t {0, 2}).1 (t {1, 2}).1 (t {0}).1 (t {1}).1 (t {2}).1, ePB]
  simp only [Function.locallyFinsuppWithin.coe_sub, Function.locallyFinsuppWithin.coe_add, Pi.sub_apply,
    Pi.add_apply]
  rw [(t {0, 1, 2}).2.2, (t {0, 1}).2.2, (t {0, 2}).2.2, (t {1, 2}).2.2, (t {0}).2.2, (t {1}).2.2, (t {2}).2.2]
  have hc := congrArg (fun D : Places.Divisor K F => D (kPl (p ≫ prj K F n i))) (cancel_VS P0 n β i p m)
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply] at hc
  linarith

end Asm2

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

section GrC

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **The cube divisor is principal up to `2`** (Gram determinants; `#blk {b} = g`, `[d] = [Θ] - g[P0]`). -/
theorem cubePrincipal_gram (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) [IsDominant (Phi3 P0 n β).left]
    (hsurj : Function.Surjective (Phi3 P0 n β).left) (hβ : ∀ b : Fin 3, (blk n β {b}).card = genusFK K F)
    (x0 d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hd : ((Multiplicative.toAdd (jacPicEquiv K F d) : Pic0K K F) : PicK K F) =
      thetaK K F - (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1)) {r : ℕ}
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (fR : ∀ S : Finset (Fin 3), Fin (Finset.univ.filter (fun k => β k ∈ S)).card ⊕ Fin r → Places.Rfin K F)
    (hm : ∀ S i l, 0 ≤ (kPl (m i)).ord (incB K F (fR S l)))
    (hne : ∀ S, detPP K F n (tauS n β S) m (fun l => incB K F (fR S l)) ≠ 0)
    (hcube : JacDivisors.pullback (Phi3 P0 n β).left (cubeZ P0 x0) =
      dS n β m (fun S l => incB K F (fR S l)) {0, 1, 2} - dS n β m (fun S l => incB K F (fR S l)) {0, 1} -
        dS n β m (fun S l => incB K F (fR S l)) {0, 2} - dS n β m (fun S l => incB K F (fR S l)) {1, 2} +
        dS n β m (fun S l => incB K F (fR S l)) {0} + dS n β m (fun S l => incB K F (fR S l)) {1} +
        dS n β m (fun S l => incB K F (fR S l)) {2}) :
    CubePrincipal P0 x0 := by
  obtain ⟨G, hGd⟩ : ∃ G : Finset (Fin 3) → (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left.functionField,
      ∀ S, G S = (grJ K F d S m (fR S)).det := ⟨_, fun _ => rfl⟩
  obtain ⟨D, hDd⟩ : ∃ D : Finset (Fin 3) → (PP K F n).left.functionField,
      ∀ S, D S = detPP K F n (tauS n β S) m (fun l => incB K F (fR S l)) := ⟨_, fun _ => rfl⟩
  have hG : ∀ S, (ffMap (Phi3 P0 n β).left).hom (G S) = D S ^ 2 := fun S => by
    rw [hGd, hDd]
    exact ffMap_det_grJ P0 hg n β S (fun b _ => hβ b) d hd m (fR S) (hm S)
  have hD0 : ∀ S, D S ≠ 0 := fun S => by rw [hDd]; exact hne S
  have hD2 : ∀ S, D S ^ 2 ≠ 0 := fun S => pow_ne_zero 2 (hD0 S)
  have hG0 : ∀ S, G S ≠ 0 := fun S e => hD2 S (by rw [← hG S, e, map_zero])
  have hc' : JacDivisors.pullback (Phi3 P0 n β).left (cubeZ P0 x0) =
      JacDivisors.div _ (D {0, 1, 2}) - JacDivisors.div _ (D {0, 1}) - JacDivisors.div _ (D {0, 2}) -
        JacDivisors.div _ (D {1, 2}) + JacDivisors.div _ (D {0}) + JacDivisors.div _ (D {1}) +
        JacDivisors.div _ (D {2}) := by
    rw [hcube]
    simp only [dS, hDd]
  have hA : G {0, 1, 2} * G {0} * G {1} * G {2} ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hG0 _) (hG0 _)) (hG0 _)) (hG0 _)
  have hB : G {0, 1} * G {0, 2} * G {1, 2} ≠ 0 := mul_ne_zero (mul_ne_zero (hG0 _) (hG0 _)) (hG0 _)
  have hh : G {0, 1, 2} * G {0} * G {1} * G {2} * (G {0, 1} * G {0, 2} * G {1, 2})⁻¹ ≠ 0 :=
    mul_ne_zero hA (inv_ne_zero hB)
  have hfm : (ffMap (Phi3 P0 n β).left).hom
      (G {0, 1, 2} * G {0} * G {1} * G {2} * (G {0, 1} * G {0, 2} * G {1, 2})⁻¹) =
      D {0, 1, 2} ^ 2 * D {0} ^ 2 * D {1} ^ 2 * D {2} ^ 2 * (D {0, 1} ^ 2 * D {0, 2} ^ 2 * D {1, 2} ^ 2)⁻¹ := by
    simp only [map_mul, map_inv₀, hG]
  have hA' : D {0, 1, 2} ^ 2 * D {0} ^ 2 * D {1} ^ 2 * D {2} ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hD2 _) (hD2 _)) (hD2 _)) (hD2 _)
  have hB' : D {0, 1} ^ 2 * D {0, 2} ^ 2 * D {1, 2} ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero (hD2 _) (hD2 _)) (hD2 _)
  have hsq : ∀ S, JacDivisors.div (PP K F n).left (D S ^ 2) =
      JacDivisors.div (PP K F n).left (D S) + JacDivisors.div (PP K F n).left (D S) := fun S => div_sq_eq (hD0 S)
  have hCZ := cubeZ_mem P0 x0
  have hE : JacDivisors.div _ (G {0, 1, 2} * G {0} * G {1} * G {2} * (G {0, 1} * G {0, 2} * G {1, 2})⁻¹) -
      (cubeZ P0 x0 + cubeZ P0 x0) ∈ weilDivisors (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left :=
    (weilDivisors _).sub_mem (div_mem_weilDivisors _) ((weilDivisors _).add_mem hCZ hCZ)
  have key : JacDivisors.pullback (Phi3 P0 n β).left
      (JacDivisors.div _ (G {0, 1, 2} * G {0} * G {1} * G {2} * (G {0, 1} * G {0, 2} * G {1, 2})⁻¹) -
        (cubeZ P0 x0 + cubeZ P0 x0)) = 0 := by
    rw [JacDivisors.pullback_sub _ (div_mem_weilDivisors _) ((weilDivisors _).add_mem hCZ hCZ),
      JacDivisors.pullback_add _ hCZ hCZ, JacDivisors.pullback_div _ hh, hfm, hc',
      JacDivisors.div_mul hA' (inv_ne_zero hB'), JacDivisors.div_inv hB',
      JacDivisors.div_mul (mul_ne_zero (mul_ne_zero (hD2 _) (hD2 _)) (hD2 _)) (hD2 _),
      JacDivisors.div_mul (mul_ne_zero (hD2 _) (hD2 _)) (hD2 _), JacDivisors.div_mul (hD2 _) (hD2 _),
      JacDivisors.div_mul (mul_ne_zero (hD2 _) (hD2 _)) (hD2 _), JacDivisors.div_mul (hD2 _) (hD2 _)]
    simp only [hsq]
    abel
  refine ⟨2, two_pos, _, hh, ?_⟩
  rw [two_nsmul]
  exact sub_eq_zero.mp (eq_zero_of_pullback_surj (Phi3 P0 n β).left hsurj hE key)

end GrC

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube =====
section

/-!
# Unit S4-ThetaCube (Theta B, lemmas L40-L42 of `S4_COREB_ROUTE.md` section 3): umbrella

For an algebraically closed `K` and a function field `F/K` of genus `g > 0`, with `J = Jac K F`:
* **`exists_cubePrincipal`**: for an infinite place `P0` and a generic `x0 ∉ W`, a positive multiple of the cube divisor
  `cubeZ P0 x0` on `J^3` is principal (`CubePrincipal`, the theorem of the cube for `Θ`). The proof pulls back along
  `Φ3 : X1^{3g} ⟶ J^3` (D-B4, `cube_PP`), descends the seven determinants through their Gram matrices (D-C1,
  `cubePrincipal_gram`), and picks the auxiliary data generically (D-C3: `exists_m_x0`, `exists_fR_HS`);
* **`degPoly_D`**: the inputs of S4-DegPoly for `c G := (polyEnd π G)^* D'`, `D' = τ_{x0}^* Θ + (τ_{x0} ∘ [-1])^* Θ`,
  `I := formTh K F g hdim`: `(D'^g) > 0` (`hD`), `hproj`, the quadratic relation `hquad` (from the cube relation via
  `DegPoly.quad_of_cube`), and `hzero`, unconditionally.
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

section Main

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **The theorem of the cube for `Θ`** (L41): some `x0 ∉ W` has `CubePrincipal P0 x0`. -/
theorem exists_cubePrincipal (hg : 0 < genusFK K F) :
    ∃ (P0 : Place K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F), pt (Jac K F) x0 ∉ W P0 ∧ CubePrincipal P0 x0 := by
  obtain ⟨v⟩ := PlacesK.nonempty_infPlace K F
  obtain ⟨W0, hW⟩ := exists_isCanonicalFK (K := K) (F := F)
  obtain ⟨cK, hcK⟩ := exists_cK (Sum.inr v) hW
  obtain ⟨c2, hc2⟩ := exists_c2 (K := K) (F := F) (Sum.inr v)
  obtain ⟨m, x0, hm0, hmm, hx0, hx0g⟩ := exists_m_x0 (Sum.inr v) cK c2 hg hW hc2
  obtain ⟨q0, hq0⟩ := exists_kPl_eq hg (Sum.inr v) (Sum.inr v)
  have hβ : ∀ b : Fin 3, (blk (3 * genusFK K F) (b3 (genusFK K F)) {b}).card = genusFK K F :=
    card_blk3 (genusFK K F)
  have := isDominant_Phi3 (Sum.inr v) hg (3 * genusFK K F) (b3 (genusFK K F)) hβ
  have hn : 0 < 3 * genusFK K F := by omega
  have hfR := fun S => exists_fR_HS (Sum.inr v) (fun P => Sum.inl_ne_inr) (3 * genusFK K F) (b3 (genusFK K F)) S
    (le_refl (genusFK K F)) hg
  choose fR hfH hli using hfR
  have hd : ((Multiplicative.toAdd (jacPicEquiv K F c2⁻¹) : Pic0K K F) : PicK K F) =
      thetaK K F - (genusFK K F : ℤ) • clsK K F (Finsupp.single (Sum.inr v) 1) := by
    rw [map_inv, toAdd_inv, AddSubgroup.coe_neg, hc2, neg_sub]
  refine ⟨Sum.inr v, x0, hx0g.1.1, cubePrincipal_gram (Sum.inr v) hg (3 * genusFK K F) (b3 (genusFK K F))
    (surjective_Phi3 (Sum.inr v) hg _ _ hβ) hβ x0 c2⁻¹ hd m fR
    (fun S i l => ord_nonneg_of_mem_LFK (hfH S l) (HS_apply_ne _ _ _ S _ (hm0 i)))
    (fun S => detPP_ne_zero (Sum.inr v) hg hW _ hn _ x0 cK c2 m q0 hq0 hm0 hmm hcK hc2 hx0 hx0g _ hfH hli S)
    (cube_PP (Sum.inr v) hg hW _ _ x0 cK c2 m q0 hq0 hm0 hmm hcK hc2 hx0 hx0g _ hfH hli)⟩

/-- **The inputs of S4-DegPoly for `D'`, unconditionally** (L42): `hD`, `hproj`, `hquad` and `hzero` for
`c G := (polyEnd π G)^* D'` and `I := formTh K F g hdim`, at one `P0` and one `x0 ∉ W` (independent of `g`, `π`). -/
theorem degPoly_D (hg : 0 < genusFK K F) :
    ∃ (P0 : Place K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F), pt (Jac K F) x0 ∉ W P0 ∧
      ∀ (g : ℕ) (hdim : ∀ x : (Jac K F).left, Order.height x ≤ g) (π : Jac K F ⟶ Jac K F) [IsMonHom π],
        ((∃ x : (Jac K F).left, (g : ℕ∞) ≤ Order.height x) → formTh K F g hdim (fun _ => cD P0 x0 π 1) ≠ 0) ∧
        (∀ G : ℤ[X], formTh K F g hdim (fun _ => cD P0 x0 π G) =
          (degree (IsogDegB.polyEnd π G).left : ℤ) * formTh K F g hdim (fun _ => cD P0 x0 π 1)) ∧
        (∀ a b : ℤ[X], ∃ e : AlgebraicCycle (Jac K F).left ℤ, ∀ n : ℤ,
          cD P0 x0 π (n * a + b) - (n ^ 2 • cD P0 x0 π a + n • e + cD P0 x0 π b) ∈
            DegPoly.numKer (formTh K F g hdim)) ∧
        cD P0 x0 π 0 ∈ DegPoly.numKer (formTh K F g hdim) := by
  obtain ⟨P0, x0, hx0, hZ⟩ := exists_cubePrincipal hg
  exact ⟨P0, x0, hx0, fun g hdim π _ => ⟨hD_D P0 hg x0 hx0 g hdim π, hproj_D P0 hg x0 hx0 g hdim π,
    quad_D P0 hg x0 hx0 g hdim π hZ, hzero_D P0 hg x0 hx0 g hdim π⟩⟩

end Main

end RamanujanPetersson.ThetaCube


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
/-- **Values of `π_J⁰`**: a `K`-point `a` of `J` over `D(u0) ∩ D(Φ u0)` has `[a ≫ π_J⁰] = σ_*[a] + cTheta`. -/
theorem jacPicEquiv_piJ0 (a : 𝟙_ (Over (Spec (.of (kbar Fq Ω)))) ⟶ Jac (kbar Fq Ω) (Fbar Fq F Ω))
    (z : BRing (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) →ₐ[kbar Fq Ω] kbar Fq Ω)
    (ha : a.left (IsLocalRing.closedPoint (kbar Fq Ω)) =
      jX0 (kbar Fq Ω) (Fbar Fq F Ω) (kpt (z.comp (IsScalarTower.toAlgHom (kbar Fq Ω)
        (LawRing (kbar Fq Ω) (Fbar Fq F Ω)) (BRing (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω)))))))) :
    ((Multiplicative.toAdd (jacPicEquiv _ _ (a ≫ piJ0 Fq F Ω hk)) : Pic0K _ _) : PicK _ _) =
      sigPic Fq F Ω hk ((Multiplicative.toAdd (jacPicEquiv _ _ a) : Pic0K _ _) : PicK _ _) +
        cTheta Fq F Ω hk :=
  cls_mor_hom _ (PhiS_u0_ne Fq F Ω hk) (sigPic Fq F Ω hk)
    (fun y => by rw [Zdiv_ptSet_PhiS, sigPic_mk]) a z ha

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Val3 =====
section

/-!
# S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`

Generic: `cls_mul` (classes of products of `K`-points add), `comp_mul_toUnit` (`a ≫ (ψ * (toUnit ≫ c)) = (a ≫ ψ) * c`).
For `J = J_{F-bar}`: `cPt` (the point of class `-cTheta`), `cls_cPt`, **`piJ`**, **`jacPicEquiv_piJ`**.
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

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

set_option synthInstance.maxHeartbeats 100000 in
/-- **Values of `π_J`** on `K`-points over `D(u0) ∩ D(Φ u0)`: `[a ≫ π_J] = σ_*[a]`. -/
theorem jacPicEquiv_piJ (a : 𝟙_ (Over (Spec (.of (kbar Fq Ω)))) ⟶ Jac (kbar Fq Ω) (Fbar Fq F Ω))
    (z : BRing (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) →ₐ[kbar Fq Ω] kbar Fq Ω)
    (ha : a.left (IsLocalRing.closedPoint (kbar Fq Ω)) =
      jX0 (kbar Fq Ω) (Fbar Fq F Ω) (kpt (z.comp (IsScalarTower.toAlgHom (kbar Fq Ω)
        (LawRing (kbar Fq Ω) (Fbar Fq F Ω)) (BRing (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω)))))))) :
    ((Multiplicative.toAdd (jacPicEquiv _ _ (a ≫ piJ Fq F Ω hk)) : Pic0K _ _) : PicK _ _) =
      sigPic Fq F Ω hk ((Multiplicative.toAdd (jacPicEquiv _ _ a) : Pic0K _ _) : PicK _ _) := by
  rw [piJ, comp_mul_toUnit, cls_mul, jacPicEquiv_piJ0 Fq F Ω hk a z ha, cls_cPt, add_neg_cancel_right]

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

variable (ψ : Jac K F ⟶ Jac K F) (s : PicK K F ≃+ PicK K F) (W : (Jac K F).left.Opens)

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
/-- **`π_J` is a homomorphism of group objects.** -/
instance isMonHom_piJ : IsMonHom (piJ Fq F Ω hk) :=
  isMonHom_of_cls (piJ Fq F Ω hk) (sigPic Fq F Ω hk)
    (eJ (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω)))).opensRange
    (dense_eJ (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) (PhiS_u0_ne Fq F Ω hk)) fun a ha => by
    obtain ⟨z, hz⟩ := ptW (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) a ha
    exact jacPicEquiv_piJ Fq F Ω hk a z hz

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_All =====
section

/-!
# S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`

Generic: `exists_kpt_mem` (every nonempty open of `J` contains a `K`-point), `invMul a` (`x ↦ x⁻¹ * a`),
`cls_all` (a homomorphism acting through `s` on the classes of the `K`-points over a dense open does so everywhere).
For `J = J_{F-bar}`: **`jacPicEquiv_piJ_all`**, **`piBar_jacPicEquiv_piJ`** (review R4, through `Ψ : PicBar ≃+ PicK`).
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

section Spec

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

set_option synthInstance.maxHeartbeats 100000 in
/-- **Values of `π_J` on all `K`-points**: `[a ≫ π_J] = σ_*[a]`. -/
theorem jacPicEquiv_piJ_all (a : 𝟙_ (Over (Spec (.of (kbar Fq Ω)))) ⟶ Jac (kbar Fq Ω) (Fbar Fq F Ω)) :
    ((Multiplicative.toAdd (jacPicEquiv _ _ (a ≫ piJ Fq F Ω hk)) : Pic0K _ _) : PicK _ _) =
      sigPic Fq F Ω hk ((Multiplicative.toAdd (jacPicEquiv _ _ a) : Pic0K _ _) : PicK _ _) :=
  cls_all (piJ Fq F Ω hk) (sigPic Fq F Ω hk)
    (eJ (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω)))).opensRange
    (dense_eJ (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) (PhiS_u0_ne Fq F Ω hk)) (fun b hb => by
      obtain ⟨z, hz⟩ := ptW (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) b hb
      exact jacPicEquiv_piJ Fq F Ω hk b z hz) a

set_option synthInstance.maxHeartbeats 100000 in
/-- **`π_J` is the arithmetic Frobenius `π` on `Pic(X-bar)`** (review R4), through `Ψ : PicBar ≃+ PicK`. -/
theorem piBar_jacPicEquiv_piJ (a : 𝟙_ (Over (Spec (.of (kbar Fq Ω)))) ⟶ Jac (kbar Fq Ω) (Fbar Fq F Ω)) :
    (Psi Fq F Ω hk).symm ((Multiplicative.toAdd (jacPicEquiv _ _ (a ≫ piJ Fq F Ω hk)) : Pic0K _ _) : PicK _ _) =
      RamanujanPetersson.PicDescent.piBar Ω hk ((Psi Fq F Ω hk).symm ((Multiplicative.toAdd (jacPicEquiv _ _ a) : Pic0K _ _) : PicK _ _)) := by
  rw [jacPicEquiv_piJ_all, Psi_symm_sigPic]

end Spec

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

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

/-- **`dψ = 1`** for a homomorphism `ψ = mor φ · (translation by c)`, when every `K[ε]`-point of `D(φ u0)` kills the
`ε`-part of `φ(S_g)` (the `q`-Frobenius case). -/
theorem dφ_eq_one (hφ : φ (lawPre K F).u0 ≠ 0)
    (H : ∀ (f : BRing φ →ₐ[K] DualNumber K) (s : SymRing K (Places.Rfin K F) (genusFK K F)),
      (f (gB φ s)).snd = 0)
    (c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (ψ : Jac K F ⟶ Jac K F) [IsMonHom ψ]
    (hψ : ψ = mor φ hφ * (toUnit _ ≫ c)) : IsogDegB.dφ ψ = 1 := by
  have : IsDomain (BRing φ) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (vA_ne φ hφ))
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum (BRing φ)) := inferInstance
  obtain ⟨b, hb⟩ := exists_kpt_mem (eJ φ).opensRange ⟨(eJ φ) p, Scheme.Hom.mem_opensRange.2 ⟨p, rfl⟩⟩
  refine MonoidHom.ext fun t => ?_
  rw [MonoidHom.one_apply]
  have h0 : IsogDegB.ι0 K ≫ (t.1 * (toUnit _ ≫ b)) = b := by
    rw [MonObj.comp_mul, IsogDegB.tan_spec, ← Category.assoc,
      toUnit_unique (IsogDegB.ι0 K ≫ toUnit _) (𝟙 _), Category.id_comp, _root_.one_mul]
  have hW : (t.1 * (toUnit _ ≫ b)).left (IsLocalRing.closedPoint (DualNumber K)) ∈ (eJ φ).opensRange := by
    have h1 := IsogDegB.DS_eq_closedPoint K ((IsogDegB.ι0 K).left (IsLocalRing.closedPoint K))
    rw [← h1, ← comp_left_cp, h0]
    exact hb
  obtain ⟨e, he⟩ := comp_mor_const φ hφ H _ hW
  have h1 : (t.1 * (toUnit _ ≫ b)) ≫ ψ = toUnit _ ≫ (e * c) := by
    rw [hψ, MonObj.comp_mul, he, ← Category.assoc,
      toUnit_unique ((t.1 * (toUnit _ ≫ b)) ≫ toUnit _) (toUnit _), ← MonObj.comp_mul]
  rw [MonObj.mul_comp] at h1
  have h2 : t.1 ≫ ψ = toUnit _ ≫ ((e * c) * (b ≫ ψ)⁻¹) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← h1, ← Category.assoc, _root_.mul_inv_cancel_right]
  exact tan_eq_one_of_const (IsogDegB.dφ ψ t) _ ((IsogDegB.dφ_val ψ t).trans h2)

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
/-- **`dπ_J = 1`**: the `q`-Frobenius `π_J` of `J = J_{F-bar}` acts trivially on the tangent space at `0`. -/
theorem dφ_piJ : IsogDegB.dφ (piJ Fq F Ω hk) = 1 :=
  dφ_eq_one _ (PhiS_u0_ne Fq F Ω hk) (snd_PhiS Fq F Ω hk) (cPt Fq F Ω hk) (piJ Fq F Ω hk) rfl

end Tan

end RamanujanPetersson.JacFrob


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

set_option synthInstance.maxHeartbeats 100000 in
/-- `π_J` acts on `J(k-bar) ≃ Pic⁰(X-bar)` as `piBar0` (review R4). -/
theorem Psi0Equiv_symm_piJ (a : 𝟙_ (Over (Spec (.of (kbar Fq Ω)))) ⟶ Jac (kbar Fq Ω) (Fbar Fq F Ω)) :
    (Psi0Equiv Fq F Ω hk).symm (Multiplicative.toAdd (jacPicEquiv _ _ (a ≫ piJ Fq F Ω hk))) =
      piBar0 Fq F Ω hk ((Psi0Equiv Fq F Ω hk).symm (Multiplicative.toAdd (jacPicEquiv _ _ a))) :=
  Subtype.ext (piBar_jacPicEquiv_piJ Fq F Ω hk a)

set_option synthInstance.maxHeartbeats 100000 in
/-- **The ring map `ℤ[π] → End(J)`**: `(PQ)(π_J) = Q(π_J) ≫ P(π_J)` (additivity: `IsogDegB.polyEnd_add`). -/
theorem polyEnd_mul_piJ (P Q : ℤ[X]) :
    IsogDegB.polyEnd (piJ Fq F Ω hk) (P * Q) =
      IsogDegB.polyEnd (piJ Fq F Ω hk) Q ≫ IsogDegB.polyEnd (piJ Fq F Ω hk) P :=
  polyEnd_mul_of_cls (piJ Fq F Ω hk) (Psi0Equiv Fq F Ω hk).symm (piBar0 Fq F Ω hk) (Psi0Equiv_symm_piJ Fq F Ω hk) P Q

set_option synthInstance.maxHeartbeats 100000 in
/-- **`Ker F(π_J)(k-bar) ≃ ker (F(π) on Pic⁰(X-bar))`.** -/
noncomputable def kerPtsEquiv_piJ (P : ℤ[X]) :
    IsogDegA.kerPts (Jac (kbar Fq Ω) (Fbar Fq F Ω)) (IsogDegB.polyEnd (piJ Fq F Ω hk) P) ≃
      LinearMap.ker (aeval (piBar0 Fq F Ω hk) P) :=
  kerPtsEquiv (piJ Fq F Ω hk) (Psi0Equiv Fq F Ω hk).symm (piBar0 Fq F Ω hk) (Psi0Equiv_symm_piJ Fq F Ω hk) P

set_option synthInstance.maxHeartbeats 100000 in
/-- **`deg F(π_J) = #ker (F(π) on Pic⁰(X-bar))` for `p ∤ F(0)`** (the `deg_eq_card_ker` field of `DegreeData`). -/
theorem degree_polyEnd_piJ (P : ℤ[X]) (hp : ¬ ((ringChar Fq : ℕ) : ℤ) ∣ P.coeff 0) :
    IsogDegA.degree (IsogDegB.polyEnd (piJ Fq F Ω hk) P).left =
      Nat.card (LinearMap.ker (aeval (piBar0 Fq F Ω hk) P)) := by
  have : CharP (kbar Fq Ω) (ringChar Fq) :=
    charP_of_injective_algebraMap (algebraMap Fq (kbar Fq Ω)).injective _
  exact degree_polyEnd_eq_card_ker (piJ Fq F Ω hk) (dφ_piJ Fq F Ω hk) (ringChar Fq) (Psi0Equiv Fq F Ω hk).symm
    (piBar0 Fq F Ω hk) (Psi0Equiv_symm_piJ Fq F Ω hk) P hp

end Spec

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_CoreB_Data =====
section

/-!
# Core B, O3 (L43): degree data for `ℤ[π]` on `Pic⁰(X-bar)`

* `exists_degreeData`: `∃ gD, Nonempty (DegreeData (piBar0 Fq F Ω hk) gD (ringChar Fq))`.
  Genus `0`: `Pic⁰` is trivial (`Def_RP_CoreB_Triv`). Positive genus: `degreeDataOfQuad` with
  `deg F := degree F(π_J)`, the theta form `formTh` of S4-ThetaCube and the bound `exists_dim_Jac`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open CategoryTheory AlgebraicGeometry
open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places RamanujanPetersson.ThetaCube

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

set_option synthInstance.maxHeartbeats 100000 in
/-- **L43.** Degree data for `ℤ[π]` on `Pic⁰(X-bar)`. -/
theorem exists_degreeData : ∃ gD : ℕ, Nonempty (DegreeData (piBar0 Fq F Ω hk) gD (ringChar Fq)) := by
  by_cases hg : genusFK (kbar Fq Ω) (Fbar Fq F Ω) = 0
  · have := subsingleton_PicBar0_of_genus_zero Fq F Ω hk hg
    exact ⟨0, ⟨degreeDataOfSubsingleton _ _⟩⟩
  · obtain ⟨P0, x0, -, hD⟩ := degPoly_D (Nat.pos_of_ne_zero hg)
    obtain ⟨g, hdim, hx⟩ := exists_dim_Jac (kbar Fq Ω) (Fbar Fq F Ω)
    obtain ⟨h1, h2, h3, h4⟩ := hD g hdim (piJ Fq F Ω hk)
    refine ⟨g, ⟨DegPoly.degreeDataOfQuad (piBar0 Fq F Ω hk) g (ringChar Fq) (formTh _ _ g hdim)
      (cD P0 x0 (piJ Fq F Ω hk)) (fun G => IsogDegA.degree (IsogDegB.polyEnd (piJ Fq F Ω hk) G).left)
      (h1 hx) h2 h3 h4 ?_ ?_ ?_⟩⟩
    · intro P Q
      show IsogDegA.degree (IsogDegB.polyEnd (piJ Fq F Ω hk) (P * Q)).left = _
      rw [polyEnd_mul_piJ, IsogDegA.degree_comp_left']
    · intro P
      show IsogDegA.degree (IsogDegB.polyEnd (piJ Fq F Ω hk) P).left = 0 ↔ _
      rw [IsogDegB.degree_eq_zero_iff, (kerPtsEquiv_piJ Fq F Ω hk P).infinite_iff]
      exact Set.infinite_coe_iff
    · intro P hp
      exact degree_polyEnd_piJ Fq F Ω hk P hp

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

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- **CB1.** `A = Pic(X̄)[l^∞]` is `l`-divisible for every prime `l ∤ q`. -/
theorem divisible_Aℓ (l : ℕ) [Fact l.Prime] (hlq : ¬ l ∣ Fintype.card Fq) :
    ∀ y : Aℓ Ω hk l, ∃ z, l • z = y := by
  obtain ⟨gD, ⟨D⟩⟩ := exists_degreeData Fq F Ω hk
  have hg := (zeta_link Fq F Ω hk D).1
  subst hg
  have hT := D.card_tors l (not_ringChar_dvd Fq l hlq)
  obtain ⟨k0, hdiv, b1, hb1, M, -, -, -, -, -, hdivi, hcard, -⟩ := tate_rank_Pic (Ω := Ω) hk l hlq
  exact hdivi.1 (hcard.1 ((Nat.card_congr (torsEquiv Fq F Ω hk l)).trans hT))

end RamanujanPetersson.CoreB


end


