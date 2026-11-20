-- Prove2me | Definitions.Def_RPLib_F2_061
-- name    : RPLib_F2_061
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T21:44:35.881185+00:00
-- url     : https://prove2.me/theorems/0698a3fe-329e-459a-8565-0f6554e59b63
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 061 of 70
-- statement:
--   File 061 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
--   * `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
--   * `S4.Def_RP_ThetaCube_Proj`: S4-ThetaCube, T7: the projection formula and positivity for pulled-back divisors (L42 inputs)
--   * `S4.Def_RP_ThetaCube_Cube`: S4-ThetaCube, file Cube (T5a): numerical triviality of pulled-back principal multiples
--   * `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
--   * `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
--   * `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
--   * `S4.Def_RP_ThetaCube_Cof`: S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
--   * `S4.Def_RP_ThetaCube_Eff`: S4-ThetaCube, file Eff (D-B3, part 2): the residual divisor of a slice of `det_k`
--   * `S4.Def_RP_ThetaCube_Rank`: S4-ThetaCube, file Rank (D-B4, part 1): the slices do not vanish
--   * `S4.Def_RP_ThetaCube_NZ`: S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
--   * `S4.Def_RP_ThetaCube_Maps`: S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
--   * `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
--   * `S4.Def_RP_ThetaCube_Gen`: S4-ThetaCube, file Gen (D-B4, part 6a): the line test at every point of the line
--   * `S4.Def_RP_ThetaCube_NZS`: S4-ThetaCube, file NZS (D-C1, part 11): the determinants `det_k` are nonzero
--   * `S4.Def_RP_ThetaCube_Pick`: S4-ThetaCube, file Pick (D-C3, part 1): a generic choice of the auxiliary points `m`
--   * `S4.Def_RP_ThetaCube_Cst`: S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
--   * `S4.Def_RP_ThetaCube_TrPP`: S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
--   * `S4.Def_RP_ThetaCube_Hook`: S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_060

/-!
# Ramanujan-Petersson curve library (flat edition), file 061 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
* `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
* `S4.Def_RP_ThetaCube_Proj`: S4-ThetaCube, T7: the projection formula and positivity for pulled-back divisors (L42 inputs)
* `S4.Def_RP_ThetaCube_Cube`: S4-ThetaCube, file Cube (T5a): numerical triviality of pulled-back principal multiples
* `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
* `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
* `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `S4.Def_RP_ThetaCube_Cof`: S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
* `S4.Def_RP_ThetaCube_Eff`: S4-ThetaCube, file Eff (D-B3, part 2): the residual divisor of a slice of `det_k`
* `S4.Def_RP_ThetaCube_Rank`: S4-ThetaCube, file Rank (D-B4, part 1): the slices do not vanish
* `S4.Def_RP_ThetaCube_NZ`: S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
* `S4.Def_RP_ThetaCube_Maps`: S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
* `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
* `S4.Def_RP_ThetaCube_Gen`: S4-ThetaCube, file Gen (D-B4, part 6a): the line test at every point of the line
* `S4.Def_RP_ThetaCube_NZS`: S4-ThetaCube, file NZS (D-C1, part 11): the determinants `det_k` are nonzero
* `S4.Def_RP_ThetaCube_Pick`: S4-ThetaCube, file Pick (D-C3, part 1): a generic choice of the auxiliary points `m`
* `S4.Def_RP_ThetaCube_Cst`: S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
* `S4.Def_RP_ThetaCube_TrPP`: S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
* `S4.Def_RP_ThetaCube_Hook`: S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaSquare_Mult2 =====
section

/-!
# Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)

* `avoid_Theta`: a map to `J` with one point off `W` avoids `Θ`;
* `kappa`: the plus-curve chart map `κ = Spec (lawMapPlus) : Spec R2 → X0`, `jMap_transl`, `kappa_kpt`;
* `lawMapPlus_normS`: `κ^* (Nm t) = t · ∏_{i ≠ i0} a_i(t)`;
* `fpull_kappa`, `ord_fpull_kappa`: `κ^* (Nm t)` has order one at a `K`-point `x` when `t` is a uniformizer at
  `ptR2 x` with no zero at the other points `a_i`;
* **`cpull_kappa_eq_one`**: `(τ ∘ κ)^* Θ` has multiplicity exactly one at every `K`-point `x` of the plus-curve
  (`τ = τ_{c_φ⁻¹}`, `φ = ptR2 x`): lower bound by `exists_eta` + `cpull_pos`, upper bound by `cpull_le_ord` with the
  norm `Nm t` (`normS_mem_eta`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section Mult2

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

variable (hg : 0 < genusFK K F) (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
  (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)

set_option maxHeartbeats 1000000 in
include hg hc in
/-- Upper bound: the multiplicity is at most the order of `κ^* (Nm t)`, which is one. -/
theorem cpull_kappa_le_one [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K)
    (hA' : Avoid (kappa c0 a i0) (JacDivisors.pullback (tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0))) :
    cpull (kappa c0 a i0) (JacDivisors.pullback (tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0)) (kpt x) ≤ 1 := by
  obtain ⟨t, ht, ht2, htS⟩ := exists_unif (ptR2 c0 a i0 x) ((Finset.univ.erase i0).image a)
    (not_mem_image_plus c0 a i0 x)
  have hcst : ∀ i ∈ Finset.univ.erase i0, a i t ≠ 0 := fun i hi => htS _ (Finset.mem_image_of_mem a hi)
  have hord := ord_kpt_lawMapPlus c0 a i0 x ht ht2 hcst
  have hLN0 : lawMapPlus c0 a i0 (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t)) ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero, Scheme.ord_zero] at hord
    exact zero_ne_one hord
  have hs0 : (Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom
      (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t)) ≠ 0 := fun h =>
    hLN0 (by rw [injective_ΓSpecIso_inv _ (h.trans (map_zero _).symm), map_zero])
  have hg0 : (X0 K F).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom
      (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t))) ≠ 0 := fun h =>
    hs0 (Scheme.germToFunctionField_injective (X0 K F) ⊤ (h.trans (map_zero _).symm))
  have hle := cpull_le_ord (kappa c0 a i0) (pullback_mem_weilDivisors _ (Theta P0)) hA' hg0
    (avoid_div_kappa c0 a i0 hLN0) (kpt x) (fun z _ hz1 => by
      rw [pullback_tauX_apply P0 hg, div_apply]
      split_ifs with hz
      · have hN := normS_mem_eta P0 hg c hc (ptR2 c0 a i0 x) (fun h0 => ht2 (by rw [h0]; exact Submodule.zero_mem _)) ht
          (x.comp (lawMapPlus c0 a i0)) (mem_ptSet_plus c0 a i0 x) (eq_of_mem_ptSet_plus c0 a i0 x hcst) hz
        have hzr : z ∉ (X0 K F).basicOpen ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom
            (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t))) := by
          rw [mem_basicOpen_X0, not_not]
          exact hN
        have := ord_germ_pos (show z ∈ (⊤ : (X0 K F).Opens) from trivial) hz1 hs0 hzr
        omega
      · exact ord_germ_nonneg _ trivial)
  rwa [fpull_kappa, hord] at hle

include hg hc in
/-- **Multiplicity one along the plus-curve** (F6b): at every `K`-point `x` of `Spec R2`, the pull-back of `Θ`
along `τ_{c_φ⁻¹} ∘ κ` (`φ = ptR2 x`) has multiplicity exactly one. -/
theorem cpull_kappa_eq_one [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K)
    (hA : Avoid (kappa c0 a i0 ≫ tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0)) :
    cpull (kappa c0 a i0 ≫ tauX (c (ptR2 c0 a i0 x))⁻¹) (Theta P0) (kpt x) = 1 := by
  have hD := theta_mem_weilDivisors P0 hg
  rw [cpull_comp _ _ hD hA]
  have hA' := avoid_pullback _ _ hD hA
  exact le_antisymm (cpull_kappa_le_one P0 c0 a i0 hg c hc x hA') (one_le_cpull_kappa P0 c0 a i0 hg c hc x hA')

end Mult2

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve1 =====
section

/-!
# Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)

* `fe P0 e = AJ ≫ transl e : X1 → J` (`p ↦ AJ(p) · e`), `feX` its underlying scheme map, `comp_fe`, `mem_W_fe`;
* **`Dc P0 e := cpull (feX P0 e) Θ`**, a cycle on the curve `X1`; `Dc_nonneg`, `Dc_eq_zero` (support in `f_e⁻¹ W`);
* `plusX` is an open immersion (`ι2`), and `plusX ≫ f_{cE · d} = τ_d ∘ κ` (`plusX_fe`);
* **`Dc_plusX_eq_one`**: `D_e` has multiplicity exactly one at the point `plusX (kpt x)` when `e = cE · c_φ⁻¹`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section Curve1

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

variable (hg : 0 < genusFK K F)

include hg in
/-- **Support**: `D_e` vanishes off `f_e⁻¹ W`. -/
theorem Dc_eq_zero (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {y : X1 K F} (hy : feX P0 e y ∉ W P0) :
    Dc P0 e y = 0 := by
  by_cases hA : Avoid (feX P0 e) (Theta P0)
  · exact cpull_eq_zero_of _ (theta_mem_weilDivisors P0 hg) hA (isClosed_W P0).isOpen_compl hy
      (fun w hw => theta_eq_zero_of_not_mem P0 hw)
  · rw [Dc, cpull, dif_neg (fun h => hA h.2)]
    rfl

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

variable (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
  (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)

end Curve1

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaCube_Proj =====
section

/-!
# S4-ThetaCube, T7: the projection formula and positivity for pulled-back divisors (L42 inputs)

For an abelian variety `A` (proper integral group object over an algebraically closed field) with
factorial stalks, an endomorphism `φ`, a point `b` and an effective Weil divisor `D` whose support
avoids the image of the generic point under `φ ≫ transl b`:
* `cpull_mem_weilDivisors`: the Cartier pull-back of a Weil divisor is a Weil divisor.
* `iform_cpull_comp`: `((φ ≫ τ_b)^* D)^g = deg φ · (D^g)` (projection formula, `deg φ = 0` if not dominant).
* `iform_cpull_transl`: `((τ_b)^* D)^g = (D^g)`.
* `iform_Theta_pos`: `0 < (Θ^g)` on the Jacobian.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB RamanujanPetersson.IntersectC RamanujanPetersson.ThetaSquare

universe u

section Weil

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

end Weil

section Proj

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left] [IsLocallyNoetherian A.left]
  [∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x)]

end Proj

section Theta

open Polynomial
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **L42 (positivity)**: `0 < (Θ^g)`. -/
theorem iform_Theta_pos (hg : 0 < genusFK K F) (g : ℕ)
    (hdim : ∀ x : (Jac K F).left, Order.height x ≤ g)
    (hg' : ∃ x : (Jac K F).left, (g : ℕ∞) ≤ Order.height x) :
    0 < iform (Jac K F) g hdim (fun _ => Theta P0) := by
  have hufd : ∀ x : (Jac K F).left, UniqueFactorizationMonoid ((Jac K F).left.presheaf.stalk x) :=
    fun x => inferInstance
  rw [iform_eq_inumZ (Jac K F) hufd g hdim _ (fun _ => theta_mem_weilDivisors P0 hg)
      (fun _ z => Theta_nonneg P0 z),
    inumZ_of (Jac K F) g hdim _ (fun _ => support_effI_Theta_ne_top P0 hg)]
  exact_mod_cast inum_pos (Jac K F) hufd hdim hg' (theta_mem_weilDivisors P0 hg)
    (support_effI_Theta_ne_top P0 hg) (hsep_Theta P0 hg)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cube =====
section

/-!
# S4-ThetaCube, file Cube (T5a): numerical triviality of pulled-back principal multiples

* general `cpull` facts: `avoid_zero`, `cpull_zero`, `avoid_neg`, `cpull_neg`, `avoid_sub`, `cpull_sub`,
  `avoid_nsmul`, `cpull_nsmul`;
* `div_mem_numKer`: principal divisors of `J` lie in `numKer` of the intersection form;
* **`mem_numKer_of_cpull_div`**: if `n • Z = div h` on any `P` and `L : J ⟶ P` avoids `Z`, then `L^* Z ∈ numKer`
  (the interface for the J^3 cube: `P = J^3`, `L = (α, β, γ)`);
* `cubeC c p q r`: the seven-term cube combination (hom-group law `*`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- Principal divisors of `J` are numerically trivial. -/
theorem div_mem_numKer (g : ℕ) (hdim : ∀ x : (Jac K F).left, Order.height x ≤ g)
    (u : (Jac K F).left.functionField) :
    JacDivisors.div (Jac K F).left u ∈ DegPoly.numKer (formTh K F g hdim) := by
  refine DegPoly.mem_numKer.mpr fun w i => ?_
  by_cases hu : u = 0
  · rw [hu, JacDivisors.div_zero]
    exact (formTh K F g hdim).map_update_zero w i
  · rw [formTh_apply]
    exact iform_update_div (Jac K F) (fun x => inferInstance) g hdim w i hu

/-- **Interface for the cube on `J^3`**: if a positive multiple of `Z` is principal on `P` and `L : J ⟶ P`
avoids `Z`, then `L^* Z` is numerically trivial on `J`. -/
theorem mem_numKer_of_cpull_div (g : ℕ) (hdim : ∀ x : (Jac K F).left, Order.height x ≤ g)
    {P : Scheme.{u}} [IsIntegral P] [IsLocallyNoetherian P]
    [∀ y : P, UniqueFactorizationMonoid (P.presheaf.stalk y)]
    (L : (Jac K F).left ⟶ P) {Z : AlgebraicCycle P ℤ} (hZ : Z ∈ weilDivisors P) (hA : Avoid L Z)
    {n : ℕ} (hn : 0 < n) {h : P.functionField} (hh : h ≠ 0) (hZh : JacDivisors.div P h = n • Z) :
    cpull L Z ∈ DegPoly.numKer (formTh K F g hdim) := by
  refine mem_numKer_of_nsmul _ hn ?_
  rw [← cpull_nsmul L hZ hA n, ← hZh, cpull_div L hh (by rw [hZh]; exact avoid_nsmul L hA n)]
  exact div_mem_numKer g hdim _

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_CubeZ =====
section

/-!
# S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`

* instances on `J ⊗ J` and `P := J ⊗ (J ⊗ J)`: integral, locally Noetherian, factorial stalks;
* `q1 q2 q3 : P ⟶ J` (projections), `cubeMap α β ga = lift α (lift β ga)`;
* `cubeZ P0 x0`: the seven-term combination of `(m_S ≫ τ_{x0})^* Θ` on `P`;
* **`cpull_cubeZ`**: `(α, β, ga)^* cubeZ = cubeC (φ ↦ (φ ≫ τ_{x0})^* Θ) α β ga` (seven `Avoid` hypotheses);
* `cpull_cubeZ_hom`: the same for homomorphisms, when `x0 ∉ W`;
* **`cubeC_mem_numKer`**: if a positive multiple of `cubeZ P0 x0` is principal on `P`, the cube relation holds
  numerically for `c φ := (φ ≫ τ_{x0})^* Θ` and all homomorphisms `α β ga`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- Pulling `pbTh` back along `(α, β, ga)`, when `cubeMap α β ga ≫ m = φ`. -/
lemma cpull_pbTh (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (m : Jac K F ⊗ (Jac K F ⊗ Jac K F) ⟶ Jac K F) [IsDominant (m ≫ transl (Jac K F) x0).left]
    (α β ga φ : Jac K F ⟶ Jac K F) (hφ : cubeMap α β ga ≫ m = φ)
    (hA : Avoid (φ ≫ transl (Jac K F) x0).left (Theta P0)) :
    Avoid (cubeMap α β ga).left (pbTh P0 x0 m) ∧
      cpull (cubeMap α β ga).left (pbTh P0 x0 m) = cpull (φ ≫ transl (Jac K F) x0).left (Theta P0) := by
  have hA' : Avoid ((cubeMap α β ga).left ≫ (m ≫ transl (Jac K F) x0).left) (Theta P0) := by
    rw [← Over.comp_left, ← Category.assoc, hφ]
    exact hA
  refine ⟨avoid_pullback _ _ (theta_mem_weilDivisors P0 hg) hA', ?_⟩
  rw [pbTh, ← cpull_comp _ _ (theta_mem_weilDivisors P0 hg) hA', ← Over.comp_left, ← Category.assoc, hφ]

/-- **The cube divisor pulled back along `(α, β, ga)`.** -/
theorem cpull_cubeZ (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (α β ga : Jac K F ⟶ Jac K F)
    (h123 : Avoid ((α * β * ga) ≫ transl (Jac K F) x0).left (Theta P0))
    (h12 : Avoid ((α * β) ≫ transl (Jac K F) x0).left (Theta P0))
    (h13 : Avoid ((α * ga) ≫ transl (Jac K F) x0).left (Theta P0))
    (h23 : Avoid ((β * ga) ≫ transl (Jac K F) x0).left (Theta P0))
    (h1 : Avoid (α ≫ transl (Jac K F) x0).left (Theta P0))
    (h2 : Avoid (β ≫ transl (Jac K F) x0).left (Theta P0))
    (h3 : Avoid (ga ≫ transl (Jac K F) x0).left (Theta P0)) :
    Avoid (cubeMap α β ga).left (cubeZ P0 x0) ∧
      cpull (cubeMap α β ga).left (cubeZ P0 x0) =
        cubeC (fun φ => cpull (φ ≫ transl (Jac K F) x0).left (Theta P0)) α β ga := by
  obtain ⟨a1, e1⟩ := cpull_pbTh P0 hg x0 (q1 K F * q2 K F * q3 K F) α β ga _
    (by rw [comp_mul, comp_mul, cubeMap_q1, cubeMap_q2, cubeMap_q3]) h123
  obtain ⟨a2, e2⟩ := cpull_pbTh P0 hg x0 (q1 K F * q2 K F) α β ga _
    (by rw [comp_mul, cubeMap_q1, cubeMap_q2]) h12
  obtain ⟨a3, e3⟩ := cpull_pbTh P0 hg x0 (q1 K F * q3 K F) α β ga _
    (by rw [comp_mul, cubeMap_q1, cubeMap_q3]) h13
  obtain ⟨a4, e4⟩ := cpull_pbTh P0 hg x0 (q2 K F * q3 K F) α β ga _
    (by rw [comp_mul, cubeMap_q2, cubeMap_q3]) h23
  obtain ⟨a5, e5⟩ := cpull_pbTh P0 hg x0 (q1 K F) α β ga _ (cubeMap_q1 α β ga) h1
  obtain ⟨a6, e6⟩ := cpull_pbTh P0 hg x0 (q2 K F) α β ga _ (cubeMap_q2 α β ga) h2
  obtain ⟨a7, e7⟩ := cpull_pbTh P0 hg x0 (q3 K F) α β ga _ (cubeMap_q3 α β ga) h3
  refine ⟨avoid_cube7 _ a1 a2 a3 a4 a5 a6 a7, ?_⟩
  rw [cubeZ, cpull_cube7 _ (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _)
    (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _) a1 a2 a3 a4 a5 a6 a7,
    e1, e2, e3, e4, e5, e6, e7, cubeC]

/-- The cube identity for homomorphisms, with one translate `x0 ∉ W`. -/
theorem cpull_cubeZ_hom (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hx0 : pt (Jac K F) x0 ∉ W P0) (α β ga : Jac K F ⟶ Jac K F) [IsMonHom α] [IsMonHom β] [IsMonHom ga] :
    Avoid (cubeMap α β ga).left (cubeZ P0 x0) ∧
      cpull (cubeMap α β ga).left (cubeZ P0 x0) =
        cubeC (fun φ => cpull (φ ≫ transl (Jac K F) x0).left (Theta P0)) α β ga :=
  have ha := MonObj.one_comp (X := 𝟙_ (Over (Spec (.of K)))) α
  have hb := MonObj.one_comp (X := 𝟙_ (Over (Spec (.of K)))) β
  have hc := MonObj.one_comp (X := 𝟙_ (Over (Spec (.of K)))) ga
  cpull_cubeZ P0 hg x0 α β ga
    (avoid_of_one_comp P0 x0 hx0 _ (one_comp_mul _ _ (one_comp_mul _ _ ha hb) hc))
    (avoid_of_one_comp P0 x0 hx0 _ (one_comp_mul _ _ ha hb))
    (avoid_of_one_comp P0 x0 hx0 _ (one_comp_mul _ _ ha hc))
    (avoid_of_one_comp P0 x0 hx0 _ (one_comp_mul _ _ hb hc))
    (avoid_of_one_comp P0 x0 hx0 _ ha) (avoid_of_one_comp P0 x0 hx0 _ hb) (avoid_of_one_comp P0 x0 hx0 _ hc)

/-- **Interface to the geometry**: a principal positive multiple of `cubeZ P0 x0` on `J^3` gives the cube
relation numerically for `c φ := (φ ≫ τ_{x0})^* Θ` and all homomorphisms. -/
theorem cubeC_mem_numKer (hg : 0 < genusFK K F) (g : ℕ) (hdim : ∀ x : (Jac K F).left, Order.height x ≤ g)
    (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hx0 : pt (Jac K F) x0 ∉ W P0)
    {n : ℕ} (hn : 0 < n) {h : (Jac K F ⊗ (Jac K F ⊗ Jac K F)).left.functionField} (hh : h ≠ 0)
    (hZh : JacDivisors.div _ h = n • cubeZ P0 x0)
    (α β ga : Jac K F ⟶ Jac K F) [IsMonHom α] [IsMonHom β] [IsMonHom ga] :
    cubeC (fun φ => cpull (φ ≫ transl (Jac K F) x0).left (Theta P0)) α β ga ∈
      DegPoly.numKer (formTh K F g hdim) := by
  obtain ⟨hA, he⟩ := cpull_cubeZ_hom P0 hg x0 hx0 α β ga
  rw [← he]
  exact mem_numKer_of_cpull_div g hdim _ (cubeZ_mem P0 x0) hA hn hh hZh

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Sym =====
section

/-!
# S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`

* `algebraMap_generic`, **`cpull_eq_pullback`**: for a dominant map, `cpull` is `JacDivisors.pullback`;
* `negJ = (𝟙 J)⁻¹` (the inverse map), `comp_negJ : φ ≫ negJ = φ⁻¹`;
* `DTh P0 x0 := τ_{x0}^* Θ + (negJ ≫ τ_{x0})^* Θ`: Weil (`DTh_mem`), effective (`DTh_nonneg`);
* `avoid_DTh`: every homomorphism avoids `DTh P0 x0` when `x0 ∉ W`;
* **`cpull_DTh`**: `φ^* D' = (φ ≫ τ_{x0})^* Θ + (φ⁻¹ ≫ τ_{x0})^* Θ`;
* **`cpull_inv_DTh`**: `(φ⁻¹)^* D' = φ^* D'` (exact symmetry).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (φ : C ⟶ Y) [IsDominant φ]

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

lemma DTh_nonneg (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hx0 : pt (Jac K F) x0 ∉ W P0) (z : (Jac K F).left) : 0 ≤ DTh P0 x0 z := by
  have hT := theta_mem_weilDivisors P0 hg
  rw [DTh, ← cpull_eq_pullback _ hT (avoid_one_transl P0 x0 hx0),
    ← cpull_eq_pullback _ hT (avoid_negJ_transl P0 x0 hx0)]
  exact add_nonneg (cpull_nonneg _ hT (avoid_one_transl P0 x0 hx0) z fun w _ _ => Theta_nonneg P0 w)
    (cpull_nonneg _ hT (avoid_negJ_transl P0 x0 hx0) z fun w _ _ => Theta_nonneg P0 w)

/-- **`φ^* D'`** splits into the two translates. -/
theorem cpull_DTh (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hx0 : pt (Jac K F) x0 ∉ W P0) (φ : Jac K F ⟶ Jac K F) [IsMonHom φ] :
    Avoid φ.left (DTh P0 x0) ∧ cpull φ.left (DTh P0 x0) =
      cpull (φ ≫ transl (Jac K F) x0).left (Theta P0) + cpull (φ⁻¹ ≫ transl (Jac K F) x0).left (Theta P0) := by
  have hT := theta_mem_weilDivisors P0 hg
  have hA1 : Avoid (φ.left ≫ (transl (Jac K F) x0).left) (Theta P0) :=
    avoid_of_one_comp P0 x0 hx0 φ (MonObj.one_comp φ)
  have hA2 : Avoid (φ.left ≫ (negJ K F ≫ transl (Jac K F) x0).left) (Theta P0) := by
    rw [← Over.comp_left, ← Category.assoc, comp_negJ]
    exact avoid_of_one_comp P0 x0 hx0 φ⁻¹ (MonObj.one_comp φ⁻¹)
  have hB1 := avoid_pullback φ.left (transl (Jac K F) x0).left hT hA1
  have hB2 := avoid_pullback φ.left (negJ K F ≫ transl (Jac K F) x0).left hT hA2
  refine ⟨avoid_add _ hB1 hB2, ?_⟩
  rw [DTh, cpull_add φ.left (pullback_mem_weilDivisors _ _) (pullback_mem_weilDivisors _ _) hB1 hB2,
    ← cpull_comp φ.left _ hT hA1, ← cpull_comp φ.left _ hT hA2, ← Over.comp_left, ← Over.comp_left,
    ← Category.assoc, comp_negJ]

/-- **Exact symmetry** of `D'`. -/
theorem cpull_inv_DTh (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hx0 : pt (Jac K F) x0 ∉ W P0) (φ : Jac K F ⟶ Jac K F) [IsMonHom φ] :
    cpull (φ⁻¹).left (DTh P0 x0) = cpull φ.left (DTh P0 x0) := by
  rw [(cpull_DTh P0 hg x0 hx0 φ⁻¹).2, (cpull_DTh P0 hg x0 hx0 φ).2, inv_inv, add_comm]

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Slice =====
section

/-!
# S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `line_prj_self`, `line_prj_ne`: a line against the projections;
* `cval q g` (the constant `g(q)` as an element of `F`), **`cval_mem`**: it lies in `K`;
* `exists_stalk_of_ord`: nonnegative place order at `q` ⇒ regular at the point `q`;
* `zPP`, `detPP` (the determinant `det_k`), `sliceRow`;
* **`slice_detPP`**: `PsiX (fpull line (detPP ..)) = det (sliceRow ..)`; **`avoid_detPP`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Slice

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **D-B2: the slice of `det_k` along the `i0`-th line through `p`.** -/
theorem slice_detPP (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hτ : ∀ j, τ j ≠ i0 → ∀ l, 0 ≤ (kPl (p ≫ prj K F n (τ j))).ord (h l))
    (hm : ∀ i l, 0 ≤ (kPl (m i)).ord (h l)) :
    PsiX K F (fpull (line K F n i0 p).left (detPP K F n τ m h)) =
      (Matrix.of (sliceRow K F n τ m i0 p h)).det := by
  have e := fpull_det_eq (line K F n i0 p).left (zPP K F n τ m) (fun _ l => phiX K F (h l))
    (reg_detPP hg n τ m h i0 p hτ hm)
  rw [detPP, e, RingHom.map_det]
  congr 1
  ext a l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rcases a with j | i
  · simp only [sliceRow, Sum.elim_inl]
    split_ifs with hj
    · rw [line_zPP_self n τ m i0 p j hj, fpull_id, PsiX_phiX]
    · rw [line_zPP_ne n τ m i0 p j hj]
      rfl
  · simp only [sliceRow, Sum.elim_inr]
    rw [line_zPP_inr n τ m i0 p i]
    rfl

/-- **`div det_k` avoids the generic point of a line along which the slice is nonzero.** -/
theorem avoid_detPP (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hτ : ∀ j, τ j ≠ i0 → ∀ l, 0 ≤ (kPl (p ≫ prj K F n (τ j))).ord (h l))
    (hm : ∀ i l, 0 ≤ (kPl (m i)).ord (h l)) (hne : (Matrix.of (sliceRow K F n τ m i0 p h)).det ≠ 0) :
    Avoid (line K F n i0 p).left (div (PP K F n).left (detPP K F n τ m h)) := by
  obtain ⟨v, h1, h2⟩ := fpull_det (line K F n i0 p).left (zPP K F n τ m) (fun _ l => phiX K F (h l))
    (reg_detPP hg n τ m h i0 p hτ hm)
  have hv : IsUnit v := by
    refine isUnit_of_stalkMap_ne_zero _ ?_
    rw [h2]
    intro h0
    apply hne
    rw [← slice_detPP hg n τ m h i0 p hτ hm, detPP,
      fpull_det_eq (line K F n i0 p).left (zPP K F n τ m) (fun _ l => phiX K F (h l))
        (reg_detPP hg n τ m h i0 p hτ hm), h0, map_zero]
  rw [detPP, ← h1]
  exact avoid_div_of_isUnit _ hv

end Slice

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cof =====
section

/-!
# S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
* `det_mem_range`: a matrix with entries in `K` has its determinant in `K`;
* **`slice_mem_LFK`** (Laplace along the variable row): the slice lies in `L(D)` when every `h l` does;
* `ptRow` (the point of each row, `q` in the variable rows), `comp_line_zPP`;
* **`ord_slice_pos`**: the slice vanishes at `q` when two rows sit at `q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Cof

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Vanishing**: if two rows of the slice sit at the point `q`, the (nonzero) slice vanishes at `q`. -/
theorem ord_slice_pos (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hτ : ∀ j, τ j ≠ i0 → ∀ l, 0 ≤ (kPl (p ≫ prj K F n (τ j))).ord (h l))
    (hm : ∀ i l, 0 ≤ (kPl (m i)).ord (h l)) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)
    (hq : ∀ l, 0 ≤ (kPl q).ord (h l)) {a b : Fin N ⊕ Fin r} (hab : a ≠ b)
    (ha : ptRow K F n τ m i0 p q a = q) (hb : ptRow K F n τ m i0 p q b = q)
    (hne : (Matrix.of (sliceRow K F n τ m i0 p h)).det ≠ 0) :
    0 < (kPl q).ord (Matrix.of (sliceRow K F n τ m i0 p h)).det := by
  have hreg : ∀ a' l, ∃ w : (X1O K F).left.presheaf.stalk
      ((((toUnit (X1O K F) ≫ q).left ≫ (line K F n i0 p).left) ≫ zPP K F n τ m a') (genericPoint _)),
      algebraMap _ (X1O K F).left.functionField w = phiX K F (h l) := by
    intro a' l
    rw [comp_line_zPP]
    refine exists_stalk_of_ord hg _ _ ?_ (toUnit_comp_apply _ _)
    rcases a' with j | i
    · by_cases hj : τ j = i0
      · simp only [ptRow, Sum.elim_inl, if_pos hj]
        exact hq l
      · simp only [ptRow, Sum.elim_inl, if_neg hj]
        exact hτ j hj l
    · exact hm i l
  obtain ⟨v, hv1, hv2⟩ := fpull_det ((toUnit (X1O K F) ≫ q).left ≫ (line K F n i0 p).left)
    (zPP K F n τ m) (fun _ l => phiX K F (h l)) hreg
  have h0 : (Matrix.of fun a' l => fpull (((toUnit (X1O K F) ≫ q).left ≫ (line K F n i0 p).left) ≫
      zPP K F n τ m a') (phiX K F (h l))).det = 0 := by
    refine Matrix.det_zero_of_row_eq hab ?_
    funext l
    simp only [Matrix.of_apply]
    rw [comp_line_zPP, comp_line_zPP, ha, hb]
  have hD : ∃ w : (PP K F n).left.presheaf.stalk
      (((toUnit (X1O K F) ≫ q).left ≫ (line K F n i0 p).left) (genericPoint _)),
      algebraMap _ (PP K F n).left.functionField w = detPP K F n τ m h := ⟨v, hv1⟩
  obtain ⟨u, hu1, hu2⟩ := fpull_fpull (toUnit (X1O K F) ≫ q).left (line K F n i0 p).left
    (detPP K F n τ m h) hD
  have hu0 : ((toUnit (X1O K F) ≫ q).left.stalkMap (genericPoint _)).hom u = 0 := by
    rw [hu2, detPP, ← hv1, fpull_algebraMap, hv2, h0]
  have hf : fpull (line K F n i0 p).left (detPP K F n τ m h) =
      phiX K F (Matrix.of (sliceRow K F n τ m i0 p h)).det := by
    rw [← slice_detPP hg n τ m h i0 p hτ hm, phiX_PsiX]
  have hu_ne : u ≠ 0 := by
    intro hu
    apply hne
    have h1 := hu1
    rw [hu, map_zero, hf] at h1
    exact (map_eq_zero_iff (phiX K F) (phiX K F).injective).mp h1.symm
  have hu_nu : u ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h1 := hunit.map ((toUnit (X1O K F) ≫ q).left.stalkMap (genericPoint _)).hom
    rw [hu0] at h1
    exact not_isUnit_zero h1
  have hx : (toUnit (X1O K F) ≫ q).left (genericPoint (X1O K F).left) = q.left (IsLocalRing.closedPoint K) :=
    toUnit_comp_apply _ _
  have hc : Order.coheight ((toUnit (X1O K F) ≫ q).left (genericPoint (X1O K F).left)) = 1 := by
    rw [hx]
    exact coheight_kpt_X1 q
  have hpos := ord_algebraMap_stalk_pos hc hu_ne hu_nu
  rw [hu1, hf, hx] at hpos
  exact hpos.trans_eq (ord_phiX_kpt hg q _)

end Cof

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Eff =====
section

/-!
# S4-ThetaCube, file Eff (D-B3, part 2): the residual divisor of a slice of `det_k`
* `ptC`, `Zsl` (the points of the constant rows and their divisor), `ptRow_of_ne`;
* `ord_nonneg_of_mem_LFK`, `deg_finsetSum_single`, `deg_Zsl`;
* **`slice_mem_LFK_sub`**: the slice lies in `L(H - Zsl)`;
* **`slice_eff`**: `G := div f + H - Zsl` is effective of degree `deg H - (N + r - 1)`;
* **`eq_of_ell_one`**: effective, linearly equivalent, `ℓ(G) = 1` ⇒ equal.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Eff

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **The slice lies in `L(H - Zsl)`.** -/
theorem slice_mem_LFK_sub (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (j0 : Fin N) (hτ0 : τ j0 = i0) (hj0 : ∀ j, τ j = i0 → j = j0)
    (H : Places.Divisor K F) (hH : ∀ l, h l ∈ LFK K F H)
    (hH0 : ∀ a, a ≠ Sum.inl j0 → H (kPl (ptC K F n τ m p a)) = 0)
    (hinj : ∀ a b, a ≠ Sum.inl j0 → b ≠ Sum.inl j0 → kPl (ptC K F n τ m p a) = kPl (ptC K F n τ m p b) → a = b) :
    (Matrix.of (sliceRow K F n τ m i0 p h)).det ∈ LFK K F (H - Zsl K F n τ m p j0) := by
  classical
  have hL := slice_mem_LFK n τ m i0 p h j0 hτ0 hj0 H hH
  by_cases hf : (Matrix.of (sliceRow K F n τ m i0 p h)).det = 0
  · rw [hf]
    exact Submodule.zero_mem _
  rw [mem_LFK hf] at hL ⊢
  rw [Finsupp.le_def] at hL ⊢
  intro P
  have hLP := hL P
  rw [Finsupp.zero_apply, Finsupp.add_apply, PlacesK.div_apply] at hLP
  rw [Finsupp.zero_apply, Finsupp.add_apply, Finsupp.sub_apply, PlacesK.div_apply]
  have hτ' : ∀ j, τ j ≠ i0 → ∀ l, 0 ≤ (kPl (p ≫ prj K F n (τ j))).ord (h l) := fun j hj l =>
    ord_nonneg_of_mem_LFK (hH l) (hH0 (Sum.inl j) fun e => hj (by rw [Sum.inl_injective e]; exact hτ0))
  have hm' : ∀ i l, 0 ≤ (kPl (m i)).ord (h l) := fun i l =>
    ord_nonneg_of_mem_LFK (hH l) (hH0 (Sum.inr i) Sum.inr_ne_inl)
  by_cases hP : ∃ a, a ≠ Sum.inl j0 ∧ kPl (ptC K F n τ m p a) = P
  · obtain ⟨a, ha0, rfl⟩ := hP
    have hZ : Zsl K F n τ m p j0 (kPl (ptC K F n τ m p a)) = 1 := by
      rw [Zsl, Finsupp.finsetSum_apply, Finset.sum_eq_single a]
      · rw [Finsupp.single_apply, if_pos rfl]
      · intro b hb hba
        rw [Finsupp.single_apply, if_neg]
        exact fun e => hba (hinj b a (Finset.ne_of_mem_erase hb) ha0 e)
      · intro ha
        exact absurd (Finset.mem_erase.mpr ⟨ha0, Finset.mem_univ _⟩) ha
    rw [hZ, hH0 a ha0]
    have hpos := ord_slice_pos hg n τ m h i0 p hτ' hm' (ptC K F n τ m p a)
      (fun l => ord_nonneg_of_mem_LFK (hH l) (hH0 a ha0)) (a := a) (b := Sum.inl j0) ha0
      (ptRow_of_ne n τ m i0 p hj0 _ ha0) (by simp only [ptRow, Sum.elim_inl, if_pos hτ0]) hf
    omega
  · have hZ : Zsl K F n τ m p j0 P = 0 := by
      rw [Zsl, Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [Finsupp.single_apply, if_neg]
      exact fun e => hP ⟨b, Finset.ne_of_mem_erase hb, e⟩
    rw [hZ, sub_zero]
    exact hLP

/-- **The residual divisor `G = div f + H - Zsl` is effective, of degree `deg H - (N + r - 1)`.** -/
theorem slice_eff (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (j0 : Fin N) (hτ0 : τ j0 = i0) (hj0 : ∀ j, τ j = i0 → j = j0)
    (H : Places.Divisor K F) (hH : ∀ l, h l ∈ LFK K F H)
    (hH0 : ∀ a, a ≠ Sum.inl j0 → H (kPl (ptC K F n τ m p a)) = 0)
    (hinj : ∀ a b, a ≠ Sum.inl j0 → b ≠ Sum.inl j0 → kPl (ptC K F n τ m p a) = kPl (ptC K F n τ m p b) → a = b)
    (hf : (Matrix.of (sliceRow K F n τ m i0 p h)).det ≠ 0) :
    0 ≤ PlacesK.div (Matrix.of (sliceRow K F n τ m i0 p h)).det + (H - Zsl K F n τ m p j0) ∧
      (PlacesK.div (Matrix.of (sliceRow K F n τ m i0 p h)).det + (H - Zsl K F n τ m p j0)).deg + (N + r) =
        H.deg + 1 := by
  refine ⟨(mem_LFK hf).mp (slice_mem_LFK_sub hg n τ m h i0 p j0 hτ0 hj0 H hH hH0 hinj), ?_⟩
  rw [PlacesK.Divisor.deg_add, PlacesK.deg_div hf, PlacesK.Divisor.deg_sub, ← deg_Zsl n τ m p j0]
  ring

end Eff

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Rank =====
section

/-!
# S4-ThetaCube, file Rank (D-B4, part 1): the slices do not vanish
* `ord_sub_cval_pos`: `f - f(q)` vanishes at `q` (the 2 x 2 case of `ord_slice_pos`);
* `ord_pos_sum`: sums of functions vanishing at a place vanish there;
* `comb_mem_LFK`: a `K`-combination of the `h l` whose values vanish at the points lies in `L(H - Σ pts)`;
* **`det_ne_zero_of_ker`**, `det_ne_zero_of_ker0`: the linear algebra (rank-nullity).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Rank

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **`f - f(q)` vanishes at `q`.** -/
theorem ord_sub_cval_pos (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (f : F)
    (hf : 0 ≤ (kPl q).ord f) (hne : f - cval K F q (phiX K F f) ≠ 0) :
    0 < (kPl q).ord (f - cval K F q (phiX K F f)) := by
  have p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F 1 := lift (𝟙 _) q
  have h1 : 0 ≤ (kPl q).ord (1 : F) := (PlacesK.Place.ord_one (P := kPl q)).ge
  have hreg : ∀ l : Fin 1 ⊕ Fin 1, 0 ≤ (kPl q).ord (Sum.elim (fun _ : Fin 1 => f) (fun _ : Fin 1 => (1 : F)) l) := by
    rintro (l | l)
    exacts [hf, h1]
  have hdet : (Matrix.of (sliceRow K F 1 (fun _ : Fin 1 => (0 : Fin 1)) (fun _ : Fin 1 => q) 0 p
      (Sum.elim (fun _ : Fin 1 => f) (fun _ : Fin 1 => (1 : F))))).det = f - cval K F q (phiX K F f) := by
    rw [← Matrix.det_reindex_self (finSumFinEquiv (m := 1) (n := 1)), Matrix.det_fin_two]
    have e0 : (finSumFinEquiv (m := 1) (n := 1)).symm 0 = Sum.inl 0 := by first | rfl | decide | simp
    have e1 : (finSumFinEquiv (m := 1) (n := 1)).symm 1 = Sum.inr 0 := by first | rfl | decide | simp
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, e0, e1, sliceRow, Sum.elim_inl,
      Sum.elim_inr, if_true, ↓reduceIte, cval_one]
    ring
  have key := ord_slice_pos hg 1 (fun _ : Fin 1 => (0 : Fin 1)) (fun _ : Fin 1 => q)
    (Sum.elim (fun _ : Fin 1 => f) (fun _ : Fin 1 => (1 : F))) 0 p (fun j hj => (hj rfl).elim)
    (fun _ l => hreg l) q hreg (a := Sum.inl 0) (b := Sum.inr 0) Sum.inl_ne_inr rfl rfl (by rw [hdet]; exact hne)
  rwa [hdet] at key

/-- **A combination with vanishing values lies in `L(H - Σ pts)`.** -/
theorem comb_mem_LFK (hg : 0 < genusFK K F) {ι κ : Type*} [Fintype ι] (h : ι → F) (H : Places.Divisor K F)
    (hH : ∀ l, h l ∈ LFK K F H) (s : Finset κ) (pt : κ → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))
    (hH0 : ∀ a ∈ s, H (kPl (pt a)) = 0) (hinj : ∀ a ∈ s, ∀ b ∈ s, kPl (pt a) = kPl (pt b) → a = b)
    (c : ι → K) (hc : ∀ a ∈ s, ∑ l, algebraMap K F (c l) * cval K F (pt a) (phiX K F (h l)) = 0) :
    ∑ l, c l • h l ∈ LFK K F (H - ∑ a ∈ s, Finsupp.single (kPl (pt a)) 1) := by
  classical
  have hL : ∑ l, c l • h l ∈ LFK K F H := Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hH l)
  by_cases hφ : ∑ l, c l • h l = 0
  · rw [hφ]; exact Submodule.zero_mem _
  rw [mem_LFK hφ] at hL ⊢
  rw [Finsupp.le_def] at hL ⊢
  intro P
  have hLP := hL P
  rw [Finsupp.zero_apply, Finsupp.add_apply, PlacesK.div_apply] at hLP
  rw [Finsupp.zero_apply, Finsupp.add_apply, Finsupp.sub_apply, PlacesK.div_apply, Finsupp.finsetSum_apply]
  by_cases hP : ∃ a ∈ s, kPl (pt a) = P
  · obtain ⟨a, ha, rfl⟩ := hP
    rw [Finset.sum_eq_single a (fun b hb hba => by
        rw [Finsupp.single_apply, if_neg]; exact fun e => hba (hinj b hb a ha e))
      (fun h' => absurd ha h'), Finsupp.single_apply, if_pos rfl, hH0 a ha]
    have hreg : ∀ l, 0 ≤ (kPl (pt a)).ord (h l) := fun l => ord_nonneg_of_mem_LFK (hH l) (hH0 a ha)
    have e : ∑ l, c l • h l =
        ∑ l, algebraMap K F (c l) * (h l - cval K F (pt a) (phiX K F (h l))) := by
      simp only [mul_sub, Finset.sum_sub_distrib, hc a ha, sub_zero, Algebra.smul_def]
    have hv := ord_pos_sum (kPl (pt a)) Finset.univ
      (fun l => algebraMap K F (c l) * (h l - cval K F (pt a) (phiX K F (h l)))) (fun l _ => by
      by_cases hc0 : c l = 0
      · left; rw [hc0, map_zero, zero_mul]
      by_cases hd : h l - cval K F (pt a) (phiX K F (h l)) = 0
      · left; rw [hd, mul_zero]
      right
      rw [PlacesK.ord_const_mul (K := K) (F := F) (IntermediateField.algebraMap_mem _ (c l))
        ((_root_.map_ne_zero (algebraMap K F)).mpr hc0) hd]
      exact ord_sub_cval_pos hg (pt a) (h l) (hreg l) hd)
    rw [← e] at hv
    rcases hv with hv | hv
    · exact absurd hv hφ
    · omega
  · have hZ : ∑ b ∈ s, (Finsupp.single (kPl (pt b)) (1 : ℤ) : Places.Divisor K F) P = 0 :=
      Finset.sum_eq_zero fun b hb => by
        rw [Finsupp.single_apply, if_neg]; exact fun e => hP ⟨b, hb, e⟩
    rw [hZ, sub_zero]
    exact hLP

end Rank

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_NZ =====
section

/-!
# S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
* `ellFK_add_div`, `ellFK_of_clsK_eq`: `ℓ` only depends on the divisor class;
* `sliceRow_of_ne`: the constant rows of a slice are the values at `ptC`;
* **`slice_ne_zero`**: the slice with one variable row is nonzero when `ℓ(H - Zsl) ≤ 1`;
* **`slice_ne_zero_const`**: the all-constant slice is nonzero when `ℓ(H - Zall) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section NZ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **The slice with one variable row does not vanish** when `ℓ(H - Zsl) ≤ 1`. -/
theorem slice_ne_zero (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (j0 : Fin N) (hτ0 : τ j0 = i0) (hj0 : ∀ j, τ j = i0 → j = j0)
    (H : Places.Divisor K F) (hH : ∀ l, h l ∈ LFK K F H)
    (hH0 : ∀ a, a ≠ Sum.inl j0 → H (kPl (ptC K F n τ m p a)) = 0)
    (hinj : ∀ a b, a ≠ Sum.inl j0 → b ≠ Sum.inl j0 → kPl (ptC K F n τ m p a) = kPl (ptC K F n τ m p b) → a = b)
    (hli : LinearIndependent K h) (hell : ellFK K F (H - Zsl K F n τ m p j0) ≤ 1) :
    (Matrix.of (sliceRow K F n τ m i0 p h)).det ≠ 0 := by
  classical
  choose V hVs using fun (a : {a : Fin N ⊕ Fin r // a ≠ Sum.inl j0}) (l : Fin N ⊕ Fin r) =>
    Set.mem_range.mp (cval_mem (ptC K F n τ m p a.1) (phiX K F (h l)))
  have hrow : ∀ a : Fin N ⊕ Fin r, a ≠ Sum.inl j0 → ∀ j, a = Sum.inl j → τ j ≠ i0 := by
    rintro a ha j rfl e
    exact ha (by rw [hj0 j e])
  have hmem : ∀ c : Fin N ⊕ Fin r → K, Matrix.mulVec V c = 0 →
      ∑ l, c l • h l ∈ LFK K F (H - Zsl K F n τ m p j0) := by
    intro c hc
    refine comb_mem_LFK hg h H hH (Finset.univ.erase (Sum.inl j0)) (ptC K F n τ m p)
      (fun a ha => hH0 a (Finset.ne_of_mem_erase ha))
      (fun a ha b hb e => hinj a b (Finset.ne_of_mem_erase ha) (Finset.ne_of_mem_erase hb) e) c
      (fun a ha => ?_)
    have h2 := congrArg (algebraMap K F) (congrFun hc ⟨a, Finset.ne_of_mem_erase ha⟩)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, map_sum, map_mul, map_zero, hVs] at h2
    exact Eq.trans (Finset.sum_congr rfl fun l _ => mul_comm _ _) h2
  refine det_ne_zero_of_ker _ (Sum.inl j0) V (fun a l => ?_) ?_ ?_
  · rw [Matrix.of_apply, sliceRow_of_ne n τ m i0 p h (hrow a.1 a.2), hVs]
  · have e : (Matrix.of (sliceRow K F n τ m i0 p h)) (Sum.inl j0) = h := by
      funext l
      simp only [Matrix.of_apply, sliceRow, Sum.elim_inl, if_pos hτ0]
    rw [e]
    exact hli
  · haveI := finiteDimensional_LFK (K := K) (F := F) (H - Zsl K F n τ m p j0)
    let Φ : LinearMap.ker (Matrix.mulVecLin (V : Matrix {a : Fin N ⊕ Fin r // a ≠ Sum.inl j0} (Fin N ⊕ Fin r) K))
        →ₗ[K] LFK K F (H - Zsl K F n τ m p j0) :=
      { toFun := fun c => ⟨∑ l, c.1 l • h l, hmem c.1 c.2⟩
        map_add' := fun c d => Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])
        map_smul' := fun a c => Subtype.ext (by simp [Finset.smul_sum, mul_smul]) }
    have hinjΦ : Function.Injective Φ := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      have hs : ∑ l, c.1 l • h l = 0 := congrArg Subtype.val hc
      exact Subtype.ext (funext fun l => Fintype.linearIndependent_iff.mp hli c.1 hs l)
    exact (LinearMap.finrank_le_finrank_of_injective hinjΦ).trans hell

/-- **The all-constant slice does not vanish** when `ℓ(H - Zall) = 0`. -/
theorem slice_ne_zero_const (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (hτ : ∀ j, τ j ≠ i0)
    (H : Places.Divisor K F) (hH : ∀ l, h l ∈ LFK K F H)
    (hH0 : ∀ a, H (kPl (ptC K F n τ m p a)) = 0)
    (hinj : ∀ a b, kPl (ptC K F n τ m p a) = kPl (ptC K F n τ m p b) → a = b)
    (hli : LinearIndependent K h) (hell : ellFK K F (H - Zall K F n τ m p) = 0) :
    (Matrix.of (sliceRow K F n τ m i0 p h)).det ≠ 0 := by
  classical
  choose V hVs using fun (a l : Fin N ⊕ Fin r) =>
    Set.mem_range.mp (cval_mem (ptC K F n τ m p a) (phiX K F (h l)))
  refine det_ne_zero_of_ker0 _ V (fun a l => ?_) (fun c hc => ?_)
  · rw [Matrix.of_apply, sliceRow_of_ne n τ m i0 p h (fun j _ => hτ j), hVs]
  · have hm : ∑ l, c l • h l ∈ LFK K F (H - Zall K F n τ m p) :=
      comb_mem_LFK hg h H hH Finset.univ (ptC K F n τ m p) (fun a _ => hH0 a)
        (fun a _ b _ e => hinj a b e) c (fun a _ => by
          have h2 := congrArg (algebraMap K F) (congrFun hc a)
          simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, map_sum, map_mul, map_zero, hVs] at h2
          exact Eq.trans (Finset.sum_congr rfl fun l _ => mul_comm _ _) h2)
    haveI := finiteDimensional_LFK (K := K) (F := F) (H - Zall K F n τ m p)
    have hbot : LFK K F (H - Zall K F n τ m p) = ⊥ := Submodule.finrank_eq_zero.mp hell
    rw [hbot, Submodule.mem_bot] at hm
    exact funext fun l => Fintype.linearIndependent_iff.mp hli c hm l

end NZ

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Maps =====
section

/-!
# S4-ThetaCube, file Maps (D-B4, part 3): the map `Φ3 : X1^n ⟶ J^3` and its lines
* `cpull_pbTh_X1`, **`cpull_cubeZ_X1`**: the cube divisor pulled back along any `f : X1 ⟶ J^3`;
* `comp_finprod`: composition distributes over finite products in the hom-group;
* `psiS P0 n β S := Π_{k : β k ∈ S} pr_k ≫ aj` (blocks given by `β : Fin n → Fin 3`), `psiS_mul`;
* `Phi3 P0 n β := (psiS {0}, psiS {1}, psiS {2})`, `Phi3_q1`, `Phi3_q2`, `Phi3_q3`;
* **`line_psiS_transl`**: along the `i0`-th line through `p`, `psiS S ≫ τ_{x0}` is `f_e` (if `β i0 ∈ S`) or the
  constant `e`, for `e = (p ≫ psiE S i0) * x0`;
* `cpull_const_Theta`: a constant map off `W` pulls `Θ` back to `0`.
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

section Maps

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- Pulling `pbTh` back along `f : X1 ⟶ J^3`, when `f ≫ m = φ`. -/
lemma cpull_pbTh_X1 (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (m : Jac K F ⊗ (Jac K F ⊗ Jac K F) ⟶ Jac K F) [IsDominant (m ≫ transl (Jac K F) x0).left]
    (f : X1O K F ⟶ Jac K F ⊗ (Jac K F ⊗ Jac K F)) (φ : X1O K F ⟶ Jac K F) (hφ : f ≫ m = φ)
    (hA : Avoid (φ ≫ transl (Jac K F) x0).left (Theta P0)) :
    Avoid f.left (pbTh P0 x0 m) ∧
      cpull f.left (pbTh P0 x0 m) = cpull (φ ≫ transl (Jac K F) x0).left (Theta P0) := by
  have hA' : Avoid (f.left ≫ (m ≫ transl (Jac K F) x0).left) (Theta P0) := by
    rw [← Over.comp_left, ← Category.assoc, hφ]
    exact hA
  refine ⟨avoid_pullback _ _ (theta_mem_weilDivisors P0 hg) hA', ?_⟩
  rw [pbTh, ← cpull_comp _ _ (theta_mem_weilDivisors P0 hg) hA', ← Over.comp_left, ← Category.assoc, hφ]

/-- **The cube divisor pulled back along any `f : X1 ⟶ J^3`.** -/
theorem cpull_cubeZ_X1 (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (f : X1O K F ⟶ Jac K F ⊗ (Jac K F ⊗ Jac K F))
    (h123 : Avoid (((f ≫ q1 K F) * (f ≫ q2 K F) * (f ≫ q3 K F)) ≫ transl (Jac K F) x0).left (Theta P0))
    (h12 : Avoid (((f ≫ q1 K F) * (f ≫ q2 K F)) ≫ transl (Jac K F) x0).left (Theta P0))
    (h13 : Avoid (((f ≫ q1 K F) * (f ≫ q3 K F)) ≫ transl (Jac K F) x0).left (Theta P0))
    (h23 : Avoid (((f ≫ q2 K F) * (f ≫ q3 K F)) ≫ transl (Jac K F) x0).left (Theta P0))
    (h1 : Avoid ((f ≫ q1 K F) ≫ transl (Jac K F) x0).left (Theta P0))
    (h2 : Avoid ((f ≫ q2 K F) ≫ transl (Jac K F) x0).left (Theta P0))
    (h3 : Avoid ((f ≫ q3 K F) ≫ transl (Jac K F) x0).left (Theta P0)) :
    Avoid f.left (cubeZ P0 x0) ∧
      cpull f.left (cubeZ P0 x0) =
        cubeC (fun φ : X1O K F ⟶ Jac K F => cpull (φ ≫ transl (Jac K F) x0).left (Theta P0))
          (f ≫ q1 K F) (f ≫ q2 K F) (f ≫ q3 K F) := by
  obtain ⟨a1, e1⟩ := cpull_pbTh_X1 P0 hg x0 (q1 K F * q2 K F * q3 K F) f _ (by rw [comp_mul, comp_mul]) h123
  obtain ⟨a2, e2⟩ := cpull_pbTh_X1 P0 hg x0 (q1 K F * q2 K F) f _ (by rw [comp_mul]) h12
  obtain ⟨a3, e3⟩ := cpull_pbTh_X1 P0 hg x0 (q1 K F * q3 K F) f _ (by rw [comp_mul]) h13
  obtain ⟨a4, e4⟩ := cpull_pbTh_X1 P0 hg x0 (q2 K F * q3 K F) f _ (by rw [comp_mul]) h23
  obtain ⟨a5, e5⟩ := cpull_pbTh_X1 P0 hg x0 (q1 K F) f _ rfl h1
  obtain ⟨a6, e6⟩ := cpull_pbTh_X1 P0 hg x0 (q2 K F) f _ rfl h2
  obtain ⟨a7, e7⟩ := cpull_pbTh_X1 P0 hg x0 (q3 K F) f _ rfl h3
  refine ⟨avoid_cube7 _ a1 a2 a3 a4 a5 a6 a7, ?_⟩
  rw [cubeZ, cpull_cube7 _ (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _)
    (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _) (pbTh_mem P0 x0 _) a1 a2 a3 a4 a5 a6 a7,
    e1, e2, e3, e4, e5, e6, e7, cubeC]

/-- **A constant map off `W` avoids `Θ` and pulls it back to `0`.** -/
theorem cpull_const_Theta (hg : 0 < genusFK K F) (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (he : pt (Jac K F) e ∉ W P0) :
    Avoid (toUnit (X1O K F) ≫ e).left (Theta P0) ∧ cpull (toUnit (X1O K F) ≫ e).left (Theta P0) = 0 := by
  have hA : Avoid (toUnit (X1O K F) ≫ e).left (Theta P0) :=
    ⟨(W P0)ᶜ, (isClosed_W P0).isOpen_compl, by rw [toUnit_comp_apply_J]; exact he,
      fun w hw => theta_eq_zero_of_not_mem P0 hw⟩
  refine ⟨hA, ?_⟩
  ext x
  rw [cpull_eq_zero_of _ (theta_mem_weilDivisors P0 hg) hA (isClosed_W P0).isOpen_compl
    (by rw [toUnit_comp_apply_J]; exact he) (fun w hw => theta_eq_zero_of_not_mem P0 hw)]
  rfl

end Maps

end RamanujanPetersson.ThetaCube


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

/-- **The determinant side at `z = p_{i0}`**: `ord_{p_{i0}}` of the slice. -/
theorem cpull_detPP_kpt (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hτ : ∀ j, τ j ≠ i0 → ∀ l, 0 ≤ (kPl (p ≫ prj K F n (τ j))).ord (h l))
    (hm : ∀ i l, 0 ≤ (kPl (m i)).ord (h l)) (hne : (Matrix.of (sliceRow K F n τ m i0 p h)).det ≠ 0) :
    Avoid (line K F n i0 p).left (JacDivisors.div (PP K F n).left (detPP K F n τ m h)) ∧
      cpull (line K F n i0 p).left (JacDivisors.div (PP K F n).left (detPP K F n τ m h))
          ((p ≫ prj K F n i0).left (IsLocalRing.closedPoint K)) =
        (kPl (p ≫ prj K F n i0)).ord (Matrix.of (sliceRow K F n τ m i0 p h)).det := by
  have hA := avoid_detPP hg n τ m h i0 p hτ hm hne
  have h00 := fpull_algebraMap (line K F n i0 p).left 0
  rw [map_zero, map_zero] at h00
  have h0 : detPP K F n τ m h ≠ 0 := by
    intro e
    apply hne
    rw [← slice_detPP hg n τ m h i0 p hτ hm, e, h00, map_zero]
  refine ⟨hA, ?_⟩
  rw [cpull_div _ h0 hA, ← slice_detPP hg n τ m h i0 p hτ hm]
  exact div_kpt hg (p ≫ prj K F n i0) _

/-- **The `Θ` side, `β i0 ∉ S`**: a constant map off `W`. -/
theorem cube_side_not_mem (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hS : β i0 ∉ S)
    (hW : pt (Jac K F) ((p ≫ psiE P0 n β S i0) * x0) ∉ W P0) :
    Avoid ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0) ∧
      cpull ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0) = 0 := by
  rw [line_psiS_transl, if_neg hS]
  exact cpull_const_Theta P0 hg _ hW

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

/-- **The order of a one-variable slice at any place**: `G q - H q + Zsl q`. -/
theorem ord_slice_gen (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (j0 : Fin N) (hτ0 : τ j0 = i0) (hj0 : ∀ j, τ j = i0 → j = j0)
    (H : Places.Divisor K F) (hH : ∀ l, h l ∈ LFK K F H)
    (hH0 : ∀ a, a ≠ Sum.inl j0 → H (kPl (ptC K F n τ m p a)) = 0)
    (hinj : ∀ a b, a ≠ Sum.inl j0 → b ≠ Sum.inl j0 → kPl (ptC K F n τ m p a) = kPl (ptC K F n τ m p b) → a = b)
    (hne : (Matrix.of (sliceRow K F n τ m i0 p h)).det ≠ 0)
    {G : Places.Divisor K F} (hG : 0 ≤ G) (hell : ellFK K F G = 1)
    (hcls : clsK K F G = clsK K F (H - Zsl K F n τ m p j0)) (q : Place K F) :
    q.ord (Matrix.of (sliceRow K F n τ m i0 p h)).det = G q - H q + Zsl K F n τ m p j0 q := by
  obtain ⟨hG', -⟩ := slice_eff hg n τ m h i0 p j0 hτ0 hj0 H hH hH0 hinj hne
  have hc0 : clsK K F (PlacesK.div (Matrix.of (sliceRow K F n τ m i0 p h)).det) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr (div_mem_PrincK (K := K) (F := F) hne)
  have e := eq_of_ell_one hG hG' hell (by rw [clsK_add, hc0, zero_add]; exact hcls)
  rw [e, Finsupp.add_apply, Finsupp.sub_apply, PlacesK.div_apply]
  ring

end Gen

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

/-- A nonzero slice forces `det_k ≠ 0`. -/
theorem detPP_ne_of_slice (hg : 0 < genusFK K F) (n : ℕ) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (hτ : ∀ j, τ j ≠ i0 → ∀ l, 0 ≤ (kPl (p ≫ prj K F n (τ j))).ord (h l))
    (hm : ∀ i l, 0 ≤ (kPl (m i)).ord (h l)) (hne : (Matrix.of (sliceRow K F n τ m i0 p h)).det ≠ 0) :
    detPP K F n τ m h ≠ 0 := by
  have h00 := fpull_algebraMap (line K F n i0 p).left 0
  rw [map_zero, map_zero] at h00
  intro e
  apply hne
  rw [← slice_detPP hg n τ m h i0 p hτ hm, e, h00, map_zero]

variable (P0 : Place K F)

end NZS

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Pick =====
section

/-!
# S4-ThetaCube, file Pick (D-C3, part 1): a generic choice of the auxiliary points `m`
* `xM c3 : X1^g ⟶ J`, `p ↦ c_3 Φ_g(p)` (class `[W0 + Σ [p_i]] - (3g-2)[P0]`, `cls_xM`), onto on `K`-points;
* `badM`: the closed conditions "`x0 ∉ Ogood`", "`p_l = P0`", "`p_l = p_l'`" on `X1^g`, each missing a point;
* **`exists_m_x0`**: `g` distinct points `m_l ≠ P0` with `x0 := c_3 Φ_g(m) ∈ Ogood` of the class `cube_PP` needs.
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

section Pick

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

variable (cK c2 c3 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

theorem exists_not_mem_badM (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0)
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (c : Unit ⊕ Fin (genusFK K F) ⊕ (Fin (genusFK K F) × Fin (genusFK K F))) :
    ∃ y, y ∉ badM P0 cK c2 c3 c := by
  rcases c with _ | l | ⟨l, l'⟩
  · obtain ⟨e, he⟩ := exists_kpt_Ogood P0 cK hg hW hc2
    obtain ⟨p, hp⟩ := xM_surj P0 c3 e
    refine ⟨p.left (IsLocalRing.closedPoint K), fun h => h ?_⟩
    show (p ≫ xM P0 c3).left (IsLocalRing.closedPoint K) ∈ Ogood P0 cK c2
    rw [hp]
    exact he
  · obtain ⟨Q, hQ⟩ := exists_ne_place P0
    obtain ⟨p, hp⟩ := exists_pt_coord hg P0 (genusFK K F) (fun _ => Q)
    refine ⟨p.left (IsLocalRing.closedPoint K), fun h => hQ ?_⟩
    have e : p ≫ prj K F (genusFK K F) l ≫ ajO P0 = 1 := JacChunk.GrpPt.ev_inj (Jac K F) h
    rw [← Category.assoc, kPl_spec P0, hp l, ← ajK_self P0] at e
    exact ajK_injective hg P0 e
  · by_cases hk : l = l'
    · obtain ⟨p0, -⟩ := exists_pt_coord hg P0 (genusFK K F) (fun _ => P0)
      refine ⟨p0.left (IsLocalRing.closedPoint K), ?_⟩
      show _ ∉ (if l = l' then ∅ else _)
      rw [if_pos hk]
      exact Set.notMem_empty _
    · obtain ⟨Q, hQ⟩ := exists_ne_place P0
      obtain ⟨p, hp⟩ := exists_pt_coord hg P0 (genusFK K F) (fun j => if j = l then Q else P0)
      refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
      show _ ∉ (if l = l' then ∅ else _)
      rw [if_neg hk]
      intro h
      have e : p ≫ ((prj K F (genusFK K F) l ≫ ajO P0) * (prj K F (genusFK K F) l' ≫ ajO P0)⁻¹) = 1 :=
        JacChunk.GrpPt.ev_inj (Jac K F) h
      rw [MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one, ← Category.assoc, ← Category.assoc,
        kPl_spec P0 (p ≫ prj K F (genusFK K F) l), kPl_spec P0 (p ≫ prj K F (genusFK K F) l')] at e
      have e2 := ajK_injective hg P0 e
      have hk1 : kPl (p ≫ prj K F (genusFK K F) l) = Q := by simpa using hp l
      have hk2 : kPl (p ≫ prj K F (genusFK K F) l') = P0 := by simpa [Ne.symm hk] using hp l'
      rw [hk1, hk2] at e2
      exact hQ e2

/-- **A generic choice of `m`** (D-C3, finding F1): `g` distinct `K`-points `m_l ≠ P0` of `X1` and `x0` of class
`[W0 + Σ [m_l]] - (3g-2)[P0]` in `Ogood`. -/
theorem exists_m_x0 (hg : 0 < genusFK K F) {W0 : Places.Divisor K F} (hW : IsCanonicalFK K F W0)
    (hc2 : ((Multiplicative.toAdd (jacPicEquiv K F c2) : Pic0K K F) : PicK K F) =
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) - thetaK K F) :
    ∃ (m : Fin (genusFK K F) → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F),
      (∀ l, kPl (m l) ≠ P0) ∧ (∀ l l', kPl (m l) = kPl (m l') → l = l') ∧
      ((Multiplicative.toAdd (jacPicEquiv K F x0) : Pic0K K F) : PicK K F) =
        clsK K F (W0 + ∑ i, Finsupp.single (kPl (m i)) 1) -
          (2 * (genusFK K F : ℤ) + (genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1) ∧
      pt (Jac K F) x0 ∈ Ogood P0 cK c2 := by
  obtain ⟨c3, hc3⟩ := exists_c3 P0 hW
  have hne := ne_univ_of_compl (badM P0 cK c2 c3) (isClosed_badM P0 cK c2 c3)
    (exists_not_mem_badM P0 cK c2 c3 hg hW hc2)
  have : JacobsonSpace (PP K F (genusFK K F)).left :=
    LocallyOfFiniteType.jacobsonSpace (PP K F (genusFK K F)).hom
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
    (isClosed_iUnion_of_finite (isClosed_badM P0 cK c2 c3)).isOpen_compl.isLocallyClosed
  obtain ⟨p, rfl⟩ := exists_kpt_of_closed (K := K) (F := F) (genusFK K F) hzc
  have hc : ∀ c, p.left (IsLocalRing.closedPoint K) ∉ badM P0 cK c2 c3 c :=
    fun c h => hz (Set.mem_iUnion.mpr ⟨c, h⟩)
  refine ⟨fun l => p ≫ prj K F (genusFK K F) l, p ≫ xM P0 c3, fun l e => ?_, fun l l' e => ?_,
    cls_xM P0 hc3 p, ?_⟩
  · apply hc (Sum.inr (Sum.inl l))
    show (p ≫ prj K F (genusFK K F) l ≫ ajO P0).left (IsLocalRing.closedPoint K) = pt (Jac K F) 1
    rw [← Category.assoc, kPl_spec P0 (p ≫ prj K F (genusFK K F) l), e, ajK_self]
    rfl
  · by_contra hk
    apply hc (Sum.inr (Sum.inr (l, l')))
    show _ ∈ (if l = l' then ∅ else _)
    rw [if_neg hk]
    show (p ≫ ((prj K F (genusFK K F) l ≫ ajO P0) * (prj K F (genusFK K F) l' ≫ ajO P0)⁻¹)).left
      (IsLocalRing.closedPoint K) = pt (Jac K F) 1
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
      kPl_spec P0 (p ≫ prj K F (genusFK K F) l), kPl_spec P0 (p ≫ prj K F (genusFK K F) l'), e, mul_inv_cancel]
    rfl
  · have h := hc (Sum.inl ())
    exact not_not.mp h

end Pick

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cst =====
section

/-!
# S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
* `gff_eq_toStalk`, `gff_surjective` (on `Spec` of a field), `gff_sum`;
* `PsiX_stalkMap_val`, `PsiX_fpull_kff`: `PsiX` of the constant `c` pulled back to `X1` is `algebraMap K F c`;
* `fpull_phiX_val`: `phiX f` is regular at a `K`-point `q` with `0 ≤ ord f`, with value `kff c`, `cval q (phiX f) = c`;
* **`fpull_phiX_incB`**: at `q` with `kPl q = inl (ptP φ)`, `fpull q (phiX (incB r)) = kff (φ r)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR RamanujanPetersson.JacLaw
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Gff

variable {R : Type u} [CommRing R] [IsDomain R]

end Gff

section Cst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **Value of `phiX (incB r)` at a `K`-point over the finite place `ptP φ`.** -/
theorem fpull_phiX_incB (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)
    (φ : Places.Rfin K F →ₐ[K] K) (hq : kPl q = Sum.inl (ptP φ)) (r : Places.Rfin K F) :
    RegAt (q.left (genericPoint _)) (phiX K F (incB K F r)) ∧
      fpull q.left (phiX K F (incB K F r)) = kff (φ r) := by
  have hf : 0 ≤ (kPl q).ord (incB K F r) := by
    rw [hq]
    exact ord_incB_nonneg _ r
  obtain ⟨hreg, c, hc1, hc2⟩ := fpull_phiX_val hg q _ hf
  refine ⟨hreg, hc1.trans (congrArg kff ?_)⟩
  have hinc : incB K F (r - algebraMap K (Places.Rfin K F) c) =
      incB K F r - cval K F q (phiX K F (incB K F r)) := by
    rw [hc2, map_sub, AlgHom.commutes]
  by_cases h0 : r - algebraMap K (Places.Rfin K F) c = 0
  · rw [sub_eq_zero.mp h0, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  · have hne : incB K F r - cval K F q (phiX K F (incB K F r)) ≠ 0 := by
      rw [← hinc]
      exact fun h => h0 (incB_injective (by rw [h, map_zero]))
    have hpos := ord_sub_cval_pos hg q _ hf hne
    rw [← hinc, hq] at hpos
    change 0 < Places.ord (ptP φ) _ at hpos
    have h1 := apply_eq_zero_of_ord (φ := φ) h0 (by omega)
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h1
    exact h1.symm

end Cst

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrPP =====
section

/-!
# S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
* `blk n β S := {k | β k ∈ S}` (the coordinates multiplied in `psiS P0 n β S`);
* `trace_val`: at a `K`-point `yR` of the chart, `yR (tr f) = Σ_{ψ ∈ ptSet yR} ψ f`;
* `trPP_val`: at a `K`-point `p` of `X1^n` such that `p ≫ ψ_S` lies on the translated chart at `yR` and the block points
  `p ≫ pr_k` (`k ∈ blk`) are the distinct points of `yR`, both sides of the identity are regular with equal values;
* **`trPP`**: if this holds on a nonempty open, `ψ_S^* (trJ d f) = Σ_{k ∈ blk} pr_k^* (phiX f)` in `K(X1^n)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR RamanujanPetersson.JacLaw
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section TrPP

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

open Classical in
/-- **Pointwise form of the block trace identity.** -/
theorem trPP_val (hg : 0 < genusFK K F) (P0 : Place K F) (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3))
    (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (f : Places.Rfin K F) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n)
    (yR : LawRing K F →ₐ[K] K)
    (hp : (p ≫ psiS P0 n β S).left = Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K)) ≫ tauX d)
    (a' : Fin n → (Places.Rfin K F →ₐ[K] K))
    (ha : ∀ k ∈ blk n β S, kPl (p ≫ prj K F n k) = Sum.inl (ptP (a' k)))
    (hinj : Set.InjOn a' (blk n β S))
    (him : (blk n β S).image a' = ptSet (yR.comp (awayι (K := K) (lawPre K F).u0))) :
    RegAt (p.left (genericPoint _)) (fpull (psiS P0 n β S).left (trJ d f)) ∧
      RegAt (p.left (genericPoint _)) (∑ k ∈ blk n β S, fpull (prj K F n k).left (phiX K F (incB K F f))) ∧
      fpull p.left (fpull (psiS P0 n β S).left (trJ d f)) =
        fpull p.left (∑ k ∈ blk n β S, fpull (prj K F n k).left (phiX K F (incB K F f))) := by
  obtain ⟨hL1, hL2⟩ := trJ_val_of d yR f _ hp
  obtain ⟨hL3, hL4⟩ := regAt_fpull p.left (psiS P0 n β S).left hL1
  have hR : ∀ k ∈ blk n β S,
      RegAt (p.left (genericPoint _)) (fpull (prj K F n k).left (phiX K F (incB K F f))) ∧
        fpull p.left (fpull (prj K F n k).left (phiX K F (incB K F f))) = kff (a' k f) := fun k hk => by
    obtain ⟨h1, h2⟩ := fpull_phiX_incB hg (p ≫ prj K F n k) (a' k) (ha k hk) f
    obtain ⟨h3, h4⟩ := regAt_fpull p.left (prj K F n k).left h1
    exact ⟨h3, h4.trans h2⟩
  refine ⟨hL3, Subring.sum_mem _ fun k hk => (hR k hk).1, ?_⟩
  have hL : fpull p.left (fpull (psiS P0 n β S).left (trJ d f)) =
      kff (yR (awayι (K := K) (lawPre K F).u0 (traceS K f))) := hL4.trans hL2
  rw [hL, fpull_sum_of p.left _ _ fun k hk => (hR k hk).1, Finset.sum_congr rfl fun k hk => (hR k hk).2,
    show ∑ k ∈ blk n β S, kff (a' k f) = kff (∑ k ∈ blk n β S, a' k f) from (gff_sum _ _).symm]
  congr 1
  rw [trace_val, ← him, Finset.sum_image hinj]

end TrPP

end RamanujanPetersson.ThetaCube


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

end Poly

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (hg : 0 < genusFK K F) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
  (hx0 : pt (Jac K F) x0 ∉ W P0) (g : ℕ) (hdim : ∀ x : (Jac K F).left, Order.height x ≤ g)
  (π : Jac K F ⟶ Jac K F) [IsMonHom π]

include hg hx0 in
theorem cD_eq (G : ℤ[X]) : cD P0 x0 π G = cc P0 x0 π G + cc P0 x0 π (-G) := by
  rw [cD, (cpull_DTh P0 hg x0 hx0 _).2, cc, cc, polyEnd_neg]

include hg hx0 in
theorem hsym_D (G : ℤ[X]) : cD P0 x0 π (-G) - cD P0 x0 π G ∈ DegPoly.numKer (formTh K F g hdim) := by
  rw [cD, cD, polyEnd_neg, cpull_inv_DTh P0 hg x0 hx0, sub_self]
  exact zero_mem _

end Theta

end RamanujanPetersson.ThetaCube


end


