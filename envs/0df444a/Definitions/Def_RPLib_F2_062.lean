-- Prove2me | Definitions.Def_RPLib_F2_062
-- name    : RPLib_F2_062
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T21:49:18.938395+00:00
-- url     : https://prove2.me/theorems/cbb986cd-62ab-440e-be00-1377554f305f
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 062 of 70
-- statement:
--   File 062 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
--   * `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
--   * `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
--   * `S4.Def_RP_ThetaCube_TrPP`: S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
--   * `S4.Def_RP_ThetaCube_TrOpen`: S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
--   * `S4.Def_RP_ThetaCube_Asm2`: S4-ThetaCube, file Asm2 (D-B4, part 6c): the pull-back of the cube divisor along `Φ3` and the assembly
--   * `S4.Def_RP_ThetaCube_Hook`: S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`
--   * `S4.Def_RP_JacFrob_Mor`: S4-JacFrob, part Mor: the morphism `J ⟶ J` induced by an endomorphism of `S_g`
--   * `S4.Def_RP_JacFrob_MorE`: S4-JacFrob, part MorE: `mor φ hφ` on `D(φ u0)` and its uniqueness
--   * `S4.Def_RP_JacFrob_PiJ0`: S4-JacFrob, part PiJ0: `π_J⁰ = mor (PhiS hk g)`
--   * `S4.Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
--   * `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Val3`: S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_TanG`: S4-JacFrob, part TanG: the differential of `mor φ` (generic)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_061

/-!
# Ramanujan-Petersson curve library (flat edition), file 062 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
* `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
* `S4.Def_RP_ThetaCube_Test`: S4-ThetaCube, file Test (D-B4, part 4): the line test, one block product `S` at a time
* `S4.Def_RP_ThetaCube_TrPP`: S4-ThetaCube, file TrPP (D-C1, part 4): the block trace identity on `X1^n`
* `S4.Def_RP_ThetaCube_TrOpen`: S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
* `S4.Def_RP_ThetaCube_Asm2`: S4-ThetaCube, file Asm2 (D-B4, part 6c): the pull-back of the cube divisor along `Φ3` and the assembly
* `S4.Def_RP_ThetaCube_Hook`: S4-ThetaCube, file Hook (T8c): the `DegPoly` hypotheses for `D' = Θ_{x0} + [-1]^* Θ_{x0}`
* `S4.Def_RP_JacFrob_Mor`: S4-JacFrob, part Mor: the morphism `J ⟶ J` induced by an endomorphism of `S_g`
* `S4.Def_RP_JacFrob_MorE`: S4-JacFrob, part MorE: `mor φ hφ` on `D(φ u0)` and its uniqueness
* `S4.Def_RP_JacFrob_PiJ0`: S4-JacFrob, part PiJ0: `π_J⁰ = mor (PhiS hk g)`
* `S4.Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
* `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Val3`: S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_TanG`: S4-JacFrob, part TanG: the differential of `mor φ` (generic)
-/

set_option autoImplicit false

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

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

variable (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
  (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)

include hg hc in
/-- **Multiplicity one on the curve** (T4c): `D_e` is `1` at the plus-curve point `ι2 (kpt x)` when
`e = cE · c_φ⁻¹` (`φ = ptR2 x`) and `f_e` avoids `Θ`. -/
theorem Dc_plusX_eq_one (x : R2 c0 a i0 →ₐ[K] K)
    (hA : Avoid (feX P0 (cE a i0 P0 * (c (ptR2 c0 a i0 x))⁻¹)) (Theta P0)) :
    Dc P0 (cE a i0 P0 * (c (ptR2 c0 a i0 x))⁻¹) (ι2 c0 a i0 (kpt x)) = 1 := by
  haveI := isDomain_R2 c0 a i0 x
  haveI : Nonempty (Spec (.of (R2 c0 a i0))) := ⟨kpt x⟩
  haveI := isDominant_openImm (ι2 (F := F) c0 a i0)
  have hD := theta_mem_weilDivisors P0 hg
  rw [Dc, ← cpull_comp_openImm (ι2 c0 a i0) _ hD hA, plusX_fe]
  have hA2 := avoid_comp_left (ι2 c0 a i0) _ hA
  rw [plusX_fe] at hA2
  exact cpull_kappa_eq_one P0 c0 a i0 hg c hc x hA2

end Curve1

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve4 =====
section

/-!
# Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))

* `exists_of_Zdiv_pos`: a place in the support of `Zdiv S` is a point of `S`;
* `exists_mem_X0`: if `ℓ(W0 - G + 2[v]) = 1` and that class contains the reduced divisor `Zdiv S`, then `v ∈ S`;
* `exists_R2pt`: a point `φ` of an `X0` point with `φ(x - c0) ≠ 0` is `ptR2 x` for a `K`-point `x` of a plus chart;
* `Zdiv_image_eq`, `eq_cE`: class bookkeeping (`e = cE · c_φ⁻¹`);
* **`Dc_eq_one`**: for `e` of class `[W0 - G] - (g-2)[P0]` and `q` with `1 ≤ G (kPl q)`, `D_e` is `1` at `q`
  (hypotheses: `ℓ(W0 - G + 2[kPl q]) = 1`, an `X0` point in that class, `f_e` avoids `Θ`).
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

section Curve4

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

open Classical

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Multiplicity one at the points of `G`** (T4c step (B)): for `e` of class `[W0 - G] - (g-2)[P0]`
(`G ≥ 0`, `deg G = g`, `ℓ(G) = 1`) avoiding `Θ`, and a `K`-point `q` of `X1` with `1 ≤ G (kPl q)` such that
`ℓ(W0 - G + 2[kPl q]) = 1` and that class contains the divisor of an `X0` point, `D_e` is `1` at `q`. -/
theorem Dc_eq_one (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G) (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1)
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (he : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))
    (hA : Avoid (feX P0 e) (Theta P0))
    (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (hv : 1 ≤ G (kPl q))
    (h2 : ellFK K F (W0 - G + Finsupp.single (kPl q) 2) = 1)
    (yR : LawRing K F →ₐ[K] K)
    (hy : clsK K F (Zdiv (ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)))) =
      clsK K F (W0 - G + Finsupp.single (kPl q) 2)) :
    Dc P0 e (q.left (IsLocalRing.closedPoint K)) = 1 := by
  obtain ⟨c0, ψ0, hcen, hq⟩ := exists_chart0 hg q
  obtain ⟨φ, hφA, hvφ⟩ := exists_mem_X0 hW hG hd h1 hv h2 _ hy
  have hcen' : IsCenter (Sum.inl (ptP φ) : Place K F) (ψ0.comp diag1) := hvφ ▸ hcen
  have hxc : φ (xcR F c0) ≠ 0 := xcR_ne_of_isCenter c0 hcen'
  obtain ⟨t, i0, x, hx, him, ht, hti⟩ := exists_R2pt c0 yR hφA hxc
  choose c hc using fun ψ => exists_cJ P0 hg ψ
  have hq2 := eq_iota2 hcen hq t i0 x (by rw [hx, hvφ])
  have hy' : clsK K F (Zdiv (Finset.univ.image t)) =
      clsK K F (W0 - G + Finsupp.single (Sum.inl (ptP (t i0))) 2) := by
    rw [him, hti, ← hvφ]
    exact hy
  have heq : e = cE t i0 P0 * (c (ptR2 c0 t i0 x))⁻¹ := by
    rw [hx, ← hti]
    exact eq_cE hg P0 e he t ht i0 hy' c hc
  rw [hq2, heq]
  rw [heq] at hA
  exact Dc_plusX_eq_one P0 hg c0 t i0 c hc x hA

end Geom

end Curve4

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

/-- **The per-`S` line test, `β i0 ∉ S`**: both sides vanish at `z`. -/
theorem test_not_mem (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n)
    (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hS : β i0 ∉ S)
    (hW : pt (Jac K F) ((p ≫ psiE P0 n β S i0) * x0) ∉ W P0) {N r : ℕ} (τ : Fin N → Fin n)
    (m : Fin r → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F)) (h : Fin N ⊕ Fin r → F) (hτ : ∀ j, τ j ≠ i0)
    (H : Places.Divisor K F) (hH : ∀ l, h l ∈ LFK K F H) (hH0 : ∀ a, H (kPl (ptC K F n τ m p a)) = 0)
    (hinj : ∀ a b, kPl (ptC K F n τ m p a) = kPl (ptC K F n τ m p b) → a = b)
    (hli : LinearIndependent K h) (hell : ellFK K F (H - Zall K F n τ m p) = 0) :
    Avoid (line K F n i0 p).left (JacDivisors.div (PP K F n).left (detPP K F n τ m h)) ∧
      Avoid ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0) ∧
      cpull (line K F n i0 p).left (JacDivisors.div (PP K F n).left (detPP K F n τ m h))
          ((p ≫ prj K F n i0).left (IsLocalRing.closedPoint K)) =
        cpull ((line K F n i0 p ≫ psiS P0 n β S) ≫ transl (Jac K F) x0).left (Theta P0)
          ((p ≫ prj K F n i0).left (IsLocalRing.closedPoint K)) := by
  have hne := slice_ne_zero_const hg n τ m h i0 p hτ H hH hH0 hinj hli hell
  obtain ⟨hA1, e1⟩ := cpull_detPP_kpt hg n τ m h i0 p
    (fun j _ l => ord_nonneg_of_mem_LFK (hH l) (hH0 (Sum.inl j)))
    (fun i l => ord_nonneg_of_mem_LFK (hH l) (hH0 (Sum.inr i))) hne
  obtain ⟨hA2, e2⟩ := cube_side_not_mem P0 hg n β S i0 p x0 hS hW
  refine ⟨hA1, hA2, ?_⟩
  rw [e1, e2, ord_slice_const n τ m h i0 p hτ hne]
  rfl

end Test

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
/-- **The block trace identity** `ψ_S^* (trJ d f) = Σ_{k ∈ blk} pr_k^* (phiX f)`, from its values at the `K`-points
of a nonempty open. -/
theorem trPP (hg : 0 < genusFK K F) (P0 : Place K F) (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3))
    (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (f : Places.Rfin K F) {V : Set (PP K F n).left} (hV : IsOpen V)
    (hne : V.Nonempty)
    (hH : ∀ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n, p.left (genericPoint _) ∈ V →
      ∃ yR : LawRing K F →ₐ[K] K,
        (p ≫ psiS P0 n β S).left = Spec.map (CommRingCat.ofHom (yR : LawRing K F →+* K)) ≫ tauX d ∧
        ∃ a' : Fin n → (Places.Rfin K F →ₐ[K] K),
          (∀ k ∈ blk n β S, kPl (p ≫ prj K F n k) = Sum.inl (ptP (a' k))) ∧ Set.InjOn a' (blk n β S) ∧
            (blk n β S).image a' = ptSet (yR.comp (awayι (K := K) (lawPre K F).u0))) :
    fpull (psiS P0 n β S).left (trJ d f) =
      ∑ k ∈ blk n β S, fpull (prj K F n k).left (phiX K F (incB K F f)) :=
  eq_of_kpt _ _ hV hne fun p hp => by
    obtain ⟨yR, hp', a', ha, hinj, him⟩ := hH p hp
    exact trPP_val hg P0 n β S d f p yR hp' a' ha hinj him

end TrPP

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_TrOpen =====
section

/-!
# S4-ThetaCube, file TrOpen (D-C1, part 5): the open where the block trace identity is checked
* `jacPic_psiS`, `cls_psiS`: the class of `p ≫ ψ_S` is `[Σ_{k ∈ blk} p_k] - #blk [P0]`;
* `ell_one_of_cls`: off `W`, a degree-`g` divisor in the class `[e] + g[P0]` has `ℓ = 1`;
* `blocks_of_Zdiv`: `Zdiv T = Σ_{k ∈ s} [v k]` with `#s = #T` makes `v` a bijection onto the points of `T`;
* `VJ P0 d := {x | x d⁻¹ ∈ jX0 (X0)} \ W` (open), `exists_yR_of_mem_VJ`;
* **`hH_of_mem`**: hypothesis (H) of `trPP` at every `K`-point of `ψ_S⁻¹ VJ` (`#blk = g`, `[d] = [Θ] - g[P0]`);
* **`trPP_open`**: the block trace identity once `ψ_S⁻¹ VJ` is nonempty.
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

section TrOpen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **The block trace identity on `X1^n`** once the open `ψ_S⁻¹ VJ` is nonempty. -/
theorem trPP_open (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3))
    (hS : (blk n β S).card = genusFK K F) (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hd : ((Multiplicative.toAdd (jacPicEquiv K F d) : Pic0K K F) : PicK K F) =
      thetaK K F - (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1)) (f : Places.Rfin K F)
    (hne : ((psiS P0 n β S).left ⁻¹' VJ P0 d).Nonempty) :
    fpull (psiS P0 n β S).left (trJ d f) =
      ∑ k ∈ blk n β S, fpull (prj K F n k).left (phiX K F (incB K F f)) :=
  trPP hg P0 n β S d f ((isOpen_VJ P0 d).preimage (psiS P0 n β S).left.continuous) hne
    fun p hp => hH_of_mem P0 hg n β S hS d hd p hp

end TrOpen

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

/-- **`cpull` of `Φ3^* cubeZ` along any curve `L` into `X1^n`**: the signed sum over `S` of the `Θ` sides. -/
theorem cpull_PB (hg : 0 < genusFK K F) (n : ℕ) (β : Fin n → Fin 3) (x0 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    [IsDominant (Phi3 P0 n β).left] (L : X1O K F ⟶ PP K F n)
    (h012 : Avoid ((L ≫ psiS P0 n β {0, 1, 2}) ≫ transl (Jac K F) x0).left (Theta P0))
    (h01 : Avoid ((L ≫ psiS P0 n β {0, 1}) ≫ transl (Jac K F) x0).left (Theta P0))
    (h02 : Avoid ((L ≫ psiS P0 n β {0, 2}) ≫ transl (Jac K F) x0).left (Theta P0))
    (h12 : Avoid ((L ≫ psiS P0 n β {1, 2}) ≫ transl (Jac K F) x0).left (Theta P0))
    (h0 : Avoid ((L ≫ psiS P0 n β {0}) ≫ transl (Jac K F) x0).left (Theta P0))
    (h1 : Avoid ((L ≫ psiS P0 n β {1}) ≫ transl (Jac K F) x0).left (Theta P0))
    (h2 : Avoid ((L ≫ psiS P0 n β {2}) ≫ transl (Jac K F) x0).left (Theta P0)) :
    Avoid L.left (JacDivisors.pullback (Phi3 P0 n β).left (cubeZ P0 x0)) ∧
      cpull L.left (JacDivisors.pullback (Phi3 P0 n β).left (cubeZ P0 x0)) =
        cpull ((L ≫ psiS P0 n β {0, 1, 2}) ≫ transl (Jac K F) x0).left (Theta P0) -
          cpull ((L ≫ psiS P0 n β {0, 1}) ≫ transl (Jac K F) x0).left (Theta P0) -
          cpull ((L ≫ psiS P0 n β {0, 2}) ≫ transl (Jac K F) x0).left (Theta P0) -
          cpull ((L ≫ psiS P0 n β {1, 2}) ≫ transl (Jac K F) x0).left (Theta P0) +
          cpull ((L ≫ psiS P0 n β {0}) ≫ transl (Jac K F) x0).left (Theta P0) +
          cpull ((L ≫ psiS P0 n β {1}) ≫ transl (Jac K F) x0).left (Theta P0) +
          cpull ((L ≫ psiS P0 n β {2}) ≫ transl (Jac K F) x0).left (Theta P0) := by
  have e1 : (L ≫ Phi3 P0 n β) ≫ q1 K F = L ≫ psiS P0 n β {0} := by rw [Category.assoc, Phi3_q1]
  have e2 : (L ≫ Phi3 P0 n β) ≫ q2 K F = L ≫ psiS P0 n β {1} := by rw [Category.assoc, Phi3_q2]
  have e3 : (L ≫ Phi3 P0 n β) ≫ q3 K F = L ≫ psiS P0 n β {2} := by rw [Category.assoc, Phi3_q3]
  have hu : ∀ (a : Fin 3) (s : Finset (Fin 3)), a ∉ s →
      (L ≫ psiS P0 n β {a}) * (L ≫ psiS P0 n β s) = L ≫ psiS P0 n β (insert a s) := by
    intro a s ha
    rw [comp_psiS_mul P0 L β (Finset.disjoint_singleton_left.mpr ha), Finset.insert_eq]
  have e12 : ((L ≫ Phi3 P0 n β) ≫ q1 K F) * ((L ≫ Phi3 P0 n β) ≫ q2 K F) = L ≫ psiS P0 n β {0, 1} := by
    rw [e1, e2, hu 0 {1} (by decide)]
  have e13 : ((L ≫ Phi3 P0 n β) ≫ q1 K F) * ((L ≫ Phi3 P0 n β) ≫ q3 K F) = L ≫ psiS P0 n β {0, 2} := by
    rw [e1, e3, hu 0 {2} (by decide)]
  have e23 : ((L ≫ Phi3 P0 n β) ≫ q2 K F) * ((L ≫ Phi3 P0 n β) ≫ q3 K F) = L ≫ psiS P0 n β {1, 2} := by
    rw [e2, e3, hu 1 {2} (by decide)]
  have e123 : ((L ≫ Phi3 P0 n β) ≫ q1 K F) * ((L ≫ Phi3 P0 n β) ≫ q2 K F) * ((L ≫ Phi3 P0 n β) ≫ q3 K F) =
      L ≫ psiS P0 n β {0, 1, 2} := by
    rw [_root_.mul_assoc, e23, e1, hu 0 {1, 2} (by decide)]
  obtain ⟨hA, hc⟩ := cpull_cubeZ_X1 P0 hg x0 (L ≫ Phi3 P0 n β) (by rw [e123]; exact h012) (by rw [e12]; exact h01)
    (by rw [e13]; exact h02) (by rw [e23]; exact h12) (by rw [e1]; exact h0) (by rw [e2]; exact h1)
    (by rw [e3]; exact h2)
  refine ⟨avoid_pullback L.left (Phi3 P0 n β).left (cubeZ_mem P0 x0) hA, ?_⟩
  rw [← cpull_comp L.left (Phi3 P0 n β).left (cubeZ_mem P0 x0) hA]
  refine hc.trans ?_
  simp only [cubeC]
  rw [e123, e12, e13, e23, e1, e2, e3]

end Asm2

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
theorem iform_cD (φ : Jac K F ⟶ Jac K F) [IsMonHom φ] :
    iform (Jac K F) g hdim (fun _ => cpull φ.left (DTh P0 x0)) =
      (degree φ.left : ℤ) * iform (Jac K F) g hdim (fun _ => DTh P0 x0) := by
  have h := iform_cpull_comp (Jac K F) g hdim φ 1 (DTh_mem P0 x0) (DTh_nonneg P0 hg x0 hx0)
    (by rw [transl_one, Category.comp_id]; exact (cpull_DTh P0 hg x0 hx0 φ).1)
  rwa [transl_one, Category.comp_id] at h

include hg hx0 in
theorem hzero_D : cD P0 x0 π 0 ∈ DegPoly.numKer (formTh K F g hdim) := by
  have h := cpull_eq_zero_of_eq_one (IsogDegB.polyEnd π 0) (polyEnd_zero π) 1 (DTh_mem P0 x0)
    (by rw [transl_one, Category.comp_id]; exact (cpull_DTh P0 hg x0 hx0 _).1)
  rw [transl_one, Category.comp_id] at h
  rw [cD, h]
  exact zero_mem _

include hg hx0 in
theorem hproj_D (G : ℤ[X]) :
    formTh K F g hdim (fun _ => cD P0 x0 π G) =
      (degree (IsogDegB.polyEnd π G).left : ℤ) * formTh K F g hdim (fun _ => cD P0 x0 π 1) := by
  rw [formTh_apply, formTh_apply, cD, cD, iform_cD P0 hg x0 hx0, iform_cD P0 hg x0 hx0, polyEnd_one,
    Over.id_left, degree_id, Nat.cast_one, _root_.one_mul]

include hg hx0 in
/-- `(D'^g) > 0`: expand `(A + B)^g`; every mixed term is an intersection number of effective divisors. -/
theorem iform_DTh_pos (hg' : ∃ x : (Jac K F).left, (g : ℕ∞) ≤ Order.height x) :
    0 < iform (Jac K F) g hdim (fun _ => DTh P0 x0) := by
  have hT := theta_mem_weilDivisors P0 hg
  have hA1 := avoid_one_transl P0 x0 hx0
  have hA2 := avoid_negJ_transl P0 x0 hx0
  have hW1 := pullback_mem_weilDivisors (transl (Jac K F) x0).left (Theta P0)
  have hW2 := pullback_mem_weilDivisors (negJ K F ≫ transl (Jac K F) x0).left (Theta P0)
  have h01 : ∀ z, 0 ≤ JacDivisors.pullback (transl (Jac K F) x0).left (Theta P0) z := by
    rw [← cpull_eq_pullback _ hT hA1]
    exact fun z => cpull_nonneg _ hT hA1 z fun w _ _ => Theta_nonneg P0 w
  have h02 : ∀ z, 0 ≤ JacDivisors.pullback (negJ K F ≫ transl (Jac K F) x0).left (Theta P0) z := by
    rw [← cpull_eq_pullback _ hT hA2]
    exact fun z => cpull_nonneg _ hT hA2 z fun w _ _ => Theta_nonneg P0 w
  rw [← formTh_apply, show (fun _ : Fin g => DTh P0 x0) =
      (fun _ => JacDivisors.pullback (transl (Jac K F) x0).left (Theta P0)) +
        (fun _ => JacDivisors.pullback (negJ K F ≫ transl (Jac K F) x0).left (Theta P0)) from rfl,
    MultilinearMap.map_add_univ]
  refine Finset.sum_pos' (fun s _ => ?_) ⟨Finset.univ, Finset.mem_univ _, ?_⟩
  · rw [formTh_apply, iform_eq_inumZ (Jac K F) (fun x => inferInstance) g hdim _
      (fun i => by unfold Finset.piecewise; split_ifs; exacts [hW1, hW2])
      (fun i z => by unfold Finset.piecewise; split_ifs; exacts [h01 z, h02 z]), inumZ]
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl
  · rw [Finset.piecewise_univ, formTh_apply, ← cpull_eq_pullback _ hT hA1,
      iform_cpull_transl (Jac K F) g hdim x0 hT (fun z => Theta_nonneg P0 z) hA1]
    exact iform_Theta_pos P0 hg g hdim hg'

include hg hx0 in
theorem hD_D (hg' : ∃ x : (Jac K F).left, (g : ℕ∞) ≤ Order.height x) :
    formTh K F g hdim (fun _ => cD P0 x0 π 1) ≠ 0 := by
  rw [formTh_apply, cD, iform_cD P0 hg x0 hx0, polyEnd_one, Over.id_left, degree_id, Nat.cast_one,
    _root_.one_mul]
  exact (iform_DTh_pos P0 hg x0 hx0 g hdim hg').ne'

include hg hx0 in
theorem cube_cc (hZ : CubePrincipal P0 x0) (a b e : ℤ[X]) :
    cc P0 x0 π (a + b + e) - cc P0 x0 π (a + b) - cc P0 x0 π (a + e) - cc P0 x0 π (b + e) +
      cc P0 x0 π a + cc P0 x0 π b + cc P0 x0 π e ∈ DegPoly.numKer (formTh K F g hdim) := by
  obtain ⟨n, hn, h, hh, hZh⟩ := hZ
  have := cubeC_mem_numKer P0 hg g hdim x0 hx0 hn hh hZh (IsogDegB.polyEnd π a) (IsogDegB.polyEnd π b)
    (IsogDegB.polyEnd π e)
  simp only [cc, IsogDegB.polyEnd_add]
  exact this

include hg hx0 in
theorem hcube_D (hZ : CubePrincipal P0 x0) (a b e : ℤ[X]) :
    cD P0 x0 π (a + b + e) - cD P0 x0 π (a + b) - cD P0 x0 π (a + e) - cD P0 x0 π (b + e) +
      cD P0 x0 π a + cD P0 x0 π b + cD P0 x0 π e ∈ DegPoly.numKer (formTh K F g hdim) := by
  have h := add_mem (cube_cc P0 hg x0 hx0 g hdim π hZ a b e) (cube_cc P0 hg x0 hx0 g hdim π hZ (-a) (-b) (-e))
  simp only [cD_eq P0 hg x0 hx0, neg_add]
  convert h using 1
  abel

include hg hx0 in
/-- **The quadratic relation** (output of `DegPoly.quad_of_cube`) for `c G := (polyEnd π G)^* D'`. -/
theorem quad_D (hZ : CubePrincipal P0 x0) (a b : ℤ[X]) :
    ∃ e : AlgebraicCycle (Jac K F).left ℤ, ∀ n : ℤ,
      cD P0 x0 π (n * a + b) - (n ^ 2 • cD P0 x0 π a + n • e + cD P0 x0 π b) ∈
        DegPoly.numKer (formTh K F g hdim) :=
  DegPoly.quad_of_cube (formTh K F g hdim) (cD P0 x0 π) (hzero_D P0 hg x0 hx0 g hdim π)
    (hsym_D P0 hg x0 hx0 g hdim π) (hcube_D P0 hg x0 hx0 g hdim π hZ) a b

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_JacFrob_Mor =====
section

/-!
# S4-JacFrob, part Mor: the morphism `J ⟶ J` induced by an endomorphism of `S_g`

Generic (JacComplete context `K F : Type u`, `[IsAlgClosed K]`): a `K`-algebra map `φ : S_g → S_g` with
`φ u0 ≠ 0` gives `rho φ : S_g[1/u0] → S_g[1/u0][1/φ u0]`, hence the partial map `jX0(D(φ u0)) ⇢ J`
(`Spec (rho φ)` followed by `jX0`), and Weil extension (`extJ`) turns it into `mor φ hφ : J ⟶ J` over `K`:
`eJ φ : Spec S_g[1/u0][1/φ u0] ⟶ J`; `eJ_mor`, `eq_mor` are in `Def_RP_JacFrob_MorE`.
The special case `piJ0 hk := mor (PhiS hk g)` is in `Def_RP_JacFrob_PiJ0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Mor

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

/-- **The morphism `J ⟶ J` over `K` induced by `φ`** (Weil extension of `pmap`). -/
noncomputable def mor (hφ : φ (lawPre K F).u0 ≠ 0) : Jac K F ⟶ Jac K F :=
  extJ (pmap φ hφ) (pmap_over φ hφ)

end Mor

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_MorE =====
section

/-!
# S4-JacFrob, part MorE: `mor φ hφ` on `D(φ u0)` and its uniqueness

* `eJ_mor : eJ φ ≫ (mor φ hφ).left = Spec.map (rho φ) ≫ jX0`;
* `eq_mor`: `mor φ hφ` is the only map `J ⟶ J` over `K` with this property.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Mor

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

theorem eJ_mor (hφ : φ (lawPre K F).u0 ≠ 0) :
    eJ φ ≫ (mor φ hφ).left = Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ jX0 K F := by
  have h : (eJ φ).opensRange.ι ≫ (mor φ hφ).left =
      (eJ φ).isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ jX0 K F :=
    ι_extJ (pmap φ hφ) (pmap_over φ hφ)
  rw [← (eJ φ).isoOpensRange_hom_ι, Category.assoc, h, Iso.hom_inv_id_assoc]

end Mor

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_PiJ0 =====
section

/-!
# S4-JacFrob, part PiJ0: `π_J⁰ = mor (PhiS hk g)`

* `PhiS_u0_ne`: `Φ_S u0 ≠ 0` (`symMap_injective` + `PhiR_injective`);
* `piJ0 hk : J ⟶ J` over `k-bar` (`J = Jac k-bar F-bar`), the morphism induced by `Φ = (·)^q ∘ σ⁻¹` on `S_g`;
* `eJ_piJ0`: on `D(Φ_S u0) ⊆ X0` it is `Spec (rho Φ_S)` followed by `jX0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

section PiJ0

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

set_option synthInstance.maxHeartbeats 100000 in
/-- **`π_J⁰`**: the morphism of `J = J_{F-bar}` over `k-bar` induced by `Φ = (·)^q ∘ σ⁻¹` on `S_g`. -/
noncomputable def piJ0 : Jac (kbar Fq Ω) (Fbar Fq F Ω) ⟶ Jac (kbar Fq Ω) (Fbar Fq F Ω) :=
  mor (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) (PhiS_u0_ne Fq F Ω hk)

end PiJ0

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Val =====
section

/-!
# S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`

Generic (JacComplete context `K F : Type u`, `[IsAlgClosed K]`):
* `kptEquiv_of_jX0`, `jacPicEquiv_of_jX0`: a `K`-point `a` of `J` with closed point `jX0 x` (`x` closed in `X0`) has value
  `lamB x` in `H` and class `psiJ x` in `Pic⁰`;
* `eJ_kpt`, `mor_kpt`: `mor φ hφ` sends `jX0 (kpt (z ∘ ι))` to `jX0 (kpt (z ∘ rho φ))` for `z : S_g[1/u0][1/φ u0] →ₐ[K] K`;
* `jacPicEquiv_mor`: the class of `a ≫ mor φ hφ` is `psiJ (kpt (z ∘ rho φ))`;
* `zOf`, `zOf_comp`: every `y` with `y (φ u0) ≠ 0` factors through `S_g[1/u0][1/φ u0]`;
* `comp_rho_S`: on `S_g`, `z ∘ rho φ` is `(z ∘ ι) ∘ φ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacFrob

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open RamanujanPetersson.JacComplete RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Val

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

theorem mor_kpt (hφ : φ (lawPre K F).u0 ≠ 0) (z : BRing φ →ₐ[K] K) :
    (mor φ hφ).left (jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))))) =
      jX0 K F (kpt (z.comp (rho φ))) := by
  have h := congrArg (fun f : Spec (.of (BRing φ)) ⟶ (Jac K F).left => f (kpt z)) (eJ_mor φ hφ)
  simp only [Scheme.Hom.comp_apply] at h
  rw [eJ_kpt] at h
  rw [h]
  exact congrArg (fun p => jX0 K F p) (SpecMap_kpt (rho φ) z)

/-- **Values of `mor φ hφ`**: a `K`-point with closed point `jX0 (kpt (z ∘ ι))` goes to the class `psiJ (kpt (z ∘ rho φ))`. -/
theorem jacPicEquiv_mor (hφ : φ (lawPre K F).u0 ≠ 0) (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (z : BRing φ →ₐ[K] K)
    (ha : a.left (IsLocalRing.closedPoint K) =
      jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))))) :
    ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ mor φ hφ)) : Pic0K K F) : PicK K F) =
      psiJ K F (kpt (z.comp (rho φ))) :=
  jacPicEquiv_of_jX0 _ _ (JacLaw.isClosed_kpt _) (by rw [left_comp_closedPoint, ha, mor_kpt])

end Val

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

end SymPt

section Gen

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

/-- The class of `a ≫ mor φ hφ`: `[Z(y_S ∘ φ)] - [Θ]`. -/
theorem cls_mor (hφ : φ (lawPre K F).u0 ≠ 0) (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (z : BRing φ →ₐ[K] K)
    (ha : a.left (IsLocalRing.closedPoint K) =
      jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))))) :
    ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ mor φ hφ)) : Pic0K K F) : PicK K F) =
      clsK K F (Zdiv (ptSet (((z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))).comp
        (IsScalarTower.toAlgHom K (SymRing K (Places.Rfin K F) (genusFK K F)) (LawRing K F))).comp φ))) -
        thetaK K F := by
  rw [jacPicEquiv_mor φ hφ a z ha, psiJ_kpt, comp_rho_S]

/-- `[a ≫ mor φ hφ] = s[a] + (s[Θ] - [Θ])` when `Z(y ∘ φ) = s Z(y)` on classes. -/
theorem cls_mor_hom (hφ : φ (lawPre K F).u0 ≠ 0) (s : PicK K F ≃+ PicK K F)
    (hs : ∀ y : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] K,
      clsK K F (Zdiv (ptSet (y.comp φ))) = s (clsK K F (Zdiv (ptSet y))))
    (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (z : BRing φ →ₐ[K] K)
    (ha : a.left (IsLocalRing.closedPoint K) =
      jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))))) :
    ((Multiplicative.toAdd (jacPicEquiv K F (a ≫ mor φ hφ)) : Pic0K K F) : PicK K F) =
      s ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F) + (s (thetaK K F) - thetaK K F) := by
  rw [cls_mor φ hφ a z ha, cls_of_kpt φ a z ha, hs, map_sub]
  abel

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
/-- **`π_J`**: the `q`-Frobenius of `J = J_{F-bar}` over `k-bar`: `π_J⁰` followed by translation by `cPt`. -/
noncomputable def piJ : Jac (kbar Fq Ω) (Fbar Fq F Ω) ⟶ Jac (kbar Fq Ω) (Fbar Fq F Ω) :=
  piJ0 Fq F Ω hk * (toUnit _ ≫ cPt Fq F Ω hk)

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

theorem comp_eq_const_of (hφ : φ (lawPre K F).u0 ≠ 0) (g : IsogDegB.DS K ⟶ Jac K F)
    (f : BRing φ →ₐ[K] DualNumber K) (hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ eJ φ = g.left)
    (y : LawRing K F →ₐ[K] K) (hy : f.comp (rho φ) = (Algebra.ofId K (DualNumber K)).comp y) :
    (g ≫ mor φ hφ).left = (toUnit _ ≫ kptJ y).left := by
  rw [Over.comp_left, Over.comp_left, Over.toUnit_left, kptJ, ← hf, Category.assoc, eJ_mor]
  show Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom (rho φ).toRingHom) ≫ jX0 K F =
    Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ Spec.map (CommRingCat.ofHom y.toRingHom) ≫ jX0 K F
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun l => ?_)
  first
    | exact DFunLike.congr_fun hy l
    | (simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
       exact DFunLike.congr_fun hy l)

theorem comp_mor_const (hφ : φ (lawPre K F).u0 ≠ 0)
    (H : ∀ (f : BRing φ →ₐ[K] DualNumber K) (s : SymRing K (Places.Rfin K F) (genusFK K F)),
      (f (gB φ s)).snd = 0)
    (g : IsogDegB.DS K ⟶ Jac K F)
    (hg : g.left (IsLocalRing.closedPoint (DualNumber K)) ∈ (eJ φ).opensRange) :
    ∃ e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, g ≫ mor φ hφ = toUnit _ ≫ e := by
  obtain ⟨f, hf⟩ := exists_lift_DS φ g hg
  exact ⟨kptJ _, Over.OverMorphism.ext (X := Spec (.of K)) (U := IsogDegB.DS K) (V := Jac K F)
    (comp_eq_const_of φ hφ g f hf _ (rho_comp_eq φ f (H f)))⟩

end TanG

end RamanujanPetersson.JacFrob


end


