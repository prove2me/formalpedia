-- Prove2me | Definitions.Def_RPLib_F2_053
-- name    : RPLib_F2_053
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T20:17:14.737342+00:00
-- url     : https://prove2.me/theorems/41e10dc1-2bf1-48a6-b12a-fad6604a0108
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 053 of 70
-- statement:
--   File 053 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_CommJ`: The Jacobian (unit S4-JacComplete), part `CommJ` (L22: `J` is commutative)
--   * `S4.Def_RP_JacComplete_PicLaw`: The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)
--   * `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
--   * `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
--   * `S4.Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
--   * `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Val3`: S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`
--   * `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
--   * `S4.Def_RP_JacFrob_All`: S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`
--   * `S4.Def_RP_JacFrob_TanG`: S4-JacFrob, part TanG: the differential of `mor φ` (generic)
--   * `S4.Def_RP_JacFrob_Tan`: S4-JacFrob, part Tan: **`dπ_J = 1`**
--   * `S4.Def_RP_JacFrob_PolyG`: S4-JacFrob, part PolyG: `ℤ[π] → End(J)` on points, generically
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_049

/-!
# Ramanujan-Petersson curve library (flat edition), file 053 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_CommJ`: The Jacobian (unit S4-JacComplete), part `CommJ` (L22: `J` is commutative)
* `S4.Def_RP_JacComplete_PicLaw`: The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)
* `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
* `S4.Def_RP_ThetaCube_CubeZ`: S4-ThetaCube, file CubeZ (T5b): the cube divisor on `J^3` and its pull-back along `(α, β, ga)`
* `S4.Def_RP_JacFrob_Val`: S4-JacFrob, part Val: values of `mor φ hφ` on the `K`-points of `J` coming from `D(φ u0)`
* `S4.Def_RP_JacFrob_Val2`: S4-JacFrob, part Val2: `[a ≫ π_J⁰] = σ_*[a] + c` on `K`-points over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Val3`: S4-JacFrob, part Val3: `π_J := π_J⁰ · (translation by cPt)` and `[a ≫ π_J] = σ_*[a]` over `D(u0) ∩ D(Φ u0)`
* `S4.Def_RP_JacFrob_Hom`: S4-JacFrob, part Hom: `π_J` is a homomorphism of group objects
* `S4.Def_RP_JacFrob_All`: S4-JacFrob, part All: `[a ≫ π_J] = σ_*[a]` for every `K`-point; `π_J` is the arithmetic Frobenius on `Pic(X-bar)`
* `S4.Def_RP_JacFrob_TanG`: S4-JacFrob, part TanG: the differential of `mor φ` (generic)
* `S4.Def_RP_JacFrob_Tan`: S4-JacFrob, part Tan: **`dπ_J = 1`**
* `S4.Def_RP_JacFrob_PolyG`: S4-JacFrob, part PolyG: `ℤ[π] → End(J)` on points, generically
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_CommJ =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `CommJ` (L22: `J` is commutative)

`H_comm_lawChunk`: the chunk group `H` of Weil's law is commutative (the law is commutative at points,
`lawData_rel_comm`, so `λ_a = ρ_a`); **`isCommMonObj_Jac`**: the Jacobian `Jac K F` is a commutative group scheme.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Jac

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **L22: the Jacobian is commutative.** -/
instance isCommMonObj_Jac : IsCommMonObj (Jac K F) := isCommMonObj_Jac_of_comm K F (H_comm_lawChunk K F)

end Jac

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_PicLaw =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicLaw` (L20: the class map of Weil's law)

* `psiJ K F : X0 → PicK`, additive (`chunkAdd_lawChunk`) and rigid (`chunkRigid_lawChunk`); `card_lawPt`, `deg_psiJ`;
* **`jacPic0 K F : H →* Multiplicative (Pic0K K F)`**, `jacPic0_injective`, `jacPic0_lamB`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Jac

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem Phi_mem_Pic0K (σ : (lawChunk K F).H) : Phi (psiJ K F) σ.1 ∈ Pic0K K F := by
  obtain ⟨x, y, hx, hy, h⟩ := exists_takes σ.1
  rw [Phi_spec (chunkAdd_lawChunk K F) (H_comm_lawChunk K F) σ.1 σ.2 hx hy h, mem_Pic0K, map_sub,
    deg_psiJ K F y hy, deg_psiJ K F x hx, sub_self]

/-- **The class map** `H → Pic⁰`, `σ ↦ [σ(D) - D]` (L20). -/
noncomputable def jacPic0 : (lawChunk K F).H →* Multiplicative (Pic0K K F) :=
  MonoidHom.mk' (fun σ => Multiplicative.ofAdd (⟨Phi (psiJ K F) σ.1, Phi_mem_Pic0K K F σ⟩ : Pic0K K F))
    fun σ τ => by
      rw [← ofAdd_add]
      exact congrArg Multiplicative.ofAdd (Subtype.ext
        (Phi_mul (chunkAdd_lawChunk K F) (H_comm_lawChunk K F) σ.1 τ.1 σ.2 τ.2))

theorem jacPic0_apply (σ : (lawChunk K F).H) :
    ((Multiplicative.toAdd (jacPic0 K F σ) : Pic0K K F) : PicK K F) = Phi (psiJ K F) σ.1 := rfl

theorem jacPic0_injective : Function.Injective (jacPic0 K F) := by
  intro σ τ h
  apply PhiHom_injective (chunkAdd_lawChunk K F) (H_comm_lawChunk K F) (chunkRigid_lawChunk K F)
  rw [PhiHom_apply, PhiHom_apply]
  exact congrArg Multiplicative.ofAdd ((jacPic0_apply K F σ).symm.trans
    ((congrArg (fun z => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) h).trans (jacPic0_apply K F τ)))

/-- `ψ(a)` lies in `Pic⁰` and is the class of `λ_a`. -/
theorem jacPic0_lamB (a : X0 K F) (ha : IsClosed ({a} : Set (X0 K F))) :
    ((Multiplicative.toAdd (jacPic0 K F ⟨(lawChunk K F).lamB a ha, (lawChunk K F).lamB_mem_H a ha⟩) :
      Pic0K K F) : PicK K F) = psiJ K F a := by
  rw [jacPic0_apply, Phi_lamB (chunkAdd_lawChunk K F) (H_comm_lawChunk K F) a ha]

end Jac

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_ThetaSquare_Curve7 =====
section

/-!
# Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)

* `kapM cK : J ⟶ J`, `e ↦ c_K e⁻¹`; `mu1 P0 : J × X1 ⟶ J`, `(e, q) ↦ AJ(q) e`; `mu2 P0 c2`, `(e, q) ↦ AJ(q)² e c_2`;
* `Bad P0 c2 := mu1⁻¹ W ∩ mu2⁻¹ (J \ jX0 (X0))`, closed in `J × X1`;
* **`Ogood P0 cK c2 := Wᶜ ∩ kapM⁻¹ (jX0 (X0)) ∩ (pr_J Bad)ᶜ`**, open (`isOpen_Ogood`: `pr_J` is closed, `X1` proper);
* **`isGoodFor_of_mem`**: every `K`-point of `Ogood` is good;
* `not_mem_image_Bad`, `mem_Ogood_of`: the converse criterion (all `K`-points `(e, q)` off `Bad`).
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

section Curve7

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (cK c2 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)

/-- `κ : J ⟶ J`, `e ↦ c_K e⁻¹`. -/
noncomputable def kapM : Jac K F ⟶ Jac K F := toUnit (Jac K F) ≫ cK * (𝟙 (Jac K F))⁻¹

theorem comp_kapM (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : e ≫ kapM cK = cK * e⁻¹ := by
  rw [kapM, MonObj.comp_mul, ← Category.assoc, toUnit_unique (e ≫ toUnit _) (𝟙 _), Category.id_comp,
    GrpObj.comp_inv, Category.comp_id]

end Curve7

end RamanujanPetersson.ThetaSquare


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

lemma one_comp_mul (φ ψ : Jac K F ⟶ Jac K F) (hφ : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≫ φ = 1)
    (hψ : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≫ ψ = 1) :
    (1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) ≫ (φ * ψ) = 1 := by
  rw [comp_mul, hφ, hψ, _root_.one_mul]

end Theta

end RamanujanPetersson.ThetaCube


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

/-- On `S_g`: `z ∘ rho φ` restricts to `(z ∘ ι) ∘ φ`. -/
theorem comp_rho_S (z : BRing φ →ₐ[K] K) :
    (z.comp (rho φ)).comp (IsScalarTower.toAlgHom K _ (LawRing K F)) =
      ((z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ))).comp
        (IsScalarTower.toAlgHom K _ (LawRing K F))).comp φ := by
  ext s
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', rho_algebraMap, gB_apply]

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

theorem psiJ_kpt (y : LawRing K F →ₐ[K] K) :
    psiJ K F (kpt y) =
      clsK K F (Zdiv (ptSet (y.comp
        (IsScalarTower.toAlgHom K (SymRing K (Places.Rfin K F) (genusFK K F)) (LawRing K F))))) - thetaK K F := by
  rw [psiJ, psiS_kpt]
  rfl

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

theorem comp_mul_toUnit (a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (ψ : Jac K F ⟶ Jac K F)
    (c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    a ≫ (ψ * (toUnit _ ≫ c)) = (a ≫ ψ) * c := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (a ≫ toUnit _) (𝟙 _), Category.id_comp]

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

theorem dense_UJ (W : (Jac K F).left.Opens) (hW : Dense (W : Set (Jac K F).left)) :
    Dense ((UJ K F W : (Jac K F ⊗ Jac K F).left.Opens) : Set (Jac K F ⊗ Jac K F).left) := by
  have : Nonempty (Jac K F).left := ⟨(η[Jac K F]).left (IsLocalRing.closedPoint K)⟩
  have hne := hW.nonempty
  have d : ∀ (g : Jac K F ⊗ Jac K F ⟶ Jac K F) (t : Jac K F ⟶ Jac K F ⊗ Jac K F), t ≫ g = 𝟙 _ →
      Dense ((g.left ⁻¹ᵁ W : (Jac K F ⊗ Jac K F).left.Opens) : Set (Jac K F ⊗ Jac K F).left) :=
    fun g t h => (g.left ⁻¹ᵁ W).isOpen.dense (nonempty_preimage_over g t h W hne)
  have d1 := d (fst _ _) (lift (𝟙 _) (toUnit _ ≫ η)) (lift_fst _ _)
  have d2 := d (snd _ _) (lift (toUnit _ ≫ η) (𝟙 _)) (lift_snd _ _)
  have d3 := d μ (lift (𝟙 _) (toUnit _ ≫ η)) (MonObj.lift_comp_one_right _ _)
  rw [UJ, TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_inf]
  exact (d1.inter_of_isOpen_left d2 (TopologicalSpace.Opens.isOpen _)).inter_of_isOpen_left d3
    ((TopologicalSpace.Opens.isOpen _).inter (TopologicalSpace.Opens.isOpen _))

variable (ψ : Jac K F ⟶ Jac K F) (s : PicK K F ≃+ PicK K F) (W : (Jac K F).left.Opens)

variable (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))

/-- A `K`-point of `J` inside `jX0(D(φ u0))` comes from a `K`-point of `S_g[1/u0][1/φ u0]`. -/
theorem ptW (b : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hb : b.left (IsLocalRing.closedPoint K) ∈ (eJ φ).opensRange) :
    ∃ z : BRing φ →ₐ[K] K, b.left (IsLocalRing.closedPoint K) =
      jX0 K F (kpt (z.comp (IsScalarTower.toAlgHom K (LawRing K F) (BRing φ)))) := by
  obtain ⟨x, hx⟩ := Scheme.Hom.mem_opensRange.1 hb
  have hc : IsClosed ({b.left (IsLocalRing.closedPoint K)} : Set (Jac K F).left) :=
    (pointEquivClosedPoint (Jac K F).hom ⟨b.left, Over.w b⟩).2
  have hxc : IsClosed ({x} : Set (Spec (.of (BRing φ)))) := by
    have e : ({x} : Set (Spec (.of (BRing φ)))) = (⇑(eJ φ)) ⁻¹' {b.left (IsLocalRing.closedPoint K)} := by
      ext w
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hx, fun h => (eJ φ).isOpenEmbedding.injective (h.trans hx.symm)⟩
    rw [e]
    exact hc.preimage (eJ φ).continuous
  obtain ⟨z, rfl⟩ := exists_kpt (K := K) x hxc
  exact ⟨z, hx.symm.trans (eJ_kpt φ z)⟩

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

/-- Every nonempty open of `J` contains a `K`-point. -/
theorem exists_kpt_mem (U : (Jac K F).left.Opens) (hU : (U : Set (Jac K F).left).Nonempty) :
    ∃ b : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, b.left (IsLocalRing.closedPoint K) ∈ U := by
  have : JacobsonSpace (Jac K F).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (Jac K F).hom
  obtain ⟨x, hxU, hx⟩ := nonempty_inter_closedPoints hU U.isOpen.isLocallyClosed
  refine ⟨Over.homMk ((pointEquivClosedPoint (Jac K F).hom).symm ⟨x, hx⟩).1
    ((pointEquivClosedPoint (Jac K F).hom).symm ⟨x, hx⟩).2, ?_⟩
  show ((pointEquivClosedPoint (Jac K F).hom ((pointEquivClosedPoint (Jac K F).hom).symm ⟨x, hx⟩) :
    (Jac K F).left)) ∈ U
  rw [Equiv.apply_symm_apply]
  exact hxU

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

theorem eJ_over : eJ φ ≫ (Jac K F).hom = Spec.map (CommRingCat.ofHom (algebraMap K (BRing φ))) := by
  rw [eJ, Category.assoc, jX0_over, eB, specOverSpec_over, ← Spec.map_comp]
  congr 1

theorem range_sub_eJ (g : IsogDegB.DS K ⟶ Jac K F)
    (hg : g.left (IsLocalRing.closedPoint (DualNumber K)) ∈ (eJ φ).opensRange) :
    Set.range g.left ⊆ Set.range (eJ φ) := by
  rintro _ ⟨x, rfl⟩
  have hx := IsogDegB.DS_eq_closedPoint K x
  subst hx
  exact Scheme.Hom.mem_opensRange.1 hg

theorem exists_lift_DS (g : IsogDegB.DS K ⟶ Jac K F)
    (hg : g.left (IsLocalRing.closedPoint (DualNumber K)) ∈ (eJ φ).opensRange) :
    ∃ f : BRing φ →ₐ[K] DualNumber K, Spec.map (CommRingCat.ofHom f.toRingHom) ≫ eJ φ = g.left := by
  obtain ⟨l, hl⟩ : ∃ l, l ≫ eJ φ = g.left := ⟨_, IsOpenImmersion.lift_fac _ _ (range_sub_eJ φ g hg)⟩
  obtain ⟨f0, hf0⟩ : ∃ f0, Spec.map f0 = l := ⟨_, Spec.map_preimage l⟩
  have hK : CommRingCat.ofHom (algebraMap K (BRing φ)) ≫ f0 =
      CommRingCat.ofHom (algebraMap K (DualNumber K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf0, ← eJ_over, ← Category.assoc, hl]
    exact Over.w g
  have hK' : ∀ c : K, f0.hom (algebraMap K (BRing φ) c) = algebraMap K (DualNumber K) c := fun c => by
    have h := congrArg (fun h => CommRingCat.Hom.hom h c) hK
    simpa using h
  let f : BRing φ →ₐ[K] DualNumber K := { toRingHom := f0.hom, commutes' := hK' }
  have hf : CommRingCat.ofHom f.toRingHom = f0 := CommRingCat.ofHom_hom f0
  exact ⟨f, by rw [hf, hf0, hl]⟩

theorem rho_comp_eq (f : BRing φ →ₐ[K] DualNumber K)
    (H : ∀ s : SymRing K (Places.Rfin K F) (genusFK K F), (f (gB φ s)).snd = 0) :
    f.comp (rho φ) =
      (Algebra.ofId K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).comp (f.comp (rho φ))) := by
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (Submonoid.powers (lawPre K F).u0) (RingHom.ext fun s => ?_)
  show f (rho φ (algebraMap _ (LawRing K F) s)) =
    algebraMap K (DualNumber K) (f (rho φ (algebraMap _ (LawRing K F) s))).fst
  rw [rho_algebraMap]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
  · rw [H s, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

omit φ in
theorem kpt_w (y : LawRing K F →ₐ[K] K) :
    (Spec.map (CommRingCat.ofHom y.toRingHom) ≫ jX0 K F) ≫ (Jac K F).hom = (𝟙_ (Over (Spec (.of K)))).hom := by
  have hid : CommRingCat.ofHom (algebraMap K (LawRing K F)) ≫ CommRingCat.ofHom y.toRingHom =
      𝟙 (CommRingCat.of K) := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    simp
  rw [Category.assoc, jX0_over, specOverSpec_over, ← Spec.map_comp, hid, Spec.map_id]
  all_goals rfl

omit φ in
/-- The `K`-point `Spec K → Spec S_g[1/u0] = X0 → J` of a `K`-algebra map `y : S_g[1/u0] → K`. -/
noncomputable def kptJ (y : LawRing K F →ₐ[K] K) : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
  Over.homMk (Spec.map (CommRingCat.ofHom y.toRingHom) ≫ jX0 K F) (kpt_w y)

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

/-- If every `φ s` is a `p^n`-th power (`n ≠ 0`, `char K = p`), every `f : BRing φ → K[ε]` kills the `ε`-part. -/
theorem snd_gB_of_pow (φ : SymRing K (Places.Rfin K F) (genusFK K F) →ₐ[K] SymRing K (Places.Rfin K F) (genusFK K F))
    (p n : ℕ) [CharP K p] (hn : n ≠ 0) (hφ : ∀ s, ∃ y, φ s = y ^ p ^ n)
    (f : BRing φ →ₐ[K] DualNumber K) (s : SymRing K (Places.Rfin K F) (genusFK K F)) :
    (f (gB φ s)).snd = 0 := by
  obtain ⟨y, hy⟩ := hφ s
  rw [gB_apply, hy, map_pow, map_pow, map_pow]
  exact snd_pow_char p n hn _

end Gen

section Tan

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : Places.constField Fq F = ⊥)

set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Every `K[ε]`-point of `D(Φ_S u0)` kills the `ε`-part of `Φ_S(S_g)`. -/
theorem snd_PhiS
    (f : BRing (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) →ₐ[kbar Fq Ω] DualNumber (kbar Fq Ω))
    (s : SymRing (kbar Fq Ω) (Places.Rfin (kbar Fq Ω) (Fbar Fq F Ω)) (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) :
    (f (gB (PhiS Fq F Ω hk (genusFK (kbar Fq Ω) (Fbar Fq F Ω))) s)).snd = 0 := by
  obtain ⟨n, hp, hq⟩ := FiniteField.card Fq (ringChar Fq)
  have : Fact (ringChar Fq).Prime := ⟨hp⟩
  have : CharP (kbar Fq Ω) (ringChar Fq) :=
    charP_of_injective_algebraMap (algebraMap Fq (kbar Fq Ω)).injective _
  exact snd_gB_of_pow _ (ringChar Fq) n n.ne_zero (PhiS_pow_root Fq F Ω hk n hq) f s

end Tan

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_PolyG =====
section

/-!
# S4-JacFrob, part PolyG: `ℤ[π] → End(J)` on points, generically

For a map `ψ : J ⟶ J` whose action on the classes of the `K`-points is `πM` (through an additive map `t`
from `Pic⁰`): `cls_piter`, **`cls_polyEnd`** (`F(ψ)` acts as `aeval πM F`), `hom_ext_kpt` (maps `J ⟶ J` agreeing
on `K`-points are equal), `polyEnd_X`, **`polyEnd_mul_of_cls`** (`F G ↦ (FG)(ψ) = G(ψ) ≫ F(ψ)`: the ring map
`ℤ[π] → End(J)`), `polyEnd_eq_one_iff`, **`kerPtsEquiv`** (`Ker F(ψ)(K) ≃ ker (aeval πM F)`),
**`degree_polyEnd_eq_card_ker`** (`deg F(ψ) = #ker (aeval πM F)` when `dψ = 1`, `p ∤ F(0)`).
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

/-- Maps `J ⟶ J` that agree on all `K`-points are equal. -/
theorem hom_ext_kpt (φ ψ : Jac K F ⟶ Jac K F)
    (h : ∀ a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, a ≫ φ = a ≫ ψ) : φ = ψ := by
  have : LocallyOfFiniteType (Jac K F).hom := inferInstance
  refine eq_of_kpt_eq (U := ⊤) (by rw [TopologicalSpace.Opens.coe_top]; exact dense_univ) φ ψ fun u => ?_
  rw [← Category.assoc, ← Category.assoc]
  exact h _

end Gen

end RamanujanPetersson.JacFrob


end


