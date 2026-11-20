-- Prove2me | Definitions.Def_RPLib_F2_057
-- name    : RPLib_F2_057
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T20:55:49.570293+00:00
-- url     : https://prove2.me/theorems/48e1b34c-5cc8-4935-bd95-2186befdf6a7
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 057 of 70
-- statement:
--   File 057 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_Fam`: The Jacobian (unit S4-JacComplete), part `Fam`: **L21, families of divisors give maps to `J`**
--   * `S4.Def_RP_ThetaSquare_Def`: Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)
--   * `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
--   * `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
--   * `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
--   * `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_056
import Definitions.Def_RPLib_F2_083

/-!
# Ramanujan-Petersson curve library (flat edition), file 057 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_Fam`: The Jacobian (unit S4-JacComplete), part `Fam`: **L21, families of divisors give maps to `J`**
* `S4.Def_RP_ThetaSquare_Def`: Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)
* `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
* `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
* `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
* `S4.Def_RP_ThetaSquare_Curve7`: Unit S4-ThetaSquare, file Curve7: the open set of good points (T4c (D), openness)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_Fam =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Fam`: **L21, families of divisors give maps to `J`**

Milne III.6.1 for split families. Let `V` be smooth over `K` (`V`, `V ×_K V` integral), `U ⊆ V` a dense open and
`p q : U ⟶ X1^n` over `K`, i.e. `2n` sections of `X × U → U`; the family is `D = Σ Γ_{p_i} - Σ Γ_{q_i}` with fibres
`D_u = Σ [p_i(u)] - Σ [q_i(u)]` of degree `0`.
* `kPl x`: the place of `F` (closed point of `X`) of a `K`-point `x` of `X1`; `kPl_spec`: `x ≫ ajO P0 = ajK P0 (kPl x)`;
* `prj n i : X1^n ⟶ X1` (projections), `PhiN_val`: `Φ_n (x_1, …, x_n) = Σ ([kPl x_i] - [P0])`;
* `famDiv a b = Σ [a_i] - Σ [b_i]`, `famU P0 U p q : U ⟶ J` (`Φ_n ∘ p - Φ_n ∘ q`), `famU_val`;
* **`existsUnique_famJ`**: there is a unique `φ : V ⟶ J` over `K` with `φ(u) = [D_u]` (in `Pic⁰(X)`, via L20
  `jacPicEquiv`) for every `K`-point `u` of `U`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Fam

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The place of a `K`-point of `X1` (its center). -/
noncomputable def kPl (x : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) : Place K F := (exists_kPl x).choose

theorem kPl_spec (P0 : Place K F) (x : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    x ≫ ajO P0 = ajK K F P0 (kPl x) :=
  (exists_kPl x).choose_spec P0

theorem jacPicEquiv_ajO (P0 : Place K F) (x : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    jacPicEquiv K F (x ≫ ajO P0) = Multiplicative.ofAdd (ajCls K F P0 (kPl x)) := by
  rw [kPl_spec P0 x, ajK, MulEquiv.apply_symm_apply]

variable (K F) in
/-- The projections `X1^n ⟶ X1`. -/
noncomputable def prj : (n : ℕ) → Fin n → (PP K F n ⟶ X1O K F)
  | 0 => fun i => i.elim0
  | n + 1 => Fin.lastCases (snd (PP K F n) (X1O K F)) (fun j => fst (PP K F n) (X1O K F) ≫ prj n j)

/-- **Value of `Φ_n`** at a `K`-point: `Σ ([kPl x_i] - [P0])`. -/
theorem PhiN_val (P0 : Place K F) (n : ℕ) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) :
    jacPicEquiv K F (p ≫ PhiN P0 n) = Multiplicative.ofAdd (∑ i, ajCls K F P0 (kPl (p ≫ prj K F n i))) := by
  induction n with
  | zero =>
    show jacPicEquiv K F (p ≫ (1 : PP K F 0 ⟶ Jac K F)) = _
    rw [MonObj.comp_one, map_one, Finset.univ_eq_empty, Finset.sum_empty, ofAdd_zero]
  | succ n ih =>
    let p' : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n ⊗ X1O K F := p
    show jacPicEquiv K F (p' ≫ (fst (PP K F n) (X1O K F) ≫ PhiN P0 n * snd (PP K F n) (X1O K F) ≫ ajO P0)) =
      Multiplicative.ofAdd (∑ i : Fin (n + 1), ajCls K F P0 (kPl (p' ≫
        (Fin.lastCases (snd (PP K F n) (X1O K F)) (fun j => fst (PP K F n) (X1O K F) ≫ prj K F n j) i :
          PP K F n ⊗ X1O K F ⟶ X1O K F))))
    rw [MonObj.comp_mul, map_mul, ← Category.assoc p' (fst (PP K F n) (X1O K F)),
      ← Category.assoc p' (snd (PP K F n) (X1O K F)), ih, jacPicEquiv_ajO, Fin.sum_univ_castSucc, ofAdd_add]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last, Category.assoc]

variable {V : Over (Spec (.of K))} [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]

end Fam

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_ThetaSquare_Def =====
section

/-!
# Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)

* `irreducibleSpace_X1`, `isIntegral_X1`: the curve `X1 = Sym¹ X` is integral (its charts are domains and pairwise meet);
* `isIntegral_PP n`: `X1^n` is integral (`IntersectA.isIntegral_pullback`);
* `W P0 := Φ_{g-1}(X1^{g-1}) ⊆ J` (`isClosed_W`, `isIrreducible_W`), `zTheta P0` its generic point;
* `Theta P0 : AlgebraicCycle J ℤ`, the prime cycle `[W_{g-1}]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Def

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **`W_{g-1} = Φ_{g-1}(X1^{g-1}) ⊆ J`** (Milne III.5.1, for the base point `P0`). -/
def W : Set (Jac K F).left := Set.range (PhiN P0 (n0 K F)).left

end Def

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_PlusX =====
section

/-!
# Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map

`plusX c0 a i0 : Spec R2 ⟶ X1` (through the chart `{c0}`) and the constant `cE a i0 P0` (class `[E] + [P0] - [Θ]`)
satisfy **`plus_eq`**: `(const cE) * (plusX ≫ AJ_{P0}) = jMap lawMapPlus` (`Spec R2 → X0 → J`).
Also `exists_eq_kptO` (every `K`-point of `Spec R` is `kptO x`) and `finiteType_R1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

section KptO

variable {K : Type u} [Field K]

end KptO

section PlusX

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

variable [IsAlgClosed K]

variable (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F)) (P0 : Place K F)

/-- **Value of `plusX ≫ AJ`** at a `K`-point: `[P] - [P0]`. -/
theorem kptO_plusX_ajO (x : R2 c0 a i0 →ₐ[K] K) :
    kptO x ≫ plusX c0 a i0 ≫ ajO P0 = ajK K F P0 (Sum.inl (ptP (ptR2 c0 a i0 x))) := by
  apply Over.OverMorphism.ext
  refine ext_of_apply_closedPoint_eq (Jac K F).hom (Over.w _) (Over.w _) ?_
  have e : (kptO x ≫ plusX c0 a i0 ≫ ajO P0).left (IsLocalRing.closedPoint K) =
      ajX1 P0 (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (op (idx0 c0))
        (Spec.map (CommRingCat.ofHom (symToR2 c0 a i0 : SymRing K (Bc F c0) 1 →+* R2 c0 a i0))
          (Spec.map (CommRingCat.ofHom (x : R2 c0 a i0 →+* K)) (IsLocalRing.closedPoint K)))) := rfl
  rw [e, SpecMap_closedPoint, SpecMap_kpt]
  refine (ajX1_apply (P0 := P0) (op (idx0 c0)) (x.comp (symToR2 c0 a i0))).trans ?_
  rw [symToR2_diag1]
  rw [plA_R1 c0 (x.comp (awayι (K := K) (plusH c0 a i0))), ajPt]

end PlusX

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

/-- The translated Abel-Jacobi map `f_e : X1 → J`, `p ↦ AJ(p) · e`. -/
noncomputable def fe (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : X1O K F ⟶ Jac K F :=
  ajO P0 ≫ transl (Jac K F) e

/-- The underlying map of schemes of `f_e`. -/
noncomputable def feX (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : X1 K F ⟶ (Jac K F).left :=
  (fe P0 e).left

theorem comp_fe (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    q ≫ fe P0 e = (q ≫ ajO P0) * e := by
  rw [fe, ← Category.assoc, comp_transl, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem feX_kpt (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    feX P0 e (q.left (IsLocalRing.closedPoint K)) = (q ≫ fe P0 e).left (IsLocalRing.closedPoint K) :=
  rfl

variable (hg : 0 < genusFK K F)

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

/-- The plus-curve chart `Spec R2 → X1` as a map of schemes. -/
noncomputable def ι2 : Spec (.of (R2 c0 a i0)) ⟶ X1 K F := (plusX c0 a i0).left

instance isOpenImmersion_ι2 : IsOpenImmersion (ι2 (F := F) c0 a i0) := by
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (awayι (K := K) (plusH c0 a i0) : R1 F c0 →+* R2 c0 a i0))) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of (R1 F c0)) (plusH c0 a i0)
  have h2 := isOpenImmersion_bc_R1 (K := K) (F := F) c0
  have h3 : IsIso (Spec.map (CommRingCat.ofHom
      ((sym1Equiv (k := K) (B := Bc F c0)).toAlgHom : SymRing K (Bc F c0) 1 →+* Bc F c0))) :=
    inferInstanceAs (IsIso (Spec.map (RingEquiv.toCommRingCatIso
      (sym1Equiv (k := K) (B := Bc F c0)).toRingEquiv).hom))
  have e4 : Spec.map (CommRingCat.ofHom (symToR2 c0 a i0 : SymRing K (Bc F c0) 1 →+* R2 c0 a i0)) =
      Spec.map (CommRingCat.ofHom (awayι (K := K) (plusH c0 a i0) : R1 F c0 →+* R2 c0 a i0)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Bc F c0) (R1 F c0))) ≫
          Spec.map (CommRingCat.ofHom
            ((sym1Equiv (k := K) (B := Bc F c0)).toAlgHom : SymRing K (Bc F c0) 1 →+* Bc F c0)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have h4 : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (symToR2 c0 a i0 : SymRing K (Bc F c0) 1 →+* R2 c0 a i0))) := by
    rw [e4]
    infer_instance
  haveI : IsOpenImmersion (ιO K F (op (idx0 c0))).left := isOpenImmersion_ιX1 (K := K) (F := F) (op (idx0 c0))
  have e : ι2 (F := F) c0 a i0 =
      Spec.map (CommRingCat.ofHom (symToR2 c0 a i0 : SymRing K (Bc F c0) 1 →+* R2 c0 a i0)) ≫
        (ιO K F (op (idx0 c0))).left := rfl
  rw [e]
  infer_instance

variable (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
  (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)

end Curve1

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve3 =====
section

/-!
# Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)

* `div_pow_of_div`, `le_ell_single`: if `div f = [Q'] - [Q]` with `Q ≠ Q'` then `ℓ(n[Q]) ≥ n + 1` for all `n`;
* **`eq_of_clsK_single`** (Abel for one point, `g ≥ 1`): `[Q] ~ [Q'] ⇒ Q = Q'`; `ajK_injective`;
* `kPl_kptO_plusX`: the place of the plus-curve point at `x` is `ptR2 x`; `kPl_chart`: the place of a chart point;
* **`exists_chart0`**: every `K`-point `q` of `X1` lies in a chart `{c0}`, at a point centered at `kPl q`;
  `xcR_ne_of_isCenter`: then `x - c0` does not vanish at that place;
* **`eq_iota2`**: if `ptR2 x` is the place of `q` (chart `{c0}` from `exists_chart0`), then `q = ι2 (kpt x)`.
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

section Abel

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end Abel

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The place of a `K`-point of `X1` given in a chart `A` is the center `plA`. -/
theorem kPl_chart (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (A : (ChartIdx K)ᵒᵖ)
    (ψ : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1 →ₐ[K] K)
    (hq : q.left (IsLocalRing.closedPoint K) = colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A
      (kpt (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) ψ)) :
    kPl q = plA A.unop (ψ.comp diag1) := by
  refine ajK_injective hg (plA A.unop (ψ.comp diag1)) ?_
  rw [← kPl_spec]
  apply Over.OverMorphism.ext
  refine ext_of_apply_closedPoint_eq (Jac K F).hom (Over.w _) (Over.w _) ?_
  have e : (q ≫ ajO (plA A.unop (ψ.comp diag1))).left (IsLocalRing.closedPoint K) =
      ajX1 (plA A.unop (ψ.comp diag1)) (q.left (IsLocalRing.closedPoint K)) := rfl
  rw [e, hq, ajX1_apply]
  rfl

/-- **Every `K`-point of `X1` lies in a chart `{c0}`**, at a point centered at `kPl q`. -/
theorem exists_chart0 (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    ∃ c0 : K, ∃ ψ0 : SymRing K (Bc F c0) 1 →ₐ[K] K, IsCenter (kPl q) (ψ0.comp diag1) ∧
      q.left (IsLocalRing.closedPoint K) = colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (op (idx0 c0))
        (kpt (A := SymRing K (Bc F c0) 1) ψ0) := by
  have hx : IsClosed ({q.left (IsLocalRing.closedPoint K)} : Set (X1 K F)) :=
    JacChunk.isClosed_singleton_apply (𝟙 (Spec (.of K))) (toSpecK K (algebraMap K[X] F X) 1) q.left (Over.w q) _
      (JacChunk.isClosed_specPt _)
  obtain ⟨A, p, hp⟩ := cht_cov (K := K) (F := F) _ hx
  have hpc : IsClosed ({p} : Set (cht K F A)) := by
    haveI := isOpenImmersion_ιX1 (K := K) (F := F) A
    have hinj := (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A).isOpenEmbedding.injective
    have h := hx.preimage (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A).isOpenEmbedding.continuous
    have e2 : (⇑(colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A)) ⁻¹'
        {q.left (IsLocalRing.closedPoint K)} = {p} := by
      ext w
      simp only [Set.mem_preimage]
      rw [← hp]
      exact hinj.eq_iff
    exact (congrArg IsClosed e2).mp h
  obtain ⟨ψ, rfl⟩ := exists_kpt (K := K) (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) p hpc
  have hc0 : A.unop.2.choose ∈ A.unop.1 := A.unop.2.choose_spec
  let f : A ⟶ op (idx0 A.unop.2.choose) :=
    (homOfLE (Subtype.coe_le_coe.1 (Finset.singleton_subset_iff.2 hc0) : idx0 A.unop.2.choose ≤ A.unop)).op
  refine ⟨A.unop.2.choose, ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop)), ?_, ?_⟩
  · have key2 : (ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop))).comp diag1 =
        (ψ.comp diag1).comp (Subalgebra.inclusion (chartRing_mono _ (leOfHom f.unop))) := by
      rw [AlgHom.comp_assoc, chartMap, symMap_diag1, AlgHom.comp_assoc]
    rw [key2, kPl_chart hg q A ψ hp.symm]
    exact isCenter_restrict (leOfHom f.unop) _ (isCenter_plA A.unop (ψ.comp diag1))
  · have key : (symDiagram K (algebraMap K[X] F X) 1).map f
          (kpt (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) ψ) =
        kpt (A := SymRing K (Bc F A.unop.2.choose) 1)
          (ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop))) := by
      rw [symDiagram_map]
      exact SpecMap_kpt (A := SymRing K (Bc F A.unop.2.choose) 1)
        (B := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1)
        (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop)) ψ
    rw [← hp, ← key, ← colimit.w (symDiagram K (algebraMap K[X] F X) 1) f]
    rfl

end Geom

end RamanujanPetersson.ThetaSquare


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

/-- `μ1 : J × X1 ⟶ J`, `(e, q) ↦ AJ(q) e`. -/
noncomputable def mu1 : Jac K F ⊗ X1O K F ⟶ Jac K F :=
  (snd (Jac K F) (X1O K F) ≫ ajO P0) * fst (Jac K F) (X1O K F)

/-- `μ2 : J × X1 ⟶ J`, `(e, q) ↦ AJ(q)² e c_2`. -/
noncomputable def mu2 : Jac K F ⊗ X1O K F ⟶ Jac K F :=
  (snd (Jac K F) (X1O K F) ≫ ajO P0) * (snd (Jac K F) (X1O K F) ≫ ajO P0) * fst (Jac K F) (X1O K F) *
    (toUnit _ ≫ c2)

theorem comp_mu1 (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    lift e q ≫ mu1 P0 = q ≫ fe P0 e := by
  rw [mu1, MonObj.comp_mul, lift_snd_assoc, lift_fst, comp_fe]

end Curve7

end RamanujanPetersson.ThetaSquare


end


