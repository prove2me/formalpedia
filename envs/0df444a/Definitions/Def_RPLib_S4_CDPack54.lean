-- Prove2me | Definitions.Def_RPLib_S4_CDPack54
-- name    : RPLib_S4_CDPack54
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:35:23.84673+00:00
-- url     : https://prove2.me/theorems/51142281-1460-4e9d-b794-769972057263
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 54 of 71
-- statement:
--   Part 54 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
--   * `Def_RP_JacComplete_Fam`: The Jacobian (unit S4-JacComplete), part `Fam`: **L21, families of divisors give maps to `J`**
--   * `Def_RP_JacComplete`: The Jacobian (unit S4-JacComplete), umbrella
--   * `Def_RP_ThetaSquare_Def`: Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)
--   * `Def_RP_ThetaSquare_Riem`: Unit S4-ThetaSquare, file Riem: the `K`-points of `W_{g-1}` (Riemann's theorem, point form; Milne III.5.2)
--   * `Def_RP_ThetaSquare_Ne`: Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`
--   * `Def_RP_ThetaSquare_Stab`: Unit S4-ThetaSquare, file Stab: the stabiliser of `W_{g-1}` is trivial (divisor form, Riemann-Roch only)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack43b
import Definitions.Def_RPLib_S4_CDPack48
import Definitions.Def_RPLib_S4_CDPack36
import Definitions.Def_RPLib_S4_CDPack36b
import Definitions.Def_RPLib_S4_CDPack36c
import Definitions.Def_RPLib_S4_CDPack25
import Definitions.Def_RPLib_S4_CDPack31

/-!
# Curve-duality library package, part 54 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
* `Def_RP_JacComplete_Fam`: The Jacobian (unit S4-JacComplete), part `Fam`: **L21, families of divisors give maps to `J`**
* `Def_RP_JacComplete`: The Jacobian (unit S4-JacComplete), umbrella
* `Def_RP_ThetaSquare_Def`: Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)
* `Def_RP_ThetaSquare_Riem`: Unit S4-ThetaSquare, file Riem: the `K`-points of `W_{g-1}` (Riemann's theorem, point form; Milne III.5.2)
* `Def_RP_ThetaSquare_Ne`: Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`
* `Def_RP_ThetaSquare_Stab`: Unit S4-ThetaSquare, file Stab: the stabiliser of `W_{g-1}` is trivial (divisor form, Riemann-Roch only)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_Ext =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)

Weil's extension theorem (S4-JacDivisors, Milne I.3.2) applied to the proper group `J` (L19, `isProper_Jac`):
* `domain_eq_top_Jac`: a rational map over `K` from a smooth `V` (with `V`, `V ×_K V` integral) to `J` is defined
  everywhere;
* `extJ f hf : V ⟶ J`, `ι_extJ` (it restricts to `f` on the domain of `f`), `eq_extJ` (unique);
* `UO V U`, `ιU V U` (a dense open `U ⊆ V` over `K`) and `eq_of_kpt_eq`: maps `V ⟶ J` from a reduced `V` locally of
  finite type are determined by their values at the `K`-points of a dense open.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacLaw

universe u

section Ext

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
instance isSeparated_Jac_left : (Jac K F).left.IsSeparated :=
  ⟨by rw [← terminal.comp_from (Jac K F).hom]; infer_instance⟩

/-- **Weil extension for `J`**: a rational map over `K` from a smooth `V` to `J` is defined everywhere. -/
theorem domain_eq_top_Jac {V : Over (Spec (.of K))} [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom) :
    f.toRationalMap.domain = ⊤ :=
  JacDivisors.domain_eq_top_of_smooth_of_isProper (G := Jac K F) f hf

variable {V : Over (Spec (.of K))} [IsReduced V.left]

/-- The morphism `V ⟶ J` of a partial map whose rational map is defined everywhere. -/
noncomputable def extL (f : V.left.PartialMap (Jac K F).left) (h : f.toRationalMap.domain = ⊤) :
    V.left ⟶ (Jac K F).left :=
  V.left.topIso.inv ≫ V.left.homOfLE (show (⊤ : V.left.Opens) ≤ f.toRationalMap.toPartialMap.domain from h.ge) ≫
    f.toRationalMap.toPartialMap.hom

theorem ι_extL (f : V.left.PartialMap (Jac K F).left) (h : f.toRationalMap.domain = ⊤) :
    f.domain.ι ≫ extL f h = f.hom := by
  have e : V.left.homOfLE (show f.domain ≤ f.toRationalMap.toPartialMap.domain from f.le_domain_toRationalMap) ≫
      f.toRationalMap.toPartialMap.hom = f.hom :=
    f.toPartialMap_toRationalMap_restrict
  rw [← e, extL, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (f.toRationalMap.toPartialMap.domain.ι), Category.assoc, Scheme.homOfLE_ι,
    Category.assoc, Scheme.toIso_inv_ι, Category.comp_id, Scheme.homOfLE_ι]

theorem extL_over (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom)
    (h : f.toRationalMap.domain = ⊤) : extL f h ≫ (Jac K F).hom = V.hom := by
  rw [extL, Category.assoc, Category.assoc, JacDivisors.toPartialMap_comp V.hom (Jac K F).hom f hf,
    ← Category.assoc (V.left.homOfLE _), Scheme.homOfLE_ι, ← Category.assoc, Scheme.toIso_inv_ι,
    Category.id_comp]

/-- Two maps `V ⟶ J` over `K` that agree on a dense open are equal. -/
theorem eq_of_comp_eq {U : V.left.Opens} (hU : Dense (U : Set V.left)) (φ ψ : V ⟶ Jac K F)
    (h : U.ι ≫ φ.left = U.ι ≫ ψ.left) : φ = ψ := by
  haveI := AlgebraicGeometry.Opens.isDominant_ι hU
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (Jac K F).hom (by rw [Over.w φ, Over.w ψ])
    U.ι h)

/-- **The extension `V ⟶ J`** of a partial map over `K` from a smooth `V`. -/
noncomputable def extJ [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom) : V ⟶ Jac K F :=
  Over.homMk (extL f (domain_eq_top_Jac f hf)) (extL_over f hf (domain_eq_top_Jac f hf))

theorem ι_extJ [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom) :
    f.domain.ι ≫ (extJ f hf).left = f.hom :=
  ι_extL f (domain_eq_top_Jac f hf)

/-- `extJ f hf` is the only map `V ⟶ J` restricting to `f`. -/
theorem eq_extJ [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom) (φ : V ⟶ Jac K F)
    (h : f.domain.ι ≫ φ.left = f.hom) : φ = extJ f hf :=
  eq_of_comp_eq f.dense_domain φ (extJ f hf) (h.trans (ι_extJ f hf).symm)

/-- **Rational maps `V ⇢ J` over `K` are morphisms** (Weil extension + L19). -/
theorem existsUnique_extJ [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap (Jac K F).left) (hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom) :
    ∃! φ : V ⟶ Jac K F, f.domain.ι ≫ φ.left = f.hom :=
  ⟨extJ f hf, ι_extJ f hf, fun φ h => eq_extJ f hf φ h⟩

variable (V) in
/-- An open `U ⊆ V` as an object over `Spec K`. -/
noncomputable abbrev UO (U : V.left.Opens) : Over (Spec (.of K)) := Over.mk (U.ι ≫ V.hom)

variable (V) in
/-- The inclusion `U ⟶ V` over `Spec K`. -/
noncomputable abbrev ιU (U : V.left.Opens) : UO V U ⟶ V := Over.homMk U.ι rfl

/-- **Maps `V ⟶ J` are determined by their values at the `K`-points of a dense open.** -/
theorem eq_of_kpt_eq [LocallyOfFiniteType V.hom] {U : V.left.Opens} (hU : Dense (U : Set V.left))
    (φ ψ : V ⟶ Jac K F)
    (h : ∀ u : 𝟙_ (Over (Spec (.of K))) ⟶ UO V U, u ≫ ιU V U ≫ φ = u ≫ ιU V U ≫ ψ) : φ = ψ := by
  have e : ιU V U ≫ φ = ιU V U ≫ ψ := by
    haveI : LocallyOfFiniteType (UO V U).hom := show LocallyOfFiniteType (U.ι ≫ V.hom) from inferInstance
    haveI : IsReduced (UO V U).left := show IsReduced U.toScheme from inferInstance
    exact (lawChunk K F).hom_ext_kpt inferInstance inferInstance _ _ fun u => congrArg _ (h u)
  exact eq_of_comp_eq hU φ ψ (congrArg CommaMorphism.left e)

end Ext

end RamanujanPetersson.JacComplete

end

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

/-- **Every `K`-point of `X1` is the center of a place**, with Abel-Jacobi value `[Q] - [P0]` for every `P0`. -/
theorem exists_kPl (x : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    ∃ Q : Place K F, ∀ P0 : Place K F, x ≫ ajO P0 = ajK K F P0 Q := by
  have hx : IsClosed ({x.left (IsLocalRing.closedPoint K)} : Set (X1 K F)) :=
    JacChunk.isClosed_singleton_apply (𝟙 (Spec (.of K))) (toSpecK K (algebraMap K[X] F X) 1) x.left (Over.w x) _
      (JacChunk.isClosed_specPt _)
  obtain ⟨A, p, hp⟩ := cht_cov (K := K) (F := F) _ hx
  have hpc : IsClosed ({p} : Set (cht K F A)) := by
    haveI := isOpenImmersion_ιX1 (K := K) (F := F) A
    have hinj := (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A).isOpenEmbedding.injective
    have h := hx.preimage (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A).isOpenEmbedding.continuous
    have e2 : (⇑(colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A)) ⁻¹'
        {x.left (IsLocalRing.closedPoint K)} = {p} := by
      ext w
      simp only [Set.mem_preimage]
      rw [← hp]
      exact hinj.eq_iff
    exact (congrArg IsClosed e2).mp h
  obtain ⟨ψ, rfl⟩ := exists_kpt (K := K) (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) p hpc
  refine ⟨plA A.unop (ψ.comp diag1), fun P0 => ?_⟩
  apply Over.OverMorphism.ext
  refine ext_of_apply_closedPoint_eq (Jac K F).hom (Over.w _) (Over.w _) ?_
  have e : (x ≫ ajO P0).left (IsLocalRing.closedPoint K) = ajX1 P0 (x.left (IsLocalRing.closedPoint K)) := rfl
  rw [e, ← hp, ajX1_apply]
  rfl

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

/-- The degree-`0` divisor `Σ [a_i] - Σ [b_i]`. -/
noncomputable def famDiv {n : ℕ} (a b : Fin n → Place K F) : Places.Divisor K F :=
  ∑ i, Finsupp.single (a i) 1 - ∑ i, Finsupp.single (b i) 1

theorem coe_sum_ajCls_sub (P0 : Place K F) {n : ℕ} (a b : Fin n → Place K F) :
    ((∑ i, ajCls K F P0 (a i) - ∑ i, ajCls K F P0 (b i) : Pic0K K F) : PicK K F) = clsK K F (famDiv a b) := by
  rw [AddSubgroup.coe_sub, AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum]
  show ∑ i, (clsK K F (Finsupp.single (a i) 1) - clsK K F (Finsupp.single P0 1)) -
    ∑ i, (clsK K F (Finsupp.single (b i) 1) - clsK K F (Finsupp.single P0 1)) = _
  have hs : ∀ c : Fin n → Place K F,
      clsK K F (∑ i, Finsupp.single (c i) 1) = ∑ i, clsK K F (Finsupp.single (c i) 1) :=
    fun c => map_sum (QuotientAddGroup.mk' (PrincK K F)) _ _
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sub_sub_sub_cancel_right, famDiv, clsK_sub, hs, hs]

variable {V : Over (Spec (.of K))} [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]

/-- The classifying map on `U` of the split family `(p, q)`: `Φ_n ∘ p - Φ_n ∘ q`. -/
noncomputable def famU (P0 : Place K F) (U : V.left.Opens) {n : ℕ} (p q : UO V U ⟶ PP K F n) :
    UO V U ⟶ Jac K F :=
  p ≫ PhiN P0 n * (q ≫ PhiN P0 n)⁻¹

theorem famU_val (P0 : Place K F) (U : V.left.Opens) {n : ℕ} (p q : UO V U ⟶ PP K F n)
    (u : 𝟙_ (Over (Spec (.of K))) ⟶ UO V U) :
    ((Multiplicative.toAdd (jacPicEquiv K F (u ≫ famU P0 U p q)) : Pic0K K F) : PicK K F) =
      clsK K F (famDiv (fun i => kPl (u ≫ p ≫ prj K F n i)) (fun i => kPl (u ≫ q ≫ prj K F n i))) := by
  rw [famU, MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_inv, ← Category.assoc u p, ← Category.assoc u q,
    PhiN_val, PhiN_val, toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, ← sub_eq_add_neg, coe_sum_ajCls_sub]
  simp only [Category.assoc]

/-- **L21 (Milne III.6.1, split families).** A family of degree-`0` divisors `D_u = Σ [p_i(u)] - Σ [q_i(u)]`
parametrized by a dense open `U` of a smooth `V` has a unique classifying morphism `φ : V ⟶ J` over `K`:
`φ(u) = [D_u] ∈ Pic⁰(X)` for every `K`-point `u` of `U`. -/
theorem existsUnique_famJ {U : V.left.Opens} (hU : Dense (U : Set V.left)) {n : ℕ} (p q : UO V U ⟶ PP K F n) :
    ∃! φ : V ⟶ Jac K F, ∀ u : 𝟙_ (Over (Spec (.of K))) ⟶ UO V U,
      ((Multiplicative.toAdd (jacPicEquiv K F (u ≫ ιU V U ≫ φ)) : Pic0K K F) : PicK K F) =
        clsK K F (famDiv (fun i => kPl (u ≫ p ≫ prj K F n i)) (fun i => kPl (u ≫ q ≫ prj K F n i))) := by
  obtain ⟨Q⟩ := PlacesK.nonempty_infPlace K F
  let P0 : Place K F := Sum.inr Q
  let f : V.left.PartialMap (Jac K F).left := ⟨U, hU, (famU P0 U p q).left⟩
  have hf : f.hom ≫ (Jac K F).hom = f.domain.ι ≫ V.hom := Over.w (famU P0 U p q)
  have e : ιU V U ≫ extJ f hf = famU P0 U p q := Over.OverMorphism.ext (ι_extJ f hf)
  refine ⟨extJ f hf, fun u => ?_, fun φ hφ => ?_⟩
  · rw [e]
    exact famU_val P0 U p q u
  · apply eq_of_kpt_eq hU
    intro u
    apply (jacPicEquiv K F).injective
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [hφ u, e, famU_val]

end Fam

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacComplete =====
section

/-!
# The Jacobian (unit S4-JacComplete), umbrella

Weil's Jacobian `Jac K F` of a function field `F/K` (`K` algebraically closed), from Weil's birational group law on
`Sym^g X` (S4-JacLaw) and the group chunk theorem (S4-JacChunkA/B). Lemmas L19-L22 of `S4_COREB_ROUTE.md`:
* `Def`: `Jac K F : Over (Spec K)`, a smooth separated group scheme, with the open chart `jX0 : X0 ⟶ J`;
* L22 `isCommMonObj_Jac` (file `CommJ`): `J` is commutative;
* L20 `jacPicEquiv K F : J(K) ≃* Multiplicative Pic⁰(X_K)` (file `PicJ`);
* L19 `isProper_Jac K F : IsProper (Jac K F).hom` (file `Proper`, via the Abel-Jacobi map `X1^g ⟶ J`);
* L21 `existsUnique_extJ` (file `Ext`: rational maps from smooth `V` to `J` are morphisms), `eq_of_kpt_eq` and
  `existsUnique_famJ` (file `Fam`: a split family of degree-`0` divisors on `X × V` has a unique classifying
  morphism `V ⟶ J`, `φ(u) = [D_u]`).
-/

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

instance isIntegral_cht (A : (ChartIdx K)ᵒᵖ) : IsIntegral (cht K F A) := by
  show IsIntegral (Spec (CommRingCat.of (SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1)))
  infer_instance

variable (K F) in
/-- **The curve `X1` is irreducible**: the charts are irreducible, open, cover `X1` and any two meet in a third. -/
theorem irreducibleSpace_X1 : IrreducibleSpace (X1 K F) := by
  let D := symDiagram K (algebraMap K[X] F X) 1
  let A0 : (ChartIdx K)ᵒᵖ := op ⟨{0}, Finset.singleton_nonempty 0⟩
  haveI : Nonempty (X1 K F) := by
    obtain ⟨z⟩ : Nonempty (D.obj A0) := (inferInstance : IsIntegral (cht K F A0)).nonempty
    exact ⟨colimit.ι D A0 z⟩
  refine IntersectA.irreducibleSpace_of_cover (fun A : (ChartIdx K)ᵒᵖ => Set.range (colimit.ι D A))
    (fun A => (colimit.ι D A).isOpenEmbedding.isOpen_range) (fun A => ?_) (fun y => ?_) (fun A A' => ?_)
  · haveI hA : IrreducibleSpace (D.obj A) := (inferInstance : IrreducibleSpace (cht K F A))
    have h := ((IrreducibleSpace.isIrreducible_univ (D.obj A)).image _
      (colimit.ι D A).continuous.continuousOn).isPreirreducible
    rw [Set.image_univ] at h
    exact h
  · obtain ⟨A, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective D y
    exact ⟨A, z, rfl⟩
  · let B : ChartIdx K := ⟨A.unop.1 ∪ A'.unop.1, A.unop.2.mono Finset.subset_union_left⟩
    obtain ⟨z⟩ : Nonempty (D.obj (op B)) := (inferInstance : IsIntegral (cht K F (op B))).nonempty
    have h1 := colimit.w D (homOfLE (show A.unop ≤ B from Finset.subset_union_left)).op
    have h2 := colimit.w D (homOfLE (show A'.unop ≤ B from Finset.subset_union_right)).op
    refine ⟨colimit.ι D (op B) z, ⟨D.map (homOfLE (show A.unop ≤ B from Finset.subset_union_left)).op z, ?_⟩,
      ⟨D.map (homOfLE (show A'.unop ≤ B from Finset.subset_union_right)).op z, ?_⟩⟩
    · rw [← h1]; rfl
    · rw [← h2]; rfl

instance isIntegral_X1 : IsIntegral (X1 K F) := by
  haveI := irreducibleSpace_X1 K F
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

/-- **`X1^n` is integral.** -/
instance isIntegral_PP (n : ℕ) : IsIntegral (PP K F n).left := by
  induction n with
  | zero =>
    show IsIntegral (Spec (.of K))
    infer_instance
  | succ n ih =>
    haveI := ih
    show IsIntegral (pullback (PP K F n).hom (toSpecK K (algebraMap K[X] F X) 1))
    exact IntersectA.isIntegral_pullback (PP K F n).hom (toSpecK K (algebraMap K[X] F X) 1)

instance irreducibleSpace_PP (n : ℕ) : IrreducibleSpace (PP K F n).left := inferInstance

variable (K F) in
/-- `g - 1`. -/
noncomputable abbrev n0 : ℕ := genusFK K F - 1

variable (P0 : Place K F)

/-- **`W_{g-1} = Φ_{g-1}(X1^{g-1}) ⊆ J`** (Milne III.5.1, for the base point `P0`). -/
def W : Set (Jac K F).left := Set.range (PhiN P0 (n0 K F)).left

theorem isClosed_W : IsClosed (W P0) := (PhiN P0 (n0 K F)).left.isClosedMap.isClosed_range

theorem isIrreducible_W : IsIrreducible (W P0) := by
  rw [W, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (PP K F (n0 K F)).left).image _
    (PhiN P0 (n0 K F)).left.continuous.continuousOn

/-- The generic point of `W_{g-1}`. -/
noncomputable def zTheta : (Jac K F).left := (isIrreducible_W P0).genericPoint

theorem isGenericPoint_zTheta : IsGenericPoint (zTheta P0) (W P0) :=
  (isIrreducible_W P0).isGenericPoint_genericPoint (isClosed_W P0)

theorem closure_zTheta : closure {zTheta P0} = W P0 := isGenericPoint_zTheta P0

/-- **The theta divisor** `Θ = [W_{g-1}]`, as a prime cycle on `J`. -/
noncomputable def Theta : AlgebraicCycle (Jac K F).left ℤ := Function.locallyFinsuppWithin.single (zTheta P0) 1

theorem Theta_apply (z : (Jac K F).left) : Theta P0 z = if z = zTheta P0 then 1 else 0 :=
  Function.locallyFinsuppWithin.single_apply

theorem Theta_nonneg : 0 ≤ Theta P0 := Function.locallyFinsuppWithin.single_nonneg.mpr zero_le_one

end Def

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_ThetaSquare_Riem =====
section

/-!
# Unit S4-ThetaSquare, file Riem: the `K`-points of `W_{g-1}` (Riemann's theorem, point form; Milne III.5.2)

**`mem_W_iff`**: a `K`-point `x` of `J` lies on `W_{g-1}` iff its class is `Σ_{i<g-1} ([t_i] - [P0])` for some places
`t_i`, i.e. iff `x + (g-1)[P0]` is the class of an effective divisor of degree `g - 1`.
(→: the fibre of the proper map `Φ_{g-1}` over the closed point `x` is a nonempty closed subset of the Jacobson
scheme `X1^{g-1}`, so it has a closed point, i.e. a `K`-point `p`, and `PhiN_val` computes `Φ(p)`; ←: `exists_pt`.)
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

section Riem

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- A point of `W = Φ_n(X1^n)` that is closed is the image of a `K`-point of `X1^n`. -/
theorem exists_kpt_of_mem_range (n : ℕ) (x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hx : x.left (IsLocalRing.closedPoint K) ∈ Set.range (PhiN P0 n).left) :
    ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n, p ≫ PhiN P0 n = x := by
  obtain ⟨y, hy⟩ := hx
  have hcl : IsClosed ({x.left (IsLocalRing.closedPoint K)} : Set (Jac K F).left) :=
    (pointEquivClosedPoint (Jac K F).hom ⟨x.left, Over.w x⟩).2
  haveI : JacobsonSpace (PP K F n).left := LocallyOfFiniteType.jacobsonSpace (PP K F n).hom
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (Z := (PhiN P0 n).left ⁻¹' {x.left (IsLocalRing.closedPoint K)}) ⟨y, hy⟩
    (hcl.preimage (PhiN P0 n).left.continuous).isLocallyClosed
  let p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n :=
    Over.homMk (pointOfClosedPoint (PP K F n).hom z hzc) (pointOfClosedPoint_comp _ _ _)
  refine ⟨p, ?_⟩
  apply Over.OverMorphism.ext
  refine ext_of_apply_closedPoint_eq (Jac K F).hom (Over.w _) (Over.w _) ?_
  have h2 : (p ≫ PhiN P0 n).left (IsLocalRing.closedPoint K) = (PhiN P0 n).left z := by
    show (PhiN P0 n).left (pointOfClosedPoint (PP K F n).hom z hzc (IsLocalRing.closedPoint K)) = _
    exact congrArg (PhiN P0 n).left (pointOfClosedPoint_apply (PP K F n).hom z hzc _)
  rw [h2]
  exact hz

/-- **Riemann's theorem, point form** (Milne III.5.2): `x ∈ W_{g-1}` iff `x = Σ_{i<g-1} ([t_i] - [P0])`. -/
theorem mem_W_iff (x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    x.left (IsLocalRing.closedPoint K) ∈ W P0 ↔
      ∃ t : Fin (n0 K F) → Place K F, jacPicEquiv K F x = Multiplicative.ofAdd (∑ i, ajCls K F P0 (t i)) := by
  constructor
  · intro hx
    obtain ⟨p, e⟩ := exists_kpt_of_mem_range P0 (n0 K F) x hx
    exact ⟨fun i => kPl (p ≫ prj K F (n0 K F) i), by rw [← e, PhiN_val]⟩
  · rintro ⟨t, ht⟩
    obtain ⟨p, hp⟩ := exists_pt P0 (n0 K F) t
    have e : p ≫ PhiN P0 (n0 K F) = x := (jacPicEquiv K F).injective (hp.trans ht.symm)
    exact ⟨p.left (IsLocalRing.closedPoint K), by rw [← e]; rfl⟩

end Riem

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_ThetaSquare_Ne =====
section

/-!
# Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`

* `not_clsK_eq_eff`: for a nonspecial `g`-set `C` and a point `R ∉ C`, the class of `Zdiv C - [R]` (degree `g - 1`)
  contains no effective divisor (an `f` with `div f + Zdiv C - [R] ≥ 0` lies in `L(Zdiv C)`, so is constant);
* `exists_not_mem_W`: for `g ≥ 1` the `K`-point with class `Σ_{φ ∈ C} ([φ] - [P0]) - ([R] - [P0])` is not on `W`
  (Riemann's theorem `mem_W_iff`);
* `one_le_coheight_zTheta`: `1 ≤ coheight (zTheta P0)`.
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

section Ne

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem clsK_sum {α : Type*} (s : Finset α) (D : α → Places.Divisor K F) :
    clsK K F (∑ i ∈ s, D i) = ∑ i ∈ s, clsK K F (D i) :=
  map_sum (QuotientAddGroup.mk' (PrincK K F)) D s

theorem coe_ajCls (Q : Place K F) : ((ajCls K F P0 Q : Pic0K K F) : PicK K F) =
    clsK K F (Finsupp.single Q 1) - clsK K F (Finsupp.single P0 1) := rfl

/-- **A non-effective class of degree `g - 1`**: `Zdiv C - [R]` for a nonspecial `C` and `R ∉ C`. -/
theorem not_clsK_eq_eff {C : Finset (Rfin K F →ₐ[K] K)} (hC : IsNS K F C) {R : Rfin K F →ₐ[K] K}
    (hR : R ∉ C) {E : Places.Divisor K F} (hE : 0 ≤ E)
    (h : clsK K F (Zdiv C - Finsupp.single (Sum.inl (ptP R)) 1) = clsK K F E) : False := by
  obtain ⟨f, hf, hfd⟩ := (mem_PrincK K F).1 ((clsK_eq_iff K F).1 h)
  have hE' : PlacesK.div f + (Zdiv C - Finsupp.single (Sum.inl (ptP R)) 1) = E := by rw [hfd]; abel
  have hDC : Zdiv C - Finsupp.single (Sum.inl (ptP R)) 1 ≤ Zdiv C :=
    sub_le_self _ (Finsupp.single_nonneg.2 zero_le_one)
  have hfL : f ∈ LFK K F (Zdiv C) := by
    rw [mem_LFK hf]
    calc (0 : Places.Divisor K F) ≤ E := hE
      _ = PlacesK.div f + (Zdiv C - Finsupp.single (Sum.inl (ptP R)) 1) := hE'.symm
      _ ≤ PlacesK.div f + Zdiv C := add_le_add (le_refl _) hDC
  obtain ⟨c, rfl⟩ := hC f hfL
  have h0 : (PlacesK.div (algebraMap K F c) : Places.Divisor K F) = 0 :=
    (PlacesK.div_eq_zero_iff (K := K) (F := F) hf).2 (IntermediateField.algebraMap_mem _ c)
  rw [h0, zero_add] at hE'
  have hv := congrArg (fun G : Places.Divisor K F => G (Sum.inl (ptP R))) hE'
  have hv0 : (0 : ℤ) ≤ E (Sum.inl (ptP R)) := Finsupp.le_def.1 hE _
  simp only [Finsupp.coe_sub, Pi.sub_apply, Zdiv_inl_ptP, if_neg hR, Finsupp.single_eq_same] at hv
  omega

/-- **`W_{g-1} ≠ J`** (`g ≥ 1`): the class `Σ_{φ∈C}([φ]-[P0]) - ([R]-[P0])` is not on `W`. -/
theorem exists_not_mem_W (hg : 0 < genusFK K F) :
    ∃ x : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, x.left (IsLocalRing.closedPoint K) ∉ W P0 := by
  obtain ⟨T, hT, -⟩ := JacComplete.exists_pool (K := K) (F := F) 1 one_ne_zero (2 * genusFK K F + 1)
  obtain ⟨R, -⟩ : T.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨C, -, hCR, hCc, hC⟩ := exists_nonspecial_avoid T {R} (by rw [Finset.card_singleton]; omega)
  have hR : R ∉ C := Finset.disjoint_singleton_right.1 hCR
  let c : Pic0K K F := ∑ φ ∈ C, ajCls K F P0 (Sum.inl (ptP φ)) - ajCls K F P0 (Sum.inl (ptP R))
  refine ⟨(jacPicEquiv K F).symm (Multiplicative.ofAdd c), fun hx => ?_⟩
  obtain ⟨t, ht⟩ := (mem_W_iff P0 _).1 hx
  rw [MulEquiv.apply_symm_apply] at ht
  have hc := congrArg (fun z : Pic0K K F => (z : PicK K F)) (Multiplicative.ofAdd.injective ht)
  simp only [c, AddSubgroup.coe_sub, AddSubmonoidClass.coe_finsetSum, coe_ajCls] at hc
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, hCc, ← clsK_sum, ← clsK_sum] at hc
  have hgn : genusFK K F = n0 K F + 1 := by simp only [n0]; omega
  rw [hgn, succ_nsmul] at hc
  refine not_clsK_eq_eff hC hR (E := ∑ i, Finsupp.single (t i) 1)
    (Finset.sum_nonneg fun i _ => Finsupp.single_nonneg.2 zero_le_one) ?_
  rw [clsK_sub, ← sub_eq_zero]
  have hZ : clsK K F (Zdiv C) = clsK K F (∑ φ ∈ C, Finsupp.single (Sum.inl (ptP φ)) 1) := rfl
  rw [hZ]
  set a := clsK K F (Finsupp.single P0 1)
  set z := clsK K F (∑ φ ∈ C, Finsupp.single (Sum.inl (ptP φ) : Place K F) (1 : ℤ))
  set r := clsK K F (Finsupp.single (Sum.inl (ptP R) : Place K F) (1 : ℤ))
  set e := clsK K F (∑ i, Finsupp.single (t i) (1 : ℤ))
  have : z - r - e = (z - (n0 K F • a + a) - (r - a)) - (e - n0 K F • a) := by abel
  rw [this, hc, sub_self]

/-- **`Θ` has codimension `≥ 1`.** -/
theorem one_le_coheight_zTheta (hg : 0 < genusFK K F) : 1 ≤ Order.coheight (zTheta P0) := by
  obtain ⟨x, hx⟩ := exists_not_mem_W P0 hg
  have hne : zTheta P0 ≠ genericPoint (Jac K F).left := by
    intro h
    apply hx
    rw [← closure_zTheta P0, h, (genericPoint_spec (Jac K F).left).def]
    trivial
  have hle : zTheta P0 ≤ genericPoint (Jac K F).left := genericPoint_specializes (zTheta P0)
  have hlt : zTheta P0 < genericPoint (Jac K F).left := lt_of_le_not_ge hle fun h =>
    hne (Specializes.antisymm (show zTheta P0 ⤳ genericPoint (Jac K F).left from h) hle).eq
  exact le_trans le_add_self (Order.coheight_add_one_le hlt)

end Ne

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_ThetaSquare_Stab =====
section

/-!
# Unit S4-ThetaSquare, file Stab: the stabiliser of `W_{g-1}` is trivial (divisor form, Riemann-Roch only)

* `ell_add_single_le`: `ℓ(D + P) ≤ ℓ(D) + 1`;
* `card_le_ell`, `exists_ell_zero`, `exists_ell_one`: for `deg B = 0` and `ℓ(B) = 0` there is a `g`-set `C` of
  distinct points with `ℓ(B + Zdiv C) = 1` (greedy choice, as in `JacLaw_GenNS`, twisted by `B`);
* `exists_eq_of_ell_one`: if `ℓ(D) = 1`, the class of `D` contains exactly one effective divisor;
* **`mem_PrincK_of_stab`**: if `deg B = 0` and `Zdiv S + B` is equivalent to an effective divisor for every
  `(g-1)`-set `S`, then `B` is principal (each point `P` of `C` lies on the unique effective `D'' ~ B + Zdiv C`,
  so `D'' = Zdiv C`).
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

section Stab

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `ℓ(D + P) ≤ ℓ(D) + 1` (Riemann-Roch). -/
theorem ell_add_single_le (D : Places.Divisor K F) (v : Place K F) :
    ellFK K F (D + Finsupp.single v 1) ≤ ellFK K F D + 1 := by
  obtain ⟨W0, hW⟩ := exists_isCanonicalFK (K := K) (F := F)
  have hk := constField_eq_bot' (K := K) (F := F)
  have h1 := riemannRochFK' hk hW (D + Finsupp.single v 1)
  have h2 := riemannRochFK' hk hW D
  have h3 : ellFK K F (W0 - (D + Finsupp.single v 1)) ≤ ellFK K F (W0 - D) :=
    ellFK_mono (sub_le_sub_left (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one)) _)
  rw [PlacesK.Divisor.deg_add, deg_single_one] at h1
  omega

/-- If every `P ∈ S` raises `ℓ` above `ℓ(D) = 0`, then `ℓ(D + Zdiv S) ≥ #S`. -/
theorem card_le_ell (D : Places.Divisor K F) (hD : ellFK K F D = 0) (S : Finset (Rfin K F →ₐ[K] K))
    (hbad : ∀ φ ∈ S, 1 ≤ ellFK K F (D + Finsupp.single (Sum.inl (ptP φ)) 1)) :
    S.card ≤ ellFK K F (D + Zdiv S) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert φ S hφ ih =>
    have ih' := ih fun ψ hψ => hbad ψ (Finset.mem_insert_of_mem hψ)
    have hle : D ≤ D + Zdiv S := le_add_of_nonneg_right (Zdiv_nonneg S)
    have hval : (D + Zdiv S) (Sum.inl (ptP φ)) = D (Sum.inl (ptP φ)) := by
      rw [Finsupp.add_apply, Zdiv_inl_ptP, if_neg hφ, add_zero]
    have key := ellFK_step (Sum.inl (ptP φ)) hle hval
    have hb := hbad φ (Finset.mem_insert_self φ S)
    rw [Finset.card_insert_of_notMem hφ, Zdiv_insert hφ, ← add_assoc]
    omega

/-- Greedy step, twisted by `B` (`deg B = 0`, `ℓ(B) = 0`): `i`-sets `C` with `ℓ(B + Zdiv C) = 0` for `i < g`. -/
theorem exists_ell_zero (B : Places.Divisor K F) (hB : ellFK K F B = 0) (hd : B.deg = 0) :
    ∀ i, i + 1 ≤ genusFK K F →
      ∃ C : Finset (Rfin K F →ₐ[K] K), C.card = i ∧ ellFK K F (B + Zdiv C) = 0 := by
  obtain ⟨T, hT, -⟩ := JacComplete.exists_pool (K := K) (F := F) 1 one_ne_zero (2 * genusFK K F)
  intro i
  induction i with
  | zero => intro _; exact ⟨∅, Finset.card_empty, by rw [Zdiv_empty, add_zero, hB]⟩
  | succ i ih =>
    intro hi
    obtain ⟨C, hCc, hC0⟩ := ih (by omega)
    by_contra hne
    have hbad : ∀ φ ∈ T \ C, 1 ≤ ellFK K F (B + Zdiv C + Finsupp.single (Sum.inl (ptP φ)) 1) := by
      intro φ hφ
      have hφC : φ ∉ C := (Finset.mem_sdiff.1 hφ).2
      by_contra h0
      exact hne ⟨insert φ C, by rw [Finset.card_insert_of_notMem hφC, hCc], by
        rw [Zdiv_insert hφC, ← add_assoc]; omega⟩
    have hge := card_le_ell (B + Zdiv C) hC0 (T \ C) hbad
    have hcard := Finset.le_card_sdiff C T
    have hdeg : (B + Zdiv C + Zdiv (T \ C)).deg = ((i + (T \ C).card : ℕ) : ℤ) := by
      rw [PlacesK.Divisor.deg_add, PlacesK.Divisor.deg_add, hd, deg_Zdiv, deg_Zdiv, hCc]; push_cast; ring
    have hrr := ellFK_eq_of_deg (constField_eq_bot' (K := K) (F := F)) (D := B + Zdiv C + Zdiv (T \ C))
      (by rw [hdeg]; push_cast; omega)
    rw [hdeg] at hrr
    push_cast at hrr
    omega

/-- A `g`-set `C` with `ℓ(B + Zdiv C) = 1`, for `deg B = 0`, `ℓ(B) = 0`, `g ≥ 1`. -/
theorem exists_ell_one (hg : 0 < genusFK K F) (B : Places.Divisor K F) (hB : ellFK K F B = 0)
    (hd : B.deg = 0) :
    ∃ C : Finset (Rfin K F →ₐ[K] K), C.card = genusFK K F ∧ ellFK K F (B + Zdiv C) = 1 := by
  obtain ⟨C, hCc, hC0⟩ := exists_ell_zero B hB hd (genusFK K F - 1) (by omega)
  obtain ⟨T, hT, -⟩ := JacComplete.exists_pool (K := K) (F := F) 1 one_ne_zero (genusFK K F)
  obtain ⟨φ, -, hφC⟩ : ∃ φ ∈ T, φ ∉ C := by
    by_contra h
    push Not at h
    have := Finset.card_le_card (fun x hx => h x hx)
    omega
  refine ⟨insert φ C, by rw [Finset.card_insert_of_notMem hφC, hCc]; omega, le_antisymm ?_ ?_⟩
  · have := ell_add_single_le (B + Zdiv C) (Sum.inl (ptP φ))
    rw [Zdiv_insert hφC, ← add_assoc]
    omega
  · have := riemann_inequalityFK' (constField_eq_bot' (K := K) (F := F)) (B + Zdiv (insert φ C))
    rw [PlacesK.Divisor.deg_add, hd, deg_Zdiv, Finset.card_insert_of_notMem hφC, hCc] at this
    omega

/-- If `ℓ(D) = 1`, the class of `D` contains exactly one effective divisor, `div f0 + D`. -/
theorem exists_eq_of_ell_one {D : Places.Divisor K F} (h1 : ellFK K F D = 1) :
    ∃ f0 : F, f0 ≠ 0 ∧ 0 ≤ PlacesK.div f0 + D ∧ ∀ E : Places.Divisor K F, 0 ≤ E →
      clsK K F E = clsK K F D → E = PlacesK.div f0 + D := by
  rw [ellFK_def] at h1
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.1 h1
  have hv0 : (v : F) ≠ 0 := fun h => hv (Subtype.ext h)
  refine ⟨v, hv0, (mem_LFK hv0).1 v.2, fun E hE hc => ?_⟩
  obtain ⟨h, hh, hdiv⟩ := (mem_PrincK K F).1 ((clsK_eq_iff K F).1 hc.symm)
  have hL : h ∈ LFK K F D := by
    rw [mem_LFK hh, hdiv, show -D + E + D = E by abel]
    exact hE
  obtain ⟨a, ha⟩ := hall ⟨h, hL⟩
  have ha' : algebraMap K F a * v = h := by
    rw [← Algebra.smul_def]
    exact congrArg Subtype.val ha
  have ha0 : algebraMap K F a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at ha'
    exact hh ha'.symm
  have hdc : (PlacesK.div (algebraMap K F a) : Places.Divisor K F) = 0 :=
    (PlacesK.div_eq_zero_iff (K := K) (F := F) ha0).2 (IntermediateField.algebraMap_mem _ a)
  rw [← ha', PlacesK.div_mul ha0 hv0, hdc, zero_add] at hdiv
  rw [hdiv]
  abel

/-- **Trivial stabiliser, divisor form**: if `deg B = 0` and `Zdiv S + B` is equivalent to an effective divisor for
every `(g-1)`-set `S` of distinct points, then `B` is principal. -/
theorem mem_PrincK_of_stab (hg : 0 < genusFK K F) (B : Places.Divisor K F) (hd : B.deg = 0)
    (hstab : ∀ S : Finset (Rfin K F →ₐ[K] K), S.card = n0 K F →
      ∃ E : Places.Divisor K F, 0 ≤ E ∧ clsK K F E = clsK K F (Zdiv S + B)) :
    B ∈ PrincK K F := by
  by_cases hB : ellFK K F B = 0
  swap
  · have hne : LFK K F B ≠ ⊥ := by
      intro h
      apply hB
      rw [ellFK_def, h, finrank_bot]
    obtain ⟨f, hfL, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hz := eq_zero_of_nonneg_of_deg ((mem_LFK hf).1 hfL)
      (by rw [PlacesK.Divisor.deg_add, PlacesK.deg_div hf, hd, add_zero])
    exact ⟨f⁻¹, inv_ne_zero hf, by rw [divK_inv K hf]; exact (eq_neg_of_add_eq_zero_right hz).symm⟩
  obtain ⟨C, hCc, hC1⟩ := exists_ell_one hg B hB hd
  obtain ⟨f0, hf0, hpos, huniq⟩ := exists_eq_of_ell_one hC1
  have hpt : ∀ φ ∈ C, 1 ≤ (PlacesK.div f0 + (B + Zdiv C) : Places.Divisor K F) (Sum.inl (ptP φ)) := by
    intro φ hφ
    have hS : (C.erase φ).card = n0 K F := by
      rw [Finset.card_erase_of_mem hφ, hCc]
    obtain ⟨E, hE, hcl⟩ := hstab _ hS
    have hZ : Zdiv C = Zdiv (C.erase φ) + Finsupp.single (Sum.inl (ptP φ)) 1 := by
      conv_lhs => rw [← Finset.insert_erase hφ]
      exact Zdiv_insert (Finset.notMem_erase φ _)
    have hcls : clsK K F (E + Finsupp.single (Sum.inl (ptP φ)) 1) = clsK K F (B + Zdiv C) := by
      rw [hZ, show B + (Zdiv (C.erase φ) + Finsupp.single (Sum.inl (ptP φ)) 1) =
        (Zdiv (C.erase φ) + B) + Finsupp.single (Sum.inl (ptP φ)) 1 by abel,
        clsK_add (K := K) (F := F) E, clsK_add (K := K) (F := F) (Zdiv (C.erase φ) + B), hcl]
    have hE' := huniq _ (add_nonneg hE (Finsupp.single_nonneg.2 zero_le_one)) hcls
    rw [← hE', Finsupp.add_apply, Finsupp.single_eq_same]
    have := Finsupp.le_def.1 hE (Sum.inl (ptP φ))
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  have hge : Zdiv C ≤ PlacesK.div f0 + (B + Zdiv C) := by
    rw [Finsupp.le_def]
    intro v
    by_cases hv : ∃ φ ∈ C, v = Sum.inl (ptP φ)
    · obtain ⟨φ, hφ, rfl⟩ := hv
      rw [Zdiv_inl_ptP, if_pos hφ]
      exact hpt φ hφ
    · have h0 : Zdiv C v = 0 := by
        rw [Zdiv, Finsupp.finsetSum_apply]
        refine Finset.sum_eq_zero fun φ hφ => ?_
        rw [Finsupp.single_apply, if_neg]
        exact fun h => hv ⟨φ, hφ, h.symm⟩
      rw [h0]
      exact Finsupp.le_def.1 hpos v
  have h0 : 0 ≤ PlacesK.div f0 + B := by
    have := sub_nonneg.2 hge
    rwa [show PlacesK.div f0 + (B + Zdiv C) - Zdiv C = PlacesK.div f0 + B by abel] at this
  have hz := eq_zero_of_nonneg_of_deg h0 (by rw [PlacesK.Divisor.deg_add, PlacesK.deg_div hf0, hd, add_zero])
  exact ⟨f0⁻¹, inv_ne_zero hf0, by rw [divK_inv K hf0]; exact (eq_neg_of_add_eq_zero_right hz).symm⟩

end Stab

end RamanujanPetersson.ThetaSquare

end


