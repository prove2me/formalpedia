-- Prove2me | Definitions.Def_RPLib_F2_083
-- name    : RPLib_F2_083
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T20:48:29.649777+00:00
-- url     : https://prove2.me/theorems/dcc8ed20-52cc-44d1-a740-19303b1b9f28
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 083 (part 1 of file 057 of 70)
-- statement:
--   File 083 (part 1 of file 057 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_AJCo`: The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`
--   * `S4.Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
--   * `S4.Def_RP_JacComplete_Fam`: The Jacobian (unit S4-JacComplete), part `Fam`: **L21, families of divisors give maps to `J`**
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_056

/-!
# Ramanujan-Petersson curve library (flat edition), file 083 (part 1 of file 057 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_AJCo`: The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`
* `S4.Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
* `S4.Def_RP_JacComplete_Fam`: The Jacobian (unit S4-JacComplete), part `Fam`: **L21, families of divisors give maps to `J`**
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJCo =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJCo`: the Abel-Jacobi map on the curve `X1 = Sym¹ X`

`X1 K F = SymX K x 1` (`x = algebraMap K[X] F X`): the charts `Spec Sym¹ B_A` glued (JacSymB).
* `diag1 : B →ₐ Sym¹ B` (the single tensor factor) and its naturality `symMap_diag1`;
* `isReduced_X1`; `plA A θ`, the center of a `K`-point `θ` of `B_A` (`isCenter_plA`, `plA_restrict`);
* `chartAJ P0 A : chart A ⟶ J` (`Rfin (SynF c) ≅ B_{c} ⊆ B_A → Sym¹ B_A`, then `ajChart P0 c`), value `chartAJ_kpt`;
* **`ajX1 P0 : X1 K F ⟶ J`** glued (`JacChunk.glueY`); `ajX1_over`, **`ajX1_apply`**: the value at the closed
  point `colimit.ι A (kpt ψ)` is `ajPt P0 (plA A (ψ.comp diag1))` (class `[Q] - [P0]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- the instance diamonds on the nested localizations need nested synthPending (diagnostics, session 20)
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section Diag

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B]

end Diag

section AJ1

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

set_option maxHeartbeats 800000 in
/-- The chart maps agree at closed points with the same image in `X1`. -/
theorem chartAJ_comp (A A' : (ChartIdx K)ᵒᵖ) (p : cht K F A) (p' : cht K F A')
    (hp : IsClosed ({p} : Set (cht K F A))) (_ : IsClosed ({p'} : Set (cht K F A')))
    (e : colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A p =
      colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A' p') :
    chartAJ P0 A p = chartAJ P0 A' p' := by
  obtain ⟨A'', fi, fj, z, rfl, rfl⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (symDiagram K (algebraMap K[X] F X) 1)).1 e
  have hz : IsClosed ({z} : Set ((symDiagram K (algebraMap K[X] F X) 1).obj A'')) := by
    have hinj := ((symDiagram K (algebraMap K[X] F X) 1).map fi).isOpenEmbedding.injective
    have h := hp.preimage ((symDiagram K (algebraMap K[X] F X) 1).map fi).isOpenEmbedding.continuous
    have e2 : (⇑((symDiagram K (algebraMap K[X] F X) 1).map fi)) ⁻¹'
        {((symDiagram K (algebraMap K[X] F X) 1).map fi) z} = {z} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact hinj.eq_iff
    exact (congrArg IsClosed e2).mp h
  obtain ⟨ψ, rfl⟩ := exists_kpt (K := K) (A := SymRing K (chartRing (algebraMap K[X] F X) A''.unop.1) 1) z hz
  have key : ∀ {B0 : (ChartIdx K)ᵒᵖ} (f : A'' ⟶ B0),
      (symDiagram K (algebraMap K[X] F X) 1).map f
          (kpt (A := SymRing K (chartRing (algebraMap K[X] F X) A''.unop.1) 1) ψ) =
        kpt (A := SymRing K (chartRing (algebraMap K[X] F X) B0.unop.1) 1)
          (ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop))) := fun {B0} f => by
    rw [symDiagram_map]
    exact SpecMap_kpt (A := SymRing K (chartRing (algebraMap K[X] F X) B0.unop.1) 1)
      (B := SymRing K (chartRing (algebraMap K[X] F X) A''.unop.1) 1)
      (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop)) ψ
  have key2 : ∀ {B0 : (ChartIdx K)ᵒᵖ} (f : A'' ⟶ B0),
      (ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop))).comp diag1 =
        (ψ.comp diag1).comp (Subalgebra.inclusion (chartRing_mono _ (leOfHom f.unop))) := fun f => by
    rw [AlgHom.comp_assoc, chartMap, symMap_diag1, AlgHom.comp_assoc]
  rw [key fi, key fj, chartAJ_kpt, chartAJ_kpt, key2 fi, key2 fj, plA_restrict (leOfHom fi.unop),
    plA_restrict (leOfHom fj.unop)]

/-- **The Abel-Jacobi map on the curve** `X1 = Sym¹ X` (base point `P0`), glued from the charts. -/
noncomputable def ajX1 : X1 K F ⟶ (Jac K F).left :=
  JacChunk.glueY (toSpecK K (algebraMap K[X] F X) 1) (Jac K F).hom (cht K F)
    (colimit.ι (symDiagram K (algebraMap K[X] F X) 1)) (chartAJ P0) cht_cov (chartAJ_over P0)
    (chartAJ_comp P0)

theorem ajX1_over : ajX1 P0 ≫ (Jac K F).hom = toSpecK K (algebraMap K[X] F X) 1 :=
  JacChunk.glueY_over _ _ _ _ _ _ _ _

/-- **Value of the AJ map** at the closed point `colimit.ι A (kpt ψ)` of `X1`: the point of class `[Q] - [P0]`,
`Q = plA A (ψ.comp diag1)`. -/
theorem ajX1_apply (A : (ChartIdx K)ᵒᵖ) (ψ : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1 →ₐ[K] K) :
    ajX1 P0 (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A
        (kpt (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) ψ)) =
      ajPt K F P0 (plA A.unop (ψ.comp diag1)) :=
  (JacChunk.glueY_apply _ _ _ _ _ _ _ _ A _).trans (chartAJ_kpt P0 A ψ)

end AJ1

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacComplete_Proper =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**

Route AJ (NOTES, session 6 decision): the Abel-Jacobi map `ajX1 P0 : X1 = Sym¹ X ⟶ J` (AJCo) gives
`Φ_n : X1^n ⟶ J`, `(Q_1, …, Q_n) ↦ Σ ([Q_i] - [P0])` (products in `Over (Spec K)`, hom-group law of `J`).
* `exists_inl`, `exists_plc`, `exists_chartPt`: every place of `F` is the center of a `K`-point of a chart of `X1`;
* `X1O`, `ιO`, `ajO P0 : X1O ⟶ J`, `exists_kX1`: every `ajK P0 Q` is the image of a `K`-point of `X1`;
* `PP n = X1^n` (`isProper_PP`), `PhiN P0 n : PP n ⟶ J`, `exists_pt`: the value `Σ ajCls P0 (t i)` is attained;
* `surjective_PhiN`: `Φ_g` is surjective (closed image, contains every closed point by `exists_eff_rep`, `J` Jacobson);
* **`isProper_Jac : IsProper (Jac K F).hom`** (`UniversallyClosed.of_comp_surjective`).
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

section Proper

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- The Abel-Jacobi map `X1 ⟶ J` over `Spec K`. -/
noncomputable def ajO : X1O K F ⟶ Jac K F := Over.homMk (ajX1 P0) (ajX1_over P0)

/-- **Every `ajK P0 Q` comes from a `K`-point of `X1`.** -/
theorem exists_kX1 (Q : Place K F) :
    ∃ q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F, q ≫ ajO P0 = ajK K F P0 Q := by
  obtain ⟨A, ψ, hψ⟩ := exists_chartPt Q
  refine ⟨kptO ψ ≫ ιO K F A, ?_⟩
  apply Over.OverMorphism.ext
  refine ext_of_apply_closedPoint_eq (Jac K F).hom (Over.w _) (Over.w _) ?_
  have e : ((kptO ψ ≫ ιO K F A) ≫ ajO P0).left (IsLocalRing.closedPoint K) =
      ajX1 P0 (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A
        (Spec.map (CommRingCat.ofHom (ψ : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1 →+* K))
          (IsLocalRing.closedPoint K))) := rfl
  rw [e, SpecMap_closedPoint, ajX1_apply, hψ]
  rfl

/-- `Φ_n : X1^n ⟶ J`, `(Q_i) ↦ Σ ([Q_i] - [P0])` (hom-group law of `J`). -/
noncomputable def PhiN : (n : ℕ) → (PP K F n ⟶ Jac K F)
  | 0 => 1
  | n + 1 => (fst (PP K F n) (X1O K F) ≫ PhiN n * snd (PP K F n) (X1O K F) ≫ ajO P0 :
      PP K F n ⊗ X1O K F ⟶ Jac K F)

/-- **The value `Σ ([t_i] - [P0])` is attained by `Φ_n`.** -/
theorem exists_pt (n : ℕ) (t : Fin n → Place K F) :
    ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n,
      jacPicEquiv K F (p ≫ PhiN P0 n) = Multiplicative.ofAdd (∑ i, ajCls K F P0 (t i)) := by
  induction n with
  | zero =>
    refine ⟨𝟙 _, ?_⟩
    show jacPicEquiv K F (𝟙 _ ≫ (1 : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)) = _
    rw [Category.id_comp, map_one, Finset.univ_eq_empty, Finset.sum_empty, ofAdd_zero]
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih (fun i => t (Fin.castSucc i))
    obtain ⟨q, hq⟩ := exists_kX1 P0 (t (Fin.last n))
    refine ⟨lift p q, ?_⟩
    show jacPicEquiv K F (lift p q ≫
      (fst (PP K F n) (X1O K F) ≫ PhiN P0 n * snd (PP K F n) (X1O K F) ≫ ajO P0)) = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, map_mul, hp, hq, ajK, MulEquiv.apply_symm_apply,
      Fin.sum_univ_castSucc, ofAdd_add]

end Proper

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

variable {V : Over (Spec (.of K))} [Smooth V.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]

end Fam

end RamanujanPetersson.JacComplete


end


