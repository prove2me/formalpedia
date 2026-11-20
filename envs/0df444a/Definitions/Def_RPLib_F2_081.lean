-- Prove2me | Definitions.Def_RPLib_F2_081
-- name    : RPLib_F2_081
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T18:29:56.589965+00:00
-- url     : https://prove2.me/theorems/730321a3-7f3e-4b93-a2e5-13d629b270aa
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 081 (part 1 of file 047 of 70)
-- statement:
--   File 081 (part 1 of file 047 of 70) of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
--   * `S4.Def_RP_ThetaSquare_Codim`: Unit S4-ThetaSquare, file Codim: `Θ` is a prime Weil divisor (`coheight (zTheta P0) = 1`)
--   * `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
--   * `S4.Def_RP_ThetaSquare_PlusJ`: Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula
--   * `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
--   * `S4.Def_RP_ThetaSquare_Mult1`: Unit S4-ThetaSquare, file Mult1: local algebra for the multiplicity-one count (F6a)
--   * `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_044

/-!
# Ramanujan-Petersson curve library (flat edition), file 081 (part 1 of file 047 of 70)

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacComplete_AJGlue`: The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces
* `S4.Def_RP_ThetaSquare_Codim`: Unit S4-ThetaSquare, file Codim: `Θ` is a prime Weil divisor (`coheight (zTheta P0) = 1`)
* `S4.Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
* `S4.Def_RP_ThetaSquare_PlusJ`: Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula
* `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
* `S4.Def_RP_ThetaSquare_Mult1`: Unit S4-ThetaSquare, file Mult1: local algebra for the multiplicity-one count (F6a)
* `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacComplete_AJGlue =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJGlue`: the cover of the chart `Spec B'` by the AJ pieces

`B' = Rfin (SynF K F c0)`.
* `locallyOfFiniteType_sR`; the piece index `PIdx K F c0` and the open immersions `pj c0 i : Spec LocR → Spec B'`.
* `pj_kpt` (closed points), `pj_cov` (the pieces cover the closed points), `pj_over`.
The glued map `ajChart` is in part `AJGlue2`.
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

section Glue

open Classical
open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K]

variable [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F) (c0 : K)

theorem pj_kpt (i : PIdx K F c0) (x : LocR c0 i.2.1 i.2.2 →ₐ[K] K) :
    pj c0 i (kpt (A := LocR c0 i.2.1 i.2.2) x) =
      kpt (A := Rfin K (SynF K F c0)) (x.comp (pieceIn c0 i.2.1 i.2.2)) :=
  SpecMap_kpt (A := Rfin K (SynF K F c0)) (B := LocR c0 i.2.1 i.2.2) (pieceIn c0 i.2.1 i.2.2) x

end Glue

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_ThetaSquare_Codim =====
section

/-!
# Unit S4-ThetaSquare, file Codim: `Θ` is a prime Weil divisor (`coheight (zTheta P0) = 1`)

`coheight_zTheta_le_one` (Krull on the chart `X0 = Spec LawRing`): pick a chart point `y0`, one of its points `φ0`
and `u = x - x(φ0) ∈ Rfin` (nonzero: `exists_pool`), `N = Nm(u) ∈ LawRing`; a minimal prime `q` of `(N)` has height
`≤ 1` (Krull's principal ideal theorem). Every closed point `A'` of `V(N)` contains a zero `φ` of `u`, so
`jX0 A' - c_φ ∈ W` (`mem_transl_W`); `V(N)` is closed in the Jacobson `X0` and the finite union of the translates
`W + c_φ` is closed, so `jX0 q` lies in one of them, whence `coheight zTheta ≤ coheight (jX0 q) = ht q ≤ 1`.
`theta_mem_weilDivisors`: with `one_le_coheight_zTheta`, `Θ ∈ weilDivisors J`.
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

section Codim

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- The value of `Nm(u)` at a chart point is `∏_l φ_l(u)`. -/
theorem eval_normS (u : Rfin K F) (yR : LawRing K F →ₐ[K] K) :
    yR (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) u)) =
      ∏ l, liftTuple (yR.comp (awayι (K := K) (lawPre K F).u0)) l u := by
  show (yR.comp (awayι (K := K) (lawPre K F).u0)) (normS K u) = _
  conv_lhs => rw [← symPt_liftTuple (yR.comp (awayι (K := K) (lawPre K F).u0))]
  exact symPt_normS _ u

end Codim

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_ThetaX0 =====
section

/-!
# Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`

* `pullback_openImm`: the pull-back of a Weil divisor along an open immersion is its restriction;
* `tauX d`, an open immersion, dominant; `pullback_tauX_apply`: `τ_d^* Θ` is the indicator of `τ_d⁻¹ (zTheta)`;
* `exists_eta`: if `τ_d y ∈ W`, then `zTheta = τ_d η'` for some `η' ⤳ y`;
* `exists_sep`: finitely many `K`-points of `Rfin` off a finite set `S` are common zeros of an `s` that has no zero on `S`;
* `normS_mem_eta` (the upper-bound input of the plus-curve trick): if `φ(t) = 0` and some chart point `A` contains `φ`
  but no other zero of `t`, then `Nm(t)` vanishes at the point `η'` with `τ_{c_φ⁻¹} η' = zTheta`. Proof: a minimal prime
  `q ⊆ m_A` of `(Nm t)` has height `≤ 1` (Krull); every closed point of `V(Nm t)` contains a zero of `t`, so it lies on
  `τ⁻¹ W` (if that zero is `φ`, `mem_transl_W`) or on `V(Nm s)` (`s` vanishing at the other zeros, none on `A`); by
  Jacobson `q ∈ τ⁻¹ W`, and `coheight zTheta = 1` forces `τ q = zTheta`.
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

section General

open CategoryTheory AlgebraicGeometry

variable {U C : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsIntegral C] [IsLocallyNoetherian C]
  [∀ y : C, UniqueFactorizationMonoid (C.presheaf.stalk y)] (ι : U ⟶ C) [IsOpenImmersion ι] [IsDominant ι]

end General

section ThetaX0

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

instance isLocallyNoetherian_JacT : IsLocallyNoetherian (Jac K F).left :=
  LocallyOfFiniteType.isLocallyNoetherian (Jac K F).hom

instance isIntegral_JacT : IsIntegral (Jac K F).left := isIntegral_of_irreducibleSpace_of_isReduced _

instance ufd_JacT (y : (Jac K F).left) : UniqueFactorizationMonoid ((Jac K F).left.presheaf.stalk y) :=
  uniqueFactorizationMonoid_stalk_of_smooth (Jac K F).hom y

instance nonempty_X0T : Nonempty (X0 K F) :=
  ⟨((⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (LawRing K F)) : X0 K F)⟩

/-- The translated chart `τ_d = t_d ∘ jX0 : X0 → J`. -/
noncomputable def tauX (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : X0 K F ⟶ (Jac K F).left :=
  jX0 K F ≫ (transl (Jac K F) d).left

theorem tauX_apply (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (z : X0 K F) :
    tauX d z = (transl (Jac K F) d).left (jX0 K F z) := rfl

instance isOpenImmersion_tauX (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : IsOpenImmersion (tauX d) := by
  haveI := isIso_translL (Jac K F) d
  unfold tauX
  infer_instance

instance isDominant_tauX (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) : IsDominant (tauX d) :=
  isDominant_openImm (tauX d)

end ThetaX0

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_PlusJ =====
section

/-!
# Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula

For `g` points `a_i` of `Rfin` and a slot `i0`, `plusR = plusMap inclR a i0 : Sym^g Rfin → R1`; with `h = plusR(u0)`
and `R2 = R1[1/h]` it induces **`lawMapPlus : LawRing → R2`**, whose `K`-points have class
`[P] + [E] - [Θ]` (`psiJ_lawMapPlus`), `P` the point of `Rfin` under `x`, `E = Σ_{i ≠ i0} a_i` (`plusE`).
Also: the center of a `K`-point `y` of `R1` restricted to `B_{c0}` is the finite place of `y|Rfin` (`isCenter_R1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial AlgebraicGeometry

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete RamanujanPetersson.RR

universe u

section PlusJ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

variable [IsAlgClosed K]

variable (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

/-- `h = plus(u0)`. -/
noncomputable def plusH : R1 F c0 := plusR c0 a i0 (lawPre K F).u0

/-- **The coordinate ring of the plus-curve**, `R2 = R1[1/h]`. -/
abbrev R2 : Type u := Localization.Away (plusH c0 a i0)

theorem isUnit_plusH :
    IsUnit (((awayι (K := K) (plusH c0 a i0)).comp (plusR c0 a i0)) (lawPre K F).u0) :=
  IsLocalization.Away.algebraMap_isUnit (plusH c0 a i0)

/-- **The plus-curve `Spec R2 → X0`** as `LawRing K F → R2`. -/
noncomputable def lawMapPlus : LawRing K F →ₐ[K] R2 c0 a i0 :=
  IsLocalization.Away.liftAlgHom (f := (awayι (K := K) (plusH c0 a i0)).comp (plusR c0 a i0)) (lawPre K F).u0
    (isUnit_plusH c0 a i0)

theorem lawMapPlus_comp : (lawMapPlus c0 a i0).comp (awayι (K := K) (lawPre K F).u0) =
    (awayι (K := K) (plusH c0 a i0)).comp (plusR c0 a i0) :=
  AlgHom.ext fun t => by
    rw [AlgHom.comp_apply, awayι_apply, lawMapPlus, IsLocalization.Away.liftAlgHom_apply,
      IsLocalization.Away.lift_eq]
    rfl

theorem comp_lawMapPlus (x : R2 c0 a i0 →ₐ[K] K) :
    (x.comp (lawMapPlus c0 a i0)).comp (awayι (K := K) (lawPre K F).u0) =
      symPt (Function.update a i0 ((x.comp (awayι (K := K) (plusH c0 a i0))).comp (inclR c0))) := by
  rw [AlgHom.comp_assoc, lawMapPlus_comp, ← AlgHom.comp_assoc]
  exact comp_plusMap _ _ _ _

/-- The point of `Rfin` under a `K`-point `x` of `R2`. -/
noncomputable abbrev ptR2 (x : R2 c0 a i0 →ₐ[K] K) : Rfin K F →ₐ[K] K :=
  (x.comp (awayι (K := K) (plusH c0 a i0))).comp (inclR c0)

open Classical in
theorem injective_update (x : R2 c0 a i0 →ₐ[K] K) :
    Function.Injective (Function.update a i0 (ptR2 c0 a i0 x)) := by
  have hc := card_lawPt (K := K) (F := F) (yR := x.comp (lawMapPlus c0 a i0))
  rw [comp_lawMapPlus, ptSet_symPt] at hc
  have h2 : (Finset.univ.image (Function.update a i0 (ptR2 c0 a i0 x))).card = (Finset.univ : Finset (Fin (genusFK K F))).card := by
    rw [hc, Finset.card_univ, Fintype.card_fin]
  intro i j hij
  exact Finset.card_image_iff.1 h2 (Finset.mem_coe.2 (Finset.mem_univ i)) (Finset.mem_coe.2 (Finset.mem_univ j)) hij

end PlusJ

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

/-- `Sym¹ B_{c0} ≅ B_{c0} → R1 → R2`. -/
noncomputable def symToR2 : SymRing K (Bc F c0) 1 →ₐ[K] R2 c0 a i0 :=
  (awayι (K := K) (plusH c0 a i0)).comp ((inclB c0).comp (sym1Equiv (k := K) (B := Bc F c0)).toAlgHom)

/-- **The plus-curve as a map to the curve**: `Spec R2 → cht {c0} ⊆ X1`. -/
noncomputable def plusX : specO K (R2 c0 a i0) ⟶ X1O K F :=
  Over.homMk (U := specO K (R2 c0 a i0)) (V := specO K (SymRing K (Bc F c0) 1))
    (Spec.map (CommRingCat.ofHom (symToR2 c0 a i0 : SymRing K (Bc F c0) 1 →+* R2 c0 a i0)))
    (SpecMap_sR (symToR2 c0 a i0)) ≫ ιO K F (op (idx0 c0))

theorem symToR2_diag1 (x : R2 c0 a i0 →ₐ[K] K) :
    (x.comp (symToR2 c0 a i0)).comp diag1 = (x.comp (awayι (K := K) (plusH c0 a i0))).comp (inclB c0) :=
  AlgHom.ext fun b => congrArg (fun z => x (awayι (K := K) (plusH c0 a i0) (inclB c0 z))) (undiag1_diag1 b)

end PlusX

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Mult1 =====
section

/-!
# Unit S4-ThetaSquare, file Mult1: local algebra for the multiplicity-one count (F6a)

* `ufd_X0T`: the stalks of the chart `X0` are factorial (they are stalks of `J`);
* `span_eq_maximalIdeal_of_dedekind`: in `A_P` (`A` Dedekind), any `t ∈ P \ P²` generates the maximal ideal;
* `eq_of_zero_imp`, `exists_unif`: a uniformizer `t` at a point `φ` of `Rfin` with no zero on a finite set `S ∌ φ`;
* on the plus-curve `Spec R2`: `plusH_ne_zero`, `isDomain_R2`, `isNoetherianRing_R2`, `isLocalization_rfin_R2`
  (`R2` is a localization of `Rfin`), `dvr_stalk_R2` (the stalk at a `K`-point is `Rfin` localized at `ptP`),
  **`coheight_kpt_R2`** (`K`-points have codimension one) and **`ord_kpt_R2`** (a uniformizer has order one).
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

section Alg

open IsLocalRing

end Alg

section Chart

open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The stalks of the chart `X0` are factorial (stalks of `J` along the open immersion `jX0`). -/
instance ufd_X0T (y : X0 K F) : UniqueFactorizationMonoid ((X0 K F).presheaf.stalk y) :=
  (asIso ((jX0 K F).stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid (ufd_JacT _)

end Chart

section R2

open CategoryTheory AlgebraicGeometry IsLocalRing Order

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

/-- `h ≠ 0` as soon as `R2 = R1[1/h]` has a `K`-point. -/
theorem plusH_ne_zero (x : R2 c0 a i0 →ₐ[K] K) : plusH c0 a i0 ≠ 0 := by
  intro h
  have h1 : IsUnit (((x : R2 c0 a i0 →+* K).comp (algebraMap (R1 F c0) (R2 c0 a i0))) (plusH c0 a i0)) :=
    (IsLocalization.Away.algebraMap_isUnit (S := R2 c0 a i0) (plusH c0 a i0)).map x
  generalize ((x : R2 c0 a i0 →+* K).comp (algebraMap (R1 F c0) (R2 c0 a i0))) = g at h1
  rw [h, map_zero, isUnit_zero_iff] at h1
  exact zero_ne_one h1

/-- `R2` is a domain as soon as it has a `K`-point. -/
theorem isDomain_R2 (x : R2 c0 a i0 →ₐ[K] K) : IsDomain (R2 c0 a i0) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (plusH_ne_zero c0 a i0 x))

instance isNoetherianRing_R2 : IsNoetherianRing (R2 c0 a i0) := by
  haveI : IsNoetherianRing (R1 F c0) := Algebra.FiniteType.isNoetherianRing K _
  exact IsLocalization.isNoetherianRing (Submonoid.powers (plusH c0 a i0)) _ inferInstance

/-- `R2` is a localization of `Rfin`. -/
instance isLocalization_rfin_R2 : IsLocalization (IsLocalization.localizationLocalizationSubmodule
    (Submonoid.powers (xcR F c0)) (Submonoid.powers (plusH c0 a i0))) (R2 c0 a i0) :=
  IsLocalization.localization_localization_isLocalization _ _ _

theorem algebraMap_rfin_R2_apply (x : R2 c0 a i0 →ₐ[K] K) (b : Rfin K F) :
    x (algebraMap (Rfin K F) (R2 c0 a i0) b) = ptR2 c0 a i0 x b := by
  rw [IsScalarTower.algebraMap_apply (Rfin K F) (R1 F c0) (R2 c0 a i0)]
  rfl

/-- **The stalk of `Spec R2` at a `K`-point `x`** is a discrete valuation ring (it is `Rfin` localized at
`ptP (ptR2 x)`), and the germ of a uniformizer `t` generates its maximal ideal. -/
theorem dvr_stalk_R2 [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K) :
    IsDiscreteValuationRing ((Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x)) ∧
    ∀ t : Rfin K F, ptR2 c0 a i0 x t = 0 → t ∉ (ptP (ptR2 c0 a i0 x)).asIdeal ^ 2 →
      Ideal.span {(Spec (.of (R2 c0 a i0))).presheaf.germ ⊤ (kpt x) trivial
        ((Scheme.ΓSpecIso (.of (R2 c0 a i0))).inv.hom (algebraMap (Rfin K F) (R2 c0 a i0) t))} =
        maximalIdeal ((Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x)) := by
  letI iR : Algebra (R2 c0 a i0) ((Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x)) :=
    StructureSheaf.stalkAlgebra _ (kpt x)
  haveI : (kpt x).asIdeal.IsPrime := (kpt x).isPrime
  haveI hR : IsLocalization.AtPrime ((Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x)) (kpt x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ (kpt x)
  letI iF : Algebra (Rfin K F) ((Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x)) :=
    ((algebraMap (R2 c0 a i0) _).comp (algebraMap (Rfin K F) (R2 c0 a i0))).toAlgebra
  haveI : IsScalarTower (Rfin K F) (R2 c0 a i0) ((Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hloc := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (M := IsLocalization.localizationLocalizationSubmodule (Submonoid.powers (xcR F c0))
      (Submonoid.powers (plusH c0 a i0)))
    (T := (Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x)) (p := (kpt x).asIdeal)
  have hcomap : (kpt x).asIdeal.comap (algebraMap (Rfin K F) (R2 c0 a i0)) = (ptP (ptR2 c0 a i0 x)).asIdeal := by
    ext b
    rw [Ideal.mem_comap, mem_ptP, ← algebraMap_rfin_R2_apply c0 a i0 x b]
    exact RingHom.mem_ker
  haveI := (ptP (ptR2 c0 a i0 x)).isPrime
  have hsub : (ptP (ptR2 c0 a i0 x)).asIdeal.primeCompl =
      ((kpt x).asIdeal.comap (algebraMap (Rfin K F) (R2 c0 a i0))).primeCompl := by
    ext b
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  haveI : IsLocalization.AtPrime ((Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x)) (ptP (ptR2 c0 a i0 x)).asIdeal := by
    show IsLocalization (ptP (ptR2 c0 a i0 x)).asIdeal.primeCompl _
    rw [hsub]
    exact hloc
  refine ⟨IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Rfin K F)
    (ptP (ptR2 c0 a i0 x)).ne_bot _, fun t ht ht2 => ?_⟩
  have hspan := span_eq_maximalIdeal_of_dedekind (O := (Spec (.of (R2 c0 a i0))).presheaf.stalk (kpt x))
    (mem_ptP.2 ht) ht2
  refine Eq.trans ?_ hspan
  congr 2

instance nonempty_top_R2 [IsDomain (R2 c0 a i0)] : Nonempty (⊤ : (Spec (.of (R2 c0 a i0))).Opens) :=
  ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (R2 c0 a i0)), trivial⟩⟩

/-- **`K`-points of the plus-curve have codimension one.** -/
theorem coheight_kpt_R2 [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K) :
    coheight (kpt x : Spec (.of (R2 c0 a i0))) = 1 := by
  haveI := (dvr_stalk_R2 c0 a i0 x).1
  have h := ringKrullDim_stalk_eq_coheight (kpt x : Spec (.of (R2 c0 a i0)))
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h
  exact_mod_cast h.symm

end R2

end RamanujanPetersson.ThetaSquare


end

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

instance nonempty_top_X0 : Nonempty (⊤ : (X0 K F).Opens) :=
  ⟨⟨Classical.arbitrary (X0 K F), trivial⟩⟩

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

/-- The plus-curve chart map `κ : Spec R2 → X0`. -/
noncomputable def kappa : Spec (.of (R2 c0 a i0)) ⟶ X0 K F :=
  Spec.map (CommRingCat.ofHom (lawMapPlus c0 a i0 : LawRing K F →+* R2 c0 a i0))

theorem jMap_transl (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) :
    (jMap K F (lawMapPlus c0 a i0)).left ≫ (transl (Jac K F) d).left = kappa c0 a i0 ≫ tauX d := by
  rw [tauX, ← Category.assoc]
  rfl

theorem kappa_kpt (x : R2 c0 a i0 →ₐ[K] K) : kappa c0 a i0 (kpt x) = kpt (x.comp (lawMapPlus c0 a i0)) :=
  SpecMap_kpt (lawMapPlus c0 a i0) x

theorem mem_kappa_asIdeal (p : Spec (.of (R2 c0 a i0))) (r : LawRing K F) :
    r ∈ PrimeSpectrum.asIdeal (R := LawRing K F) (kappa c0 a i0 p) ↔
      lawMapPlus c0 a i0 r ∈ PrimeSpectrum.asIdeal (R := R2 c0 a i0) p := Iff.rfl

/-- `κ^* (Nm t) = t · ∏_{i ≠ i0} a_i(t)`. -/
theorem lawMapPlus_normS (t : Rfin K F) :
    lawMapPlus c0 a i0 (awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t)) =
      algebraMap (Rfin K F) (R2 c0 a i0) t *
        algebraMap K (R2 c0 a i0) (∏ i ∈ Finset.univ.erase i0, a i t) := by
  have h1 := AlgHom.congr_fun (lawMapPlus_comp c0 a i0) (normS K (g := genusFK K F) t)
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1
  rw [h1, show plusR c0 a i0 = plusMap (inclR c0) a i0 from rfl, plusMap_normS, map_mul, map_prod, map_prod]
  congr 1

theorem appTop_kappa (r : LawRing K F) :
    (Scheme.ΓSpecIso (.of (R2 c0 a i0))).inv.hom (lawMapPlus c0 a i0 r) =
      (kappa c0 a i0).appTop.hom ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom r) :=
  congrArg (fun f => f.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (lawMapPlus c0 a i0 : LawRing K F →+* R2 c0 a i0)))

/-- Pull-back of a global function of `X0` along `κ`. -/
theorem fpull_kappa [IsDomain (R2 c0 a i0)] (r : LawRing K F) :
    fpull (kappa c0 a i0) ((X0 K F).germToFunctionField ⊤ ((Scheme.ΓSpecIso (.of (LawRing K F))).inv.hom r)) =
      (Spec (.of (R2 c0 a i0))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (.of (R2 c0 a i0))).inv.hom (lawMapPlus c0 a i0 r)) := by
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X0 K F)
    (show kappa c0 a i0 (genericPoint (Spec (.of (R2 c0 a i0)))) ∈ (⊤ : (X0 K F).Opens) from trivial),
    fpull_algebraMap, appTop_kappa]
  exact Scheme.Hom.germ_stalkMap_apply (kappa c0 a i0) ⊤ _ trivial _

variable (hg : 0 < genusFK K F) (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))

end Mult2

end RamanujanPetersson.ThetaSquare


end


