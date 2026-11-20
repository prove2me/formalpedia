-- Prove2me | Definitions.Def_RPLib_F2_015
-- name    : RPLib_F2_015
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T09:30:32.688822+00:00
-- url     : https://prove2.me/theorems/5ae73d32-3256-4eca-864b-da1202ece9ec
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 015 of 70
-- statement:
--   File 015 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Tsen_Zero`: S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property
--   * `S4.Def_RP_JacSymB_Exist`: S4-JacSymB, file H2c': `Sym^g X → Spec k` is universally closed and proper (L12)
--   * `S4.Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
--   * `S4.Def_RP_JacAlg_Defs`: Core B algebra, part 1: the `DegreeData` interface (unit S4-JacAlg, lemma L1)
--   * `S4.Def_RP_PicDescent_E4`: S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`
--   * `S4.Def_RP_JacFrob_Setup`: S4-JacFrob, part Setup: the geometric function field `F-bar = F · k-bar` inside `Ω`
--   * `S4.Def_RP_JacFrob_FF`: S4-JacFrob, part FF: `F-bar = F · k-bar` is a separable function field over `k-bar`
--   * `S4.Def_RP_JacFrob_Sig`: S4-JacFrob, part Sig: `F-bar` as the union of the levels `F_{lev j}`, and the arithmetic Frobenius `σ`
--   * `S4.Def_RP_JacFrob_Phi`: S4-JacFrob, part Phi: the relative (`k-bar`-linear) Frobenius `Φ = σ⁻¹ ∘ (·)^q` of `F-bar`
--   * `S4.Def_RP_JacFrob_SigPl`: S4-JacFrob, part SigPl: `σ_*` on places, divisors and `Pic` of `F-bar / k-bar`
--   * `S4.Def_RP_JacFrob_BrR`: S4-JacFrob, part BrR (bridge 1): the rings of the levels `F_N` inside those of `F-bar`
--   * `S4.Def_RP_JacFrob_BrC`: S4-JacFrob, part BrC (bridge 2): contraction of places of `F-bar` to the levels `F_{lev j}`
--   * `S4.Def_RP_JacFrob_BrO`: S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified
--   * `S4.Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
--   * `S4.Def_RP_DegPoly`: Degree polynomiality (unit S4-DegPoly, lemma L37 of `S4_COREB_ROUTE.md`)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_014

/-!
# Ramanujan-Petersson curve library (flat edition), file 015 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Tsen_Zero`: S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property
* `S4.Def_RP_JacSymB_Exist`: S4-JacSymB, file H2c': `Sym^g X → Spec k` is universally closed and proper (L12)
* `S4.Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
* `S4.Def_RP_JacAlg_Defs`: Core B algebra, part 1: the `DegreeData` interface (unit S4-JacAlg, lemma L1)
* `S4.Def_RP_PicDescent_E4`: S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`
* `S4.Def_RP_JacFrob_Setup`: S4-JacFrob, part Setup: the geometric function field `F-bar = F · k-bar` inside `Ω`
* `S4.Def_RP_JacFrob_FF`: S4-JacFrob, part FF: `F-bar = F · k-bar` is a separable function field over `k-bar`
* `S4.Def_RP_JacFrob_Sig`: S4-JacFrob, part Sig: `F-bar` as the union of the levels `F_{lev j}`, and the arithmetic Frobenius `σ`
* `S4.Def_RP_JacFrob_Phi`: S4-JacFrob, part Phi: the relative (`k-bar`-linear) Frobenius `Φ = σ⁻¹ ∘ (·)^q` of `F-bar`
* `S4.Def_RP_JacFrob_SigPl`: S4-JacFrob, part SigPl: `σ_*` on places, divisors and `Pic` of `F-bar / k-bar`
* `S4.Def_RP_JacFrob_BrR`: S4-JacFrob, part BrR (bridge 1): the rings of the levels `F_N` inside those of `F-bar`
* `S4.Def_RP_JacFrob_BrC`: S4-JacFrob, part BrC (bridge 2): contraction of places of `F-bar` to the levels `F_{lev j}`
* `S4.Def_RP_JacFrob_BrO`: S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified
* `S4.Def_RP_JacFrob_BrD`: S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count
* `S4.Def_RP_DegPoly`: Degree polynomiality (unit S4-DegPoly, lemma L37 of `S4_COREB_ROUTE.md`)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Tsen_Zero =====
section

set_option autoImplicit false

/-!
# S4-PD (1), T1: common zeros over an algebraically closed field; the strong `C₁` property

* `exists_common_zero`: over an algebraically closed field `k`, `m` polynomials in `n > m` variables without constant
  term have a common nonzero zero (Krull's height theorem + the Nullstellensatz).
* `IsC1 K`: every polynomial in `n` variables over `K` with total degree `< n` and constant term `0` has a nonzero zero.
  (`IsC1.exists_zero_of_isHomogeneous`: the classical `C₁` property for forms.)
-/

namespace RamanujanPetersson.Tsen

open MvPolynomial

section Zero

variable {k : Type*} [Field k]

end Zero

/-- The (strong) **`C₁` property**: every polynomial in `n` variables of total degree `< n` without constant term has a
nonzero zero. Over a field it implies the classical `C₁` property for forms (`IsC1.exists_zero_of_isHomogeneous`). -/
def IsC1 (K : Type*) [Field K] : Prop :=
  ∀ (n : ℕ) (f : MvPolynomial (Fin n) K), f.totalDegree < n → constantCoeff f = 0 →
    ∃ x : Fin n → K, x ≠ 0 ∧ eval x f = 0

end RamanujanPetersson.Tsen


end

-- ===== S4.Def_RP_JacSymB_Exist =====
section

/-!
# S4-JacSymB, file H2c': `Sym^g X → Spec k` is universally closed and proper (L12)

Valuative existence: a `K`-point of `Sym^g X` lies in a singleton chart `{c}` (`exists_mem_range_ι_single`); the
ring-level lemma `exists_valuative_lift` moves it to the chart `{d}` where the `O`-point exists. With quasi-compactness
(Cover), separatedness (Sep) and local finite type (Cover) this gives `IsProper (toSpecK k x g)`.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Limits

namespace RamanujanPetersson.JacSym

section ExistScheme

universe u

variable (k : Type u) [Field k] {F : Type u} [Field F] [Algebra k F] (x : F) (g : ℕ) [hx : Fact (Transcendental k x)]

include hx

set_option backward.isDefEq.respectTransparency.types false in
theorem valuativeCriterion_existence_toSpecK [Infinite k] : ValuativeCriterion.Existence (toSpecK k x g) := by
  classical
  rintro ⟨O, K, i₁, i₂, w⟩
  obtain ⟨C, hC⟩ := Infinite.exists_subset_card_eq k (g + 1)
  obtain ⟨c, -, hc⟩ := exists_mem_range_ι_single k x g C (by omega) (i₁ (IsLocalRing.closedPoint K))
  have hrange : Set.range i₁ ⊆
      Set.range (colimit.ι (symDiagram k x g) (op ⟨{c}, Finset.singleton_nonempty c⟩)) := by
    rintro _ ⟨y, rfl⟩
    obtain rfl := Subsingleton.elim y (IsLocalRing.closedPoint K)
    exact hc
  have hoi := isOpenImmersion_ι k x g (op ⟨{c}, Finset.singleton_nonempty c⟩)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (SymRing k (chartRing x {c}) g)),
      ψ ≫ colimit.ι (symDiagram k x g) (op ⟨{c}, Finset.singleton_nonempty c⟩) = i₁ :=
    ⟨@IsOpenImmersion.lift _ _ _ _ _ hoi hrange, @IsOpenImmersion.lift_fac _ _ _ _ _ hoi hrange⟩
  have H : Spec.preimage i₂ ≫ CommRingCat.ofHom (algebraMap O K) =
      CommRingCat.ofHom (algebraMap k (SymRing k (chartRing x {c}) g)) ≫ Spec.preimage ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    calc Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ i₂ = i₁ ≫ toSpecK k x g := w.w.symm
      _ = (ψ ≫ colimit.ι (symDiagram k x g) (op ⟨{c}, Finset.singleton_nonempty c⟩)) ≫ toSpecK k x g :=
          (congrArg (fun f => f ≫ toSpecK k x g) hψ).symm
      _ = ψ ≫ colimit.ι (symDiagram k x g) (op ⟨{c}, Finset.singleton_nonempty c⟩) ≫ toSpecK k x g :=
          Category.assoc _ _ _
      _ = ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (SymRing k (chartRing x {c}) g))) :=
          whisker_eq ψ (ι_toSpecK k x g (op ⟨{c}, Finset.singleton_nonempty c⟩))
  have hμ : ∀ a, algebraMap O K ((Spec.preimage i₂).hom a) =
      (Spec.preimage ψ).hom (algebraMap k (SymRing k (chartRing x {c}) g) a) := fun a => by
    have := congrArg (fun f => f.hom a) H
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using this
  obtain ⟨d, φ', φ'', hφ'c, hφ'', hμ''⟩ :=
    exists_valuative_lift (g := g) hx.out c (Spec.preimage i₂).hom (Spec.preimage ψ).hom hμ
  have hw1 : Spec.map (CommRingCat.ofHom (chartMap x g
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self c {d}))).toRingHom) ≫
      colimit.ι (symDiagram k x g) (op ⟨{c}, Finset.singleton_nonempty c⟩) =
      colimit.ι (symDiagram k x g) (op ⟨{c, d}, Finset.insert_nonempty c {d}⟩) :=
    colimit.w (symDiagram k x g) (homOfLE (show (⟨{c}, Finset.singleton_nonempty c⟩ : ChartIdx k) ≤
      ⟨{c, d}, Finset.insert_nonempty c {d}⟩ from Finset.singleton_subset_iff.mpr (Finset.mem_insert_self c {d}))).op
  have hw2 : Spec.map (CommRingCat.ofHom (chartMap x g (Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self d)))).toRingHom) ≫
      colimit.ι (symDiagram k x g) (op ⟨{d}, Finset.singleton_nonempty d⟩) =
      colimit.ι (symDiagram k x g) (op ⟨{c, d}, Finset.insert_nonempty c {d}⟩) :=
    colimit.w (symDiagram k x g) (homOfLE (show (⟨{d}, Finset.singleton_nonempty d⟩ : ChartIdx k) ≤
      ⟨{c, d}, Finset.insert_nonempty c {d}⟩ from
        Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self d)))).op
  have e1 : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ Spec.map (CommRingCat.ofHom φ'') =
      Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom (chartMap x g (Finset.singleton_subset_iff.mpr
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self d)))).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hφ'']
  have e2 : Spec.map (CommRingCat.ofHom φ') ≫ Spec.map (CommRingCat.ofHom (chartMap x g
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self c {d}))).toRingHom) = ψ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ'c, CommRingCat.ofHom_hom, Spec.map_preimage]
  refine ⟨⟨Spec.map (CommRingCat.ofHom φ'') ≫ colimit.ι (symDiagram k x g) (op ⟨{d}, Finset.singleton_nonempty d⟩),
    ?_, ?_⟩⟩
  · calc Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ Spec.map (CommRingCat.ofHom φ'') ≫
          colimit.ι (symDiagram k x g) (op ⟨{d}, Finset.singleton_nonempty d⟩)
        = (Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ Spec.map (CommRingCat.ofHom φ'')) ≫
          colimit.ι (symDiagram k x g) (op ⟨{d}, Finset.singleton_nonempty d⟩) := (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom φ') ≫
          colimit.ι (symDiagram k x g) (op ⟨{c, d}, Finset.insert_nonempty c {d}⟩) := by
          rw [e1, Category.assoc, hw2]
      _ = ψ ≫ colimit.ι (symDiagram k x g) (op ⟨{c}, Finset.singleton_nonempty c⟩) := by
          rw [← hw1, ← Category.assoc, e2]
      _ = i₁ := hψ
  · calc (Spec.map (CommRingCat.ofHom φ'') ≫ colimit.ι (symDiagram k x g) (op ⟨{d}, Finset.singleton_nonempty d⟩)) ≫
          toSpecK k x g
        = Spec.map (CommRingCat.ofHom φ'') ≫ colimit.ι (symDiagram k x g) (op ⟨{d}, Finset.singleton_nonempty d⟩) ≫
          toSpecK k x g := Category.assoc _ _ _
      _ = Spec.map (CommRingCat.ofHom φ'') ≫
          Spec.map (CommRingCat.ofHom (algebraMap k (SymRing k (chartRing x {d}) g))) :=
          whisker_eq _ (ι_toSpecK k x g (op ⟨{d}, Finset.singleton_nonempty d⟩))
      _ = i₂ := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hμ'', CommRingCat.ofHom_hom, Spec.map_preimage]

set_option backward.isDefEq.respectTransparency.types false in
instance universallyClosed_toSpecK [Infinite k] : UniversallyClosed (toSpecK k x g) :=
  UniversallyClosed.of_valuativeCriterion _ (valuativeCriterion_existence_toSpecK k x g)

set_option backward.isDefEq.respectTransparency.types false in
/-- **L12**: `Sym^g X → Spec k` is proper. -/
instance isProper_toSpecK [Infinite k] [FiniteDimensional (IntermediateField.adjoin k {x}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k {x}) F] : IsProper (toSpecK k x g) where

end ExistScheme

end RamanujanPetersson.JacSym


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

/-- Every place is finite on some chart synonym `SynF K F c`. -/
theorem exists_inl (Q : Place K F) :
    ∃ c : K, ∃ P : HeightOneSpectrum (Rfin K (SynF K F c)), synPlace c Q = Sum.inl P := by
  have key : ∀ c : K, 1 ≤ placeVal Q (algebraMap K[X] F X - algebraMap K F c) →
      ∃ P : HeightOneSpectrum (Rfin K (SynF K F c)), synPlace c Q = Sum.inl P := by
    intro c hc
    rcases h : synPlace c Q with P | Q'
    · exact ⟨P, rfl⟩
    · exfalso
      have h1 := one_lt_placeVal_inr_x (K := K) (F := SynF K F c) Q'
      rw [synAlg_X, ← h, placeVal_synPlace, JacSym.uc, map_inv₀] at h1
      have hne : placeVal Q (algebraMap K[X] F X - algebraMap K F c) ≠ 0 :=
        ne_of_gt (lt_of_lt_of_le zero_lt_one hc)
      have h2 := le_mul_of_one_le_left' (b := placeVal Q (algebraMap K[X] F X - algebraMap K F c))
        (a := (placeVal Q (algebraMap K[X] F X - algebraMap K F c))⁻¹) hc
      rw [mul_inv_cancel₀ hne] at h2
      exact absurd h1 (not_lt.2 h2)
  by_cases hx : 1 ≤ placeVal Q (algebraMap K[X] F X)
  · exact ⟨0, key 0 (by rw [map_zero, sub_zero]; exact hx)⟩
  · refine ⟨1, key 1 ?_⟩
    have hlt : placeVal Q (algebraMap K[X] F X) < placeVal Q (algebraMap K F 1) := by
      rw [map_one, Valuation.map_one]; exact lt_of_not_ge hx
    rw [Valuation.map_sub_eq_of_lt_right _ hlt, map_one, Valuation.map_one]

/-- Every place is the center `plc c ψ` of a `K`-point of a one-point chart. -/
theorem exists_plc (Q : Place K F) :
    ∃ c : K, ∃ ψ : chartRing (algebraMap K[X] F X) {c} →ₐ[K] K, plc c ψ = Q := by
  obtain ⟨c, P, hP⟩ := exists_inl Q
  obtain ⟨φ, hφ⟩ := exists_ptP P
  refine ⟨c, φ.comp (rfinG c).toAlgHom, ?_⟩
  have e : ptSyn c (φ.comp (rfinG c).toAlgHom) = φ := by
    ext y
    simp [ptSyn]
  rw [plc, e, hφ, ← hP, Equiv.symm_apply_apply]

/-- Every place is the center of a `K`-point of a chart `Spec Sym¹ B_A` of `X1`. -/
theorem exists_chartPt (Q : Place K F) : ∃ A : (ChartIdx K)ᵒᵖ,
    ∃ ψ : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1 →ₐ[K] K, plA A.unop (ψ.comp diag1) = Q := by
  obtain ⟨c, θ, hθ⟩ := exists_plc Q
  refine ⟨op ⟨{c}, Finset.singleton_nonempty c⟩, symPt (fun _ => θ), ?_⟩
  have e : (symPt (k := K) (B := chartRing (algebraMap K[X] F X) {c}) (fun _ : Fin 1 => θ)).comp diag1 = θ :=
    AlgHom.ext fun b => by
      show ptOf (fun _ : Fin 1 => θ) (inc 0 b) = θ b
      exact DFunLike.congr_fun (ptOf_inc (fun _ : Fin 1 => θ) 0) b
  rw [e]
  exact plA_eq_of_isCenter _ (hθ ▸ isCenter_plc c θ)

variable (P0 : Place K F)

instance isProper_PP (n : ℕ) : IsProper (PP K F n).hom := by
  induction n with
  | zero =>
    show IsProper (𝟙 (Spec (.of K)))
    infer_instance
  | succ n ih =>
    haveI : IsProper (toSpecK K (algebraMap K[X] F X) 1) := inferInstance
    show IsProper (pullback.fst (PP K F n).hom (toSpecK K (algebraMap K[X] F X) 1) ≫ (PP K F n).hom)
    infer_instance

end Proper

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_JacAlg_Defs =====
section

/-!
# Core B algebra, part 1: the `DegreeData` interface (unit S4-JacAlg, lemma L1)

`A` is an abelian group (in the application `Pic⁰(X̄) = J(F̄_q)`), `π` an additive endomorphism of `A`
(the arithmetic Frobenius) and `deg F` the degree of the endomorphism `F(π_J)` of the Jacobian, for
`F ∈ ℤ[X]`. The fields are (D1)-(D3) of `S4_COREB_ROUTE.md` (reduction F1):
* (D1) `deg` is multiplicative with `deg 1 = 1`;
* (D2) `deg (n • F + G)` is a polynomial in `n ∈ ℤ` of degree `≤ 2g`, and `deg n = n ^ (2g)`;
* (D3) `deg F = 0` iff `Ker F(π)` is infinite, and `deg F = #Ker F(π)` when `p ∤ F(0)`.
Every geometric Core B unit delivers exactly this structure.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlg

open Polynomial

namespace DegreeData

variable {A : Type*} [AddCommGroup A] {π : Module.End ℤ A} {g p : ℕ} (D : DegreeData π g p)

theorem deg_intCast (n : ℤ) : D.deg (n : ℤ[X]) = n.natAbs ^ (2 * g) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast, D.deg_natCast, Int.natAbs_natCast]
  · rw [Int.cast_neg, Int.cast_natCast, D.deg_neg, D.deg_natCast, Int.natAbs_neg,
      Int.natAbs_natCast]

theorem deg_C_mul (c : ℤ) (F : ℤ[X]) : D.deg (C c * F) = c.natAbs ^ (2 * g) * D.deg F := by
  rw [show (C c : ℤ[X]) = (c : ℤ[X]) from by simpa using C_eq_intCast (R := ℤ) c,
    D.deg_mul, D.deg_intCast]

theorem polyOf_eval (F G : ℤ[X]) (n : ℤ) :
    (D.polyOf F G).eval (n : ℚ) = (D.deg (n • F + G) : ℚ) :=
  ((Classical.choose_spec (D.deg_poly F G)).2 n).symm

/-- `P_π` (Milne 10.9): the polynomial with `P_π(n) = deg(n - π)` for every `n : ℤ`. -/
noncomputable def charPoly : ℚ[X] := D.polyOf 1 (-X)

theorem charPoly_eval (n : ℤ) : D.charPoly.eval (n : ℚ) = (D.deg ((n : ℤ[X]) - X) : ℚ) := by
  rw [charPoly, polyOf_eval, zsmul_one, sub_eq_add_neg]

theorem charPoly_natDegree_le : D.charPoly.natDegree ≤ 2 * g := D.polyOf_natDegree_le _ _

theorem mem_ker_natCast (n : ℕ) (x : A) :
    x ∈ LinearMap.ker (aeval π (n : ℤ[X])) ↔ n • x = 0 := by
  simp [map_natCast]

include D in
/-- (D2) + (D3): `#A[n] = n ^ (2g)` for `p ∤ n` (first half of A1). -/
theorem card_ker_natCast (n : ℕ) (hn : ¬ (p : ℤ) ∣ n) :
    Nat.card (LinearMap.ker (aeval π (n : ℤ[X]))) = n ^ (2 * g) := by
  rw [← D.deg_eq_card_ker _ (by simpa using hn), D.deg_natCast]

/-- `deg F ≠ 0` iff `Ker F(π)` is finite. -/
theorem deg_ne_zero_iff (F : ℤ[X]) :
    D.deg F ≠ 0 ↔ (LinearMap.ker (aeval π F) : Set A).Finite := by
  rw [Ne, D.deg_eq_zero_iff, Set.not_infinite]

/-- `deg π ≠ 0` when `π` is injective on `A` (so the roots of `P_π` are nonzero). -/
theorem deg_X_ne_zero (hπ : Function.Injective π) : D.deg X ≠ 0 := by
  rw [D.deg_ne_zero_iff, aeval_X]
  have : (LinearMap.ker π : Set A) = {0} := by
    rw [LinearMap.ker_eq_bot.mpr hπ]; simp
  rw [this]; exact Set.finite_singleton 0

end DegreeData

end RamanujanPetersson.JacAlg


end

-- ===== S4.Def_RP_PicDescent_E4 =====
section

/-!
# S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`

For a function field `F / Fq` with full constant field `K = constField Fq F` (`#K = q ^ d`, `d = [K : Fq]`,
`card_constField`), `F` is rebased as a function field over `K` with the same separating element `x`:
* instances `Algebra K[X] F` (`x ↦ xF Fq F`), `Algebra (RatFunc K) F`, the towers, `FunctionField K F`,
  `Algebra.IsSeparable (RatFunc K) F`; `xF_constField : xF K F = xF Fq F`;
* `constField_K : constField K F = ⊥` (`F / K` is geometrically connected),
  `exists_deg_one_K` (F. K. Schmidt over `K`), `finite_Pic0_K`;
so parts A–E apply over `K` with `q ^ d` in place of `q`; the `K`-Frobenius is `π ^ d` (`mem_Lc_K`).
Restated over `K`: `picBarEquivK`, `pic0BarEquivK`, `picBaseEquivK`, `pic0BaseEquivK`, `classNumber_barK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Rebase

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

noncomputable instance decEq_ratK : DecidableEq (RatFunc (constField Fq F)) := Classical.decEq _

/-- `K[X] → F`, `X ↦ x`. -/
noncomputable instance algebra_polyK : Algebra (constField Fq F)[X] F :=
  (aeval (RR.xF Fq F)).toRingHom.toAlgebra

theorem algebraMap_polyK (p : (constField Fq F)[X]) :
    algebraMap (constField Fq F)[X] F p = aeval (RR.xF Fq F) p := rfl

instance isScalarTower_polyK : IsScalarTower (constField Fq F) (constField Fq F)[X] F :=
  IsScalarTower.of_algebraMap_eq fun a => (aeval_C (RR.xF Fq F) a).symm

section Descent

-- `Algebra K Ω` and `IsScalarTower K F Ω` are Mathlib's intermediate-field instances (through `F`).
variable {Ω : Type*} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]

end Descent

end Rebase

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_JacFrob_Setup =====
section

/-!
# S4-JacFrob, part Setup: the geometric function field `F-bar = F · k-bar` inside `Ω`

`kbar = algebraicClosure Fq Ω` (an algebraic closure of `Fq`), `Fbar = F(kbar)` inside `Ω`, with the algebra
structures over `kbar`, `kbar[X]` and `RatFunc kbar` (`X ↦ x`) needed by `JacComplete.Jac kbar Fbar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial RamanujanPetersson.PicDescent

section Setup

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]

/-- `k-bar`: the algebraic closure of `Fq` inside `Ω`. -/
noncomputable abbrev kbar : IntermediateField Fq Ω := algebraicClosure Fq Ω

instance isAlgClosed_kbar [IsAlgClosed Ω] : IsAlgClosed (kbar Fq Ω) := IsAlgClosure.isAlgClosed Fq

/-- `F-bar = F · k-bar` inside `Ω`. -/
noncomputable def Fbar : IntermediateField F Ω := IntermediateField.adjoin F (kbar Fq Ω : Set Ω)

variable {Fq F Ω} in
theorem mem_Fbar_of_mem_kbar {x : Ω} (hx : x ∈ kbar Fq Ω) : x ∈ Fbar Fq F Ω :=
  IntermediateField.subset_adjoin F _ hx

/-- The inclusion `k-bar → F-bar`. -/
noncomputable def KtoF : kbar Fq Ω →+* Fbar Fq F Ω where
  toFun x := ⟨x, mem_Fbar_of_mem_kbar x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance algebra_kF : Algebra (kbar Fq Ω) (Fbar Fq F Ω) := (KtoF Fq F Ω).toAlgebra

theorem coe_algebraMap_kF (x : kbar Fq Ω) :
    ((algebraMap (kbar Fq Ω) (Fbar Fq F Ω) x : Fbar Fq F Ω) : Ω) = x := rfl

instance isScalarTower_kF : IsScalarTower Fq (kbar Fq Ω) (Fbar Fq F Ω) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

section FF

variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The separating element `x` of `F`, inside `F-bar`. -/
noncomputable def xbar : Fbar Fq F Ω := algebraMap F (Fbar Fq F Ω) (RR.xF Fq F)

noncomputable instance algebra_polyK : Algebra (kbar Fq Ω)[X] (Fbar Fq F Ω) :=
  (aeval (xbar Fq F Ω)).toRingHom.toAlgebra

theorem algebraMap_polyK (p : (kbar Fq Ω)[X]) :
    algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) p = aeval (xbar Fq F Ω) p := rfl

instance isScalarTower_polyK : IsScalarTower (kbar Fq Ω) (kbar Fq Ω)[X] (Fbar Fq F Ω) :=
  IsScalarTower.of_algebraMap_eq fun a => (aeval_C (xbar Fq F Ω) a).symm

theorem transcendental_xbar : Transcendental (kbar Fq Ω) (xbar Fq F Ω) := by
  have h1 : Transcendental Fq (xbar Fq F Ω) := by
    rw [xbar, transcendental_algebraMap_iff (algebraMap F (Fbar Fq F Ω)).injective]
    exact transcendental_xF Fq F
  exact h1.extendScalars (kbar Fq Ω)

theorem aeval_xbar_injective : Function.Injective (aeval (R := kbar Fq Ω) (xbar Fq F Ω)) :=
  transcendental_iff_injective.1 (transcendental_xbar Fq F Ω)

noncomputable instance algebra_ratK : Algebra (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) :=
  (RatFunc.liftAlgHom (aeval (xbar Fq F Ω))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (aeval_xbar_injective Fq F Ω))).toRingHom.toAlgebra

theorem algebraMap_ratK (g : RatFunc (kbar Fq Ω)) :
    algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) g = RatFunc.liftAlgHom (aeval (xbar Fq F Ω))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_xbar_injective Fq F Ω)) g :=
  rfl

instance isScalarTower_ratK :
    IsScalarTower (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [algebraMap_ratK, ← div_one (algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) p),
      ← map_one (algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω))), RatFunc.liftAlgHom_apply_div,
      map_one, div_one, algebraMap_polyK]

noncomputable instance decEq_ratK : DecidableEq (RatFunc (kbar Fq Ω)) := Classical.decEq _

theorem hx_Fbar : algebraMap F (Fbar Fq F Ω) (RR.xF Fq F) = RR.xF (kbar Fq Ω) (Fbar Fq F Ω) := by
  show xbar Fq F Ω = algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) X
  rw [algebraMap_polyK, aeval_X]

end FF

end Setup

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_FF =====
section

/-!
# S4-JacFrob, part FF: `F-bar = F · k-bar` is a separable function field over `k-bar`

* `ratK : Fq(x) →+* kbar(x)` and `compatK`: the maps `Fq(x) → kbar(x) → F-bar` and `Fq(x) → F → F-bar` agree.
* `aeval_map_ratK`, `isIntegral_img`, `isSeparable_img`: images of elements of `F` are integral and separable
  over `kbar(x)`.
* `adjoin_bimg_eq_top`: the images of an `Fq(x)`-basis of `F` generate `F-bar` as a `kbar(x)`-algebra.
* instances `functionField_Fbar : FunctionField kbar Fbar` and `isSeparable_Fbar`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial RamanujanPetersson.PicDescent

section FF

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

instance isScalarTower_FqFFbar : IsScalarTower Fq F (Fbar Fq F Ω) :=
  IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (IsScalarTower.algebraMap_apply Fq F Ω a)

/-- The ring map `Fq(x) → kbar(x)`. -/
noncomputable def ratK : RatFunc Fq →+* RatFunc (kbar Fq Ω) :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap Fq (kbar Fq Ω)))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap Fq (kbar Fq Ω)).injective))

theorem ratK_div (p d : Fq[X]) :
    ratK Fq Ω (algebraMap Fq[X] (RatFunc Fq) p / algebraMap Fq[X] (RatFunc Fq) d) =
      algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (p.map (algebraMap Fq (kbar Fq Ω))) /
        algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (d.map (algebraMap Fq (kbar Fq Ω))) :=
  RatFunc.map_apply_div _ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ (algebraMap Fq (kbar Fq Ω)).injective)) p d

theorem ratK_algebraMap (p : Fq[X]) :
    ratK Fq Ω (algebraMap Fq[X] (RatFunc Fq) p) =
      algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (p.map (algebraMap Fq (kbar Fq Ω))) := by
  have h := ratK_div Fq Ω p 1
  rwa [map_one, div_one, Polynomial.map_one, map_one, div_one] at h

theorem compatK_poly_hom :
    (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)).comp (mapRingHom (algebraMap Fq (kbar Fq Ω))) =
      (algebraMap F (Fbar Fq F Ω)).comp (algebraMap Fq[X] F) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have e1 : algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) (C (algebraMap Fq (kbar Fq Ω) a)) =
        algebraMap Fq (Fbar Fq F Ω) a := by
      rw [IsScalarTower.algebraMap_apply Fq (kbar Fq Ω) (Fbar Fq F Ω)]
      exact (IsScalarTower.algebraMap_apply (kbar Fq Ω) (kbar Fq Ω)[X] (Fbar Fq F Ω) _).symm
    have e2 : algebraMap Fq[X] F (C a) = algebraMap Fq F a :=
      (IsScalarTower.algebraMap_apply Fq Fq[X] F a).symm
    simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C]
    rw [e1, e2, ← IsScalarTower.algebraMap_apply Fq F (Fbar Fq F Ω)]
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]
    exact (hx_Fbar Fq F Ω).symm

theorem compatK_hom :
    (algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)).comp (ratK Fq Ω) =
      (algebraMap F (Fbar Fq F Ω)).comp (algebraMap (RatFunc Fq) F) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors Fq[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [ratK_algebraMap,
    ← IsScalarTower.algebraMap_apply (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω),
    ← IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) F]
  exact RingHom.congr_fun (compatK_poly_hom Fq F Ω) p

theorem compatK (g : RatFunc Fq) :
    algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) (ratK Fq Ω g) =
      algebraMap F (Fbar Fq F Ω) (algebraMap (RatFunc Fq) F g) :=
  RingHom.congr_fun (compatK_hom Fq F Ω) g

theorem aeval_map_ratK (p : (RatFunc Fq)[X]) (f : F) :
    aeval (algebraMap F (Fbar Fq F Ω) f) (p.map (ratK Fq Ω)) =
      algebraMap F (Fbar Fq F Ω) (aeval f p) := by
  rw [aeval_def, eval₂_map, compatK_hom, aeval_def, hom_eval₂]

theorem isIntegral_img (f : F) :
    IsIntegral (RatFunc (kbar Fq Ω)) (algebraMap F (Fbar Fq F Ω) f) := by
  have hf : IsIntegral (RatFunc Fq) f := Algebra.IsIntegral.isIntegral f
  refine ⟨(minpoly (RatFunc Fq) f).map (ratK Fq Ω), (minpoly.monic hf).map _, ?_⟩
  rw [← aeval_def, aeval_map_ratK, minpoly.aeval, map_zero]

theorem isSeparable_img (f : F) :
    IsSeparable (RatFunc (kbar Fq Ω)) (algebraMap F (Fbar Fq F Ω) f) := by
  have hs : (minpoly (RatFunc Fq) f).Separable := Algebra.IsSeparable.isSeparable (RatFunc Fq) f
  refine (hs.map (f := ratK Fq Ω)).of_dvd (minpoly.dvd _ _ ?_)
  rw [aeval_map_ratK, minpoly.aeval, map_zero]

/-- The images in `F-bar` of the standard `Fq(x)`-basis of `F`. -/
noncomputable abbrev bimg : Set (Fbar Fq F Ω) :=
  Set.range (fun j => algebraMap F (Fbar Fq F Ω) (Module.finBasis (RatFunc Fq) F j))

theorem img_mem_adjoin (f : F) :
    algebraMap F (Fbar Fq F Ω) f ∈ Algebra.adjoin (RatFunc (kbar Fq Ω)) (bimg Fq F Ω) := by
  rw [← (Module.finBasis (RatFunc Fq) F).sum_repr f, map_sum]
  refine Subalgebra.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def, map_mul, ← compatK Fq F Ω]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Algebra.subset_adjoin (Set.mem_range_self j))

theorem adjoin_bimg_eq_top : Algebra.adjoin (RatFunc (kbar Fq Ω)) (bimg Fq F Ω) = ⊤ := by
  have hsub : ∀ y, y ∈ Algebra.adjoin F (kbar Fq Ω : Set Ω) → y ∈ Fbar Fq F Ω :=
    fun y hy => IntermediateField.algebra_adjoin_le_adjoin (F := F) (S := (kbar Fq Ω : Set Ω)) hy
  have hall : ∀ y (hy : y ∈ Algebra.adjoin F (kbar Fq Ω : Set Ω)),
      (⟨y, hsub y hy⟩ : Fbar Fq F Ω) ∈ Algebra.adjoin (RatFunc (kbar Fq Ω)) (bimg Fq F Ω) := by
    intro y hy
    refine Algebra.adjoin_induction (p := fun y hy => (⟨y, hsub y hy⟩ : Fbar Fq F Ω) ∈
      Algebra.adjoin (RatFunc (kbar Fq Ω)) (bimg Fq F Ω)) (fun x hx => ?_) (fun f => ?_)
      (fun x y _ _ hx hy => Subalgebra.add_mem _ hx hy)
      (fun x y _ _ hx hy => Subalgebra.mul_mem _ hx hy) hy
    · have e : (⟨x, hsub x (Algebra.subset_adjoin hx)⟩ : Fbar Fq F Ω) =
          algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)
            (algebraMap (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (C ⟨x, hx⟩)) := by
        rw [← IsScalarTower.algebraMap_apply, algebraMap_polyK, aeval_C]
        rfl
      rw [e]
      exact Subalgebra.algebraMap_mem _ _
    · exact img_mem_adjoin Fq F Ω f
  refine Algebra.eq_top_iff.2 fun z => ?_
  have hz : (z : Ω) ∈ Algebra.adjoin F (kbar Fq Ω : Set Ω) := by
    have h := IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (F := F)
      (S := (kbar Fq Ω : Set Ω))
      (fun x hx => ((mem_algebraicClosure_iff'.1 hx).tower_top (A := F)).isAlgebraic)
    rw [← h]
    exact z.2
  exact hall z hz

instance functionField_Fbar : FunctionField (kbar Fq Ω) (Fbar Fq F Ω) := by
  have hint : ∀ x ∈ bimg Fq F Ω, IsIntegral (RatFunc (kbar Fq Ω)) x := by
    rintro _ ⟨j, rfl⟩
    exact isIntegral_img Fq F Ω _
  have h := fg_adjoin_of_finite (s := bimg Fq F Ω) (Set.finite_range _) hint
  rw [adjoin_bimg_eq_top, Algebra.top_toSubmodule] at h
  exact ⟨h⟩

instance isSeparable_Fbar : Algebra.IsSeparable (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) := by
  refine (separableClosure.eq_top_iff _ _).1 (IntermediateField.toSubalgebra_injective ?_)
  rw [IntermediateField.top_toSubalgebra, eq_top_iff, ← adjoin_bimg_eq_top Fq F Ω]
  exact Algebra.adjoin_le (by
    rintro _ ⟨j, rfl⟩
    exact mem_separableClosure_iff.2 (isSeparable_img Fq F Ω _))

end FF

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Sig =====
section

/-!
# S4-JacFrob, part Sig: `F-bar` as the union of the levels `F_{lev j}`, and the arithmetic Frobenius `σ`

* `Lc_le_kbar`, `Fc_le_Fbar`, `exists_lev_of_mem_kbar`, `exists_lev_of_mem_Fbar`: `k-bar = ⋃ L_{lev j}` and
  `F-bar = ⋃ F_{lev j}`; `Kc j` (the level `F_{lev j}` as an `F`-subalgebra of `Ω`) is directed, and
  `Kc i ≤ Kc j → i ≤ j` (degrees).
* `sig : F-bar ≃ₐ[F] F-bar`, glued from the level Frobenii `frobF` (`Subalgebra.iSupLift`):
  `coe_sig_of_mem` (on `F_{lev j}` it is `frobF` of that level) and `sig_algebraMap_kbar` (`c ↦ c ^ q` on `k-bar`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial RamanujanPetersson.PicDescent Places

section Lev

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]

theorem Lc_le_kbar (n : ℕ) [NeZero n] : Lc Fq Ω n ≤ kbar Fq Ω := fun _ hx =>
  mem_algebraicClosure_iff'.2 (isSeparable_of_mem_Lc hx).isIntegral

theorem Fc_le_Fbar (n : ℕ) [NeZero n] : Fc Fq F Ω n ≤ Fbar Fq F Ω :=
  IntermediateField.adjoin_le_iff.2 fun _ hx => mem_Fbar_of_mem_kbar (Lc_le_kbar Fq Ω n hx)

variable {Fq Ω} in
theorem exists_lev_of_mem_kbar {x : Ω} (hx : x ∈ kbar Fq Ω) : ∃ j, x ∈ Lc Fq Ω (lev j) := by
  have hint : IsIntegral Fq x := mem_algebraicClosure_iff'.1 hx
  have : FiniteDimensional Fq (IntermediateField.adjoin Fq {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin Fq {x}) := Module.finite_of_finite Fq
  letI : Fintype (IntermediateField.adjoin Fq {x}) := Fintype.ofFinite _
  have hd : 0 < Module.finrank Fq (IntermediateField.adjoin Fq {x}) := Module.finrank_pos
  have h := congrArg Subtype.val (FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self Fq x⟩ : IntermediateField.adjoin Fq {x}))
  rw [SubmonoidClass.coe_pow, Module.card_eq_pow_finrank (K := Fq)] at h
  exact ⟨_, Lc_le (Nat.dvd_factorial hd (Nat.le_succ _)) (mem_Lc.2 h)⟩

theorem Fbar_toSubalgebra :
    (Fbar Fq F Ω).toSubalgebra = Algebra.adjoin F (kbar Fq Ω : Set Ω) :=
  IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
    (fun _ hx => ((mem_algebraicClosure_iff'.1 hx).tower_top (A := F)).isAlgebraic)

/-- The level `F_{lev j}` as an `F`-subalgebra of `Ω`. -/
noncomputable abbrev Kc (j : ℕ) : Subalgebra F Ω := (Fc Fq F Ω (lev j)).toSubalgebra

theorem lev_dvd_lev {i j : ℕ} (h : i ≤ j) : lev i ∣ lev j :=
  Nat.factorial_dvd_factorial (Nat.succ_le_succ h)

theorem dir_Kc : Directed (· ≤ ·) (Kc Fq F Ω) :=
  Monotone.directed_le fun _ _ h _ hx => Fc_le (lev_dvd_lev h) hx

theorem Fbar_le_iSup : (Fbar Fq F Ω).toSubalgebra ≤ ⨆ j, Kc Fq F Ω j := by
  rw [Fbar_toSubalgebra]
  refine Algebra.adjoin_le fun x hx => ?_
  obtain ⟨j, hj⟩ := exists_lev_of_mem_kbar hx
  exact le_iSup (Kc Fq F Ω) j (mem_Fc_of_mem_Lc hj)

variable {Fq F Ω} in
theorem exists_lev_of_mem_Fbar {y : Ω} (hy : y ∈ Fbar Fq F Ω) : ∃ j, y ∈ Fc Fq F Ω (lev j) := by
  have h := Fbar_le_iSup Fq F Ω hy
  rw [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed (dir_Kc Fq F Ω), Set.mem_iUnion] at h
  exact h

end Lev

section Sig

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : constField Fq F = ⊥)

include hk in
theorem le_of_Kc_le {i j : ℕ} (h : Kc Fq F Ω i ≤ Kc Fq F Ω j) : i ≤ j := by
  have hr : ∀ N [NeZero N], Module.finrank F (Fc Fq F Ω N) = N := fun N _ => by
    rw [finrank_Fc Fq F Ω hk N, finrank_Lc Fq Ω (NeZero.ne N)]
  have : FiniteDimensional F (Fc Fq F Ω (lev j)) :=
    Module.finite_of_finrank_pos (by rw [hr]; exact Nat.pos_of_ne_zero (NeZero.ne _))
  have h2 := IntermediateField.finrank_le_of_le_right
    (show Fc Fq F Ω (lev i) ≤ Fc Fq F Ω (lev j) from fun _ hx => h hx)
  rw [hr, hr] at h2
  by_contra hlt
  exact absurd h2 (not_le.2 ((Nat.factorial_lt (Nat.succ_pos j)).2 (Nat.succ_lt_succ (not_le.1 hlt))))

/-- The level-`lev j` Frobenius as an `F`-algebra map `F_{lev j} → Ω`. -/
noncomputable def frobLev (j : ℕ) : Kc Fq F Ω j →ₐ[F] Ω :=
  (Fc Fq F Ω (lev j)).val.comp (frobF (isConstExt_Fc Fq F Ω hk (lev j))).toAlgHom

theorem frobLev_apply (j : ℕ) (y : Fc Fq F Ω (lev j)) :
    frobLev Fq F Ω hk j y = (frobF (isConstExt_Fc Fq F Ω hk (lev j)) y : Ω) := rfl

theorem frobLev_coe (j : ℕ) {c : Ω} (hc : c ∈ Lc Fq Ω (lev j)) :
    frobLev Fq F Ω hk j ⟨c, mem_Fc_of_mem_Lc hc⟩ = c ^ Fintype.card Fq := by
  show ((frobF (isConstExt_Fc Fq F Ω hk (lev j))
    (algebraMap (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) ⟨c, hc⟩) : Fc Fq F Ω (lev j)) : Ω) = _
  rw [frobF_algebraMap_L, coe_algebraMap_LF, frobL, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    SubmonoidClass.coe_pow]

theorem frobLev_compat (i j : ℕ) (h : Kc Fq F Ω i ≤ Kc Fq F Ω j) :
    frobLev Fq F Ω hk i = (frobLev Fq F Ω hk j).comp (Subalgebra.inclusion h) := by
  have hij : lev i ∣ lev j := lev_dvd_lev (le_of_Kc_le Fq F Ω hk h)
  refine AlgHom.coe_ringHom_injective (ringHom_ext_of_constExt (isConstExt_Fc Fq F Ω hk (lev i))
    (fun a => ?_) (fun l => ?_))
  · exact ((frobLev Fq F Ω hk i).commutes a).trans
      (((frobLev Fq F Ω hk j).comp (Subalgebra.inclusion h)).commutes a).symm
  · have e1 : (frobLev Fq F Ω hk i : Kc Fq F Ω i →+* Ω)
        (algebraMap (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i)) l) = (l : Ω) ^ Fintype.card Fq :=
      frobLev_coe Fq F Ω hk i l.2
    have e2 : ((frobLev Fq F Ω hk j).comp (Subalgebra.inclusion h) : Kc Fq F Ω i →+* Ω)
        (algebraMap (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i)) l) = (l : Ω) ^ Fintype.card Fq :=
      frobLev_coe Fq F Ω hk j (Lc_le hij l.2)
    exact e1.trans e2.symm

/-- The glued Frobenius `F-bar → Ω`. -/
noncomputable def sig0 : (Fbar Fq F Ω).toSubalgebra →ₐ[F] Ω :=
  Subalgebra.iSupLift (Kc Fq F Ω) (dir_Kc Fq F Ω) (frobLev Fq F Ω hk) (frobLev_compat Fq F Ω hk) _
    (Fbar_le_iSup Fq F Ω)

theorem sig0_of_mem (y : (Fbar Fq F Ω).toSubalgebra) {j : ℕ} (hy : (y : Ω) ∈ Kc Fq F Ω j) :
    sig0 Fq F Ω hk y = frobLev Fq F Ω hk j ⟨y, hy⟩ :=
  Subalgebra.iSupLift_of_mem (Kc Fq F Ω) y hy

theorem sig0_mem (y : (Fbar Fq F Ω).toSubalgebra) : sig0 Fq F Ω hk y ∈ (Fbar Fq F Ω).toSubalgebra := by
  obtain ⟨j, hj⟩ := exists_lev_of_mem_Fbar y.2
  rw [sig0_of_mem Fq F Ω hk y hj]
  exact Fc_le_Fbar Fq F Ω (lev j) (frobF (isConstExt_Fc Fq F Ω hk (lev j)) ⟨y, hj⟩).2

/-- `σ` as an `F`-algebra endomorphism of `F-bar`. -/
noncomputable def sig1 : Fbar Fq F Ω →ₐ[F] Fbar Fq F Ω :=
  (sig0 Fq F Ω hk).codRestrict (Fbar Fq F Ω).toSubalgebra (sig0_mem Fq F Ω hk)

theorem sig1_surjective : Function.Surjective (sig1 Fq F Ω hk) := by
  intro z
  obtain ⟨j, hj⟩ := exists_lev_of_mem_Fbar z.2
  let w := (frobF (isConstExt_Fc Fq F Ω hk (lev j))).symm ⟨z, hj⟩
  refine ⟨⟨w, Fc_le_Fbar Fq F Ω (lev j) w.2⟩, Subtype.ext ?_⟩
  show sig0 Fq F Ω hk ⟨w, Fc_le_Fbar Fq F Ω (lev j) w.2⟩ = z
  rw [sig0_of_mem Fq F Ω hk _ (j := j) w.2]
  show ((frobF (isConstExt_Fc Fq F Ω hk (lev j)) w : Fc Fq F Ω (lev j)) : Ω) = z
  rw [AlgEquiv.apply_symm_apply]

/-- **The arithmetic Frobenius** `σ` of `F-bar / F`: `frobF` on every level, `c ↦ c ^ q` on `k-bar`. -/
noncomputable def sig : Fbar Fq F Ω ≃ₐ[F] Fbar Fq F Ω :=
  AlgEquiv.ofBijective (sig1 Fq F Ω hk)
    ⟨(sig1 Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω).injective, sig1_surjective Fq F Ω hk⟩

theorem coe_sig_of_mem (y : Fbar Fq F Ω) {j : ℕ} (hy : (y : Ω) ∈ Fc Fq F Ω (lev j)) :
    ((sig Fq F Ω hk y : Fbar Fq F Ω) : Ω) = (frobF (isConstExt_Fc Fq F Ω hk (lev j)) ⟨y, hy⟩ : Ω) :=
  sig0_of_mem Fq F Ω hk y hy

theorem sig_algebraMap_kbar (c : kbar Fq Ω) :
    sig Fq F Ω hk (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) =
      algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c ^ Fintype.card Fq := by
  obtain ⟨j, hj⟩ := exists_lev_of_mem_kbar c.2
  apply Subtype.ext
  rw [coe_sig_of_mem Fq F Ω hk _ (j := j) (mem_Fc_of_mem_Lc hj), SubmonoidClass.coe_pow]
  exact frobLev_coe Fq F Ω hk j hj

end Sig

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_Phi =====
section

/-!
# S4-JacFrob, part Phi: the relative (`k-bar`-linear) Frobenius `Φ = σ⁻¹ ∘ (·)^q` of `F-bar`

* `Phi : F-bar →ₐ[k-bar] F-bar`, `Phi z = σ⁻¹ (z ^ q) = (σ⁻¹ z) ^ q`; `Phi a = a ^ q` on `F`; `Phi x = x ^ q`;
* `Phi_comp_poly`: on `k-bar[X]` it is `expand q`; hence `isIntegral_Phi` and
* `PhiR : Rfin →ₐ[k-bar] Rfin` (the Frobenius of the affine curve `X⁰ = Spec Rfin`) and
  `PhiS g := symMap PhiR` on `S_g = SymRing k-bar Rfin g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial RamanujanPetersson.PicDescent Places RamanujanPetersson.JacSym

section Phi

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : constField Fq F = ⊥)

/-- **The relative Frobenius** `Φ = σ⁻¹ ∘ (·)^q`, a `k-bar`-algebra endomorphism of `F-bar`. -/
noncomputable def Phi : Fbar Fq F Ω →ₐ[kbar Fq Ω] Fbar Fq F Ω where
  toRingHom := ((sig Fq F Ω hk).symm : Fbar Fq F Ω →+* Fbar Fq F Ω).comp
    (FiniteField.frobeniusAlgHom Fq (Fbar Fq F Ω) : Fbar Fq F Ω →+* Fbar Fq F Ω)
  commutes' c := by
    show (sig Fq F Ω hk).symm (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c ^ Fintype.card Fq) = _
    rw [← sig_algebraMap_kbar Fq F Ω hk, AlgEquiv.symm_apply_apply]

theorem Phi_apply (z : Fbar Fq F Ω) : Phi Fq F Ω hk z = (sig Fq F Ω hk).symm (z ^ Fintype.card Fq) := rfl

theorem Phi_apply' (z : Fbar Fq F Ω) : Phi Fq F Ω hk z = (sig Fq F Ω hk).symm z ^ Fintype.card Fq := by
  rw [Phi_apply, map_pow]

theorem Phi_algebraMap_F (a : F) :
    Phi Fq F Ω hk (algebraMap F (Fbar Fq F Ω) a) = algebraMap F (Fbar Fq F Ω) a ^ Fintype.card Fq := by
  rw [Phi_apply, ← map_pow, AlgEquiv.commutes]

theorem Phi_xbar : Phi Fq F Ω hk (xbar Fq F Ω) = xbar Fq F Ω ^ Fintype.card Fq :=
  Phi_algebraMap_F Fq F Ω hk (RR.xF Fq F)

theorem Phi_injective : Function.Injective (Phi Fq F Ω hk) :=
  (Phi Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω).injective

theorem Phi_comp_poly :
    (Phi Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω).comp (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)) =
      (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)).comp
        (expand (kbar Fq Ω) (Fintype.card Fq) : (kbar Fq Ω)[X] →+* (kbar Fq Ω)[X]) := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, algebraMap_polyK, expand_C, aeval_C,
      AlgHom.commutes]
  · simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, algebraMap_polyK, expand_X, aeval_X,
      map_pow, Phi_xbar]

theorem isIntegral_Phi {z : Fbar Fq F Ω} (hz : IsIntegral (kbar Fq Ω)[X] z) :
    IsIntegral (kbar Fq Ω)[X] (Phi Fq F Ω hk z) :=
  IsIntegral.map_of_comp_eq
    (expand (kbar Fq Ω) (Fintype.card Fq) : (kbar Fq Ω)[X] →+* (kbar Fq Ω)[X])
    (Phi Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω) (Phi_comp_poly Fq F Ω hk).symm hz

/-- `Φ` on the finite coordinate ring `Rfin = k-bar[X]`-integral closure in `F-bar`. -/
noncomputable def PhiR : Rfin (kbar Fq Ω) (Fbar Fq F Ω) →ₐ[kbar Fq Ω] Rfin (kbar Fq Ω) (Fbar Fq F Ω) where
  toFun r := ⟨Phi Fq F Ω hk r, isIntegral_Phi Fq F Ω hk r.2⟩
  map_one' := Subtype.ext (map_one (Phi Fq F Ω hk))
  map_mul' a b := Subtype.ext (map_mul (Phi Fq F Ω hk) (a : Fbar Fq F Ω) b)
  map_zero' := Subtype.ext (map_zero (Phi Fq F Ω hk))
  map_add' a b := Subtype.ext (map_add (Phi Fq F Ω hk) (a : Fbar Fq F Ω) b)
  commutes' c := Subtype.ext ((Phi Fq F Ω hk).commutes c)

theorem coe_PhiR (r : Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :
    ((PhiR Fq F Ω hk r : Rfin (kbar Fq Ω) (Fbar Fq F Ω)) : Fbar Fq F Ω) = Phi Fq F Ω hk r := rfl

theorem PhiR_injective : Function.Injective (PhiR Fq F Ω hk) := fun _ _ h =>
  Subtype.ext (Phi_injective Fq F Ω hk (congrArg Subtype.val h))

/-- `Φ` on `S_g = SymRing k-bar Rfin g` (coordinate ring of `Sym^g X⁰`). -/
noncomputable abbrev PhiS (g : ℕ) :
    SymRing (kbar Fq Ω) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) g →ₐ[kbar Fq Ω]
      SymRing (kbar Fq Ω) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) g :=
  symMap (PhiR Fq F Ω hk)

end Phi

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_SigPl =====
section

/-!
# S4-JacFrob, part SigPl: `σ_*` on places, divisors and `Pic` of `F-bar / k-bar`

* `frK : k-bar ≃+* k-bar`, `c ↦ c ^ q`; `ratFr ρ` and `oinfMap ρ`: a ring endomorphism `ρ` of `K`
  acting coefficientwise on `K(x)` and on `O_∞(K)`;
* `sigRfin, sigRinf`: the arithmetic Frobenius `σ` preserves `Rfin` and `Rinf` (semilinearly);
* `sigPl : Place ≃ Place` with `ord_sigPl : (sigPl P).ord f = P.ord (σ⁻¹ f)` (so `sigPl = σ_*`);
* `sigD := Finsupp.domCongr sigPl` with `div_sig : div (σ f) = sigD (div f)` and `deg_sigD`;
* `sigPic : PicK ≃+ PicK` with `sigPic_mk`, `degPicK_sigPic`, `sigPic_mem_Pic0K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places RamanujanPetersson.JacComplete

section Generic

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

/-- A ring endomorphism of `K` acting on the coefficients of `K(x)`. -/
noncomputable def ratFr (ρ : K →+* K) : RatFunc K →+* RatFunc K :=
  RatFunc.mapRingHom (Polynomial.mapRingHom ρ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.map_injective _ ρ.injective))

theorem ratFr_div (ρ : K →+* K) (p d : K[X]) :
    ratFr ρ (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) d) =
      algebraMap K[X] (RatFunc K) (p.map ρ) / algebraMap K[X] (RatFunc K) (d.map ρ) :=
  RatFunc.map_apply_div _ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ ρ.injective)) p d

theorem ratFr_algebraMap (ρ : K →+* K) (p : K[X]) :
    ratFr ρ (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (p.map ρ) := by
  have h := ratFr_div ρ p 1
  rwa [map_one, div_one, Polynomial.map_one, map_one, div_one] at h

theorem ratFr_mem_Oinf (ρ : K →+* K) {g : RatFunc K} (hg : g ∈ Oinf K) : ratFr ρ g ∈ Oinf K := by
  by_cases h0 : g = 0
  · rw [h0, map_zero]; exact zero_mem _
  have hdeg : g.intDegree ≤ 0 := (mem_Oinf_iff' K h0).mp hg
  have e := RatFunc.num_div_denom g
  rw [← e, ratFr_div]
  apply mem_Oinf_div ((Polynomial.map_ne_zero_iff ρ.injective).mpr (RatFunc.denom_ne_zero g))
  rw [natDegree_map, natDegree_map]
  unfold RatFunc.intDegree at hdeg
  omega

/-- `ρ` acting on `O_∞(K)`. -/
noncomputable def oinfMap (ρ : K →+* K) : Oinf K →+* Oinf K :=
  (ratFr ρ).restrict (Oinf K) (Oinf K) fun _ hz => ratFr_mem_Oinf ρ hz

/-- A ring automorphism preserving a subring (both ways) restricts to it. -/
def restrEquiv {L S : Type*} [Ring L] [SetLike S L] [SubringClass S L] (s : S) (τ : L ≃+* L)
    (h1 : ∀ z ∈ s, τ z ∈ s) (h2 : ∀ z ∈ s, τ.symm z ∈ s) : s ≃+* s where
  toFun z := ⟨τ z, h1 z z.2⟩
  invFun z := ⟨τ.symm z, h2 z z.2⟩
  left_inv _ := Subtype.ext (τ.symm_apply_apply _)
  right_inv _ := Subtype.ext (τ.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul τ _ _)
  map_add' _ _ := Subtype.ext (map_add τ _ _)

/-- `w ↦ σ⁻¹ w` as a bijection of `HeightOneSpectrum B`. -/
noncomputable def hosEquiv {B : Type*} [CommRing B] [IsDedekindDomain B] (σ : B ≃+* B) :
    HeightOneSpectrum B ≃ HeightOneSpectrum B where
  toFun := pullH σ
  invFun := pullH σ.symm
  left_inv w := by
    apply HeightOneSpectrum.ext
    ext b
    show σ (σ.symm b) ∈ w.asIdeal ↔ b ∈ w.asIdeal
    rw [RingEquiv.apply_symm_apply]
  right_inv w := by
    apply HeightOneSpectrum.ext
    ext b
    show σ.symm (σ b) ∈ w.asIdeal ↔ b ∈ w.asIdeal
    rw [RingEquiv.symm_apply_apply]

theorem ord_hosEquiv {B L : Type*} [CommRing B] [IsDedekindDomain B] [Field L] [Algebra B L]
    [IsFractionRing B L] (σ : B ≃+* B) (σL : L ≃+* L)
    (hσ : ∀ b, algebraMap B L (σ b) = σL (algebraMap B L b)) (w : HeightOneSpectrum B) (x : L) :
    Places.ord (hosEquiv σ w) x = Places.ord w (σL x) := by
  unfold Places.ord
  rw [show hosEquiv σ w = pullH σ w from rfl, valuation_pullH σ σL hσ w x]

end Generic

section Frob

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω]

/-- The `q`-power Frobenius of `k-bar` (bijective: `k-bar` is algebraic over `Fq`). -/
noncomputable def frK : kbar Fq Ω ≃+* kbar Fq Ω :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic Fq (kbar Fq Ω)).toRingEquiv

theorem frK_apply (c : kbar Fq Ω) : frK Fq Ω c = c ^ Fintype.card Fq := rfl

end Frob

section Transport

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable {Fq F Ω}

theorem comp_poly_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) :
    (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)).comp (mapRingHom ρ) =
      τ.comp (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)) := by
  have e : ∀ c : kbar Fq Ω,
      algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) (C c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c :=
    fun c => (IsScalarTower.algebraMap_apply (kbar Fq Ω) (kbar Fq Ω)[X] (Fbar Fq F Ω) c).symm
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C, e, hc]
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]
    rw [algebraMap_polyK, aeval_X, hx]

theorem comp_rat_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) :
    (algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)).comp (ratFr ρ) =
      τ.comp (algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (kbar Fq Ω)[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [ratFr_algebraMap,
    ← IsScalarTower.algebraMap_apply (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω),
    ← IsScalarTower.algebraMap_apply (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)]
  exact RingHom.congr_fun (comp_poly_of τ ρ hc hx) p

theorem comp_oinf_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) :
    (algebraMap (Oinf (kbar Fq Ω)) (Fbar Fq F Ω)).comp (oinfMap ρ) =
      τ.comp (algebraMap (Oinf (kbar Fq Ω)) (Fbar Fq F Ω)) := by
  refine RingHom.ext fun z => ?_
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (Oinf (kbar Fq Ω)) (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω),
    IsScalarTower.algebraMap_apply (Oinf (kbar Fq Ω)) (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) z]
  exact RingHom.congr_fun (comp_rat_of τ ρ hc hx) (z : RatFunc (kbar Fq Ω))

theorem mem_Rfin_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) {z : Fbar Fq F Ω}
    (hz : z ∈ FunctionField.ringOfIntegers (kbar Fq Ω) (Fbar Fq F Ω)) :
    τ z ∈ FunctionField.ringOfIntegers (kbar Fq Ω) (Fbar Fq F Ω) :=
  IsIntegral.map_of_comp_eq (mapRingHom ρ) τ (comp_poly_of τ ρ hc hx) hz

theorem mem_Rinf_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) {z : Fbar Fq F Ω}
    (hz : z ∈ integralClosure (Oinf (kbar Fq Ω)) (Fbar Fq F Ω)) :
    τ z ∈ integralClosure (Oinf (kbar Fq Ω)) (Fbar Fq F Ω) :=
  IsIntegral.map_of_comp_eq (oinfMap ρ) τ (comp_oinf_of τ ρ hc hx) hz

end Transport

section SigPl

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : constField Fq F = ⊥)

theorem sig_kbar (c : kbar Fq Ω) :
    sig Fq F Ω hk (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) =
      algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (frK Fq Ω c) := by
  rw [sig_algebraMap_kbar, frK_apply, map_pow]

theorem sigsymm_kbar (c : kbar Fq Ω) :
    (sig Fq F Ω hk).symm (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) =
      algebraMap (kbar Fq Ω) (Fbar Fq F Ω) ((frK Fq Ω).symm c) := by
  rw [AlgEquiv.symm_apply_eq, sig_kbar, RingEquiv.apply_symm_apply]

theorem sig_xbar : sig Fq F Ω hk (xbar Fq F Ω) = xbar Fq F Ω := AlgEquiv.commutes _ _

theorem sigsymm_xbar : (sig Fq F Ω hk).symm (xbar Fq F Ω) = xbar Fq F Ω := AlgEquiv.commutes _ _

/-- `σ` on the finite ring `Rfin = k-bar[x]`-integral closure. -/
noncomputable def sigRfin : Rfin (kbar Fq Ω) (Fbar Fq F Ω) ≃+* Rfin (kbar Fq Ω) (Fbar Fq F Ω) :=
  restrEquiv (FunctionField.ringOfIntegers (kbar Fq Ω) (Fbar Fq F Ω)) (sig Fq F Ω hk).toRingEquiv
    (fun _ hz => mem_Rfin_of (sig Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω) (frK Fq Ω : kbar Fq Ω →+* kbar Fq Ω)
      (sig_kbar Fq F Ω hk) (sig_xbar Fq F Ω hk) hz)
    (fun _ hz => mem_Rfin_of ((sig Fq F Ω hk).symm : Fbar Fq F Ω →+* Fbar Fq F Ω)
      ((frK Fq Ω).symm : kbar Fq Ω →+* kbar Fq Ω) (sigsymm_kbar Fq F Ω hk) (sigsymm_xbar Fq F Ω hk) hz)

/-- `σ` on the ring `Rinf` of the places over `x = ∞`. -/
noncomputable def sigRinf : Rinf (kbar Fq Ω) (Fbar Fq F Ω) ≃+* Rinf (kbar Fq Ω) (Fbar Fq F Ω) :=
  restrEquiv (integralClosure (Oinf (kbar Fq Ω)) (Fbar Fq F Ω)) (sig Fq F Ω hk).toRingEquiv
    (fun _ hz => mem_Rinf_of (sig Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω) (frK Fq Ω : kbar Fq Ω →+* kbar Fq Ω)
      (sig_kbar Fq F Ω hk) (sig_xbar Fq F Ω hk) hz)
    (fun _ hz => mem_Rinf_of ((sig Fq F Ω hk).symm : Fbar Fq F Ω →+* Fbar Fq F Ω)
      ((frK Fq Ω).symm : kbar Fq Ω →+* kbar Fq Ω) (sigsymm_kbar Fq F Ω hk) (sigsymm_xbar Fq F Ω hk) hz)

/-- **`σ_*` on places**: `ord_{σ_* P} f = ord_P (σ⁻¹ f)`. -/
noncomputable def sigPl : Places.Place (kbar Fq Ω) (Fbar Fq F Ω) ≃ Places.Place (kbar Fq Ω) (Fbar Fq F Ω) :=
  Equiv.sumCongr (hosEquiv (sigRfin Fq F Ω hk).symm) (hosEquiv (sigRinf Fq F Ω hk).symm)

theorem ord_sigPl (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) (f : Fbar Fq F Ω) :
    (sigPl Fq F Ω hk P).ord f = P.ord ((sig Fq F Ω hk).symm f) := by
  rcases P with w | w
  · exact ord_hosEquiv (sigRfin Fq F Ω hk).symm (sig Fq F Ω hk).symm.toRingEquiv (fun _ => rfl) w f
  · exact ord_hosEquiv (sigRinf Fq F Ω hk).symm (sig Fq F Ω hk).symm.toRingEquiv (fun _ => rfl) w f

/-- `σ_*` on divisors. -/
noncomputable def sigD : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω) ≃+ Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω) :=
  Finsupp.domCongr (sigPl Fq F Ω hk)

theorem sigD_apply (D : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) (Q : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    sigD Fq F Ω hk D Q = D ((sigPl Fq F Ω hk).symm Q) := rfl

/-- **`div (σ f) = σ_* (div f)`**. -/
theorem div_sig (f : Fbar Fq F Ω) :
    (PlacesK.div (sig Fq F Ω hk f) : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) =
      sigD Fq F Ω hk (PlacesK.div f) := by
  ext Q
  obtain ⟨P, rfl⟩ := (sigPl Fq F Ω hk).surjective Q
  rw [sigD_apply, PlacesK.div_apply, PlacesK.div_apply, Equiv.symm_apply_apply, ord_sigPl,
    AlgEquiv.symm_apply_apply]

theorem deg_sigD (D : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) :
    Places.Divisor.deg (sigD Fq F Ω hk D) = D.deg := by
  unfold Places.Divisor.deg
  rw [show sigD Fq F Ω hk D = Finsupp.mapDomain (sigPl Fq F Ω hk) D from
      Finsupp.equivMapDomain_eq_mapDomain _ _,
    Finsupp.sum_mapDomain_index (fun _ => by ring) (fun _ _ _ => by ring)]
  simp only [placeDeg_one]

theorem map_sigD_PrincK :
    (PrincK (kbar Fq Ω) (Fbar Fq F Ω)).map
        (sigD Fq F Ω hk : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω) →+ Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) =
      PrincK (kbar Fq Ω) (Fbar Fq F Ω) := by
  ext D
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨f, hf, rfl⟩ := (mem_PrincK _ _).mp hE
    exact ⟨sig Fq F Ω hk f, (_root_.map_ne_zero _).mpr hf, div_sig Fq F Ω hk f⟩
  · intro hD
    obtain ⟨f, hf, rfl⟩ := (mem_PrincK _ _).mp hD
    refine ⟨PlacesK.div ((sig Fq F Ω hk).symm f),
      div_mem_PrincK _ _ ((_root_.map_ne_zero _).mpr hf), ?_⟩
    show sigD Fq F Ω hk (PlacesK.div ((sig Fq F Ω hk).symm f)) = PlacesK.div f
    rw [← div_sig, AlgEquiv.apply_symm_apply]

/-- **`σ_*` on the divisor class group** of `F-bar / k-bar`. -/
noncomputable def sigPic : PicK (kbar Fq Ω) (Fbar Fq F Ω) ≃+ PicK (kbar Fq Ω) (Fbar Fq F Ω) :=
  QuotientAddGroup.congr _ _ (sigD Fq F Ω hk) (map_sigD_PrincK Fq F Ω hk)

theorem sigPic_mk (D : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) :
    sigPic Fq F Ω hk (clsK _ _ D) = clsK _ _ (sigD Fq F Ω hk D) := rfl

theorem degPicK_sigPic (x : PicK (kbar Fq Ω) (Fbar Fq F Ω)) :
    degPicK _ _ (sigPic Fq F Ω hk x) = degPicK _ _ x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  show degPicK _ _ (clsK _ _ (sigD Fq F Ω hk D)) = degPicK _ _ (clsK _ _ D)
  rw [degPicK_clsK, degPicK_clsK, deg_sigD]

end SigPl

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_BrR =====
section

/-!
# S4-JacFrob, part BrR (bridge 1): the rings of the levels `F_N` inside those of `F-bar`

* generic: `ratHom ρ : K(x) →+* K'(x)`, `oinfHom ρ`, `gen_comp_poly/rat/oinf`, `gen_int_fin/inf`
  (a map of function fields compatible with `ρ` on constants and fixing `x` preserves integrality);
* `incL j : Lc (lev j) →+* k-bar`, `incF j : Fc (lev j) →+* F-bar`;
* `finR j : Rfin (Fc (lev j)) →+* Rfin (F-bar)`, `infR j` likewise (injective);
* **`exists_finR`, `exists_infR`**: every element of `Rfin (F-bar)` (`Rinf (F-bar)`) comes from a level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section Gen

variable {K K' : Type*} [Field K] [Field K'] [DecidableEq (RatFunc K)] [DecidableEq (RatFunc K')]
variable {L L' : Type*} [Field L] [Field L'] [Algebra K L] [Algebra K[X] L] [Algebra (RatFunc K) L]
  [IsScalarTower K[X] (RatFunc K) L] [IsScalarTower K K[X] L]
  [Algebra K' L'] [Algebra K'[X] L'] [Algebra (RatFunc K') L']
  [IsScalarTower K'[X] (RatFunc K') L'] [IsScalarTower K' K'[X] L']

/-- A field map `ρ : K → K'` acting on the coefficients of rational functions. -/
noncomputable def ratHom (ρ : K →+* K') : RatFunc K →+* RatFunc K' :=
  RatFunc.mapRingHom (Polynomial.mapRingHom ρ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.map_injective _ ρ.injective))

theorem ratHom_div (ρ : K →+* K') (p d : K[X]) :
    ratHom ρ (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) d) =
      algebraMap K'[X] (RatFunc K') (p.map ρ) / algebraMap K'[X] (RatFunc K') (d.map ρ) :=
  RatFunc.map_apply_div _ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ ρ.injective)) p d

theorem ratHom_algebraMap (ρ : K →+* K') (p : K[X]) :
    ratHom ρ (algebraMap K[X] (RatFunc K) p) = algebraMap K'[X] (RatFunc K') (p.map ρ) := by
  have h := ratHom_div ρ p 1
  rwa [map_one, div_one, Polynomial.map_one, map_one, div_one] at h

theorem ratHom_mem_Oinf (ρ : K →+* K') {g : RatFunc K} (hg : g ∈ Oinf K) : ratHom ρ g ∈ Oinf K' := by
  by_cases h0 : g = 0
  · rw [h0, map_zero]; exact zero_mem _
  have hdeg : g.intDegree ≤ 0 := (mem_Oinf_iff' K h0).mp hg
  have e := RatFunc.num_div_denom g
  rw [← e, ratHom_div]
  apply mem_Oinf_div ((Polynomial.map_ne_zero_iff ρ.injective).mpr (RatFunc.denom_ne_zero g))
  rw [natDegree_map, natDegree_map]
  unfold RatFunc.intDegree at hdeg
  omega

/-- `ρ` acting on `O_∞`. -/
noncomputable def oinfHom (ρ : K →+* K') : Oinf K →+* Oinf K' :=
  (ratHom ρ).restrict (Oinf K) (Oinf K') fun _ hz => ratHom_mem_Oinf ρ hz

theorem coe_oinfHom (ρ : K →+* K') (z : Oinf K) : ((oinfHom ρ z : Oinf K') : RatFunc K') = ratHom ρ z :=
  RingHom.coe_restrict_apply _ _ _ _ _

variable (ψ : L →+* L') (ρ : K →+* K') (hc : ∀ c, ψ (algebraMap K L c) = algebraMap K' L' (ρ c))
  (hx : ψ (algebraMap K[X] L X) = algebraMap K'[X] L' X)

include hc hx

theorem gen_comp_poly : (algebraMap K'[X] L').comp (mapRingHom ρ) = ψ.comp (algebraMap K[X] L) := by
  have e1 : ∀ c : K, algebraMap K[X] L (C c) = algebraMap K L c :=
    fun c => (IsScalarTower.algebraMap_apply K K[X] L c).symm
  have e2 : ∀ c : K', algebraMap K'[X] L' (C c) = algebraMap K' L' c :=
    fun c => (IsScalarTower.algebraMap_apply K' K'[X] L' c).symm
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C, e1, e2, hc]
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]
    exact hx.symm

theorem gen_comp_rat : (algebraMap (RatFunc K') L').comp (ratHom ρ) = ψ.comp (algebraMap (RatFunc K) L) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors K[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [ratHom_algebraMap, ← IsScalarTower.algebraMap_apply K'[X] (RatFunc K') L',
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) L]
  exact RingHom.congr_fun (gen_comp_poly ψ ρ hc hx) p

theorem gen_comp_oinf : (algebraMap (Oinf K') L').comp (oinfHom ρ) = ψ.comp (algebraMap (Oinf K) L) := by
  refine RingHom.ext fun z => ?_
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (Oinf K') (RatFunc K') L',
    IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) L z]
  exact RingHom.congr_fun (gen_comp_rat ψ ρ hc hx) (z : RatFunc K)

theorem gen_int_fin {z : L} (hz : IsIntegral K[X] z) : IsIntegral K'[X] (ψ z) :=
  IsIntegral.map_of_comp_eq (mapRingHom ρ) ψ (gen_comp_poly ψ ρ hc hx) hz

theorem gen_int_inf {z : L} (hz : IsIntegral (Oinf K) z) : IsIntegral (Oinf K') (ψ z) :=
  IsIntegral.map_of_comp_eq (oinfHom ρ) ψ (gen_comp_oinf ψ ρ hc hx) hz

end Gen

/-- Coefficients of a polynomial over a directed union lie in one member. -/
theorem exists_coeff_mem {R : Type*} [Semiring R] (A : ℕ → Set R) (hA : Monotone A)
    (h0 : ∀ j, (0 : R) ∈ A j) (hcov : ∀ r, ∃ j, r ∈ A j) (p : R[X]) : ∃ j, ∀ n, p.coeff n ∈ A j := by
  choose f hf using hcov
  refine ⟨p.support.sup fun n => f (p.coeff n), fun n => ?_⟩
  by_cases hn : n ∈ p.support
  · exact hA (Finset.le_sup (f := fun n => f (p.coeff n)) hn) (hf _)
  · rw [Polynomial.notMem_support_iff.mp hn]; exact h0 _

section Lev

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- `Lc (lev j) → k-bar`. -/
noncomputable def incL (j : ℕ) : Lc Fq Ω (lev j) →+* kbar Fq Ω :=
  (IntermediateField.inclusion (Lc_le_kbar Fq Ω (lev j))).toRingHom

/-- `Fc (lev j) → F-bar`. -/
noncomputable def incF (j : ℕ) : Fc Fq F Ω (lev j) →+* Fbar Fq F Ω :=
  (IntermediateField.inclusion (Fc_le_Fbar Fq F Ω (lev j))).toRingHom

theorem hc_lev (j : ℕ) (c : Lc Fq Ω (lev j)) :
    incF Fq F Ω j (algebraMap (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) c) =
      algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (incL Fq Ω j c) := Subtype.ext rfl

theorem hx_lev (j : ℕ) :
    incF Fq F Ω j (algebraMap (Lc Fq Ω (lev j))[X] (Fc Fq F Ω (lev j)) X) =
      algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) X := by
  rw [algebraMap_polyF, algebraMap_polyK, aeval_X, aeval_X]
  exact Subtype.ext rfl

/-- The finite ring of level `lev j` inside that of `F-bar`. -/
noncomputable def finR (j : ℕ) :
    Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) →+* Rfin (kbar Fq Ω) (Fbar Fq F Ω) :=
  (incF Fq F Ω j).restrict (FunctionField.ringOfIntegers (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)))
    (FunctionField.ringOfIntegers (kbar Fq Ω) (Fbar Fq F Ω))
    fun _ hz => gen_int_fin (incF Fq F Ω j) (incL Fq Ω j) (hc_lev Fq F Ω j) (hx_lev Fq F Ω j) hz

/-- The infinite ring of level `lev j` inside that of `F-bar`. -/
noncomputable def infR (j : ℕ) :
    Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) →+* Rinf (kbar Fq Ω) (Fbar Fq F Ω) :=
  (incF Fq F Ω j).restrict (integralClosure (Oinf (Lc Fq Ω (lev j))) (Fc Fq F Ω (lev j)))
    (integralClosure (Oinf (kbar Fq Ω)) (Fbar Fq F Ω))
    fun _ hz => gen_int_inf (incF Fq F Ω j) (incL Fq Ω j) (hc_lev Fq F Ω j) (hx_lev Fq F Ω j) hz

theorem coe_finR (j : ℕ) (y : Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    (finR Fq F Ω j y : Fbar Fq F Ω) = incF Fq F Ω j y := RingHom.coe_restrict_apply _ _ _ _ _

theorem coe_infR (j : ℕ) (y : Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    (infR Fq F Ω j y : Fbar Fq F Ω) = incF Fq F Ω j y := RingHom.coe_restrict_apply _ _ _ _ _

theorem finR_injective (j : ℕ) : Function.Injective (finR Fq F Ω j) := fun a b h =>
  Subtype.ext ((incF Fq F Ω j).injective (by rw [← coe_finR, ← coe_finR, h]))

theorem infR_injective (j : ℕ) : Function.Injective (infR Fq F Ω j) := fun a b h =>
  Subtype.ext ((incF Fq F Ω j).injective (by rw [← coe_infR, ← coe_infR, h]))

theorem range_incL_mono {i j : ℕ} (h : i ≤ j) : Set.range (incL Fq Ω i) ⊆ Set.range (incL Fq Ω j) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨(a : Ω), Lc_le (lev_dvd_lev h) a.2⟩, Subtype.ext rfl⟩

theorem lifts_incL_mono {i j : ℕ} (h : i ≤ j) (r : (kbar Fq Ω)[X]) (hr : r ∈ lifts (incL Fq Ω i)) :
    r ∈ lifts (incL Fq Ω j) :=
  (lifts_iff_coeff_lifts r).mpr fun n => range_incL_mono Fq Ω h ((lifts_iff_coeff_lifts r).mp hr n)

theorem exists_lifts_incL (r : (kbar Fq Ω)[X]) : ∃ j, r ∈ lifts (incL Fq Ω j) := by
  obtain ⟨j, hj⟩ := exists_coeff_mem (fun j => Set.range (incL Fq Ω j)) (fun _ _ h => range_incL_mono Fq Ω h)
    (fun j => ⟨0, map_zero _⟩) (fun c => by
      obtain ⟨j, hj⟩ := exists_lev_of_mem_kbar c.2
      exact ⟨j, ⟨⟨c, hj⟩, rfl⟩⟩) r
  exact ⟨j, (lifts_iff_coeff_lifts r).mpr hj⟩

/-- **Every finite regular function on `F-bar` comes from a level.** -/
theorem exists_finR (z : Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :
    ∃ j, ∃ y : Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)), finR Fq F Ω j y = z := by
  obtain ⟨j0, hj0⟩ := exists_lev_of_mem_Fbar (z : Fbar Fq F Ω).2
  have hz : IsIntegral (kbar Fq Ω)[X] (z : Fbar Fq F Ω) := z.2
  obtain ⟨p, hpm, hpz⟩ := hz
  obtain ⟨j1, hj1⟩ := exists_coeff_mem (fun j => {r | r ∈ lifts (incL Fq Ω j)})
    (fun _ _ h => lifts_incL_mono Fq Ω h)
    (fun _ => show (0 : (kbar Fq Ω)[X]) ∈ lifts (incL Fq Ω _) from zero_mem _) (exists_lifts_incL Fq Ω) p
  set j := max j0 j1
  have hl : p ∈ lifts (mapRingHom (incL Fq Ω j)) := (lifts_iff_coeff_lifts p).mpr fun n =>
    (lifts_iff_set_range _).mp (lifts_incL_mono Fq Ω (le_max_right j0 j1) _ (hj1 n))
  obtain ⟨p', hp'map, -, hp'm⟩ := lifts_and_natDegree_eq_and_monic hl hpm
  let y0 : Fc Fq F Ω (lev j) := ⟨((z : Fbar Fq F Ω) : Ω), Fc_le (lev_dvd_lev (le_max_left j0 j1)) hj0⟩
  have hy0 : incF Fq F Ω j y0 = (z : Fbar Fq F Ω) := Subtype.ext rfl
  have key : incF Fq F Ω j (eval₂ (algebraMap _ (Fc Fq F Ω (lev j))) y0 p') = 0 := by
    rw [hom_eval₂, ← gen_comp_poly (incF Fq F Ω j) (incL Fq Ω j) (hc_lev Fq F Ω j) (hx_lev Fq F Ω j), hy0,
      ← eval₂_map, hp'map]
    exact hpz
  have h0 : eval₂ (algebraMap _ (Fc Fq F Ω (lev j))) y0 p' = 0 :=
    (incF Fq F Ω j).injective (key.trans (map_zero _).symm)
  exact ⟨j, ⟨y0, (show IsIntegral _ y0 from ⟨p', hp'm, h0⟩)⟩, Subtype.ext ((coe_finR Fq F Ω j _).trans hy0)⟩

theorem exists_oinfHom (a : Oinf (kbar Fq Ω)) (j : ℕ) (h1 : (a : RatFunc (kbar Fq Ω)).num ∈ lifts (incL Fq Ω j))
    (h2 : (a : RatFunc (kbar Fq Ω)).denom ∈ lifts (incL Fq Ω j)) :
    a ∈ Set.range (oinfHom (incL Fq Ω j)) := by
  by_cases ha : (a : RatFunc (kbar Fq Ω)) = 0
  · exact ⟨0, Subtype.ext (by rw [map_zero, ha]; rfl)⟩
  obtain ⟨r1, hr1⟩ := (lifts_iff_set_range _).mp h1
  obtain ⟨r2, hr2⟩ := (lifts_iff_set_range _).mp h2
  have hr20 : r2 ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hr2
    exact RatFunc.denom_ne_zero _ hr2.symm
  have hdeg : (a : RatFunc (kbar Fq Ω)).intDegree ≤ 0 := (mem_Oinf_iff' _ ha).mp a.2
  have hle : r1.natDegree ≤ r2.natDegree := by
    unfold RatFunc.intDegree at hdeg
    rw [← natDegree_map (p := r1) (incL Fq Ω j), ← natDegree_map (p := r2) (incL Fq Ω j), hr1, hr2]
    omega
  refine ⟨⟨_, mem_Oinf_div hr20 hle⟩, Subtype.ext ?_⟩
  rw [coe_oinfHom]
  show ratHom (incL Fq Ω j) (algebraMap _ (RatFunc (Lc Fq Ω (lev j))) r1 /
    algebraMap _ (RatFunc (Lc Fq Ω (lev j))) r2) = (a : RatFunc (kbar Fq Ω))
  rw [ratHom_div, hr1, hr2, RatFunc.num_div_denom]

/-- **Every function on `F-bar` regular at the places over `∞` comes from a level.** -/
theorem exists_infR (z : Rinf (kbar Fq Ω) (Fbar Fq F Ω)) :
    ∃ j, ∃ y : Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)), infR Fq F Ω j y = z := by
  obtain ⟨j0, hj0⟩ := exists_lev_of_mem_Fbar (z : Fbar Fq F Ω).2
  have hz : IsIntegral (Oinf (kbar Fq Ω)) (z : Fbar Fq F Ω) := z.2
  obtain ⟨p, hpm, hpz⟩ := hz
  obtain ⟨j1, hj1⟩ := exists_coeff_mem
    (fun j => {a : Oinf (kbar Fq Ω) | (a : RatFunc (kbar Fq Ω)).num ∈ lifts (incL Fq Ω j) ∧
      (a : RatFunc (kbar Fq Ω)).denom ∈ lifts (incL Fq Ω j)})
    (fun _ _ h _ ha => ⟨lifts_incL_mono Fq Ω h _ ha.1, lifts_incL_mono Fq Ω h _ ha.2⟩)
    (fun _ => by
      show (0 : RatFunc (kbar Fq Ω)).num ∈ _ ∧ (0 : RatFunc (kbar Fq Ω)).denom ∈ _
      rw [RatFunc.num_zero, RatFunc.denom_zero]
      exact ⟨zero_mem _, one_mem _⟩)
    (fun a => by
      obtain ⟨i1, h1⟩ := exists_lifts_incL Fq Ω (a : RatFunc (kbar Fq Ω)).num
      obtain ⟨i2, h2⟩ := exists_lifts_incL Fq Ω (a : RatFunc (kbar Fq Ω)).denom
      exact ⟨max i1 i2, lifts_incL_mono Fq Ω (le_max_left _ _) _ h1,
        lifts_incL_mono Fq Ω (le_max_right _ _) _ h2⟩) p
  set j := max j0 j1
  have hl : p ∈ lifts (oinfHom (incL Fq Ω j)) := (lifts_iff_coeff_lifts p).mpr fun n =>
    exists_oinfHom Fq Ω _ j (lifts_incL_mono Fq Ω (le_max_right j0 j1) _ (hj1 n).1)
      (lifts_incL_mono Fq Ω (le_max_right j0 j1) _ (hj1 n).2)
  obtain ⟨p', hp'map, -, hp'm⟩ := lifts_and_natDegree_eq_and_monic hl hpm
  let y0 : Fc Fq F Ω (lev j) := ⟨((z : Fbar Fq F Ω) : Ω), Fc_le (lev_dvd_lev (le_max_left j0 j1)) hj0⟩
  have hy0 : incF Fq F Ω j y0 = (z : Fbar Fq F Ω) := Subtype.ext rfl
  have key : incF Fq F Ω j (eval₂ (algebraMap _ (Fc Fq F Ω (lev j))) y0 p') = 0 := by
    rw [hom_eval₂, ← gen_comp_oinf (incF Fq F Ω j) (incL Fq Ω j) (hc_lev Fq F Ω j) (hx_lev Fq F Ω j), hy0,
      ← eval₂_map, hp'map]
    exact hpz
  have h0 : eval₂ (algebraMap _ (Fc Fq F Ω (lev j))) y0 p' = 0 :=
    (incF Fq F Ω j).injective (key.trans (map_zero _).symm)
  exact ⟨j, ⟨y0, (show IsIntegral _ y0 from ⟨p', hp'm, h0⟩)⟩, Subtype.ext ((coe_infR Fq F Ω j _).trans hy0)⟩

end Lev

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_BrC =====
section

/-!
# S4-JacFrob, part BrC (bridge 2): contraction of places of `F-bar` to the levels `F_{lev j}`

* generic (a constant field extension `h`): `isIntegral_algFin/Inf h` (the ring pairs are integral),
  `coe_algFin/Inf h` (the pair maps are the field inclusion);
* `coe_incF`; `finR_pair`, `infR_pair` (`finR m ∘ (pair map) = finR i` for `lev i ∣ lev m`);
* **`isIntegral_finR j`, `isIntegral_infR j`**: `Rfin(F-bar)` (`Rinf(F-bar)`) is integral over the level ring;
* generic `asIdeal_contFin/Inf h` (the level contraction is `comap` of the pair map);
* `contFinB j`, `contInfB j` (`w ↦ w ∩ Rfin_j` via `HeightOneSpectrum.under`), `asIdeal_contFinB/InfB` (`= comap (finR j)`),
  `mem_contFinB`, `mem_contInfB`; `contB_inl/inr`, `contractNN_inl/inr`;
* **`contB j : Place (F-bar) → Place (F_{lev j})`**; `isLeft_contB`; **`contractNN_contB`** (compatible with the
  contractions between levels); **`exists_contB_eq`** (lying over); **`finite_contB`** (finite fibres).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section PairInt

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

theorem isIntegral_algFin : letI := algFin h; Algebra.IsIntegral (Rfin Fq F) (Rfin L F') := by
  letI := algFin h; haveI := towerFin h
  exact isIntegral_AA' h.linearIndependent h.span (injFin Fq F) (injFin L F') h.fin

theorem isIntegral_algInf : letI := algInf h; Algebra.IsIntegral (Rinf Fq F) (Rinf L F') := by
  letI := algInf h; haveI := towerInf h
  exact isIntegral_AA' h.linearIndependent h.span (injInf Fq F) (injInf L F') h.inf

theorem coe_algFin (a : Rfin Fq F) :
    letI := algFin h
    ((algebraMap (Rfin Fq F) (Rfin L F') a : Rfin L F') : F') = algebraMap F F' (a : F) := by
  letI := algFin h; haveI := towerFin h
  exact (IsScalarTower.algebraMap_apply (Rfin Fq F) (Rfin L F') F' a).symm.trans
    (IsScalarTower.algebraMap_apply (Rfin Fq F) F F' a)

theorem coe_algInf (a : Rinf Fq F) :
    letI := algInf h
    ((algebraMap (Rinf Fq F) (Rinf L F') a : Rinf L F') : F') = algebraMap F F' (a : F) := by
  letI := algInf h; haveI := towerInf h
  exact (IsScalarTower.algebraMap_apply (Rinf Fq F) (Rinf L F') F' a).symm.trans
    (IsScalarTower.algebraMap_apply (Rinf Fq F) F F' a)

theorem asIdeal_contFin (v : HeightOneSpectrum (Rfin L F')) :
    letI := algFin h
    (contFin h v).asIdeal = v.asIdeal.comap (algebraMap (Rfin Fq F) (Rfin L F')) := rfl

theorem asIdeal_contInf (v : HeightOneSpectrum (Rinf L F')) :
    letI := algInf h
    (contInf h v).asIdeal = v.asIdeal.comap (algebraMap (Rinf Fq F) (Rinf L F')) := rfl

end PairInt

section Cont

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem coe_incF (j : ℕ) (y : Fc Fq F Ω (lev j)) : ((incF Fq F Ω j y : Fbar Fq F Ω) : Ω) = (y : Ω) :=
  IntermediateField.coe_inclusion _ y

variable (hk : constField Fq F = ⊥)

theorem finR_pair {i m : ℕ} [Fact (lev i ∣ lev m)] (a : Rfin (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i))) :
    letI := algFin (isConstExt_pair Fq F Ω hk (n := lev i) (N := lev m))
    finR Fq F Ω m (algebraMap _ (Rfin (Lc Fq Ω (lev m)) (Fc Fq F Ω (lev m))) a) = finR Fq F Ω i a := by
  letI := algFin (isConstExt_pair Fq F Ω hk (n := lev i) (N := lev m))
  apply Subtype.ext
  rw [coe_finR, coe_finR]
  apply Subtype.ext
  rw [coe_incF, coe_incF, coe_algFin, coe_algebraMap_FF]

theorem infR_pair {i m : ℕ} [Fact (lev i ∣ lev m)] (a : Rinf (Lc Fq Ω (lev i)) (Fc Fq F Ω (lev i))) :
    letI := algInf (isConstExt_pair Fq F Ω hk (n := lev i) (N := lev m))
    infR Fq F Ω m (algebraMap _ (Rinf (Lc Fq Ω (lev m)) (Fc Fq F Ω (lev m))) a) = infR Fq F Ω i a := by
  letI := algInf (isConstExt_pair Fq F Ω hk (n := lev i) (N := lev m))
  apply Subtype.ext
  rw [coe_infR, coe_infR]
  apply Subtype.ext
  rw [coe_incF, coe_incF, coe_algInf, coe_algebraMap_FF]

include hk in
/-- **`Rfin(F-bar)` is integral over the level ring** `Rfin(F_{lev j})`. -/
theorem isIntegral_finR (j : ℕ) :
    letI := (finR Fq F Ω j).toAlgebra
    Algebra.IsIntegral (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := by
  letI := (finR Fq F Ω j).toAlgebra
  refine ⟨fun z => ?_⟩
  obtain ⟨j1, y, rfl⟩ := exists_finR Fq F Ω z
  obtain ⟨m, hjm, hj1m⟩ : ∃ m, j ≤ m ∧ j1 ≤ m := ⟨max j j1, le_max_left _ _, le_max_right _ _⟩
  haveI : Fact (lev j ∣ lev m) := ⟨lev_dvd_lev hjm⟩
  haveI : Fact (lev j1 ∣ lev m) := ⟨lev_dvd_lev hj1m⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Rfin (Lc Fq Ω (lev m)) (Fc Fq F Ω (lev m)), finR Fq F Ω m y' = finR Fq F Ω j1 y :=
    ⟨_, finR_pair Fq F Ω hk (i := j1) (m := m) y⟩
  rw [← hy']
  letI := algFin (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev m))
  haveI := isIntegral_algFin (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev m))
  refine IsIntegral.map_of_comp_eq (RingHom.id _) (finR Fq F Ω m) (RingHom.ext fun a => ?_)
    (Algebra.IsIntegral.isIntegral y')
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply, RingHom.algebraMap_toAlgebra]
  exact (finR_pair Fq F Ω hk a).symm

include hk in
/-- **`Rinf(F-bar)` is integral over the level ring** `Rinf(F_{lev j})`. -/
theorem isIntegral_infR (j : ℕ) :
    letI := (infR Fq F Ω j).toAlgebra
    Algebra.IsIntegral (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) := by
  letI := (infR Fq F Ω j).toAlgebra
  refine ⟨fun z => ?_⟩
  obtain ⟨j1, y, rfl⟩ := exists_infR Fq F Ω z
  obtain ⟨m, hjm, hj1m⟩ : ∃ m, j ≤ m ∧ j1 ≤ m := ⟨max j j1, le_max_left _ _, le_max_right _ _⟩
  haveI : Fact (lev j ∣ lev m) := ⟨lev_dvd_lev hjm⟩
  haveI : Fact (lev j1 ∣ lev m) := ⟨lev_dvd_lev hj1m⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Rinf (Lc Fq Ω (lev m)) (Fc Fq F Ω (lev m)), infR Fq F Ω m y' = infR Fq F Ω j1 y :=
    ⟨_, infR_pair Fq F Ω hk (i := j1) (m := m) y⟩
  rw [← hy']
  letI := algInf (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev m))
  haveI := isIntegral_algInf (isConstExt_pair Fq F Ω hk (n := lev j) (N := lev m))
  refine IsIntegral.map_of_comp_eq (RingHom.id _) (infR Fq F Ω m) (RingHom.ext fun a => ?_)
    (Algebra.IsIntegral.isIntegral y')
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply, RingHom.algebraMap_toAlgebra]
  exact (infR_pair Fq F Ω hk a).symm

/-- Contraction of finite places of `F-bar` to the level `lev j`. -/
noncomputable def contFinB (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) :
    HeightOneSpectrum (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :=
  letI := (finR Fq F Ω j).toAlgebra
  haveI := isIntegral_finR Fq F Ω hk j
  w.under _

/-- Contraction of the places of `F-bar` over `∞` to the level `lev j`. -/
noncomputable def contInfB (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) :
    HeightOneSpectrum (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :=
  letI := (infR Fq F Ω j).toAlgebra
  haveI := isIntegral_infR Fq F Ω hk j
  w.under _

theorem asIdeal_contFinB (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) :
    (contFinB Fq F Ω hk j w).asIdeal = w.asIdeal.comap (finR Fq F Ω j) := by
  letI := (finR Fq F Ω j).toAlgebra
  haveI := isIntegral_finR Fq F Ω hk j
  show (w.under _).asIdeal = _
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, RingHom.algebraMap_toAlgebra]

theorem mem_contFinB (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω)))
    (a : Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    a ∈ (contFinB Fq F Ω hk j w).asIdeal ↔ finR Fq F Ω j a ∈ w.asIdeal := by
  rw [asIdeal_contFinB, Ideal.mem_comap]

theorem asIdeal_contInfB (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) :
    (contInfB Fq F Ω hk j w).asIdeal = w.asIdeal.comap (infR Fq F Ω j) := by
  letI := (infR Fq F Ω j).toAlgebra
  haveI := isIntegral_infR Fq F Ω hk j
  show (w.under _).asIdeal = _
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, RingHom.algebraMap_toAlgebra]

theorem mem_contInfB (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω)))
    (a : Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    a ∈ (contInfB Fq F Ω hk j w).asIdeal ↔ infR Fq F Ω j a ∈ w.asIdeal := by
  rw [asIdeal_contInfB, Ideal.mem_comap]

/-- **Contraction** of places of `F-bar` to the level `F_{lev j}`. -/
noncomputable def contB (j : ℕ) :
    Places.Place (kbar Fq Ω) (Fbar Fq F Ω) → Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) :=
  Sum.map (contFinB Fq F Ω hk j) (contInfB Fq F Ω hk j)

theorem contB_inl (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) :
    contB Fq F Ω hk j (Sum.inl w) = Sum.inl (contFinB Fq F Ω hk j w) := rfl

theorem contB_inr (j : ℕ) (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) :
    contB Fq F Ω hk j (Sum.inr w) = Sum.inr (contInfB Fq F Ω hk j w) := rfl

theorem isLeft_contB (j : ℕ) (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    (contB Fq F Ω hk j P).isLeft = P.isLeft := by
  rcases P with w | w
  · rw [contB_inl, Sum.isLeft_inl, Sum.isLeft_inl]
  · rw [contB_inr, Sum.isLeft_inr, Sum.isLeft_inr]

theorem contractNN_inl {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]
    (v : HeightOneSpectrum (Rfin (Lc Fq Ω N) (Fc Fq F Ω N))) :
    contractNN Ω hk n N (Sum.inl v) = Sum.inl (contFin (isConstExt_pair Fq F Ω hk (n := n) (N := N)) v) := rfl

theorem contractNN_inr {n N : ℕ} [NeZero n] [NeZero N] [Fact (n ∣ N)]
    (v : HeightOneSpectrum (Rinf (Lc Fq Ω N) (Fc Fq F Ω N))) :
    contractNN Ω hk n N (Sum.inr v) = Sum.inr (contInf (isConstExt_pair Fq F Ω hk (n := n) (N := N)) v) := rfl

/-- **Compatibility** with the contractions between levels. -/
theorem contractNN_contB {i j : ℕ} [Fact (lev i ∣ lev j)] (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    contractNN Ω hk (lev i) (lev j) (contB Fq F Ω hk j P) = contB Fq F Ω hk i P := by
  rcases P with w | w
  · rw [contB_inl, contB_inl, contractNN_inl]
    congr 1
    apply HeightOneSpectrum.ext
    rw [asIdeal_contFin, asIdeal_contFinB, asIdeal_contFinB, Ideal.comap_comap]
    congr 1
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply]
    exact finR_pair Fq F Ω hk a
  · rw [contB_inr, contB_inr, contractNN_inr]
    congr 1
    apply HeightOneSpectrum.ext
    rw [asIdeal_contInf, asIdeal_contInfB, asIdeal_contInfB, Ideal.comap_comap]
    congr 1
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply]
    exact infR_pair Fq F Ω hk a

/-- **Lying over**: every place of a level is a contraction of a place of `F-bar`. -/
theorem exists_contB_eq (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    ∃ P, contB Fq F Ω hk j P = Q := by
  rcases Q with v | v
  · letI := (finR Fq F Ω j).toAlgebra
    letI : Module (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
    haveI := isIntegral_finR Fq F Ω hk j
    haveI : Module.IsTorsionFree (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (by
        rw [RingHom.algebraMap_toAlgebra]; exact finR_injective Fq F Ω j)
    obtain ⟨w, hw⟩ := RamanujanPetersson.PicDescent.exists_under_eq (B := Rfin (kbar Fq Ω) (Fbar Fq F Ω)) v
    exact ⟨Sum.inl w, by rw [contB_inl]; exact congrArg Sum.inl hw⟩
  · letI := (infR Fq F Ω j).toAlgebra
    letI : Module (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
    haveI := isIntegral_infR Fq F Ω hk j
    haveI : Module.IsTorsionFree (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (by
        rw [RingHom.algebraMap_toAlgebra]; exact infR_injective Fq F Ω j)
    obtain ⟨w, hw⟩ := RamanujanPetersson.PicDescent.exists_under_eq (B := Rinf (kbar Fq Ω) (Fbar Fq F Ω)) v
    exact ⟨Sum.inr w, by rw [contB_inr]; exact congrArg Sum.inr hw⟩

/-- **Finite fibres** of the contraction. -/
theorem finite_contB (j : ℕ) (Q : Places.Place (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    {P | contB Fq F Ω hk j P = Q}.Finite := by
  rcases Q with v | v
  · letI := (finR Fq F Ω j).toAlgebra
    letI : Module (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
    haveI := isIntegral_finR Fq F Ω hk j
    haveI : Module.IsTorsionFree (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (by
        rw [RingHom.algebraMap_toAlgebra]; exact finR_injective Fq F Ω j)
    refine ((RamanujanPetersson.PicDescent.finite_under (B := Rfin (kbar Fq Ω) (Fbar Fq F Ω)) v).image
      Sum.inl).subset ?_
    rintro (w | w) hw
    · rw [Set.mem_setOf_eq, contB_inl] at hw
      exact ⟨w, Sum.inl.inj hw, rfl⟩
    · rw [Set.mem_setOf_eq, contB_inr] at hw
      exact absurd hw Sum.inr_ne_inl
  · letI := (infR Fq F Ω j).toAlgebra
    letI : Module (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
    haveI := isIntegral_infR Fq F Ω hk j
    haveI : Module.IsTorsionFree (Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rinf (kbar Fq Ω) (Fbar Fq F Ω)) :=
      Module.isTorsionFree_iff_algebraMap_injective.2 (by
        rw [RingHom.algebraMap_toAlgebra]; exact infR_injective Fq F Ω j)
    refine ((RamanujanPetersson.PicDescent.finite_under (B := Rinf (kbar Fq Ω) (Fbar Fq F Ω)) v).image
      Sum.inr).subset ?_
    rintro (w | w) hw
    · rw [Set.mem_setOf_eq, contB_inl] at hw
      exact absurd hw Sum.inl_ne_inr
    · rw [Set.mem_setOf_eq, contB_inr] at hw
      exact ⟨w, Sum.inr.inj hw, rfl⟩

end Cont

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_BrO =====
section

/-!
# S4-JacFrob, part BrO (bridge 3): `F-bar / F_{lev j}` is unramified

* generic: `ord_liesOver_mul` (`ord_w (x) = e(w | v) · ord_v x` for `w` over `v`, from Mathlib `valuation_liesOver`);
* `ord_contFinB_mul`, `ord_contInfB_mul` (the same for the contraction to a level);
* `placeOrd_inl_bar/inr_bar` (`Place.ord` on `F-bar`, which has no `Fintype` constants);
* **`ord_contFinB`, `ord_contInfB`, `ord_contB`**: `ord_{contB j P} f = ord_P f` for `f ∈ F_{lev j}` (a uniformizer of
  `P` lies in some level `M`, forcing `e = 1` there, and the levels are unramified over each other).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section GenOrd

variable {A K : Type*} (L : Type*) {B : Type*}
variable [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]
variable [Field K] [Field L] [Algebra K L]
variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

theorem ord_liesOver_mul (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    (x : K) : Places.ord w (algebraMap K L x) = (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * Places.ord v x := by
  simp only [Places.ord]
  rw [← HeightOneSpectrum.valuation_liesOver L v w x, WithZero.log_pow, nsmul_eq_mul, mul_neg]

end GenOrd

section Unram

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

theorem ord_contFinB_mul (j : ℕ) (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) (f : Fc Fq F Ω (lev j)) :
    letI := (finR Fq F Ω j).toAlgebra
    Places.ord w (incF Fq F Ω j f) =
      ((contFinB Fq F Ω hk j w).asIdeal.ramificationIdx' w.asIdeal : ℤ) * Places.ord (contFinB Fq F Ω hk j w) f := by
  letI := (finR Fq F Ω j).toAlgebra
  letI : Module (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toModule
  haveI := isIntegral_finR Fq F Ω hk j
  haveI : Module.IsTorsionFree (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (by
      rw [RingHom.algebraMap_toAlgebra]; exact finR_injective Fq F Ω j)
  letI : Algebra (Fc Fq F Ω (lev j)) (Fbar Fq F Ω) := (incF Fq F Ω j).toAlgebra
  letI : Algebra (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fbar Fq F Ω) :=
    ((incF Fq F Ω j).comp (algebraMap (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fc Fq F Ω (lev j)))).toAlgebra
  letI : SMul (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) := Algebra.toSMul
  letI : SMul (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fbar Fq F Ω) := Algebra.toSMul
  letI : SMul (Fc Fq F Ω (lev j)) (Fbar Fq F Ω) := Algebra.toSMul
  letI : SMul (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fc Fq F Ω (lev j)) := Algebra.toSMul
  haveI : IsScalarTower (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Fc Fq F Ω (lev j)) (Fbar Fq F Ω) :=
    IsScalarTower.of_algebraMap_eq' (by rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra])
  haveI : IsScalarTower (Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) (Rfin (kbar Fq Ω) (Fbar Fq F Ω)) (Fbar Fq F Ω) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      refine RingHom.ext fun a => ?_
      rw [RingHom.comp_apply, RingHom.comp_apply]
      exact (coe_finR Fq F Ω j a).symm)
  haveI : w.asIdeal.LiesOver (contFinB Fq F Ω hk j w).asIdeal :=
    ⟨by rw [asIdeal_contFinB, Ideal.under_def, RingHom.algebraMap_toAlgebra]⟩
  have h := ord_liesOver_mul (Fbar Fq F Ω) (contFinB Fq F Ω hk j w) w f
  rw [RingHom.algebraMap_toAlgebra] at h
  exact h

theorem placeOrd_inl_bar (w : HeightOneSpectrum (Rfin (kbar Fq Ω) (Fbar Fq F Ω))) (f : Fbar Fq F Ω) :
    Places.Place.ord (Sum.inl w : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) f = Places.ord w f := rfl

theorem placeOrd_inr_bar (w : HeightOneSpectrum (Rinf (kbar Fq Ω) (Fbar Fq F Ω))) (f : Fbar Fq F Ω) :
    Places.Place.ord (Sum.inr w : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) f = Places.ord w f := rfl

end Unram

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_JacFrob_BrD =====
section

/-!
# S4-JacFrob, part BrD (bridge 4): degree-1 places, separation, fibre count

* generic: `deg_eq_one_of_const` (a place all of whose residues are constants has degree `1`),
  `exists_const_of_isAlgClosed` (over an algebraically closed field every residue is a constant);
* generic (constant field extensions): `exists_sum_fin/inf` (`A' = Σ L · A`), `const_of_base_fin/inf`;
* `degOne`: every place of `F-bar` contracts to a degree-1 place at all large levels;
* `sepB`, `contB_ne_mono`: places of `F-bar` are separated by their contractions;
* `uniqB`, `fibreB`, `exists_fibreB_singleton`: over a degree-1 level place there is exactly one place of `F-bar`;
* **`card_fibreB`**: `#{P | contB j P = Q} = deg Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section GenDeg

variable {L : Type*} [Field L] {A : Type*} [CommRing A] [IsDedekindDomain A] [Algebra L A]

theorem exists_not_mem_of_ne {w1 w2 : HeightOneSpectrum A} (h : w1 ≠ w2) :
    ∃ z ∈ w1.asIdeal, z ∉ w2.asIdeal := by
  by_contra hc
  push_neg at hc
  exact h (HeightOneSpectrum.ext (w1.isMaximal.eq_of_le w2.isPrime.ne_top hc))

end GenDeg

section Gen

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {L : Type*} [Field L] [Fintype L] [Algebra Fq L] [DecidableEq (RatFunc L)]
variable {F' : Type*} [Field F'] [Algebra L F'] [Algebra L[X] F'] [Algebra (RatFunc L) F']
  [IsScalarTower L[X] (RatFunc L) F'] [IsScalarTower L L[X] F'] [FunctionField L F']
  [Algebra.IsSeparable (RatFunc L) F']
variable [Algebra F F'] [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
variable {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
variable (h : RR.IsConstExt Fq F L F' c)

end Gen

section DegOne

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

end DegOne

end RamanujanPetersson.JacFrob


end

-- ===== S4.Def_RP_DegPoly =====
section

/-!
# Degree polynomiality (unit S4-DegPoly, lemma L37 of `S4_COREB_ROUTE.md`)

Milne, *Abelian Varieties*, Lemma 10.12 and Prop. 10.13, in hypothesis form and over pure algebra.

`I` is a `g`-linear integer form on an abelian group `M` (the intersection form on divisors of an abelian variety of
dimension `g`), `c : R → M` sends an endomorphism `a` to the class `a^* D` of a divisor `D = c 1`, and
`deg : R → ℕ` is the degree. Two classes are *numerically equivalent* when their difference lies in `numKer I`.
Assume
* `(D^g) ≠ 0`;
* the projection formula `((a^* D)^g) = deg a · (D^g)`;
* the quadratic relation `(n a + b)^* D ≡ n² a^* D + n e(a, b) + b^* D` for all `a, b` (this is where `D` symmetric
  enters), and `0^* D ≡ 0`.
Then `n ↦ deg (n a + b)` is a polynomial of degree `≤ 2g` with rational coefficients, and `deg n = n ^ (2g)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.DegPoly

open Polynomial

variable {M : Type*} [AddCommGroup M] {g : ℕ}

/-- The numerical kernel of a `g`-linear form: the classes `u` with `I (w₁, …, u, …, w_g) = 0` in every slot. -/
def numKer (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ) : AddSubgroup M where
  carrier := {u | ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i u) = 0}
  zero_mem' := fun w i => I.map_update_zero w i
  add_mem' {u v} hu hv w i := by
    have hu' : ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i u) = 0 := hu
    have hv' : ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i v) = 0 := hv
    rw [I.map_update_add, hu' w i, hv' w i, add_zero]
  neg_mem' {u} hu w i := by
    have hu' : ∀ (w : Fin g → M) (i : Fin g), I (Function.update w i u) = 0 := hu
    rw [I.map_update_neg, hu' w i, neg_zero]

variable (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ)

variable {R : Type*} [Ring R]

end RamanujanPetersson.DegPoly


end


