-- Prove2me | Definitions.Def_RPLib_S4_CDPack43b
-- name    : RPLib_S4_CDPack43b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:31:35.393662+00:00
-- url     : https://prove2.me/theorems/6a72c0ae-a25b-424d-bf3d-fb4d3e324110
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 43b of 71
-- statement:
--   Part 43b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
--   * `Def_RP_CoreB_Dim`: Core B, O1: the heights on the Jacobian are bounded
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack43
import Definitions.Def_RPLib_S4_CDPack31
import Definitions.Def_RPLib_S4_CDPack42b

/-!
# Curve-duality library package, part 43b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacComplete_Proper`: The Jacobian (unit S4-JacComplete), part `Proper`: **L19, the Jacobian is proper**
* `Def_RP_CoreB_Dim`: Core B, O1: the heights on the Jacobian are bounded
-/

set_option autoImplicit false

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

variable (K F) in
/-- `X1` as an object over `Spec K`. -/
noncomputable abbrev X1O : Over (Spec (.of K)) := Over.mk (toSpecK K (algebraMap K[X] F X) 1)

variable (K F) in
/-- The chart `A` of `X1` as a map over `Spec K`. -/
noncomputable def ιO (A : (ChartIdx K)ᵒᵖ) :
    specO K (SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) ⟶ X1O K F :=
  Over.homMk (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A) (ι_toSpecK K _ 1 A)

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

variable (K F) in
/-- `X1^n` over `Spec K`. -/
noncomputable def PP : ℕ → Over (Spec (.of K))
  | 0 => 𝟙_ (Over (Spec (.of K)))
  | n + 1 => PP n ⊗ X1O K F

instance isProper_PP (n : ℕ) : IsProper (PP K F n).hom := by
  induction n with
  | zero =>
    show IsProper (𝟙 (Spec (.of K)))
    infer_instance
  | succ n ih =>
    haveI : IsProper (toSpecK K (algebraMap K[X] F X) 1) := inferInstance
    show IsProper (pullback.fst (PP K F n).hom (toSpecK K (algebraMap K[X] F X) 1) ≫ (PP K F n).hom)
    infer_instance

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

instance universallyClosed_PhiN (n : ℕ) : UniversallyClosed (PhiN P0 n).left := by
  haveI : UniversallyClosed ((PhiN P0 n).left ≫ (Jac K F).hom) := by
    rw [Over.w (PhiN P0 n)]; infer_instance
  exact UniversallyClosed.of_comp_of_isSeparated (PhiN P0 n).left (Jac K F).hom

/-- **`Φ_g` is surjective.** -/
theorem surjective_PhiN : Function.Surjective (PhiN P0 (genusFK K F)).left := by
  haveI : JacobsonSpace (Jac K F).left := LocallyOfFiniteType.jacobsonSpace (Jac K F).hom
  have hcl : closedPoints (Jac K F).left ⊆ Set.range (PhiN P0 (genusFK K F)).left := by
    intro j hj
    let a : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
      Over.homMk (pointOfClosedPoint (Jac K F).hom j hj) (pointOfClosedPoint_comp _ _ _)
    obtain ⟨t, ht⟩ := exists_eff_rep P0 (Multiplicative.toAdd (jacPicEquiv K F a)).2
    obtain ⟨p, hp⟩ := exists_pt P0 (genusFK K F) t
    have hs : ((∑ i, ajCls K F P0 (t i) : Pic0K K F) : PicK K F) =
        ((Multiplicative.toAdd (jacPicEquiv K F a) : Pic0K K F) : PicK K F) := by
      rw [ht, AddSubmonoidClass.coe_finsetSum]
      show ∑ i, (clsK K F (Finsupp.single (t i) 1) - clsK K F (Finsupp.single P0 1)) = _
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, natCast_zsmul]
    have e : p ≫ PhiN P0 (genusFK K F) = a := by
      apply (jacPicEquiv K F).injective
      rw [hp, show (∑ i, ajCls K F P0 (t i)) = Multiplicative.toAdd (jacPicEquiv K F a) from Subtype.ext hs]
      rfl
    refine ⟨p.left (IsLocalRing.closedPoint K), ?_⟩
    have h2 : (p ≫ PhiN P0 (genusFK K F)).left (IsLocalRing.closedPoint K) = j := by
      rw [e]
      exact pointOfClosedPoint_apply (Jac K F).hom j hj _
    exact h2
  have h := closure_minimal hcl (PhiN P0 (genusFK K F)).left.isClosedMap.isClosed_range
  rw [closure_closedPoints] at h
  exact fun j => h (Set.mem_univ j)

variable (K F) in
/-- **L19: the Jacobian is proper over `K`.** -/
instance isProper_Jac : IsProper (Jac K F).hom := by
  obtain ⟨Q⟩ := PlacesK.nonempty_infPlace K F
  haveI hs : Surjective (PhiN (Sum.inr Q : Place K F) (genusFK K F)).left := ⟨surjective_PhiN _⟩
  haveI : UniversallyClosed ((PhiN (Sum.inr Q : Place K F) (genusFK K F)).left ≫ (Jac K F).hom) := by
    rw [Over.w (PhiN (Sum.inr Q : Place K F) (genusFK K F))]; infer_instance
  haveI := UniversallyClosed.of_comp_surjective (PhiN (Sum.inr Q : Place K F) (genusFK K F)).left (Jac K F).hom
  exact {}

end Proper

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_CoreB_Dim =====
section

/-!
# Core B, O1: the heights on the Jacobian are bounded

* `ringKrullDim_le_of_finiteType`: a finite type algebra over a field has finite Krull dimension.
* `exists_coheight_le_of_isAffineOpen`: on an affine open of a scheme locally of finite type over a field,
  the coheights are bounded.
* `exists_height_le`: a quasi-compact scheme locally of finite type over a field has bounded heights
  (for the specialization order).
* `exists_height_max`: a bound on heights is attained by a least bound `g`.
* `exists_dim_Jac`: `∃ g, (∀ x, height x ≤ g) ∧ ∃ x, g ≤ height x` on `Jac K F`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open CategoryTheory AlgebraicGeometry Order

universe u

lemma ringKrullDim_le_of_finiteType {K B : Type*} [Field K] [CommRing B] (φ : K →+* B)
    (hφ : φ.FiniteType) : ∃ n : ℕ, ringKrullDim B ≤ n := by
  let _ := φ.toAlgebra
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hφ
  refine ⟨n, (ringKrullDim_le_of_surjective f.toRingHom hf).trans ?_⟩
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

lemma exists_coheight_le_of_isAffineOpen {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ n : ℕ, ∀ x ∈ U, coheight x ≤ n := by
  have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
    (HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType) (f := f)).1 inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have hs : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective
  obtain ⟨n, hn⟩ := ringKrullDim_le_of_finiteType _
    (h1.comp (RingHom.FiniteType.of_surjective _ hs))
  refine ⟨n, fun x hx => ?_⟩
  rw [← SetLike.mem_coe, ← hU.range_fromSpec] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [coheight_eq_of_isOpenImmersion hU.fromSpec, ← idealHeight_eq_coheight]
  have : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  have h2 := (Ideal.height_le_ringKrullDim_of_isPrime (I := y.asIdeal)).trans hn
  exact_mod_cast h2

lemma exists_height_le {X : Scheme.{u}} {K : Type u} [Field K] [CompactSpace X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] : ∃ N : ℕ, ∀ x : X, height x ≤ N := by
  have hV : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) := fun x => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hxU⟩
  choose V hxV using hV
  choose n hn using fun x => exists_coheight_le_of_isAffineOpen f (V x).2
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => ((V x : X.Opens) : Set X))
    (fun x => (V x : X.Opens).isOpen.mem_nhds (hxV x))
  have hcoh : ∀ x : X, coheight x ≤ (t.sup n : ℕ) := fun x => by
    have hx : x ∈ ⋃ y ∈ t, ((V y : X.Opens) : Set X) := by rw [ht]; trivial
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact (hn y x hxy).trans (by exact_mod_cast Finset.le_sup (f := n) hy)
  refine ⟨t.sup n, fun x => ?_⟩
  have h1 : krullDim X ≤ (t.sup n : ℕ) := by
    rw [krullDim_eq_iSup_coheight]
    exact iSup_le fun a => by exact_mod_cast hcoh a
  have h2 := (height_le_krullDim x).trans h1
  exact_mod_cast h2

lemma exists_height_max {α : Type*} [Preorder α] [Nonempty α] (N : ℕ) (h : ∀ x : α, height x ≤ N) :
    ∃ g : ℕ, (∀ x : α, height x ≤ g) ∧ ∃ x : α, (g : ℕ∞) ≤ height x := by
  let S : Set ℕ := {n | ∃ x : α, (n : ℕ∞) ≤ height x}
  have hbdd : BddAbove S := ⟨N, fun n ⟨x, hx⟩ => by exact_mod_cast hx.trans (h x)⟩
  have h0 : S.Nonempty := ⟨0, Classical.arbitrary α, by simp⟩
  refine ⟨sSup S, fun x => ?_, Nat.sSup_mem h0 hbdd⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, height x = k :=
    ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top N) (h x)) |>.imp fun _ h => h.symm
  rw [hk]
  exact_mod_cast le_csSup hbdd ⟨x, hk.ge⟩

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

open RamanujanPetersson.JacComplete in
theorem exists_dim_Jac :
    ∃ g : ℕ, (∀ x : (Jac K F).left, height x ≤ g) ∧ ∃ x : (Jac K F).left, (g : ℕ∞) ≤ height x := by
  have : CompactSpace (Jac K F).left := QuasiCompact.compactSpace_of_compactSpace (Jac K F).hom
  obtain ⟨N, hN⟩ := exists_height_le (Jac K F).hom
  exact exists_height_max N hN

end RamanujanPetersson.CoreB

end


