-- Prove2me | Definitions.Def_RPLib_S4_CDPack42b
-- name    : RPLib_S4_CDPack42b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:50:12.448051+00:00
-- url     : https://prove2.me/theorems/5494f8f9-f399-4482-a372-4650dff67ff6
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 42b of 71
-- statement:
--   Part 42b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacSymB_Sep`: S4-JacSymB, file H1: `Sym^g X → Spec k` is separated (L12)
--   * `Def_RP_JacSymB_ExistAlg`: S4-JacSymB, file H2c: ring-level valuative existence for `Sym^g X` (L12)
--   * `Def_RP_JacSymB_Exist`: S4-JacSymB, file H2c': `Sym^g X → Spec k` is universally closed and proper (L12)
--   * `Def_RP_ThetaSquare_CPullOpen`: S4-ThetaSquare, file CPullOpen: `cpull` along open immersions, and monotonicity (F4)
--   * `Def_RP_ThetaCube_Val`: S4-ThetaCube, file Val (D-C1, part 1): values of rational functions at `K`-points
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack42
import Definitions.Def_RPLib_S4_CDPack25
import Definitions.Def_RPLib_S4_CDPack37
import Definitions.Def_RPLib_S4_CDPack38

/-!
# Curve-duality library package, part 42b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacSymB_Sep`: S4-JacSymB, file H1: `Sym^g X → Spec k` is separated (L12)
* `Def_RP_JacSymB_ExistAlg`: S4-JacSymB, file H2c: ring-level valuative existence for `Sym^g X` (L12)
* `Def_RP_JacSymB_Exist`: S4-JacSymB, file H2c': `Sym^g X → Spec k` is universally closed and proper (L12)
* `Def_RP_ThetaSquare_CPullOpen`: S4-ThetaSquare, file CPullOpen: `cpull` along open immersions, and monotonicity (F4)
* `Def_RP_ThetaCube_Val`: S4-ThetaCube, file Val (D-C1, part 1): values of rational functions at `K`-points
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacSymB_Sep =====
section

/-!
# S4-JacSymB, file H1: `Sym^g X → Spec k` is separated (L12)

Template: Mathlib `ProjectiveSpectrum/Proper.lean` (`isSeparated`). For charts `A, A'` the overlap of `Spec S_A` and
`Spec S_A'` in `Sym^g X` is `Spec S_{A ∪ A'}` (`isPullback_ι_ι`, from `ι_eq_ι_iff`), and
`S_A ⊗_k S_A' → S_{A ∪ A'}` is surjective: `S_{A ∪ A'} = S_A[1/N w]` and `1/N w = N(1/w)` comes from `S_A'`.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite Limits

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

section SepAlg

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F} {g : ℕ}

omit [Field k] in
theorem sdiff_subset_union_right [DecidableEq k] (A A' : Finset k) : (A ∪ A') \ A ⊆ A' := by
  intro d hd
  rw [Finset.mem_sdiff, Finset.mem_union] at hd
  tauto

theorem chartMap_normS_inv_mul [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} {c0 : k} (hc0 : c0 ∈ A) :
    chartMap x g (Finset.subset_union_right : A' ⊆ A ∪ A')
      (normS k (⟨(wt x c0 ((A ∪ A') \ A))⁻¹, wt_inv_mem_chartRing hx (sdiff_subset_union_right A A') c0⟩ :
        chartRing x A')) *
    chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A')
      (normS k (⟨wt x c0 ((A ∪ A') \ A), wt_mem_chartRing hx hc0 _⟩ : chartRing x A)) = 1 := by
  rw [chartMap, chartMap, symMap_normS, symMap_normS, ← normS_mul, ← normS_one (k := k) (g := g)]
  congr 1
  apply Subtype.ext
  simp only [Subalgebra.coe_inclusion, MulMemClass.coe_mul, OneMemClass.coe_one]
  exact inv_mul_cancel₀ (wt_ne_zero hx c0 _)

theorem lift_chartMap_surjective [DecidableEq k] (hx : Transcendental k x) {A A' : Finset k} (hA : A.Nonempty) :
    Function.Surjective (Algebra.TensorProduct.lift (chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A'))
      (chartMap x g (Finset.subset_union_right : A' ⊆ A ∪ A')) (fun _ _ => Commute.all _ _)) := by
  obtain ⟨c0, hc0⟩ := hA
  let _ := (chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A')).toRingHom.toAlgebra
  have _ := isLocalization_chartMap (g := g) hx (Finset.subset_union_left : A ⊆ A ∪ A') hc0
  intro z
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Submonoid.powers (normS k (g := g)
    (⟨wt x c0 ((A ∪ A') \ A), wt_mem_chartRing hx hc0 _⟩ : chartRing x A))) z
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp s.2
  change z * chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A') s =
    chartMap x g (Finset.subset_union_left : A ⊆ A ∪ A') a at h
  rw [← hn, map_pow] at h
  refine ⟨a ⊗ₜ ((normS k (⟨(wt x c0 ((A ∪ A') \ A))⁻¹, wt_inv_mem_chartRing hx (sdiff_subset_union_right A A') c0⟩ :
        chartRing x A')) ^ n), ?_⟩
  have h1 := chartMap_normS_inv_mul (g := g) (A' := A') hx hc0
  rw [mul_comm] at h1
  simp only [Algebra.TensorProduct.lift_tmul, map_pow]
  rw [← h, mul_assoc, ← mul_pow, h1, one_pow, mul_one]

end SepAlg

section SepScheme

universe u

variable (k : Type u) [Field k] {F : Type u} [Field F] [Algebra k F] (x : F) (g : ℕ) [hx : Fact (Transcendental k x)]

/-- The chart `A ∪ A'`, i.e. the overlap of the charts `A` and `A'`. -/
abbrev unionIdx [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) : ChartIdx k :=
  ⟨i.unop.1 ∪ j.unop.1, i.unop.2.mono Finset.subset_union_left⟩

omit hx in
theorem symDiagram_map {i j : (ChartIdx k)ᵒᵖ} (f : i ⟶ j) :
    (symDiagram k x g).map f = Spec.map (CommRingCat.ofHom (chartMap x g (leOfHom f.unop)).toRingHom) :=
  rfl

theorem isPullback_ι_ι [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) :
    IsPullback ((symDiagram k x g).map (homOfLE (show i.unop ≤ unionIdx k i j from Finset.subset_union_left)).op)
      ((symDiagram k x g).map (homOfLE (show j.unop ≤ unionIdx k i j from Finset.subset_union_right)).op)
      (colimit.ι (symDiagram k x g) i) (colimit.ι (symDiagram k x g) j) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by rw [colimit.w, colimit.w]) ?_
  apply TopologicalSpace.Opens.ext
  ext P
  simp only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange, Set.mem_preimage, Set.mem_range]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨l, fi, fj, y, hy1, hy2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (symDiagram k x g)).mp hq
    have hU : unionIdx k i j ≤ l.unop := Finset.union_subset (leOfHom fi.unop) (leOfHom fj.unop)
    refine ⟨(symDiagram k x g).map (homOfLE hU).op y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    have e : (homOfLE hU).op ≫ (homOfLE (show j.unop ≤ unionIdx k i j from Finset.subset_union_right)).op = fj :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [e, hy2]
  · rintro ⟨y, rfl⟩
    exact ⟨(symDiagram k x g).map (homOfLE (show i.unop ≤ unionIdx k i j from Finset.subset_union_left)).op y, by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, colimit.w, colimit.w]⟩

/-- `S_A ⊗_k S_A' → S_{A ∪ A'}` (surjective, `lift_chartMap_surjective`). -/
noncomputable def overlapHom [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) :
    CommRingCat.of (SymRing k (chartRing x i.unop.1) g ⊗[k] SymRing k (chartRing x j.unop.1) g) ⟶
      CommRingCat.of (SymRing k (chartRing x (i.unop.1 ∪ j.unop.1)) g) :=
  CommRingCat.ofHom (Algebra.TensorProduct.lift (chartMap x g (Finset.subset_union_left : i.unop.1 ⊆ i.unop.1 ∪ j.unop.1))
    (chartMap x g (Finset.subset_union_right : j.unop.1 ⊆ i.unop.1 ∪ j.unop.1)) (fun _ _ => Commute.all _ _)).toRingHom

omit hx in
theorem overlap_fst [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) :
    (symDiagram k x g).map (homOfLE (show i.unop ≤ unionIdx k i j from Finset.subset_union_left)).op =
      Spec.map (CommRingCat.ofHom ((overlapHom k x g i j).hom.comp Algebra.TensorProduct.includeLeftRingHom)) := by
  rw [symDiagram_map]
  congr 1
  ext a
  simp [overlapHom]

omit hx in
theorem overlap_snd [DecidableEq k] (i j : (ChartIdx k)ᵒᵖ) :
    (symDiagram k x g).map (homOfLE (show j.unop ≤ unionIdx k i j from Finset.subset_union_right)).op =
      Spec.map (CommRingCat.ofHom ((overlapHom k x g i j).hom.comp (Algebra.TensorProduct.includeRight :
        SymRing k (chartRing x j.unop.1) g →ₐ[k] _).toRingHom)) := by
  rw [symDiagram_map]
  congr 1
  ext a
  simp [overlapHom]

/-- Generic closing step: a map into `Spec S ×_{Spec R} Spec T` that is `Spec` of a surjection `S ⊗_R T → U` on both
factors is a closed immersion. Stated with bare variables so all tensor-product instances are the canonical ones. -/
theorem isClosedImmersion_of_tensor {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R S] [Algebra R T] (F : S ⊗[R] T →+* U) (hF : Function.Surjective F)
    (f : Spec (.of S) ⟶ Spec (.of R)) (f' : Spec (.of T) ⟶ Spec (.of R))
    (hf : f = Spec.map (CommRingCat.ofHom (algebraMap R S))) (hf' : f' = Spec.map (CommRingCat.ofHom (algebraMap R T)))
    {P : Scheme.{u}} (e : P ≅ Spec (.of U)) (m : P ⟶ pullback f f')
    (h1 : m ≫ pullback.fst f f' = e.hom ≫ Spec.map (CommRingCat.ofHom (F.comp Algebra.TensorProduct.includeLeftRingHom)))
    (h2 : m ≫ pullback.snd f f' = e.hom ≫ Spec.map (CommRingCat.ofHom (F.comp
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom))) :
    IsClosedImmersion m := by
  subst hf hf'
  have hm : m = e.hom ≫ Spec.map (CommRingCat.ofHom F) ≫ (pullbackSpecIso R S T).inv := by
    apply pullback.hom_ext
    · rw [h1, Category.assoc, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      rfl
    · rw [h2, Category.assoc, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      rfl
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom F) hF
  rw [hm]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
instance isSeparated_toSpecK : IsSeparated (toSpecK k x g) := by
  classical
  change @IsSeparated (colimit (symDiagram k x g)) _ (toSpecK k x g)
  refine ⟨IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight
    (Scheme.IsLocallyDirected.openCover (symDiagram k x g)) (Scheme.IsLocallyDirected.openCover (symDiagram k x g))
    _ _) ?_⟩
  rintro ⟨(i : (ChartIdx k)ᵒᵖ), (j : (ChartIdx k)ᵒᵖ)⟩
  dsimp [Scheme, Scheme.Cover.pullbackHom]
  refine (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (f := (pullbackDiagonalMapIdIso ..).inv) _).mp ?_
  change IsClosedImmersion ((pullbackDiagonalMapIdIso (colimit.ι (symDiagram k x g) i)
    (colimit.ι (symDiagram k x g) j) (toSpecK k x g)).inv ≫ pullback.snd _ _)
  have hP := isPullback_ι_ι k x g i j
  refine isClosedImmersion_of_tensor (S := SymRing k (chartRing x i.unop.1) g) (T := SymRing k (chartRing x j.unop.1) g)
    (U := SymRing k (chartRing x (i.unop.1 ∪ j.unop.1)) g) (overlapHom k x g i j).hom
    (lift_chartMap_surjective (g := g) hx.out i.unop.2) _ _ (ι_toSpecK k x g i) (ι_toSpecK k x g j)
    hP.isoPullback.symm _ ?_ ?_
  · refine (Category.assoc _ _ _).trans ((pullbackDiagonalMapIdIso_inv_snd_fst _ _ _).trans ?_)
    refine (Iso.eq_inv_comp hP.isoPullback).mpr ?_
    exact hP.isoPullback_hom_fst.trans (overlap_fst k x g i j)
  · refine (Category.assoc _ _ _).trans ((pullbackDiagonalMapIdIso_inv_snd_snd _ _ _).trans ?_)
    refine (Iso.eq_inv_comp hP.isoPullback).mpr ?_
    exact hP.isoPullback_hom_snd.trans (overlap_snd k x g i j)

end SepScheme

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymB_ExistAlg =====
section

/-!
# S4-JacSymB, file H2c: ring-level valuative existence for `Sym^g X` (L12)

Given a ring map `φ : Sym^g B_{c} → K` (`K = Frac O`, `O` a valuation ring) compatible with `μ : k → O`, there is
`d = c + t` such that `φ` extends to `φ' : Sym^g B_{c,d} → K` and `φ' ∘ (Sym^g B_{d} → Sym^g B_{c,d})` lands in `O`.
Proof: `t` from `exists_taylor_integral` applied to `P = φ(E(u_c))`; the Taylor identity `N(1 - t u_c) E(u_d) =
E(u_c)(X + t)` puts the coefficients of `E(u_d)` into `O`; `Sym^g B_d` is integral over them (`exists_monic_genE`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section ExistAlg

open Polynomial

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F} {g : ℕ}

/-- The coordinate `u_c = 1/(x - c)` as an element of the chart ring `B_A` (`c ∈ A`). -/
noncomputable def ucB (x : F) {A : Finset k} {c : k} (hc : c ∈ A) : chartRing x A :=
  ⟨uc x c, polyA_le_chartRing x A (uc_mem_polyA x hc)⟩

/-- Elements of `B_{d}` are integral over `k[u_d]`. -/
theorem hint_chartRing_single (d : k) (b : chartRing x {d}) :
    ∃ p : (Polynomial k)[X], p.Monic ∧
      p.eval₂ (Polynomial.aeval (R := k) (ucB x (Finset.mem_singleton_self d))).toRingHom b = 0 := by
  classical
  let u : polyA x {d} := ⟨uc x d, uc_mem_polyA x (Finset.mem_singleton_self d)⟩
  have hπ : Function.Surjective (Polynomial.aeval (R := k) u).toRingHom := by
    intro y
    have hy : (y : F) ∈ Algebra.adjoin k {uc x d} := by
      rw [← polyA_singleton]
      exact y.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, hp⟩ := (AlgHom.mem_range _).mp hy
    exact ⟨p, Subtype.ext ((Polynomial.aeval_subalgebra_coe p _ u).trans hp)⟩
  obtain ⟨q, hqm, hq⟩ := (mem_chartRing (x := x) (A := {d})).mp b.2
  obtain ⟨p, hpq, -, hpm⟩ := lifts_and_degree_eq_and_monic (mem_lifts_of_surjective hπ q) hqm
  refine ⟨p, hpm, Subtype.val_injective ?_⟩
  have e : (chartRing x {d}).val.toRingHom.comp
      (Polynomial.aeval (R := k) (ucB x (Finset.mem_singleton_self d))).toRingHom =
      (algebraMap (polyA x {d}) F).comp (Polynomial.aeval (R := k) u).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C]
      rfl
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]
      rfl
  change (chartRing x {d}).val.toRingHom (p.eval₂ _ b) = (chartRing x {d}).val.toRingHom 0
  rw [Polynomial.hom_eval₂, e, ← Polynomial.eval₂_map, hpq, map_zero]
  exact hq

theorem genPoly_eval_zero {B : Type*} [CommRing B] [Algebra k B] (w : B) :
    (genPoly (k := k) (g := g) w).eval 0 = 1 := by
  have h := genPoly_eval (k := k) (g := g) w 0
  simp only [map_zero, zero_mul, sub_zero, normS_one] at h
  exact h

variable [DecidableEq k]

theorem wt_pair_eq (hx : Transcendental k x) (c t : k) :
    wt x c ({c, c + t} \ {c}) = 1 - algebraMap k F t * uc x c := by
  by_cases ht : t = 0
  · subst ht
    simp [wt]
  · have hs : ({c, c + t} \ {c} : Finset k) = {c + t} := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · rintro rfl
        exact ⟨Or.inr rfl, fun h => ht (by simpa using h)⟩
    rw [hs, wt_singleton_eq hx, show c - (c + t) = -t by ring, map_neg]
    ring

/-- Ring-level valuative existence: `φ : Sym^g B_{c} → K` extends over `B_{c,d}` with `Sym^g B_{d}` landing in `O`. -/
theorem exists_valuative_lift [Infinite k] (hx : Transcendental k x) (c : k) {O K : Type*} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (μ : k →+* O)
    (φ : SymRing k (chartRing x {c}) g →+* K) (hμ : ∀ a, algebraMap O K (μ a) = φ (algebraMap k _ a)) :
    ∃ (d : k) (φ' : SymRing k (chartRing x {c, d}) g →+* K) (φ'' : SymRing k (chartRing x {d}) g →+* O),
      φ'.comp (chartMap x g (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self c {d}))).toRingHom = φ ∧
      (algebraMap O K).comp φ'' = φ'.comp (chartMap x g (Finset.singleton_subset_iff.mpr
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self d)))).toRingHom ∧
      φ''.comp (algebraMap k _) = μ := by
  set w := ucB x (Finset.mem_singleton_self c) with hw
  set P : K[X] := (genPoly (k := k) (g := g) w).map φ with hP
  have hP0 : P.eval 0 = 1 := by rw [hP, eval_zero_map, genPoly_eval_zero, map_one]
  have hPne : P ≠ 0 := fun h => by
    rw [h, eval_zero] at hP0
    exact zero_ne_one hP0
  obtain ⟨t, hev, hcoef⟩ := exists_taylor_integral μ P hPne
  simp only [hμ] at hev hcoef
  choose o ho using hcoef
  have h1 : ({c} : Finset k) ⊆ {c, c + t} := Finset.singleton_subset_iff.mpr (Finset.mem_insert_self c _)
  have h2 : ({c + t} : Finset k) ⊆ {c, c + t} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  let _ := (chartMap x g h1).toRingHom.toAlgebra
  have := isLocalization_chartMap (g := g) hx h1 (Finset.mem_singleton_self c)
  set Nw := normS k (g := g)
    (⟨wt x c ({c, c + t} \ {c}), wt_mem_chartRing hx (Finset.mem_singleton_self c) _⟩ : chartRing x {c}) with hNdef
  have hNw : Nw = normS k (1 - algebraMap k (chartRing x {c}) t * w) := by
    rw [hNdef]
    congr 1
    exact Subtype.ext ((wt_pair_eq hx c t).trans rfl)
  have hφN : φ Nw = P.eval (φ (algebraMap k _ t)) := by
    rw [hNw, ← genPoly_eval, hP, eval_map, eval₂_hom]
  have hunit : IsUnit (φ Nw) := by
    rw [hφN]
    exact hev.isUnit
  let φ' : SymRing k (chartRing x {c, c + t}) g →+* K := IsLocalization.Away.lift Nw hunit
  have hφ'c : φ'.comp (chartMap x g h1).toRingHom = φ := IsLocalization.Away.lift_comp Nw hunit
  -- the Taylor identity on `B_{c,d}`
  set a := ucB x (h1 (Finset.mem_singleton_self c)) with ha
  set wd := ucB x (Finset.mem_singleton_self (c + t)) with hwd
  set b := ucB x (h2 (Finset.mem_singleton_self (c + t))) with hb
  have hab : (1 - algebraMap k (chartRing x {c, c + t}) t * a) * b = a := by
    apply Subtype.ext
    change (1 - algebraMap k F t * uc x c) * uc x (c + t) = uc x c
    have hc0 := sub_ne_zero_of_tr hx c
    have hd0 := sub_ne_zero_of_tr hx (c + t)
    rw [map_add] at hd0
    simp only [uc, map_add]
    field_simp
    ring
  have hT := congrArg (Polynomial.map φ') (genPoly_taylor (k := k) (g := g) a b t hab)
  have hNa : φ' (normS k (g := g) (1 - algebraMap k (chartRing x {c, c + t}) t * a)) = φ Nw := by
    have e : normS k (g := g) (1 - algebraMap k (chartRing x {c, c + t}) t * a) = chartMap x g h1 Nw := by
      rw [hNw, chartMap, symMap_normS]
      congr 1
    rw [e]
    exact DFunLike.congr_fun hφ'c Nw
  have hPa : (genPoly (k := k) (g := g) a).map φ' = P := by
    have e : genPoly (k := k) (g := g) a = (genPoly w).map (chartMap x g h1).toRingHom :=
      (symMap_genPoly (Subalgebra.inclusion (chartRing_mono x h1)) w).symm
    rw [e, Polynomial.map_map, hφ'c]
  have hlam : φ' (algebraMap k (SymRing k (chartRing x {c, c + t}) g) t) = φ (algebraMap k _ t) := by
    rw [← AlgHom.commutes (chartMap x g h1) t]
    exact DFunLike.congr_fun hφ'c _
  rw [Polynomial.map_mul, map_C, map_taylor, hNa, hPa, hlam, hφN] at hT
  have eb : genPoly (k := k) (g := g) b = (genPoly wd).map (chartMap x g h2).toRingHom :=
    (symMap_genPoly (Subalgebra.inclusion (chartRing_mono x h2)) wd).symm
  have hQ : ∀ j, algebraMap O K (o j) = φ' (chartMap x g h2 ((genPoly (k := k) (g := g) wd).coeff j)) := by
    intro j
    have e1 := congrArg (fun p => p.coeff j) hT
    simp only [coeff_C_mul] at e1
    rw [← ho j] at e1
    have e2 := mul_left_cancel₀ hev (e1.trans (mul_comm _ _))
    rw [← e2, coeff_map, eb, coeff_map]
    rfl
  have hΦk : ∀ a, algebraMap O K (μ a) = (φ'.comp (chartMap x g h2).toRingHom) (algebraMap k _ a) := by
    intro a
    rw [hμ]
    change _ = φ' (chartMap x g h2 (algebraMap k _ a))
    rw [AlgHom.commutes, ← AlgHom.commutes (chartMap x g h1) a]
    exact (DFunLike.congr_fun hφ'c _).symm
  have hs : ∀ s : SymRing k (chartRing x {c + t}) g, ∃ p : (MvPolynomial ℕ k)[X], p.Monic ∧
      p.eval₂ (MvPolynomial.aeval fun j => (genPoly (k := k) (g := g) wd).coeff j).toRingHom s = 0 := by
    intro s
    obtain ⟨p, hpm, hp⟩ := exists_monic_genE (k := k) (g := g) wd (hint_chartRing_single (x := x) (c + t)) s.1
    refine ⟨p, hpm, Subtype.val_injective ?_⟩
    have e : (SymRing k (chartRing x {c + t}) g).val.toRingHom.comp
        (MvPolynomial.aeval (R := k) fun j => (genPoly (k := k) (g := g) wd).coeff j).toRingHom =
        (MvPolynomial.aeval (R := k) fun j => (genE (k := k) (g := g) wd).coeff j).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
        rfl
      · intro j
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
        exact coeff_genPoly wd j
    change (SymRing k (chartRing x {c + t}) g).val.toRingHom (p.eval₂ _ s) =
      (SymRing k (chartRing x {c + t}) g).val.toRingHom 0
    rw [Polynomial.hom_eval₂, e, map_zero]
    exact hp
  have hrange : (φ'.comp (chartMap x g h2).toRingHom).range ≤ (algebraMap O K).range := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨y, hy⟩ := mem_range_of_monic μ _ hΦk _ o hQ s (hs s)
    exact ⟨y, hy⟩
  let e : O ≃+* (algebraMap O K).range :=
    (AlgEquiv.ofInjective (Algebra.ofId O K) (IsFractionRing.injective _ _)).toRingEquiv
  let φ'' := e.symm.toRingHom.comp ((Subring.inclusion hrange).comp (RingHom.rangeRestrict _))
  have hφ'' : (algebraMap O K).comp φ'' = φ'.comp (chartMap x g h2).toRingHom := by
    ext s
    exact congr_arg Subtype.val (e.apply_symm_apply _)
  refine ⟨c + t, φ', φ'', hφ'c, hφ'', ?_⟩
  ext a
  apply IsFractionRing.injective O K
  rw [hΦk a]
  exact DFunLike.congr_fun hφ'' (algebraMap k _ a)

end ExistAlg

end RamanujanPetersson.JacSym

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

-- ===== S4.Def_RP_ThetaSquare_CPullOpen =====
section

/-!
# S4-ThetaSquare, file CPullOpen: `cpull` along open immersions, and monotonicity (F4)

* `ringOrd_ringEquiv`: `Ring.ord` is invariant under ring isomorphisms.
* `ord_algebraMap_stalkMap`, `ord_ffMap_openImm`: an open immersion `ι` keeps orders of vanishing
  (`ord_x (ι^* h) = ord_{ι x} h`).
* `fpull_comp_left`, `avoid_comp_left`, **`cpull_comp_openImm`**: `cpull (ι ≫ f) D x = cpull f D (ι x)`.
* `isDominant_openImm`; `cpull_mono` (`D ≤ E` near `f x`) and `cpull_le_ord` (`D ≤ div g` near `f x`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RamanujanPetersson.ThetaSquare

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing RamanujanPetersson.JacDivisors
  RamanujanPetersson.IsogDegA

universe u

/-- **`Ring.ord` is invariant under ring isomorphisms.** -/
lemma ringOrd_ringEquiv {R R' : Type u} [CommRing R] [CommRing R'] (e : R ≃+* R') (b : R) :
    Ring.ord R' (e b) = Ring.ord R b := by
  letI : Algebra R R' := e.toRingHom.toAlgebra
  have h1 : Module.length R (R' ⧸ Ideal.span {e b}) = Module.length R' (R' ⧸ Ideal.span {e b}) :=
    Module.length_eq_of_surjective e.surjective
  let f : R ≃ₐ[R] R' := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  have hJ : Ideal.span {e b} = (Ideal.span {b}).map (f : R →+* R') := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have h2 := (Ideal.quotientEquivAlg (Ideal.span {b}) (Ideal.span {e b}) f hJ).toLinearEquiv.length_eq
  exact h1.symm.trans h2.symm

/-- An open dense immersion: a nonempty open immersion into an irreducible scheme is dominant. -/
theorem isDominant_openImm {U C : Scheme.{u}} (ι : U ⟶ C) [IsOpenImmersion ι] [Nonempty U]
    [IrreducibleSpace C] : IsDominant ι :=
  ⟨ι.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

section
variable {U C : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsIntegral C] [IsLocallyNoetherian C]
  (ι : U ⟶ C) [IsOpenImmersion ι]

/-- **Open immersions keep orders of stalk elements.** -/
lemma ord_algebraMap_stalkMap (x : U) (a : C.presheaf.stalk (ι x)) :
    Scheme.ord (algebraMap _ U.functionField ((ι.stalkMap x).hom a)) x =
      Scheme.ord (algebraMap _ C.functionField a) (ι x) := by
  have hco : coheight (ι x) = coheight x := ι.isOpenEmbedding.coheight_eq
  by_cases hx : coheight x = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hco ▸ h))]
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, Scheme.ord_zero, Pi.zero_apply]
  have hx' : coheight (ι x) = 1 := hco.trans hx
  have : Ring.KrullDimLE 1 (C.presheaf.stalk (ι x)) := krullDimLE_of_coheight_le hx'.le
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (R := C.presheaf.stalk (ι x)) (mem_nonZeroDivisors_of_ne_zero ha))
  let e : C.presheaf.stalk (ι x) ≃+* U.presheaf.stalk x :=
    (asIso (ι.stalkMap x)).commRingCatIsoToRingEquiv
  have he : ∀ b, e b = (ι.stalkMap x).hom b := fun _ => rfl
  have hb : (ι.stalkMap x).hom a ≠ 0 := by
    rw [← he]
    exact (map_ne_zero_iff e e.injective).mpr ha
  have hn' : Ring.ord (U.presheaf.stalk x) ((ι.stalkMap x).hom a) = n := by
    rw [← he, ringOrd_ringEquiv]
    exact hn.symm
  rw [ord_algebraMap_stalk hx hb hn', ord_algebraMap_stalk hx' ha hn.symm]

variable [IsDominant ι]

/-- **Open immersions keep orders of rational functions**: `ord_x (ι^* h) = ord_{ι x} h`. -/
lemma ord_ffMap_openImm (h : C.functionField) (x : U) :
    Scheme.ord ((ffMap ι).hom h) x = Scheme.ord h (ι x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C.presheaf.stalk (ι x)) h
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hB : algebraMap _ C.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  by_cases ha0 : a = 0
  · subst ha0
    simp only [map_zero, zero_div, Scheme.ord_zero, Pi.zero_apply]
  have hA : algebraMap _ C.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha0
  have k1 := Scheme.ord_mul (x := ι x) (div_ne_zero hA hB) hB
  rw [div_mul_cancel₀ _ hB] at k1
  have k2 := Scheme.ord_mul (x := x) (ffMap_ne_zero ι (div_ne_zero hA hB)) (ffMap_ne_zero ι hB)
  rw [← map_mul, div_mul_cancel₀ _ hB, ffMap_algebraMap ι x a, ffMap_algebraMap ι x b] at k2
  have ea : Scheme.ord (algebraMap _ U.functionField (ι.stalkMap x a)) x =
      Scheme.ord (algebraMap _ C.functionField a) (ι x) := ord_algebraMap_stalkMap ι x a
  have eb : Scheme.ord (algebraMap _ U.functionField (ι.stalkMap x b)) x =
      Scheme.ord (algebraMap _ C.functionField b) (ι x) := ord_algebraMap_stalkMap ι x b
  rw [ea, eb] at k2
  linarith

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (f : C ⟶ Y)

/-- `fpull` along `ι ≫ f` is `fpull` along `f` followed by `ι^*`. -/
lemma fpull_comp_left (u : Y.presheaf.stalk (f (genericPoint C))) :
    fpull (ι ≫ f) (algebraMap _ Y.functionField u) =
      (ffMap ι).hom (fpull f (algebraMap _ Y.functionField u)) := by
  have h' : ι (genericPoint U) ⤳ genericPoint C := specializes_of_eq (map_genericPoint ι)
  have hs : (ι ≫ f) (genericPoint U) ⤳ f (genericPoint C) := f.base.hom.map_specializes h'
  rw [fpull_algebraMap f u, ← algebraMap_stalkSpecializes hs u, fpull_algebraMap]
  calc ((ι ≫ f).stalkMap (genericPoint U)).hom ((Y.presheaf.stalkSpecializes hs).hom u)
      = (ι.stalkMap (genericPoint U)).hom ((f.stalkMap (ι (genericPoint U))).hom
          ((Y.presheaf.stalkSpecializes hs).hom u)) := by
        rw [Scheme.Hom.stalkMap_comp]
        rfl
    _ = (ι.stalkMap (genericPoint U)).hom ((C.presheaf.stalkSpecializes h').hom
          ((f.stalkMap (genericPoint C)).hom u)) :=
        congrArg (ι.stalkMap (genericPoint U)).hom (f.stalkSpecializes_stalkMap_apply _ _ h' u)
    _ = _ := rfl

variable [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

lemma avoid_comp_left {D : AlgebraicCycle Y ℤ} (hA : Avoid f D) : Avoid (ι ≫ f) D := by
  obtain ⟨V, hV, hξ, h0⟩ := hA
  refine ⟨V, hV, ?_, h0⟩
  show f (ι (genericPoint U)) ∈ V
  rw [map_genericPoint ι]
  exact hξ

/-- **Pull-back along `ι ≫ f` (`ι` an open immersion) is pull-back along `f` read on `U`.** -/
lemma cpull_comp_openImm {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid f D) (x : U) :
    cpull (ι ≫ f) D x = cpull f D (ι x) := by
  have hloc : IsLocEq D ((ι ≫ f) x) (locEq D (f (ι x))) := isLocEq_locEq hD (f (ι x))
  obtain ⟨w, -, hw⟩ := exists_unit_of_isLocEq f hA (isLocEq_locEq hD (f (ι x)))
  rw [cpull_eq_of (ι ≫ f) hD (avoid_comp_left ι f hA) hloc, cpull_apply f hD hA, ← hw,
    fpull_comp_left, ord_ffMap_openImm]

end

section
variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

lemma avoid_sub {D E : AlgebraicCycle Y ℤ} (hD : Avoid f D) (hE : Avoid f E) : Avoid f (E - D) := by
  obtain ⟨V, hV, h1, h2⟩ := hD
  obtain ⟨V', hV', h1', h2'⟩ := hE
  refine ⟨V ∩ V', hV.inter hV', ⟨h1, h1'⟩, fun w hw => ?_⟩
  rw [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, h2 w hw.1, h2' w hw.2, sub_zero]

/-- **Monotonicity**: `D ≤ E` near `f x` gives `cpull f D x ≤ cpull f E x`. -/
lemma cpull_mono {D E : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hE : E ∈ weilDivisors Y)
    (hAD : Avoid f D) (hAE : Avoid f E) (x : C) (h : ∀ z : Y, z ⤳ f x → coheight z = 1 → D z ≤ E z) :
    cpull f D x ≤ cpull f E x := by
  have hED : E - D ∈ weilDivisors Y := (weilDivisors Y).sub_mem hE hD
  have hAED : Avoid f (E - D) := avoid_sub f hAD hAE
  have e : cpull f E = cpull f D + cpull f (E - D) := by
    rw [← cpull_add f hD hED hAD hAED]
    congr 1
    abel
  have hn := cpull_nonneg f hED hAED x fun z hz h1 => by
    rw [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply]
    linarith [h z hz h1]
  rw [e, Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  linarith

/-- **`D ≤ div g` near `f x`** gives `cpull f D x ≤ ord_x (f^* g)`. -/
lemma cpull_le_ord {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hAD : Avoid f D)
    {g : Y.functionField} (hg : g ≠ 0) (hA : Avoid f (div Y g)) (x : C)
    (h : ∀ z : Y, z ⤳ f x → coheight z = 1 → D z ≤ div Y g z) :
    cpull f D x ≤ Scheme.ord (fpull f g) x := by
  have := cpull_mono f hD (div_mem_weilDivisors g) hAD hA x h
  rwa [cpull_div f hg hA, div_apply] at this

end

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_ThetaCube_Val =====
section

/-!
# S4-ThetaCube, file Val (D-C1, part 1): values of rational functions at `K`-points
* `RegAt x G`: `G` is regular at `x` (a subring condition); `fpull_add_of`, `fpull_sub_of`, `fpull_sum_of`;
* `regAt_fpull`: regular at `(ℓ ≫ z) (η_C)` ⇒ `fpull z G` regular at `ℓ (η_C)`, `fpull ℓ (fpull z G) = fpull (ℓ ≫ z) G`;
* **`eq_zero_of_kpt`**, **`eq_of_kpt`**: on an integral scheme locally of finite type over an algebraically closed
  `K`, rational functions regular with equal values at the `K`-points of a nonempty open are equal.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory Topology RamanujanPetersson.ThetaSquare

universe u

section Reg

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- `G` is regular at `x`. -/
def RegAt (x : Y) (G : Y.functionField) : Prop :=
  G ∈ (algebraMap (Y.presheaf.stalk x) Y.functionField).range

lemma regAt_iff (x : Y) (G : Y.functionField) :
    RegAt x G ↔ ∃ w : Y.presheaf.stalk x, algebraMap _ Y.functionField w = G :=
  RingHom.mem_range

variable {C : Scheme.{u}} [IsIntegral C] (f : C ⟶ Y)

lemma fpull_add_of {G H : Y.functionField} (hG : RegAt (f (genericPoint C)) G) (hH : RegAt (f (genericPoint C)) H) :
    fpull f (G + H) = fpull f G + fpull f H := by
  obtain ⟨w, rfl⟩ := (regAt_iff _ _).mp hG
  obtain ⟨v, rfl⟩ := (regAt_iff _ _).mp hH
  rw [← map_add, fpull_algebraMap, fpull_algebraMap, fpull_algebraMap, map_add]

lemma fpull_sub_of {G H : Y.functionField} (hG : RegAt (f (genericPoint C)) G) (hH : RegAt (f (genericPoint C)) H) :
    fpull f (G - H) = fpull f G - fpull f H := by
  obtain ⟨w, rfl⟩ := (regAt_iff _ _).mp hG
  obtain ⟨v, rfl⟩ := (regAt_iff _ _).mp hH
  rw [← map_sub, fpull_algebraMap, fpull_algebraMap, fpull_algebraMap, map_sub]

lemma fpull_sum_of {ι : Type*} (s : Finset ι) (G : ι → Y.functionField)
    (h : ∀ i ∈ s, RegAt (f (genericPoint C)) (G i)) :
    fpull f (∑ i ∈ s, G i) = ∑ i ∈ s, fpull f (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← map_zero (algebraMap (Y.presheaf.stalk (f (genericPoint C)))
      Y.functionField), fpull_algebraMap, map_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      fpull_add_of f (h a (Finset.mem_insert_self a s))
        (Subring.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end Reg

section Comp

variable {C P X : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral X]

/-- Regularity and values along a composite. -/
lemma regAt_fpull (ℓ : C ⟶ P) (z : P ⟶ X) {G : X.functionField} (hG : RegAt ((ℓ ≫ z) (genericPoint C)) G) :
    RegAt (ℓ (genericPoint C)) (fpull z G) ∧ fpull ℓ (fpull z G) = fpull (ℓ ≫ z) G := by
  obtain ⟨v, h1, h2⟩ := fpull_fpull ℓ z G ((regAt_iff _ _).mp hG)
  refine ⟨(regAt_iff _ _).mpr ⟨v, h1⟩, ?_⟩
  rw [← h1, fpull_algebraMap, h2]

end Comp

section Agree

variable {K : Type u} [Field K] [IsAlgClosed K]

instance isIntegral_unitO : IsIntegral (𝟙_ (Over (Spec (.of K)))).left :=
  inferInstanceAs (IsIntegral (Spec (.of K)))

/-- **A rational function vanishing at the `K`-points of a nonempty open is zero.** -/
theorem eq_zero_of_kpt {X : Over (Spec (.of K))} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (G : X.left.functionField) {V : Set X.left} (hV : IsOpen V) (hne : V.Nonempty)
    (h : ∀ p : 𝟙_ (Over (Spec (.of K))) ⟶ X, p.left (genericPoint _) ∈ V →
      ∃ w : X.left.presheaf.stalk (p.left (genericPoint _)), algebraMap _ X.left.functionField w = G ∧
        (p.left.stalkMap (genericPoint _)).hom w = 0) : G = 0 := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hpt : ∀ x ∈ closedPoints X.left, ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ X, p.left (genericPoint _) = x :=
    fun x hx => ⟨Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp _ _ _),
      pointOfClosedPoint_apply _ _ _ _⟩
  obtain ⟨x0, hx0V, hx0c⟩ := nonempty_inter_closedPoints hne hV.isLocallyClosed
  obtain ⟨p0, rfl⟩ := hpt x0 hx0c
  obtain ⟨w0, hw0, -⟩ := h p0 hx0V
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.left.presheaf w0
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  by_contra hG
  have hs : s ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hw0
    exact hG hw0.symm
  have hb : ((X.left.basicOpen s : X.left.Opens) : Set X.left).Nonempty := by
    by_contra hb
    exact hs ((basicOpen_eq_bot_iff s).mp ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hb))
  obtain ⟨y, ⟨hyb, hyV⟩, hyc⟩ := nonempty_inter_closedPoints
    (nonempty_preirreducible_inter (X.left.basicOpen s).isOpen hV hb ⟨_, hx0V⟩)
    ((X.left.basicOpen s).isOpen.inter hV).isLocallyClosed
  obtain ⟨p1, rfl⟩ := hpt y hyc
  obtain ⟨w1, hw1, hz⟩ := h p1 hyV
  have hyU : p1.left (genericPoint _) ∈ U := X.left.basicOpen_le s hyb
  have hu : IsUnit (X.left.presheaf.germ U _ hyU s) := (X.left.mem_basicOpen s _ hyU).mp hyb
  have e : w1 = X.left.presheaf.germ U _ hyU s := by
    apply IsFractionRing.injective (X.left.presheaf.stalk _) X.left.functionField
    rw [hw1, ← hw0, Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField]
  rw [e] at hz
  exact (hu.map (p1.left.stalkMap _).hom).ne_zero hz

/-- **Rational functions regular with equal values at the `K`-points of a nonempty open are equal.** -/
theorem eq_of_kpt {X : Over (Spec (.of K))} [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (G H : X.left.functionField) {V : Set X.left} (hV : IsOpen V) (hne : V.Nonempty)
    (h : ∀ p : 𝟙_ (Over (Spec (.of K))) ⟶ X, p.left (genericPoint _) ∈ V →
      RegAt (p.left (genericPoint _)) G ∧ RegAt (p.left (genericPoint _)) H ∧ fpull p.left G = fpull p.left H) :
    G = H := by
  refine sub_eq_zero.mp (eq_zero_of_kpt (G - H) hV hne fun p hp => ?_)
  obtain ⟨hG, hH, e⟩ := h p hp
  obtain ⟨w, rfl⟩ := (regAt_iff _ _).mp hG
  obtain ⟨v, rfl⟩ := (regAt_iff _ _).mp hH
  refine ⟨w - v, map_sub _ _ _, ?_⟩
  rw [fpull_algebraMap, fpull_algebraMap] at e
  rw [map_sub, e, sub_self]

end Agree

end RamanujanPetersson.ThetaCube

end


