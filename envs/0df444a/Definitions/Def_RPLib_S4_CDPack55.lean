-- Prove2me | Definitions.Def_RPLib_S4_CDPack55
-- name    : RPLib_S4_CDPack55
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T16:04:41.316379+00:00
-- url     : https://prove2.me/theorems/e32dc6c5-1257-478f-893a-4a3adace60d6
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 55 of 71
-- statement:
--   Part 55 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
--   * `Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
--   * `Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
--   * `Def_RP_ThetaSquare_Mult1`: Unit S4-ThetaSquare, file Mult1: local algebra for the multiplicity-one count (F6a)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack54
import Definitions.Def_RPLib_S4_CDPack54b
import Definitions.Def_RPLib_S4_CDPack53
import Definitions.Def_RPLib_S4_CDPack42b
import Definitions.Def_RPLib_S4_CDPack48
import Definitions.Def_RPLib_S4_CDPack43c
import Definitions.Def_RPLib_S4_CDPack41d

/-!
# Curve-duality library package, part 55 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_ThetaSquare_Sep`: Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)
* `Def_RP_ThetaSquare_ThetaX0`: Unit S4-ThetaSquare, file ThetaX0: `Θ` on the translated chart `τ_d = t_d ∘ jX0 : X0 → J`
* `Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
* `Def_RP_ThetaSquare_Mult1`: Unit S4-ThetaSquare, file Mult1: local algebra for the multiplicity-one count (F6a)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaSquare_Sep =====
section

/-!
# Unit S4-ThetaSquare, file Sep: inputs of `IntersectC.inum_pos` for `Θ` (L42)

* **`eq_one_of_stab`**: a `K`-point `c` of `J` with `W(K) · c ⊆ W` is `1` (Riemann's theorem `mem_W_iff` and the
  divisor form `mem_PrincK_of_stab`);
* `hsep_W`: translates of `W` separate `K`-points: for `b ≠ b'` some `a` has `b a ∈ W`, `b' a ∉ W`;
* `support_effI_Theta`: the support of the ideal sheaf `effI Θ` is `W`; `support_effI_Theta_ne_top`;
* **`hsep_Theta`**: the `hsep` hypothesis of `inum_pos` for `D = Θ`.
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
open RamanujanPetersson.IntersectC

universe u

section Sep

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- **Trivial stabiliser of `W_{g-1}`**: a `K`-point `c` with `W(K) · c ⊆ W` is `1`. -/
theorem eq_one_of_stab (hg : 0 < genusFK K F) (c : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (hc : ∀ w : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, w.left (IsLocalRing.closedPoint K) ∈ W P0 →
      (w * c).left (IsLocalRing.closedPoint K) ∈ W P0) : c = 1 := by
  obtain ⟨B, hB⟩ : ∃ B : Places.Divisor K F,
      clsK K F B = ((Multiplicative.toAdd (jacPicEquiv K F c) : Pic0K K F) : PicK K F) :=
    QuotientAddGroup.mk_surjective _
  have hd : B.deg = 0 := by
    have := (mem_Pic0K K F).1 (Multiplicative.toAdd (jacPicEquiv K F c)).2
    rwa [← hB, degPicK_clsK] at this
  have hP : B ∈ PrincK K F := by
    refine mem_PrincK_of_stab hg B hd fun S hS => ?_
    have hm : clsK K F (Zdiv S) - n0 K F • clsK K F (Finsupp.single P0 1) ∈ Pic0K K F := by
      rw [mem_Pic0K, map_sub, map_nsmul, degPicK_clsK, degPicK_clsK, deg_Zdiv, deg_single_one, hS]
      simp
    obtain ⟨w, hwc⟩ : ∃ w : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F,
        ((Multiplicative.toAdd (jacPicEquiv K F w) : Pic0K K F) : PicK K F) =
          clsK K F (Zdiv S) - n0 K F • clsK K F (Finsupp.single P0 1) :=
      ⟨(jacPicEquiv K F).symm (Multiplicative.ofAdd ⟨_, hm⟩), by rw [MulEquiv.apply_symm_apply]; rfl⟩
    obtain ⟨t, ht⟩ := (mem_W_iff P0 (w * c)).1 (hc w (mem_W_of_cls P0 w S hS hwc))
    refine ⟨∑ i, Finsupp.single (t i) 1,
      Finset.sum_nonneg fun i _ => Finsupp.single_nonneg.2 zero_le_one, ?_⟩
    rw [map_mul] at ht
    have h1 := congrArg (fun z : Multiplicative (Pic0K K F) => ((Multiplicative.toAdd z : Pic0K K F) : PicK K F)) ht
    simp only [toAdd_mul, toAdd_ofAdd, AddSubgroup.coe_add, AddSubmonoidClass.coe_finsetSum, coe_ajCls] at h1
    rw [hwc, ← hB, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← clsK_sum] at h1
    rw [clsK_add (K := K) (F := F)]
    calc clsK K F (∑ i, Finsupp.single (t i) 1)
        = (clsK K F (∑ i, Finsupp.single (t i) 1) - n0 K F • clsK K F (Finsupp.single P0 1)) +
            n0 K F • clsK K F (Finsupp.single P0 1) := by abel
      _ = (clsK K F (Zdiv S) - n0 K F • clsK K F (Finsupp.single P0 1) + clsK K F B) +
            n0 K F • clsK K F (Finsupp.single P0 1) := by rw [h1]
      _ = clsK K F (Zdiv S) + clsK K F B := by abel
  have h0 : Multiplicative.toAdd (jacPicEquiv K F c) = 0 := by
    apply Subtype.ext
    rw [← hB, ZeroMemClass.coe_zero]
    exact (QuotientAddGroup.eq_zero_iff B).2 hP
  apply (jacPicEquiv K F).injective
  rw [map_one]
  exact toAdd_eq_zero.1 h0

/-- **Translates of `W` separate `K`-points.** -/
theorem hsep_W (hg : 0 < genusFK K F) (b b' : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (hbb : b ≠ b') :
    ∃ a, pt (Jac K F) (b * a) ∈ W P0 ∧ pt (Jac K F) (b' * a) ∉ W P0 := by
  by_contra hne
  push Not at hne
  apply hbb
  have h1 := eq_one_of_stab P0 hg (b⁻¹ * b') fun w hw => by
    have hw' : b * (b⁻¹ * w) = w := by rw [← _root_.mul_assoc, _root_.mul_inv_cancel, _root_.one_mul]
    have h2 := hne (b⁻¹ * w) (by rw [hw']; exact hw)
    have heq : b' * (b⁻¹ * w) = w * (b⁻¹ * b') := (jacPicEquiv K F).injective (by
      simp only [map_mul, map_inv]
      ac_rfl)
    rw [← heq]
    exact h2
  rw [_root_.inv_mul_eq_one] at h1
  exact h1

instance isIntegral_Jac_left : IsIntegral (Jac K F).left := isIntegral_of_irreducibleSpace_of_isReduced _

theorem finite_support_Theta : (Function.support (Theta P0)).Finite :=
  (Set.finite_singleton (zTheta P0)).subset fun z hz => by
    rw [Function.mem_support, Theta_apply] at hz
    split_ifs at hz with h
    · exact h
    · exact absurd rfl hz

/-- The support of the ideal sheaf of `Θ` is `W`. -/
theorem support_effI_Theta : ((effI (Theta P0)).support : Set (Jac K F).left) = W P0 := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, hxz⟩ := mem_support_effI (Theta P0) (finite_support_Theta P0) hx
    rw [Theta_apply] at hz
    split_ifs at hz with h
    · rw [← closure_zTheta P0, ← h]
      exact hxz
    · exact absurd hz (lt_irrefl 0)
  · intro hx
    have hz := mem_support_effI_of_pos (Theta P0) (finite_support_Theta P0) (z := zTheta P0)
      (by rw [Theta_apply, if_pos rfl]; exact one_pos)
    rw [← closure_zTheta P0] at hx
    exact closure_minimal (Set.singleton_subset_iff.2 hz) (effI (Theta P0)).support.isClosed hx

theorem support_effI_Theta_ne_top (hg : 0 < genusFK K F) : (effI (Theta P0)).support ≠ ⊤ := by
  have : IsLocallyNoetherian (Jac K F).left := LocallyOfFiniteType.isLocallyNoetherian (Jac K F).hom
  exact support_effI_ne_top (Theta P0) (theta_mem_weilDivisors P0 hg) (finite_support_Theta P0)

/-- **The `hsep` input of `IntersectC.inum_pos` for `D = Θ`.** -/
theorem hsep_Theta (hg : 0 < genusFK K F) :
    ∀ b b' : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F, b ≠ b' → ∃ a,
      pt (Jac K F) (b * a) ∈ ((effI (Theta P0)).support : Set (Jac K F).left) ∧
        pt (Jac K F) (b' * a) ∉ ((effI (Theta P0)).support : Set (Jac K F).left) := by
  rw [support_effI_Theta]
  exact hsep_W P0 hg

end Sep

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

/-- **Pull-back along an open immersion is restriction**: `(ι^* D)(x) = D(ι x)`. -/
lemma pullback_openImm {D : AlgebraicCycle C ℤ} (hD : D ∈ weilDivisors C) (x : U) :
    JacDivisors.pullback ι D x = D (ι x) := by
  obtain ⟨-, V, -, hxV, hDV⟩ := isLocEq_locEq hD (ι x)
  rw [pullback_apply ι hD, ord_ffMap_openImm, hDV (ι x) hxV, div_apply]

end General

section ThetaX0

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

instance isNoetherianRing_lawRingT : IsNoetherianRing (LawRing K F) := Algebra.FiniteType.isNoetherianRing K _

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

/-- `τ_d^* Θ` is the indicator of the point over `zTheta`. -/
theorem pullback_tauX_apply (hg : 0 < genusFK K F) (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) (z : X0 K F) :
    JacDivisors.pullback (tauX d) (Theta P0) z = if tauX d z = zTheta P0 then 1 else 0 := by
  rw [pullback_openImm (tauX d) (theta_mem_weilDivisors P0 hg) z, Theta_apply]

/-- If `τ_d y ∈ W`, the generic point `zTheta` is `τ_d η'` for a generization `η'` of `y`. -/
theorem exists_eta (d : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F) {y : X0 K F} (hy : tauX d y ∈ W P0) :
    ∃ z : X0 K F, tauX d z = zTheta P0 ∧ z ⤳ y := by
  have h1 : zTheta P0 ⤳ tauX d y := specializes_iff_mem_closure.2 (by rw [closure_zTheta P0]; exact hy)
  obtain ⟨z, hz⟩ : zTheta P0 ∈ Set.range (tauX d) :=
    h1.mem_open (tauX d).isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  refine ⟨z, hz, ?_⟩
  rw [← (tauX d).isOpenEmbedding.toIsEmbedding.toIsInducing.specializes_iff, hz]
  exact h1

/-- A `K`-point `e ∉ S` of `Rfin` is a zero of some `s` with no zero on `S` (prime avoidance). -/
theorem exists_sep_one (S : Finset (Rfin K F →ₐ[K] K)) (e : Rfin K F →ₐ[K] K) (he : e ∉ S) :
    ∃ s : Rfin K F, e s = 0 ∧ ∀ ψ ∈ S, ψ s ≠ 0 := by
  by_contra hne
  push Not at hne
  have hsub : ((RingHom.ker (e : Rfin K F →+* K) : Ideal (Rfin K F)) : Set (Rfin K F)) ⊆
      ⋃ ψ ∈ (↑S : Set (Rfin K F →ₐ[K] K)), ((RingHom.ker (ψ : Rfin K F →+* K) : Ideal (Rfin K F)) : Set (Rfin K F)) := by
    intro s hs
    obtain ⟨ψ, hψ, h0⟩ := hne s (RingHom.mem_ker.1 hs)
    exact Set.mem_biUnion (Finset.mem_coe.2 hψ) (RingHom.mem_ker.2 h0)
  obtain ⟨ψ, hψ, hle⟩ := (Ideal.subset_union_prime e e (fun ψ _ _ _ => RingHom.ker_isPrime _)).1 hsub
  apply he
  have heψ : e = ψ := by
    ext b
    have hb : b - algebraMap K (Rfin K F) (e b) ∈ RingHom.ker (e : Rfin K F →+* K) := by
      refine RingHom.mem_ker.2 ?_
      show e (b - algebraMap K (Rfin K F) (e b)) = 0
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
    have h2 : ψ (b - algebraMap K (Rfin K F) (e b)) = 0 := RingHom.mem_ker.1 (hle hb)
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h2
    exact h2.symm
  rw [heψ]
  exact hψ

/-- Finitely many `K`-points off `S` are common zeros of an `s` with no zero on `S`. -/
theorem exists_sep (S T : Finset (Rfin K F →ₐ[K] K)) (hST : Disjoint S T) :
    ∃ s : Rfin K F, (∀ e ∈ T, e s = 0) ∧ ∀ ψ ∈ S, ψ s ≠ 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨1, fun e he => absurd he (Finset.notMem_empty e), fun ψ _ => by rw [map_one]; exact one_ne_zero⟩
  | @insert e T heT ih =>
    obtain ⟨s1, h1, h1'⟩ := ih (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hST)
    obtain ⟨s2, h2, h2'⟩ := exists_sep_one S e (Finset.disjoint_right.1 hST (Finset.mem_insert_self _ _))
    refine ⟨s1 * s2, fun e' he' => ?_, fun ψ hψ => ?_⟩
    · rcases Finset.mem_insert.1 he' with rfl | he'
      · rw [map_mul, h2, mul_zero]
      · rw [map_mul, h1 e' he', zero_mul]
    · rw [map_mul]
      exact mul_ne_zero (h1' ψ hψ) (h2' ψ hψ)

set_option maxHeartbeats 1000000 in
/-- **Upper-bound input**: `Nm(t)` vanishes at the point `η'` over `zTheta` of the chart translated by `c_φ⁻¹`, as soon
as one chart point `A` contains `φ` and no other zero of `t`. -/
theorem normS_mem_eta (hg : 0 < genusFK K F) (c : (Rfin K F →ₐ[K] K) → (𝟙_ (Over (Spec (.of K))) ⟶ Jac K F))
    (hc : ∀ φ, ((Multiplicative.toAdd (jacPicEquiv K F (c φ)) : Pic0K K F) : PicK K F) =
      clsK K F (Finsupp.single (Sum.inl (ptP φ)) 1) + n0 K F • clsK K F (Finsupp.single P0 1) - thetaK K F)
    (φ : Rfin K F →ₐ[K] K) {t : Rfin K F} (ht0 : t ≠ 0) (ht : φ t = 0)
    (yA : LawRing K F →ₐ[K] K) (hφA : φ ∈ ptSet (yA.comp (awayι (K := K) (lawPre K F).u0)))
    (hA : ∀ ψ ∈ ptSet (yA.comp (awayι (K := K) (lawPre K F).u0)), ψ t = 0 → ψ = φ)
    {z : X0 K F} (hz : tauX (c φ)⁻¹ z = zTheta P0) :
    awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t) ∈
      PrimeSpectrum.asIdeal (R := LawRing K F) z := by
  obtain ⟨s, hsT, hsA⟩ := exists_sep (ptSet (yA.comp (awayι (K := K) (lawPre K F).u0)))
    ((finite_zeros ht0).toFinset.erase φ) (by
      rw [Finset.disjoint_right]
      intro e he heA
      have h1 := Finset.mem_erase.1 he
      exact h1.1 (hA e heA ((finite_zeros ht0).mem_toFinset.1 h1.2)))
  set N : LawRing K F := awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) t) with hN_def
  set M : LawRing K F := awayι (K := K) (lawPre K F).u0 (normS K (g := genusFK K F) s) with hM_def
  have hN : ∀ yR : LawRing K F →ₐ[K] K, yR N = 0 →
      ∃ ψ ∈ ptSet (yR.comp (awayι (K := K) (lawPre K F).u0)), ψ t = 0 := by
    intro yR h
    rw [hN_def, eval_normS] at h
    obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.1 h
    exact ⟨_, (mem_ptSet _ _).2 ⟨l, rfl⟩, hl⟩
  have hyAN : yA N = 0 := by
    obtain ⟨l, hl⟩ := (mem_ptSet _ _).1 hφA
    rw [hN_def, eval_normS]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by rw [hl]; exact ht)
  have hyAM : yA M ≠ 0 := by
    rw [hM_def, eval_normS]
    exact Finset.prod_ne_zero_iff.2 fun l _ => hsA _ ((mem_ptSet _ _).2 ⟨l, rfl⟩)
  -- the minimal prime `q ⊆ m_A` of `(N)` (Krull: height `≤ 1`)
  have hNk : Ideal.span {N} ≤ RingHom.ker (yA : LawRing K F →+* K) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (RingHom.mem_ker).2 hyAN
  haveI : (RingHom.ker (yA : LawRing K F →+* K)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, hqmin, hqk⟩ := Ideal.exists_minimalPrimes_le hNk
  have hq1 : q.height ≤ 1 := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := ({N} : Finset (LawRing K F))) (p := q)
      (by rw [Finset.coe_singleton]; exact hqmin)
    rwa [Finset.card_singleton, Nat.cast_one] at h1
  let xq : X0 K F := ((⟨q, hqmin.1.1⟩ : PrimeSpectrum (LawRing K F)) : X0 K F)
  have hMq : M ∉ q := fun h => hyAM (RingHom.mem_ker.1 (hqk h))
  -- `V(N) ⊆ τ⁻¹ W ∪ V(M)` (closed points, then Jacobson)
  let Sset : Set (X0 K F) :=
    tauX (c φ)⁻¹ ⁻¹' W P0 ∪ (PrimeSpectrum.zeroLocus ({M} : Set (LawRing K F)) : Set (X0 K F))
  have hS : IsClosed Sset :=
    ((isClosed_W P0).preimage (tauX (c φ)⁻¹).continuous).union (PrimeSpectrum.isClosed_zeroLocus _)
  haveI hJ : JacobsonSpace (X0 K F) := LocallyOfFiniteType.jacobsonSpace (jX0 K F ≫ (Jac K F).hom)
  haveI : JacobsonSpace (PrimeSpectrum ↑(CommRingCat.of (LawRing K F))) := hJ
  have hV : IsClosed (PrimeSpectrum.zeroLocus ({N} : Set (LawRing K F)) : Set (X0 K F)) :=
    PrimeSpectrum.isClosed_zeroLocus _
  have hsub : (PrimeSpectrum.zeroLocus ({N} : Set (LawRing K F)) : Set (X0 K F)) ⊆ Sset := by
    rw [← closure_inter_closedPoints hV]
    refine closure_minimal ?_ hS
    rintro p ⟨hpN, hpc⟩
    obtain ⟨yR, rfl⟩ := JacLaw.exists_kpt (K := K) (A := LawRing K F) p hpc
    have hyN : yR N = 0 := by
      have h1 : N ∈ PrimeSpectrum.asIdeal (R := LawRing K F) (kpt yR) :=
        (PrimeSpectrum.mem_zeroLocus _ _).1 hpN (Set.mem_singleton N)
      rwa [kpt_asIdeal, RingHom.mem_ker] at h1
    obtain ⟨ψ, hψ, hψt⟩ := hN yR hyN
    by_cases hψφ : ψ = φ
    · refine Or.inl ?_
      show tauX (c φ)⁻¹ (kpt yR) ∈ W P0
      rw [tauX_apply]
      rw [hψφ] at hψ
      exact mem_transl_W P0 c hc yR φ hψ
    · refine Or.inr ((PrimeSpectrum.mem_zeroLocus _ _).2 (Set.singleton_subset_iff.2 ?_))
      show M ∈ PrimeSpectrum.asIdeal (R := LawRing K F) (kpt yR)
      rw [kpt_asIdeal, RingHom.mem_ker]
      obtain ⟨l, hl⟩ := (mem_ptSet _ _).1 hψ
      rw [hM_def, eval_normS]
      exact Finset.prod_eq_zero (Finset.mem_univ l) (by
        rw [hl]
        exact hsT ψ (Finset.mem_erase.2 ⟨hψφ, (finite_zeros ht0).mem_toFinset.2 hψt⟩))
  have hxq : xq ∈ Sset := hsub ((PrimeSpectrum.mem_zeroLocus _ _).2
    (Set.singleton_subset_iff.2 (hqmin.1.2 (Ideal.subset_span rfl))))
  have hxqW : tauX (c φ)⁻¹ xq ∈ W P0 := by
    rcases (Set.mem_union _ _ _).1 hxq with h | h
    · exact h
    · exact absurd ((PrimeSpectrum.mem_zeroLocus _ _).1 h (Set.mem_singleton M)) hMq
  -- coheight: `τ xq = zTheta`
  have hspec : tauX (c φ)⁻¹ xq ≤ zTheta P0 :=
    specializes_iff_mem_closure.2 (by rw [closure_zTheta P0]; exact hxqW)
  have hco : Order.coheight (tauX (c φ)⁻¹ xq) ≤ 1 := by
    rw [(tauX (c φ)⁻¹).isOpenEmbedding.coheight_eq, ← idealHeight_eq_coheight (.of (LawRing K F)) xq]
    exact hq1
  have heq : tauX (c φ)⁻¹ xq = zTheta P0 := by
    by_contra hne
    have hlt := Order.coheight_strictAnti (lt_of_le_not_ge hspec fun h =>
      hne (Specializes.antisymm (show tauX (c φ)⁻¹ xq ⤳ zTheta P0 from h)
        (show zTheta P0 ⤳ tauX (c φ)⁻¹ xq from hspec)).eq)
      (by rw [coheight_zTheta P0 hg]; exact ENat.one_lt_top)
    rw [coheight_zTheta P0 hg] at hlt
    exact absurd (lt_of_lt_of_le hlt hco) (lt_irrefl _)
  have hzq : z = xq := (tauX (c φ)⁻¹).isOpenEmbedding.injective (hz.trans heq.symm)
  rw [hzq]
  exact hqmin.1.2 (Ideal.subset_span rfl)

end ThetaX0

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

/-- **Every `K`-point of `Spec R` is `kptO x`.** -/
theorem exists_eq_kptO {R : Type u} [CommRing R] [Algebra K R] (p : 𝟙_ (Over (Spec (.of K))) ⟶ specO K R) :
    ∃ x : R →ₐ[K] K, p = kptO x := by
  have hw : p.left ≫ sR K R = 𝟙 (Spec (.of K)) := Over.w p
  obtain ⟨f, hf⟩ : ∃ f : CommRingCat.of R ⟶ CommRingCat.of K, Spec.map f = p.left :=
    ⟨Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of K) p.left, Spec.map_preimage _⟩
  have hc : CommRingCat.ofHom (algebraMap K R) ≫ f = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf, Spec.map_id]
    exact hw
  refine ⟨{ f.hom with commutes' := fun k => congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of K => φ.hom k) hc },
    ?_⟩
  apply Over.OverMorphism.ext
  refine hf.symm.trans ?_
  rfl

end KptO

section PlusX

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

instance finiteType_R1 : Algebra.FiniteType K (R1 F c0) := by
  have : IsScalarTower K (Rfin K F) (R1 F c0) :=
    IsScalarTower.of_algebraMap_eq fun k => ((inclR c0).commutes k).symm
  exact Algebra.FiniteType.trans (S := Rfin K F) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (xcR F c0)) (R1 F c0))

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

theorem deg_plusE : (plusE a i0).deg = (genusFK K F : ℤ) - 1 := by
  have h : ∀ s : Finset (Fin (genusFK K F)),
      Places.Divisor.deg (∑ i ∈ s, Finsupp.single (Sum.inl (ptP (a i)) : Place K F) (1 : ℤ)) = s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Places.Divisor.deg]
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, PlacesK.Divisor.deg_add, ih, deg_single_one, Finset.card_insert_of_notMem hj]
      push_cast; ring
  rw [plusE, h, Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub (i0.pos : 1 ≤ genusFK K F), Nat.cast_one]

theorem mem_Pic0K_cE :
    clsK K F (plusE a i0) + clsK K F (Finsupp.single P0 1) - thetaK K F ∈ Pic0K K F := by
  rw [mem_Pic0K, map_sub, map_add, deg_thetaK, degPicK_clsK, degPicK_clsK, deg_plusE, deg_single_one]
  ring

/-- The constant `cE` with class `[E] + [P0] - [Θ]`. -/
noncomputable def cE : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F :=
  (jacPicEquiv K F).symm (Multiplicative.ofAdd ⟨_, mem_Pic0K_cE a i0 P0⟩)

theorem kptO_plus (x : R2 c0 a i0 →ₐ[K] K) :
    kptO x ≫ ((toUnit (specO K (R2 c0 a i0)) ≫ cE a i0 P0) * (plusX c0 a i0 ≫ ajO P0)) =
      kptO x ≫ jMap K F (lawMapPlus c0 a i0) := by
  rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (kptO x ≫ toUnit (specO K (R2 c0 a i0))) (𝟙 _),
    Category.id_comp, kptO_plusX_ajO]
  apply (jacPicEquiv K F).injective
  rw [map_mul, cE, ajK, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
  apply Subtype.ext
  rw [AddSubgroup.coe_add, jacPicEquiv_jMap K F (lawMapPlus c0 a i0) x, psiJ_lawMapPlus]
  show clsK K F (plusE a i0) + clsK K F (Finsupp.single P0 1) - thetaK K F +
    (clsK K F (Finsupp.single (Sum.inl (ptP (ptR2 c0 a i0 x))) 1) - clsK K F (Finsupp.single P0 1)) = _
  abel

/-- **The plus-curve is a translate of the Abel-Jacobi map**: `cE · (plusX ≫ AJ) = Spec R2 → X0 → J`. -/
theorem plus_eq : (toUnit (specO K (R2 c0 a i0)) ≫ cE a i0 P0) * (plusX c0 a i0 ≫ ajO P0) =
    jMap K F (lawMapPlus c0 a i0) := by
  refine (lawChunk K F).hom_ext_kpt (by show IsReduced (Spec (.of (R2 c0 a i0))); infer_instance)
    (by show LocallyOfFiniteType (sR K (R2 c0 a i0)); infer_instance) _ _ fun p => ?_
  obtain ⟨x, rfl⟩ := exists_eq_kptO p
  exact congrArg (lawChunk K F).kval (kptO_plus c0 a i0 P0 x)

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

/-- In the localization of a Dedekind domain at a prime `P`, any `t ∈ P \ P²` generates the maximal ideal. -/
theorem span_eq_maximalIdeal_of_dedekind {A O : Type*} [CommRing A] [IsDedekindDomain A] [CommRing O] [IsDomain O] [IsLocalRing O]
    [Algebra A O] {P : Ideal A} [hPp : P.IsPrime] [IsLocalization.AtPrime O P] {t : A} (ht : t ∈ P)
    (ht2 : t ∉ P ^ 2) : Ideal.span {algebraMap A O t} = maximalIdeal O := by
  have hP : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at ht
    exact ht2 (ht ▸ Ideal.zero_mem _)
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP O
  have hτm : algebraMap A O t ∈ maximalIdeal O := (IsLocalization.AtPrime.to_map_mem_maximal_iff O P t).2 ht
  have hτ2 : algebraMap A O t ∉ maximalIdeal O ^ 2 := by
    intro h
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O, ← Ideal.map_pow] at h
    have hprim : (P ^ 2).IsPrimary := by
      refine Ideal.isPrimary_of_isMaximal_radical ?_
      rw [Ideal.radical_pow P two_ne_zero, hPp.radical]
      exact hPp.isMaximal hP
    have hdis : Disjoint (P.primeCompl : Set A) (↑(P ^ 2)) := by
      rw [Set.disjoint_left]
      intro b hb hb2
      exact hb (Ideal.pow_le_self two_ne_zero hb2)
    apply ht2
    rw [← IsLocalization.under_map_of_isPrimary_disjoint P.primeCompl O hprim hdis]
    exact h
  have hτ0 : algebraMap A O t ≠ 0 := by
    intro h0
    apply hτ2
    rw [h0]
    exact Ideal.zero_mem _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖm : ϖ ∈ maximalIdeal O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit)
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hτ0 hϖ
  rcases n with _ | _ | n
  · exfalso
    apply (mem_maximalIdeal _).1 hτm
    rw [hv, pow_zero, mul_one]
    exact v.isUnit
  · rw [hv, zero_add, pow_one, Ideal.span_singleton_mul_left_unit v.isUnit,
      ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  · exfalso
    apply hτ2
    have e : (v : O) * ϖ ^ (n + 1 + 1) = ((v : O) * ϖ ^ n * ϖ) * ϖ := by ring
    rw [hv, e, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hϖm) hϖm

/-- Two `K`-points with `φ b = 0 → ψ b = 0` agree. -/
theorem eq_of_zero_imp {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra K R] {φ ψ : R →ₐ[K] K}
    (h : ∀ b, φ b = 0 → ψ b = 0) : φ = ψ := by
  ext b
  have h2 : ψ (b - algebraMap K R (φ b)) = 0 := by
    refine h _ ?_
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h2
  exact h2.symm

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

/-- **A uniformizer avoiding finitely many points**: for `φ ∉ S` there is `t ∈ m_φ \ m_φ²` with no zero on `S`. -/
theorem exists_unif (φ : Rfin K F →ₐ[K] K) (S : Finset (Rfin K F →ₐ[K] K)) (hφ : φ ∉ S) :
    ∃ t : Rfin K F, φ t = 0 ∧ t ∉ (ptP φ).asIdeal ^ 2 ∧ ∀ ψ ∈ S, ψ t ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  let f : (Rfin K F →ₐ[K] K) → Ideal (Rfin K F) := fun ψ =>
    if ψ = φ then (ptP φ).asIdeal ^ 2 else (ptP ψ).asIdeal
  have hsub : ((ptP φ).asIdeal : Set (Rfin K F)) ⊆
      ⋃ ψ ∈ (↑(insert φ S) : Set (Rfin K F →ₐ[K] K)), (f ψ : Set (Rfin K F)) := by
    intro s hs
    by_cases h2 : s ∈ (ptP φ).asIdeal ^ 2
    · refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_self φ S)) ?_
      show s ∈ f φ
      simp only [f, if_pos rfl]
      exact h2
    · obtain ⟨ψ, hψ, h0⟩ := hne s (mem_ptP.1 hs) h2
      have hne' : ψ ≠ φ := fun h => hφ (h ▸ hψ)
      refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_of_mem hψ)) ?_
      show s ∈ f ψ
      simp only [f, if_neg hne']
      exact mem_ptP.2 h0
  obtain ⟨ψ, -, hle⟩ := (Ideal.subset_union_prime φ φ (fun ψ _ h1 _ => by
    simp only [f, if_neg h1]
    exact (ptP ψ).isPrime)).1 hsub
  by_cases hψ : ψ = φ
  · simp only [f, if_pos hψ] at hle
    haveI := (ptP φ).isPrime
    exact (Ideal.pow_succ_lt_pow (ptP φ).ne_bot 1).not_ge (by rw [pow_one]; exact hle)
  · simp only [f, if_neg hψ] at hle
    exact hψ (eq_of_zero_imp (fun b hb => mem_ptP.1 (hle (mem_ptP.2 hb)))).symm

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

/-- **A uniformizer has order one** at a `K`-point of the plus-curve. -/
theorem ord_kpt_R2 [IsDomain (R2 c0 a i0)] (x : R2 c0 a i0 →ₐ[K] K) {t : Rfin K F} (ht : ptR2 c0 a i0 x t = 0)
    (ht2 : t ∉ (ptP (ptR2 c0 a i0 x)).asIdeal ^ 2) :
    Scheme.ord ((Spec (.of (R2 c0 a i0))).germToFunctionField ⊤
      ((Scheme.ΓSpecIso (.of (R2 c0 a i0))).inv.hom (algebraMap (Rfin K F) (R2 c0 a i0) t))) (kpt x) = 1 := by
  obtain ⟨hdvr, hsp⟩ := dvr_stalk_R2 c0 a i0 x
  have hspan := hsp t ht ht2
  refine ord_germ_eq_one (show kpt x ∈ (⊤ : (Spec (.of (R2 c0 a i0))).Opens) from trivial) (coheight_kpt_R2 c0 a i0 x) ?_ hspan
  intro h0
  rw [h0, map_zero, Ideal.span_singleton_eq_bot.2 rfl] at hspan
  exact IsDiscreteValuationRing.not_a_field _ hspan.symm

end R2

end RamanujanPetersson.ThetaSquare

end


