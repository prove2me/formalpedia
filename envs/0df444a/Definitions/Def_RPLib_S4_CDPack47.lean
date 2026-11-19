-- Prove2me | Definitions.Def_RPLib_S4_CDPack47
-- name    : RPLib_S4_CDPack47
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:24:11.23688+00:00
-- url     : https://prove2.me/theorems/9e2144d6-626f-48bd-ba98-cbcd60b16521
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 47 of 71
-- statement:
--   Part 47 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacDivisors_G`: S4-JacDivisors G (O9: Auslander-Buchsbaum, regular local rings are UFDs)
--   * `Def_RP_IsogDegA_QF`: S4-IsogDegA, file QF: a dominant endomorphism of a proper group variety is finite (O3)
--   * `Def_RP_IsogDegA_Trdeg`: S4-IsogDegA, file Trdeg: `K(A)` is finite over `φ^* K(A)` (O3 without the hypothesis)
--   * `Def_RP_IsogDegA_Mult`: S4-IsogDegA, file Mult: the degree is multiplicative (O4)
--   * `Def_RP_IsogDegB_Der`: S4-IsogDegB, tangent vectors from the cotangent space (lemma L27 of S4_COREB_ROUTE.md §3)
--   * `Def_RP_IsogDegB_TanA`: S4-IsogDegB, the tangent space at the identity (lemma L27 of S4_COREB_ROUTE.md §3)
--   * `Def_RP_IsogDegB_TanB`: S4-IsogDegB, differentials on stalks and tangent vectors from stalk maps (L27 of S4_COREB_ROUTE.md §3)
--   * `Def_RP_IsogDegB_TanC`: S4-IsogDegB, the group law on tangent vectors is addition (L27 of S4_COREB_ROUTE.md §3)
--   * `Def_RP_IsogDegB_DerT`: S4-IsogDegB, tangent vectors over a `k`-tower (L27 of S4_COREB_ROUTE.md §3)
--   * `Def_RP_IsogDegB_Sep`: S4-IsogDegB, file Sep: an injective differential makes `φ` unramified at the identity
--   * `Def_RP_JacSymB_Coord`: S4-JacSymB, file D: a coordinate that is étale at finitely many points
--   * `Def_RP_DegPoly_Cube`: Degree polynomiality, part 3: the quadratic relation from the cube relation (unit S4-DegPoly)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack45
import Definitions.Def_RPLib_S4_CDPack37
import Definitions.Def_RPLib_S4_CDPack20

/-!
# Curve-duality library package, part 47 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacDivisors_G`: S4-JacDivisors G (O9: Auslander-Buchsbaum, regular local rings are UFDs)
* `Def_RP_IsogDegA_QF`: S4-IsogDegA, file QF: a dominant endomorphism of a proper group variety is finite (O3)
* `Def_RP_IsogDegA_Trdeg`: S4-IsogDegA, file Trdeg: `K(A)` is finite over `φ^* K(A)` (O3 without the hypothesis)
* `Def_RP_IsogDegA_Mult`: S4-IsogDegA, file Mult: the degree is multiplicative (O4)
* `Def_RP_IsogDegB_Der`: S4-IsogDegB, tangent vectors from the cotangent space (lemma L27 of S4_COREB_ROUTE.md §3)
* `Def_RP_IsogDegB_TanA`: S4-IsogDegB, the tangent space at the identity (lemma L27 of S4_COREB_ROUTE.md §3)
* `Def_RP_IsogDegB_TanB`: S4-IsogDegB, differentials on stalks and tangent vectors from stalk maps (L27 of S4_COREB_ROUTE.md §3)
* `Def_RP_IsogDegB_TanC`: S4-IsogDegB, the group law on tangent vectors is addition (L27 of S4_COREB_ROUTE.md §3)
* `Def_RP_IsogDegB_DerT`: S4-IsogDegB, tangent vectors over a `k`-tower (L27 of S4_COREB_ROUTE.md §3)
* `Def_RP_IsogDegB_Sep`: S4-IsogDegB, file Sep: an injective differential makes `φ` unramified at the identity
* `Def_RP_JacSymB_Coord`: S4-JacSymB, file D: a coordinate that is étale at finitely many points
* `Def_RP_DegPoly_Cube`: Degree polynomiality, part 3: the quadratic relation from the cube relation (unit S4-DegPoly)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacDivisors_G =====
section

/-!
# S4-JacDivisors G (O9: Auslander-Buchsbaum, regular local rings are UFDs)
* `invertible_of_forall_isMaximal`: a nonzero ideal of a domain that is principal near every
  maximal ideal is an invertible module.
* `exists_dvd_of_ufd_localization`: a height-one prime `p` is principal near `Q` when `R_Q` is a UFD.
* `uniqueFactorizationMonoid_of_isRegularLocalRing` (O9).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal

universe u

/-- A (nonzero) ideal of a domain that is "principal near every maximal ideal" is invertible. -/
theorem invertible_of_forall_isMaximal {A : Type u} [CommRing A] [IsDomain A] (P : Ideal A)
    (hP : ∀ M : Ideal A, M.IsMaximal → ∃ a ∈ P, a ≠ 0 ∧ ∃ s ∉ M, ∀ y ∈ P, a ∣ s * y) :
    Module.Invertible A P := by
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hIJ : Submodule.map (Algebra.linearMap A (FractionRing A)) P *
      (1 / Submodule.map (Algebra.linearMap A (FractionRing A)) P) = 1 := by
    refine le_antisymm Submodule.mul_one_div_le_one ?_
    let L : Ideal A := Submodule.comap (Algebra.linearMap A (FractionRing A))
      (Submodule.map (Algebra.linearMap A (FractionRing A)) P *
        (1 / Submodule.map (Algebra.linearMap A (FractionRing A)) P))
    have hL : L = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hLM⟩ := Ideal.exists_le_maximal L hne
      obtain ⟨a, ha, ha0, s, hs, hdiv⟩ := hP M hM
      refine hs (hLM ?_)
      have ha0' : algebraMap A (FractionRing A) a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
      have hmem : algebraMap A (FractionRing A) s / algebraMap A (FractionRing A) a ∈
          1 / Submodule.map (Algebra.linearMap A (FractionRing A)) P := by
        rw [Submodule.mem_div_iff_forall_mul_mem]
        intro y hy
        obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
        obtain ⟨c, hc⟩ := hdiv p hp
        rw [Submodule.mem_one]
        refine ⟨c, ?_⟩
        rw [Algebra.linearMap_apply, div_mul_eq_mul_div, eq_div_iff ha0', ← map_mul, ← map_mul,
          hc, mul_comm]
      show Algebra.linearMap A (FractionRing A) s ∈
        Submodule.map (Algebra.linearMap A (FractionRing A)) P *
          (1 / Submodule.map (Algebra.linearMap A (FractionRing A)) P)
      rw [Algebra.linearMap_apply]
      have : algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a *
          (algebraMap A (FractionRing A) s / algebraMap A (FractionRing A) a) := by
        field_simp
      rw [this]
      exact Submodule.mul_mem_mul (Submodule.mem_map_of_mem ha) hmem
    intro z hz
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hz
    have : r ∈ L := hL ▸ Submodule.mem_top
    exact this
  let u := (IsUnit.of_mul_eq_one _ hIJ).unit
  have h1 : Module.Invertible A (u : Submodule A (FractionRing A)) := inferInstance
  have h2 : Module.Invertible A (Submodule.map (Algebra.linearMap A (FractionRing A)) P) := h1
  exact Module.Invertible.congr
    (Submodule.equivMapOfInjective (Algebra.linearMap A (FractionRing A)) hinj P).symm

/-- If `R_Q` is a UFD, a height-one prime `p` of `R` is principal near `Q`. -/
theorem exists_dvd_of_ufd_localization {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (Q : Ideal R) [Q.IsPrime]
    [IsDomain (Localization.AtPrime Q)] [UniqueFactorizationMonoid (Localization.AtPrime Q)] :
    ∃ a ∈ p, a ≠ 0 ∧ ∃ s ∉ Q, ∀ y ∈ p, a ∣ s * y := by
  by_cases hpQ : p ≤ Q
  swap
  · obtain ⟨t, htp, htQ⟩ := SetLike.not_le_iff_exists.mp hpQ
    exact ⟨t, htp, fun h => htQ (h ▸ Q.zero_mem), t, htQ, fun y _ => dvd_mul_right t y⟩
  have hd : Disjoint (Q.primeCompl : Set R) p :=
    Set.disjoint_left.mpr fun t ht htp => ht (hpQ htp)
  have hQp : (p.map (algebraMap R (Localization.AtPrime Q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ p ‹_› hd
  have hh : (p.map (algebraMap R (Localization.AtPrime Q))).height = 1 := by
    rw [← IsLocalization.height_under Q.primeCompl,
      IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl _ ‹p.IsPrime› hd, hp]
  obtain ⟨g, hg⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
  have hg0 : g ∈ p.map (algebraMap R (Localization.AtPrime Q)) :=
    hg ▸ Submodule.mem_span_singleton_self g
  obtain ⟨⟨a, t⟩, hat⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl _).mp hg0
  have hspan : p.map (algebraMap R (Localization.AtPrime Q)) =
      Ideal.span {algebraMap R (Localization.AtPrime Q) a} := by
    rw [hg, ← hat]
    exact (Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ t) g).symm
  have ha0 : (a : R) ≠ 0 := by
    intro h0
    refine Ideal.ne_bot_of_height_eq_one hh ?_
    rw [hspan, h0, map_zero, Ideal.span_singleton_eq_bot]
  have hloc : ∀ y ∈ p, ∃ t' ∈ Q.primeCompl, (a : R) ∣ t' * y := by
    intro y hy
    have hy' : algebraMap R (Localization.AtPrime Q) y ∈
        Ideal.span {algebraMap R (Localization.AtPrime Q) a} :=
      hspan ▸ Ideal.mem_map_of_mem _ hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hy'
    obtain ⟨⟨r, t'⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl c
    have he : algebraMap R (Localization.AtPrime Q) (r * a) =
        algebraMap R (Localization.AtPrime Q) (t' * y) := by
      rw [map_mul, map_mul, ← hc, ← mul_assoc, IsLocalization.mk'_spec']
    have := IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors he
    exact ⟨t', t'.2, r, by rw [← this, mul_comm]⟩
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian p : p.FG)
  choose! t' ht' hdvd using hloc
  have hGp : ∀ g ∈ G, g ∈ p := fun g hg => hG ▸ Submodule.subset_span hg
  refine ⟨a, a.2, ha0, ∏ g ∈ G, t' g, ?_, fun y hy => ?_⟩
  · exact Q.primeCompl.prod_mem fun g hg => ht' g (hGp g hg)
  rw [← hG] at hy
  refine Submodule.span_induction (fun g hg => ?_) ?_ (fun u v _ _ hu hv => ?_)
    (fun c u _ hu => ?_) hy
  · obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem t' hg
    rw [hw, mul_comm (t' g) w, mul_assoc]
    exact Dvd.dvd.mul_left (hdvd g (hGp g hg)) w
  · simp
  · rw [mul_add]
    exact dvd_add hu hv
  · rw [smul_eq_mul, mul_left_comm]
    exact Dvd.dvd.mul_left hu c

variable {R : Type u} [CommRing R]

/-- O9 core: for `x ∈ m \ m²` and a height-one prime `p ∌ x`, `p R_x` is principal, provided every
`R_Q` with `Q ≠ m` is a UFD. -/
theorem isPrincipal_map_away [IsRegularLocalRing R] {x : R} (hx0 : x ≠ 0)
    (hxm : x ∈ maximalIdeal R) (p : Ideal R) [p.IsPrime] (hp : p.height = 1)
    (hQ : ∀ (Q : Ideal R) [Q.IsPrime], x ∉ Q →
      UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    (p.map (algebraMap R (Localization.Away x))).IsPrincipal := by
  have : IsDomain (Localization.Away x) := IsLocalization.Away.isDomain _ hx0
  have hinjA := IsLocalization.injective (Localization.Away x)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  have hInv : Module.Invertible (Localization.Away x)
      (p.map (algebraMap R (Localization.Away x))) := by
    refine invertible_of_forall_isMaximal _ fun M hM => ?_
    have hxQ : x ∉ M.comap (algebraMap R (Localization.Away x)) := fun h =>
      hM.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit x))
    have := hQ _ hxQ
    obtain ⟨a, ha, ha0, s, hs, hdiv⟩ :=
      exists_dvd_of_ufd_localization p hp (M.comap (algebraMap R (Localization.Away x)))
    refine ⟨algebraMap R _ a, Ideal.mem_map_of_mem _ ha, (map_ne_zero_iff _ hinjA).mpr ha0,
      algebraMap R _ s, hs, fun y hy => ?_⟩
    refine Submodule.span_induction (fun g hg => ?_) ?_ (fun u v _ _ hu hv => ?_)
      (fun c u _ hu => ?_) hy
    · obtain ⟨h, hh, rfl⟩ := hg
      rw [← map_mul]
      exact map_dvd _ (hdiv h hh)
    · simp
    · rw [mul_add]
      exact dvd_add hu hv
    · rw [smul_eq_mul, mul_left_comm]
      exact Dvd.dvd.mul_left hu c
  obtain ⟨n, hn⟩ := exists_hasPDLT_of_isRegularLocalRing (ModuleCat.of R p)
  have hn' : HasProjectiveDimensionLT (ModuleCat.of R p) (n + 1) :=
    hasProjectiveDimensionLT_of_ge _ n (n + 1) (by omega)
  have h1 : HasFFR R n p := hasFFR_of_hasPDLT n (ModuleCat.of R p) inferInstance hn'
  have h2 := hasFFR_of_isLocalizedModule (Submonoid.powers x) (Localization.Away x) n p h1 _
    (p.toLocalized' (Localization.Away x) (Submonoid.powers x)
      (Algebra.linearMap R (Localization.Away x)))
  have h3 : HasFFR (Localization.Away x) n (p.map (algebraMap R (Localization.Away x))) :=
    h2.of_equiv (LinearEquiv.ofEq _ _
      (Ideal.localized'_eq_map (Localization.Away x) (Submonoid.powers x) p))
  have : Module.IsStablyFree (Localization.Away x)
      (p.map (algebraMap R (Localization.Away x))) := isStablyFree_of_hasFFR n _ h3
  have := Module.free_of_isStablyFree_of_invertible (Localization.Away x)
    (p.map (algebraMap R (Localization.Away x)))
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp this
  refine ⟨⟨(e.symm 1 : Localization.Away x), le_antisymm (fun y hy => ?_)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr (e.symm 1).2)⟩⟩
  rw [Submodule.mem_span_singleton]
  refine ⟨e ⟨y, hy⟩, ?_⟩
  have he : e.symm (e ⟨y, hy⟩) = e ⟨y, hy⟩ • e.symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [e.symm_apply_apply] at he
  exact (congrArg Subtype.val he).symm

theorem uniqueFactorizationMonoid_aux : ∀ (k : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
    ringKrullDim R = k → UniqueFactorizationMonoid R := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro R _ _ hk
  rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
  intro p _ hp1
  have hk0 : (maximalIdeal R).spanFinrank ≠ 0 := by
    intro h0
    have h1 := Ideal.height_le_ringKrullDim_of_isPrime (I := p)
    rw [hp1, ← IsRegularLocalRing.spanFinrank_maximalIdeal, h0] at h1
    exact absurd h1 (by decide)
  obtain ⟨x, hxm, hx2⟩ := exists_mem_maximalIdeal_not_mem_sq hk0
  have hx0 : x ≠ 0 := fun h => hx2 (h ▸ Ideal.zero_mem _)
  have hxp : Prime x := (Ideal.span_singleton_prime hx0).mp (isPrime_span_of_not_mem_sq hxm hx2)
  by_cases hxP : x ∈ p
  · exact ⟨x, p.eq_span_singleton_of_height_eq_one hp1 hxP hxp⟩
  refine p.isPrincipal_of_isPrincipal_localizationAway_of_prime hxp hxP
    (isPrincipal_map_away hx0 hxm p hp1 fun Q _ hxQ => ?_)
  have hQm : Q ≠ maximalIdeal R := fun h => hxQ (h ▸ hxm)
  have hlt : Q.height < ringKrullDim R := lt_of_le_of_ne Ideal.height_le_ringKrullDim_of_isPrime
    fun h => hQm (Ideal.height_eq_ringKrullDim_iff.mp h)
  have := isRegularLocalRing_localization Q
  obtain ⟨k', hk'⟩ := exists_nat_ringKrullDim_eq (R := Localization.AtPrime Q)
  have hkk : k' < k := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q), hk', hk] at hlt
    exact_mod_cast hlt
  exact ih k' hkk _ hk'

/-- O9 (Auslander-Buchsbaum): a regular local ring is a UFD. -/
theorem uniqueFactorizationMonoid_of_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : UniqueFactorizationMonoid R := by
  obtain ⟨k, hk⟩ := exists_nat_ringKrullDim_eq (R := R)
  exact uniqueFactorizationMonoid_aux k R hk

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_IsogDegA_QF =====
section

/-!
# S4-IsogDegA, file QF: a dominant endomorphism of a proper group variety is finite (O3)

`Q = {x | φ quasi-finite at x}` is open, translation invariant (`transl_comp_hom`), and contains the
generic point when `K(A)` is finite over `φ^* K(A)`. By the Jacobson property `Q = A`, so `φ` is
locally quasi-finite; it is proper, hence finite (`IsFinite.of_isProper_of_locallyQuasiFinite`),
and surjective (closed dense range).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology MonObj

namespace RamanujanPetersson.IsogDegA

theorem quasiFiniteAt_iff_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    f.QuasiFiniteAt x ↔
      (Y.presheaf.stalkSpecializes (specializes_of_eq h) ≫ f.stalkMap x).hom.QuasiFinite := by
  subst h
  simp [Scheme.Hom.QuasiFiniteAt]

theorem quasiFiniteAt_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] (hf : (ffMap f).hom.Finite) :
    f.QuasiFiniteAt (genericPoint X) :=
  (quasiFiniteAt_iff_of_eq f _ _ (map_genericPoint f)).2 (RingHom.QuasiFinite.of_finite hf)

section Abelian

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

theorem isIso_transl_left (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : IsIso (transl A a).left :=
  ⟨⟨(transl A a⁻¹).left, by
    rw [← Over.comp_left, transl_comp_transl, _root_.mul_inv_cancel, transl_one, Over.id_left], by
    rw [← Over.comp_left, transl_comp_transl, _root_.inv_mul_cancel, transl_one, Over.id_left]⟩⟩

variable (φ : A ⟶ A) [IsMonHom φ]

theorem quasiFiniteAt_transl_iff (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) (x : A.left) :
    φ.left.QuasiFiniteAt ((transl A a).left x) ↔ φ.left.QuasiFiniteAt x := by
  have := isIso_transl_left A a
  have := isIso_transl_left A (a ≫ φ)
  have h1 : ((transl A a).left ≫ φ.left).QuasiFiniteAt x ↔
      φ.left.QuasiFiniteAt ((transl A a).left x) :=
    Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
  have h2 : (φ.left ≫ (transl A (a ≫ φ)).left).QuasiFiniteAt x ↔ φ.left.QuasiFiniteAt x :=
    Scheme.Hom.quasiFiniteAt_comp_iff
  rw [← h1, ← Over.comp_left, transl_comp_hom, Over.comp_left, h2]

variable [IsAlgClosed k] [IsProper A.hom]

instance locallyOfFiniteType_left : LocallyOfFiniteType φ.left := by
  have : LocallyOfFiniteType (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  exact locallyOfFiniteType_of_comp φ.left A.hom

omit [GrpObj A] [IsMonHom φ] [IsAlgClosed k] in
theorem isProper_left : IsProper φ.left := by
  have : IsProper (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  exact IsProper.of_comp φ.left A.hom

/-- One quasi-finite point makes `φ` locally quasi-finite. -/
theorem locallyQuasiFinite_of_quasiFiniteAt (x₀ : A.left) (h₀ : φ.left.QuasiFiniteAt x₀) :
    LocallyQuasiFinite φ.left := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hQ : IsOpen {x | φ.left.QuasiFiniteAt x} := φ.left.isOpen_quasiFiniteAt
  obtain ⟨x₁, hx₁Q, hx₁⟩ := nonempty_inter_closedPoints ⟨x₀, h₀⟩ hQ.isLocallyClosed
  have hcl : ∀ z : A.left, IsClosed {z} → φ.left.QuasiFiniteAt z := fun z hz ↦ by
    obtain ⟨a, rfl⟩ := exists_transl_eq A x₁ z hx₁ hz
    exact (quasiFiniteAt_transl_iff A φ a x₁).2 hx₁Q
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  refine top_le_iff.1 fun x _ ↦ Scheme.Hom.mem_quasiFiniteLocus.2 ?_
  by_contra hx
  obtain ⟨z, hzQ, hz⟩ := nonempty_inter_closedPoints (Z := {x | ¬ φ.left.QuasiFiniteAt x}) ⟨x, hx⟩
    hQ.isClosed_compl.isLocallyClosed
  exact hzQ (hcl z hz)

/-- O3: a dominant endomorphism with `K(A)` finite over `φ^* K(A)` is finite. -/
theorem isFinite_of_isDominant [IsIntegral A.left] [IsDominant φ.left]
    (hfin : (ffMap φ.left).hom.Finite) : IsFinite φ.left := by
  have := isProper_left A φ
  have := locallyQuasiFinite_of_quasiFiniteAt A φ _ (quasiFiniteAt_genericPoint φ.left hfin)
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ.left

omit [GrpObj A] [IsMonHom φ] [IsAlgClosed k] in
/-- A dominant endomorphism is surjective. -/
theorem surjective_of_isDominant [IsDominant φ.left] : Surjective φ.left := by
  have := isProper_left A φ
  exact surjective_of_isDominant_of_isClosed_range φ.left φ.left.isClosedMap.isClosed_range

end Abelian

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IsogDegA_Trdeg =====
section

/-!
# S4-IsogDegA, file Trdeg: `K(A)` is finite over `φ^* K(A)` (O3 without the hypothesis)

Abstractly: if `K ≃ₐ[k] L` and `L` is essentially of finite type over `k`, then in a tower
`k → K → L` the extension `L/K` has transcendence degree `0` (degrees add, `trdeg k L < ℵ₀`),
so it is algebraic and essentially of finite type, hence finite.
For a dominant endomorphism `φ` of `A` over `Spec k`, `φ^*` is a `k`-algebra map
(`Over.w φ`), and `K(A)` is essentially of finite type over `k` (`A` locally of finite type).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology

namespace RamanujanPetersson.IsogDegA

/-- In a tower `k → K → L` with `K ≃ₐ[k] L` and `L` essentially of finite type over `k`,
`L` is finite over `K`. -/
theorem finiteDimensional_of_algEquiv {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [hKL : Algebra K L] [IsScalarTower k K L] (e : K ≃ₐ[k] L)
    [Algebra.EssFiniteType k L] : FiniteDimensional K L := by
  have hadd := trdeg_add_eq k K (A := L)
  rw [e.trdeg_eq] at hadd
  have h0 : Algebra.trdeg K L = 0 :=
    Cardinal.eq_of_add_eq_add_left (hadd.trans (add_zero _).symm) (trdeg_lt_aleph0 k L)
  have : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.1 h0
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp k K L
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem appTop_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.appTop ≫ X.presheaf.germ ⊤ x trivial = Y.presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x :=
  (Scheme.Hom.germ_stalkMap f ⊤ x trivial).symm

/-- `f^*` on global sections and on function fields agree. -/
theorem germ_ffMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsDominant f] :
    Y.presheaf.germ ⊤ (genericPoint Y) trivial ≫ ffMap f =
      f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
  rw [appTop_germ, ffMap, ← Category.assoc]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes _ _ _

section Variety

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- The structure map `k → Γ(Spec k) → Γ(A) → K(A)`. -/
noncomputable def kMap [IrreducibleSpace A.left] : k →+* A.left.functionField :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
    A.left.presheaf.germ ⊤ (genericPoint A.left) trivial).hom

theorem essFiniteType_kMap [IrreducibleSpace A.left] [LocallyOfFiniteType A.hom] :
    (kMap A).EssFiniteType := by
  rw [kMap, appTop_germ, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.EssFiniteType.comp ?_
    (RingHom.EssFiniteType.comp ?_ (LocallyOfFiniteType.stalkMap A.hom _))
  · exact (RingHom.FiniteType.of_surjective _
      fun x ↦ ⟨(Scheme.ΓSpecIso (.of k)).hom x, by simp⟩).essFiniteType
  · let x : (⊤ : (Spec (.of k)).Opens) := ⟨A.hom (genericPoint A.left), trivial⟩
    letI := TopCat.Presheaf.algebra_section_stalk (Spec (.of k)).presheaf x
    have := (isAffineOpen_top (Spec (.of k))).isLocalization_stalk x
    exact RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _
      ((isAffineOpen_top (Spec (.of k))).primeIdealOf x).asIdeal.primeCompl)

/-- `φ^*` is a `k`-algebra map. -/
theorem ffMap_comp_kMap [IsIntegral A.left] (φ : A ⟶ A) [IsDominant φ.left] :
    (ffMap φ.left).hom.comp (kMap A) = kMap A := by
  rw [kMap, ← CommRingCat.hom_comp, Category.assoc, Category.assoc, germ_ffMap,
    ← Category.assoc A.hom.appTop, ← Scheme.Hom.comp_appTop, Over.w φ]

/-- `K(A)` is finite over `φ^* K(A)`. -/
theorem ffMap_finite [IsIntegral A.left] [LocallyOfFiniteType A.hom] (φ : A ⟶ A)
    [IsDominant φ.left] : (ffMap φ.left).hom.Finite := by
  letI i : Algebra k A.left.functionField := (kMap A).toAlgebra
  haveI hE : Algebra.EssFiniteType k A.left.functionField := essFiniteType_kMap A
  have hT := @IsScalarTower.of_algebraMap_eq' k A.left.functionField A.left.functionField _ _ _
    i (ffAlgebra φ.left) i (ffMap_comp_kMap A φ).symm
  exact @finiteDimensional_of_algEquiv k _ _ _ _ _ i i (ffAlgebra φ.left) hT
    (AlgEquiv.refl) hE

variable [GrpObj A] (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]

/-- O3: a dominant endomorphism of a proper group variety is finite. -/
theorem isFinite_left [IsIntegral A.left] [IsDominant φ.left] : IsFinite φ.left :=
  isFinite_of_isDominant A φ (ffMap_finite A φ)

end Variety

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IsogDegA_Mult =====
section

/-!
# S4-IsogDegA, file Mult: the degree is multiplicative (O4)

If `f ≫ g` is dominant and `g` has discrete fibres, then `f` is dominant: `g` sends both the
generic point `η` and `f η` (a specialization of `η`) to the generic point, and a discrete
fibre has no nontrivial specializations. Together with `degree_comp` (dominant pairs) this gives
`degree (f ≫ g) = degree f * degree g` whenever `g` is locally quasi-finite once dominant, in
particular for every composite of endomorphisms of a proper group variety (O3: dominant ⇒ finite).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology

namespace RamanujanPetersson.IsogDegA

/-- A morphism sending the generic point to the generic point is dominant. -/
theorem isDominant_of_map_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] (h : f (genericPoint X) = genericPoint Y) : IsDominant f := by
  rw [isDominant_iff, DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff,
    ← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.2 ⟨_, h⟩)

/-- If `f ≫ g` is dominant and `g` is locally quasi-finite, `f` is dominant. -/
theorem isDominant_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace Z] [LocallyQuasiFinite g] [IsDominant (f ≫ g)] :
    IsDominant f := by
  have : IsDominant g := IsDominant.of_comp (f := f) (g := g)
  have h1 := map_genericPoint (f ≫ g)
  have h2 := map_genericPoint g
  apply isDominant_of_map_genericPoint
  refine ((g.isDiscrete_preimage_singleton (genericPoint Z)).eq_of_specializes
    ((genericPoint_spec Y).specializes trivial) h2 ?_).symm
  simpa using h1

/-- Multiplicativity of the degree, including the non-dominant cases. -/
theorem degree_comp_of_lqf {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] (hg : IsDominant g → LocallyQuasiFinite g) :
    degree (f ≫ g) = degree f * degree g := by
  by_cases hfg : IsDominant (f ≫ g)
  · have : IsDominant g := IsDominant.of_comp (f := f) (g := g)
    have := hg this
    have := isDominant_of_comp f g
    exact degree_comp f g
  · rw [degree_of_not_isDominant _ hfg]
    by_cases hgd : IsDominant g
    · have hf : ¬ IsDominant f := fun _ ↦ hfg inferInstance
      rw [degree_of_not_isDominant _ hf, zero_mul]
    · rw [degree_of_not_isDominant _ hgd, mul_zero]

section Variety

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsAlgClosed k]
  [IsProper A.hom] [IsIntegral A.left]

/-- O4: `deg (φ ∘ ψ) = deg ψ * deg φ` for endomorphisms `ψ`, `φ` (`φ` a group hom). -/
theorem degree_comp_left (ψ φ : A ⟶ A) [IsMonHom φ] :
    degree (ψ ≫ φ).left = degree ψ.left * degree φ.left := by
  rw [Over.comp_left]
  refine degree_comp_of_lqf _ _ fun _ ↦ ?_
  have := isFinite_left A φ
  infer_instance

/-- O4 for group homomorphisms (both factors). -/
theorem degree_comp_left' (ψ φ : A ⟶ A) [IsMonHom ψ] [IsMonHom φ] :
    degree (ψ ≫ φ).left = degree φ.left * degree ψ.left := by
  rw [degree_comp_left, mul_comm]

end Variety

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IsogDegB_Der =====
section

/-!
# S4-IsogDegB, tangent vectors from the cotangent space (lemma L27 of S4_COREB_ROUTE.md §3)

`R` a local `k`-algebra with a `k`-point `ev : R →ₐ[k] k` (kernel `𝔪_R`), `S → R` local. If
`𝔪_R ⊄ 𝔪_S R + 𝔪_R²` (the cotangent map is not surjective) there is a `k`-algebra map
`h : R → k[ε]` lifting `ev`, killing `𝔪_S` in the `ε`-part and nonzero in the `ε`-part
(a nonzero tangent vector killed by the differential).
-/

set_option autoImplicit false

namespace RamanujanPetersson.IsogDegB

open IsLocalRing

section Der

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- The pointed derivation `r ↦ l (r - ev r)`. -/
def dmap (ev : R →ₐ[k] k) (l : R →ₗ[k] k) : R →ₗ[k] k :=
  l ∘ₗ (LinearMap.id - Algebra.linearMap k R ∘ₗ ev.toLinearMap)

theorem dmap_apply (ev : R →ₐ[k] k) (l : R →ₗ[k] k) (r : R) :
    dmap ev l r = l (r - algebraMap k R (ev r)) := rfl

theorem dmap_algebraMap (ev : R →ₐ[k] k) (l : R →ₗ[k] k) (c : k) :
    dmap ev l (algebraMap k R c) = 0 := by
  simp [dmap_apply]

/-- Leibniz rule for `dmap`, given that `l` kills products of elements of `ker ev`. -/
theorem dmap_mul (ev : R →ₐ[k] k) (l : R →ₗ[k] k)
    (hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0) (a b : R) :
    dmap ev l (a * b) = ev a * dmap ev l b + ev b * dmap ev l a := by
  have key : a * b - algebraMap k R (ev (a * b)) =
      (a - algebraMap k R (ev a)) * (b - algebraMap k R (ev b)) +
      ev a • (b - algebraMap k R (ev b)) + ev b • (a - algebraMap k R (ev a)) := by
    rw [map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]; ring
  rw [dmap_apply, key, map_add, map_add, map_smul, map_smul,
    hl _ _ (by simp) (by simp), zero_add, dmap_apply, dmap_apply, smul_eq_mul, smul_eq_mul]

/-- The `k`-linear map `r ↦ ev r + ε · dmap r` into the dual numbers. -/
def toDualLin (ev : R →ₐ[k] k) (l : R →ₗ[k] k) : R →ₗ[k] DualNumber k :=
  Algebra.linearMap k (DualNumber k) ∘ₗ ev.toLinearMap + TrivSqZeroExt.inrHom k k ∘ₗ dmap ev l

theorem toDualLin_fst (ev : R →ₐ[k] k) (l : R →ₗ[k] k) (r : R) :
    (toDualLin ev l r).fst = ev r := by
  simp [toDualLin, TrivSqZeroExt.algebraMap_eq_inl]

theorem toDualLin_snd (ev : R →ₐ[k] k) (l : R →ₗ[k] k) (r : R) :
    (toDualLin ev l r).snd = dmap ev l r := by
  simp [toDualLin, TrivSqZeroExt.algebraMap_eq_inl]

/-- The `k`-algebra map `R → k[ε]` attached to a functional killing `(ker ev)²`. -/
def toDual (ev : R →ₐ[k] k) (l : R →ₗ[k] k)
    (hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0) : R →ₐ[k] DualNumber k :=
  AlgHom.ofLinearMap (toDualLin ev l)
    (by
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [toDualLin_fst, map_one, TrivSqZeroExt.fst_one]
      · rw [toDualLin_snd, TrivSqZeroExt.snd_one, ← map_one (algebraMap k R), dmap_algebraMap])
    (fun a b ↦ by
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [toDualLin_fst, map_mul, TrivSqZeroExt.fst_mul, toDualLin_fst, toDualLin_fst]
      · rw [toDualLin_snd, TrivSqZeroExt.snd_mul, toDualLin_fst, toDualLin_fst, toDualLin_snd,
          toDualLin_snd, dmap_mul ev l hl, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
          smul_eq_mul, mul_comm (dmap ev l a)])

theorem toDual_fst (ev : R →ₐ[k] k) (l : R →ₗ[k] k)
    (hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0) (r : R) :
    (toDual ev l hl r).fst = ev r := toDualLin_fst ev l r

theorem toDual_snd (ev : R →ₐ[k] k) (l : R →ₗ[k] k)
    (hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0) (r : R) :
    (toDual ev l hl r).snd = dmap ev l r := toDualLin_snd ev l r

end Der

section Lambda

variable {k S R : Type*} [Field k] [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
  [Algebra S R] [IsLocalHom (algebraMap S R)] [Algebra k R]

theorem ev_eq_zero_iff (ev : R →ₐ[k] k) (hm : ∀ r, ev r = 0 → r ∈ maximalIdeal R) (r : R) :
    ev r = 0 ↔ r ∈ maximalIdeal R := by
  refine ⟨hm r, fun hr ↦ by_contra fun h0 ↦ ?_⟩
  have h1 : r - algebraMap k R (ev r) ∈ maximalIdeal R := hm _ (by simp)
  have h2 : algebraMap k R (ev r) ∈ maximalIdeal R := by
    simpa using Ideal.sub_mem _ hr h1
  exact (mem_maximalIdeal _).1 h2 ((Ne.isUnit h0).map (algebraMap k R))

/-- **Alg-1.** A non-surjective cotangent map gives a nonzero tangent vector killed by `S`. -/
theorem exists_tangent_of_not_le (ev : R →ₐ[k] k) (hm : ∀ r, ev r = 0 → r ∈ maximalIdeal R)
    (hJ : ¬ maximalIdeal R ≤ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    ∃ h : R →ₐ[k] DualNumber k, (∀ r, (h r).fst = ev r) ∧
      (∀ s ∈ maximalIdeal S, (h (algebraMap S R s)).snd = 0) ∧ ∃ r, (h r).snd ≠ 0 := by
  set J := Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2
  obtain ⟨x, hxm, hxJ⟩ := Set.not_subset.1 hJ
  have hx : x ∉ J.restrictScalars k := hxJ
  obtain ⟨l, hlx, hlJ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hl0 : ∀ y ∈ J, l y = 0 := fun y hy ↦
    LinearMap.mem_ker.1 (LinearMap.le_ker_iff_map.2 hlJ (show y ∈ J.restrictScalars k from hy))
  have hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0 := fun a b ha hb ↦
    hl0 _ (Ideal.mem_sup_right (by
      rw [pow_two]; exact Ideal.mul_mem_mul ((ev_eq_zero_iff ev hm a).1 ha)
        ((ev_eq_zero_iff ev hm b).1 hb)))
  refine ⟨toDual ev l hl, toDual_fst ev l hl, fun s hs ↦ ?_, x, ?_⟩
  · have hsm := algebraMap_mem_maximalIdeal (R := R) hs
    rw [toDual_snd, dmap_apply, (ev_eq_zero_iff ev hm _).2 hsm, map_zero, sub_zero]
    exact hl0 _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hs))
  · rw [toDual_snd, dmap_apply, (ev_eq_zero_iff ev hm _).2 hxm, map_zero, sub_zero]
    exact hlx

end Lambda

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_IsogDegB_TanA =====
section

/-!
# S4-IsogDegB, the tangent space at the identity (lemma L27 of S4_COREB_ROUTE.md §3)

`T A := {t : Spec k[ε] ⟶ A // ι0 ≫ t = 1}` (a subgroup of the Hom-group), `dφ t := t ≫ φ`.
A tangent vector is determined by its stalk map `tvec t : 𝒪_{A,e} → k[ε]` (whose `ε`-free part is the
fixed `k`-point `ev0`), hence by the `ε`-parts `(tvec t r).snd`.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Stalk

variable {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]

theorem exists_stalkLift (f : Spec R ⟶ X) {x : X} (hx : f (closedPoint R) = x) :
    ∃ g : X.presheaf.stalk x ⟶ R, IsLocalHom g.hom ∧ Spec.map g ≫ X.fromSpecStalk x = f := by
  subst hx
  exact ⟨_, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem stalkLift_injective {x : X} (g₁ g₂ : X.presheaf.stalk x ⟶ R) [IsLocalHom g₁.hom]
    [IsLocalHom g₂.hom] (h : Spec.map g₁ ≫ X.fromSpecStalk x = Spec.map g₂ ≫ X.fromSpecStalk x) :
    g₁ = g₂ := by
  have := (SpecToEquivOfLocalRing X R).symm.injective
    (a₁ := ⟨x, g₁, inferInstance⟩) (a₂ := ⟨x, g₂, inferInstance⟩) h
  obtain ⟨_, e⟩ := SpecToEquivOfLocalRing_eq_iff.1 this
  simpa using e

end Stalk

section Tangent

variable (k : Type u) [Field k]

/-- `Spec k[ε]` over `k`. -/
noncomputable abbrev DS : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- `ε ↦ 0`. -/
noncomputable abbrev fstC : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom

instance : IsLocalHom (fstC k).hom := ⟨fun _ hx ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hx⟩

/-- The `k`-point of `Spec k[ε]`. -/
noncomputable def ι0 : 𝟙_ (Over (Spec (.of k))) ⟶ DS k :=
  Over.homMk (Spec.map (fstC k)) (by
    have h : CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫ fstC k = 𝟙 _ := by
      ext x; simp
    change Spec.map (fstC k) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) = 𝟙 _
    rw [← Spec.map_comp, h, Spec.map_id])

theorem DS_eq_closedPoint (x : PrimeSpectrum (DualNumber k)) : x = closedPoint (DualNumber k) := by
  have hε : (DualNumber.eps : DualNumber k) ∈ x.asIdeal := by
    rcases x.isPrime.mem_or_mem (show DualNumber.eps * DualNumber.eps ∈ x.asIdeal by
      rw [DualNumber.eps_mul_eps]; exact x.asIdeal.zero_mem) with h | h <;> exact h
  have hle : maximalIdeal (DualNumber k) ≤ x.asIdeal := by
    rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_le, Set.singleton_subset_iff]
    exact hε
  exact PrimeSpectrum.ext ((maximalIdeal.isMaximal _).eq_of_le x.isPrime.ne_top hle).symm

variable {k} (A : Over (Spec (.of k))) [GrpObj A]

theorem left_closedPoint (t : DS k ⟶ A) (ht : ι0 k ≫ t = 1) :
    t.left (closedPoint (DualNumber k)) = pt A 1 := by
  rw [← ht, pt_comp]
  congr 1
  exact (DS_eq_closedPoint k _).symm

/-- Restriction along `ι0`. -/
noncomputable def resι : (DS k ⟶ A) →* (𝟙_ (Over (Spec (.of k))) ⟶ A) where
  toFun t := ι0 k ≫ t
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- The tangent space of `A` at the identity. -/
noncomputable def Tan : Subgroup (DS k ⟶ A) := (resι A).ker

variable {A}

theorem tan_spec (t : Tan A) : ι0 k ≫ t.1 = 1 := MonoidHom.mem_ker.1 t.2

/-- The differential of a homomorphism at the identity. -/
noncomputable def dφ (φ : A ⟶ A) [IsMonHom φ] : Tan A →* Tan A where
  toFun t := ⟨t.1 ≫ φ, MonoidHom.mem_ker.2 (by
    show ι0 k ≫ t.1 ≫ φ = 1
    rw [← Category.assoc, tan_spec, MonObj.one_comp])⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' t s := Subtype.ext (MonObj.mul_comp _ _ _)

theorem dφ_val (φ : A ⟶ A) [IsMonHom φ] (t : Tan A) : (dφ φ t).1 = t.1 ≫ φ := rfl

/-- `d(φ + ψ) = dφ + dψ` in the Hom-group (L27 (i)). -/
theorem comp_mul_tan (t : DS k ⟶ A) (φ ψ : A ⟶ A) : t ≫ (φ * ψ) = (t ≫ φ) * (t ≫ ψ) :=
  MonObj.comp_mul _ _ _

theorem exists_tvec (t : Tan A) :
    ∃ g : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k),
      IsLocalHom g.hom ∧ Spec.map g ≫ A.left.fromSpecStalk (pt A 1) = t.1.left :=
  exists_stalkLift (R := CommRingCat.of (DualNumber k)) t.1.left (left_closedPoint A t.1 (tan_spec t))

/-- The stalk map `𝒪_{A,e} → k[ε]` of a tangent vector. -/
noncomputable def tvec (t : Tan A) : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k) :=
  (exists_tvec t).choose

instance (t : Tan A) : IsLocalHom (tvec t).hom := (exists_tvec t).choose_spec.1

theorem tvec_spec (t : Tan A) : Spec.map (tvec t) ≫ A.left.fromSpecStalk (pt A 1) = t.1.left :=
  (exists_tvec t).choose_spec.2

variable (A) in
theorem exists_ev0 : ∃ g : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of k, IsLocalHom g.hom ∧
    Spec.map g ≫ A.left.fromSpecStalk (pt A 1) = (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A).left :=
  exists_stalkLift (R := CommRingCat.of k) (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A).left rfl

variable (A) in
/-- Evaluation at the identity point, `𝒪_{A,e} → k`. -/
noncomputable def ev0 : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of k := (exists_ev0 A).choose

instance : IsLocalHom (ev0 A).hom := (exists_ev0 A).choose_spec.1

theorem ev0_spec : Spec.map (ev0 A) ≫ A.left.fromSpecStalk (pt A 1) =
    (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A).left := (exists_ev0 A).choose_spec.2

theorem tvec_fst (t : Tan A) : tvec t ≫ fstC k = ev0 A := by
  have : IsLocalHom (tvec t ≫ fstC k).hom := by rw [CommRingCat.hom_comp]; infer_instance
  apply stalkLift_injective
  rw [Spec.map_comp, Category.assoc, tvec_spec, ev0_spec]
  exact congrArg CommaMorphism.left (tan_spec t)

/-- The `ε`-part of a tangent vector. -/
noncomputable def coeff (t : Tan A) (r : A.left.presheaf.stalk (pt A 1)) : k := ((tvec t).hom r).snd

theorem fst_tvec (t : Tan A) (r : A.left.presheaf.stalk (pt A 1)) :
    ((tvec t).hom r).fst = (ev0 A).hom r :=
  congrArg (fun g ↦ g.hom r) (tvec_fst t)

theorem tan_ext {t s : Tan A} (h : ∀ r, coeff t r = coeff s r) : t = s := by
  have hv : tvec t = tvec s := by
    ext r
    · exact (fst_tvec t r).trans (fst_tvec s r).symm
    · exact h r
  apply Subtype.ext
  apply Over.OverMorphism.ext
  rw [← tvec_spec t, ← tvec_spec s, hv]

end Tangent

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_IsogDegB_TanB =====
section

/-!
# S4-IsogDegB, differentials on stalks and tangent vectors from stalk maps (L27 of S4_COREB_ROUTE.md §3)

`tvec (dφ t) = φ♯ ≫ tvec t` with `φ♯ : 𝒪_{A,e} → 𝒪_{A,e}` the stalk map of `φ` at the identity;
the structure map `kS A : k → 𝒪_{A,e}` (so `kS ≫ ev0 = 𝟙`); every local `h : 𝒪_{A,e} → k[ε]` with
`h ≫ fst = ev0` and `kS ≫ h = algebraMap` is `tvec` of a tangent vector.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Stalk

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}

theorem stalkLift_comp (f : X ⟶ Y) {x : X} {y : Y} (hxy : f x = y) (g : X.presheaf.stalk x ⟶ R) :
    Spec.map ((Y.presheaf.stalkSpecializes (specializes_of_eq hxy) ≫ f.stalkMap x) ≫ g) ≫
      Y.fromSpecStalk y = Spec.map g ≫ X.fromSpecStalk x ≫ f := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem stalkSpec_fromSpecStalk (f : X ⟶ Y) {x : X} {y : Y} (hxy : f x = y) :
    Spec.map (Y.presheaf.stalkSpecializes (specializes_of_eq hxy) ≫ f.stalkMap x) ≫
      Y.fromSpecStalk y = X.fromSpecStalk x ≫ f := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem isLocalHom_stalkLift (f : X ⟶ Y) {x : X} {y : Y} (hxy : f x = y)
    (g : X.presheaf.stalk x ⟶ R) [IsLocalHom g.hom] :
    IsLocalHom ((Y.presheaf.stalkSpecializes (specializes_of_eq hxy) ≫ f.stalkMap x) ≫ g).hom := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, CommRingCat.hom_comp]
  infer_instance

end Stalk

section Tangent

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

theorem left_pt_one (φ : A ⟶ A) [IsMonHom φ] : φ.left (pt A 1) = pt A 1 := by
  rw [← pt_comp, MonObj.one_comp]

/-- The stalk map `φ♯ : 𝒪_{A,e} → 𝒪_{A,e}` of `φ` at the identity. -/
noncomputable abbrev sharp (φ : A ⟶ A) [IsMonHom φ] :
    A.left.presheaf.stalk (pt A 1) ⟶ A.left.presheaf.stalk (pt A 1) :=
  A.left.presheaf.stalkSpecializes (specializes_of_eq (left_pt_one φ)) ≫ φ.left.stalkMap (pt A 1)

theorem tvec_dφ (φ : A ⟶ A) [IsMonHom φ] (t : Tan A) : tvec (dφ φ t) = sharp φ ≫ tvec t := by
  have := isLocalHom_stalkLift φ.left (left_pt_one φ) (tvec t)
  apply stalkLift_injective
  rw [tvec_spec, dφ_val, Over.comp_left, stalkLift_comp φ.left (left_pt_one φ) (tvec t),
    ← Category.assoc, tvec_spec]

theorem coeff_dφ (φ : A ⟶ A) [IsMonHom φ] (t : Tan A) (r : A.left.presheaf.stalk (pt A 1)) :
    coeff (dφ φ t) r = coeff t ((sharp φ).hom r) := by
  rw [coeff, coeff, tvec_dφ]; rfl

variable (A) in
/-- The structure map `k → 𝒪_{A,e}`. -/
noncomputable def kS : CommRingCat.of k ⟶ A.left.presheaf.stalk (pt A 1) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (A.hom (pt A 1)) trivial) ≫
    A.hom.stalkMap (pt A 1)

theorem fromSpecStalk_comp_hom : A.left.fromSpecStalk (pt A 1) ≫ A.hom = Spec.map (kS A) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, kS]
  simp only [Spec.map_comp, Category.assoc]

theorem kS_ev0 : kS A ≫ ev0 A = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, ← fromSpecStalk_comp_hom, ← Category.assoc, ev0_spec, Over.w, Spec.map_id]
  rfl

/-- The tangent vector with stalk map `h`. -/
noncomputable def tOf (h : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k))
    (hh : h ≫ fstC k = ev0 A) (hk : kS A ≫ h = CommRingCat.ofHom (algebraMap k (DualNumber k))) :
    Tan A :=
  ⟨Over.homMk (Spec.map h ≫ A.left.fromSpecStalk (pt A 1)) (by
      rw [Category.assoc, fromSpecStalk_comp_hom, ← Spec.map_comp, hk]; rfl),
    MonoidHom.mem_ker.2 (by
      apply Over.OverMorphism.ext
      show Spec.map (fstC k) ≫ Spec.map h ≫ _ = _
      rw [← Category.assoc, ← Spec.map_comp, hh, ev0_spec])⟩

theorem tvec_tOf (h : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k))
    [IsLocalHom h.hom] (hh : h ≫ fstC k = ev0 A)
    (hk : kS A ≫ h = CommRingCat.ofHom (algebraMap k (DualNumber k))) :
    tvec (tOf h hh hk) = h :=
  stalkLift_injective _ _ (tvec_spec _)

theorem coeff_tOf (h : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k))
    [IsLocalHom h.hom] (hh : h ≫ fstC k = ev0 A)
    (hk : kS A ≫ h = CommRingCat.ofHom (algebraMap k (DualNumber k))) (r) :
    coeff (tOf h hh hk) r = (h.hom r).snd := by
  rw [coeff, tvec_tOf]

theorem kS_sharp (φ : A ⟶ A) [IsMonHom φ] : kS A ≫ sharp φ = kS A := by
  apply Spec.map_injective
  rw [Spec.map_comp, ← fromSpecStalk_comp_hom, ← Category.assoc,
    stalkSpec_fromSpecStalk φ.left (left_pt_one φ), Category.assoc, Over.w]

end Tangent

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_IsogDegB_TanC =====
section

/-!
# S4-IsogDegB, the group law on tangent vectors is addition (L27 of S4_COREB_ROUTE.md §3)

With `D2 = Spec k[ε₁, ε₂]` (`k[ε₁, ε₂] = TrivSqZeroExt k (k × k)`), `u := (p₁ ≫ t) * (p₂ ≫ s)` restricts to
`t * s`, `t`, `s` along `δ, ι₁, ι₂ : Spec k[ε] → D2`; on stalks this reads `coeff (t * s) = coeff t + coeff s`.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Maps

variable (k : Type u) [Field k]

/-- `k[ε₁, ε₂]`. -/
abbrev K2 := TrivSqZeroExt k (k × k)

instance : IsLocalRing (K2 k) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
  rcases eq_or_ne x.fst 0 with h | h
  · right; rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]; simp [h]
  · left; rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]; exact h.isUnit

theorem tsze_eq_closedPoint {M : Type u} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] [IsLocalRing (TrivSqZeroExt k M)] (x : PrimeSpectrum (TrivSqZeroExt k M)) :
    x = closedPoint _ := by
  have hle : maximalIdeal (TrivSqZeroExt k M) ≤ x.asIdeal := fun y hy ↦ by
    have h0 : y.fst = 0 := by
      by_contra h
      exact (mem_maximalIdeal _).1 hy (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h))
    have hy' : y * y = 0 := by ext <;> simp [h0]
    rcases x.isPrime.mem_or_mem (show y * y ∈ x.asIdeal by rw [hy']; exact x.asIdeal.zero_mem)
      with h | h <;> exact h
  exact PrimeSpectrum.ext ((maximalIdeal.isMaximal _).eq_of_le x.isPrime.ne_top hle).symm

variable {M N L : Type u} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
  [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N]
  [AddCommGroup L] [Module k L] [Module kᵐᵒᵖ L] [IsCentralScalar k L]

/-- `TrivSqZeroExt.map f` in `CommRingCat`. -/
noncomputable abbrev mapC (f : M →ₗ[k] N) :
    CommRingCat.of (TrivSqZeroExt k M) ⟶ CommRingCat.of (TrivSqZeroExt k N) :=
  CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom

instance (f : M →ₗ[k] N) : IsLocalHom (mapC k f).hom :=
  ⟨fun x hx ↦ by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at hx ⊢
    simpa using hx⟩

/-- `Spec (TrivSqZeroExt k M)` over `k`. -/
noncomputable abbrev DM (M : Type u) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))))

/-- The morphism `Spec (k ⊕ N) → Spec (k ⊕ M)` of `f : M → N`. -/
noncomputable def homOfMap (f : M →ₗ[k] N) : DM k N ⟶ DM k M :=
  Over.homMk (Spec.map (mapC k f)) (by
    change Spec.map (mapC k f) ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x <;> simp)

theorem homOfMap_comp (f : M →ₗ[k] N) (g : L →ₗ[k] M) :
    homOfMap k f ≫ homOfMap k g = homOfMap k (f ∘ₗ g) := by
  apply Over.OverMorphism.ext
  change Spec.map (mapC k f) ≫ Spec.map (mapC k g) = Spec.map (mapC k (f ∘ₗ g))
  rw [← Spec.map_comp]
  congr 1
  ext x <;> simp

theorem homOfMap_id : homOfMap k (LinearMap.id : M →ₗ[k] M) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (mapC k LinearMap.id) = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  ext x <;> simp

theorem toUnit_left_DS : (toUnit (DS k)).left = (DS k).hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (DS k)))

theorem homOfMap_zero : homOfMap k (0 : k →ₗ[k] k) = toUnit (DS k) ≫ ι0 k := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, toUnit_left_DS]
  change Spec.map (mapC k 0) = Spec.map _ ≫ Spec.map (fstC k)
  rw [← Spec.map_comp]
  congr 1
  ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

end Maps

section GroupLaw

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

theorem tvec_of_comp (v : Tan A) {u : DM k (k × k) ⟶ A}
    (U : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (K2 k)) [IsLocalHom U.hom]
    (hU : Spec.map U ≫ A.left.fromSpecStalk (pt A 1) = u.left) (f : k × k →ₗ[k] k)
    (hv : homOfMap k f ≫ u = v.1) : tvec v = U ≫ mapC k f := by
  have : IsLocalHom (U ≫ mapC k f).hom := by rw [CommRingCat.hom_comp]; infer_instance
  apply stalkLift_injective
  rw [tvec_spec, ← hv, Over.comp_left, Spec.map_comp, Category.assoc, hU]
  rfl

/-- **Group law = addition** on tangent vectors. -/
theorem coeff_mul (t s : Tan A) (r : A.left.presheaf.stalk (pt A 1)) :
    coeff (t * s) r = coeff t r + coeff s r := by
  set u : DM k (k × k) ⟶ A :=
    (homOfMap k (LinearMap.inl k k k) ≫ t.1) * (homOfMap k (LinearMap.inr k k k) ≫ s.1)
  have hδ : homOfMap k (LinearMap.coprod LinearMap.id LinearMap.id) ≫ u = (t * s).1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homOfMap_comp, homOfMap_comp,
      LinearMap.coprod_inl, LinearMap.coprod_inr, homOfMap_id, Category.id_comp, Category.id_comp]
    rfl
  have h1 : homOfMap k (LinearMap.fst k k k) ≫ u = t.1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homOfMap_comp, homOfMap_comp,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, homOfMap_id, homOfMap_zero, Category.id_comp,
      Category.assoc, tan_spec, MonObj.comp_one, _root_.mul_one]
  have h2 : homOfMap k (LinearMap.snd k k k) ≫ u = s.1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homOfMap_comp, homOfMap_comp,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, homOfMap_id, homOfMap_zero, Category.id_comp,
      Category.assoc, tan_spec, MonObj.comp_one, _root_.one_mul]
  have hpt : u.left (closedPoint (K2 k)) = pt A 1 := by
    have e1 : (homOfMap k (LinearMap.coprod LinearMap.id LinearMap.id)).left
        (closedPoint (DualNumber k)) = closedPoint (K2 k) := tsze_eq_closedPoint k _
    have e2 : (t * s).1.left (closedPoint (DualNumber k)) = pt A 1 :=
      left_closedPoint A _ (tan_spec (t * s))
    rw [← hδ] at e2
    calc u.left (closedPoint (K2 k))
        = u.left ((homOfMap k (LinearMap.coprod LinearMap.id LinearMap.id)).left
          (closedPoint (DualNumber k))) := by rw [e1]
      _ = pt A 1 := e2
  obtain ⟨U, hUl, hU⟩ := exists_stalkLift (R := CommRingCat.of (K2 k)) u.left hpt
  rw [coeff, coeff, coeff, tvec_of_comp (t * s) U hU _ hδ, tvec_of_comp t U hU _ h1,
    tvec_of_comp s U hU _ h2]
  simp

theorem coeff_one (r : A.left.presheaf.stalk (pt A 1)) : coeff (1 : Tan A) r = 0 := by
  have h := coeff_mul (1 : Tan A) 1 r
  rw [_root_.mul_one] at h
  calc coeff (1 : Tan A) r = coeff (1 : Tan A) r + coeff (1 : Tan A) r - coeff (1 : Tan A) r := by ring
    _ = 0 := by rw [← h, sub_self]

/-- `coeff` as a homomorphism to the additive group of functions. -/
noncomputable def coeffHom : Tan A →* Multiplicative (A.left.presheaf.stalk (pt A 1) → k) where
  toFun t := Multiplicative.ofAdd (coeff t)
  map_one' := by
    ext r
    exact coeff_one r
  map_mul' t s := by
    ext r
    exact coeff_mul t s r

theorem coeff_zpow (t : Tan A) (n : ℤ) (r : A.left.presheaf.stalk (pt A 1)) :
    coeff (t ^ n) r = n * coeff t r := by
  have := congrArg (fun f : Multiplicative (A.left.presheaf.stalk (pt A 1) → k) ↦ Multiplicative.toAdd f r) (map_zpow (coeffHom (A := A)) t n)
  simpa [coeffHom, toAdd_zpow, zsmul_eq_mul] using this

theorem tan_eq_one_iff (t : Tan A) : t = 1 ↔ ∀ r, coeff t r = 0 :=
  ⟨fun h r ↦ h ▸ coeff_one r, fun h ↦ tan_ext fun r ↦ (h r).trans (coeff_one r).symm⟩

end GroupLaw

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_IsogDegB_DerT =====
section

/-!
# S4-IsogDegB, tangent vectors over a `k`-tower (L27 of S4_COREB_ROUTE.md §3)

With `k → S → R` and `k`-points on `S` and `R`: the tangent vector of `exists_tangent_of_not_le` kills all of `S`,
and the residue hypotheses of `Unram.formallyUnramified_of_le` hold.
-/

set_option autoImplicit false

namespace RamanujanPetersson.IsogDegB

open IsLocalRing

section Points

variable {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]

theorem mem_of_ev_eq_zero (ev : R →ₐ[k] k) (r : R) (hr : ev r = 0) : r ∈ maximalIdeal R :=
  (mem_maximalIdeal _).2 fun hu ↦ (hu.map ev).ne_zero hr

theorem sub_algebraMap_mem (ev : R →ₐ[k] k) (r : R) : r - algebraMap k R (ev r) ∈ maximalIdeal R :=
  mem_of_ev_eq_zero ev _ (by simp)

end Points

section Tower

variable {k S R : Type*} [Field k] [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
  [Algebra S R] [IsLocalHom (algebraMap S R)] [Algebra k R] [Algebra k S] [IsScalarTower k S R]

omit [IsLocalRing S] [IsLocalHom (algebraMap S R)] in
theorem exists_res (ev : R →ₐ[k] k) (r : R) : ∃ s : S, r - algebraMap S R s ∈ maximalIdeal R :=
  ⟨algebraMap k S (ev r), by rw [← IsScalarTower.algebraMap_apply]; exact sub_algebraMap_mem ev r⟩

/-- **Alg-1 over a tower.** A non-surjective cotangent map gives a nonzero tangent vector of `R`
killed by all of `S`. -/
theorem exists_tangent_of_not_le' (ev : R →ₐ[k] k) (evS : S →ₐ[k] k)
    (hJ : ¬ maximalIdeal R ≤ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    ∃ h : R →ₐ[k] DualNumber k, (∀ r, (h r).fst = ev r) ∧
      (∀ s, (h (algebraMap S R s)).snd = 0) ∧ ∃ r, (h r).snd ≠ 0 := by
  obtain ⟨h, h1, h2, h3⟩ := exists_tangent_of_not_le (S := S) ev (mem_of_ev_eq_zero ev) hJ
  refine ⟨h, h1, fun s ↦ ?_, h3⟩
  have e : algebraMap S R s =
      algebraMap S R (s - algebraMap k S (evS s)) + algebraMap k R (evS s) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, sub_add_cancel]
  rw [e, map_add, TrivSqZeroExt.snd_add, h2 _ (sub_algebraMap_mem evS s), h.commutes]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end Tower

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_IsogDegB_Sep =====
section

/-!
# S4-IsogDegB, file Sep: an injective differential makes `φ` unramified at the identity

Sep-3: if `dφ` is injective on the tangent space at `e`, the cotangent map of the stalk map
`φ♯ : 𝒪_{A,φ e} → 𝒪_{A,e}` is surjective (`𝔪_e = φ♯ 𝔪 + 𝔪_e²`). Otherwise `DerT` gives a nonzero
tangent vector killed by `φ♯`, i.e. a nontrivial element of the kernel of `dφ`.
Sep-4 (first half): then `φ♯` is formally unramified (`Unram`), hence quasi-finite, so `φ` is
quasi-finite at `e` and locally quasi-finite (`IsogDegA.locallyQuasiFinite_of_quasiFiniteAt`).
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Sep

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

/-- `ρ : 𝒪_{A,e} → 𝒪_{A,φ e}` along `φ e = e`. -/
noncomputable abbrev rho (φ : A ⟶ A) [IsMonHom φ] :
    A.left.presheaf.stalk (pt A 1) ⟶ A.left.presheaf.stalk (φ.left (pt A 1)) :=
  A.left.presheaf.stalkSpecializes (specializes_of_eq (left_pt_one φ))

theorem kS_rho_stalkMap (φ : A ⟶ A) [IsMonHom φ] :
    kS A ≫ rho φ ≫ φ.left.stalkMap (pt A 1) = kS A := kS_sharp φ

/-- Residues of `φ♯` exhaust the residue field (constants lift). -/
theorem exists_res_stalk (φ : A ⟶ A) [IsMonHom φ] (r : A.left.presheaf.stalk (pt A 1)) :
    ∃ s, r - (φ.left.stalkMap (pt A 1)).hom s ∈ maximalIdeal (A.left.presheaf.stalk (pt A 1)) := by
  refine ⟨(kS A ≫ rho φ).hom ((ev0 A).hom r), ?_⟩
  have e : (φ.left.stalkMap (pt A 1)).hom ((kS A ≫ rho φ).hom ((ev0 A).hom r)) =
      (kS A).hom ((ev0 A).hom r) := by
    show (kS A ≫ rho φ ≫ φ.left.stalkMap (pt A 1)).hom ((ev0 A).hom r) = _
    rw [kS_rho_stalkMap]
  rw [e, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 : (ev0 A).hom ((kS A).hom ((ev0 A).hom r)) = (ev0 A).hom r := by
    show (kS A ≫ ev0 A).hom _ = _
    rw [kS_ev0]; rfl
  have h0 : (ev0 A).hom (r - (kS A).hom ((ev0 A).hom r)) = 0 := by
    rw [map_sub, h1, sub_self]
  exact not_isUnit_zero (h0 ▸ hu.map (ev0 A).hom)

/-- **Sep-3.** An injective differential makes the cotangent map at `e` surjective. -/
theorem cotangent_le_of_injective (φ : A ⟶ A) [IsMonHom φ] (hinj : Function.Injective (dφ φ)) :
    maximalIdeal (A.left.presheaf.stalk (pt A 1)) ≤
      Ideal.map (φ.left.stalkMap (pt A 1)).hom
          (maximalIdeal (A.left.presheaf.stalk (φ.left (pt A 1)))) ⊔
        maximalIdeal (A.left.presheaf.stalk (pt A 1)) ^ 2 := by
  let : Algebra k (A.left.presheaf.stalk (pt A 1)) := (kS A).hom.toAlgebra
  let : Algebra k (A.left.presheaf.stalk (φ.left (pt A 1))) := (kS A ≫ rho φ).hom.toAlgebra
  let : Algebra (A.left.presheaf.stalk (φ.left (pt A 1))) (A.left.presheaf.stalk (pt A 1)) :=
    (φ.left.stalkMap (pt A 1)).hom.toAlgebra
  have : IsLocalHom (algebraMap (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1))) :=
    inferInstanceAs (IsLocalHom (φ.left.stalkMap (pt A 1)).hom)
  have : IsScalarTower k (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      show (kS A).hom c = (kS A ≫ rho φ ≫ φ.left.stalkMap (pt A 1)).hom c
      rw [kS_rho_stalkMap]
  let ev : A.left.presheaf.stalk (pt A 1) →ₐ[k] k :=
    { toRingHom := (ev0 A).hom
      commutes' := fun c ↦ by
        show (kS A ≫ ev0 A).hom c = c
        rw [kS_ev0]; rfl }
  let evS : A.left.presheaf.stalk (φ.left (pt A 1)) →ₐ[k] k :=
    { toRingHom := (φ.left.stalkMap (pt A 1) ≫ ev0 A).hom
      commutes' := fun c ↦ by
        show ((kS A ≫ rho φ ≫ φ.left.stalkMap (pt A 1)) ≫ ev0 A).hom c = c
        rw [kS_rho_stalkMap, kS_ev0]; rfl }
  by_contra hJ
  obtain ⟨h, h1, h2, r, hr⟩ := exists_tangent_of_not_le' ev evS hJ
  have hloc : IsLocalHom (CommRingCat.ofHom h.toRingHom).hom := ⟨fun x hx ↦ by
    have hx' : IsUnit ((ev0 A).hom x) := by
      have := TrivSqZeroExt.isUnit_iff_isUnit_fst.1 hx
      exact (h1 x) ▸ this
    exact isUnit_of_map_unit (ev0 A).hom x hx'⟩
  have hh : CommRingCat.ofHom h.toRingHom ≫ fstC k = ev0 A := by
    ext x; exact h1 x
  have hk : kS A ≫ CommRingCat.ofHom h.toRingHom =
      CommRingCat.ofHom (algebraMap k (DualNumber k)) := by
    exact CommRingCat.hom_ext (RingHom.ext fun c ↦ h.commutes c)
  have ht : tOf (CommRingCat.ofHom h.toRingHom) hh hk ≠ 1 := by
    intro h0
    have := coeff_tOf (CommRingCat.ofHom h.toRingHom) hh hk r
    rw [h0, coeff_one] at this
    exact hr this.symm
  refine ht (hinj ?_)
  rw [map_one, tan_eq_one_iff]
  intro r'
  rw [coeff_dφ]
  exact (coeff_tOf (CommRingCat.ofHom h.toRingHom) hh hk _).trans (h2 ((rho φ).hom r'))

/-- **Sep-4a.** An injective differential makes `φ` quasi-finite at the identity. -/
theorem quasiFiniteAt_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    (hinj : Function.Injective (dφ φ)) : φ.left.QuasiFiniteAt (pt A 1) := by
  let : Algebra (A.left.presheaf.stalk (φ.left (pt A 1))) (A.left.presheaf.stalk (pt A 1)) :=
    (φ.left.stalkMap (pt A 1)).hom.toAlgebra
  have : IsLocalHom (algebraMap (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1))) :=
    inferInstanceAs (IsLocalHom (φ.left.stalkMap (pt A 1)).hom)
  have : Algebra.EssFiniteType (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) := LocallyOfFiniteType.stalkMap φ.left (pt A 1)
  have : Algebra.FormallyUnramified (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) :=
    formallyUnramified_of_le (fun r ↦ exists_res_stalk φ r) (cotangent_le_of_injective φ hinj)
  exact (RingHom.quasiFinite_algebraMap (R := A.left.presheaf.stalk (φ.left (pt A 1)))
    (S := A.left.presheaf.stalk (pt A 1))).2 inferInstance

/-- An injective differential makes `φ` locally quasi-finite. -/
theorem locallyQuasiFinite_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    (hinj : Function.Injective (dφ φ)) : LocallyQuasiFinite φ.left :=
  locallyQuasiFinite_of_quasiFiniteAt A φ (pt A 1) (quasiFiniteAt_of_injective φ hinj)

end Sep

end RamanujanPetersson.IsogDegB

end

-- ===== S4.Def_RP_JacSymB_Coord =====
section

/-!
# S4-JacSymB, file D: a coordinate that is étale at finitely many points

For a Dedekind domain `B` over an infinite field `k` and finitely many `k`-points `T`, there is `x ∈ B` with
`k[x] + ⋂_{φ ∈ T} (ker φ)^n = B` for every `n` (`x - φ(x)` is a uniformiser at each point, the `φ(x)` distinct).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacSym

section Coord

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra k B]

omit [IsDedekindDomain B] in
theorem sub_algebraMap_mem_ker (φ : B →ₐ[k] k) (r : B) : r - algebraMap k B (φ r) ∈ RingHom.ker φ := by
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

omit [Algebra k B] in
/-- At a uniformiser `y ∈ P \ P^2` of a maximal ideal of a Dedekind domain: `P = (y) + P^2`. -/
theorem eq_span_sup_sq {P : Ideal B} [hPm : P.IsMaximal] {y : B} (hy : y ∈ P) (hx : y ∉ P ^ 2) :
    P = Ideal.span {y} ⊔ P ^ 2 := by
  have hP : P ≠ ⊥ := by
    rintro rfl
    exact hx (by rw [Ideal.mem_bot.1 hy]; exact zero_mem _)
  have hpr : Prime P := Ideal.prime_of_isPrime hP hPm.isPrime
  have hIP : Ideal.span {y} ⊔ P ^ 2 ≤ P :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hy) (Ideal.pow_le_self (by norm_num))
  have hdvd : Ideal.span {y} ⊔ P ^ 2 ∣ P ^ 2 := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hpr 2).1 hdvd
  rw [associated_iff_eq] at hassoc
  interval_cases i
  · rw [hassoc, pow_zero, Ideal.one_eq_top, top_le_iff] at hIP
    exact absurd hIP hPm.ne_top
  · rw [pow_one] at hassoc; exact hassoc.symm
  · exact absurd (hassoc ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self y)) hx

omit [IsDedekindDomain B] [Algebra k B] in
theorem pow_le_span_sup {P : Ideal B} {y : B} (hy : y ∈ P) (hPy : P = Ideal.span {y} ⊔ P ^ 2) (m : ℕ) :
    P ^ m ≤ Ideal.span {y ^ m} ⊔ P ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hym : Ideal.span {y ^ m} ≤ P ^ m := (Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hy m)
    have hy1 : Ideal.span {y} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 hy
    calc P ^ (m + 1) = P ^ m * P := pow_succ P m
      _ ≤ (Ideal.span {y ^ m} ⊔ P ^ (m + 1)) * (Ideal.span {y} ⊔ P ^ 2) := Ideal.mul_mono ih hPy.le
      _ ≤ Ideal.span {y ^ (m + 1)} ⊔ P ^ (m + 1 + 1) := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
        refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
        · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]; exact le_sup_left
        · refine le_sup_of_le_right ?_
          calc Ideal.span {y ^ m} * P ^ 2 ≤ P ^ m * P ^ 2 := Ideal.mul_mono_left hym
            _ = P ^ (m + 1 + 1) := by rw [← pow_add]
        · refine le_sup_of_le_right ?_
          calc P ^ (m + 1) * Ideal.span {y} ≤ P ^ (m + 1) * P := Ideal.mul_mono_right hy1
            _ = P ^ (m + 1 + 1) := (pow_succ P (m + 1)).symm
        · refine le_sup_of_le_right ?_
          rw [← pow_add]
          exact Ideal.pow_le_pow_right (by omega)

/-- One point: `k[x] + P^m = B` when `x - φ x` is a uniformiser at `P = ker φ`. -/
theorem exists_poly_single (φ : B →ₐ[k] k) (x : B) (hx : x - algebraMap k B (φ x) ∉ RingHom.ker φ ^ 2)
    (m : ℕ) (b : B) : ∃ p : k[X], b - aeval x p ∈ RingHom.ker φ ^ m := by
  have : (RingHom.ker φ).IsMaximal := ker_isMaximal φ
  have hy := sub_algebraMap_mem_ker φ x
  have hPy := eq_span_sup_sq hy hx
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (pow_le_span_sup hy hPy m hp)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    refine ⟨p + C (φ r) * (X - C (φ x)) ^ m, ?_⟩
    have he : b - aeval x (p + C (φ r) * (X - C (φ x)) ^ m) =
        (r - algebraMap k B (φ r)) * (x - algebraMap k B (φ x)) ^ m + v := by
      simp only [map_add, map_mul, aeval_C, map_pow, map_sub, aeval_X]
      linear_combination (-1 : B) * huv
    rw [he]
    refine add_mem ?_ hv
    rw [pow_succ']
    exact Ideal.mul_mem_mul (sub_algebraMap_mem_ker φ r) (Ideal.pow_mem_pow hy m)

/-- Finitely many points: one `x` with `k[x] + P^n = B` at every point of `T`, for every `n`. -/
theorem exists_coord [Infinite k] (hB : ¬ IsField B) (T : Finset (B →ₐ[k] k)) :
    ∃ x : B, ∀ n : ℕ, ∀ b : B, ∃ p : k[X], ∀ φ ∈ T, b - aeval x p ∈ RingHom.ker φ ^ n := by
  classical
  let c : (B →ₐ[k] k) → k := fun φ =>
    if h : φ ∈ T then Infinite.natEmbedding k (T.equivFin ⟨φ, h⟩ : ℕ) else 0
  have hc : ∀ φ ∈ T, ∀ ψ ∈ T, c φ = c ψ → φ = ψ := by
    intro φ hφ ψ hψ h
    simp only [c, dif_pos hφ, dif_pos hψ] at h
    have h1 := T.equivFin.injective (Fin.ext ((Infinite.natEmbedding k).injective h))
    exact congrArg Subtype.val h1
  have hπ : ∀ φ : B →ₐ[k] k, ∃ π ∈ RingHom.ker φ, π ∉ RingHom.ker φ ^ 2 := by
    intro φ
    have hm := ker_isMaximal φ
    have hP : RingHom.ker φ ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm hB
    have hlt : RingHom.ker φ ^ 2 < RingHom.ker φ ^ 1 :=
      Ideal.pow_right_strictAnti _ hP hm.ne_top (by norm_num)
    rw [pow_one] at hlt
    obtain ⟨π, h1, h2⟩ := SetLike.exists_of_lt hlt
    exact ⟨π, h1, h2⟩
  choose π hπP hπ2 using hπ
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun φ => RingHom.ker φ) (fun _ => 2)
    (fun φ _ => Ideal.prime_of_isPrime (Ring.ne_bot_of_isMaximal_of_not_isField (ker_isMaximal φ) hB)
      (ker_isMaximal φ).isPrime)
    (fun φ _ ψ _ hne h => hne (algHom_eq_of_ker_eq h))
    (fun φ => algebraMap k B (c φ.1) + π φ.1)
  have hx' : ∀ φ ∈ T, x - (algebraMap k B (c φ) + π φ) ∈ RingHom.ker φ ^ 2 := fun φ hφ => hx φ hφ
  have hxφ : ∀ φ ∈ T, φ x = c φ := by
    intro φ hφ
    have h' : x - (algebraMap k B (c φ) + π φ) ∈ RingHom.ker φ := Ideal.pow_le_self (by norm_num) (hx' φ hφ)
    rw [RingHom.mem_ker, map_sub, map_add, AlgHom.commutes, (RingHom.mem_ker).1 (hπP φ)] at h'
    simpa [sub_eq_zero] using h'
  have hunif : ∀ φ ∈ T, x - algebraMap k B (φ x) ∉ RingHom.ker φ ^ 2 := by
    intro φ hφ hmem
    apply hπ2 φ
    have h1 := sub_mem hmem (hx' φ hφ)
    rw [hxφ φ hφ] at h1
    convert h1 using 1
    ring
  refine ⟨x, fun n b => ?_⟩
  choose p hp using fun φ : T => exists_poly_single φ.1 x (hunif φ.1 φ.2) n b
  have hcop : Pairwise (Function.onFun IsCoprime fun φ : T => Ideal.span {((X : k[X]) - C (c φ.1)) ^ n}) := by
    intro φ ψ hne
    rw [Function.onFun, Ideal.isCoprime_span_singleton_iff]
    apply IsCoprime.pow
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    intro h
    exact hne (Subtype.ext (hc _ φ.2 _ ψ.2 h))
  obtain ⟨q, hq⟩ := Ideal.exists_forall_sub_mem_ideal hcop p
  refine ⟨q, fun φ hφ => ?_⟩
  have h1 := hp ⟨φ, hφ⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hq ⟨φ, hφ⟩)
  have h2 : aeval x q - aeval x (p ⟨φ, hφ⟩) ∈ RingHom.ker φ ^ n := by
    rw [← map_sub, ← hr, map_mul, map_pow, map_sub, aeval_X, aeval_C, ← hxφ φ hφ]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (sub_algebraMap_mem_ker φ x) n)
  have h3 := sub_mem h1 h2
  convert h3 using 1
  ring

omit [IsDedekindDomain B] in
/-- `⋂ P^n ≤ (⋂ P)^n` for finitely many distinct `k`-points. -/
theorem iInf_pow_le_pow_iInf (T : Finset (B →ₐ[k] k)) (n : ℕ) :
    (⨅ φ ∈ T, RingHom.ker φ ^ n) ≤ (⨅ φ ∈ T, RingHom.ker φ) ^ n := by
  classical
  have hcop : (T : Set (B →ₐ[k] k)).Pairwise (Function.onFun IsCoprime fun φ => RingHom.ker φ ^ n) := by
    intro φ _ ψ _ hne
    have := ker_isMaximal φ
    have := ker_isMaximal ψ
    exact (Ideal.isCoprime_of_isMaximal (fun h => hne (algHom_eq_of_ker_eq h))).pow
  rw [← Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop, Finset.prod_pow, ← Finset.inf_eq_iInf]
  exact Ideal.pow_right_mono Ideal.prod_le_inf n

end Coord

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_DegPoly_Cube =====
section

/-!
# Degree polynomiality, part 3: the quadratic relation from the cube relation (unit S4-DegPoly)

The input `hquad` of `deg_poly_of_quad` in the form the theorem of the cube gives it (Milne, Abelian Varieties,
Cor. 5.4 and the proof of Lemma 10.12): if `Q : R → N` on an abelian group satisfies `Q 0 = 0`, the cube relation
`Q (a+b+e) - Q (a+b) - Q (a+e) - Q (b+e) + Q a + Q b + Q e = 0` and `Q (-a) = Q a` (`D` symmetric), then
`Q (n • a + b) = n² • Q a + n • B a b + Q b` with `B a b = Q (a + b) - Q a - Q b`. `quad_of_cube` states it for
`c : R → M` up to numerical equivalence (`numKer I`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.DegPoly

section Quad

variable {R N : Type*} [AddCommGroup R] [AddCommGroup N]

/-- The polarisation `B a b = Q (a + b) - Q a - Q b` of `Q`. -/
def polar (Q : R → N) (a b : R) : N := Q (a + b) - Q a - Q b

variable {Q : R → N}

theorem polar_comm (a b : R) : polar Q a b = polar Q b a := by
  simp only [polar, add_comm a b]
  abel

theorem polar_add_left
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (a e b : R) : polar Q (a + e) b = polar Q a b + polar Q e b := by
  unfold polar
  rw [← sub_eq_zero]
  convert hcube a e b using 1
  abel

/-- `a ↦ B a b` as an additive map. -/
def polarHom (hQ0 : Q 0 = 0)
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (b : R) : R →+ N where
  toFun a := polar Q a b
  map_zero' := by simp [polar, hQ0]
  map_add' a e := polar_add_left hcube a e b

theorem polar_self (hQ0 : Q 0 = 0)
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (hsym : ∀ a, Q (-a) = Q a) (a : R) : polar Q a a = (2 : ℤ) • Q a := by
  have h1 : polar Q (-a) a = -polar Q a a := (polarHom hQ0 hcube a).map_neg a
  have h2 : polar Q (-a) a = Q 0 - Q (-a) - Q a := by simp only [polar, neg_add_cancel]
  rw [hQ0, hsym] at h2
  have h3 : polar Q a a = -(0 - Q a - Q a) := by rw [← h2, h1, neg_neg]
  rw [h3, two_smul]
  abel

theorem quad_step (hQ0 : Q 0 = 0)
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (hsym : ∀ a, Q (-a) = Q a) (m : ℤ) (a b : R) :
    Q ((m + 1) • a + b) = Q (m • a + b) + (2 * m + 1) • Q a + polar Q a b := by
  have hx : (m + 1) • a + b = (m • a + b) + a := by rw [add_smul, one_smul]; abel
  have hp : Q ((m • a + b) + a) = Q (m • a + b) + Q a + polar Q (m • a + b) a := by
    simp only [polar]
    abel
  have hz : polar Q (m • a) a = m • polar Q a a := map_zsmul (polarHom hQ0 hcube a) m a
  rw [hx, hp, polar_add_left hcube, hz, polar_self hQ0 hcube hsym, polar_comm b a, smul_smul,
    add_smul, one_smul, mul_comm m 2]
  abel

/-- **The quadratic relation** from the cube relation and symmetry. -/
theorem quad_of_cube_fun (hQ0 : Q 0 = 0)
    (hcube : ∀ a b e : R, Q (a + b + e) - Q (a + b) - Q (a + e) - Q (b + e) + Q a + Q b + Q e = 0)
    (hsym : ∀ a, Q (-a) = Q a) (n : ℤ) (a b : R) :
    Q (n • a + b) = n ^ 2 • Q a + n • polar Q a b + Q b := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    rw [quad_step hQ0 hcube hsym, ih]
    simp only [add_sq, add_smul, mul_smul, one_pow, mul_one, one_smul]
    abel
  | pred i ih =>
    have hs := quad_step hQ0 hcube hsym (-(i : ℤ) - 1) a b
    rw [sub_add_cancel, ih] at hs
    have h : Q ((-(i : ℤ) - 1) • a + b) = ((-(i : ℤ)) ^ 2 • Q a + (-(i : ℤ)) • polar Q a b + Q b) -
        (2 * (-(i : ℤ) - 1) + 1) • Q a - polar Q a b := by
      rw [hs]
      abel
    rw [h]
    simp only [sub_sq, neg_sq, add_smul, sub_smul, mul_smul, one_pow, mul_one, one_smul, neg_smul, two_smul]
    abel

end Quad

variable {M : Type*} [AddCommGroup M] {g : ℕ}

/-- **Input for `deg_poly_of_quad`** from the cube relation, `0^* D ≡ 0` and `[-1]^* D ≡ D`, all up to numerical
equivalence. -/
theorem quad_of_cube (I : MultilinearMap ℤ (fun _ : Fin g => M) ℤ) {R : Type*} [Ring R] (c : R → M)
    (hzero : c 0 ∈ numKer I) (hsym : ∀ a, c (-a) - c a ∈ numKer I)
    (hcube : ∀ a b e : R,
      c (a + b + e) - c (a + b) - c (a + e) - c (b + e) + c a + c b + c e ∈ numKer I)
    (a b : R) : ∃ e : M, ∀ n : ℤ, c (n * a + b) - (n ^ 2 • c a + n • e + c b) ∈ numKer I := by
  refine ⟨c (a + b) - c a - c b, fun n => ?_⟩
  have hQ0 : ((c 0 : M) : M ⧸ numKer I) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hzero
  have hQs : ∀ x : R, ((c (-x) : M) : M ⧸ numKer I) = ((c x : M) : M ⧸ numKer I) :=
    fun x => QuotientAddGroup.eq_iff_sub_mem.mpr (hsym x)
  have hQc : ∀ x y z : R, ((c (x + y + z) : M) : M ⧸ numKer I) - (c (x + y) : M ⧸ numKer I) -
      (c (x + z) : M ⧸ numKer I) - (c (y + z) : M ⧸ numKer I) + (c x : M ⧸ numKer I) +
      (c y : M ⧸ numKer I) + (c z : M ⧸ numKer I) = 0 := by
    intro x y z
    have h := (QuotientAddGroup.eq_zero_iff _).mpr (hcube x y z)
    simpa only [QuotientAddGroup.mk_add, QuotientAddGroup.mk_sub] using h
  have hmain := quad_of_cube_fun (Q := fun x => ((c x : M) : M ⧸ numKer I)) hQ0 hQc hQs n a b
  simp only [polar] at hmain
  rw [← QuotientAddGroup.eq_zero_iff, ← zsmul_eq_mul]
  simp only [QuotientAddGroup.mk_add, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_zsmul]
  rw [hmain, sub_self]

end RamanujanPetersson.DegPoly

end


