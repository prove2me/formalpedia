-- Prove2me | Definitions.Def_RPLib_S4_CDPack48
-- name    : RPLib_S4_CDPack48
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:41:19.090533+00:00
-- url     : https://prove2.me/theorems/ac6059be-89ea-422a-9153-50efb05400c0
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 48 of 71
-- statement:
--   Part 48 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacDivisors_S`: S4-JacDivisors S (O10, scheme part, and the smooth form of Weil's extension theorem)
--   * `Def_RP_IntersectB_Prime`: S4-IntersectB, file Prime: prime divisors as locally principal ideal sheaves (O6)
--   * `Def_RP_IntersectB_Form`: S4-IntersectB, file Form: intersection numbers of prime-divisor products (O7, part 1)
--   * `Def_RP_IntersectB_Form2`: S4-IntersectB, file Form2: the intersection form on all divisors (O7, part 2; L33)
--   * `Def_RP_IntersectB_Pen3`: S4-IntersectB, O9 part 3: the Weil bridge for the pencil of a rational function
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack46
import Definitions.Def_RPLib_S4_CDPack26
import Definitions.Def_RPLib_S4_CDPack47
import Definitions.Def_RPLib_S4_CDPack38

/-!
# Curve-duality library package, part 48 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacDivisors_S`: S4-JacDivisors S (O10, scheme part, and the smooth form of Weil's extension theorem)
* `Def_RP_IntersectB_Prime`: S4-IntersectB, file Prime: prime divisors as locally principal ideal sheaves (O6)
* `Def_RP_IntersectB_Form`: S4-IntersectB, file Form: intersection numbers of prime-divisor products (O7, part 1)
* `Def_RP_IntersectB_Form2`: S4-IntersectB, file Form2: the intersection form on all divisors (O7, part 2; L33)
* `Def_RP_IntersectB_Pen3`: S4-IntersectB, O9 part 3: the Weil bridge for the pencil of a rational function
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacDivisors_S =====
section

/-!
# S4-JacDivisors S (O10, scheme part, and the smooth form of Weil's extension theorem)
* `isRegularLocalRing_stalk_of_smooth`: the local rings of a smooth `k`-scheme are regular
  (standard smooth charts are étale over a polynomial ring, file R).
* `uniqueFactorizationMonoid_stalk_of_smooth`: they are factorial (file G, Auslander-Buchsbaum).
* `domain_eq_top_of_smooth`, `domain_eq_top_of_smooth_of_isProper` (Milne I.3.2): for `k`
  algebraically closed, `V` smooth over `k` with `V` and `V ×_k V` integral, every rational map
  from `V` to a separated group `G` over `k` (locally of finite type, valuative existence, e.g.
  proper) is defined everywhere.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj CartesianMonoidalCategory

universe u

/-- The stalks of `X` at points of an affine open with regular ring of sections are regular. -/
theorem isRegularLocalRing_stalk_of_isAffineOpen {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    [IsRegularRing Γ(X, V)] (y : V) : IsRegularLocalRing (X.presheaf.stalk y) := by
  have := hV.isLocalization_stalk y
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv
    (hV.primeIdealOf y).asIdeal.primeCompl (Localization.AtPrime (hV.primeIdealOf y).asIdeal)
    (X.presheaf.stalk y)).toRingEquiv

/-- The local rings of a smooth scheme over a field are regular local rings. -/
theorem isRegularLocalRing_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hxV, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, g, -, het⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hs
  have hUtop : U = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have hfx : f x ∈ U := e hxV
    rwa [Subsingleton.elim y (f x)]
  subst hUtop
  have : IsRegularRing Γ(Spec (.of k), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
  let := g.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) Γ(Spec (.of k), ⊤)) Γ(X, V) := het
  have : IsRegularRing Γ(X, V) :=
    isRegularRing_of_etale (A := MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))
  exact isRegularLocalRing_stalk_of_isAffineOpen hV ⟨x, hxV⟩

/-- The local rings of a smooth scheme over a field are factorial. -/
theorem uniqueFactorizationMonoid_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  haveI := isRegularLocalRing_stalk_of_smooth f x
  uniqueFactorizationMonoid_of_isRegularLocalRing _

section
variable {k : Type u} [Field k] {V G : Over (Spec (.of k))}

instance smooth_tensor_hom [Smooth V.hom] : Smooth (V ⊗ V).hom :=
  show Smooth (pullback.fst V.hom V.hom ≫ V.hom) from inferInstance

variable [GrpObj G]

/-- **Weil's extension theorem** (Milne I.3.2), smooth form: a rational map from a smooth
`k`-variety `V` (with `V ×_k V` integral) to a separated group `G` satisfying valuative
existence is defined everywhere. -/
theorem domain_eq_top_of_smooth [IsAlgClosed k] [Smooth V.hom] [LocallyOfFiniteType G.hom]
    [IsSeparated G.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (hY : ValuativeCriterion.Existence G.hom)
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    f.toRationalMap.domain = ⊤ := by
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : IsLocallyNoetherian (V ⊗ V).left := LocallyOfFiniteType.isLocallyNoetherian (V ⊗ V).hom
  have : ∀ v : V.left, UniqueFactorizationMonoid (V.left.presheaf.stalk v) :=
    uniqueFactorizationMonoid_stalk_of_smooth V.hom
  have : ∀ p : (V ⊗ V).left, UniqueFactorizationMonoid ((V ⊗ V).left.presheaf.stalk p) :=
    uniqueFactorizationMonoid_stalk_of_smooth (V ⊗ V).hom
  exact domain_eq_top hY f hf

/-- **Weil's extension theorem** (Milne I.3.2) for a proper group `G` and smooth `V`. -/
theorem domain_eq_top_of_smooth_of_isProper [IsAlgClosed k] [Smooth V.hom] [IsProper G.hom]
    [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    f.toRationalMap.domain = ⊤ := by
  have h : UniversallyClosed G.hom := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact domain_eq_top_of_smooth h.1 f hf

end

end RamanujanPetersson.JacDivisors

end

-- ===== S4.Def_RP_IntersectB_Prime =====
section

/-!
# S4-IntersectB, file Prime: prime divisors as locally principal ideal sheaves (O6)

* `primeI z`: the vanishing ideal sheaf of `closure {z}`; `coe_support_primeI`.
* `ideal_primeI_fromSpec`, `ideal_primeI_of_notMem`: on an affine chart `V` the ideal is the prime
  `y` with `z = fromSpec y`, and `⊤` when `z ∉ V`.
* `support_primeI_ne_top`: the support is a proper closed set when `z` has codimension one.
* `isLocPrin_primeI`: on an integral locally Noetherian scheme with factorial stalks, a
  codimension-one point gives a locally principal ideal sheaf; `isLocPrin_primeI_of_smooth`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology Order

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.JacDivisors

variable {X : Scheme.{u}}

/-- The ideal sheaf of the closure of a point (a prime divisor when `z` has codimension one). -/
noncomputable def primeI (z : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {z}, isClosed_closure⟩

lemma coe_support_primeI (z : X) : ((primeI z).support : Set X) = closure {z} := by
  simp [primeI]

lemma ideal_primeI (z : X) (V : X.affineOpens) :
    (primeI z).ideal V = PrimeSpectrum.vanishingIdeal (V.2.fromSpec ⁻¹' closure {z}) := by
  rw [primeI, Scheme.IdealSheafData.vanishingIdeal_ideal]
  rfl

lemma ideal_primeI_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (y : Spec Γ(X, V)) :
    (primeI (hV.fromSpec y)).ideal ⟨V, hV⟩ = y.asIdeal := by
  ext r
  rw [ideal_primeI, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h
    exact h y (subset_closure (Set.mem_singleton _))
  · intro hr x hx
    have hx' : hV.fromSpec y ⤳ hV.fromSpec x := specializes_iff_mem_closure.mpr hx
    exact (fromSpec_specializes_iff hV y x).mp hx' hr

lemma ideal_primeI_of_notMem {z : X} (V : X.affineOpens) (hz : z ∉ (V : X.Opens)) :
    (primeI z).ideal V = ⊤ := by
  rw [Ideal.eq_top_iff_one, ideal_primeI, PrimeSpectrum.mem_vanishingIdeal]
  intro w hw
  have hw' : z ⤳ V.2.fromSpec w := specializes_iff_mem_closure.mpr hw
  exact absurd (hw'.mem_open (V : X.Opens).isOpen (fromSpec_mem V.2 w)) hz

/-- A codimension-one point is not dense. -/
lemma support_primeI_ne_top {z : X} (hz : coheight z = 1) : (primeI z).support ≠ ⊤ := by
  intro h
  have h1 : ¬ IsMax z := fun hmax => by
    rw [Order.coheight_eq_zero.mpr hmax] at hz; exact zero_ne_one hz
  obtain ⟨η, hη⟩ := not_isMax_iff.mp h1
  have hmem : η ∈ ((primeI z).support : Set X) := by rw [h]; exact Set.mem_univ _
  rw [coe_support_primeI] at hmem
  exact hη.not_ge (show η ≤ z from specializes_iff_mem_closure.mpr hmem)

/-- The UFD hypothesis at a closed point of a chart, transported to `R_m`. -/
lemma ufd_localization {V : X.Opens} (hV : IsAffineOpen V) (m : Ideal Γ(X, V)) [m.IsPrime]
    (hufd : UniqueFactorizationMonoid (X.presheaf.stalk (hV.fromSpec ⟨m, ‹_›⟩)))
    [IsDomain (X.presheaf.stalk (hV.fromSpec ⟨m, ‹_›⟩))] [IsDomain (Localization.AtPrime m)] :
    UniqueFactorizationMonoid (Localization.AtPrime m) := by
  let mm : PrimeSpectrum Γ(X, V) := ⟨m, ‹_›⟩
  let _ : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec mm)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hV.fromSpec mm, fromSpec_mem hV mm⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec mm)) m :=
    hV.isLocalization_stalk' mm (fromSpec_mem hV mm)
  exact (IsLocalization.algEquiv m.primeCompl (X.presheaf.stalk (hV.fromSpec mm))
    (Localization.AtPrime m)).toRingEquiv.toMulEquiv.uniqueFactorizationMonoid hufd

/-- **O6**: a codimension-one point with factorial local rings is locally principal. -/
theorem isLocPrin_primeI [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {z : X}
    (hz : coheight z = 1) : IsLocPrin (primeI z) := by
  intro V m hm
  by_cases hzV : z ∈ (V : X.Opens)
  · obtain ⟨y, rfl⟩ := exists_fromSpec_eq V.2 hzV
    rw [ideal_primeI_fromSpec V.2 y]
    have : Nonempty (V : X.Opens) := ⟨⟨_, hzV⟩⟩
    have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
    have : y.asIdeal.IsPrime := y.isPrime
    have : m.IsPrime := hm.isPrime
    have hy : y.asIdeal.height = 1 := by rw [← coheight_fromSpec V.2 y]; exact hz
    have : UniqueFactorizationMonoid (Localization.AtPrime m) :=
      ufd_localization V.2 m (hufd _)
    obtain ⟨a, ha, -, s, hs, hdvd⟩ := exists_dvd_of_ufd_localization y.asIdeal hy m
    exact ⟨a, ha, s, hs, fun w hw => Ideal.mem_span_singleton.mpr (hdvd w hw)⟩
  · rw [ideal_primeI_of_notMem V hzV]
    refine ⟨1, Submodule.mem_top, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h),
      fun w _ => ?_⟩
    rw [Ideal.span_singleton_one]; exact Submodule.mem_top

/-- **O6**, smooth form. -/
theorem isLocPrin_primeI_of_smooth {k : Type u} [Field k] [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f] {z : X} (hz : coheight z = 1) : IsLocPrin (primeI z) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact isLocPrin_primeI (uniqueFactorizationMonoid_stalk_of_smooth f) hz

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Form =====
section

/-!
# S4-IntersectB, file Form: intersection numbers of prime-divisor products (O7, part 1)

* `support_finite_of_compact`: a cycle on a quasi-compact scheme has finite support.
* `support_mul_ne_top`, `support_prod_mul_ne_top`: proper supports stay proper under products.
* `inumZ`: `inum` extended by `0`; `inumZ_perm` (B1), `inumZ_cons_top`, `inumZ_mul` (B3),
  `inumZ_pow_mul`, `inumZ_prod_mul`: `(∏ P_z^{f z}) · J · E = Σ f z (P_z · E) + (J · E)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Top

variable {X : Scheme.{u}}

/-- A cycle on a quasi-compact scheme has finite support. -/
lemma support_finite_of_compact [CompactSpace X] (D : AlgebraicCycle X ℤ) :
    (Function.support D).Finite := by
  choose t ht hfin using fun x => D.supportLocallyFiniteWithinDomain' x (Set.mem_univ x)
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover t (fun x _ => ht x)
  refine (s.finite_toSet.biUnion fun x _ => hfin x).subset fun z hz => ?_
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z))
  exact Set.mem_biUnion hx ⟨hzx, hz⟩

/-- In an irreducible space two proper closed supports do not cover. -/
lemma support_mul_ne_top [IrreducibleSpace X] {I J : X.IdealSheafData}
    (hI : I.support ≠ ⊤) (hJ : J.support ≠ ⊤) : (I * J).support ≠ ⊤ := by
  rw [Scheme.IdealSheafData.support_mul]
  intro h
  have hu : (I.support : Set X) ∪ J.support = Set.univ := by
    rw [← TopologicalSpace.Closeds.coe_sup, h, TopologicalSpace.Closeds.coe_top]
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp
      (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
      _ _ I.support.isClosed J.support.isClosed hu.ge with h2 | h2
  · exact hI (SetLike.coe_injective ((Set.univ_subset_iff.mp h2).trans
      TopologicalSpace.Closeds.coe_top.symm))
  · exact hJ (SetLike.coe_injective ((Set.univ_subset_iff.mp h2).trans
      TopologicalSpace.Closeds.coe_top.symm))

lemma support_pow_mul_ne_top [IrreducibleSpace X] {P J : X.IdealSheafData}
    (hP : P.support ≠ ⊤) (hJ : J.support ≠ ⊤) (m : ℕ) : (P ^ m * J).support ≠ ⊤ := by
  induction m with
  | zero => simpa using hJ
  | succ m ih => rw [pow_succ, _root_.mul_right_comm]; exact support_mul_ne_top ih hP

lemma support_prod_mul_ne_top [IrreducibleSpace X] (P : X → X.IdealSheafData) (f : X → ℕ)
    (s : Finset X) (hP : ∀ z ∈ s, (P z).support ≠ ⊤) {J : X.IdealSheafData}
    (hJ : J.support ≠ ⊤) : ((∏ z ∈ s, P z ^ f z) * J).support ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hJ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, _root_.mul_assoc]
    exact support_pow_mul_ne_top (hP a (Finset.mem_insert_self _ _))
      (ih fun z hz => hP z (Finset.mem_insert_of_mem hz)) (f a)

end Top

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

open Classical in
/-- `inum` extended by `0` to configurations with a dense slot. -/
noncomputable def inumZ (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) : ℤ :=
  if h : ∀ i, (D i).support ≠ ⊤ then (inum A g hdim D h : ℤ) else 0

lemma inumZ_of (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (h : ∀ i, (D i).support ≠ ⊤) :
    inumZ A g hdim D = inum A g hdim D h := by
  rw [inumZ, dif_pos h]

lemma inumZ_of_not (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (h : ¬ ∀ i, (D i).support ≠ ⊤) :
    inumZ A g hdim D = 0 := by
  rw [inumZ, dif_neg h]

/-- B1 for `inumZ`. -/
lemma inumZ_perm (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (σ : Equiv.Perm (Fin g)) :
    inumZ A g hdim (fun i => D (σ i)) = inumZ A g hdim D := by
  by_cases h : ∀ i, (D i).support ≠ ⊤
  · rw [inumZ_of A g hdim D h, inumZ_of A g hdim _ (fun i => h (σ i)), inum_perm]
  · rw [inumZ_of_not A g hdim D h, inumZ_of_not A g hdim]
    exact fun h' => h fun i => by simpa using h' (σ.symm i)

lemma len_top : len A (⊤ : A.left.IdealSheafData) = 0 := by
  obtain ⟨V, -⟩ := exists_affine_mem A ∅
  letI := (algV A V).hom.toAlgebra
  obtain ⟨-, e⟩ := len_eq_finrank A ⊤ V (by simp) (by simp)
  rw [e]
  have : Subsingleton (Γ(A.left, V) ⧸ (⊤ : A.left.IdealSheafData).ideal V) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

lemma inumZ_cons_top (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (E : Fin n → A.left.IdealSheafData) :
    inumZ A (n + 1) hdim (Fin.cons ⊤ E : Fin (n + 1) → A.left.IdealSheafData) = 0 := by
  by_cases h : ∀ i, ((Fin.cons ⊤ E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤
  · rw [inumZ_of A _ hdim _ h]
    have := isIntegral_Pw A (n + 1)
    have := isProper_Pw A (n + 1)
    obtain ⟨U, hU, hne, hc⟩ := inum_spec A (n + 1) hdim _ h
    obtain ⟨c, hcU⟩ := exists_pt_mem (Pw A (n + 1)) U hU.isLocallyClosed hne
    rw [← (hc c hcU).2, Zid_cons, Scheme.IdealSheafData.comap_top, top_sup_eq, len_top]
    rfl
  · exact inumZ_of_not A _ hdim _ h

lemma cons_support_ne_top {n : ℕ} {X : A.left.IdealSheafData} {E : Fin n → A.left.IdealSheafData}
    (hX : X.support ≠ ⊤) (hE : ∀ j, (E j).support ≠ ⊤) :
    ∀ i, ((Fin.cons X E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤ :=
  fun i => Fin.cases (by simpa using hX) (fun j => by simpa using hE j) i

lemma inumZ_cons_of_not (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    {E : Fin n → A.left.IdealSheafData} (hE : ¬ ∀ j, (E j).support ≠ ⊤)
    (X : A.left.IdealSheafData) :
    inumZ A (n + 1) hdim (Fin.cons X E : Fin (n + 1) → A.left.IdealSheafData) = 0 := by
  refine inumZ_of_not A _ hdim _ fun h => hE fun j => ?_
  simpa using h j.succ

/-- B3 for `inumZ`. -/
lemma inumZ_mul (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    {I I' : A.left.IdealSheafData} (E : Fin n → A.left.IdealSheafData)
    (hI : I.support ≠ ⊤) (hI' : I'.support ≠ ⊤) (hloc : IsLocPrin I') :
    inumZ A (n + 1) hdim (Fin.cons (I * I') E : Fin (n + 1) → A.left.IdealSheafData) =
      inumZ A (n + 1) hdim (Fin.cons I E : Fin (n + 1) → A.left.IdealSheafData) +
        inumZ A (n + 1) hdim (Fin.cons I' E : Fin (n + 1) → A.left.IdealSheafData) := by
  by_cases hE : ∀ j, (E j).support ≠ ⊤
  · rw [inumZ_of A _ hdim _ (cons_support_ne_top A (support_mul_ne_top hI hI') hE),
      inumZ_of A _ hdim _ (cons_support_ne_top A hI hE),
      inumZ_of A _ hdim _ (cons_support_ne_top A hI' hE), inum_mul A n hdim I I' E _ _ _ hloc]
    push_cast; rfl
  · rw [inumZ_cons_of_not A n hdim hE, inumZ_cons_of_not A n hdim hE,
      inumZ_cons_of_not A n hdim hE, add_zero]

lemma inumZ_pow_mul (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    {P J : A.left.IdealSheafData} (E : Fin n → A.left.IdealSheafData)
    (hP : P.support ≠ ⊤) (hJ : J.support ≠ ⊤) (hloc : IsLocPrin P) (m : ℕ) :
    inumZ A (n + 1) hdim (Fin.cons (P ^ m * J) E : Fin (n + 1) → A.left.IdealSheafData) =
      m * inumZ A (n + 1) hdim (Fin.cons P E : Fin (n + 1) → A.left.IdealSheafData) +
        inumZ A (n + 1) hdim (Fin.cons J E : Fin (n + 1) → A.left.IdealSheafData) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, _root_.mul_right_comm,
      inumZ_mul A n hdim E (support_pow_mul_ne_top hP hJ m) hP hloc, ih]
    push_cast; ring

/-- Expansion of a product of locally principal factors in slot `0`. -/
lemma inumZ_prod_mul (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (P : A.left → A.left.IdealSheafData) (f : A.left → ℕ) (E : Fin n → A.left.IdealSheafData)
    (s : Finset A.left) (hP : ∀ z ∈ s, (P z).support ≠ ⊤) (hloc : ∀ z ∈ s, IsLocPrin (P z))
    {J : A.left.IdealSheafData} (hJ : J.support ≠ ⊤) :
    inumZ A (n + 1) hdim
        (Fin.cons ((∏ z ∈ s, P z ^ f z) * J) E : Fin (n + 1) → A.left.IdealSheafData) =
      ∑ z ∈ s, (f z : ℤ) *
          inumZ A (n + 1) hdim (Fin.cons (P z) E : Fin (n + 1) → A.left.IdealSheafData) +
        inumZ A (n + 1) hdim (Fin.cons J E : Fin (n + 1) → A.left.IdealSheafData) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ z ∈ s, (P z).support ≠ ⊤ := fun z hz => hP z (Finset.mem_insert_of_mem hz)
    rw [Finset.prod_insert ha, _root_.mul_assoc,
      inumZ_pow_mul A n hdim E (hP a (Finset.mem_insert_self _ _))
        (support_prod_mul_ne_top P f s hs hJ) (hloc a (Finset.mem_insert_self _ _)),
      ih hs fun z hz => hloc z (Finset.mem_insert_of_mem hz), Finset.sum_insert ha]
    ring

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Form2 =====
section

/-!
# S4-IntersectB, file Form2: the intersection form on all divisors (O7, part 2; L33)

* `multi_expand`: a slot-wise expansion rule expands all `n` slots at once.
* `effI D = ∏ᶠ z, P_z ^ (D z)⁺`; `inumZ_update_effI`: expansion of an effective Weil divisor in
  any slot.
* `iform D = Σ_z (∏ D_i(z_i)) · (P_{z_1} ⋯ P_{z_n})`: additive in each slot (`iform_update_add`),
  symmetric (`iform_perm`), and equal to `inumZ (effI ∘ D)` on effective Weil divisors
  (`iform_eq_inumZ`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.JacDivisors

section Comb

variable {α β : Type*}

lemma support_prod_subset {n : ℕ} (w : Fin n → α → ℤ) (G : (Fin n → α) → ℤ) :
    Function.support (fun z : Fin n → α => (∏ i, w i (z i)) * G z) ⊆
      Set.pi Set.univ fun i => Function.support (w i) := by
  intro z hz i _
  exact Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hz) i (Finset.mem_univ i)

lemma finite_support_prod {n : ℕ} (w : Fin n → α → ℤ) (hw : ∀ i, (Function.support (w i)).Finite)
    (G : (Fin n → α) → ℤ) :
    (Function.support (fun z : Fin n → α => (∏ i, w i (z i)) * G z)).Finite :=
  (Set.Finite.pi hw).subset (support_prod_subset w G)

/-- Slot-wise expansion rules expand all slots. -/
theorem multi_expand (p : α → β) : ∀ (n : ℕ) (F : (Fin n → β) → ℤ) (e : Fin n → β)
    (w : Fin n → α → ℤ), (∀ i, (Function.support (w i)).Finite) →
    (∀ (Q : Fin n → β) (i : Fin n),
      F (Function.update Q i (e i)) = ∑ᶠ a, w i a * F (Function.update Q i (p a))) →
    F e = ∑ᶠ z : Fin n → α, (∏ i, w i (z i)) * F (fun i => p (z i))
  | 0, F, e, w, _, _ => by
    rw [finsum_unique]
    obtain rfl : e = fun i => p ((default : Fin 0 → α) i) := funext fun i => i.elim0
    simp
  | n + 1, F, e, w, hw, h => by
    have h0 := h e 0
    rw [Function.update_eq_self] at h0
    rw [h0]
    have hIH : ∀ a, F (Function.update e 0 (p a)) = ∑ᶠ z' : Fin n → α,
        (∏ j, w j.succ (z' j)) * F (Fin.cons (p a) fun j => p (z' j)) := by
      intro a
      have he : Function.update e 0 (p a) = Fin.cons (p a) (Fin.tail e) := by
        rw [← Fin.update_cons_zero (e 0) (Fin.tail e) (p a), Fin.cons_self_tail]
      rw [he]
      refine multi_expand p n (fun Q => F (Fin.cons (p a) Q)) (Fin.tail e) (fun j => w j.succ)
        (fun j => hw j.succ) fun Q j => ?_
      simp only [Fin.cons_update]
      exact h _ j.succ
    simp_rw [hIH]
    have hfin := finite_support_prod w hw (fun z => F fun i => p (z i))
    rw [← finsum_comp_equiv (Fin.consEquiv fun _ => α)] at *
    rw [finsum_curry _ (by
      refine (hfin.preimage (Fin.consEquiv fun _ => α).injective.injOn).subset fun x hx => ?_
      exact hx)]
    refine finsum_congr fun a => ?_
    rw [mul_finsum]
    refine finsum_congr fun z' => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [_root_.mul_assoc]
    congr 3
    funext i
    refine Fin.cases rfl (fun j => rfl) i

lemma update_swap {n : ℕ} (P : Fin (n + 1) → β) (i : Fin (n + 1)) (Y : β) :
    (fun j => Function.update P i Y (Equiv.swap 0 i j)) =
      (Fin.cons Y fun j => P (Equiv.swap 0 i j.succ) : Fin (n + 1) → β) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · rw [Fin.cons_succ, Function.update_of_ne]
    rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    exact Fin.succ_ne_zero j

lemma prod_update_apply {n : ℕ} (D : Fin n → α → ℤ) (i : Fin n) (Y : α → ℤ) (z : Fin n → α) :
    ∏ j, Function.update D i Y j (z j) = Y (z i) * ∏ j ∈ Finset.univ.erase i, D j (z j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

end Comb

section Eff

variable {X : Scheme.{u}}

/-- The effective ideal sheaf `∏ P_z ^ (D z)⁺` of a cycle. -/
noncomputable def effI (D : AlgebraicCycle X ℤ) : X.IdealSheafData :=
  ∏ᶠ z, primeI z ^ (D z).toNat

lemma effI_eq_prod (D : AlgebraicCycle X ℤ) (s : Finset X) (hs : Function.support D ⊆ s) :
    effI D = ∏ z ∈ s, primeI z ^ (D z).toNat := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun z hz => hs fun h => hz ?_
  simp [h]

end Eff

section Iform

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- Expansion of an effective Weil divisor in slot `0`. -/
theorem inumZ_cons_effI (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ)) (D : AlgebraicCycle A.left ℤ)
    (hW : D ∈ weilDivisors A.left) (hD : ∀ z, 0 ≤ D z) (E : Fin n → A.left.IdealSheafData) :
    inumZ A (n + 1) hdim (Fin.cons (effI D) E : Fin (n + 1) → A.left.IdealSheafData) =
      ∑ᶠ z, D z *
        inumZ A (n + 1) hdim (Fin.cons (primeI z) E : Fin (n + 1) → A.left.IdealSheafData) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hfin := support_finite_of_compact D
  have hs : Function.support D ⊆ hfin.toFinset := fun z hz => hfin.mem_toFinset.mpr hz
  have h1 : ∀ z ∈ hfin.toFinset, Order.coheight z = 1 := fun z hz =>
    hW z (hfin.mem_toFinset.mp hz)
  have htop : (⊤ : A.left.IdealSheafData).support ≠ ⊤ := by
    intro h
    obtain ⟨x⟩ : Nonempty A.left := inferInstance
    have hx : x ∈ ((⊤ : A.left.IdealSheafData).support : Set A.left) := by
      rw [h]; exact Set.mem_univ _
    simp [Scheme.IdealSheafData.support_top] at hx
  rw [effI_eq_prod D _ hs, ← _root_.mul_one (∏ z ∈ hfin.toFinset, primeI z ^ (D z).toNat),
    Scheme.IdealSheafData.one_eq_top,
    inumZ_prod_mul A n hdim primeI (fun z => (D z).toNat) E _
      (fun z hz => support_primeI_ne_top (h1 z hz)) (fun z hz => isLocPrin_primeI hufd (h1 z hz))
      htop, inumZ_cons_top, add_zero,
    finsum_eq_sum_of_support_subset _ (fun z hz => hs (left_ne_zero_of_mul hz))]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Int.toNat_of_nonneg (hD z)]

/-- Expansion of an effective Weil divisor in any slot. -/
theorem inumZ_update_effI
    (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (P : Fin (n + 1) → A.left.IdealSheafData) (i : Fin (n + 1)) (D : AlgebraicCycle A.left ℤ)
    (hW : D ∈ weilDivisors A.left) (hD : ∀ z, 0 ≤ D z) :
    inumZ A (n + 1) hdim (Function.update P i (effI D)) =
      ∑ᶠ z, D z * inumZ A (n + 1) hdim (Function.update P i (primeI z)) := by
  rw [← inumZ_perm A _ hdim _ (Equiv.swap 0 i), update_swap,
    inumZ_cons_effI A hufd n hdim D hW hD]
  refine finsum_congr fun z => ?_
  rw [← inumZ_perm A _ hdim (Function.update P i (primeI z)) (Equiv.swap 0 i), update_swap]

/-- **L33**: the intersection form on all cycles, the multilinear extension of `inumZ` on prime
divisors. -/
noncomputable def iform (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ n)
    (D : Fin n → AlgebraicCycle A.left ℤ) : ℤ :=
  ∑ᶠ z : Fin n → A.left, (∏ i, D i (z i)) * inumZ A n hdim (fun i => primeI (z i))

/-- On effective Weil divisors `iform` is the intersection number of the effective ideals. -/
theorem iform_eq_inumZ (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ n) (D : Fin n → AlgebraicCycle A.left ℤ)
    (hW : ∀ i, D i ∈ weilDivisors A.left) (hD : ∀ i z, 0 ≤ D i z) :
    iform A n hdim D = inumZ A n hdim (fun i => effI (D i)) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  refine (multi_expand primeI n (inumZ A n hdim) (fun i => effI (D i)) (fun i z => D i z)
    (fun i => support_finite_of_compact (D i)) fun Q i => ?_).symm
  cases n with
  | zero => exact i.elim0
  | succ m => exact inumZ_update_effI A hufd m hdim Q i (D i) (hW i) (hD i)

/-- **L33**: additivity in each slot. -/
theorem iform_update_add (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ n)
    (D : Fin n → AlgebraicCycle A.left ℤ) (i : Fin n) (D₁ D₂ : AlgebraicCycle A.left ℤ) :
    iform A n hdim (Function.update D i (D₁ + D₂)) =
      iform A n hdim (Function.update D i D₁) + iform A n hdim (Function.update D i D₂) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have e : ∀ z : Fin n → A.left,
      (∏ j, Function.update D i (D₁ + D₂) j (z j)) * inumZ A n hdim (fun j => primeI (z j)) =
        (∏ j, Function.update D i D₁ j (z j)) * inumZ A n hdim (fun j => primeI (z j)) +
          (∏ j, Function.update D i D₂ j (z j)) * inumZ A n hdim (fun j => primeI (z j)) := by
    intro z
    have h : ∀ Y : AlgebraicCycle A.left ℤ, ∏ j, Function.update D i Y j (z j) =
        Y (z i) * ∏ j ∈ Finset.univ.erase i, D j (z j) := fun Y => by
      rw [← prod_update_apply (fun j => ⇑(D j)) i (⇑Y) z]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [h, h, h, Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    ring
  simp only [iform]
  rw [finsum_congr e]
  exact finsum_add_distrib
    (finite_support_prod _ (fun j => support_finite_of_compact (Function.update D i D₁ j)) _)
    (finite_support_prod _ (fun j => support_finite_of_compact (Function.update D i D₂ j)) _)

/-- **L33**: symmetry. -/
theorem iform_perm (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ n)
    (D : Fin n → AlgebraicCycle A.left ℤ) (σ : Equiv.Perm (Fin n)) :
    iform A n hdim (fun i => D (σ i)) = iform A n hdim D := by
  simp only [iform]
  let e : (Fin n → A.left) ≃ (Fin n → A.left) :=
    { toFun := fun z i => z (σ i), invFun := fun z i => z (σ.symm i),
      left_inv := fun z => by funext i; simp, right_inv := fun z => by funext i; simp }
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun z => ?_
  show (∏ i, D (σ i) (z (σ i))) * inumZ A n hdim (fun i => primeI (z (σ i))) = _
  congr 1
  · exact Equiv.prod_comp σ (fun i => D i (z i))
  · exact inumZ_perm A n hdim (fun i => primeI (z i)) σ

end Iform

end RamanujanPetersson.IntersectB

end

-- ===== S4.Def_RP_IntersectB_Pen3 =====
section

/-!
# S4-IntersectB, O9 part 3: the Weil bridge for the pencil of a rational function

* `ideal_res_span`: a principal component of an ideal sheaf stays principal on a smaller affine.
* `ideal_prod_pow`: components of finite products of powers of ideal sheaves.
* `exists_chart_gens`: finitely many codimension-one prime ideal sheaves are principal on one
  affine chart around any point (factorial local rings).
* `ord_chart_gen`: such a generator has order one along its own prime divisor and order zero at
  the other codimension-one points of the chart.
* `effGen`: near every point, `effI D` is generated by one section whose order at every
  codimension-one point of the chart is the positive part of `D`.
* `exists_bridge`: near every point, the zero and pole ideal sheaves `effI (div f)` and
  `effI (-div f)` are generated by sections `u`, `v` of one affine chart with `u = f * v` in the
  function field.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology Order IsLocalRing

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.JacDivisors

variable {X : Scheme.{u}}

/-- A principal component restricts to a principal component on a smaller affine open. -/
lemma ideal_res_span (I : X.IdealSheafData) {U V : X.affineOpens} (h : U ≤ V) {a : Γ(X, V)}
    (ha : I.ideal V = Ideal.span {a}) :
    I.ideal U = Ideal.span {X.presheaf.map (homOfLE h).op a} := by
  rw [← I.map_ideal h, ha, Ideal.map_span, Set.image_singleton]

lemma ideal_prod_pow (s : Finset X) (P : X → X.IdealSheafData) (n : X → ℕ) (W : X.affineOpens) :
    (∏ z ∈ s, P z ^ n z).ideal W = ∏ z ∈ s, (P z).ideal W ^ n z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top]
    rfl
  | insert z s hz ih =>
    rw [Finset.prod_insert hz, Finset.prod_insert hz, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
      Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, ih]

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The prime ideal sheaves of finitely many codimension-one points are principal on one affine
chart around `x`. -/
lemma exists_chart_gens (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (s : Finset X) (hs : ∀ z ∈ s, coheight z = 1) (x : X) :
    ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ ∃ a : X → Γ(X, W),
      ∀ z ∈ s, (primeI z).ideal W = Ideal.span {a z} := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hV hxV
  obtain ⟨m, hm, hym⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
  have key : ∀ z : X, ∃ v t : Γ(X, V), t ∉ m ∧ (z ∈ s → v ∈ (primeI z).ideal ⟨V, hV⟩ ∧
      ∀ w ∈ (primeI z).ideal ⟨V, hV⟩, t * w ∈ Ideal.span {v}) := by
    intro z
    by_cases hz : z ∈ s
    · obtain ⟨v, hv, t, ht, h⟩ := isLocPrin_primeI hufd (hs z hz) ⟨V, hV⟩ m hm
      exact ⟨v, t, ht, fun _ => ⟨hv, h⟩⟩
    · exact ⟨1, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h), fun h => absurd h hz⟩
  choose v t ht hv using key
  have : m.IsPrime := hm.isPrime
  have hT : (∏ z ∈ s, t z) ∉ m := by
    intro h
    obtain ⟨z, -, hz⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact ht z hz
  obtain ⟨W, hW⟩ : ∃ W : X.affineOpens,
      W = X.affineBasicOpen (U := ⟨V, hV⟩) (∏ z ∈ s, t z) := ⟨_, rfl⟩
  have hWV : (W : X.Opens) ≤ V := by rw [hW]; exact X.basicOpen_le _
  have h1 : IsUnit ((X.presheaf.map (homOfLE hWV).op).hom (∏ z ∈ s, t z)) := by
    subst hW; exact X.toRingedSpace.isUnit_res_basicOpen _
  refine ⟨W, ?_, fun z => (X.presheaf.map (homOfLE hWV).op).hom (v z), fun z hz => ?_⟩
  · rw [hW]; exact (fromSpec_mem_basicOpen_iff hV _ y).mpr fun h => hT (hym h)
  · set ρ := (X.presheaf.map (homOfLE hWV).op).hom with hρ
    have hu : IsUnit (ρ (t z)) := by
      have h2 := map_mul ρ (t z) (∏ w ∈ s.erase z, t w)
      rw [Finset.mul_prod_erase s t hz] at h2
      rw [h2] at h1
      exact isUnit_of_mul_isUnit_left h1
    rw [← (primeI z).map_ideal (U := W) (V := ⟨V, hV⟩) hWV]
    apply le_antisymm
    · refine Ideal.map_le_of_le_comap fun w hw => ?_
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hv z hz).2 w hw)
      refine Ideal.mem_span_singleton'.mpr ⟨↑hu.unit⁻¹ * ρ c, ?_⟩
      have e : ρ c * ρ (v z) = ρ (t z) * ρ w := by rw [← map_mul, ← map_mul, hc]
      rw [mul_assoc, e, ← mul_assoc, hu.val_inv_mul, one_mul]
      exact rfl
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_map_of_mem _ (hv z hz).1))

open Classical in
/-- A chart generator of a codimension-one prime has order one along it and order zero at the
other codimension-one points of the chart. -/
lemma ord_chart_gen {W : X.affineOpens} [Nonempty (W : X.Opens)] {z : X} (hz : coheight z = 1)
    {a : Γ(X, W)} (ha : (primeI z).ideal W = Ideal.span {a}) :
    a ≠ 0 ∧ ∀ w ∈ (W : X.Opens), coheight w = 1 →
      Scheme.ord (X.germToFunctionField W a) w = if w = z then 1 else 0 := by
  by_cases hzW : z ∈ (W : X.Opens)
  · obtain ⟨y, rfl⟩ := exists_fromSpec_eq W.2 hzW
    have hy : y.asIdeal = Ideal.span {a} := (ideal_primeI_fromSpec W.2 y).symm.trans ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      have h1 : ¬ IsMax (W.2.fromSpec y) := fun hmax => by
        rw [Order.coheight_eq_zero.mpr hmax] at hz; exact zero_ne_one hz
      obtain ⟨η, hη⟩ := not_isMax_iff.mp h1
      have hηW : η ∈ (W : X.Opens) :=
        (show η ⤳ W.2.fromSpec y from hη.le).mem_open W.1.isOpen hzW
      obtain ⟨y'', rfl⟩ := exists_fromSpec_eq W.2 hηW
      have hbot : y.asIdeal = ⊥ := by rw [hy]; exact Ideal.span_singleton_eq_bot.mpr rfl
      have : y'' = y := PrimeSpectrum.ext (le_antisymm
        ((fromSpec_specializes_iff W.2 y'' y).mp hη.le) (by rw [hbot]; exact bot_le))
      exact hη.ne (by rw [this])
    refine ⟨ha0, fun w hw hw1 => ?_⟩
    by_cases hwz : w = W.2.fromSpec y
    · subst hwz
      rw [if_pos rfl]
      refine ord_germ_eq_one hw hz ha0 ?_
      rw [maximalIdeal_stalk_fromSpec W.2 y, hy, Ideal.map_span, Set.image_singleton]
    · rw [if_neg hwz]
      obtain ⟨y', rfl⟩ := exists_fromSpec_eq W.2 hw
      refine ord_germ_eq_zero a ((fromSpec_mem_basicOpen_iff W.2 a y').mpr fun hay => ?_)
      have hsp : W.2.fromSpec y ⤳ W.2.fromSpec y' := (fromSpec_specializes_iff W.2 y y').mpr
        (by rw [hy]; exact (Ideal.span_singleton_le_iff_mem _).mpr hay)
      have hle : W.2.fromSpec y' ≤ W.2.fromSpec y := hsp
      have hlt : W.2.fromSpec y' < W.2.fromSpec y :=
        lt_of_le_not_ge hle fun hge => hwz (Specializes.antisymm hsp hge).eq.symm
      have := coheight_strictAnti hlt (by simp [hz])
      rw [hz, hw1] at this
      exact lt_irrefl _ this
  · have htop : Ideal.span {a} = ⊤ := by rw [← ha]; exact ideal_primeI_of_notMem W hzW
    have hunit : IsUnit a := Ideal.span_singleton_eq_top.mp htop
    refine ⟨hunit.ne_zero, fun w hw _ => ?_⟩
    rw [if_neg (fun h : w = z => hzW (h ▸ hw))]
    exact ord_germ_eq_zero a (by rw [X.basicOpen_of_isUnit hunit]; exact hw)

/-- **Local generators of `effI D`** with the expected orders. -/
theorem effGen (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {D : AlgebraicCycle X ℤ} (hD : D ∈ weilDivisors X) (hfin : (Function.support D).Finite)
    (x : X) :
    ∃ W : X.affineOpens, ∃ hxW : x ∈ (W : X.Opens), ∃ u : Γ(X, W), u ≠ 0 ∧
      (effI D).ideal W = Ideal.span {u} ∧ ∀ w ∈ (W : X.Opens), coheight w = 1 →
        Scheme.ord (algebraMap _ X.functionField (X.presheaf.germ W x hxW u)) w = (D w).toNat := by
  classical
  have hs : ∀ z ∈ hfin.toFinset, coheight z = 1 :=
    fun z hz => hD z ((Set.Finite.mem_toFinset hfin).mp hz)
  obtain ⟨W, hxW, a, ha⟩ := exists_chart_gens hufd hfin.toFinset hs x
  have : Nonempty (W : X.Opens) := ⟨⟨x, hxW⟩⟩
  have hA := fun z (hz : z ∈ hfin.toFinset) => ord_chart_gen (hs z hz) (ha z hz)
  refine ⟨W, hxW, ∏ z ∈ hfin.toFinset, a z ^ (D z).toNat, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun z hz => pow_ne_zero _ (hA z hz).1
  · have e : ∀ z ∈ hfin.toFinset, (primeI z).ideal W ^ (D z).toNat =
        Ideal.span {a z ^ (D z).toNat} := fun z hz => by rw [ha z hz, Ideal.span_singleton_pow]
    rw [effI_eq_prod D hfin.toFinset (Set.Finite.coe_toFinset hfin).ge,
      ideal_prod_pow hfin.toFinset primeI (fun z => (D z).toNat) W, Finset.prod_congr rfl e,
      Ideal.prod_span_singleton]
  · intro w hw hw1
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, map_prod]
    have e : ∀ z ∈ hfin.toFinset, X.germToFunctionField W (a z ^ (D z).toNat) =
        X.germToFunctionField W (a z) ^ (((D z).toNat : ℕ) : ℤ) := fun z _ => by
      rw [map_pow, zpow_natCast]
    rw [Finset.prod_congr rfl e, ord_prod_zpow hfin.toFinset _ _
      (fun z hz => germToFunctionField_ne_zero (hA z hz).1) w,
      Finset.sum_congr rfl (fun z hz => congrArg (fun t => (((D z).toNat : ℕ) : ℤ) * t)
        ((hA z hz).2 w hw hw1))]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · have : D w = 0 := by simpa using h
      simp [this]

/-- **Weil bridge**: near every point the zero and pole ideal sheaves of `f` are generated by
sections `u`, `v` of one affine chart with `u = f * v` in the function field. -/
theorem exists_bridge (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {f : X.functionField} (hf : f ≠ 0) (hfin : (Function.support (div X f)).Finite) (x : X) :
    ∃ W : X.affineOpens, ∃ hxW : x ∈ (W : X.Opens), ∃ u v : Γ(X, W),
      (effI (div X f)).ideal W = Ideal.span {u} ∧ (effI (-div X f)).ideal W = Ideal.span {v} ∧
      algebraMap _ X.functionField (X.presheaf.germ W x hxW u) =
        f * algebraMap _ X.functionField (X.presheaf.germ W x hxW v) := by
  have hD := div_mem_weilDivisors f
  have hfin' : (Function.support (-div X f)).Finite := by
    convert hfin using 1; ext z; simp
  obtain ⟨W1, hx1, u1, hu1, hI1, ho1⟩ := effGen hufd hD hfin x
  obtain ⟨W2, hx2, v2, hv2, hI2, ho2⟩ := effGen hufd (neg_mem hD) hfin' x
  have hgu : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W1 x hx1 u1) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (germ_ne_zero hx1 hu1)
  have hgv : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W2 x hx2 v2) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (germ_ne_zero hx2 hv2)
  have := hufd x
  obtain ⟨e0, he0, he0'⟩ := exists_isUnit_of_ord_eq_zero x
    (div_ne_zero (mul_ne_zero hf hgv) hgu) fun z hzx hz1 => by
      rw [div_eq_mul_inv, Scheme.ord_mul (mul_ne_zero hf hgv) (inv_ne_zero hgu),
        Scheme.ord_mul hf hgv, ord_inv' hgu, ho1 z (hzx.mem_open W1.1.isOpen hx1) hz1,
        ho2 z (hzx.mem_open W2.1.isOpen hx2) hz1]
      have hneg : (-div X f) z = -(div X f z) := by simp
      rw [hneg, show Scheme.ord f z = div X f z from rfl]
      generalize div X f z = n
      omega
  obtain ⟨U, hxU, e, he⟩ := X.presheaf.exists_germ_eq e0
  have hxe : x ∈ X.basicOpen e := (X.mem_basicOpen e x hxU).mpr (by rw [he]; exact he0)
  obtain ⟨r, hr2, hxr⟩ := W1.2.exists_basicOpen_le (V := W2) ⟨x, hx2⟩ hx1
  obtain ⟨r', hr', hxr'⟩ := (X.affineBasicOpen r).2.exists_basicOpen_le ⟨x, hxe⟩ hxr
  obtain ⟨W, hW⟩ : ∃ W : X.affineOpens, W = X.affineBasicOpen r' := ⟨_, rfl⟩
  have hxW : x ∈ (W : X.Opens) := by rw [hW]; exact hxr'
  have hW1 : (W : X.Opens) ≤ W1 := by rw [hW]; exact (X.basicOpen_le r').trans (X.basicOpen_le r)
  have hW2 : (W : X.Opens) ≤ W2 := by rw [hW]; exact (X.basicOpen_le r').trans hr2
  have hWe : (W : X.Opens) ≤ X.basicOpen e := by rw [hW]; exact hr'
  have he' : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le e)).op e) :=
    X.toRingedSpace.isUnit_res_basicOpen e
  have hu : IsUnit (X.presheaf.map (homOfLE hWe).op
      (X.presheaf.map (homOfLE (X.basicOpen_le e)).op e)) :=
    he'.map (ConcreteCategory.hom (X.presheaf.map (homOfLE hWe).op))
  refine ⟨W, hxW,
    X.presheaf.map (homOfLE hWe).op (X.presheaf.map (homOfLE (X.basicOpen_le e)).op e) *
      X.presheaf.map (homOfLE hW1).op u1, X.presheaf.map (homOfLE hW2).op v2, ?_, ?_, ?_⟩
  · rw [Ideal.span_singleton_mul_left_unit hu]
    exact ideal_res_span (U := W) _ hW1 hI1
  · exact ideal_res_span (U := W) _ hW2 hI2
  · simp only [map_mul, TopCat.Presheaf.germ_res_apply]
    rw [he, he0']
    exact div_mul_cancel₀ _ hgu

end RamanujanPetersson.IntersectB

end


