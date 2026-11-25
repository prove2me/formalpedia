-- Prove2me | Definitions.Def_RPLib_FX_EtP1_08
-- name    : RPLib_FX_EtP1_08
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:58:46.149052+00:00
-- url     : https://prove2.me/theorems/6cb1c53f-3f9f-534f-8a2f-d282fa0ae179
-- title:
--   Étale cohomology of the projective line, library file 08 of 34
-- statement:
--   File 08 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Glue`: S4-EtCompact, part 31: gluing along a Zariski cover; endomorphisms of `Λ_X` (O8b, file 1)
--   * `S4.Def_RP_EtCompact_MVSplit`: S4-EtCompact, part 32: `H^1` vanishes when it vanishes on two affine charts (O8b, file 2)
--   * `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
--   * `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
--   * `S4.Def_RP_EtCompact_A1Kum`: S4-EtCompact, part 34: `H^1(A^1_k, Λ) = 0` for `k` algebraically closed (O8b, file 4)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_07

/-!
# Étale cohomology of the projective line, library file 08 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Glue`: S4-EtCompact, part 31: gluing along a Zariski cover; endomorphisms of `Λ_X` (O8b, file 1)
* `S4.Def_RP_EtCompact_MVSplit`: S4-EtCompact, part 32: `H^1` vanishes when it vanishes on two affine charts (O8b, file 2)
* `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
* `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
* `S4.Def_RP_EtCompact_A1Kum`: S4-EtCompact, part 34: `H^1(A^1_k, Λ) = 0` for `k` algebraically closed (O8b, file 4)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Glue =====
section

/-!
# S4-EtCompact, part 31: gluing along a Zariski cover; endomorphisms of `Λ_X` (O8b, file 1)

* `comp_quotCutπ_inf`: a map into `G` factoring through `j_{U!}G|_U` and `j_{V!}G|_V` factors through `j_{U⊓V!}`.
* **`exists_glue`**: for opens `U, V` covering `X`, maps `φ_U : j_{U!}F|_U ⟶ G`, `φ_V : j_{V!}F|_V ⟶ G` agreeing on
  `j_{U⊓V!}F|_{U⊓V}` glue to `φ : F ⟶ G` (Mayer-Vietoris: `j_{U!} ⊞ j_{V!} ⟶ F` is epi with kernel `j_{U⊓V!}`).
* **`eq_smulEnd`**: on a connected `X`, every `φ : Λ_X ⟶ Λ_X` is multiplication by a scalar.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Glue

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem comp_quotCutπ_inf {T G : EtSh Λ X} {U V : X.Opens} (t : T ⟶ G) (a : T ⟶ openCut Λ U G)
    (ha : a ≫ openCutι Λ U G = t) (b : T ⟶ openCut Λ V G) (hb : b ≫ openCutι Λ V G = t) :
    t ≫ quotCutπ Λ (U ⊓ V) G = 0 := by
  refine eq_zero_of_stalk _ (fun x => ?_)
  by_cases hU : x ∈ U
  · by_cases hV : x ∈ V
    · exact (isZero_stalk_quotCut (U ⊓ V) G _
        (mem_center_geomPtAt (show x ∈ (U ⊓ V : X.Opens) from Opens.mem_inf.2 ⟨hU, hV⟩))).eq_of_tgt _ _
    · rw [← hb, Category.assoc, CategoryTheory.Functor.map_comp,
        (isZero_stalk_openCut V G _ (not_mem_center_geomPtAt hV)).eq_of_src
          (((geomPtAt x).stalkF Λ).map (openCutι Λ V G ≫ quotCutπ Λ (U ⊓ V) G)) 0, comp_zero]
  · rw [← ha, Category.assoc, CategoryTheory.Functor.map_comp,
      (isZero_stalk_openCut U G _ (not_mem_center_geomPtAt hU)).eq_of_src
        (((geomPtAt x).stalkF Λ).map (openCutι Λ U G ≫ quotCutπ Λ (U ⊓ V) G)) 0, comp_zero]

/-- `j_{U!} F ⊞ j_{V!} F ⟶ F` is epi when `U, V` cover `X`. -/
theorem epi_biprod_desc_openCutι {F : EtSh Λ X} {U V : X.Opens} (hUV : ∀ x : X, x ∈ U ∨ x ∈ V) :
    Epi (biprod.desc (openCutι Λ U F) (openCutι Λ V F)) := by
  rw [epi_iff_stalk]
  intro x
  rcases hUV x with hx | hx
  · have : IsIso (((geomPtAt x).stalkF Λ).map (biprod.inl : openCut Λ U F ⟶ openCut Λ U F ⊞ openCut Λ V F) ≫
        ((geomPtAt x).stalkF Λ).map (biprod.desc (openCutι Λ U F) (openCutι Λ V F))) := by
      rw [← CategoryTheory.Functor.map_comp, biprod.inl_desc]
      exact isIso_stalk_openCutι U F _ (mem_center_geomPtAt hx)
    exact @epi_of_epi _ _ _ _ _ (((geomPtAt x).stalkF Λ).map
      (biprod.inl : openCut Λ U F ⟶ openCut Λ U F ⊞ openCut Λ V F)) _ (IsIso.epi_of_iso _)
  · have : IsIso (((geomPtAt x).stalkF Λ).map (biprod.inr : openCut Λ V F ⟶ openCut Λ U F ⊞ openCut Λ V F) ≫
        ((geomPtAt x).stalkF Λ).map (biprod.desc (openCutι Λ U F) (openCutι Λ V F))) := by
      rw [← CategoryTheory.Functor.map_comp, biprod.inr_desc]
      exact isIso_stalk_openCutι V F _ (mem_center_geomPtAt hx)
    exact @epi_of_epi _ _ _ _ _ (((geomPtAt x).stalkF Λ).map
      (biprod.inr : openCut Λ V F ⟶ openCut Λ U F ⊞ openCut Λ V F)) _ (IsIso.epi_of_iso _)

end Glue

section Scalar

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

end Scalar

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_MVSplit =====
section

/-!
# S4-EtCompact, part 32: `H^1` vanishes when it vanishes on two affine charts (O8b, file 2)

* `smulEnd_comp`, `res_map_smulEnd`: scalars commute with all maps and with restriction.
* `openCut_unitSh_ext`: on a connected nonempty open `W`, every `j_{W!}Λ|_W ⟶ Λ_X` is `ι ≫ (r • ·)`.
* `splits_of_cover`: a short exact sequence that splits over `U` and over `V` (with the overlap
  extension property) splits.
* **`subsingleton_h1_of_cover`**: if `X = U ∪ V` (open immersions `j_U, j_V`), `U ∩ V` is connected and
  nonempty, and `H^1(U, Λ) = H^1(V, Λ) = 0`, then `H^1(X, Λ) = 0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Scal

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- `j^* Λ_X ≅ Λ_Y` for an open immersion `j : Y ⟶ X`. -/
def resUnitIsoOf {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    (res j Λ).obj (unitSh Λ X) ≅ unitSh Λ Y :=
  ((pullIsoRes j Λ).app _).symm ≪≫ pullConst Λ j (ModuleCat.of Λ Λ)

end Scal

section Split

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end Split

section Charts

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

end Charts

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_P1Cover =====
section

/-!
# S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)

* `dehom' = dehom ∘ swap` (`X₁ ↦ 1`, `X₀ ↦ t`), `awayDehom' : K[X₀, X₁]_(X₁) ≃ K[t]`, the chart
  `chartA1' : A^1_K ⟶ P^1_K` (`t ↦ [t : 1]`) with range `D₊(X₁)`.
* `P1.cover`: the two charts cover `P^1`; their overlap is nonempty and connected (`P^1` irreducible).
* **`P1.subsingleton_h1`**: `H^1(A^1, Λ) = 0 ⇒ H^1(P^1, Λ) = 0` (`subsingleton_h1_of_cover`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves

universe u

section Chart1

variable {K : Type u} [Field K]

theorem isUnit_dehom'_X1 :
    IsUnit (((dehom' : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K) : MvPolynomial (Fin 2) K →+* Polynomial K)
      (X 1)) := by
  rw [AlgHom.coe_toRingHom, dehom'_X1]
  exact isUnit_one

/-- `K[X₀, X₁]_(X₁) → K[t]`, induced by `dehom'`. -/
def awayDehom' : Away (homogeneousSubmodule (Fin 2) K) (X 1 : MvPolynomial (Fin 2) K) →+* Polynomial K :=
  (Localization.awayLift ((dehom' : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K) :
      MvPolynomial (Fin 2) K →+* Polynomial K) (X 1) isUnit_dehom'_X1).comp
    (algebraMap (Away (homogeneousSubmodule (Fin 2) K) (X 1 : MvPolynomial (Fin 2) K))
      (Localization.Away (X 1 : MvPolynomial (Fin 2) K)))

theorem awayDehom'_mk (n : ℕ) (a : MvPolynomial (Fin 2) K)
    (ha : a ∈ homogeneousSubmodule (Fin 2) K (n • 1)) :
    awayDehom' (Away.mk (homogeneousSubmodule (Fin 2) K) (P1.X_mem K 1) n a ha) = dehom' a := by
  rw [awayDehom', RingHom.comp_apply]
  change Localization.awayLift _ _ _
    (Away.mk (homogeneousSubmodule (Fin 2) K) (P1.X_mem K 1) n a ha).val = _
  rw [Away.val_mk, Localization.awayLift_mk _ (X 1) a 1 (by rw [AlgHom.coe_toRingHom, dehom'_X1, one_mul]) n]
  simp

theorem awayDehom'_injective : Function.Injective (awayDehom' (K := K)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (homogeneousSubmodule (Fin 2) K) (P1.X_mem K 1) x
  rw [awayDehom'_mk] at hx
  have ha' : a.IsHomogeneous n := by simpa [mem_homogeneousSubmodule] using ha
  obtain rfl := eq_zero_of_dehom' ha' hx
  ext
  rw [Away.val_mk, val_zero]
  exact Localization.mk_zero _

theorem awayDehom'_surjective : Function.Surjective (awayDehom' (K := K)) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    exact ⟨x + y, map_add _ _ _⟩
  | monomial n c =>
    have hmem : (C c * X 0 ^ n : MvPolynomial (Fin 2) K) ∈ homogeneousSubmodule (Fin 2) K (n • 1) := by
      rw [smul_eq_mul, mul_one, mem_homogeneousSubmodule]
      exact isHomogeneous_C_mul_X_pow c 0 n
    refine ⟨Away.mk (homogeneousSubmodule (Fin 2) K) (P1.X_mem K 1) n _ hmem, ?_⟩
    rw [awayDehom'_mk, map_mul, map_pow, dehom'_X0, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp [dehom']

instance isIso_ofHom_awayDehom' : IsIso (CommRingCat.ofHom (awayDehom' (K := K))) :=
  (RingEquiv.toCommRingCatIso
    (RingEquiv.ofBijective awayDehom' ⟨awayDehom'_injective, awayDehom'_surjective⟩)).isIso_hom

variable (K) in
/-- **The second chart `A^1_K ⟶ P^1_K`** (`t ↦ [t : 1]`). -/
def chartA1' : A1 K ⟶ P1 K :=
  Spec.map (CommRingCat.ofHom (awayDehom' (K := K))) ≫
    Proj.awayι (homogeneousSubmodule (Fin 2) K) (X 1) (P1.X_mem K 1) one_pos

instance isOpenImmersion_chartA1' : IsOpenImmersion (chartA1' K) := by
  unfold chartA1'
  infer_instance

end Chart1

section Cover

variable (K : Type u) [Field K]

theorem P1.opensRange_chartA1' :
    (chartA1' K).opensRange = Proj.basicOpen (homogeneousSubmodule (Fin 2) K) (X 1) :=
  (Scheme.Hom.opensRange_comp_of_isIso (Spec.map (CommRingCat.ofHom (awayDehom' (K := K)))) _).trans
    (Proj.opensRange_awayι ..)

theorem P1.mem_range_chartA1'_iff (x : P1 K) :
    x ∈ (chartA1' K).opensRange ↔ (X 1 : MvPolynomial (Fin 2) K) ∉ x.asHomogeneousIdeal := by
  rw [P1.opensRange_chartA1', Proj.mem_basicOpen]

/-- **The two charts cover `P^1`.** -/
theorem P1.cover (x : P1 K) : x ∈ (chartA1 K).opensRange ∨ x ∈ (chartA1' K).opensRange := by
  by_cases h : x = P1.infPt K
  · right
    rw [P1.mem_range_chartA1'_iff, h]
    exact P1.X1_not_mem K _ (P1.X0_mem_infPt K)
  · left
    exact (P1.mem_range_chartA1_iff K x).2 h

end Cover

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_H1 =====
section

/-!
# S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`

* `isRepExt_fibRep`: the generic stalk of `0 → G → P → Λ_X → 0` (`G`, `P` lisse) is an extension of
  `π₁`-representations;
* **`exists_kappa_eq`**: `κ` is surjective (write `e` as the class of a short exact sequence, its middle term is lisse
  by `isLisse_of_ext`, its generic stalk gives the cocycle);
* `kappaZ : Z¹ →+ H¹`, with kernel the coboundaries;
* **`h1Equiv A K hG : H Λ G 1 ≃+ CurveCoh.H1 (fibRep G) ⊤`**, with `h1Equiv_symm_mk`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr RamanujanPetersson.EtSheaves.TorSec

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

variable [IsNoetherianRing A]

section Z1

variable {A K} {G : EtSh Λ (Spec (CommRingCat.of A))} {hG : IsLisse Λ G}

end Z1

variable {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)

/-- `κ` on `Z¹(π₁, G_η̄)`, as an additive map. -/
def kappaZ : CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤ →+ H Λ G 1 :=
  AddMonoidHom.mk' (fun z => kappa A K hG (cz z) (isCocycle_cz z) (isLocallyConstant_cz z)) fun z₁ z₂ =>
    kappa_add A K hG _ _ _ _ _ _ fun _ => rfl

theorem kappaZ_apply (z : CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤) :
    kappaZ A K hG z = kappa A K hG (cz z) (isCocycle_cz z) (isLocallyConstant_cz z) := rfl

theorem kappaZ_eq_zero_iff (z : CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤) :
    kappaZ A K hG z = 0 ↔ z ∈ (CurveCoh.B1 (EssSurj.fibRep A K G hG) ⊤).comap
      (CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤).subtype := by
  rw [kappaZ_apply, Submodule.mem_comap, Submodule.subtype_apply, CurveCoh.mem_B1]
  constructor
  · intro h
    obtain ⟨m₀, hm⟩ := exists_coboundary_of_kappa_eq_zero A K hG _ _ h
    exact ⟨z.2, m₀, fun g => hm g.1⟩
  · rintro ⟨-, m₀, hm⟩
    exact kappa_coboundary A K hG _ _ m₀ fun τ => hm ⟨τ, Subgroup.mem_top τ⟩

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_A1Kum =====
section

/-!
# S4-EtCompact, part 34: `H^1(A^1_k, Λ) = 0` for `k` algebraically closed (O8b, file 4)

`A = k[X]`, `K = Frac A`, `K_U = maxUnram A K`, `π₁ = Pi1 A K`, `N` invertible in `k`.

* `dvd_ord_of_unram0`: for a UFD `R` and `L ∈ unramSet R K`, an `N`-th root `α ∈ L` of `a ∈ Kˣ` forces
  `N ∣ ord_π(den a) - ord_π(num a)` at every prime `π` (level-`0` form of `EtPi1.dvd_ord_of_unram`).
* `fixed_of_pow_fixed`: if `α ∈ K_U` and `α ^ N ∈ K`, then `α ∈ K` (units of `k[X]` are `N`-th powers, roots of unity
  lie in `k`).
* `hom_eq_zero_A1`, `hom_eq_zero_A1_tors`: every locally constant homomorphism `π₁ → V`, `N • V = 0`, vanishes
  (Kummer: `exists_kchar_eq`; finite image + characters).
* **`A1.subsingleton_h1`**: `H^1(A^1_k, Λ) = 0` when `N • Λ = 0`, `(N : k) ≠ 0` (`h1Equiv`).
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr Kummer EtPi1

section Ord0

variable {R K : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Orders of `N`-th powers at level `0`.** -/
theorem dvd_ord_of_unram0 {L : IntermediateField K (AlgebraicClosure K)} (hL : L ∈ unramSet R K)
    {N : ℕ} {α : AlgebraicClosure K} (hαL : α ∈ L) {a : K}
    (ha : α ^ N = algebraMap K (AlgebraicClosure K) a) (ha0 : a ≠ 0) (π : R) (hπ : Prime π) :
    (N : ℤ) ∣ (multiplicity π (IsFractionRing.den R a : R) : ℤ) - multiplicity π (IsFractionRing.num R a) := by
  have : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  let D : Subalgebra R K :=
    Localization.subalgebra.ofField K (Ideal.span {π}).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  have : IsLocalization.AtPrime D (Ideal.span {π}) := Localization.subalgebra.isLocalization_ofField K _ _
  have : IsFractionRing D K := Localization.subalgebra.isFractionRing_ofField K _ _
  have : IsLocalRing D := IsLocalization.AtPrime.isLocalRing D (Ideal.span {π})
  have : IsDedekindDomain D := isDedekindDomain_atPrime π D
  let _ : Algebra D L := ((algebraMap K L).comp (algebraMap D K)).toAlgebra
  have : @IsScalarTower D K L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : @IsScalarTower R D L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional K L := hL.1
  have : IsGalois K L := hL.2.1
  have hI : InertiaTrivial D K L := fun Q hQ => inertia_eq_bot_of_unramSet hL Q hQ
  have hαN : (⟨α, hαL⟩ : L) ^ N = algebraMap K L a := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact ha
  have h := dvd_log_valuation_of_inertia D K L hI hαN (place π D hπ.ne_zero)
  rwa [log_valuation_place π D K hπ.ne_zero ha0] at h

end Ord0

section Kum

variable {k : Type} [Field k] [IsAlgClosed k] {K : Type} [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]

/-- **`α ∈ K_U` with `α ^ N ∈ K` lies in `K`** (`k` algebraically closed, `N` invertible). -/
theorem fixed_of_pow_fixed {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (α : maxUnram k[X] K) (hα0 : α ≠ 0)
    (hα : ∀ σ : Pi1 k[X] K, σ (α ^ N) = α ^ N) (σ : Pi1 k[X] K) : σ α = α := by
  obtain ⟨a, ha'⟩ := (InfiniteGalois.mem_bot_iff_fixed (k := K) (K := maxUnram k[X] K) (α ^ N)).2 hα
  have ha : algebraMap K (maxUnram k[X] K) a = α ^ N := ha'
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact hα0 ((pow_eq_zero_iff (NeZero.ne N)).1 ha.symm)
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite (A := k[X]) (K := K) {(α : AlgebraicClosure K)}
    (fun x hx => by rw [Finset.mem_singleton] at hx; exact hx ▸ α.2)
  have hαL : (α : AlgebraicClosure K) ∈ L :=
    hle (IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 (Finset.mem_singleton_self _)))
  have haN : (α : AlgebraicClosure K) ^ N = algebraMap K (AlgebraicClosure K) a := by
    rw [← IntermediateField.coe_pow, ← ha]
    rfl
  have hdvd := fun π hπ => dvd_ord_of_unram0 hL hαL haN ha0 π hπ
  obtain ⟨u, b, hab⟩ := exists_eq_unit_mul_pow (R := k[X]) K ha0 hdvd
  obtain ⟨c, -, hcu⟩ := Polynomial.isUnit_iff.1 u.isUnit
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (NeZero.pos N)
  have hβN : a = (algebraMap k[X] K (C d) * b) ^ N := by
    rw [hab, mul_pow, ← map_pow, ← C_pow, hd, hcu]
  have hβ0 : algebraMap k[X] K (C d) * b ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne N)] at hβN
    exact ha0 hβN
  have hβ0' : algebraMap K (maxUnram k[X] K) (algebraMap k[X] K (C d) * b) ≠ 0 := (_root_.map_ne_zero _).2 hβ0
  have hγ : (α / algebraMap K (maxUnram k[X] K) (algebraMap k[X] K (C d) * b)) ^ N = 1 := by
    rw [div_pow, ← ha, hβN, map_pow, div_self (pow_ne_zero N hβ0')]
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_ne hN
  obtain ⟨i, -, hi⟩ := (isPrimitiveRoot_image K hζ).eq_pow_of_pow_eq_one hγ
  have hαe : α = algebraMap K (maxUnram k[X] K)
      ((algebraMap k[X] K (C ζ)) ^ i * (algebraMap k[X] K (C d) * b)) := by
    rw [map_mul, map_pow, hi, div_mul_cancel₀ _ hβ0']
  rw [hαe, AlgEquiv.commutes]

/-- **Locally constant homomorphisms `π₁(A^1_k) → ℤ/N` vanish.** -/
theorem hom_eq_zero_A1 {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0)
    (c : (⊤ : Subgroup (Pi1 k[X] K)) → ZMod N) (hc : IsLocallyConstant c)
    (hadd : ∀ σ τ, c (σ * τ) = c σ + c τ) : c = 0 := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_ne hN
  have hζE := isPrimitiveRoot_image K hζ
  have hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 k[X] K)),
      σ (algebraMap K (maxUnram k[X] K) (algebraMap k[X] K (C ζ))) =
        algebraMap K (maxUnram k[X] K) (algebraMap k[X] K (C ζ)) := fun σ _ => AlgEquiv.commutes σ _
  obtain ⟨α, hα, hαc⟩ := exists_kchar_eq hζE hζΓ c hc hadd
  have hfix : α ∈ fixUnits (⊤ : Subgroup (Pi1 k[X] K)) := fun σ _ =>
    fixed_of_pow_fixed hN (α : maxUnram k[X] K) α.ne_zero (fun τ => hα τ (Subgroup.mem_top τ)) σ
  have h0 := (kchar_eq_zero_iff hζE hα).2 hfix
  funext σ
  rw [← hαc σ, h0 σ]
  rfl

/-- Finite coefficients killed by `N`. -/
theorem hom_eq_zero_A1_fin {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) {M : Type} [AddCommGroup M] [Finite M]
    (hM : ∀ x : M, N • x = 0) (c : (⊤ : Subgroup (Pi1 k[X] K)) → M) (hlc : IsLocallyConstant c)
    (hadd : ∀ g h, c (g * h) = c g + c h) : c = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hpow : ∀ (ψ : AddChar M ℂ) (x : M), ψ x ^ N = 1 := fun ψ x => by
    rw [← AddChar.map_nsmul_eq_pow, hM, AddChar.map_zero_eq_one]
  funext g
  refine AddChar.forall_apply_eq_zero.1 fun ψ => ?_
  have h := hom_eq_zero_A1 (K := K) hN (fun γ => dlog hζ (ψ (c γ)))
    (hlc.comp fun x => dlog hζ (ψ x)) (fun γ δ => by
      rw [hadd, AddChar.map_add_eq_mul, dlog_mul' hζ (hpow ψ _) (hpow ψ _)])
  have hg := congrFun h g
  simp only [Pi.zero_apply] at hg
  rw [← epow_dlog hζ (hpow ψ (c g)), hg]
  simp [epow]

/-- **Locally constant homomorphisms `π₁(A^1_k) → V` vanish** for any `V` killed by `N`. -/
theorem hom_eq_zero_A1_tors {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) {V : Type} [AddCommGroup V]
    (hV : ∀ v : V, N • v = 0) (c : (⊤ : Subgroup (Pi1 k[X] K)) → V) (hlc : IsLocallyConstant c)
    (hadd : ∀ g h, c (g * h) = c g + c h) : c = 0 := by
  have hc1 : c 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    exact left_eq_add.1 h
  have hcinv : ∀ σ, c σ⁻¹ = -c σ := fun σ => by
    have h := hadd σ⁻¹ σ
    rw [inv_mul_cancel, hc1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  haveI : CompactSpace (⊤ : Subgroup (Pi1 k[X] K)) :=
    isCompact_iff_compactSpace.1 (by rw [Subgroup.coe_top]; exact isCompact_univ)
  let M : AddSubgroup V :=
    { carrier := Set.range c
      add_mem' := by
        rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
        exact ⟨σ * τ, hadd σ τ⟩
      zero_mem' := ⟨1, hc1⟩
      neg_mem' := by
        rintro _ ⟨σ, rfl⟩
        exact ⟨σ⁻¹, hcinv σ⟩ }
  haveI : Finite M := (hlc.range_finite).to_subtype
  let c' : (⊤ : Subgroup (Pi1 k[X] K)) → M := fun σ => ⟨c σ, σ, rfl⟩
  have hlc' : IsLocallyConstant c' := IsLocallyConstant.desc c' Subtype.val hlc Subtype.val_injective
  have h0 := hom_eq_zero_A1_fin (K := K) hN (M := M) (fun x => Subtype.ext (hV x.1)) c' hlc'
    (fun g h => Subtype.ext (hadd g h))
  funext σ
  exact congrArg Subtype.val (congrFun h0 σ)

end Kum

section H1

variable (k : Type) [Field k] [IsAlgClosed k] (K : Type) [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]

/-- `H^1_cont(π₁(A^1_k), Λ) = 0`. -/
theorem curveH1_unitSh_subsingleton {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0)
    (hΛ : (N : Λ) = 0) :
    Subsingleton (CurveCoh.H1 (EssSurj.fibRep k[X] K (unitSh Λ (Spec (CommRingCat.of k[X]))) isLisse_unitSh)
      ⊤) := by
  suffices h : ∀ x : CurveCoh.H1 (EssSurj.fibRep k[X] K (unitSh Λ (Spec (CommRingCat.of k[X])))
      isLisse_unitSh) ⊤, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  have hz := (CurveCoh.mem_Z1 _ _ _).1 z.2
  have h0 : z.1 = 0 := by
    refine hom_eq_zero_A1_tors (K := K) hN ?_ _ hz.1 ?_
    · intro v
      rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
    · intro g h
      rw [hz.2, fibRep_unitSh, LinearMap.id_apply]
  have hz0 : z = 0 := Subtype.ext h0
  rw [hz0, map_zero]

end H1

end RamanujanPetersson.EtCompact

end

end


