-- Prove2me | Definitions.Def_RPLib_S4_JacDivisorsB
-- name    : RPLib_S4_JacDivisorsB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:16:34.052749+00:00
-- url     : https://prove2.me/theorems/3b7848b5-7f11-412e-b080-2165441b91b3
-- title:
--   Regular local rings: every finitely generated module has finite projective dimension
-- statement:
--   Let $R$ be a commutative ring, $x \in R$ a non-zero-divisor and $E$ an $R/(x)$-module. If $\operatorname{pd}_{R/(x)} E < n+1$ then, viewed as an $R$-module, $\operatorname{pd}_R E < n+2$. Combined with the cutting lemma for regular local rings, induction on the embedding dimension gives: if $R$ is a regular local ring then every module $M$ (in `ModuleCat R`) has finite projective dimension, i.e. $$\exists\, n,\ \operatorname{pd}_R M < n.$$ This is the easy direction of Serre's homological characterization of regular local rings.
--
--   **Formalization note.** This file is a library module (namespace `RamanujanPetersson.JacDivisors`) of a formalization of the Ramanujan-Petersson conjecture; it is the regular-local-ring part of that library. It contains definitions together with proved lemmas (no `sorry`), stated with Mathlib's `IsRegularLocalRing`, `Ideal.spanFinrank` and the categorical `HasProjectiveDimensionLT` on `ModuleCat`, so that later solution files can import them.
-- source:
--   H. Matsumura, Commutative Ring Theory, Cambridge Stud. Adv. Math. 8, Cambridge University Press 1986, doi:10.1017/CBO9781139171762, Lemma 19.1 and Theorem 19.2; J.-P. Serre, Sur la dimension homologique des anneaux et des modules noethériens, Proc. Int. Symp. Algebraic Number Theory, Tokyo-Nikko 1955, Sci. Council Japan (1956), 175-189

import Mathlib
import Definitions.Def_RPLib_S4_JacDivisorsA

/-!
# S4-JacDivisors B (O3b, O5): change of rings and Serre's easy direction
* `hasPDLT_restrict`: if `x` is `R`-regular and `E` is an `R ⧸ (x)`-module with `pd < n + 1`, then
  `pd_R E < n + 2`.
* `exists_hasPDLT_of_isRegularLocalRing`: over a regular local ring every finite module has finite
  projective dimension.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R]

/-- Restriction of `ModuleCat.of (R ⧸ I) M` along `R → R ⧸ I`, for compatible actions. -/
noncomputable def restrictOfIso (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]
    [Module (R ⧸ I) M] (h : ∀ (r : R) (m : M), Ideal.Quotient.mk I r • m = r • m) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) M) ≅
      ModuleCat.of R M :=
  let e : ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) M)) ≃ₗ[R] M :=
    { toFun := fun m => m
      invFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => h r m
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  e.toModuleIso

theorem isSMulRegular_finsupp {x : R} (hx : IsSMulRegular R x) (ι : Type u) :
    IsSMulRegular (ι →₀ R) x := fun f g h => Finsupp.ext fun i => hx (by
  simpa using DFunLike.congr_fun h i)

theorem ker_mapRange_mkQ (x : R) (ι : Type u) :
    LinearMap.ker (Finsupp.mapRange.linearMap (Submodule.mkQ (span {x})) :
      (ι →₀ R) →ₗ[R] (ι →₀ R ⧸ span {x})) = x • (⊤ : Submodule R (ι →₀ R)) := by
  rw [Finsupp.ker_mapRange, Submodule.ker_mkQ, ← (span {x}).mul_top, ← smul_eq_mul,
    Finsupp.submodule_smul]
  simp [Submodule.ideal_span_singleton_smul]

/-- `(R/x)^(ι)` has projective dimension `< 2` over `R` when `x` is `R`-regular. -/
theorem hasPDLT_restrict_finsupp {x : R} (hx : IsSMulRegular R x) (ι : Type u) :
    HasProjectiveDimensionLT ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x}))).obj
      (ModuleCat.of (R ⧸ span {x}) (ι →₀ R ⧸ span {x}))) 2 := by
  have hS : (ModuleCat.smulShortComplex (ModuleCat.of R (ι →₀ R)) x).ShortExact :=
    IsSMulRegular.smulShortComplex_shortExact (isSMulRegular_finsupp hx ι)
  have : Projective (ModuleCat.of R (ι →₀ R)) :=
    ModuleCat.projective_of_free Finsupp.basisSingleOne
  have h3 : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x (ι →₀ R))) 2 :=
    hS.hasProjectiveDimensionLT_X₃ 1
      (inferInstance : HasProjectiveDimensionLT (ModuleCat.of R (ι →₀ R)) 1)
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R (ι →₀ R)) 1 2 (by norm_num))
  let e : QuotSMulTop x (ι →₀ R) ≃ₗ[R] (ι →₀ R ⧸ span {x}) :=
    (Submodule.quotEquivOfEq _ _ (ker_mapRange_mkQ x ι).symm).trans
      (LinearMap.quotKerEquivOfSurjective (Finsupp.mapRange.linearMap (Submodule.mkQ (span {x})))
        (by exact Finsupp.mapRange_surjective _ (map_zero _) (Submodule.mkQ_surjective (span {x}))))
  have := hasProjectiveDimensionLT_of_iso e.toModuleIso 2
  exact hasProjectiveDimensionLT_of_iso (restrictOfIso (span {x}) (ι →₀ R ⧸ span {x})
    (fun r f => by rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul])).symm 2

/-- O3b: `pd_R E ≤ pd_{R/x} E + 1` for an `R ⧸ (x)`-module `E`, when `x` is `R`-regular. -/
theorem hasPDLT_restrict {x : R} (hx : IsSMulRegular R x) : ∀ (n : ℕ)
    (E : ModuleCat.{u} (R ⧸ span {x})), HasProjectiveDimensionLT E (n + 1) →
      HasProjectiveDimensionLT
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x}))).obj E) (n + 2) := by
  intro n
  induction n with
  | zero =>
    intro E hE
    have : Projective E := projective_iff_hasProjectiveDimensionLT_one.mpr hE
    let p : ModuleCat.of (R ⧸ span {x}) (E →₀ R ⧸ span {x}) ⟶ E :=
      ModuleCat.ofHom (Finsupp.linearCombination _ id)
    have : Epi p := (ModuleCat.epi_iff_surjective _).mpr
      (fun e => ⟨Finsupp.single e 1, by simp [p]⟩)
    let rt : Retract E (ModuleCat.of (R ⧸ span {x}) (E →₀ R ⧸ span {x})) :=
      ⟨Projective.factorThru (𝟙 E) p, p, Projective.factorThru_comp _ _⟩
    have := hasPDLT_restrict_finsupp hx E
    exact (rt.map (ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x})))).hasProjectiveDimensionLT 2
  | succ n ih =>
    intro E hE
    let f : (E →₀ R ⧸ span {x}) →ₗ[R ⧸ span {x}] E := Finsupp.linearCombination _ id
    have surj : Function.Surjective f := fun e => ⟨Finsupp.single e 1, by simp [f]⟩
    have hS := LinearMap.shortExact_shortComplexKer surj
    have : Projective (ModuleCat.of (R ⧸ span {x}) (E →₀ R ⧸ span {x})) :=
      ModuleCat.projective_of_free Finsupp.basisSingleOne
    have hK := (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hE
    have hS' := hS.map_of_exact (ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x})))
    have := hasPDLT_restrict_finsupp hx E
    exact hS'.hasProjectiveDimensionLT_X₃ (n + 2) (ih _ hK)
      (hasProjectiveDimensionLT_of_ge ((ModuleCat.restrictScalars (Ideal.Quotient.mk (span {x}))).obj
        (ModuleCat.of (R ⧸ span {x}) (E →₀ R ⧸ span {x}))) 2 (n + 3) (by omega))

/-- `x ∈ m \ m²` exists when `m` needs at least one generator. -/
theorem exists_mem_maximalIdeal_not_mem_sq [IsLocalRing R] [IsNoetherianRing R]
    (h : (maximalIdeal R).spanFinrank ≠ 0) : ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 := by
  refine SetLike.not_le_iff_exists.mp fun hle => h ?_
  have hb : maximalIdeal R = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
    (maximalIdeal R).fg_of_isNoetherianRing (by rwa [pow_two] at hle)
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  rw [hb, Submodule.spanFinrank_bot]

/-- O5 (Serre, easy direction): over a regular local ring every finite module has finite
projective dimension (induction on the number of generators of `m`). -/
theorem exists_hasPDLT_of_spanFinrank : ∀ (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
    (maximalIdeal R).spanFinrank = d → ∀ (M : ModuleCat.{u} R), Module.Finite R M →
      ∃ n : ℕ, HasProjectiveDimensionLT M n := by
  intro d
  induction d with
  | zero =>
    intro R _ _ h M _
    have hb : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp h
    let := ((isField_iff_maximalIdeal_eq).mpr hb).toField
    have : Module.Free R M := Module.Free.of_divisionRing R M
    have : Projective M := ModuleCat.projective_of_free (Module.Free.chooseBasis R M)
    exact ⟨1, inferInstance⟩
  | succ d ih =>
    intro R _ _ h M _
    obtain ⟨x, hx, hx2⟩ := exists_mem_maximalIdeal_not_mem_sq (R := R) (by omega)
    have : IsLocalRing (R ⧸ span {x}) := isLocalRing_quotient_span hx
    obtain ⟨hreg, hcard⟩ := isRegularLocalRing_quotient hx hx2
    have := hreg
    have hx0 : x ≠ 0 := fun h0 => hx2 (h0 ▸ zero_mem _)
    have hxR : IsSMulRegular R x := IsSMulRegular.of_ne_zero hx0
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have hxK : IsSMulRegular (LinearMap.ker f) x := IsSMulRegular.of_ne_zero hx0
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x (LinearMap.ker f)) :=
      Module.Finite.of_restrictScalars_finite R _ _
    obtain ⟨m, hm⟩ := ih (R ⧸ span {x}) (by omega)
      (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x (LinearMap.ker f))) inferInstance
    have h1 : HasProjectiveDimensionLT
        (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x (LinearMap.ker f))) (m + 1) :=
      hasProjectiveDimensionLT_of_ge _ m (m + 1) (by omega)
    have := hasPDLT_restrict hxR m _ h1
    have h3 : HasProjectiveDimensionLT (ModuleCat.of R (QuotSMulTop x (LinearMap.ker f))) (m + 2) :=
      hasProjectiveDimensionLT_of_iso (restrictOfIso (span {x}) (QuotSMulTop x (LinearMap.ker f))
        (fun r q => Module.IsTorsionBy.mk_smul (Module.isTorsionBy_quotient_element_smul _ x) r q)) _
    have h3' := (projectiveDimension_le_iff _ (m + 1)).mpr h3
    have h4 := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R (LinearMap.ker f)) x hxK hx
    have h5 := h4.symm.trans_le h3'
    have h6 : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker f)) (m + 1) :=
      projectiveDimension_lt_iff.mp (ENat.WithBot.add_one_le_natCast_iff.mp h5)
    have : Projective (ModuleCat.of R P) := ModuleCat.projective_of_free (Module.Free.chooseBasis R P)
    exact ⟨m + 2, hS.hasProjectiveDimensionLT_X₃ (m + 1) h6
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R P) 1 (m + 2) (by omega))⟩

/-- O5: every finite module over a regular local ring has finite projective dimension. -/
theorem exists_hasPDLT_of_isRegularLocalRing [IsRegularLocalRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] : ∃ n : ℕ, HasProjectiveDimensionLT M n :=
  exists_hasPDLT_of_spanFinrank _ R rfl M inferInstance

end RamanujanPetersson.JacDivisors


