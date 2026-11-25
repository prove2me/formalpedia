-- Prove2me | Definitions.Def_RPLib_FX_EtP1_07
-- name    : RPLib_FX_EtP1_07
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:42:02.29491+00:00
-- url     : https://prove2.me/theorems/a691b099-f9e5-4fd4-aa56-6dffce6f4004
-- title:
--   Étale cohomology of the projective line, library file 07 of 34
-- statement:
--   File 07 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_Bridge`: S4-EtCompact, O9b part 6: `κ` is additive, kills coboundaries and is injective on `H¹`
--   * `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
--   * `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
--   * `S4.Def_RP_EtCompact_A1Kum`: S4-EtCompact, part 34: `H^1(A^1_k, Λ) = 0` for `k` algebraically closed (O8b, file 4)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_06

/-!
# Étale cohomology of the projective line, library file 07 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_Bridge`: S4-EtCompact, O9b part 6: `κ` is additive, kills coboundaries and is injective on `H¹`
* `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
* `S4.Def_RP_EtCompact_H1`: S4-EtCompact, O9b part 7: `H¹(Spec A, G) ≃ H¹_cont(π₁, G_η̄)` for lisse `G`
* `S4.Def_RP_EtCompact_A1Kum`: S4-EtCompact, part 34: `H^1(A^1_k, Λ) = 0` for `k` algebraically closed (O8b, file 4)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_Bridge =====
section

/-!
# S4-EtCompact, O9b part 6: `κ` is additive, kills coboundaries and is injective on `H¹`

* `fibRep_natural`: stalk maps intertwine the fibre representations;
* `kappa_comp` (naturality), **`kappa_add`**, `kappa_zero`, **`kappa_coboundary`** (`κ(dm) = 0`);
* **`exists_coboundary_of_kappa_eq_zero`**: `κ(c) = 0` only for coboundaries.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr RamanujanPetersson.EtSheaves.TorSec

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

variable [IsNoetherianRing A]

/-- **`κ` is additive.** -/
theorem kappa_add {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    {c₁ c₂ c₃ : Pi1 A K → stalk Λ G (genPt A)}
    (hc₁ : IsCocycle (EssSurj.fibRep A K G hG) c₁) (hcl₁ : IsLocallyConstant c₁)
    (hc₂ : IsCocycle (EssSurj.fibRep A K G hG) c₂) (hcl₂ : IsLocallyConstant c₂)
    (hc₃ : IsCocycle (EssSurj.fibRep A K G hG) c₃) (hcl₃ : IsLocallyConstant c₃) (h : ∀ τ, c₃ τ = c₁ τ + c₂ τ) :
    kappa A K hG c₃ hc₃ hcl₃ = kappa A K hG c₁ hc₁ hcl₁ + kappa A K hG c₂ hc₂ hcl₂ := by
  have hGG := IsLisse.biprod' hG hG
  obtain ⟨c, hcdef⟩ : ∃ c : Pi1 A K → stalk Λ (G ⊞ G) (genPt A),
      ∀ τ, c τ = gs A biprod.inl (c₁ τ) + gs A biprod.inr (c₂ τ) := ⟨_, fun _ => rfl⟩
  have hcc : IsCocycle (EssSurj.fibRep A K (G ⊞ G) hGG) c := by
    intro g g'
    simp only [hcdef, hc₁ g g', hc₂ g g', map_add, fibRep_natural A K hG hGG]
    abel
  have hccl : IsLocallyConstant c := by
    rw [show c = (gs A biprod.inl ∘ c₁) + (gs A biprod.inr ∘ c₂) from funext hcdef]
    exact (hcl₁.comp _).add (hcl₂.comp _)
  rw [← kappa_comp A K hGG hG hcc hccl hc₃ hcl₃ (biprod.fst + biprod.snd) ?_,
    ← kappa_comp A K hGG hG hcc hccl hc₁ hcl₁ biprod.fst ?_, ← kappa_comp A K hGG hG hcc hccl hc₂ hcl₂ biprod.snd ?_,
    Abelian.Ext.mk₀_add, Abelian.Ext.comp_add]
  -- side goals come in reverse order (snd, fst, fst + snd)
  · intro τ
    rw [hcdef, map_add, ← gs_comp_apply, ← gs_comp_apply, biprod.inl_snd, biprod.inr_snd, gs_id_apply,
      gs_zero_apply, zero_add]
  · intro τ
    rw [hcdef, map_add, ← gs_comp_apply, ← gs_comp_apply, biprod.inl_fst, biprod.inr_fst, gs_id_apply,
      gs_zero_apply, add_zero]
  · intro τ
    rw [hcdef, gs_add_apply, map_add, map_add, ← gs_comp_apply, ← gs_comp_apply, ← gs_comp_apply, ← gs_comp_apply,
      biprod.inl_fst, biprod.inr_fst, biprod.inl_snd, biprod.inr_snd, gs_id_apply, gs_id_apply, gs_zero_apply,
      gs_zero_apply, add_zero, zero_add, h]

theorem kappa_zero {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    (hc : IsCocycle (EssSurj.fibRep A K G hG) 0) (hcl : IsLocallyConstant (0 : Pi1 A K → stalk Λ G (genPt A))) :
    kappa A K hG 0 hc hcl = 0 := by
  have h := kappa_add A K hG hc hcl hc hcl hc hcl (fun _ => (add_zero 0).symm)
  calc kappa A K hG 0 hc hcl = (kappa A K hG 0 hc hcl + kappa A K hG 0 hc hcl) - kappa A K hG 0 hc hcl := by abel
    _ = kappa A K hG 0 hc hcl - kappa A K hG 0 hc hcl := by rw [← h]
    _ = 0 := sub_self _

/-- **`κ` kills coboundaries.** -/
theorem kappa_coboundary {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    {c : Pi1 A K → stalk Λ G (genPt A)} (hc : IsCocycle (EssSurj.fibRep A K G hG) c) (hcl : IsLocallyConstant c)
    (m₀ : stalk Λ G (genPt A)) (hm : ∀ τ, c τ = EssSurj.fibRep A K G hG τ m₀ - m₀) :
    kappa A K hG c hc hcl = 0 := by
  let R := Classical.choice (nonempty_realExt A K hG hc hcl)
  have hc0 : IsCocycle (EssSurj.fibRep A K G hG) (0 : Pi1 A K → stalk Λ G (genPt A)) := fun g g' => by simp
  have h0 : Realizes A K (0 : Pi1 A K → stalk Λ G (genPt A)) R.f R.g (R.w - gs A R.f m₀) := by
    constructor
    · rw [map_sub, R.real.one, ← gs_comp_apply, R.zero, gs_zero_apply, sub_zero]
    · intro σ
      have h1 := R.real.coc σ
      have h2 : galRep Λ R.P (genPt A) σ (gs A R.f m₀) = gs A R.f (galRep Λ G (genPt A) σ m₀) :=
        (LinearMap.congr_fun (galRep_natural Λ R.f (genPt A) σ) m₀).symm
      rw [hm, EssSurj.fibRep_genToPi1, map_sub, sub_eq_iff_eq_add] at h1
      rw [Pi.zero_apply, map_zero, map_sub, h2, h1]
      abel
  show R.se.extClass = 0
  rw [kappa_eq A K hG hc0 IsLocallyConstant.zero R.se h0, kappa_zero]

/-- **Injectivity of `κ` on classes**: `κ(c) = 0` only for coboundaries. -/
theorem exists_coboundary_of_kappa_eq_zero {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    {c : Pi1 A K → stalk Λ G (genPt A)} (hc : IsCocycle (EssSurj.fibRep A K G hG) c) (hcl : IsLocallyConstant c)
    (h : kappa A K hG c hc hcl = 0) :
    ∃ m₀ : stalk Λ G (genPt A), ∀ τ, c τ = EssSurj.fibRep A K G hG τ m₀ - m₀ := by
  let R := Classical.choice (nonempty_realExt A K hG hc hcl)
  obtain ⟨r, hr⟩ := (extClass_eq_zero_iff R.se).1 h
  have hR := isRepExt_stalk (genPt A) R.se
  have hw : (unitCoord Λ (genPt A) ∘ₗ gs A R.g) R.w = 1 := by
    rw [LinearMap.comp_apply, R.real.one, unitCoord_oneStalk]
  obtain ⟨m₀, hm₀⟩ := (exists_retraction_iff (galRep Λ G (genPt A)) (isCocycle_extCocycle hR R.w)).1
    ⟨gs A r ∘ₗ (extIso hR R.w hw).symm.toLinearMap, LinearMap.ext fun m => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, ← extIsoFun_i hR R.w hw m,
        ← extIso_apply, LinearEquiv.symm_apply_apply, ← gs_comp_apply, hr, gs_id_apply, LinearMap.id_apply],
      fun σ => LinearMap.ext fun y => by
      have he : (extIso hR R.w hw).symm (extRep (galRep Λ G (genPt A)) _ (isCocycle_extCocycle hR R.w) σ y) =
          galRep Λ R.P (genPt A) σ ((extIso hR R.w hw).symm y) := by
        apply (extIso hR R.w hw).injective
        rw [LinearEquiv.apply_symm_apply, extIso_apply, extIsoFun_equivariant, ← extIso_apply,
          LinearEquiv.apply_symm_apply]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [he]
      exact LinearMap.congr_fun (galRep_natural Λ r (genPt A) σ) _⟩
  refine ⟨m₀, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := genToPi1_surjective A K τ
  rw [EssSurj.fibRep_genToPi1, ← hm₀ σ]
  exact (hR.inj ((i_extCocycle hR R.w σ).trans (R.real.coc σ))).symm

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

theorem dehom'_X0 : dehom' (X 0 : MvPolynomial (Fin 2) K) = Polynomial.X := by
  simp [dehom']

theorem dehom'_X1 : dehom' (X 1 : MvPolynomial (Fin 2) K) = 1 := by
  simp [dehom']

theorem eq_zero_of_dehom' {n : ℕ} {a : MvPolynomial (Fin 2) K} (ha : a.IsHomogeneous n)
    (h0 : dehom' a = 0) : a = 0 := by
  have hs : (swapP a).IsHomogeneous n := ha.rename_isHomogeneous
  have h1 : swapP a = 0 := eq_zero_of_dehom hs h0
  exact rename_injective _ (Equiv.injective _) (h1.trans (map_zero _).symm)

end Chart1

section Cover

variable (K : Type u) [Field K]

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

theorem isLocallyConstant_cz (z : CurveCoh.Z1 (EssSurj.fibRep A K G hG) ⊤) : IsLocallyConstant (cz z) :=
  ((CurveCoh.mem_Z1 _ _ _).1 z.2).1.comp_continuous
    (continuous_id.subtype_mk fun τ => Subgroup.mem_top τ)

end Z1

variable {G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)

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

end Ord0

section Kum

variable {k : Type} [Field k] [IsAlgClosed k] {K : Type} [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]

theorem exists_primitiveRoot_of_ne {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) : ∃ ζ : k, IsPrimitiveRoot ζ N := by
  haveI : NeZero (N : k) := ⟨hN⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic N k) (degree_cyclotomic_pos N k (NeZero.pos N)).ne'
  exact ⟨ζ, (isRoot_cyclotomic_iff).1 hζ⟩

omit [IsAlgClosed k] in
variable (K) in
theorem isPrimitiveRoot_image {N : ℕ} [NeZero N] {ζ : k} (hζ : IsPrimitiveRoot ζ N) :
    IsPrimitiveRoot (algebraMap K (maxUnram k[X] K) (algebraMap k[X] K (C ζ))) N := by
  have hinj : Function.Injective ((algebraMap K (maxUnram k[X] K)).comp ((algebraMap k[X] K).comp C)) :=
    (algebraMap K (maxUnram k[X] K)).injective.comp ((IsFractionRing.injective k[X] K).comp C_injective)
  exact hζ.map_of_injective hinj

theorem dlog_mul' {E : Type} [Field E] {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N) {x y : E}
    (hx : x ^ N = 1) (hy : y ^ N = 1) : dlog hζ (x * y) = dlog hζ x + dlog hζ y :=
  epow_injective hζ (by
    rw [epow_dlog hζ (by rw [mul_pow, hx, hy, one_mul]), epow_add hζ, epow_dlog hζ hx, epow_dlog hζ hy])

end Kum

section H1

variable (k : Type) [Field k] [IsAlgClosed k] (K : Type) [Field K] [Algebra k[X] K] [IsFractionRing k[X] K]

theorem fibRep_unitSh {Λ : Type} [CommRing Λ] (τ : Pi1 k[X] K) :
    EssSurj.fibRep k[X] K (unitSh Λ (Spec (CommRingCat.of k[X]))) isLisse_unitSh τ = LinearMap.id := by
  obtain ⟨σ, rfl⟩ := genToPi1_surjective k[X] K τ
  rw [EssSurj.fibRep_genToPi1, galRep_unitSh]

end H1

end RamanujanPetersson.EtCompact

end

end


