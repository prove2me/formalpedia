-- Prove2me | Definitions.Def_RPLib_FX_EtP1_05
-- name    : RPLib_FX_EtP1_05
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T01:23:10.347752+00:00
-- url     : https://prove2.me/theorems/36d1e495-a599-4c12-9d21-7d1cc315f503
-- title:
--   Étale cohomology of the projective line, library file 05 of 34
-- statement:
--   File 05 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_RepExt`: S4-EtCompact, O9b part 2: extensions of `Λ` by a representation and 1-cocycles (pure algebra)
--   * `S4.Def_RP_EtSheaves_InertiaLift`: S4-EtSheaves, O10c part 2c: lifting an inertia element to the separable closure
--   * `S4.Def_RP_EtSheaves_InertiaLift2`: S4-EtSheaves, O10c part 2d: the inertia lift
--   * `S4.Def_RP_EtSheaves_UnramKer`: S4-EtSheaves, O10c part 5a: open kernel of a lisse Galois representation; ranges of normal embeddings
--   * `S4.Def_RP_EtSheaves_UnramMain`: S4-EtSheaves, O10c part 5: the generic Galois representation of a lisse sheaf is unramified
--   * `S4.Def_RP_EtSheaves_EssSurj`: S4-EtSheaves, O10f part f: lisse sheaves on `Spec A` are their generic Galois representations
--   * `S4.Def_RP_EtCompact_H0`: S4-EtCompact, O9a: `H⁰` of a lisse sheaf on `Spec A` is the invariants of its generic stalk
--   * `S4.Def_RP_EtCompact_Ext1`: S4-EtCompact, O9b part 1: `Ext¹` classes and extensions (any abelian category)
--   * `S4.Def_RP_EtSheaves_FVMap`: S4-EtSheaves, part O10e(ii): `V ↦ F_V` is a functor, compatible with the stalk isomorphisms
--   * `S4.Def_RP_EtSheaves_FVFull`: S4-EtSheaves, part O10e(iii): `V ↦ F_V` is fully faithful
--   * `S4.Def_RP_EtCompact_FVExact`: S4-EtCompact, O9b part 3: `F_V` over one Galois cover is exact
--   * `S4.Def_RP_EtCompact_SheafExt`: S4-EtCompact, O9b part 4: comparing extensions of `Λ_X` by lisse sheaves on `Spec A`
--   * `S4.Def_RP_EtCompact_Kappa`: S4-EtCompact, O9b part 5: the extension class `κ(c) ∈ H¹(Spec A, G)` of a `π₁`-cocycle
--   * `S4.Def_RP_EtCompact_Bridge`: S4-EtCompact, O9b part 6: `κ` is additive, kills coboundaries and is injective on `H¹`
--   * `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
--   * `S4.Def_RP_PicDescent_D2`: S4-PicDescent, part D2: unramified Dedekind extensions, generic
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_04

/-!
# Étale cohomology of the projective line, library file 05 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_RepExt`: S4-EtCompact, O9b part 2: extensions of `Λ` by a representation and 1-cocycles (pure algebra)
* `S4.Def_RP_EtSheaves_InertiaLift`: S4-EtSheaves, O10c part 2c: lifting an inertia element to the separable closure
* `S4.Def_RP_EtSheaves_InertiaLift2`: S4-EtSheaves, O10c part 2d: the inertia lift
* `S4.Def_RP_EtSheaves_UnramKer`: S4-EtSheaves, O10c part 5a: open kernel of a lisse Galois representation; ranges of normal embeddings
* `S4.Def_RP_EtSheaves_UnramMain`: S4-EtSheaves, O10c part 5: the generic Galois representation of a lisse sheaf is unramified
* `S4.Def_RP_EtSheaves_EssSurj`: S4-EtSheaves, O10f part f: lisse sheaves on `Spec A` are their generic Galois representations
* `S4.Def_RP_EtCompact_H0`: S4-EtCompact, O9a: `H⁰` of a lisse sheaf on `Spec A` is the invariants of its generic stalk
* `S4.Def_RP_EtCompact_Ext1`: S4-EtCompact, O9b part 1: `Ext¹` classes and extensions (any abelian category)
* `S4.Def_RP_EtSheaves_FVMap`: S4-EtSheaves, part O10e(ii): `V ↦ F_V` is a functor, compatible with the stalk isomorphisms
* `S4.Def_RP_EtSheaves_FVFull`: S4-EtSheaves, part O10e(iii): `V ↦ F_V` is fully faithful
* `S4.Def_RP_EtCompact_FVExact`: S4-EtCompact, O9b part 3: `F_V` over one Galois cover is exact
* `S4.Def_RP_EtCompact_SheafExt`: S4-EtCompact, O9b part 4: comparing extensions of `Λ_X` by lisse sheaves on `Spec A`
* `S4.Def_RP_EtCompact_Kappa`: S4-EtCompact, O9b part 5: the extension class `κ(c) ∈ H¹(Spec A, G)` of a `π₁`-cocycle
* `S4.Def_RP_EtCompact_Bridge`: S4-EtCompact, O9b part 6: `κ` is additive, kills coboundaries and is injective on `H¹`
* `S4.Def_RP_EtCompact_P1Cover`: S4-EtCompact, part 33: the second chart of `P^1` and `H^1(P^1, Λ)` from `H^1(A^1, Λ)` (O8b, file 3)
* `S4.Def_RP_PicDescent_D2`: S4-PicDescent, part D2: unramified Dedekind extensions, generic
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_RepExt =====
section

/-!
# S4-EtCompact, O9b part 2: extensions of `Λ` by a representation and 1-cocycles (pure algebra)

For `ρ : Representation Λ G M` and a 1-cocycle `c` (`IsCocycle ρ c`):
* `extRep ρ c hc` on `M × Λ`: `g • (m, a) = (ρ g m + a • c g, a)`; `M → M × Λ → Λ` is equivariant
  (`extRep_inl`, `extRep_snd`); `isOpen_ker_extRep`: open kernel if `ρ` has open kernel and `c` is locally constant;
* `exists_retraction_iff`: an equivariant retraction of `M → M × Λ` exists iff `c` is a coboundary;
* for an extension `0 → M →ⁱ E →ᵖ Λ → 0` of representations and `w ∈ E` with `p w = 1`: `extCocycle` is a cocycle
  (`isCocycle_extCocycle`), and `extIso : E ≃ₗ M × Λ` intertwines `ρE` with `extRep` (`extIso_equivariant`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtCompact

section RepExt

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module Λ M]
  (ρ : Representation Λ G M)

variable {ρ}

theorem IsCocycle.map_one {c : G → M} (hc : IsCocycle ρ c) : c 1 = 0 := by
  have h := hc 1 1
  have h1 : ρ 1 (c 1) = c 1 := by rw [MonoidHom.map_one ρ]; rfl
  rw [one_mul, h1] at h
  calc c 1 = (c 1 + c 1) - c 1 := by abel
    _ = c 1 - c 1 := by rw [← h]
    _ = 0 := sub_self _

variable (ρ) (c : G → M)

/-- **The extension of `Λ` (trivial action) by `M` with cocycle `c`.** -/
def extRep (hc : IsCocycle ρ c) : Representation Λ G (M × Λ) where
  toFun := extRepFun ρ c
  map_one' := LinearMap.ext fun v => by
    rw [extRepFun_apply, hc.map_one, map_one, smul_zero, add_zero]
    rfl
  map_mul' g h := LinearMap.ext fun v => by
    show extRepFun ρ c (g * h) v = extRepFun ρ c g (extRepFun ρ c h v)
    rw [extRepFun_apply, extRepFun_apply, extRepFun_apply, hc g h, map_mul]
    show ((ρ g) ((ρ h) v.1) + v.2 • (c g + (ρ g) (c h)), v.2) = ((ρ g) ((ρ h) v.1 + v.2 • c h) + v.2 • c g, v.2)
    rw [map_add, map_smul, smul_add]
    congr 1
    abel

variable {c}

theorem extRep_apply (hc : IsCocycle ρ c) (g : G) (v : M × Λ) :
    extRep ρ c hc g v = (ρ g v.1 + v.2 • c g, v.2) := rfl

theorem extRep_inl (hc : IsCocycle ρ c) (g : G) (m : M) :
    extRep ρ c hc g (LinearMap.inl Λ M Λ m) = LinearMap.inl Λ M Λ (ρ g m) := by
  rw [extRep_apply]
  simp

theorem extRep_snd (hc : IsCocycle ρ c) (g : G) (v : M × Λ) :
    LinearMap.snd Λ M Λ (extRep ρ c hc g v) = LinearMap.snd Λ M Λ v := rfl

theorem isOpen_ker_extRep [TopologicalSpace G] [IsTopologicalGroup G] (hc : IsCocycle ρ c)
    (hρ : IsOpen (ρ.ker : Set G)) (hcl : IsLocallyConstant c) : IsOpen ((extRep ρ c hc).ker : Set G) := by
  have h0 : IsOpen (c ⁻¹' {0}) := hcl.isOpen_fiber 0
  have hsub : (ρ.ker : Set G) ∩ c ⁻¹' {0} ⊆ ((extRep ρ c hc).ker : Set G) := by
    rintro g ⟨hg, hg0⟩
    have hg' : ρ g = 1 := hg
    have hg0' : c g = 0 := hg0
    show extRep ρ c hc g = 1
    refine LinearMap.ext fun v => ?_
    rw [extRep_apply, hg', hg0', smul_zero, add_zero]
    rfl
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ?_ hsub)
  exact Filter.inter_mem (hρ.mem_nhds (Subgroup.one_mem _)) (h0.mem_nhds (show c 1 ∈ ({0} : Set M) from hc.map_one))

/-- **Split iff coboundary.** -/
theorem exists_retraction_iff (hc : IsCocycle ρ c) :
    (∃ r : (M × Λ) →ₗ[Λ] M, r ∘ₗ LinearMap.inl Λ M Λ = LinearMap.id ∧
      ∀ g : G, r ∘ₗ extRep ρ c hc g = ρ g ∘ₗ r) ↔ ∃ m₀ : M, ∀ g : G, c g = ρ g m₀ - m₀ := by
  constructor
  · rintro ⟨r, hr, hreq⟩
    refine ⟨r (0, 1), fun g => ?_⟩
    have h1 := LinearMap.congr_fun (hreq g) (0, 1)
    simp only [LinearMap.comp_apply, extRep_apply, map_zero, one_smul, zero_add] at h1
    have h2 : r (c g, 1) = c g + r (0, 1) := by
      have : ((c g, 1) : M × Λ) = LinearMap.inl Λ M Λ (c g) + (0, 1) := by simp
      rw [this, map_add]
      rw [← LinearMap.comp_apply r (LinearMap.inl Λ M Λ), hr, LinearMap.id_apply]
    rw [h2] at h1
    rw [← h1]
    abel
  · rintro ⟨m₀, hm₀⟩
    refine ⟨LinearMap.fst Λ M Λ + LinearMap.smulRight (LinearMap.snd Λ M Λ) m₀, ?_, fun g => ?_⟩
    · refine LinearMap.ext fun m => ?_
      simp
    · refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.smulRight_apply,
        LinearMap.snd_apply, extRep_apply, hm₀, map_add, map_smul]
      rw [smul_sub]
      abel

end RepExt

section FromExt

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module Λ M]
  {ρ : Representation Λ G M} {E : Type*} [AddCommGroup E] [Module Λ E] {ρE : Representation Λ G E}
  {i : M →ₗ[Λ] E} {p : E →ₗ[Λ] Λ}

/-- The data of an extension `0 → M → E → Λ → 0` of representations (`Λ` with the trivial action). -/
structure IsRepExt (ρ : Representation Λ G M) (ρE : Representation Λ G E) (i : M →ₗ[Λ] E) (p : E →ₗ[Λ] Λ) :
    Prop where
  inj : Function.Injective i
  exact : LinearMap.range i = LinearMap.ker p
  equiv_i : ∀ g : G, i ∘ₗ ρ g = ρE g ∘ₗ i
  equiv_p : ∀ g : G, p ∘ₗ ρE g = p

variable (h : IsRepExt ρ ρE i p) (w : E) (hw : p w = 1)

include h in
theorem IsRepExt.mem_range (g : G) : ρE g w - w ∈ LinearMap.range i := by
  rw [h.exact, LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply p (ρE g), h.equiv_p g, sub_self]

/-- The preimage under the injective `i`. -/
def IsRepExt.pre (v : LinearMap.range i) : M := (LinearEquiv.ofInjective i h.inj).symm v

theorem IsRepExt.i_pre (v : LinearMap.range i) : i (h.pre v) = v :=
  congrArg Subtype.val ((LinearEquiv.ofInjective i h.inj).apply_symm_apply v)

/-- **The cocycle of an extension**: `g ↦ i⁻¹(g w - w)`. -/
def extCocycle (g : G) : M := h.pre ⟨ρE g w - w, h.mem_range w g⟩

theorem i_extCocycle (g : G) : i (extCocycle h w g) = ρE g w - w := h.i_pre _

theorem isCocycle_extCocycle : IsCocycle ρ (extCocycle h w) := by
  intro g g'
  apply h.inj
  rw [map_add, i_extCocycle, i_extCocycle, ← LinearMap.comp_apply i (ρ g), h.equiv_i g, LinearMap.comp_apply,
    i_extCocycle, map_mul, map_sub]
  show ρE g (ρE g' w) - w = ρE g w - w + (ρE g (ρE g' w) - ρE g w)
  abel

/-- `v ↦ (i⁻¹(v - p v • w), p v)`. -/
def extIsoFun : E →ₗ[Λ] M × Λ where
  toFun v := (h.pre ⟨v - p v • w, by
    rw [h.exact, LinearMap.mem_ker, map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]⟩, p v)
  map_add' v v' := by
    refine Prod.ext (h.inj ?_) (map_add p v v')
    simp only [Prod.fst_add, map_add, h.i_pre]
    rw [add_smul]
    abel
  map_smul' a v := by
    refine Prod.ext (h.inj ?_) (by simp)
    simp only [Prod.smul_fst, map_smul, h.i_pre, RingHom.id_apply, smul_eq_mul, mul_smul, smul_sub]

theorem i_extIsoFun_fst (v : E) : i (extIsoFun h w hw v).1 = v - p v • w := h.i_pre _

theorem extIsoFun_snd (v : E) : (extIsoFun h w hw v).2 = p v := rfl

theorem extIsoFun_i (m : M) : extIsoFun h w hw (i m) = LinearMap.inl Λ M Λ m := by
  have hp : p (i m) = 0 := by
    have : i m ∈ LinearMap.ker p := h.exact ▸ LinearMap.mem_range_self i m
    exact this
  refine Prod.ext (h.inj ?_) hp
  rw [i_extIsoFun_fst, hp, zero_smul, sub_zero]
  rfl

/-- **The extension is isomorphic to `extRep` of its cocycle** (equivariantly). -/
theorem extIsoFun_equivariant (g : G) (v : E) :
    extIsoFun h w hw (ρE g v) = extRep ρ _ (isCocycle_extCocycle h w) g (extIsoFun h w hw v) := by
  have hpv : p (ρE g v) = p v := by rw [← LinearMap.comp_apply p (ρE g), h.equiv_p g]
  refine Prod.ext (h.inj ?_) hpv
  rw [i_extIsoFun_fst, extRep_apply, map_add, map_smul, i_extCocycle, extIsoFun_snd, hpv,
    ← LinearMap.comp_apply i (ρ g), h.equiv_i g, LinearMap.comp_apply, i_extIsoFun_fst, map_sub, map_smul]
  rw [smul_sub]
  abel

theorem extIsoFun_bijective : Function.Bijective (extIsoFun h w hw) := by
  refine ⟨fun v v' hv => ?_, fun x => ⟨i x.1 + x.2 • w, ?_⟩⟩
  · have h1 := congrArg (fun y => i y.1) hv
    have h2 := congrArg Prod.snd hv
    simp only [i_extIsoFun_fst, extIsoFun_snd] at h1 h2
    rw [h2] at h1
    exact sub_left_injective h1
  · have hp : p (i x.1) = 0 := by
      have : i x.1 ∈ LinearMap.ker p := h.exact ▸ LinearMap.mem_range_self i x.1
      exact this
    have hs : p (i x.1 + x.2 • w) = x.2 := by rw [map_add, hp, map_smul, hw, smul_eq_mul, mul_one, zero_add]
    refine Prod.ext (h.inj ?_) hs
    rw [i_extIsoFun_fst, hs, add_sub_cancel_right]

/-- The isomorphism `E ≃ M × Λ`. -/
def extIso : E ≃ₗ[Λ] M × Λ := LinearEquiv.ofBijective (extIsoFun h w hw) (extIsoFun_bijective h w hw)

theorem extIso_apply (v : E) : extIso h w hw v = extIsoFun h w hw v := rfl

end FromExt

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_InertiaLift =====
section

/-!
# S4-EtSheaves, O10c part 2c: lifting an inertia element to the separable closure

For a prime `𝔭` of `S = B ⊗[A] R'` over `(0)` fixed by `τ ⊗ 1`, the field `E = Frac (S ⧸ 𝔭)` is
separable over `L = Frac B` (it is generated by a simple root of `f`), and `τ ⊗ 1` induces
`τ_E ∈ Aut(E/K)`. Embedding `E` into a separably closed normal `Ω/K` and extending `τ_E` gives
`τ' ∈ Aut(Ω/K)` that fixes the image of `R'` and restricts to `τ` on `L`.
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves.InertiaLift

variable {A K L B R' : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
  [CommRing R'] [Algebra A R']

theorem algebraMap_injective (𝔭 : Ideal (B ⊗[A] R')) [𝔭.IsPrime]
    (h0 : 𝔭.comap (algebraMap B (B ⊗[A] R')) = ⊥) : Function.Injective (algebraMap B (Fld 𝔭)) := by
  rw [IsScalarTower.algebraMap_eq B (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭), RingHom.coe_comp]
  refine (IsFractionRing.injective (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭)).comp ?_
  rw [injective_iff_map_eq_zero]
  intro b hb
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem,
    ← Ideal.mem_comap, h0, Ideal.mem_bot] at hb
  exact hb

/-- The field of a branch is separable over `L`: it is generated by a simple root of `f`. -/
theorem isSeparable_frac (𝔭 : Ideal (B ⊗[A] R')) [𝔭.IsPrime] (P0 : StandardEtalePresentation A R')
    (E : Type*) [Field E] [Algebra (B ⊗[A] R' ⧸ 𝔭) E] [IsFractionRing (B ⊗[A] R' ⧸ 𝔭) E]
    [Algebra L E] [Algebra A E] [Algebra B E] [IsScalarTower A (B ⊗[A] R' ⧸ 𝔭) E]
    [IsScalarTower B (B ⊗[A] R' ⧸ 𝔭) E] [IsScalarTower B L E] [IsScalarTower A L E] :
    Algebra.IsSeparable L E := by
  let ρ : R' →ₐ[A] E := (IsScalarTower.toAlgHom A (B ⊗[A] R' ⧸ 𝔭) E).comp
    ((Ideal.Quotient.mkₐ A 𝔭).comp Algebra.TensorProduct.includeRight)
  have hθ : IsSeparable L (ρ P0.x) := by
    apply isSeparable_root (ρ P0.x) (P0.f.map (algebraMap A L))
    · rw [aeval_map_algebraMap L, aeval_algHom_apply, P0.hasMap.1, map_zero]
    · rw [derivative_map, aeval_map_algebraMap L, aeval_algHom_apply]
      exact (P0.hasMap.isUnit_derivative_f.map ρ).ne_zero
  have hpoly : ∀ p : A[X], aeval (ρ P0.x) p ∈ separableClosure L E := by
    intro p
    rw [← aeval_map_algebraMap L]
    exact Algebra.adjoin_le (S := (separableClosure L E).toSubalgebra)
      (Set.singleton_subset_iff.mpr (mem_separableClosure_iff.mpr hθ))
      (aeval_mem_adjoin_singleton L (ρ P0.x))
  have hρ : ∀ r, ρ r ∈ separableClosure L E := by
    intro r
    obtain ⟨p, n, e⟩ := P0.exists_mul_aeval_x_g_pow_eq_aeval_x r
    have hu : IsUnit (aeval (ρ P0.x) P0.g) := by
      rw [aeval_algHom_apply]
      exact P0.hasMap.2.map ρ
    have e' : ρ r * aeval (ρ P0.x) P0.g ^ n = aeval (ρ P0.x) p := by
      rw [aeval_algHom_apply, aeval_algHom_apply, ← map_pow, ← map_mul, e]
    have hr : ρ r = aeval (ρ P0.x) p / aeval (ρ P0.x) P0.g ^ n := by
      rw [← e', mul_div_cancel_right₀ _ (pow_ne_zero n hu.ne_zero)]
    rw [hr]
    exact div_mem (hpoly p) (pow_mem (hpoly _) n)
  have hS : ∀ s : B ⊗[A] R',
      algebraMap (B ⊗[A] R' ⧸ 𝔭) E (Ideal.Quotient.mk 𝔭 s) ∈ separableClosure L E := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | tmul b r =>
      have hbr : (b ⊗ₜ[A] r : B ⊗[A] R') = algebraMap B (B ⊗[A] R') b * ((1 : B) ⊗ₜ r) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hbr, map_mul, map_mul]
      refine mul_mem ?_ (hρ r)
      have hb : algebraMap (B ⊗[A] R' ⧸ 𝔭) E (Ideal.Quotient.mk 𝔭 (algebraMap B (B ⊗[A] R') b)) =
          algebraMap L E (algebraMap B L b) := by
        rw [← IsScalarTower.algebraMap_apply B L E, IsScalarTower.algebraMap_apply B (B ⊗[A] R' ⧸ 𝔭) E,
          Ideal.Quotient.mk_algebraMap]
      rw [hb]
      exact IntermediateField.algebraMap_mem _ _
    | add x y hx hy =>
      rw [map_add, map_add]
      exact add_mem hx hy
  apply (separableClosure.eq_top_iff L E).mp
  rw [eq_top_iff]
  intro e _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (B ⊗[A] R' ⧸ 𝔭) e
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact div_mem (hS a) (hS b)

end RamanujanPetersson.EtSheaves.InertiaLift

end

end

-- ===== S4.Def_RP_EtSheaves_InertiaLift2 =====
section

/-!
# S4-EtSheaves, O10c part 2d: the inertia lift

HEADLINE `exists_inertia_lift`: let `τ ∈ Gal(L/K)` act on `B` (`Frac B = L`, `B` integrally closed)
through `τB` with `τB b - b ∈ Q` for all `b` (inertia at `Q`), and let `R'` be standard etale over `A`
with a prime `u` over `Q ∩ A`. Then for any separably closed `Ω` normal over `K` there are
`ψ : R' →ₐ[A] Ω`, `ι : L →ₐ[K] Ω` and `τ' ∈ Aut(Ω/K)` with `τ' ∘ ψ = ψ` and `τ' ∘ ι = ι ∘ τ`.
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtSheaves.InertiaLift

variable {A K L B R' : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
  [CommRing R'] [Algebra A R']

/-- The lift for a fixed branch `𝔭` of `B ⊗[A] R'` over `(0)` with `(τB ⊗ 1)⁻¹ 𝔭 = 𝔭`. -/
theorem exists_lift [Algebra.IsSeparable K L] (P0 : StandardEtalePresentation A R')
    (τ : L ≃ₐ[K] L) (τB : B ≃ₐ[A] B) (hτB : ∀ b, algebraMap B L (τB b) = τ (algebraMap B L b))
    (𝔭 : Ideal (B ⊗[A] R')) [𝔭.IsPrime] (h0 : 𝔭.comap (algebraMap B (B ⊗[A] R')) = ⊥)
    (hfix : 𝔭.comap (InertiaFix.tauT τB) = 𝔭)
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosed Ω]
    [Normal K Ω] :
    ∃ ψ : R' →ₐ[A] Ω, ∃ ι : L →ₐ[K] Ω, ∃ τ' : Ω ≃ₐ[K] Ω,
      (∀ r, τ' (ψ r) = ψ r) ∧ ∀ l, τ' (ι l) = ι (τ l) := by
  have hinj := algebraMap_injective 𝔭 h0
  let lam : L →+* Fld 𝔭 := IsFractionRing.lift (A := B) (K := L) hinj
  have hlam : ∀ b, lam (algebraMap B L b) = algebraMap B (Fld 𝔭) b :=
    IsFractionRing.lift_algebraMap hinj
  letI : Algebra L (Fld 𝔭) := lam.toAlgebra
  letI : Algebra K (Fld 𝔭) := (lam.comp (algebraMap K L)).toAlgebra
  haveI : IsScalarTower K L (Fld 𝔭) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B L (Fld 𝔭) := IsScalarTower.of_algebraMap_eq (fun b => (hlam b).symm)
  haveI : IsScalarTower A L (Fld 𝔭) := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A (Fld 𝔭) a = lam (algebraMap A L a)
    rw [IsScalarTower.algebraMap_apply A B L, hlam, ← IsScalarTower.algebraMap_apply])
  haveI : IsScalarTower A K (Fld 𝔭) := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap A (Fld 𝔭) a = lam (algebraMap K L (algebraMap A K a))
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L, hlam,
      ← IsScalarTower.algebraMap_apply])
  haveI : Algebra.IsSeparable L (Fld 𝔭) := isSeparable_frac 𝔭 P0 (Fld 𝔭)
  haveI : Algebra.IsSeparable K (Fld 𝔭) := Algebra.IsSeparable.trans K L (Fld 𝔭)
  have hIJ : 𝔭 = 𝔭.map ((InertiaFix.tauT τB : B ⊗[A] R' ≃ₐ[A] B ⊗[A] R') :
      B ⊗[A] R' →+* B ⊗[A] R') := by
    have h := Ideal.map_comap_of_surjective (InertiaFix.tauT (R' := R') τB)
      (InertiaFix.tauT τB).surjective 𝔭
    rw [hfix] at h
    exact h.symm
  let τD := Ideal.quotientEquivAlg 𝔭 𝔭 (InertiaFix.tauT τB) hIJ
  let τE : Fld 𝔭 ≃ₐ[K] Fld 𝔭 := IsFractionRing.fieldEquivOfAlgEquiv K (Fld 𝔭) (Fld 𝔭) τD
  have hτE : ∀ s, τE (algebraMap (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (Ideal.Quotient.mk 𝔭 s)) =
      algebraMap (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (Ideal.Quotient.mk 𝔭 (InertiaFix.tauT τB s)) := by
    intro s
    rw [IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
    exact congrArg _ (Ideal.quotientEquivAlg_mk 𝔭 (InertiaFix.tauT τB) hIJ s)
  have hB : ∀ b, τE (algebraMap B (Fld 𝔭) b) = algebraMap B (Fld 𝔭) (τB b) := by
    intro b
    rw [IsScalarTower.algebraMap_apply B (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭),
      IsScalarTower.algebraMap_apply B (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (τB b),
      ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, hτE,
      InertiaFix.tauT_algebraMap]
  have hlamτ : ∀ l, τE (lam l) = lam (τ l) := by
    have h : (τE : Fld 𝔭 →+* Fld 𝔭).comp lam = lam.comp (τ : L →+* L) := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors B)
      ext b
      show τE (lam (algebraMap B L b)) = lam (τ (algebraMap B L b))
      rw [hlam, hB, ← hτB, hlam]
    intro l
    exact congrArg (fun φ : L →+* Fld 𝔭 => φ l) h
  let ρ : R' →ₐ[A] Fld 𝔭 := (IsScalarTower.toAlgHom A (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭)).comp
    ((Ideal.Quotient.mkₐ A 𝔭).comp Algebra.TensorProduct.includeRight)
  have hρ : ∀ r, τE (ρ r) = ρ r := by
    intro r
    show τE (algebraMap (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (Ideal.Quotient.mk 𝔭 ((1 : B) ⊗ₜ r))) =
      algebraMap (B ⊗[A] R' ⧸ 𝔭) (Fld 𝔭) (Ideal.Quotient.mk 𝔭 ((1 : B) ⊗ₜ r))
    rw [hτE, InertiaFix.tauT_tmul, map_one]
  obtain ⟨j, τ', hj⟩ := exists_lift_aut (Ω := Ω) τE
  refine ⟨(j.restrictScalars A).comp ρ, j.comp (IsScalarTower.toAlgHom K L (Fld 𝔭)), τ',
    fun r => ?_, fun l => ?_⟩
  · show τ' (j (ρ r)) = j (ρ r)
    rw [hj, hρ]
  · show τ' (j (lam l)) = j (lam (τ l))
    rw [hj, hlamτ]

/-- HEADLINE (O10c F2): an inertia element at `Q` lifts to `Aut(Ω/K)` fixing an `Ω`-point of `R'`. -/
theorem exists_inertia_lift [Algebra.IsSeparable K L] [IsIntegrallyClosed B]
    (P0 : StandardEtalePresentation A R') (τ : L ≃ₐ[K] L) (τB : B ≃ₐ[A] B)
    (hτB : ∀ b, algebraMap B L (τB b) = τ (algebraMap B L b)) (Q : Ideal B) [Q.IsPrime]
    (hτ : ∀ b, τB b - b ∈ Q) (u : Ideal R') [u.IsPrime]
    (hu : u.comap (algebraMap A R') = Q.comap (algebraMap A B))
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosed Ω]
    [Normal K Ω] :
    ∃ ψ : R' →ₐ[A] Ω, ∃ ι : L →ₐ[K] Ω, ∃ τ' : Ω ≃ₐ[K] Ω,
      (∀ r, τ' (ψ r) = ψ r) ∧ ∀ l, τ' (ι l) = ι (τ l) := by
  obtain ⟨𝔮, h𝔮p, h𝔮⟩ := FibreNe.exists_prime_tmul Q u hu
  haveI := h𝔮p
  obtain ⟨𝔭, h𝔭p, -, h0, hfix⟩ := InertiaFix.exists_fixed_prime P0 τB Q hτ 𝔮 h𝔮
  haveI := h𝔭p
  exact exists_lift P0 τ τB hτB 𝔭 h0 hfix Ω

end RamanujanPetersson.EtSheaves.InertiaLift

end

end

-- ===== S4.Def_RP_EtSheaves_UnramKer =====
section

/-!
# S4-EtSheaves, O10c part 5a: open kernel of a lisse Galois representation; ranges of normal embeddings

* `isOpen_ker_galRep`: for lisse `F`, the kernel of `Gal(κ(x)^sep/κ(x)) → Aut(F_x̄)` is open (finite stalk, each
  generator has an open stabilizer).
* `mem_fieldRange_of_normal`: two embeddings of a normal extension have the same range.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

/-- **The Galois representation on a lisse stalk has open kernel.** -/
theorem isOpen_ker_galRep {F : EtSh Λ X} (hF : IsLisse Λ F) (x : X) :
    IsOpen ((galRep Λ F x).ker : Set (Gal x)) := by
  have hfin : Module.Finite Λ (stalk Λ F x) := hF.finite_stalkF (geomPtAt x)
  obtain ⟨s, hs⟩ := hfin.fg_top
  choose H hHo hH using fun v : stalk Λ F x => exists_open_fix Λ F x v
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have hmem : (⋂ v ∈ s, (H v : Set (Gal x))) ∈ nhds (1 : Gal x) :=
    (Filter.biInter_finset_mem s).mpr fun v _ => (hHo v).mem_nhds (H v).one_mem
  refine Filter.mem_of_superset hmem fun σ hσ => ?_
  rw [Set.mem_iInter₂] at hσ
  show σ ∈ (galRep Λ F x).ker
  rw [MonoidHom.mem_ker]
  exact LinearMap.ext_on hs fun v hv => hH v σ (hσ v hv)

/-- Two embeddings of a normal extension `E/F` into `M` have the same range. -/
theorem mem_fieldRange_of_normal {F E M : Type*} [Field F] [Field E] [Field M] [Algebra F E] [Algebra F M]
    [Normal F E] (f g : E →ₐ[F] M) (x : E) : f x ∈ g.fieldRange := by
  let e := g.equivFieldRange
  have : Normal F g.fieldRange := Normal.of_algEquiv e
  rw [← AlgHom.fieldRange_of_normal (f.comp e.symm.toAlgHom)]
  refine ⟨e x, ?_⟩
  show f (e.symm (e x)) = f x
  rw [AlgEquiv.symm_apply_apply]

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_UnramMain =====
section

/-!
# S4-EtSheaves, O10c part 5: the generic Galois representation of a lisse sheaf is unramified

For a lisse `F` on `Spec A` (`A` an integrally closed domain with fraction field `K`), the Galois
representation on the generic stalk `F_η̄` is trivial on the kernel of `Gal(κ(η)^sep/κ(η)) → π₁(Spec A)`
(`galRep_unram`). The fixed field `L0` of its (open) kernel is a finite Galois extension of `K`; its copy
in `K̄` is unramified over `A` (`unram`): an inertia element lifts (`InertiaLift.exists_inertia_lift`) to an
automorphism fixing a chart point (`Plumb.exists_chart`), hence `L0`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.UnramMain

open GenBr

attribute [local instance] genAlg genAlgSep genTower Plumb.genAlgA

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

theorem fracIso_algebraMap' (a : A) : fracIso A K (algebraMap A K a) = Plumb.toGen A a := by
  show (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).inv.hom
    (IsLocalization.algEquiv (nonZeroDivisors A) K (⊥ : Ideal A).ResidueField (algebraMap A K a)) = _
  rw [AlgEquiv.commutes]
  rfl

theorem tower : IsScalarTower A K (SeparableClosure (genField A)) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap (genField A) (SeparableClosure (genField A)) (Plumb.toGen A a) =
      algebraMap (genField A) (SeparableClosure (genField A)) (fracIso A K (algebraMap A K a))
    rw [fracIso_algebraMap'])

theorem isGaloisK : IsGalois K (SeparableClosure (genField A)) :=
  IsGalois.of_equiv_equiv (F := genField A) (E := SeparableClosure (genField A)) (f := (fracIso A K).symm)
    (g := RingEquiv.refl _) (RingHom.ext fun x => by
      show algebraMap (genField A) (SeparableClosure (genField A)) (fracIso A K ((fracIso A K).symm x)) =
        algebraMap (genField A) (SeparableClosure (genField A)) x
      rw [RingEquiv.apply_symm_apply])

attribute [local instance] tower isGaloisK

/-- An automorphism of `κ(η)^sep` over `K` is one over `κ(η) ≅ K`. -/
def toGal (τ : SeparableClosure (genField A) ≃ₐ[K] SeparableClosure (genField A)) : Gal (genPt A) :=
  AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => by
    obtain ⟨y, rfl⟩ := (fracIso A K).surjective x
    exact τ.commutes y)

variable {Λ : Type} [CommRing Λ] (F : EtSh Λ (Spec (CommRingCat.of A)))

/-- The fixed field of the kernel of the generic Galois representation. -/
def L0 : IntermediateField (genField A) (SeparableClosure (genField A)) :=
  IntermediateField.fixedField (galRep Λ F (genPt A)).ker

theorem fixingSubgroup_L0 (hF : IsLisse Λ F) : (L0 A F).fixingSubgroup = (galRep Λ F (genPt A)).ker :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨(galRep Λ F (genPt A)).ker, Subgroup.isClosed_of_isOpen _ (isOpen_ker_galRep hF _)⟩

theorem finiteDimensional_L0 (hF : IsLisse Λ F) : FiniteDimensional (genField A) (L0 A F) :=
  (InfiniteGalois.isOpen_iff_finite _).mp (by
    rw [fixingSubgroup_L0 A F hF]
    exact isOpen_ker_galRep hF _)

theorem isGalois_L0 (hF : IsLisse Λ F) : IsGalois (genField A) (L0 A F) :=
  (InfiniteGalois.normal_iff_isGalois _).mp (by
    rw [fixingSubgroup_L0 A F hF]
    infer_instance)

theorem finK (hF : IsLisse Λ F) : FiniteDimensional K (L0 A F) := by
  have := finiteDimensional_L0 A F hF
  have : Module.Finite K (genField A) := Module.Finite.of_surjective (Algebra.linearMap K (genField A))
    (fun y => ⟨(fracIso A K).symm y, (fracIso A K).apply_symm_apply y⟩)
  exact Module.Finite.trans (genField A) (L0 A F)

/-- `K`-copies of `L0` are finite over `K` (with the `K`-module structure of the `K`-algebra `L0`). -/
theorem finRange (hF : IsLisse Λ F) (j : L0 A F →ₐ[K] AlgebraicClosure K) : FiniteDimensional K j.fieldRange := by
  have := finiteDimensional_L0 A F hF
  have : Module.Finite K (genField A) := Module.Finite.of_surjective (Algebra.linearMap K (genField A))
    (fun y => ⟨(fracIso A K).symm y, (fracIso A K).apply_symm_apply y⟩)
  letI : Module K (L0 A F) := Algebra.toModule
  letI : IsScalarTower K (genField A) (L0 A F) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Finite K (L0 A F) := Module.Finite.trans (genField A) (L0 A F)
  exact Module.Finite.equiv j.equivFieldRange.toLinearEquiv

theorem galK (hF : IsLisse Λ F) : IsGalois K (L0 A F) := by
  have := isGalois_L0 A F hF
  exact IsGalois.of_equiv_equiv (F := genField A) (E := L0 A F) (f := (fracIso A K).symm)
    (g := RingEquiv.refl _) (RingHom.ext fun x => by
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply K (genField A) (L0 A F)]
      exact congrArg (algebraMap (genField A) (L0 A F)) ((fracIso A K).apply_symm_apply x))

/-- Any `K`-copy `L` of `L0` inside `K̄` is unramified over `A`. -/
theorem unram [IsIntegrallyClosed A] (hF : IsLisse Λ F) (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L] (e0 : L0 A F ≃ₐ[K] L) : IsUnramifiedSub A K L := by
  intro Q hQ
  have := hQ
  have : IsFractionRing (integralClosure A L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K L
  have : IsIntegrallyClosed (integralClosure A L) := integralClosure.isIntegrallyClosedOfFiniteExtension K
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  let τB : integralClosure A L ≃ₐ[A] integralClosure A L :=
    AlgEquiv.ofRingEquiv (f := MulSemiringAction.toRingEquiv _ (integralClosure A L) τ) (fun a =>
      Subtype.ext (by
        show τ (algebraMap A L a) = algebraMap A L a
        rw [IsScalarTower.algebraMap_apply A K L]
        exact τ.commutes _))
  obtain ⟨R', _, _, P0, u, hu, hcomp, H⟩ :=
    Plumb.exists_chart A F hF ⟨Q.comap (algebraMap A (integralClosure A L)), inferInstance⟩
  have := hu
  obtain ⟨ψ, ι, τ', hψ, hι⟩ := InertiaLift.exists_inertia_lift P0 τ τB (fun _ => rfl) Q
    (fun b => AddSubgroup.mem_inertia.mp hτ b) u hcomp (SeparableClosure (genField A))
  have hN : toGal A K τ' ∈ (L0 A F).fixingSubgroup := by
    rw [fixingSubgroup_L0 A F hF]
    exact MonoidHom.mem_ker.mpr (H ψ (toGal A K τ') hψ)
  have hx : ∀ x, τ x = x := by
    intro x
    have hmem : ι x ∈ L0 A F := by
      obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.mp
        (mem_fieldRange_of_normal ι (((L0 A F).val.restrictScalars K).comp e0.symm.toAlgHom) x)
      rw [← hy]
      exact (e0.symm y).2
    apply ι.toRingHom.injective
    show ι (τ x) = ι x
    rw [← hι x]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hN (ι x) hmem
  exact AlgEquiv.ext hx

/-- **HEADLINE (O10c).** For lisse `F` on `Spec A` (`A` integrally closed), the Galois representation on the
generic stalk `F_η̄` factors through `π₁(Spec A)`: it is trivial on the kernel of `genToPi1`. -/
theorem galRep_unram [IsIntegrallyClosed A] (hF : IsLisse Λ F) (σ : Gal (genPt A))
    (hσ : genToPi1 A K σ = 1) : galRep Λ F (genPt A) σ = LinearMap.id := by
  have := finiteDimensional_L0 A F hF
  have := isGalois_L0 A F hF
  have := finK A K F hF
  have := galK A K F hF
  let j : L0 A F →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let e0 := j.equivFieldRange
  have : FiniteDimensional K j.fieldRange := finRange A K F hF j
  have : IsGalois K j.fieldRange := IsGalois.of_algEquiv e0
  have hmem : j.fieldRange ∈ unramSet A K := ⟨inferInstance, inferInstance, unram A K F hF j.fieldRange e0⟩
  have hle : j.fieldRange ≤ maxUnram A K := by
    rw [maxUnram_eq_sSup]
    exact le_sSup hmem
  have hker : σ ∈ (galRep Λ F (genPt A)).ker := by
    rw [← fixingSubgroup_L0 A F hF, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.mp (mem_fieldRange_of_normal
      (((L0 A F).val.restrictScalars K).comp e0.symm.toAlgHom)
      ((emb A K (SeparableClosure (genField A))).comp (IntermediateField.inclusion hle)) (e0 ⟨y, hy⟩))
    have h2 : ((e0.symm (e0 ⟨y, hy⟩) : L0 A F) : SeparableClosure (genField A)) = y := by
      rw [AlgEquiv.symm_apply_apply]
    have hz' : genEmb A K (IntermediateField.inclusion hle z) = y := hz.trans h2
    rw [← hz']
    exact (genToPi1_eq_one_iff A K σ).mp hσ _
  exact MonoidHom.mem_ker.mp hker

end RamanujanPetersson.EtSheaves.UnramMain

end

end

-- ===== S4.Def_RP_EtSheaves_EssSurj =====
section

/-!
# S4-EtSheaves, O10f part f: lisse sheaves on `Spec A` are their generic Galois representations

`A` is a noetherian integrally closed domain with fraction field `K`, `η` the generic point of `Spec A`.
* `full`: every Galois-equivariant map of generic stalks `F_η̄ → G_η̄` (`G` lisse) is the stalk of a sheaf map;
* `fibRep`: the Galois action on the generic stalk of a lisse `F` factors through `π₁ = Pi1 A K`, with open kernel
  (`isOpen_ker_fibRep`);
* `nonempty_iso_of_stalk`: lisse sheaves with equivariantly isomorphic generic stalks are isomorphic;
* **`essSurj`**: every lisse `F` is isomorphic to the sheaf `F_V` of its fibre representation `V = F_η̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.EssSurj

open GenBr TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower

section Full

variable (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  {Λ : Type} [CommRing Λ]

/-- **Fullness of the generic fibre functor on `Spec A`.** -/
theorem full {F G : EtSh Λ (Spec (CommRingCat.of A))} (hG : IsLisse Λ G)
    (f : stalk Λ F (genPt A) →ₗ[Λ] stalk Λ G (genPt A))
    (hf : ∀ (σ : Gal (genPt A)) (v : stalk Λ F (genPt A)),
      f (galRep Λ F (genPt A) σ v) = galRep Λ G (genPt A) σ (f v)) :
    ∃ φ : F ⟶ G, (((geomPtAt (genPt A)).stalkF Λ).map φ).hom = f :=
  FullAbs.full (genPt A) f ⟨genPt_mem A, hG.isLocConst, ChartSch.hChart A G hG, hf⟩

end Full

section Rep

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

/-- `galRep` as a hom to units, killed by `ker genToPi1` (`galRep_unram`). -/
def fibRepU (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F) :
    {g : Gal (genPt A) →* (Module.End Λ (stalk Λ F (genPt A)))ˣ // (genToPi1 A K).ker ≤ g.ker} :=
  ⟨(galRep Λ F (genPt A)).toHomUnits, fun σ hσ => MonoidHom.mem_ker.2 (Units.ext
    ((UnramMain.galRep_unram A K F hF σ (MonoidHom.mem_ker.1 hσ)).trans rfl))⟩

/-- The **fibre representation** of a lisse `F`: `π₁` acting on the generic stalk `F_η̄` (the Galois action
factors through `genToPi1` by `galRep_unram`). -/
def fibRep (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F) :
    Representation Λ (Pi1 A K) (stalk Λ F (genPt A)) :=
  (Units.coeHom (Module.End Λ (stalk Λ F (genPt A)))).comp
    ((genToPi1 A K).liftOfSurjective (genToPi1_surjective A K) (fibRepU A K F hF))

theorem fibRep_genToPi1 (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F) (σ : Gal (genPt A)) :
    fibRep A K F hF (genToPi1 A K σ) = galRep Λ F (genPt A) σ :=
  congrArg Units.val ((genToPi1 A K).liftOfRightInverse_comp_apply
    (Function.surjInv (genToPi1_surjective A K)) (Function.rightInverse_surjInv (genToPi1_surjective A K))
    (fibRepU A K F hF) σ)

/-- The fibre representation has open kernel. -/
theorem isOpen_ker_fibRep (F : EtSh Λ (Spec (CommRingCat.of A))) (hF : IsLisse Λ F) :
    IsOpen ((fibRep A K F hF).ker : Set (Pi1 A K)) := by
  let H := (galRep Λ F (genPt A)).ker
  have hH : IsOpen (H : Set (Gal (genPt A))) := isOpen_ker_galRep hF (genPt A)
  have hk : (genToPi1 A K).ker ≤ H := fun σ hσ =>
    MonoidHom.mem_ker.2 ((UnramMain.galRep_unram A K F hF σ (MonoidHom.mem_ker.1 hσ)).trans rfl)
  have : T2Space (Pi1 A K) := krullTopology_t2
  have : Finite (Gal (genPt A) ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient (H := H)
  have : (H.map (genToPi1 A K)).FiniteIndex :=
    ⟨by rw [H.index_map_eq (genToPi1_surjective A K) hk]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  refine Subgroup.isOpen_mono (fun τ hτ => ?_) (Subgroup.isOpen_of_isClosed_of_finiteIndex (H.map (genToPi1 A K)) ?_)
  · obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hτ
    rw [MonoidHom.mem_ker, fibRep_genToPi1]
    exact MonoidHom.mem_ker.1 hσ
  · rw [Subgroup.coe_map]
    exact ((H.isClosed_of_isOpen hH).isCompact.image (genToPi1_continuous A K)).isClosed

variable [IsNoetherianRing A]

end Rep

end RamanujanPetersson.EtSheaves.EssSurj

end

end

-- ===== S4.Def_RP_EtCompact_H0 =====
section

/-!
# S4-EtCompact, O9a: `H⁰` of a lisse sheaf on `Spec A` is the invariants of its generic stalk

* `galRep_unitSh`: `Gal(κ(x)^sep/κ(x))` acts trivially on the stalks of `Λ_X`;
* `h0Eval G x : H⁰(X, G) →+ G_x̄`, evaluation of a global section at `1 ∈ (Λ_X)_x̄ ≅ Λ`; it lands in the
  Galois invariants (`h0Eval_mem`);
* **`h0Equiv`**: for `A` a noetherian integrally closed domain and `G` lisse on `Spec A`,
  `H⁰(Spec A, G) ≃+ (G_η̄)^{Gal(η)}`; `fibRep_invariants`: the same submodule is the `π₁`-invariants of the
  fibre representation, so `H⁰(Spec A, G) ≃+ (G_η̄)^{π₁}` (`h0EquivPi1`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr

universe u

section General

variable {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]

/-- Stalk functors are additive (they preserve binary coproducts, hence biproducts). -/
instance stalkF_additive' (s : GeomPt X) : (s.stalkF Λ).Additive := by
  have : PreservesColimitsOfShape (Discrete WalkingPair) (s.stalkF Λ) :=
    PreservesFiniteColimits.preservesFiniteColimits _
  have : PreservesBinaryBiproducts (s.stalkF Λ) := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The Galois action on the stalks of the constant sheaf `Λ_X` is trivial. -/
theorem galRep_unitSh (x : X) (σ : Gal x) : galRep Λ (unitSh Λ X) x σ = LinearMap.id :=
  galRep_eq_id_of_triv (𝟙 X) (unitSh Λ X) x (ModuleCat.of Λ Λ) (pullConst Λ (𝟙 X) _) (geomPtAt x).pt
    (Category.comp_id _) σ (galSpec_comp x σ)

/-- The element `1` of the stalk `(Λ_X)_x̄ ≅ Λ`. -/
def oneStalk (x : X) : stalk Λ (unitSh Λ X) x :=
  (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv.hom (1 : Λ)

/-- Maps out of the stalk `(Λ_X)_x̄` are determined by their value at `1`. -/
theorem stalk_unitSh_hom_ext (x : X) {N : ModuleCat.{u} Λ} {f g : stalk Λ (unitSh Λ X) x ⟶ N}
    (h : f.hom (oneStalk Λ x) = g.hom (oneStalk Λ x)) : f = g := by
  rw [← cancel_epi (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv]
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  exact h

end General

section Spec

variable (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
  (Λ : Type) [CommRing Λ]

variable (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]

end Spec

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Ext1 =====
section

/-!
# S4-EtCompact, O9b part 1: `Ext¹` classes and extensions (any abelian category)

* `mk₀_injective`;
* **`extClass_eq_zero_iff`**: the class of a short exact `0 → X₁ → X₂ → X₃ → 0` vanishes iff `X₁ → X₂` has a
  retraction;
* **`exists_extClass_eq`** (enough injectives): every `e ∈ Ext¹(X₃, X₁)` is the class of a short exact sequence
  `0 → X₁ → P → X₃ → 0` (pull back an injective presentation of `X₁`).
-/

set_option autoImplicit false

open CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

open Abelian

theorem mk₀_injective (X Y : C) : Function.Injective (Ext.mk₀ : (X ⟶ Y) → Ext.{w} X Y 0) :=
  (Ext.mk₀_bijective X Y).1

/-- **The class of a short exact sequence vanishes iff it splits** (`S.f` has a retraction). -/
theorem extClass_eq_zero_iff {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = (0 : Ext.{w} S.X₃ S.X₁ 1) ↔ ∃ r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 S.X₁ := by
  constructor
  · intro h
    have h1 : hS.extClass.comp (Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) = 0 := by rw [Ext.comp_mk₀_id, h]
    obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS S.X₁ (Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) h1
    obtain ⟨r, rfl⟩ := (Ext.mk₀_bijective S.X₂ S.X₁).2 x₂
    have hr : (Ext.mk₀ (S.f ≫ r) : Ext.{w} S.X₁ S.X₁ 0) = Ext.mk₀ (𝟙 S.X₁) := by
      rw [← Ext.mk₀_comp_mk₀, hx₂]
    exact ⟨r, mk₀_injective _ _ hr⟩
  · rintro ⟨r, hr⟩
    have := hS.extClass_comp_assoc (Ext.mk₀ r) (h := add_zero 1)
    rwa [Ext.mk₀_comp_mk₀, hr, Ext.comp_mk₀_id] at this

section Pullback

variable [EnoughInjectives C] {X₁ X₃ : C}

/-- The injective presentation `0 → X₁ → I → I/X₁ → 0`. -/
abbrev injPres (X₁ : C) : ShortComplex C :=
  ShortComplex.mk (Injective.ι X₁) (cokernel.π (Injective.ι X₁)) (cokernel.condition _)

omit [HasExt C] in
theorem injPres_shortExact (X₁ : C) : (injPres X₁).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι X₁))

variable (s : X₃ ⟶ cokernel (Injective.ι X₁))

/-- The pull-back of the injective presentation along `s : X₃ ⟶ I/X₁`. -/
abbrev pbSES : ShortComplex C :=
  ShortComplex.mk (pullback.lift (Injective.ι X₁) 0 (by rw [cokernel.condition, zero_comp]) :
      X₁ ⟶ pullback (cokernel.π (Injective.ι X₁)) s) (pullback.snd _ _) (pullback.lift_snd _ _ _)

/-- The comparison map from the pull-back sequence to the injective presentation. -/
def pbHom : pbSES s ⟶ injPres X₁ where
  τ₁ := 𝟙 X₁
  τ₂ := pullback.fst _ _
  τ₃ := s
  comm₁₂ := (Category.id_comp _).trans (pullback.lift_fst _ _ _).symm
  comm₂₃ := pullback.condition

omit [HasExt C] in
theorem pbHom_τ₁ : (pbHom s).τ₁ = 𝟙 X₁ := rfl

omit [HasExt C] in
theorem pbHom_τ₃ : (pbHom s).τ₃ = s := rfl

omit [HasExt C] in
theorem pbSES_shortExact : (pbSES s).ShortExact := by
  have hP := injPres_shortExact X₁
  have hm : Mono (pbSES s).f := by
    have : (pbSES s).f ≫ pullback.fst _ _ = Injective.ι X₁ := pullback.lift_fst _ _ _
    exact mono_of_mono_fac this
  have he : Epi (pbSES s).g := by
    show Epi (pullback.snd _ _)
    infer_instance
  refine ShortComplex.ShortExact.mk' ?_ hm he
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun {W} k hk => hP.exact.lift (k ≫ pullback.fst _ _) ?_) (fun {W} k hk => ?_) (fun {W} k hk m hm' => ?_))
  · show (k ≫ pullback.fst _ _) ≫ cokernel.π (Injective.ι X₁) = 0
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have : k ≫ pullback.snd _ _ = 0 := hk
    rw [this, zero_comp]
  · apply pullback.hom_ext
    · simp only [pbSES, Category.assoc, pullback.lift_fst]
      exact hP.exact.lift_f _ _
    · simp only [pbSES, Category.assoc, pullback.lift_snd, comp_zero]
      exact hk.symm
  · rw [← cancel_mono (injPres X₁).f, hP.exact.lift_f, ← hm']
    simp only [pbSES, injPres, Category.assoc, pullback.lift_fst]

/-- **Every class in `Ext¹(X₃, X₁)` is the class of a short exact sequence** `0 → X₁ → P → X₃ → 0`. -/
theorem exists_extClass_eq (e : Ext.{w} X₃ X₁ 1) :
    ∃ (s : X₃ ⟶ cokernel (Injective.ι X₁)), (pbSES_shortExact s).extClass (C := C) = e := by
  have hP := injPres_shortExact X₁
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ X₃ hP e (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective X₃ (cokernel (Injective.ι X₁))).2 x₃
  refine ⟨s, ?_⟩
  have := (pbSES_shortExact s).extClass_naturality hP (pbHom s)
  rw [pbHom_τ₁, pbHom_τ₃, Ext.comp_mk₀_id] at this
  rw [← hx₃]
  exact this

end Pullback

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_FVMap =====
section

/-!
# S4-EtSheaves, part O10e(ii): `V ↦ F_V` is a functor, compatible with the stalk isomorphisms

* `eqShMap`: a map `φ : S ⟶ S'` intertwining `a, b` with `a', b'` restricts to the equaliser subsheaves.
* `cMap f : V_X ⟶ W_X` (constant sheaf map), `cMap_constUnit`; `sMap f : SV V ⟶ SV W`.
* `FVMap f hf : F_V ⟶ F_W` for a `G`-equivariant `f : V →ₗ W`; `eT_FVMap`, `FVMap_unitFV`.
* `stalkFV_FVMap`, `stalkFVAt_FVMap`, `stalkFVAt_FVMap_hom`: under `stalkFVAt`, the stalk map of `FVMap f` is `f`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

section EqMap

universe u

variable {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}}

theorem app_comm {F G : EtSh Λ Z} {c : F ⟶ F} {c' : G ⟶ G} {ψ : F ⟶ G} (h : c ≫ ψ = ψ ≫ c') (U : Z.Etale)
    (s : F.obj.obj (op U)) :
    (ψ.hom.app (op U)).hom ((c.hom.app (op U)).hom s) = (c'.hom.app (op U)).hom ((ψ.hom.app (op U)).hom s) :=
  congrArg (fun χ : F ⟶ G => (χ.hom.app (op U)).hom s) h

variable {S S' : EtSh Λ Z} {ι : Type*} (a b : ι → (S ⟶ S)) (a' b' : ι → (S' ⟶ S')) (φ : S ⟶ S')
  (ha : ∀ i, a i ≫ φ = φ ≫ a' i) (hb : ∀ i, b i ≫ φ = φ ≫ b' i)

/-- `φ` on sections of the equaliser. -/
def eqShMapLin (U : Z.Etale) : eqSecSub S a b U →ₗ[Λ] eqSecSub S' a' b' U where
  toFun s := ⟨(φ.hom.app (op U)).hom s.1, (mem_eqSecSub S' a' b' _).2 fun i =>
    (app_comm (ha i) U s.1).symm.trans ((congrArg (fun t => (φ.hom.app (op U)).hom t)
      ((mem_eqSecSub S a b _).1 s.2 i)).trans (app_comm (hb i) U s.1))⟩
  map_add' s t := Subtype.ext (map_add _ s.1 t.1)
  map_smul' c s := Subtype.ext (map_smul _ c s.1)

/-- **Functoriality of the equaliser subsheaf.** -/
def eqShMap : eqSh S a b ⟶ eqSh S' a' b' :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom (eqShMapLin a b a' b' φ ha hb U.unop)
      naturality := fun _ _ f => ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext
        (app_map φ f.unop s.1)) }

theorem eqShMap_val (U : Z.Etale) (s : (eqSh S a b).obj.obj (op U)) :
    (((eqShMap a b a' b' φ ha hb).hom.app (op U)).hom s).1 = (φ.hom.app (op U)).hom s.1 := rfl

end EqMap

namespace TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ]
  {V W : Type} [AddCommGroup V] [Module Λ V] [AddCommGroup W] [Module Λ W]

/-- The map of constant sheaves `V_X ⟶ W_X` induced by `f`. -/
def cMap (f : V →ₗ[Λ] W) : VX A Λ V ⟶ VX A Λ W :=
  (constantSheaf (SX A).smallEtaleTopology (ModuleCat.{0} Λ)).map (ModuleCat.ofHom f)

theorem cMap_constUnit (f : V →ₗ[Λ] W) (U : (SX A).Etale) (v : V) :
    ((cMap Λ f).hom.app (op U)).hom ((constUnit (ModuleCat.of Λ V) U).hom v) =
      (constUnit (ModuleCat.of Λ W) U).hom (f v) :=
  (congrArg (fun η => (η.app (op U)).hom v) (toSheafify_naturality (SX A).smallEtaleTopology
    ((Functor.const ((SX A).Etale)ᵒᵖ).map (ModuleCat.ofHom f)))).symm

theorem th_cMap (ρV : Representation Λ C.G V) (ρW : Representation Λ C.G W) (f : V →ₗ[Λ] W)
    (hf : ∀ g : C.G, f ∘ₗ ρV g = ρW g ∘ₗ f) (σ : C.G) :
    th C Λ ρV σ ≫ cMap Λ f = cMap Λ f ≫ th C Λ ρW σ := by
  have h : ModuleCat.ofHom (ρV σ⁻¹) ≫ ModuleCat.ofHom f = ModuleCat.ofHom f ≫ ModuleCat.ofHom (ρW σ⁻¹) := by
    ext v
    exact LinearMap.congr_fun (hf σ⁻¹) v
  unfold th cMap
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, h]

/-- `f` on `SV : U ↦ V_X(U ×_X Y)`. -/
def sMap (f : V →ₗ[Λ] W) : SV C Λ V ⟶ SV C Λ W :=
  ObjectProperty.homMk
    { app := fun U => (cMap Λ f).hom.app (op ((etComp (pr C)).obj ((etPull (pr C)).obj U.unop)))
      naturality := fun _ _ g =>
        (cMap Λ f).hom.naturality ((etComp (pr C)).map ((etPull (pr C)).map g.unop)).op }

theorem aS_sMap (f : V →ₗ[Λ] W) (σ : C.G) : aS C Λ V σ ≫ sMap (C := C) Λ f = sMap Λ f ≫ aS C Λ W σ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => (cMap Λ f).hom.naturality (tE C σ U.unop).op))

theorem bS_sMap (ρV : Representation Λ C.G V) (ρW : Representation Λ C.G W) (f : V →ₗ[Λ] W)
    (hf : ∀ g : C.G, f ∘ₗ ρV g = ρW g ∘ₗ f) (σ : C.G) :
    bS C Λ ρV σ ≫ sMap (C := C) Λ f = sMap Λ f ≫ bS C Λ ρW σ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => congrArg
    (fun χ : VX A Λ V ⟶ VX A Λ W => χ.hom.app (op ((etComp (pr C)).obj ((etPull (pr C)).obj U.unop))))
    (th_cMap Λ ρV ρW f hf σ)))

variable (ρV : Representation Λ C.G V) (ρW : Representation Λ C.G W) (f : V →ₗ[Λ] W)
  (hf : ∀ g : C.G, f ∘ₗ ρV g = ρW g ∘ₗ f)

/-- **`F_V ⟶ F_W` for a `G`-equivariant `f : V → W`.** -/
def FVMap : FV C Λ ρV ⟶ FV C Λ ρW :=
  eqShMap (aS C Λ V) (bS C Λ ρV) (aS C Λ W) (bS C Λ ρW) (sMap (C := C) Λ f) (aS_sMap Λ f)
    (bS_sMap Λ ρV ρW f hf)

theorem eT_FVMap (T : (SY C).Etale) (s : (FV C Λ ρV).obj.obj (op (tx T))) :
    eT Λ ρW T (((FVMap Λ ρV ρW f hf).hom.app (op (tx T))).hom s) =
      ((cMap Λ f).hom.app (op (tx T))).hom (eT Λ ρV T s) := by
  let s1 : (VX A Λ V).obj.obj (op (tp T)) := s.1
  change ((VX A Λ W).obj.map (sec T 1).op).hom (((cMap Λ f).hom.app (op (tp T))).hom s1) =
    ((cMap Λ f).hom.app (op (tx T))).hom (((VX A Λ V).obj.map (sec T 1).op).hom s1)
  exact (app_map (cMap Λ f) (sec T 1) s1).symm

theorem FVMap_unitFV (v : V) :
    ((FVMap Λ ρV ρW f hf).hom.app (op (tx (etId (SY C))))).hom (unitFV Λ ρV v) = unitFV Λ ρW (f v) := by
  refine (eT Λ ρW (etId (SY C))).injective ((eT_FVMap Λ ρV ρW f hf _ _).trans ?_)
  rw [unitFV, unitFV, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, cMap_constUnit]

/-- **The stalk map of `FVMap f` is `f`** (at `t ≫ π`, inverse form). -/
theorem stalkFV_FVMap (t : GeomPt (SY C)) (v : V) :
    (((t.map (pr C)).stalkF Λ).map (FVMap Λ ρV ρW f hf)).hom ((stalkFV Λ ρV t).inv.hom v) =
      (stalkFV Λ ρW t).inv.hom (f v) := by
  rw [stalkFV_inv, stalkFV_inv, ← FVMap_unitFV Λ ρV ρW f hf v]
  have h := congrArg (fun φ => φ.hom (unitFV Λ ρV v))
    ((t.map (pr C)).point.toPresheafFiber_naturality (FVMap Λ ρV ρW f hf).hom (tx (etId (SY C)))
      (liftX (pr C) t t.top))
  first
  | exact h
  | exact h.symm

theorem stalkFVAt_FVMap_mk (Ω : Type) [Field Ω] [IsSepClosed Ω] (pt : Spec (CommRingCat.of Ω) ⟶ SX A)
    (l : Spec (CommRingCat.of Ω) ⟶ SY C) (hl : l ≫ pr C = pt) (v : V) :
    (((GeomPt.mk Ω pt).stalkF Λ).map (FVMap Λ ρV ρW f hf)).hom
        ((stalkFVAt Λ ρV (GeomPt.mk Ω pt) l hl).inv.hom v) =
      (stalkFVAt Λ ρW (GeomPt.mk Ω pt) l hl).inv.hom (f v) := by
  subst hl
  exact stalkFV_FVMap Λ ρV ρW f hf (liftPt (GeomPt.mk Ω (l ≫ pr C)) l) v

/-- **Under `stalkFVAt`, the stalk map of `FVMap f` is `f`** (any geometric point with a lift). -/
theorem stalkFVAt_FVMap (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C) (hl : l ≫ pr C = s.pt)
    (v : V) :
    ((s.stalkF Λ).map (FVMap Λ ρV ρW f hf)).hom ((stalkFVAt Λ ρV s l hl).inv.hom v) =
      (stalkFVAt Λ ρW s l hl).inv.hom (f v) :=
  stalkFVAt_FVMap_mk Λ ρV ρW f hf s.Ω s.pt l hl v

theorem stalkFVAt_FVMap_hom (s : GeomPt (SX A)) (l : Spec (CommRingCat.of s.Ω) ⟶ SY C)
    (hl : l ≫ pr C = s.pt) (w : (s.stalkF Λ).obj (FV C Λ ρV)) :
    (stalkFVAt Λ ρW s l hl).hom.hom (((s.stalkF Λ).map (FVMap Λ ρV ρW f hf)).hom w) =
      f ((stalkFVAt Λ ρV s l hl).hom.hom w) := by
  conv_lhs => rw [← iso_hom_inv_apply Λ (stalkFVAt Λ ρV s l hl) w]
  rw [stalkFVAt_FVMap, iso_inv_hom_apply]

end TorSec

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_FVFull =====
section

/-!
# S4-EtSheaves, part O10e(iii): `V ↦ F_V` is fully faithful

* `Spec A` is connected for a domain `A` (`preconnectedSpace_SX`).
* `FV_hom_ext`: maps `F_V ⟶ F_W` (finite `V`, `W`) agreeing on one stalk (read through `stalkFVAt`) are equal.
* For `C = coverOf L` (`L` finite Galois unramified over `A`), `galFV = resL ∘ genToPi1` at the generic point is onto
  `G = Gal(L/K)` (`galFV_gen_surjective`).
* `genMap φ : V → W`, the generic-stalk map of `φ : F_V ⟶ F_W`, is `G`-equivariant (`genMap_equivariant`).
* **`FV_full`**: every `φ : F_V ⟶ F_W` is `FVMap (genMap φ)`; `genMap_FVMap`; **`homEquiv`**:
  `(F_V ⟶ F_W) ≃ {f : V →ₗ W // f G-equivariant}`; `FVMap_id`, `FVMap_comp` (functoriality).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

open GenBr

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower

/-- `Spec A` is connected for a domain `A`. -/
instance preconnectedSpace_SX (A : Type) [CommRing A] [IsDomain A] : PreconnectedSpace (SX A) :=
  inferInstance

section Ext

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ]
  {V W : Type} [AddCommGroup V] [Module Λ V] [AddCommGroup W] [Module Λ W]
  (ρV : Representation Λ C.G V) (ρW : Representation Λ C.G W)

end Ext

section Full

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]
  (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)

variable (Λ : Type) [CommRing Λ] {V W : Type} [AddCommGroup V] [Module Λ V] [AddCommGroup W] [Module Λ W]
  (ρV : Representation Λ (coverOf A K L hL).G V) (ρW : Representation Λ (coverOf A K L hL).G W)

end Full

end RamanujanPetersson.EtSheaves.TorSec

end

end

-- ===== S4.Def_RP_EtCompact_FVExact =====
section

/-!
# S4-EtCompact, O9b part 3: `F_V` over one Galois cover is exact

For a finite Galois cover `C` of `Spec A` and equivariant maps `V₁ →ᶠ V₂ →ᵍ V₃` of `C.G`-representations:
* `FVMap_comp_eq_zero`: `g ∘ f = 0` gives `F(f) ≫ F(g) = 0`;
* **`FV_shortExact`**: if `0 → V₁ → V₂ → V₃ → 0` is exact, then `0 → F_{V₁} → F_{V₂} → F_{V₃} → 0` is a short
  exact sequence of etale sheaves (checked on every stalk: each geometric point lifts to the cover, and there the
  stalk sequence is the `V`-sequence).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ]
  {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module Λ V₁] [AddCommGroup V₂] [Module Λ V₂]
  [AddCommGroup V₃] [Module Λ V₃]
  (ρ₁ : Representation Λ C.G V₁) (ρ₂ : Representation Λ C.G V₂) (ρ₃ : Representation Λ C.G V₃)
  (f : V₁ →ₗ[Λ] V₂) (g : V₂ →ₗ[Λ] V₃) (hf : ∀ σ : C.G, f ∘ₗ ρ₁ σ = ρ₂ σ ∘ₗ f)
  (hg : ∀ σ : C.G, g ∘ₗ ρ₂ σ = ρ₃ σ ∘ₗ g)

variable (hinj : Function.Injective f) (hsurj : Function.Surjective g)
  (hex : LinearMap.range f = LinearMap.ker g)

include hex in
theorem comp_eq_zero_of_range_eq_ker : g ∘ₗ f = 0 := by
  refine LinearMap.ext fun v => ?_
  have : f v ∈ LinearMap.ker g := hex ▸ LinearMap.mem_range_self f v
  exact this

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_SheafExt =====
section

/-!
# S4-EtCompact, O9b part 4: comparing extensions of `Λ_X` by lisse sheaves on `Spec A`

* `isRepExt_stalk`: the stalk at `x̄` of a short exact `0 → G → P → Λ_X → 0` is an extension of Galois
  representations (`unitCoord : (Λ_X)_x̄ ≅ Λ`);
* `extMap` (algebra): the map of extensions over `u : M₁ → M₂` in the coordinates `extIso`, with
  `extMap_equivariant`, `extMap_i`, `extMap_w`;
* `Realizes c f g w`: `w` lifts `1` and `σ w - w = f (c σ)` at the generic stalk;
* **`extClass_comp_eq`**: if `S₁` realizes `c₁`, `S₂` realizes `c₂` (`S₂` lisse in the middle) and `u_η̄ ∘ c₁ = c₂`,
  then `[S₁] ∘ u = [S₂]` in `Ext¹(Λ_X, G₂)`;
* `exists_iso_of_stalk`: lisse sheaves with equivariantly isomorphic generic stalks are isomorphic, with the given
  stalk map.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr RamanujanPetersson.EtSheaves.TorSec

universe u

section Alg

variable {Λ : Type*} [CommRing Λ] {G : Type*} [Group G] {M₁ M₂ E₁ E₂ : Type*} [AddCommGroup M₁] [Module Λ M₁]
  [AddCommGroup M₂] [Module Λ M₂] [AddCommGroup E₁] [Module Λ E₁] [AddCommGroup E₂] [Module Λ E₂]
  {ρ₁ : Representation Λ G M₁} {ρ₂ : Representation Λ G M₂} {ρE₁ : Representation Λ G E₁}
  {ρE₂ : Representation Λ G E₂} {i₁ : M₁ →ₗ[Λ] E₁} {i₂ : M₂ →ₗ[Λ] E₂} {p₁ : E₁ →ₗ[Λ] Λ} {p₂ : E₂ →ₗ[Λ] Λ}

theorem extRep_prodMap {c₁ : G → M₁} {c₂ : G → M₂} (hc₁ : IsCocycle ρ₁ c₁) (hc₂ : IsCocycle ρ₂ c₂)
    (u : M₁ →ₗ[Λ] M₂) (hu : ∀ g, u ∘ₗ ρ₁ g = ρ₂ g ∘ₗ u) (huc : ∀ g, u (c₁ g) = c₂ g) (g : G) (v : M₁ × Λ) :
    LinearMap.prodMap u LinearMap.id (extRep ρ₁ c₁ hc₁ g v) =
      extRep ρ₂ c₂ hc₂ g (LinearMap.prodMap u LinearMap.id v) := by
  have h1 : u (ρ₁ g v.1) = ρ₂ g (u v.1) := LinearMap.congr_fun (hu g) v.1
  rw [extRep_apply, extRep_apply]
  refine Prod.ext ?_ rfl
  simp only [LinearMap.prodMap_apply, LinearMap.id_apply, map_add, map_smul, huc, h1]

variable (h₁ : IsRepExt ρ₁ ρE₁ i₁ p₁) (w₁ : E₁) (hw₁ : p₁ w₁ = 1) (h₂ : IsRepExt ρ₂ ρE₂ i₂ p₂) (w₂ : E₂)
  (hw₂ : p₂ w₂ = 1) (u : M₁ →ₗ[Λ] M₂)

theorem extIsoFun_self : extIsoFun h₁ w₁ hw₁ w₁ = (0, 1) := by
  refine Prod.ext (h₁.inj ?_) hw₁
  rw [i_extIsoFun_fst, hw₁, one_smul, sub_self]
  exact (map_zero i₁).symm

/-- The map of extensions `E₁ → E₂` over `u`, in the coordinates `extIso`. -/
def extMap : E₁ →ₗ[Λ] E₂ :=
  (extIso h₂ w₂ hw₂).symm.toLinearMap ∘ₗ LinearMap.prodMap u LinearMap.id ∘ₗ (extIso h₁ w₁ hw₁).toLinearMap

theorem extIso_extMap (v : E₁) :
    extIso h₂ w₂ hw₂ (extMap h₁ w₁ hw₁ h₂ w₂ hw₂ u v) = LinearMap.prodMap u LinearMap.id (extIso h₁ w₁ hw₁ v) := by
  simp only [extMap, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

theorem extMap_equivariant (hu : ∀ g, u ∘ₗ ρ₁ g = ρ₂ g ∘ₗ u)
    (huc : ∀ g, u (extCocycle h₁ w₁ g) = extCocycle h₂ w₂ g) (g : G) (v : E₁) :
    extMap h₁ w₁ hw₁ h₂ w₂ hw₂ u (ρE₁ g v) = ρE₂ g (extMap h₁ w₁ hw₁ h₂ w₂ hw₂ u v) := by
  apply (extIso h₂ w₂ hw₂).injective
  rw [extIso_extMap, extIso_apply h₂ w₂ hw₂ (ρE₂ g _), extIsoFun_equivariant h₂ w₂ hw₂ g,
    ← extIso_apply h₂ w₂ hw₂, extIso_extMap, extIso_apply h₁ w₁ hw₁ (ρE₁ g v), extIsoFun_equivariant h₁ w₁ hw₁ g,
    ← extIso_apply h₁ w₁ hw₁]
  exact extRep_prodMap _ _ u hu huc g _

theorem extMap_i (m : M₁) : extMap h₁ w₁ hw₁ h₂ w₂ hw₂ u (i₁ m) = i₂ (u m) := by
  apply (extIso h₂ w₂ hw₂).injective
  rw [extIso_extMap, extIso_apply h₁ w₁ hw₁, extIsoFun_i, extIso_apply h₂ w₂ hw₂, extIsoFun_i]
  rfl

theorem extMap_w : extMap h₁ w₁ hw₁ h₂ w₂ hw₂ u w₁ = w₂ := by
  apply (extIso h₂ w₂ hw₂).injective
  rw [extIso_extMap, extIso_apply h₁ w₁ hw₁, extIsoFun_self, extIso_apply h₂ w₂ hw₂, extIsoFun_self]
  simp

end Alg

section General

variable {X : Scheme.{u}} (Λ : Type u) [CommRing Λ] (x : X)

/-- The coordinate `(Λ_X)_x̄ ≅ Λ`. -/
abbrev unitCoord : stalk Λ (unitSh Λ X) x →ₗ[Λ] Λ :=
  (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom

theorem unitCoord_oneStalk : unitCoord Λ x (oneStalk Λ x) = 1 := by
  show ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv ≫
    (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom).hom (1 : Λ) = 1
  rw [Iso.inv_hom_id]
  rfl

theorem unitCoord_injective : Function.Injective (unitCoord Λ x) := fun a b h => by
  have h' := congrArg (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv.hom h
  change ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom ≫
      (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv).hom a =
    ((constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom ≫
      (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).inv).hom b at h'
  rwa [Iso.hom_inv_id] at h'

variable {Λ}

/-- **The stalk of `0 → G → P → Λ_X → 0` is an extension of Galois representations.** -/
theorem isRepExt_stalk {G P : EtSh Λ X} {f : G ⟶ P} {g : P ⟶ unitSh Λ X} {hfg : f ≫ g = 0}
    (hS : (ShortComplex.mk f g hfg).ShortExact) :
    IsRepExt (galRep Λ G x) (galRep Λ P x) (((geomPtAt x).stalkF Λ).map f).hom
      (unitCoord Λ x ∘ₗ (((geomPtAt x).stalkF Λ).map g).hom) where
  inj := (ModuleCat.mono_iff_injective _).1 ((mono_iff_stalk Λ f).1 hS.mono_f x)
  exact := by
    have hex := (exact_iff_stalk Λ _).1 hS.exact x
    have hz : (((geomPtAt x).stalkF Λ).map g).hom ∘ₗ (((geomPtAt x).stalkF Λ).map f).hom = 0 := by
      rw [← ModuleCat.hom_comp, ← Functor.map_comp, hfg, Functor.map_zero, ModuleCat.hom_zero]
    have hk : LinearMap.ker (unitCoord Λ x ∘ₗ (((geomPtAt x).stalkF Λ).map g).hom) =
        LinearMap.ker (((geomPtAt x).stalkF Λ).map g).hom := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.comp_apply]
      constructor
      · intro hv
        exact unitCoord_injective Λ x (hv.trans (map_zero _).symm)
      · intro hv
        rw [hv, map_zero]
    rw [hk]
    refine le_antisymm (LinearMap.range_le_ker_iff.2 hz) ?_
    rw [ShortComplex.moduleCat_exact_iff_ker_sub_range] at hex
    exact hex
  equiv_i σ := galRep_natural Λ f x σ
  equiv_p σ := by
    rw [LinearMap.comp_assoc, galRep_natural Λ g x σ, galRep_unitSh, LinearMap.id_comp]

end General

section Spec

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

/-- The generic stalk map of a sheaf map on `Spec A`. -/
abbrev gs {F G : EtSh Λ (Spec (CommRingCat.of A))} (φ : F ⟶ G) :
    stalk Λ F (genPt A) →ₗ[Λ] stalk Λ G (genPt A) :=
  (((geomPtAt (genPt A)).stalkF Λ).map φ).hom

/-- `(P, f, g, w)` **realizes the `π₁`-cocycle `c`**: `g_η̄ w = 1` and `σ w - w = f_η̄ (c σ)`. -/
structure Realizes {G P : EtSh Λ (Spec (CommRingCat.of A))} (c : Pi1 A K → stalk Λ G (genPt A))
    (f : G ⟶ P) (g : P ⟶ unitSh Λ (Spec (CommRingCat.of A))) (w : stalk Λ P (genPt A)) : Prop where
  one : gs A g w = oneStalk Λ (genPt A)
  coc : ∀ σ : Gal (genPt A), galRep Λ P (genPt A) σ w - w = gs A f (c (genToPi1 A K σ))

omit [IsIntegrallyClosed A] in
theorem gs_comp_apply {F G P : EtSh Λ (Spec (CommRingCat.of A))} (φ : F ⟶ G) (ψ : G ⟶ P)
    (v : stalk Λ F (genPt A)) : gs A (φ ≫ ψ) v = gs A ψ (gs A φ v) := by
  show (((geomPtAt (genPt A)).stalkF Λ).map (φ ≫ ψ)).hom v = _
  rw [Functor.map_comp]
  rfl

omit [IsIntegrallyClosed A] in
theorem gs_sub_apply {F G : EtSh Λ (Spec (CommRingCat.of A))} (φ ψ : F ⟶ G) (v : stalk Λ F (genPt A)) :
    gs A (φ - ψ) v = gs A φ v - gs A ψ v := by
  show (((geomPtAt (genPt A)).stalkF Λ).map (φ - ψ)).hom v = _
  rw [Functor.map_sub]
  rfl

variable [IsNoetherianRing A]

/-- **Comparison of extensions realizing cocycles** (`S₁` arbitrary, `S₂` with lisse middle term). -/
theorem extClass_comp_eq {G₁ G₂ P₁ P₂ : EtSh Λ (Spec (CommRingCat.of A))} (hG₁ : IsLisse Λ G₁)
    (hP₂ : IsLisse Λ P₂) {f₁ : G₁ ⟶ P₁} {g₁ : P₁ ⟶ unitSh Λ (Spec (CommRingCat.of A))} {hfg₁ : f₁ ≫ g₁ = 0}
    {f₂ : G₂ ⟶ P₂} {g₂ : P₂ ⟶ unitSh Λ (Spec (CommRingCat.of A))} {hfg₂ : f₂ ≫ g₂ = 0}
    (hS₁ : (ShortComplex.mk f₁ g₁ hfg₁).ShortExact) (hS₂ : (ShortComplex.mk f₂ g₂ hfg₂).ShortExact)
    {c₁ : Pi1 A K → stalk Λ G₁ (genPt A)} {c₂ : Pi1 A K → stalk Λ G₂ (genPt A)}
    {w₁ : stalk Λ P₁ (genPt A)} {w₂ : stalk Λ P₂ (genPt A)}
    (h₁ : Realizes A K c₁ f₁ g₁ w₁) (h₂ : Realizes A K c₂ f₂ g₂ w₂) (u : G₁ ⟶ G₂)
    (hu : ∀ τ, gs A u (c₁ τ) = c₂ τ) :
    (hS₁.extClass.comp (Abelian.Ext.mk₀ u) (add_zero 1) : H Λ G₂ 1) = hS₂.extClass := by
  have hR₁ := isRepExt_stalk (genPt A) hS₁
  have hR₂ := isRepExt_stalk (genPt A) hS₂
  have hw₁ : (unitCoord Λ (genPt A) ∘ₗ gs A g₁) w₁ = 1 := by
    rw [LinearMap.comp_apply, h₁.one, unitCoord_oneStalk]
  have hw₂ : (unitCoord Λ (genPt A) ∘ₗ gs A g₂) w₂ = 1 := by
    rw [LinearMap.comp_apply, h₂.one, unitCoord_oneStalk]
  have hc₁ : ∀ σ, extCocycle hR₁ w₁ σ = c₁ (genToPi1 A K σ) := fun σ =>
    hR₁.inj ((i_extCocycle hR₁ w₁ σ).trans (h₁.coc σ))
  have hc₂ : ∀ σ, extCocycle hR₂ w₂ σ = c₂ (genToPi1 A K σ) := fun σ =>
    hR₂.inj ((i_extCocycle hR₂ w₂ σ).trans (h₂.coc σ))
  have hT := extMap_equivariant hR₁ w₁ hw₁ hR₂ w₂ hw₂ (gs A u) (fun σ => galRep_natural Λ u (genPt A) σ)
    (fun σ => by rw [hc₁, hc₂, hu])
  obtain ⟨τ₂, hτ₂⟩ := EssSurj.full A hP₂ _ hT
  have hτ₂' : gs A τ₂ = extMap hR₁ w₁ hw₁ hR₂ w₂ hw₂ (gs A u) := hτ₂
  have h12 : f₁ ≫ τ₂ = u ≫ f₂ := stalk_faithful hG₁ hP₂.isLocConst (geomPtAt (genPt A)) (by
    rw [Functor.map_comp, Functor.map_comp]
    refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, hτ₂]
    exact extMap_i hR₁ w₁ hw₁ hR₂ w₂ hw₂ (gs A u) m)
  have := hS₁.epi_g
  have hd : f₁ ≫ (τ₂ ≫ g₂ - g₁) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, h12, Category.assoc, hfg₂, comp_zero, hfg₁, sub_zero]
  have hz : hS₁.exact.desc (τ₂ ≫ g₂ - g₁) hd = 0 := by
    refine stalk_faithful (isLisse_unitSh (Λ := Λ) (X := Spec (CommRingCat.of A)))
      (isLisse_unitSh (Λ := Λ) (X := Spec (CommRingCat.of A))).isLocConst (geomPtAt (genPt A)) ?_
    rw [Functor.map_zero]
    refine stalk_unitSh_hom_ext Λ (genPt A) ?_
    rw [ModuleCat.hom_zero, LinearMap.zero_apply, ← h₁.one]
    show gs A (hS₁.exact.desc (τ₂ ≫ g₂ - g₁) hd) (gs A g₁ w₁) = 0
    rw [← gs_comp_apply, hS₁.exact.g_desc, gs_sub_apply, gs_comp_apply, hτ₂', extMap_w, h₂.one, h₁.one, sub_self]
  have h23 : τ₂ ≫ g₂ = g₁ := by
    have h := hS₁.exact.g_desc (τ₂ ≫ g₂ - g₁) hd
    rw [hz, comp_zero] at h
    exact sub_eq_zero.1 h.symm
  let φ : ShortComplex.mk f₁ g₁ hfg₁ ⟶ ShortComplex.mk f₂ g₂ hfg₂ :=
    { τ₁ := u, τ₂ := τ₂, τ₃ := 𝟙 _, comm₁₂ := h12.symm, comm₂₃ := h23.trans (Category.comp_id _).symm }
  exact (hS₁.extClass_naturality hS₂ φ).trans (Abelian.Ext.mk₀_id_comp _)

/-- **Lisse sheaves with equivariantly isomorphic generic stalks are isomorphic**, with the given stalk map. -/
theorem exists_iso_of_stalk {F G : EtSh Λ (Spec (CommRingCat.of A))} (hF : IsLisse Λ F) (hG : IsLisse Λ G)
    (e : stalk Λ F (genPt A) ≅ stalk Λ G (genPt A))
    (he : ∀ (σ : Gal (genPt A)) (v : stalk Λ F (genPt A)),
      e.hom.hom (galRep Λ F (genPt A) σ v) = galRep Λ G (genPt A) σ (e.hom.hom v)) :
    ∃ E : F ≅ G, gs A E.hom = e.hom.hom := by
  have hinv : ∀ (σ : Gal (genPt A)) (w : stalk Λ G (genPt A)),
      e.inv.hom (galRep Λ G (genPt A) σ w) = galRep Λ F (genPt A) σ (e.inv.hom w) := by
    intro σ w
    have h := he σ (e.inv.hom w)
    rw [iso_inv_hom_apply] at h
    rw [← h, iso_hom_inv_apply]
  obtain ⟨φ, hφ⟩ := EssSurj.full A hG e.hom.hom he
  obtain ⟨ψ, hψ⟩ := EssSurj.full A hF e.inv.hom hinv
  let s := geomPtAt (genPt A)
  have h1 : φ ≫ ψ = 𝟙 F := stalk_faithful hF hF.isLocConst s (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    show ((s.stalkF Λ).map ψ).hom (((s.stalkF Λ).map φ).hom v) = v
    rw [hφ, hψ]
    exact iso_hom_inv_apply Λ e v)
  have h2 : ψ ≫ φ = 𝟙 G := stalk_faithful hG hG.isLocConst s (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    refine ModuleCat.hom_ext (LinearMap.ext fun w => ?_)
    show ((s.stalkF Λ).map φ).hom (((s.stalkF Λ).map ψ).hom w) = w
    rw [hφ, hψ]
    exact iso_inv_hom_apply Λ e w)
  exact ⟨⟨φ, ψ, h1, h2⟩, hφ⟩

end Spec

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_Kappa =====
section

/-!
# S4-EtCompact, O9b part 5: the extension class `κ(c) ∈ H¹(Spec A, G)` of a `π₁`-cocycle

`A` noetherian integrally closed domain, `G` lisse on `Spec A` with fibre representation `ρ = fibRep G` of
`π₁ = Pi1 A K` on `M = G_η̄`, `c` a continuous (locally constant) 1-cocycle.
* `nonempty_realExt`: there is a short exact `0 → G → P → Λ_X → 0` with lisse `P` realizing `c` (`P = F_V` for the
  extension representation `V = M × Λ` of `extRep ρ c` over one Galois cover, `G ≅ F_M`, `Λ_X ≅ F_Λ`);
* `kappa`: its class; **`kappa_eq`**: every short exact sequence realizing `c` has class `κ(c)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin GalCover.grp GalCover.fG GalCover.act GalCover.gal

theorem modIso_injective {Λ : Type} [CommRing Λ] {M N : ModuleCat.{0} Λ} (e : M ≅ N) :
    Function.Injective e.hom.hom := fun a b h => by
  have h' := congrArg e.inv.hom h
  rwa [iso_hom_inv_apply, iso_hom_inv_apply] at h'

/-- `(a ≪≫ b⁻¹)(a⁻¹ u) = b⁻¹ u` (generic: keeps concrete sheaf isomorphisms out of `rw`). -/
theorem trans_symm_inv_apply {Λ : Type} [CommRing Λ] {M N P : ModuleCat.{0} Λ} (a : M ≅ N) (b : P ≅ N) (u : N) :
    (a ≪≫ b.symm).hom.hom (a.inv.hom u) = b.inv.hom u := by
  rw [Iso.trans_hom, ModuleCat.hom_comp, LinearMap.comp_apply, iso_inv_hom_apply, Iso.symm_hom]

/-- The cocycle identity of `w = F⁻¹(0, 1)` in an extension representation, generically. -/
theorem coc_aux {Λ : Type} [CommRing Λ] {Pi : Type} [Group Pi] {M : Type} [AddCommGroup M] [Module Λ M]
    {N : ModuleCat.{0} Λ} (F : N ≅ ModuleCat.of Λ (M × Λ)) (gal : N →ₗ[Λ] N) (ρ : Representation Λ Pi M)
    (c : Pi → M) (hc : IsCocycle ρ c) (τ : Pi)
    (hgal : ∀ n, F.hom.hom (gal n) = extRep ρ c hc τ (F.hom.hom n)) (w : N)
    (hw : F.hom.hom w = ((0 : M), (1 : Λ))) (y : N) (hy : F.hom.hom y = LinearMap.inl Λ M Λ (c τ)) :
    gal w - w = y := by
  apply modIso_injective F
  rw [map_sub, hgal, hw, hy, extRep_apply]
  refine Prod.ext ?_ ?_ <;> simp

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] {Λ : Type} [CommRing Λ]

omit [IsIntegrallyClosed A] in
theorem gs_id_apply {F : EtSh Λ (Spec (CommRingCat.of A))} (v : stalk Λ F (genPt A)) : gs A (𝟙 F) v = v := by
  show (((geomPtAt (genPt A)).stalkF Λ).map (𝟙 F)).hom v = v
  rw [CategoryTheory.Functor.map_id]
  rfl

omit [IsIntegrallyClosed A] in
theorem gs_inv_hom_apply {F G : EtSh Λ (Spec (CommRingCat.of A))} (E : F ≅ G) (v : stalk Λ F (genPt A)) :
    gs A E.inv (gs A E.hom v) = v := by
  rw [← gs_comp_apply, E.hom_inv_id, gs_id_apply]

omit [IsIntegrallyClosed A] in
theorem exists_cIso : ∃ e : stalk Λ (unitSh Λ (Spec (CommRingCat.of A))) (genPt A) ≅ ModuleCat.of Λ Λ,
    e = constStalkIso Λ (geomPtAt (genPt A)) (ModuleCat.of Λ Λ) := ⟨_, rfl⟩

variable [IsNoetherianRing A]

variable {A K}
variable (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)

section SIso

variable {V W : Type} [AddCommGroup V] [Module Λ V] [AddCommGroup W] [Module Λ W]

end SIso

variable (A K)

end RamanujanPetersson.EtCompact

end

end

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

omit [IsIntegrallyClosed A] in
theorem gs_add_apply {F G : EtSh Λ (Spec (CommRingCat.of A))} (φ ψ : F ⟶ G) (v : stalk Λ F (genPt A)) :
    gs A (φ + ψ) v = gs A φ v + gs A ψ v := by
  show (((geomPtAt (genPt A)).stalkF Λ).map (φ + ψ)).hom v = _
  rw [CategoryTheory.Functor.map_add, ModuleCat.hom_add, LinearMap.add_apply]

omit [IsIntegrallyClosed A] in
theorem gs_zero_apply {F G : EtSh Λ (Spec (CommRingCat.of A))} (v : stalk Λ F (genPt A)) :
    gs A (0 : F ⟶ G) v = 0 := by
  show (((geomPtAt (genPt A)).stalkF Λ).map (0 : F ⟶ G)).hom v = 0
  rw [CategoryTheory.Functor.map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- Stalk maps intertwine the fibre representations. -/
theorem fibRep_natural {F G : EtSh Λ (Spec (CommRingCat.of A))} (hF : IsLisse Λ F) (hG : IsLisse Λ G)
    (φ : F ⟶ G) (τ : Pi1 A K) (v : stalk Λ F (genPt A)) :
    gs A φ (EssSurj.fibRep A K F hF τ v) = EssSurj.fibRep A K G hG τ (gs A φ v) := by
  obtain ⟨σ, rfl⟩ := genToPi1_surjective A K τ
  rw [EssSurj.fibRep_genToPi1, EssSurj.fibRep_genToPi1]
  exact LinearMap.congr_fun (galRep_natural Λ φ (genPt A) σ) v

variable [IsNoetherianRing A]

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

/-- The swap `X₀ ↔ X₁`. -/
abbrev swapP : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K := rename (Equiv.swap (0 : Fin 2) 1)

end Chart1

section Cover

variable (K : Type u) [Field K]

end Cover

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_PicDescent_D2 =====
section

/-!
# S4-PicDescent, part D2: unramified Dedekind extensions, generic

* `A → B` Dedekind, finite, torsion free, formally unramified (`B ≅ A ⊗ L` for a separable `L`):
  every place `w` of `B` has ramification index `1` over `w.under A`, so
  `valuation_under : (w.under A).valuation K x = w.valuation L x'` (orders agree);
  the fibre over `v` is finite and nonempty, `Σ_{w | v} f(w|v) = [B : A]`, `#(A/v)^f = #(B/w)`.
* `pullH σ w = σ⁻¹(w)` for a ring automorphism `σ` of `B`: `valuation_pullH`
  (`(σ⁻¹ w).valuation x = w.valuation (σ x)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson.PicDescent

section Unram

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]

instance liesOver_under' (w : HeightOneSpectrum B) : w.asIdeal.LiesOver (w.under A).asIdeal := ⟨rfl⟩

end Unram

section Equiv

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

end Equiv

end RamanujanPetersson.PicDescent


end


