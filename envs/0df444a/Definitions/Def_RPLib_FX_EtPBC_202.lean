-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_202
-- name    : RPLib_FX_EtPBC_202
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:15:59.821487+00:00
-- url     : https://prove2.me/theorems/527d7eef-334c-561b-93e5-efbcd8dd9978
-- title:
--   Proper base change for the projective line, library file 202
-- statement:
--   File 202 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovEt1`: S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`
--   * `S4.Def_RP_EtPBC_A_CovEtA`: S4-EtPBC-A, R4-T2 (A2c-5, E4c): the completed charts are etale
--   * `S4.Def_RP_EtPBC_A_CovAs6e`: S4-EtPBC-A, R4-T2 (A3 assembly, As6e): the lift from a completed cover and an approximation property
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_182
import Definitions.Def_RPLib_FX_EtPBC_198

/-!
# Proper base change for the projective line, library file 202

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovEt1`: S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`
* `S4.Def_RP_EtPBC_A_CovEtA`: S4-EtPBC-A, R4-T2 (A2c-5, E4c): the completed charts are etale
* `S4.Def_RP_EtPBC_A_CovAs6e`: S4-EtPBC-A, R4-T2 (A3 assembly, As6e): the lift from a completed cover and an approximation property
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovEt1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`

* **`et_near₁`**: there is `s ∈ Ê₁` with `s ≡ 1 mod J₁ Ê₁` and `Ê₁[1/s]` etale over `B₁` (via `β₁`); mirror of
  `et_near₀` (CovEt). Flatness of `Ê₁ ⧸ J₁^(k+1)` over `B₁ ⧸ J₁^(k+1)` comes from `θ₁ k` (`fq_flat`), freeness near `V(J₁)` from the
  local criterion (`lf_mem_freeLocus`), the unit `r` killing `Ω` from `unr_elt`, and etaleness from `et_gen` (CovEt).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Et₁

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))

include hts in
/-- **`Ê₁` is etale over `B₁` on a basic open containing `V(J₁ Ê₁)`.** -/
theorem et_near₁ [IsNoetherianRing B₁] [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁) :
    letI := (β₁ C H hφ₀ hu₀).toAlgebra
    ∃ s : hE₁ C H, s - 1 ∈ J₁.map (β₁ C H hφ₀ hu₀) ∧ Algebra.Etale B₁ (Localization.Away s) := by
  letI := (β₁ C H hφ₀ hu₀).toAlgebra
  haveI : Module.Finite B₁ (hE₁ C H) :=
    β₁_finite C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil
  obtain ⟨g, hg1, hg⟩ := et_free₁ C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil hspl
  haveI : Algebra.FormallyUnramified B₁
      (hE₁ C H ⧸ (J₁ ^ (0 + 1)).map (algebraMap B₁ (hE₁ C H))) := hE₁_fu C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil
  exact et_gen J₁ g hg1 hg

end Et₁

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovEtA =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E4c): the completed charts are etale

* **`et_cov`**: for `p ≤ jacobson ⊥`, the structure maps `β₀ : B₀ → Ê₀` and `β₁ : B₁ → Ê₁` of the completed
  charts are etale. This is `glob_etale` (CovEtL) applied to `Ê₀`, `Ê₁`, `Ê`, with finiteness from `β₀_finite`,
  `β₁_finite` and etaleness near the closed fibre from `et_near₀` (CovEt), `et_near₁` (CovEt1).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section EtA

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

include hts in
/-- `et_near₁` with `J₁ Ê₁` written as `(p B₁) Ê₁`. -/
theorem et_cov_n₁ [IsNoetherianRing B₁] [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁) :
    letI := (β₁ C H hφ₀ hu₀).toAlgebra
    ∃ s : hE₁ C H, s - 1 ∈ (p.map ιB₁).map (β₁ C H hφ₀ hu₀) ∧
      Algebra.Etale B₁ (Localization.Away s) := by
  letI := (β₁ C H hφ₀ hu₀).toAlgebra
  obtain ⟨s, hs1, hse⟩ := et_near₁ C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil hspl
  refine ⟨s, ?_, hse⟩
  rw [← hJ₁]
  exact hs1

end EtA

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs6e =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As6e): the lift from a completed cover and an approximation property

* `ker_comp_equiv`: kernels along a ring isomorphism compatible with the structure maps.
* **`assemble`** (generic `S`, flat over `A`, with a residue `res : S →+* K` and an ideal `pI` it kills): if every
  finitely generated `C ≤ S` maps residually to an etale neighbourhood `(R', χ')` of `χ` (in the application
  `S = Â`, from `approxAlg`), then a completed cover over `S` of the shape of `hat_lift` gives a `CoverLift`.
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section KerEquiv

end KerEquiv

section Assemble

variable (K : Type u) [Field K] (A : Type u) [CommRing A] [Algebra K A] (χ : A →ₐ[K] K)

set_option maxHeartbeats 1600000 in
/-- **The lift** from a completed cover over `S` and the approximation property of `S`. -/
theorem assemble {S : Type u} [CommRing S] [Algebra A S] [Module.Flat A S] (res : S →+* K)
    (hres : ∀ a, res (algebraMap A S a) = χ a) (pI : Ideal S) (hp : ∀ x ∈ pI, res x = 0)
    (hAp : ∀ C : Subalgebra A S, C.FG → ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra A R')
      (_ : Algebra.Etale A R') (χ' : R' →+* K) (σ : C →ₐ[A] R'),
        (∀ a : A, χ' (algebraMap A R' a) = χ a) ∧ ∀ c, χ' (σ c) = res (c : S))
    {B₀ B₁ N : Type u} [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
    [CommRing B₁] [Algebra A[X] B₁] [Algebra A B₁] [IsScalarTower A A[X] B₁]
    [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N]
    (φ₀ : B₀ →ₐ[A[X]] N) (φ₁ : B₁ →ₐ[A] N)
    (hX : algebraMap A[X] N X * φ₁ (algebraMap A[X] B₁ X) = 1)
    (hs₀ : ∀ y : N, ∃ (k : ℕ) (a : B₀), algebraMap A[X] N X ^ k * y = φ₀ a)
    (hs₁ : ∀ y : N, ∃ (k : ℕ) (b : B₁), φ₁ (algebraMap A[X] B₁ X) ^ k * y = φ₁ b)
    (hk₀ : ∀ a, φ₀ a = 0 → ∃ k : ℕ, algebraMap A[X] B₀ X ^ k * a = 0)
    (hk₁ : ∀ b, φ₁ b = 0 → ∃ k : ℕ, algebraMap A[X] B₁ X ^ k * b = 0)
    {F₀ F₁ F₀₁ : Type u} [CommRing F₀] [CommRing F₁] [CommRing F₀₁] [Algebra K F₀] [Algebra K F₁]
    [Algebra K F₀₁] (β₀ : B₀ →+* F₀) (β₁ : B₁ →+* F₁) (β₀₁ : N →+* F₀₁)
    (hβ₀ : ∀ a : A, β₀ (algebraMap A B₀ a) = algebraMap K F₀ (χ a))
    (hβ₁ : ∀ a : A, β₁ (algebraMap A B₁ a) = algebraMap K F₁ (χ a))
    (hβ₀₁ : ∀ a : A, β₀₁ (algebraMap A N a) = algebraMap K F₀₁ (χ a))
    (φb₀ : F₀ →+* F₀₁) (φb₁ : F₁ →+* F₀₁) (hρ₀ : φb₀.comp β₀ = β₀₁.comp φ₀.toRingHom)
    (hρ₁ : φb₁.comp β₁ = β₀₁.comp φ₁.toRingHom)
    {E₀ E₁ E₀₁ : Type u} [CommRing E₀] [CommRing E₁] [CommRing E₀₁] [Algebra F₀ E₀] [Algebra F₁ E₁]
    [Algebra F₀₁ E₀₁] (ψ₀ : E₀ →+* E₀₁) (ψ₁ : E₁ →+* E₀₁)
    (hψ₀ : ψ₀.comp (algebraMap F₀ E₀) = (algebraMap F₀₁ E₀₁).comp φb₀)
    (hψ₁ : ψ₁.comp (algebraMap F₁ E₁) = (algebraMap F₀₁ E₀₁).comp φb₁)
    {Eh₀ Eh₁ Eh : Type u} [CommRing Eh₀] [CommRing Eh₁] [CommRing Eh]
    (b₀ : S ⊗[A] B₀ →+* Eh₀) (b₁ : S ⊗[A] B₁ →+* Eh₁) (bN : S ⊗[A] N →+* Eh) (q₀ : Eh₀ →+* Eh)
    (q₁ : Eh₁ →+* Eh) (θh₀ : Eh₀ →+* E₀) (θh₁ : Eh₁ →+* E₁) (θh : Eh →+* E₀₁)
    (hE : b₀.Etale ∧ b₁.Etale ∧ b₀.Finite ∧ b₁.Finite)
    (hQ : q₀.comp b₀ = bN.comp (bcS S (φ₀.restrictScalars A)) ∧ q₁.comp b₁ = bN.comp (bcS S φ₁) ∧
      IsAwayMap q₀ (b₀ ((1 : S) ⊗ₜ[A] algebraMap A[X] B₀ X)) ∧ IsAwayMap q₁ (b₁ ((1 : S) ⊗ₜ[A] algebraMap A[X] B₁ X)))
    (hS : Function.Surjective θh₀ ∧ Function.Surjective θh₁ ∧
      RingHom.ker θh₀ = pI.map (b₀.comp Algebra.TensorProduct.includeLeftRingHom) ∧
      RingHom.ker θh₁ = pI.map (b₁.comp Algebra.TensorProduct.includeLeftRingHom))
    (hC : θh.comp q₀ = ψ₀.comp θh₀ ∧ θh.comp q₁ = ψ₁.comp θh₁)
    (v₀ : ∀ (r : S) (b : B₀), θh₀ (b₀ (r ⊗ₜ b)) = algebraMap F₀ E₀ (algebraMap K F₀ (res r) * β₀ b))
    (v₁ : ∀ (r : S) (b : B₁), θh₁ (b₁ (r ⊗ₜ b)) = algebraMap F₁ E₁ (algebraMap K F₁ (res r) * β₁ b))
    (vN : ∀ (r : S) (n : N), θh (bN (r ⊗ₜ n)) = algebraMap F₀₁ E₀₁ (algebraMap K F₀₁ (res r) * β₀₁ n)) :
    Nonempty (CoverLift K A χ B₀ B₁ N φ₀ φ₁ F₀ F₁ F₀₁ β₀ β₁ β₀₁ E₀ E₁ E₀₁ ψ₀ ψ₁) := by
  obtain ⟨het₀, het₁, hfi₀, hfi₁⟩ := hE
  obtain ⟨hq₀, hq₁, aq₀, aq₁⟩ := hQ
  obtain ⟨sh₀, sh₁, kh₀, kh₁⟩ := hS
  obtain ⟨ch₀, ch₁⟩ := hC
  have hA₀ : IsAwayMap ((φ₀.restrictScalars A : B₀ →ₐ[A] N) : B₀ →+* N) (algebraMap A[X] B₀ X) :=
    away_A₀ φ₀ hs₀ hk₀
  have hA₁ : IsAwayMap (φ₁ : B₁ →+* N) (algebraMap A[X] B₁ X) := ⟨hs₁, hk₁⟩
  have hts := hts_hat φ₀ φ₁ S hX
  obtain ⟨C, hCfg, r₀, r₁, gC₀, gC₁, uC, vC, ⟨hJ₀, hF₀, hJ₁, hF₁⟩, H, E₀', E₁', EN, hE₀, hE₁, hEN, hX₀, hX₁⟩ :=
    desc_cover (φ₀.restrictScalars A) φ₁ (algebraMap A[X] B₀ X) (algebraMap A[X] B₁ X)
      (away_bc (S := S) _ _ hA₀) (away_bc (S := S) _ _ hA₁) (IsUnit.of_mul_eq_one _ hts)
      (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hts)) b₀ b₁ bN q₀ q₁ het₀ het₁ hfi₀ hfi₁ hq₀ hq₁ aq₀ aq₁
  obtain ⟨R', _, _, _, χ', σ, hχ', hσ⟩ := hAp C hCfg
  haveI : Module.Flat A R' := inferInstance
  have hsK : ∀ k : K, χ' (((algebraMap A R').comp (algebraMap K A)) k) = k := fun k => by
    rw [RingHom.comp_apply, hχ']
    exact χ.commutes k
  have hshK : ∀ k : K, res (((algebraMap A S).comp (algebraMap K A)) k) = k := fun k => by
    rw [RingHom.comp_apply, hres]
    exact χ.commutes k
  -- the two charts
  obtain ⟨θ'₀, hv₀, hs₀', hk₀', hc₀⟩ := chart_resid (χ : A →+* K) χ' res hres hχ' β₀ hβ₀ _ hsK _ hshK C.val σ hσ
    gC₀ (θh₀.comp (E₀' : _ →+* Eh₀)) (fun x b => (congrArg θh₀ (hE₀ (x ⊗ₜ b))).trans (v₀ x b)) (sh₀.comp E₀'.surjective)
    pI hp (by
      rw [Ideal.map_map]
      exact ker_comp_equiv E₀' ((algebraMap (S ⊗[A] B₀) (Pres (gmap (tvC B₀ C) gC₀))).comp
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B₀))
        (b₀.comp (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B₀))
        (fun a => hE₀ (Algebra.TensorProduct.includeLeftRingHom a)) θh₀ pI kh₀)
  obtain ⟨θ'₁, hv₁, hs₁', hk₁', hc₁⟩ := chart_resid (χ : A →+* K) χ' res hres hχ' β₁ hβ₁ _ hsK _ hshK C.val σ hσ
    gC₁ (θh₁.comp (E₁' : _ →+* Eh₁)) (fun x b => (congrArg θh₁ (hE₁ (x ⊗ₜ b))).trans (v₁ x b)) (sh₁.comp E₁'.surjective)
    pI hp (by
      rw [Ideal.map_map]
      exact ker_comp_equiv E₁' ((algebraMap (S ⊗[A] B₁) (Pres (gmap (tvC B₁ C) gC₁))).comp
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B₁))
        (b₁.comp (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B₁))
        (fun a => hE₁ (Algebra.TensorProduct.includeLeftRingHom a)) θh₁ pI kh₁)
  -- the overlap
  obtain ⟨κ', hκt, hκ⟩ : ∃ κ' : R' ⊗[A] N →+* E₀₁,
      (∀ (r : R') (n : N), κ' (r ⊗ₜ n) = algebraMap F₀₁ E₀₁ (algebraMap K F₀₁ (χ' r) * β₀₁ n)) ∧
      κ'.comp (tsC σ N) = ((θh.comp (EN : _ →+* Eh)).comp
        (algebraMap (S ⊗[A] N) (Pres (gmap (tvC N C) (gmap (bcC (φ₀.restrictScalars A) C) gC₀))))).comp
          (tvC N C) :=
    ⟨kap (χ : A →+* K) ((algebraMap F₀₁ E₀₁).comp (algebraMap K F₀₁)) ((algebraMap F₀₁ E₀₁).comp β₀₁)
      (fun a => congrArg (algebraMap F₀₁ E₀₁) (hβ₀₁ a)) χ' hχ',
      fun r n => (kap_tmul _ _ _ _ χ' hχ' r n).trans
        (map_mul (algebraMap F₀₁ E₀₁) (algebraMap K F₀₁ (χ' r)) (β₀₁ n)).symm,
      kap_comp_tsC _ _ _ _ σ χ' hχ' res hσ _
        (fun x n => (congrArg θh (hEN (x ⊗ₜ n))).trans ((vN x n).trans (map_mul (algebraMap F₀₁ E₀₁) (algebraMap K F₀₁ (res x)) (β₀₁ n))))⟩
  -- the overlap residue map `resid (tvC N C) (tsC σ N) _ _ κ' hκ`
  have hθa := resid_algebraMap (tvC N C) (tsC σ N) _ _ κ' hκ
  have hθX := resid_X (tvC N C) (tsC σ N) _ _ κ' hκ
  have hθm := resid_mk_map (tvC N C) (tsC σ N) _ _ κ' hκ
  -- compatibilities
  have hK₀ := phib_K (χ : A →+* K) (chi_surj K A χ) (φ₀.restrictScalars A) β₀ β₀₁ φb₀ hβ₀ hβ₀₁
    (fun b => RingHom.congr_fun hρ₀ b)
  have hK₁ := phib_K (χ : A →+* K) (chi_surj K A χ) φ₁ β₁ β₀₁ φb₁ hβ₁ hβ₀₁ (fun b => RingHom.congr_fun hρ₁ b)
  have cθ₀ := ctheta0 (φ₀.restrictScalars A) σ gC₀ θ'₀ (resid (tvC N C) (tsC σ N) _ _ κ' hκ) ψ₀ ?_ ?_
  rotate_left
  · intro x
    rw [hθa]
    exact fib_coeff χ' (φ₀.restrictScalars A) β₀ β₀₁ φb₀ ψ₀ (fun y => RingHom.congr_fun hψ₀ y)
      (fun b => RingHom.congr_fun hρ₀ b) hK₀ (θ'₀.comp (algebraMap _ _)) hv₀ κ' hκt x
  · intro j
    rw [comp_presMap_X _ _ gC₀ θ'₀ _ hc₀ j, hθX]
    have e := RingHom.congr_fun ch₀ (E₀' (Ideal.Quotient.mk _ (MvPolynomial.X j)))
    rw [RingHom.comp_apply, RingHom.comp_apply, hX₀ j] at e
    exact e.symm
  have cθ₁ := ctheta1 (φ₀.restrictScalars A) φ₁ σ gC₀ gC₁ uC vC H θ'₁ (resid (tvC N C) (tsC σ N) _ _ κ' hκ) ψ₁ ?_ ?_
  rotate_left
  · intro x
    rw [hθa]
    exact fib_coeff χ' φ₁ β₁ β₀₁ φb₁ ψ₁ (fun y => RingHom.congr_fun hψ₁ y)
      (fun b => RingHom.congr_fun hρ₁ b) hK₁ (θ'₁.comp (algebraMap _ _)) hv₁ κ' hκt x
  · intro j
    rw [comp_presMap_X _ _ gC₁ θ'₁ _ hc₁ j, hθm]
    have e := RingHom.congr_fun ch₁ (E₁' (Ideal.Quotient.mk _ (MvPolynomial.X j)))
    rw [RingHom.comp_apply, RingHom.comp_apply, hX₁ j] at e
    exact e.symm
  haveI := pres_finite_map (tsC σ B₀) gC₀ hF₀
  haveI := pres_finite_map (tsC σ B₁) gC₁ hF₁
  haveI := pres_etale_map (tsC σ B₀) gC₀ hJ₀
  haveI := pres_etale_map (tsC σ B₁) gC₁ hJ₁
  exact ⟨{
    R' := R', χ' := χ', hχ := hχ', E₀ := Pres (gmap (tsC σ B₀) gC₀), E₁ := Pres (gmap (tsC σ B₁) gC₁),
    E₀₁ := Pres (gmap (tsC σ N) (gmap (bcC (φ₀.restrictScalars A) C) gC₀)),
    ψ₀ := psi0 (φ₀.restrictScalars A) σ gC₀, ψ₁ := psi1 (φ₀.restrictScalars A) φ₁ σ gC₀ gC₁ uC vC H,
    hψ₀ := psi0_tmul (φ₀.restrictScalars A) σ gC₀, hψ₁ := psi1_tmul (φ₀.restrictScalars A) φ₁ σ gC₀ gC₁ uC vC H,
    aw₀ := psi0_away (φ₀.restrictScalars A) σ gC₀ _ hA₀,
    aw₁ := psi1_away (φ₀.restrictScalars A) φ₁ σ gC₀ gC₁ uC vC H _ hA₁,
    θ₀ := θ'₀, θ₁ := θ'₁, θ₀₁ := resid (tvC N C) (tsC σ N) _ _ κ' hκ, hθ₀ := hv₀, hθ₁ := hv₁,
    hθ₀₁ := fun r n => (hθa _).trans (hκt r n), sθ₀ := hs₀', sθ₁ := hs₁', kθ₀ := hk₀', kθ₁ := hk₁',
    cθ₀ := cθ₀, cθ₁ := cθ₁
  }⟩

end Assemble

end RamanujanPetersson.EtPBC.Cov

end

end


