-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_198
-- name    : RPLib_FX_EtPBC_198
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:10:46.165806+00:00
-- url     : https://prove2.me/theorems/3d0365f1-2679-54a7-9eb5-54fe741c472f
-- title:
--   Proper base change for the projective line, library file 198
-- statement:
--   File 198 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
--   * `S4.Def_RP_EtPBC_A_CovEt1`: S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`
--   * `S4.Def_RP_EtPBC_A_CovEtA`: S4-EtPBC-A, R4-T2 (A2c-5, E4c): the completed charts are etale
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_186
import Definitions.Def_RPLib_FX_EtPBC_191

/-!
# Proper base change for the projective line, library file 198

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
* `S4.Def_RP_EtPBC_A_CovEt1`: S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`
* `S4.Def_RP_EtPBC_A_CovEtA`: S4-EtPBC-A, R4-T2 (A2c-5, E4c): the completed charts are etale
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_CovEt =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`

* **`et_near₀`**: there is `s ∈ Ê₀` with `s ≡ 1 mod J₀ Ê₀` and `Ê₀[1/s]` etale over `B₀` (via `β₀`).
  Flatness of `Ê₀ ⧸ J₀^(k+1)` over `B₀ ⧸ J₀^(k+1)` comes from `θ₀ k` (`fq_flat`), freeness near `V(J₀)` from the
  local criterion (`lf_mem_freeLocus`), the unit `r` killing `Ω` from `unr_elt`, and etaleness from `fq_etale` (`et_gen`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Et₀

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- **`Ê₀` is etale over `B₀` on a basic open containing `V(J₀ Ê₀)`.** -/
def et_near₀ [IsNoetherianRing B₀] [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁) :
    letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
    ∃ s : hE₀ C H hts, s - 1 ∈ J₀.map (β₀ C H hts hφ₁ hu₁) ∧ Algebra.Etale B₀ (Localization.Away s) := by
  letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
  haveI : Module.Finite B₀ (hE₀ C H hts) :=
    β₀_finite C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil
  obtain ⟨g, hg1, hg⟩ := et_free₀ C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil hspl
  haveI : Algebra.FormallyUnramified B₀
      (hE₀ C H hts ⧸ (J₀ ^ (0 + 1)).map (algebraMap B₀ (hE₀ C H hts))) := hE₀_fu C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil
  exact et_gen J₀ g hg1 hg

end Et₀

end RamanujanPetersson.EtPBC.Cov

end

end

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
/-- A basic open `D(g)`, `g ≡ 1 mod J₁`, inside the free locus of `Ê₁`. -/
theorem et_free₁ [IsNoetherianRing B₁] [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁) :
    letI := (β₁ C H hφ₀ hu₀).toAlgebra
    ∃ g : B₁, g - 1 ∈ J₁ ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B₁)) ⊆ Module.freeLocus B₁ (hE₁ C H) := by
  letI := (β₁ C H hφ₀ hu₀).toAlgebra
  haveI : Module.Finite B₁ (hE₁ C H) :=
    β₁_finite C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil
  haveI : Module.FinitePresentation B₁ (hE₁ C H) :=
    Module.finitePresentation_of_finite (R := B₁) (M := hE₁ C H)
  have hfl := hE₁_flat C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil
  exact fq_basicOpen J₁ (Module.freeLocus B₁ (hE₁ C H)) Module.isOpen_freeLocus
    (fun q hq => lf_mem_freeLocus J₁ hfl q (fun x hx => (PrimeSpectrum.mem_zeroLocus _ _).1 hq hx))

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

/-- `et_near₀` with `J₀ Ê₀` written as `(p B₀) Ê₀`. -/
theorem et_cov_n₀ [IsNoetherianRing B₀] [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁) :
    letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
    ∃ s : hE₀ C H hts, s - 1 ∈ (p.map ιB₀).map (β₀ C H hts hφ₁ hu₁) ∧
      Algebra.Etale B₀ (Localization.Away s) := by
  letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
  obtain ⟨s, hs1, hse⟩ := et_near₀ C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil hspl
  refine ⟨s, ?_, hse⟩
  rw [← hJ₀]
  exact hs1

end EtA

end RamanujanPetersson.EtPBC.Cov

end

end


