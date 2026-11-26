-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_207
-- name    : RPLib_FX_EtPBC_207
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:19:17.787374+00:00
-- url     : https://prove2.me/theorems/f384a060-c0ce-516c-b05c-373e8ed43567
-- title:
--   Proper base change for the projective line, library file 207
-- statement:
--   File 207 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovEtA`: S4-EtPBC-A, R4-T2 (A2c-5, E4c): the completed charts are etale
--   * `S4.Def_RP_EtPBC_A_CovAs3b`: S4-EtPBC-A, R4-T2 (A3 assembly, As3b): the completed charts of the tower are finite etale
--   * `S4.Def_RP_EtPBC_A_CovAs3d`: S4-EtPBC-A, R4-T2 (A3 assembly, As3d): the completed cover as one existential package
--   * `S4.Def_RP_EtPBC_A_CovAs3f`: S4-EtPBC-A, R4-T2 (A3 assembly, As3f): the completed cover over `Â` from the `CoverLiftAt₂` data
--   * `S4.Def_RP_EtPBC_A_CovAs6f`: S4-EtPBC-A, R4-T2 (A3 assembly, As6f): the algebraic T2 from Artin approximation
--   * `S4.Def_RP_EtPBC_A_O1G1`: S4-EtPBC-A, O1 glue: **degree-1 base change on `P¹_S`**
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_ArtinApprox_04
import Definitions.Def_RPLib_FX_EtPBC_202

/-!
# Proper base change for the projective line, library file 207

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovEtA`: S4-EtPBC-A, R4-T2 (A2c-5, E4c): the completed charts are etale
* `S4.Def_RP_EtPBC_A_CovAs3b`: S4-EtPBC-A, R4-T2 (A3 assembly, As3b): the completed charts of the tower are finite etale
* `S4.Def_RP_EtPBC_A_CovAs3d`: S4-EtPBC-A, R4-T2 (A3 assembly, As3d): the completed cover as one existential package
* `S4.Def_RP_EtPBC_A_CovAs3f`: S4-EtPBC-A, R4-T2 (A3 assembly, As3f): the completed cover over `Â` from the `CoverLiftAt₂` data
* `S4.Def_RP_EtPBC_A_CovAs6f`: S4-EtPBC-A, R4-T2 (A3 assembly, As6f): the algebraic T2 from Artin approximation
* `S4.Def_RP_EtPBC_A_O1G1`: S4-EtPBC-A, O1 glue: **degree-1 base change on `P¹_S`**
-/

set_option autoImplicit false

set_option linter.defProp false

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

set_option maxHeartbeats 400000 in
/-- **The completed charts are etale over the charts**: `β₀ : B₀ → Ê₀` and `β₁ : B₁ → Ê₁` are etale. -/
def et_cov [IsNoetherianRing B₀] [IsNoetherianRing B₁] (hm : p ≤ Ideal.jacobson ⊥) [IsNoetherianRing R]
    [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁) :
    (β₀ C H hts hφ₁ hu₁).Etale ∧ (β₁ C H hφ₀ hu₀).Etale :=
  glob_etale ιB₀ ιB₁ φ₀ φ₁ t₀ t₁ hφ₀ hu₀ hφ₁ hu₁ hts hιB hB₀ hB₁ p hm (β₀ C H hts hφ₁ hu₁)
    (β₁ C H hφ₀ hu₀) (β C H hts hφ₀ hu₀ hφ₁ hu₁) (hψ₀ C H hts) (hψ₁ C H hts)
    (hψ₀_β₀ C H hts hφ₀ hu₀ hφ₁ hu₁) (hψ₁_β₁ C H hts hφ₀ hu₀ hφ₁ hu₁) (aw_hψ₀ C H hts hφ₁ hu₁)
    (aw_hψ₁ C H hts hφ₀ hu₀) (β₀_finite C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil)
    (β₁_finite C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil)
    (et_cov_n₀ C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil hspl)
    (et_cov_n₁ C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil hspl)

end EtA

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3b): the completed charts of the tower are finite etale

**`hat_et`**: for `C := tower .. C₀`, `H := towerHom .. C₀` over a noetherian `p`-precomplete base `R` with
`p ≤ jacobson ⊥` and `p = span (range α)`, the maps `β₀ : B₀ → Ê₀` and `β₁ : B₁ → Ê₁` are etale and finite
(`hat_pack` + `et_cov` + `β₀_finite` + `β₁_finite`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section HatEt

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] (φ₀ : B₀ →+* N)
  (φ₁ : B₁ →+* N) (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN)
  (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀) (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀))
  (hu₁ : IsUnit (φ₁ t₁)) (C₀ : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)
  (p : Ideal R)

set_option maxHeartbeats 400000 in
theorem hat_et [IsNoetherianRing B₀] [IsNoetherianRing B₁] [IsNoetherianRing R] [IsPrecomplete p R]
    (hm : p ≤ Ideal.jacobson ⊥) {g : ℕ} (α : Fin g → R) (hα : p = Ideal.span (Set.range α))
    (hts : φ₀ t₀ * φ₁ t₁ = 1) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) :
    (β₀ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀)
        (towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀) hts hφ₁ hu₁).Etale ∧
      (β₁ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀)
        (towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀) hφ₀ hu₀).Etale ∧
      (β₀ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀)
        (towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀) hts hφ₁ hu₁).Finite ∧
      (β₁ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀)
        (towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀) hφ₀ hu₀).Finite := by
  obtain ⟨D, hspl, hs, hfil⟩ :=
    hat_pack φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ ιB₀ ιB₁ p α hα hts hB₀ hιB hJ₀ hJ₁
  have hα' : ∀ i, α i ∈ p := fun i => by
    rw [hα]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨e₀, e₁⟩ := et_cov (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀)
    (towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀) ιB₀ ιB₁ p hts hφ₀ hu₀ hφ₁ hu₁ hm α hα' hιB hB₀ hB₁
    hJ₀ hJ₁ D hs hfil hspl
  exact ⟨e₀, e₁,
    β₀_finite (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀)
      (towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀) ιB₀ ιB₁ p hts hφ₁ hu₁ α hα' hιB hB₀ hB₁ hJ₀ hJ₁ D
      hspl hs hfil,
    β₁_finite (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀)
      (towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀) ιB₀ ιB₁ p hts hφ₀ hu₀ α hα' hιB hB₀ hB₁ hJ₀ hJ₁ D
      hspl hs hfil⟩

end HatEt

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3d =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3d): the completed cover as one existential package

**`hat_cov`**: for a level-0 cover `C₀` over a noetherian `p`-precomplete base `R` (`p ≤ jacobson ⊥`,
`p = span (range α)`), there are rings `Ê₀, Ê₁, Ê` with finite etale `B₀ → Ê₀`, `B₁ → Ê₁`, glued by away maps
`Êᵢ → Ê` over `N → Ê`, and surjections `θ̂ᵢ : Êᵢ ↠ C₀.Eᵢ` with kernel `p Êᵢ`, compatible with the gluing and with
the charts of `C₀` (the tower `tower .. C₀` stays hidden). `hat_cov_gen` is the same for any tower `C`, `H`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section HatCovGen

end HatCovGen

section HatCov

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] (φ₀ : B₀ →+* N)
  (φ₁ : B₁ →+* N) (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN)
  (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀) (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀))
  (hu₁ : IsUnit (φ₁ t₁)) (C₀ : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)
  (p : Ideal R)

include hφ₀ hφ₁ hu₀ hu₁ in
set_option maxHeartbeats 400000 in
/-- **The completed cover of `C₀`** as one existential package. -/
theorem hat_cov [IsNoetherianRing B₀] [IsNoetherianRing B₁] [IsNoetherianRing R] [IsPrecomplete p R]
    (hm : p ≤ Ideal.jacobson ⊥) {g : ℕ} (α : Fin g → R) (hα : p = Ideal.span (Set.range α))
    (hts : φ₀ t₀ * φ₁ t₁ = 1) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) :
    ∃ (Eh₀ Eh₁ Eh : Type u) (_ : CommRing Eh₀) (_ : CommRing Eh₁) (_ : CommRing Eh)
      (b₀ : B₀ →+* Eh₀) (b₁ : B₁ →+* Eh₁) (b : N →+* Eh) (q₀ : Eh₀ →+* Eh) (q₁ : Eh₁ →+* Eh)
      (θh₀ : Eh₀ →+* C₀.E₀) (θh₁ : Eh₁ →+* C₀.E₁) (θh : Eh →+* C₀.E),
      (b₀.Etale ∧ b₁.Etale ∧ b₀.Finite ∧ b₁.Finite) ∧
      (q₀.comp b₀ = b.comp φ₀ ∧ q₁.comp b₁ = b.comp φ₁ ∧ IsAwayMap q₀ (b₀ t₀) ∧ IsAwayMap q₁ (b₁ t₁)) ∧
      (Function.Surjective θh₀ ∧ Function.Surjective θh₁ ∧
        RingHom.ker θh₀ = p.map (b₀.comp ιB₀) ∧ RingHom.ker θh₁ = p.map (b₁.comp ιB₁)) ∧
      (θh.comp q₀ = C₀.ψ₀.comp θh₀ ∧ θh.comp q₁ = C₀.ψ₁.comp θh₁) ∧
      (θh₀.comp b₀ = C₀.a₀.comp (Ideal.Quotient.mk (J₀ ^ (0 + 1))) ∧
        θh₁.comp b₁ = C₀.a₁.comp (Ideal.Quotient.mk (J₁ ^ (0 + 1))) ∧
        θh.comp b = C₀.a.comp (Ideal.Quotient.mk (JN ^ (0 + 1)))) := by
  obtain ⟨D, -, hs, hfil⟩ :=
    hat_pack φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ ιB₀ ιB₁ p α hα hts hB₀ hιB hJ₀ hJ₁
  have hα' : ∀ i, α i ∈ p := fun i => by
    rw [hα]
    exact Ideal.subset_span ⟨i, rfl⟩
  exact hat_cov_gen (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀)
    (towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀) ιB₀ ιB₁ p hts hφ₀ hu₀ hφ₁ hu₁
    (hat_et φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ ιB₀ ιB₁ p hm α hα hts hιB hB₀ hB₁ hJ₀ hJ₁)
    (hat_sk (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀)
      (towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀) ιB₀ ιB₁ p hts hφ₀ hu₀ hφ₁ hu₁ α hα' hιB hB₀ hB₁
      hJ₀ hJ₁ D hs hfil)

end HatCov

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3f =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3f): the completed cover over `Â` from the `CoverLiftAt₂` data

**`hat_lift`**: under the hypotheses of `CoverLiftAt₂` (and `A` noetherian), there are rings `Ê₀, Ê₁, Ê` with
finite etale `Â ⊗ B₀ → Ê₀`, `Â ⊗ B₁ → Ê₁`, glued by away maps over `Â ⊗ N → Ê`, and surjections `θ̂ᵢ : Êᵢ ↠ Eᵢ`
with kernel `(ker χ) Êᵢ`, compatible with `ψᵢ` and with `r ⊗ b ↦ resHat r * βᵢ b`. (`hat_cov` over `R = Â`,
charts `Â ⊗ Bᵢ`, level-0 cover `baseG` with fibre charts `kap`.)
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section AwayA

end AwayA

section HatLift

variable (K : Type u) [Field K] (A : Type u) [CommRing A] [Algebra K A] (χ : A →ₐ[K] K)
  {B₀ B₁ N : Type u} [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
  [CommRing B₁] [Algebra A[X] B₁] [Algebra A B₁] [IsScalarTower A A[X] B₁]
  [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N]
  (φ₀ : B₀ →ₐ[A[X]] N) (φ₁ : B₁ →ₐ[A] N)

set_option maxHeartbeats 1000000 in
/-- **The completed cover over `Â`** from the data of `CoverLiftAt₂`. -/
theorem hat_lift [IsNoetherianRing A] [Module.Finite A[X] B₀] [Module.Finite A[X] B₁]
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
    (hβs₀ : Function.Surjective β₀) (hβs₁ : Function.Surjective β₁) (hβs₀₁ : Function.Surjective β₀₁)
    (hkβ₀ : RingHom.ker β₀ = (RingHom.ker χ).map (algebraMap A B₀))
    (hkβ₁ : RingHom.ker β₁ = (RingHom.ker χ).map (algebraMap A B₁))
    (hkβ₀₁ : RingHom.ker β₀₁ = (RingHom.ker χ).map (algebraMap A N))
    (φb₀ : F₀ →+* F₀₁) (φb₁ : F₁ →+* F₀₁) (hρ₀ : φb₀.comp β₀ = β₀₁.comp φ₀.toRingHom)
    (hρ₁ : φb₁.comp β₁ = β₀₁.comp φ₁.toRingHom)
    (E₀ E₁ E₀₁ : Type u) [CommRing E₀] [CommRing E₁] [CommRing E₀₁] [Algebra F₀ E₀] [Algebra F₁ E₁]
    [Algebra F₀₁ E₀₁] (het₀ : Algebra.Etale F₀ E₀) (het₁ : Algebra.Etale F₁ E₁) (hf₀ : Module.Finite F₀ E₀)
    (hf₁ : Module.Finite F₁ E₁) (ψ₀ : E₀ →+* E₀₁) (ψ₁ : E₁ →+* E₀₁)
    (hψ₀ : ψ₀.comp (algebraMap F₀ E₀) = (algebraMap F₀₁ E₀₁).comp φb₀)
    (hψ₁ : ψ₁.comp (algebraMap F₁ E₁) = (algebraMap F₀₁ E₀₁).comp φb₁)
    (aw₀ : IsAwayMap ψ₀ (algebraMap F₀ E₀ (β₀ (algebraMap A[X] B₀ X))))
    (aw₁ : IsAwayMap ψ₁ (algebraMap F₁ E₁ (β₁ (algebraMap A[X] B₁ X)))) :
    ∃ (Eh₀ Eh₁ Eh : Type u) (_ : CommRing Eh₀) (_ : CommRing Eh₁) (_ : CommRing Eh)
      (b₀ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* Eh₀) (b₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* Eh₁) (bN : (AdicCompletion (RingHom.ker χ) A) ⊗[A] N →+* Eh) (q₀ : Eh₀ →+* Eh)
      (q₁ : Eh₁ →+* Eh) (θh₀ : Eh₀ →+* E₀) (θh₁ : Eh₁ →+* E₁) (θh : Eh →+* E₀₁),
      (b₀.Etale ∧ b₁.Etale ∧ b₀.Finite ∧ b₁.Finite) ∧
      (q₀.comp b₀ = bN.comp (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) ∧ q₁.comp b₁ = bN.comp (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) φ₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) ∧ IsAwayMap q₀ (b₀ ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₀ X)) ∧ IsAwayMap q₁ (b₁ ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₁ X))) ∧
      (Function.Surjective θh₀ ∧ Function.Surjective θh₁ ∧
        RingHom.ker θh₀ = ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (b₀.comp (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀)) ∧ RingHom.ker θh₁ = ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (b₁.comp (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁))) ∧
      (θh.comp q₀ = ψ₀.comp θh₀ ∧ θh.comp q₁ = ψ₁.comp θh₁) ∧
      (∀ (r : (AdicCompletion (RingHom.ker χ) A)) (b : B₀), θh₀ (b₀ (r ⊗ₜ b)) = algebraMap F₀ E₀ (algebraMap K F₀ (resHat K A χ r) * β₀ b)) ∧
      (∀ (r : (AdicCompletion (RingHom.ker χ) A)) (b : B₁), θh₁ (b₁ (r ⊗ₜ b)) = algebraMap F₁ E₁ (algebraMap K F₁ (resHat K A χ r) * β₁ b)) ∧
      (∀ (r : (AdicCompletion (RingHom.ker χ) A)) (n : N), θh (bN (r ⊗ₜ n)) =
        algebraMap F₀₁ E₀₁ (algebraMap K F₀₁ (resHat K A χ r) * β₀₁ n)) := by
  have hp : (RingHom.ker χ).FG := Ideal.fg_of_isNoetherianRing _
  haveI : IsNoetherianRing (AdicCompletion (RingHom.ker χ) A) := hat_noeth _
  haveI : IsNoetherianRing ((AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀) := noeth_bc (A := A) (S := (AdicCompletion (RingHom.ker χ) A)) (B := B₀)
  haveI : IsNoetherianRing ((AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁) := noeth_bc (A := A) (S := (AdicCompletion (RingHom.ker χ) A)) (B := B₁)
  haveI : IsPrecomplete ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))) (AdicCompletion (RingHom.ker χ) A) := (hat_complete A (RingHom.ker χ) hp).toIsPrecomplete
  obtain ⟨g, α, hα, -⟩ := map_fin_gens (algebraMap A (AdicCompletion (RingHom.ker χ) A)) (RingHom.ker χ) hp
  have hχs := chi_surj K A χ
  have hβ₀' : ∀ a : A, β₀ (algebraMap A B₀ a) = algebraMap K F₀ ((χ : A →+* K) a) := hβ₀
  have hβ₁' : ∀ a : A, β₁ (algebraMap A B₁ a) = algebraMap K F₁ ((χ : A →+* K) a) := hβ₁
  have hβ₀₁' : ∀ a : A, β₀₁ (algebraMap A N a) = algebraMap K F₀₁ ((χ : A →+* K) a) := hβ₀₁
  have hres : ∀ a : A, resHat K A χ (algebraMap A (AdicCompletion (RingHom.ker χ) A) a) = (χ : A →+* K) a := resHat_algebraMap K A χ
  have hts : (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₀ X) * (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) φ₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₁ X) = 1 := hts_hat φ₀ φ₁ (AdicCompletion (RingHom.ker χ) A) hX
  have hu₀ : IsUnit ((Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₀ X)) := IsUnit.of_mul_eq_one _ hts
  have hu₁ : IsUnit ((Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) φ₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₁ X)) := IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hts)
  have hφ₀ : IsAwayMap (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₀ X) := away_bc (S := (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) _ (away_A₀ φ₀ hs₀ hk₀)
  have hφ₁ : IsAwayMap (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) φ₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₁ X) :=
    away_bc (S := (AdicCompletion (RingHom.ker χ) A)) φ₁ _ (⟨hs₁, hk₁⟩ : IsAwayMap (φ₁ : B₁ →+* N) (algebraMap A[X] B₁ X))
  have hιB : (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N).comp (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀) = (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) φ₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N).comp (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁) := (bc_inc (R' := (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A)).trans (bc_inc (R' := (AdicCompletion (RingHom.ker χ) A)) φ₁).symm
  have h₀ : (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀)).map (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) = ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) := by rw [Ideal.map_map, bc_inc]
  have h₁ : (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁)).map (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) φ₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) = ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) := by rw [Ideal.map_map, bc_inc]
  have hκ₀ : RingHom.ker (kap (χ : A →+* K) (algebraMap K F₀) β₀ hβ₀' (resHat K A χ) hres) = ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀) :=
    (ker_kap (χ : A →+* K) (algebraMap K F₀) β₀ hβ₀' (resHat K A χ) hres hχs hkβ₀).trans
      (congrArg (fun J => Ideal.map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀) J) (ker_resHat K A χ))
  have hκ₁ : RingHom.ker (kap (χ : A →+* K) (algebraMap K F₁) β₁ hβ₁' (resHat K A χ) hres) = ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁) :=
    (ker_kap (χ : A →+* K) (algebraMap K F₁) β₁ hβ₁' (resHat K A χ) hres hχs hkβ₁).trans
      (congrArg (fun J => Ideal.map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁) J) (ker_resHat K A χ))
  have hκN : RingHom.ker (kap (χ : A →+* K) (algebraMap K F₀₁) β₀₁ hβ₀₁' (resHat K A χ) hres) = ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) :=
    (ker_kap (χ : A →+* K) (algebraMap K F₀₁) β₀₁ hβ₀₁' (resHat K A χ) hres hχs hkβ₀₁).trans
      (congrArg (fun J => Ideal.map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) J) (ker_resHat K A χ))
  have hs₀' : Function.Surjective (kap (χ : A →+* K) (algebraMap K F₀) β₀ hβ₀' (resHat K A χ) hres) :=
    kap_surj (χ : A →+* K) (resHat K A χ) hres (algebraMap K F₀) β₀ hβ₀' hβs₀
  have hs₁' : Function.Surjective (kap (χ : A →+* K) (algebraMap K F₁) β₁ hβ₁' (resHat K A χ) hres) :=
    kap_surj (χ : A →+* K) (resHat K A χ) hres (algebraMap K F₁) β₁ hβ₁' hβs₁
  have hsN' : Function.Surjective (kap (χ : A →+* K) (algebraMap K F₀₁) β₀₁ hβ₀₁' (resHat K A χ) hres) :=
    kap_surj (χ : A →+* K) (resHat K A χ) hres (algebraMap K F₀₁) β₀₁ hβ₀₁' hβs₀₁
  have hρ₀' : φb₀.comp (kap (χ : A →+* K) (algebraMap K F₀) β₀ hβ₀' (resHat K A χ) hres) = (kap (χ : A →+* K) (algebraMap K F₀₁) β₀₁ hβ₀₁' (resHat K A χ) hres).comp (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) :=
    kap_comm (χ : A →+* K) (resHat K A χ) hres hχs β₀ β₀₁ hβ₀' hβ₀₁'
      (φ₀.restrictScalars A) φb₀ (fun b => RingHom.congr_fun hρ₀ b)
  have hρ₁' : φb₁.comp (kap (χ : A →+* K) (algebraMap K F₁) β₁ hβ₁' (resHat K A χ) hres) = (kap (χ : A →+* K) (algebraMap K F₀₁) β₀₁ hβ₀₁' (resHat K A χ) hres).comp (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) φ₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) :=
    kap_comm (χ : A →+* K) (resHat K A χ) hres hχs β₁ β₀₁ hβ₁' hβ₀₁' φ₁ φb₁
      (fun b => RingHom.congr_fun hρ₁ b)
  have aw₀' : IsAwayMap ψ₀ (algebraMap F₀ E₀ ((kap (χ : A →+* K) (algebraMap K F₀) β₀ hβ₀' (resHat K A χ) hres) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₀ X))) := by
    rw [kap_tmul, map_one, map_one, one_mul]
    exact aw₀
  have aw₁' : IsAwayMap ψ₁ (algebraMap F₁ E₁ ((kap (χ : A →+* K) (algebraMap K F₁) β₁ hβ₁' (resHat K A χ) hres) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₁ X))) := by
    rw [kap_tmul, map_one, map_one, one_mul]
    exact aw₁
  obtain ⟨Eh₀, Eh₁, Eh, i₀, i₁, i, b₀, b₁, bN, q₀, q₁, θh₀, θh₁, θh, het, hgl, hsk, hθψ, hθb₀, hθb₁, hθb⟩ :=
    hat_cov (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) φ₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀)) (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁)) (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N)) h₀ h₁ ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₀ X) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₁ X) hφ₀ hφ₁ hu₀ hu₁
      (baseG (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) (φ₀.restrictScalars A) : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) (Algebra.TensorProduct.map (AlgHom.id A (AdicCompletion (RingHom.ker χ) A)) φ₁ : (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁ →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N) (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀)) (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁)) (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N)) h₀ h₁ ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₀ X) ((1 : AdicCompletion (RingHom.ker χ) A) ⊗ₜ[A] algebraMap A[X] B₁ X) (kap (χ : A →+* K) (algebraMap K F₀) β₀ hβ₀' (resHat K A χ) hres) (kap (χ : A →+* K) (algebraMap K F₁) β₁ hβ₁' (resHat K A χ) hres) (kap (χ : A →+* K) (algebraMap K F₀₁) β₀₁ hβ₀₁' (resHat K A χ) hres) hs₀' hs₁' hsN' hκ₀ hκ₁ hκN
        φb₀ φb₁ hρ₀' hρ₁' E₀ E₁ E₀₁ het₀ het₁ hf₀ hf₁ ψ₀ ψ₁ hψ₀ hψ₁ aw₀' aw₁')
      (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀) (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁) ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))) (hat_jac A (RingHom.ker χ) hp) α hα hts hιB (fin_bc (A := A) (S := (AdicCompletion (RingHom.ker χ) A)) (B := B₀))
      (fin_bc (A := A) (S := (AdicCompletion (RingHom.ker χ) A)) (B := B₁)) rfl rfl
  refine ⟨Eh₀, Eh₁, Eh, i₀, i₁, i, b₀, b₁, bN, q₀, q₁, θh₀, θh₁, θh, het, hgl, hsk, hθψ,
    fun r b => ?_, fun r b => ?_, fun r n => ?_⟩
  · refine (RingHom.congr_fun hθb₀ (r ⊗ₜ b)).trans ?_
    show algebraMap F₀ E₀ (eqvG (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₀)) (kap (χ : A →+* K) (algebraMap K F₀) β₀ hβ₀' (resHat K A χ) hres) hs₀' hκ₀ (Ideal.Quotient.mk _ (r ⊗ₜ[A] b))) = _
    rw [eqvG_mk, kap_tmul]
  · refine (RingHom.congr_fun hθb₁ (r ⊗ₜ b)).trans ?_
    show algebraMap F₁ E₁ (eqvG (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] B₁)) (kap (χ : A →+* K) (algebraMap K F₁) β₁ hβ₁' (resHat K A χ) hres) hs₁' hκ₁ (Ideal.Quotient.mk _ (r ⊗ₜ[A] b))) = _
    rw [eqvG_mk, kap_tmul]
  · refine (RingHom.congr_fun hθb (r ⊗ₜ n)).trans ?_
    show algebraMap F₀₁ E₀₁ (eqvG (((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))).map (Algebra.TensorProduct.includeLeftRingHom : (AdicCompletion (RingHom.ker χ) A) →+* (AdicCompletion (RingHom.ker χ) A) ⊗[A] N)) (kap (χ : A →+* K) (algebraMap K F₀₁) β₀₁ hβ₀₁' (resHat K A χ) hres) hsN' hκN (Ideal.Quotient.mk _ (r ⊗ₜ[A] n))) = _
    rw [eqvG_mk, kap_tmul]

end HatLift

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs6f =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As6f): the algebraic T2 from Artin approximation

**`coverLiftAt₂_of_approx`**: for a noetherian `A` with a `K`-point `χ` at which Artin approximation holds
(`ArtinApproxAt K A χ`), every fibre cover of the shape of `CoverLiftAt₂` lifts. The completed cover over
`Â = AdicCompletion (ker χ) A` comes from `hat_lift`; `assemble` descends it with `approxAlg`.
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

variable (K : Type u) [Field K] (A : Type u) [CommRing A] [Algebra K A]

/-- **The algebraic T2 at `χ`** from Artin approximation at `χ`. -/
theorem coverLiftAt₂_of_approx [IsNoetherianRing A] (χ : A →ₐ[K] K) (hA : ArtinApproxAt K A χ) :
    CoverLiftAt₂ K A χ := by
  intro B₀ B₁ N _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ₀ φ₁ hX hs₀ hs₁ hk₀ hk₁ F₀ F₁ F₀₁ _ _ _ _ _ _ β₀ β₁ β₀₁ hβ₀ hβ₁ hβ₀₁
    hβs₀ hβs₁ hβs₀₁ hkβ₀ hkβ₁ hkβ₀₁ φb₀ φb₁ hρ₀ hρ₁ E₀ E₁ E₀₁ _ _ _ _ _ _ het₀ het₁ hf₀ hf₁ ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁
  obtain ⟨Eh₀, Eh₁, Eh, _, _, _, b₀, b₁, bN, q₀, q₁, θh₀, θh₁, θh, hE, hQ, hS, hC, v₀, v₁, vN⟩ :=
    hat_lift K A χ φ₀ φ₁ hX hs₀ hs₁ hk₀ hk₁ β₀ β₁ β₀₁ hβ₀ hβ₁ hβ₀₁ hβs₀ hβs₁ hβs₀₁ hkβ₀ hkβ₁ hkβ₀₁ φb₀ φb₁ hρ₀ hρ₁
      E₀ E₁ E₀₁ het₀ het₁ hf₀ hf₁ ψ₀ ψ₁ hψ₀ hψ₁ aw₀ aw₁
  refine assemble K A χ (resHat K A χ) (resHat_algebraMap K A χ)
    ((RingHom.ker χ).map (algebraMap A (AdicCompletion (RingHom.ker χ) A))) ?_ ?_ φ₀ φ₁ hX hs₀ hs₁ hk₀ hk₁
    β₀ β₁ β₀₁ hβ₀ hβ₁ hβ₀₁ φb₀ φb₁ hρ₀ hρ₁ ψ₀ ψ₁ hψ₀ hψ₁ b₀ b₁ bN q₀ q₁ θh₀ θh₁ θh hE hQ hS hC v₀ v₁ vN
  · intro x hx
    rw [← ker_resHat K A χ] at hx
    exact RingHom.mem_ker.mp hx
  · intro C hC
    haveI : Algebra.FiniteType A C := (Subalgebra.fg_iff_finiteType C).mp hC
    exact approxAlg K A χ hA C C.val

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O1G1 =====
section

/-!
# S4-EtPBC-A, O1 glue: **degree-1 base change on `P¹_S`**

* `coverLiftAt₂_ft`: `CoverLiftAt₂` for a finite-type algebra over a perfect field (Artin approximation `artinApproxAt`
  fed into `coverLiftAt₂_of_approx`);
* `liftT_qV`: the lifting property `LiftT (qV K gK) s π` for every finite `π : Y ⟶ P¹_S`, from an affine noetherian
  etale neighbourhood of `s`;
* **`bcSurj_one_PV`**: `BCSurj 1` for every sheaf on `P¹_S` at a geometric point `s` with `s ≫ g_K` an isomorphism
  (`S` noetherian, locally of finite type over a perfect field `K`, `Λ` finite noetherian).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

/-- `CoverLiftAt₂` for a finite-type algebra over a perfect field. -/
theorem coverLiftAt₂_ft {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A] [PerfectField K]
    [Algebra.FiniteType K A] (χ : A →ₐ[K] K) : CoverLiftAt₂ K A χ := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  exact coverLiftAt₂_of_approx K A χ (artinApproxAt χ)

end RamanujanPetersson.EtPBC.Cov

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.Cov

universe u

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S)
  [IsIso (s.pt ≫ gK)]

/-- **`LiftT` for `qV`**: every finite `π : Y ⟶ P¹_S` has the lifting property at `s`. -/
theorem liftT_qV [PerfectField K] [IsLocallyNoetherian S] [LocallyOfFiniteType gK] {Y : Scheme.{u}}
    (π : Y ⟶ PV K gK) [IsFinite π] : T2.LiftT (qV K gK) s π := by
  obtain ⟨j, hA, -⟩ := exists_affine_nbhd s
  haveI : IsAffine j.1.left := hA
  haveI : Etale (nbh s j) := j.1.prop
  letI := algKV K (nbh s j ≫ gK)
  haveI : Algebra.FiniteType K Γ(j.1.left, ⊤) := finiteType_algKV K (nbh s j ≫ gK)
  exact liftT_of_coverLiftAt₂ K gK s π (nbh s j) (nbv s j) (nbv_w s j) (coverLiftAt₂_ft _)

end RamanujanPetersson.EtPBC

end

end


