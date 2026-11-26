-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_181
-- name    : RPLib_FX_EtPBC_181
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:25:56.464804+00:00
-- url     : https://prove2.me/theorems/ec4e2a8a-64b0-5bfa-a58e-f106e9474469
-- title:
--   Proper base change for the projective line, library file 181
-- statement:
--   File 181 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
--   * `S4.Def_RP_EtPBC_A_CovEt1`: S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`
--   * `S4.Def_RP_EtPBC_A_CovAs3d`: S4-EtPBC-A, R4-T2 (A3 assembly, As3d): the completed cover as one existential package
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_168
import Definitions.Def_RPLib_FX_EtPBC_174
import Definitions.Def_RPLib_FX_EtPBC_175

/-!
# Proper base change for the projective line, library file 181

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
* `S4.Def_RP_EtPBC_A_CovEt1`: S4-EtPBC-A, R4-T2 (A2c-5, E4a): the completed chart `Ê₁` is etale near `p`
* `S4.Def_RP_EtPBC_A_CovAs3d`: S4-EtPBC-A, R4-T2 (A3 assembly, As3d): the completed cover as one existential package
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
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

/-- `Ê₀ ⧸ J₀^(k+1)` is flat over `B₀ ⧸ J₀^(k+1)`. -/
def hE₀_flat [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (k : ℕ) :
    letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
    Module.Flat (B₀ ⧸ J₀ ^ (k + 1)) (hE₀ C H hts ⧸ (J₀ ^ (k + 1) • ⊤ : Submodule B₀ (hE₀ C H hts))) := by
  letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
  letI : Algebra (B₀ ⧸ J₀ ^ (k + 1)) (C k).E₀ := (C k).a₀.toAlgebra
  letI : Algebra B₀ (C k).E₀ := ((C k).a₀.comp (Ideal.Quotient.mk (J₀ ^ (k + 1)))).toAlgebra
  haveI : IsScalarTower B₀ (B₀ ⧸ J₀ ^ (k + 1)) (C k).E₀ :=
    IsScalarTower.of_algebraMap_eq (R := B₀) (S := B₀ ⧸ J₀ ^ (k + 1)) (A := (C k).E₀) (fun _ => rfl)
  haveI : Module.Flat (B₀ ⧸ J₀ ^ (k + 1)) (C k).E₀ :=
    RingHom.flat_algebraMap_iff.1 (RingHom.Etale.iff_flat_and_formallyUnramified.1 (C k).et₀).1
  let θA : hE₀ C H hts →ₐ[B₀] (C k).E₀ := { toRingHom := θ₀ C H hts k, commutes' := θ₀_β₀ C H hts hφ₁ hu₁ k }
  exact fq_flat (J₀ ^ (k + 1)) θA (θ₀_surj C H ιB₀ ιB₁ p hts α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil k)
    ((RingHom.ker_coe_toRingHom θA).symm.trans (θ₀_ker' C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil k))

/-- `Ê₀ ⧸ J₀ Ê₀ ≅ E₀(0)` is formally unramified over `B₀`. -/
def hE₀_fu [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) :
    letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
    Algebra.FormallyUnramified B₀ (hE₀ C H hts ⧸ (J₀ ^ (0 + 1)).map (β₀ C H hts hφ₁ hu₁)) := by
  letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
  letI : Algebra (B₀ ⧸ J₀ ^ (0 + 1)) (C 0).E₀ := (C 0).a₀.toAlgebra
  letI : Algebra B₀ (C 0).E₀ := ((C 0).a₀.comp (Ideal.Quotient.mk (J₀ ^ (0 + 1)))).toAlgebra
  haveI : IsScalarTower B₀ (B₀ ⧸ J₀ ^ (0 + 1)) (C 0).E₀ :=
    IsScalarTower.of_algebraMap_eq (R := B₀) (S := B₀ ⧸ J₀ ^ (0 + 1)) (A := (C 0).E₀) (fun _ => rfl)
  haveI : Algebra.Etale (B₀ ⧸ J₀ ^ (0 + 1)) (C 0).E₀ := RingHom.etale_algebraMap.1 (C 0).et₀
  haveI : Algebra.FormallyUnramified B₀ (C 0).E₀ :=
    Algebra.FormallyUnramified.comp B₀ (B₀ ⧸ J₀ ^ (0 + 1)) (C 0).E₀
  let θA : hE₀ C H hts →ₐ[B₀] (C 0).E₀ := { toRingHom := θ₀ C H hts 0, commutes' := θ₀_β₀ C H hts hφ₁ hu₁ 0 }
  have hθA : Function.Surjective θA := θ₀_surj C H ιB₀ ιB₁ p hts α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil 0
  exact Algebra.FormallyUnramified.of_equiv ((Ideal.quotientEquivAlgOfEq B₀
    ((RingHom.ker_coe_toRingHom θA).symm.trans (θ₀_ker' C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil 0)).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hθA)).symm

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
/-- `ker (θ₁ k) = J₁^(k+1) Ê₁`. -/
def θ₁_ker' [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d) (k : ℕ) :
    RingHom.ker (θ₁ C H k) = (J₁ ^ (k + 1)).map (β₁ C H hφ₀ hu₀) := by
  have e1 : J₁ ^ (k + 1) = (p ^ (k + 1)).map ιB₁ := by rw [Ideal.map_pow, hJ₁]
  rw [θ₁_ker C H ιB₀ ιB₁ p hts hφ₀ hu₀ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil k, e1, Ideal.map_map]
  all_goals rfl

end Et₁

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

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- **The package for any tower** `C`, `H` (etale/finite part given). -/
def hat_cov_gen
    (het : (β₀ C H hts hφ₁ hu₁).Etale ∧ (β₁ C H hφ₀ hu₀).Etale ∧ (β₀ C H hts hφ₁ hu₁).Finite ∧
      (β₁ C H hφ₀ hu₀).Finite)
    (hsk : Function.Surjective (θ₀ C H hts 0) ∧ Function.Surjective (θ₁ C H 0) ∧
      RingHom.ker (θ₀ C H hts 0) = p.map ((β₀ C H hts hφ₁ hu₁).comp ιB₀) ∧
      RingHom.ker (θ₁ C H 0) = p.map ((β₁ C H hφ₀ hu₀).comp ιB₁)) :
    ∃ (Eh₀ Eh₁ Eh : Type u) (_ : CommRing Eh₀) (_ : CommRing Eh₁) (_ : CommRing Eh)
      (b₀ : B₀ →+* Eh₀) (b₁ : B₁ →+* Eh₁) (b : N →+* Eh) (q₀ : Eh₀ →+* Eh) (q₁ : Eh₁ →+* Eh)
      (θh₀ : Eh₀ →+* (C 0).E₀) (θh₁ : Eh₁ →+* (C 0).E₁) (θh : Eh →+* (C 0).E),
      (b₀.Etale ∧ b₁.Etale ∧ b₀.Finite ∧ b₁.Finite) ∧
      (q₀.comp b₀ = b.comp φ₀ ∧ q₁.comp b₁ = b.comp φ₁ ∧ IsAwayMap q₀ (b₀ t₀) ∧ IsAwayMap q₁ (b₁ t₁)) ∧
      (Function.Surjective θh₀ ∧ Function.Surjective θh₁ ∧
        RingHom.ker θh₀ = p.map (b₀.comp ιB₀) ∧ RingHom.ker θh₁ = p.map (b₁.comp ιB₁)) ∧
      (θh.comp q₀ = (C 0).ψ₀.comp θh₀ ∧ θh.comp q₁ = (C 0).ψ₁.comp θh₁) ∧
      (θh₀.comp b₀ = (C 0).a₀.comp (Ideal.Quotient.mk (J₀ ^ (0 + 1))) ∧
        θh₁.comp b₁ = (C 0).a₁.comp (Ideal.Quotient.mk (J₁ ^ (0 + 1))) ∧
        θh.comp b = (C 0).a.comp (Ideal.Quotient.mk (JN ^ (0 + 1)))) :=
  ⟨hE₀ C H hts, hE₁ C H, hE C H hts, inferInstance, inferInstance, inferInstance, β₀ C H hts hφ₁ hu₁,
    β₁ C H hφ₀ hu₀, β C H hts hφ₀ hu₀ hφ₁ hu₁, hψ₀ C H hts, hψ₁ C H hts, θ₀ C H hts 0, θ₁ C H 0, θ C H hts 0, het,
    ⟨hψ₀_β₀ C H hts hφ₀ hu₀ hφ₁ hu₁, hψ₁_β₁ C H hts hφ₀ hu₀ hφ₁ hu₁, aw_hψ₀ C H hts hφ₁ hu₁,
      aw_hψ₁ C H hts hφ₀ hu₀⟩, hsk,
    ⟨RingHom.ext (θ_hψ₀ C H hts 0), RingHom.ext (θ_hψ₁ C H hts 0)⟩,
    ⟨RingHom.ext (θ₀_β₀ C H hts hφ₁ hu₁ 0), RingHom.ext (θ₁_β₁ C H hφ₀ hu₀ 0),
      RingHom.ext (θ_β C H hts hφ₀ hu₀ hφ₁ hu₁ 0)⟩⟩

end HatCovGen

section HatCov

end HatCov

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFib =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover

For lift data `L : LiftD K gV π x q hx` of a fibre cover `q : T ⟶ Y_x`: the glued cover `dL L` of `Y_{V'}`
(`V' = Spec L.R'`), the lift `xL L` of `x`, and **`ψL L : U_x ⟶ T`** on `U_x = (dL L).glued ×_{Y_{V'}} Y_x`, glued
from the chart lifts `gW` (`g0`, `g1`; `overlap` on `Y₀₁`), with **`ψL_q`**: `ψL L ≫ q = pullback.snd`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁

universe u

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}}
  {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} [IsAffine V] [IsFinite π] {hx : x ≫ gV = 𝟙 _}
  {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} [IsAffineHom q] (L : LiftD K gV π x q hx)

/-- **The two chart lifts agree on the overlap.** -/
theorem overlap : (cvL L).trans WalkingSpan.Hom.snd ≫ g1 L = (cvL L).trans WalkingSpan.Hom.fst ≫ g0 L := by
  obtain ⟨c, hc0, hc1⟩ := ov_glue L
  rw [ov_g0, ov_g1, hc0, hc1, Category.assoc, Category.assoc, ov_m0, ov_m1]

theorem gL_h {i j : (cvL L).I₀} (hij : i ⟶ j) : (cvL L).trans hij ≫ gL L j = gL L i := by
  rcases hij with _ | (_ | _)
  · change (cvL L).trans (𝟙 _) ≫ _ = _
    rw [Scheme.Cover.trans_id, Category.id_comp]
  · rfl
  · exact overlap L

/-- **The glued lift `U_x ⟶ T`.** -/
def ψL : UxL L ⟶ T := (cvL L).glueMorphismsOfLocallyDirected (gL L) (gL_h L)

end RamanujanPetersson.EtPBC.Cov

end

end


