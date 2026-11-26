-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_186
-- name    : RPLib_FX_EtPBC_186
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:28:22.084697+00:00
-- url     : https://prove2.me/theorems/07d11099-7c48-5ec2-b10d-d5f0524ed608
-- title:
--   Proper base change for the projective line, library file 186
-- statement:
--   File 186 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
--   * `S4.Def_RP_EtPBC_A_O2T9a`: S4-EtPBC-A, O2 S6a (O2T9a): naturality of `resFreeIso` and `clsD` in the coefficients; `clsD` is one-point
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_055
import Definitions.Def_RPLib_FX_EtPBC_181

/-!
# Proper base change for the projective line, library file 186

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
* `S4.Def_RP_EtPBC_A_O2T9a`: S4-EtPBC-A, O2 S6a (O2T9a): naturality of `resFreeIso` and `clsD` in the coefficients; `clsD` is one-point
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

/-- A basic open `D(g)`, `g ≡ 1 mod J₀`, inside the free locus of `Ê₀`. -/
theorem et_free₀ [IsNoetherianRing B₀] [IsNoetherianRing R] [IsPrecomplete p R] {g : ℕ} (α : Fin g → R)
    (hα : ∀ i, α i ∈ p) (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) (hB₀ : (eval₂RingHom ιB₀ t₀).Finite)
    (hB₁ : (eval₂RingHom ιB₁ t₁).Finite) (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (D : ℕ)
    (hs : ∀ d, D ≤ d → ∀ k, Function.Surjective ((H k).secMap (Ideal.Quotient.factor_mk _ _) d))
    (hfil : ∀ d, D ≤ d → ∀ k, FilProp ιB₀ ιB₁ p α (C k) d)
    (hspl : ∀ e, D ≤ e → ∀ z : (C 0).E, ∃ (x₀ : (C 0).E₀) (x₁ : (C 0).E₁),
      z = (C 0).ψ₀ x₀ - (C 0).u ^ e * (C 0).ψ₁ x₁) :
    letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
    ∃ g : B₀, g - 1 ∈ J₀ ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B₀)) ⊆ Module.freeLocus B₀ (hE₀ C H hts) := by
  letI := (β₀ C H hts hφ₁ hu₁).toAlgebra
  haveI : Module.Finite B₀ (hE₀ C H hts) :=
    β₀_finite C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hspl hs hfil
  haveI : Module.FinitePresentation B₀ (hE₀ C H hts) :=
    Module.finitePresentation_of_finite (R := B₀) (M := hE₀ C H hts)
  have hfl := hE₀_flat C H ιB₀ ιB₁ p hts hφ₁ hu₁ α hα hιB hB₀ hB₁ hJ₀ hJ₁ D hs hfil
  exact fq_basicOpen J₀ (Module.freeLocus B₀ (hE₀ C H hts)) Module.isOpen_freeLocus
    (fun q hq => lf_mem_freeLocus J₀ hfl q (fun x hx => (PrimeSpectrum.mem_zeroLocus _ _).1 hq hx))

end Et₀

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T9a =====
section

/-!
# S4-EtPBC-A, O2 S6a (O2T9a): naturality of `resFreeIso` and `clsD` in the coefficients; `clsD` is one-point

* `resFreeIso_natural r`: `resFreeIso_{T'} ≫ res Λ[r] = Λ[e⁻¹ r] ≫ resFreeIso_T`;
* `clsD_natF f h Y`: `clsD (f ≫ res h) Y = clsD f Y ∘ h` for `h : F' ⟶ F` on `P`;
* **`clsD_isLoc`**: every `clsD f Y` is a one-point class `IsLoc` at `c (X = a)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option profiler true
set_option profiler.threshold 3000

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section ResNat

end ResNat

section ClsNat

variable {k : Type} [Field k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)
  {Uz : P.Opens} (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact)

set_option backward.isDefEq.respectTransparency false in
/-- **`clsD` classes are one-point classes** at `c (X = a)`. -/
theorem clsD_isLoc (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a))
    (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
    (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
    {F : EtSh Λ P} {G : EtSh Λ (chEt c φ).left} (f : G ⟶ (res (chEt c φ).hom Λ).obj F)
    (Y : H Λ ((res (toD1 c φ a).left Λ).obj G) 1) :
    IsLoc Λ F (c (A1pt k a)) (clsD c φ a hUz hS f Y) := by
  have hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uz ∨ (chEt c φ).hom v = c (A1pt k a) := fun v => by
    by_cases hv : (chEt c φ).hom v = c (A1pt k a)
    · exact Or.inr hv
    · exact Or.inl ((hz _).2 hv)
  refine ⟨Uz, Uz, le_refl Uz, hz, chEt c φ, hD, hDn, hDr,
    (Ext.mk₀ (freeMap Λ (isoT c φ hUz).inv)).comp ((extFree Λ (W1 c φ a) F 1).symm
      (Y.comp (Ext.mk₀ ((res (toD1 c φ a).left Λ).map f ≫ (resCompIso Λ (toD1 c φ a)).hom.app F))
        (add_zero 1))) (zero_add 1), ?_⟩
  rw [clsD_eq]
  exact Ext.comp_assoc_of_second_deg_zero _ _ _ _

end ClsNat

end RamanujanPetersson.EtPBC.EtMV

end

end


