-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_085
-- name    : RPLib_FX_EtPBC_085
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:29:38.62509+00:00
-- url     : https://prove2.me/theorems/833702a5-4804-5ca9-b02e-8f163b3aa9dd
-- title:
--   Proper base change for the projective line, library file 085
-- statement:
--   File 085 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2KapN`: S4-EtPBC-A, O2 M6 (O2KapN): naturality of Kummer classes along etale maps of Dedekind domains
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_075

/-!
# Proper base change for the projective line, library file 085

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
* `S4.Def_RP_EtPBC_A_O2KapN`: S4-EtPBC-A, O2 M6 (O2KapN): naturality of Kummer classes along etale maps of Dedekind domains
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Km4b =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains

**`h1_exists_kappa`**: if `Γ = Γ(X, ⊤)` is noetherian, its localizations at maximal ideals are domains and its
quotients by minimal primes are Dedekind, every `c ∈ H¹(X, Λ)` is `Σ_p kapS h Λ p (χ_p)` with `χ_p` a character of
`π₁(Γ ⧸ p)` (`kappaLH_surj` on each piece, `h1_split`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur

section Kappa

variable {X : Scheme.{0}} [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ p : minimalPrimes Γ(X, ⊤), IsDedekindDomain (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))]
  [Fintype (minimalPrimes Γ(X, ⊤))] [DecidableEq (minimalPrimes Γ(X, ⊤))] (Λ : Type) [CommRing Λ]

theorem h1_exists_kappa_term (c : H Λ (unitSh Λ X) 1) (p : minimalPrimes Γ(X, ⊤))
    (χ : ChL (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ)
    (hχ : kappaLH (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ χ =
        h1_eS h Λ p ((Ext.mk₀ (splitIn (piS (piEquiv h)) Λ p)).comp c (zero_add 1))) :
    (Ext.mk₀ (splitPr (piS (piEquiv h)) Λ p)).comp ((Ext.mk₀ (splitIn (piS (piEquiv h)) Λ p)).comp c (zero_add 1))
      (zero_add 1) = kapS h Λ p χ := by
  rw [kapS_eq_eS, hχ, AddEquiv.symm_apply_apply]

end Kappa

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapN =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapN): naturality of Kummer classes along etale maps of Dedekind domains

* **`resLE_kumD`**: along an etale `Spec.map φ` (`η' ↦ η`) with `ψ : K → K'` extending `φ`, the class `κ(kumD α)`
  (`α^d = u`) restricts to `κ(kumD γ)` for any radical `γ` with `γ^d = ψ u` (roots of unity matched by `ψ`);
* **`exists_root_of_isUnit`**: a unit of a Dedekind domain has a `d`-th root in `K_U` (`d` invertible);
* **`resLE_kumD_eq`**: two Kummer classes from `A` and `A''` agree on `A'` once their radicands differ by a `d`-th
  power there and one of them is a unit of `A'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

section Root

end Root

section KapN

variable {A K A' K' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing A'] [IsDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K']
  [IsIntegrallyClosed A] [IsNoetherianRing A] [IsIntegrallyClosed A'] [IsNoetherianRing A']
  (φ : CommRingCat.of A ⟶ CommRingCat.of A') [Etale (Spec.map φ)]
  (h : Spec.map φ (GenBr.genPt A') = GenBr.genPt A)
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] {ζ : maxUnram A K} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ) {ζ' : maxUnram A' K'} (hζ' : IsPrimitiveRoot ζ' N)
  (hζΓ' : ∀ σ ∈ (⊤ : Subgroup (Pi1 A' K')), σ ζ' = ζ') {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {α : (maxUnram A K)ˣ} (hα : α ∈ rad (⊤ : Subgroup (Pi1 A K)) d) {g : Λ} (hg : d • g = 0)

include h in
/-- **Naturality of Kummer classes**: `κ(kumD α)` restricts to `κ(kumD γ)` for `γ^d = ψ(α^d)`. -/
theorem resLE_kumD (ψ : K →+* K') (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (φ.hom a))
    {z₀ u : K} (hz : ζ = algebraMap K (maxUnram A K) z₀) (hz' : ζ' = algebraMap K' (maxUnram A' K') (ψ z₀))
    (hu : (α : maxUnram A K) ^ d = algebraMap K (maxUnram A K) u)
    {γ : (maxUnram A' K')ˣ} (hγ : γ ∈ rad (⊤ : Subgroup (Pi1 A' K')) d)
    (hu' : (γ : maxUnram A' K') ^ d = algebraMap K' (maxUnram A' K') (ψ u)) :
    resLE (Spec.map φ) 1 (kappaLH A K Λ (kumD hζ hζΓ hdN hα hg)) =
      kappaLH A' K' Λ (kumD hζ' hζΓ' hdN hγ hg) :=
  resLE_kappaL_kum_field φ h (primd hζ hdN) (primd hζ' hdN) (fix_pow hζΓ) (fix_pow hζΓ') ψ hψ
    (z := z₀ ^ (N / d)) (u := u) (by rw [hz, map_pow]) (by rw [hz']; simp only [map_pow]) hα hγ hg hu hu'

end KapN

section KapE

end KapE

end RamanujanPetersson.EtPBC.EtKum

end

end


