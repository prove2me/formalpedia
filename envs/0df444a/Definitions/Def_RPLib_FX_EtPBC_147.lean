-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_147
-- name    : RPLib_FX_EtPBC_147
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T01:18:14.67781+00:00
-- url     : https://prove2.me/theorems/e8869e8f-fc06-4036-9566-8a088f3c981f
-- title:
--   Proper base change for the projective line, library file 147
-- statement:
--   File 147 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_085
import Definitions.Def_RPLib_FX_EtPBC_140

/-!
# Proper base change for the projective line, library file 147

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
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

/-- **Kummer data for `H¹` of a finite product of Dedekind domains.** -/
def h1_exists_kappa (c : H Λ (unitSh Λ X) 1) :
    ∃ χ : ∀ p : minimalPrimes Γ(X, ⊤),
        ChL (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ,
      c = ∑ p, kapS h Λ p (χ p) := by
  choose χ hχ using h1_exists_kappa_piece h Λ c
  exact ⟨χ, (h1_split (piS (piEquiv h)) Λ c).trans
    (Finset.sum_congr rfl fun p _ => h1_exists_kappa_term h Λ c p (χ p) (hχ p))⟩

end Kappa

end RamanujanPetersson.EtPBC.EtKum

end

end


