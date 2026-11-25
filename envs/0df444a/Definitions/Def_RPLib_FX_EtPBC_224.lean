-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_224
-- name    : RPLib_FX_EtPBC_224
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:55:18.845444+00:00
-- url     : https://prove2.me/theorems/e9a580e6-8253-5fa9-9e32-8a0d1d542227
-- title:
--   Proper base change for the projective line, library file 224
-- statement:
--   File 224 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Km4`: S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_046

/-!
# Proper base change for the projective line, library file 224

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Km4`: S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Km4 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km4): `H¹` of an affine scheme whose ring is a product of Dedekind domains

* `piHom e k : Spec (R k) ⟶ X`, `piS e k : X.Etale` for a ring isomorphism `e : Γ(X, ⊤) ≃+* Π k, R k`;
  `cop_piS_hom`, `IsIso (cop (piS e)).hom` (via `sigmaSpec`);
* `kapS h Λ p χ = pr_p^* (extFreeU⁻¹ (κ(χ)))`: the Kummer class of a character `χ` of `π₁(Γ ⧸ p)` as a class
  in `H¹(X, Λ)` (`Γ = Γ(X, ⊤)` noetherian, localizations at maximal ideals domains, `p` a minimal prime);
  `kapS_apply`. The decomposition theorem `h1_exists_kappa` is in O2Km4b (split for the kernel budget).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur

universe u

section PiS

end PiS

section GenKap
universe w v₁ u₁ u₂ u₃

end GenKap

section Kappa

variable {X : Scheme.{0}} [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ p : minimalPrimes Γ(X, ⊤), IsDedekindDomain (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))]
  [Fintype (minimalPrimes Γ(X, ⊤))] [DecidableEq (minimalPrimes Γ(X, ⊤))] (Λ : Type) [CommRing Λ]

/-- The Kummer class of a character of the piece `Spec (Γ ⧸ p)`, as a class on `X`. -/
def kapS (p : minimalPrimes Γ(X, ⊤)) :
    ChL (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ →+
      H Λ (unitSh Λ X) 1 :=
  precompSymmGen (splitPr (piS (piEquiv h)) Λ p) (extFreeU Λ (piS (piEquiv h) p) 1)
    (kappaLH (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ)

end Kappa

end RamanujanPetersson.EtPBC.EtKum

end

end


