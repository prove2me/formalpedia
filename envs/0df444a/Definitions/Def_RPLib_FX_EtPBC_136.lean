-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_136
-- name    : RPLib_FX_EtPBC_136
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:20:04.815121+00:00
-- url     : https://prove2.me/theorems/9a7ac72c-fca8-5c46-a832-2db052ed92a4
-- title:
--   Proper base change for the projective line, library file 136
-- statement:
--   File 136 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_098
import Definitions.Def_RPLib_FX_EtPBC_118
import Definitions.Def_RPLib_FX_EtPBC_119
import Definitions.Def_RPLib_FX_EtPBC_126

/-!
# Proper base change for the projective line, library file 136

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2PPTb =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map

GLOB/REL PLAN v1 (5), piece part. For etale `f : X₁ ⟶ X` of affine schemes whose rings are finite products of
Dedekind domains:
* **`exists_rad_hom`**: moving a radical `α` (`α ^ d = u`) along `ψ : K →+* K'` (`φ : A →+* A'` compatible);
* **`exists_gam`**: one radical `γ p₁` on every piece `p₁` of `X₁` over `p`, with `γ p₁ ^ d = Ψ u` for every
  compatible `Ψ`;
* **`resLE_kapS_off`**: a piece class of `X` vanishes on the pieces of `X₁` not over its piece;
* **`resLE_kapS_kumD_sum`**: `resLE f (kapS p (kumD α)) = Σ_{p₁} kapS p₁ (χ₁ p₁)` with `χ₁ p₁ = kumD (γ p₁)` for the
  pieces `p₁` over `p` and `χ₁ p₁ = 0` for the others.
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

section RadHom

end RadHom

section PPTb

variable {X X₁ : Scheme.{0}} [IsAffine X] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ p : minimalPrimes Γ(X, ⊤), IsDedekindDomain (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))]
  [∀ p : minimalPrimes Γ(X₁, ⊤), IsDedekindDomain (Γ(X₁, ⊤) ⧸ (p : Ideal Γ(X₁, ⊤)))]
  [Fintype (minimalPrimes Γ(X, ⊤))] [DecidableEq (minimalPrimes Γ(X, ⊤))]
  [Fintype (minimalPrimes Γ(X₁, ⊤))] [DecidableEq (minimalPrimes Γ(X₁, ⊤))] (Λ : Type) [CommRing Λ]
  (f : X₁ ⟶ X) [Etale f] (p : minimalPrimes Γ(X, ⊤)) {N : ℕ} [NeZero N]
  {ζ : maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))}
  (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))),
    σ ζ = ζ)
  {ζ₁ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))}
  (hζ₁ : ∀ p₁, IsPrimitiveRoot (ζ₁ p₁) N)
  (hζΓ₁ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤),
    ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))), σ (ζ₁ p₁) = ζ₁ p₁)
  {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {α : (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))ˣ}
  (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))
    (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))) d)
  {γ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), (maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))ˣ}
  (hγ : ∀ p₁, γ p₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))) d)
  {gΛ : Λ} (hgΛ : d • gΛ = 0)

set_option maxHeartbeats 1000000 in
include h h₁ in
/-- **A piece Kummer class pulled back along an etale `f`** is the sum of the Kummer classes of the pieces over it. -/
def resLE_kapS_kumD_sum {u : FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))} (sX : Γ(X, ⊤)) (sX₁ : Γ(X₁, ⊤))
    (hz : ζ = algebraMap _ (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))
      (algebraMap (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))
        (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) sX)))
    (hz₁ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), ζ₁ p₁ =
      algebraMap _ (maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))
        (algebraMap (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)) (Ideal.Quotient.mk p₁.1 sX₁)))
    (hs : f.appTop sX = sX₁)
    (hu : (α : maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))) ^ d =
      algebraMap _ (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))) u)
    (hγu : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁) →
      ∀ Ψ : FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) →+* FractionRing (Γ(X₁, ⊤) ⧸ p₁.1),
      (∀ a : Γ(X, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) a)) =
        algebraMap _ _ (Ideal.Quotient.mk p₁.1 (f.appTop a))) →
      (γ p₁ : maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))) ^ d =
        algebraMap _ (maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))) (Ψ u))
    (χ₁ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), ChL (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))
      (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) Λ)
    (hχ₁ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁) →
      χ₁ p₁ = kumD (hζ₁ p₁) (hζΓ₁ p₁) hdN (hγ p₁) hgΛ)
    (hχ₀ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), ¬ (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁) → χ₁ p₁ = 0) :
    resLE f 1 (kapS h Λ p (kumD hζ hζΓ hdN hα hgΛ)) = ∑ p₁ : minimalPrimes Γ(X₁, ⊤), kapS h₁ Λ p₁ (χ₁ p₁) :=
  h1_eq_of_pieces (piS (piEquiv h₁)) _ _ fun p₁ => by
    refine Eq.trans ?_ (resLE_kapS_sum h₁ Λ χ₁ p₁).symm
    by_cases hp : (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁)
    · exact (resLE_kapS_kumD_sum_on h h₁ Λ f p hζ hζΓ hζ₁ hζΓ₁ hdN hα hγ hgΛ sX sX₁ hz hz₁ hs hu hγu p₁ hp).trans
        (congrArg (kappaLH (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) Λ)
          (hχ₁ p₁ hp)).symm
    · exact resLE_kapS_kumD_sum_off h h₁ Λ f p p₁ hp _ (χ₁ p₁) (hχ₀ p₁ hp)

end PPTb

end RamanujanPetersson.EtPBC.EtKum

end

end


