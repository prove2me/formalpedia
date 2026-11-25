-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_056
-- name    : RPLib_FX_EtPBC_056
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:15:15.556216+00:00
-- url     : https://prove2.me/theorems/7325549a-07d3-5ffe-bc45-d59498a2f3e6
-- title:
--   Proper base change for the projective line, library file 056
-- statement:
--   File 056 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Km9a`: S4-EtPBC-A, O2 M6 (O2Km9a): roots of unity on the Shapiro pieces
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_043

/-!
# Proper base change for the projective line, library file 056

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Km9a`: S4-EtPBC-A, O2 M6 (O2Km9a): roots of unity on the Shapiro pieces
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Km9a =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km9a): roots of unity on the Shapiro pieces

Setting of O2Km6 (`D = Spec B` over `𝔸¹ ⊆ P`, `D_o = D ×_P Uo` affine, `R` affine with constant degree `n` over
`D_o`, `W = D_o ×_P R`), plus a primitive `N`-th root of unity `ζ0 ∈ k` and `N • Λ = 0`.
* `fW p : k →+* Frac(Γ(W) ⧸ p)`, `ζW p`, `hζW` (primitive), `hζWΓ` (fixed by `π₁`);
  (the hypotheses `hζ`, `hζΓ` of `ext_mem_of_kum`, O2Km9b).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Zeta

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]

variable {N : ℕ} {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)

def hζWΓ (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) :
    ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)
      (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))),
      σ (ζW c φ R (ζ0 := ζ0) p) = ζW c φ R (ζ0 := ζ0) p :=
  zetaE_fix _ _

end Zeta

end RamanujanPetersson.EtPBC.EtKum

end

end


