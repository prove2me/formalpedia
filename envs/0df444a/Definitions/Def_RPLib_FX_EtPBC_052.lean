-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_052
-- name    : RPLib_FX_EtPBC_052
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:13:40.843237+00:00
-- url     : https://prove2.me/theorems/691ec251-95fb-5edd-82a3-f753874db5e7
-- title:
--   Proper base change for the projective line, library file 052
-- statement:
--   File 052 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Gl3c`: S4-EtPBC-A, O2 GLOB (O2Gl3c): a piece of `W₁` survives in `W₂ = W₁[1/φ₁ c₀']`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_042
import Definitions.Def_RPLib_FX_EtPBC_043

/-!
# Proper base change for the projective line, library file 052

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Gl3c`: S4-EtPBC-A, O2 GLOB (O2Gl3c): a piece of `W₁` survives in `W₂ = W₁[1/φ₁ c₀']`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Gl3c =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3c): a piece of `W₁` survives in `W₂ = W₁[1/φ₁ c₀']`

* **`exists_piece_overB`** (generic): in a localization `G₂ = G₁[1/s]`, a minimal prime `p₁ ∌ s` lies under a minimal
  prime `p₂` (`p₁ ≤ ker (κ p₂)` for any `κ` with `ker (κ q) = σ⁻¹ q`);
* **`not_mem_of_toPiQ_ne_zero`**; **`exists_piece_toDF`**: the chart form (`c₀' ≠ 0`, flatness of `W₁ → Spec k[X]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section PieceOver

end PieceOver

section PieceChart

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]

/-- **A piece `p₁` of `W₁` lies under a piece `p₂` of `W₂ = W₁[1/φ₁ c₀']`** (`c₀' ≠ 0`). -/
def exists_piece_toDF {c₀' : k[X]} (hc : c₀' ≠ 0) [IsAffine (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).left]
    (p₁ : minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) :
    ∃ p₂ : minimalPrimes Γ(((etPull (prd (chEt c (φ₁ ≫ locF (φ₁.hom c₀'))) (opEt Uo)).hom).obj R).left, ⊤),
      (p₁ : Ideal Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) ≤ RingHom.ker (kerMap (wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))) p₂) :=
  exists_piece_overB (wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo))).appTop.hom
    ((bW (Spec.map φ₁ ≫ c) (opEt Uo) R) (φ₁.hom c₀')) (isLocalization_away_toDF c φ₁ (φ₁.hom c₀') (opEt Uo) R)
    (kerMap (wm (R := R) (prdMap (toDF c φ₁ (φ₁.hom c₀')) (opEt Uo)))) (fun q => ker_kerMap _ q) p₁
    (not_mem_of_toPiQ_ne_zero (gamMap_shG c R φ₁ c₀') (toPiQ_gamMap_ne_zero (shG c φ₁ (Uo := Uo) R) hc p₁))

end PieceChart

end RamanujanPetersson.EtPBC.EtKum

end

end


