-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_119
-- name    : RPLib_FX_EtPBC_119
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:59:34.268608+00:00
-- url     : https://prove2.me/theorems/51925e26-e27e-5b75-b3fa-510bbf582484
-- title:
--   Proper base change for the projective line, library file 119
-- statement:
--   File 119 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_051
import Definitions.Def_RPLib_FX_EtPBC_108
import Definitions.Def_RPLib_FX_EtPBC_109

/-!
# Proper base change for the projective line, library file 119

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2KapD =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class

* **`resLE_kapS_sum`**: the global class `Σ_Q kapS Q (χ Q)` restricts to `κ(χ Q)` on the piece `Q`;
* **`resLE_kapS_kumD_eq`**: for etale `f : X₁ ⟶ X`, `g : X₁ ⟶ Y` of affine schemes whose rings are finite products of
  Dedekind domains, `resLE f (kapS p (kumD α)) = resLE g c_Y` when `c_Y` is the Kummer class of a unit `H` of `Γ(Y)`
  (piecewise), `α ^ d = u`, the roots of unity match, and on every piece `p₁` of `X₁`: over `p`, `u = H · v ^ d`;
  over another piece of `X`, `H` is a `d`-th power.
  Proof: `h1_eq_zero_of_pieces` on `X₁`, `piHom_comp_eq` for `f` and `g`, `resLE_kapS_self/ne`, `resLE_kumD_eq`
  (O2KapN) and `resLE_kumD_eq_zero` (O2KapF).
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

section KapSum

variable {Y : Scheme.{0}} [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)]
  (hY : ∀ (m : Ideal Γ(Y, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ Q : minimalPrimes Γ(Y, ⊤), IsDedekindDomain (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤)))]
  [Fintype (minimalPrimes Γ(Y, ⊤))] [DecidableEq (minimalPrimes Γ(Y, ⊤))] (Λ : Type) [CommRing Λ]

set_option maxHeartbeats 1000000 in
/-- **The sum of the piece classes restricts to the class of each piece.** -/
def resLE_kapS_sum
    (χ : ∀ Q : minimalPrimes Γ(Y, ⊤), ChL (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤)))
      (FractionRing (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤)))) Λ) (Q : minimalPrimes Γ(Y, ⊤)) :
    resLE (piHom (piEquiv hY) Q) 1 (∑ Q' : minimalPrimes Γ(Y, ⊤), kapS hY Λ Q' (χ Q')) =
      kappaLH (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤))) (FractionRing (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤)))) Λ (χ Q) := by
  rw [← resLEHom_apply, map_sum]
  refine (Finset.sum_eq_single Q (fun Q' _ hQ' => ?_) (fun hQ => absurd (Finset.mem_univ Q) hQ)).trans ?_
  · rw [resLEHom_apply]
    exact resLE_kapS_ne hY Λ (Ne.symm hQ') _
  · rw [resLEHom_apply]
    exact resLE_kapS_self hY Λ Q _

end KapSum

section KapB

end KapB

section Piece

end Piece

section GenPieces

universe u'

end GenPieces

section KapD

end KapD

end RamanujanPetersson.EtPBC.EtKum

end

end


