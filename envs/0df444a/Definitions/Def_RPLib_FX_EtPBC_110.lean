-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_110
-- name    : RPLib_FX_EtPBC_110
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:56:03.566609+00:00
-- url     : https://prove2.me/theorems/d851e578-0042-53aa-be7a-11d4d52f6084
-- title:
--   Proper base change for the projective line, library file 110
-- statement:
--   File 110 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2UKd1`: S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_082
import Definitions.Def_RPLib_FX_EtPBC_087
import Definitions.Def_RPLib_FX_EtPBC_097

/-!
# Proper base change for the projective line, library file 110

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2UKd1`: S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2UKd1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`

Generic (abstract affine schemes) forms of the two facts used by `uk_diff` / `uk_kill_glob` (O2UKd2):
* `resLE_kumG_eq_zero`: a global Kummer class dies along `g` once its radicand is a `d`-th power on every piece;
* **`resLE_kapS_kumD_eq_comp`**: along `f : X₁ ⟶ X`, the piece class `kapS p (kumD α)` (`α ^ d = u`) equals the
  restriction of a global Kummer class `c_Y` of a unit `H` along `g₀ : X ⟶ Y`, when `g₀^* H = u · r_p` on `p`,
  `g₀^* H = r_q` on the other pieces, and every `r_q` becomes a `d`-th power along every `Ψ` compatible with `f`;
* **`resLE_kumG_eq_zero_comp`**: the same class dies along `f` when `g₀^* H = r_q` on every piece.
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

section Aux

end Aux

section KillG

variable {Y X₁ : Scheme.{0}} [IsAffine Y] [IsAffine X₁] [IsNoetherianRing Γ(Y, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (hY : ∀ (m : Ideal Γ(Y, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ Q : minimalPrimes Γ(Y, ⊤), IsDedekindDomain (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤)))]
  [∀ p : minimalPrimes Γ(X₁, ⊤), IsDedekindDomain (Γ(X₁, ⊤) ⧸ (p : Ideal Γ(X₁, ⊤)))]
  [Fintype (minimalPrimes Γ(Y, ⊤))] [DecidableEq (minimalPrimes Γ(Y, ⊤))]
  [Fintype (minimalPrimes Γ(X₁, ⊤))] [DecidableEq (minimalPrimes Γ(X₁, ⊤))] (Λ : Type) [CommRing Λ]
  (g : X₁ ⟶ Y) [Etale g] {N : ℕ} [NeZero N]
  {ζY : ∀ Q : minimalPrimes Γ(Y, ⊤), maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1))}
  (hζY : ∀ Q, IsPrimitiveRoot (ζY Q) N)
  (hζΓY : ∀ Q : minimalPrimes Γ(Y, ⊤),
    ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))), σ (ζY Q) = ζY Q)
  {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {β : ∀ Q : minimalPrimes Γ(Y, ⊤), (maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))ˣ}
  (hβ : ∀ Q, β Q ∈ rad (⊤ : Subgroup (Pi1 (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))) d)
  {gΛ : Λ} (hgΛ : d • gΛ = 0)

set_option maxHeartbeats 1000000 in
include h₁ in
/-- **A global Kummer class dies along `g` once its radicand is a `d`-th power on every piece of `X₁`.** -/
def resLE_kumG_eq_zero (sY : Γ(Y, ⊤))
    (hzY : ∀ Q : minimalPrimes Γ(Y, ⊤), ζY Q = algebraMap _ (maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))
      (algebraMap (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 sY)))
    {Hg : Γ(Y, ⊤)}
    (hβH : ∀ Q : minimalPrimes Γ(Y, ⊤), (β Q : maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1))) ^ d =
      algebraMap _ (maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))
        (algebraMap (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 Hg)))
    (cY : H Λ (unitSh Λ Y) 1)
    (hcY : ∀ Q : minimalPrimes Γ(Y, ⊤), resLE (piHom (piEquiv hY) Q) 1 cY =
      kappaLH (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)) Λ (kumD (hζY Q) (hζΓY Q) hdN (hβ Q) hgΛ))
    (hkill : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), ∃ v : FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))),
      v ^ d = algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))))
        (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (g.appTop Hg))) :
    resLE g 1 cY = 0 := by
  apply h1_eq_zero_of_pieces Λ (piS (piEquiv h₁))
  intro p₁
  obtain ⟨Q, hQ⟩ := exists_minimalPrime_le_ker g p₁
  have := etale_kerLift hY h₁ g hQ
  have hinjQ : Function.Injective (CommRingCat.ofHom (kerLift hQ)).hom := injective_of_etale (kerLift hQ)
  show resLE (piHom (piEquiv h₁) p₁) 1 (resLE g 1 cY) = 0
  refine (resLE_piece hY h₁ g p₁ Q hQ cY).trans ?_
  refine (congrArg (resLE (Spec.map (CommRingCat.ofHom (kerLift hQ))) 1) (hcY Q)).trans ?_
  obtain ⟨v, hv⟩ := hkill p₁
  have hv' : v ^ d = algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))))
      ((CommRingCat.ofHom (kerLift hQ)).hom (Ideal.Quotient.mk Q.1 Hg)) := hv
  exact resLE_kumD_eq_zero_ring (CommRingCat.ofHom (kerLift hQ)) (hζY Q) (hζΓY Q) hdN (hβ Q) hgΛ hinjQ
    (hzY Q) (H'' := Ideal.Quotient.mk Q.1 Hg) (hβH Q) hv'

end KillG

section KapDC

end KapDC

end RamanujanPetersson.EtPBC.EtKum

end

end


