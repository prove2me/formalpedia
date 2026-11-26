-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_137
-- name    : RPLib_FX_EtPBC_137
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:25:25.875801+00:00
-- url     : https://prove2.me/theorems/42796c5c-dd14-5f03-bdc8-c29c87e5ac27
-- title:
--   Proper base change for the projective line, library file 137
-- statement:
--   File 137 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2UKd1`: S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_129

/-!
# Proper base change for the projective line, library file 137

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

end KillG

section KapDC

variable {X Y X₁ : Scheme.{0}} [IsAffine X] [IsAffine Y] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)]
  [IsNoetherianRing Γ(Y, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (hY : ∀ (m : Ideal Γ(Y, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ p : minimalPrimes Γ(X, ⊤), IsDedekindDomain (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))]
  [∀ Q : minimalPrimes Γ(Y, ⊤), IsDedekindDomain (Γ(Y, ⊤) ⧸ (Q : Ideal Γ(Y, ⊤)))]
  [∀ p : minimalPrimes Γ(X₁, ⊤), IsDedekindDomain (Γ(X₁, ⊤) ⧸ (p : Ideal Γ(X₁, ⊤)))]
  [Fintype (minimalPrimes Γ(X, ⊤))] [DecidableEq (minimalPrimes Γ(X, ⊤))]
  [Fintype (minimalPrimes Γ(Y, ⊤))] [DecidableEq (minimalPrimes Γ(Y, ⊤))]
  [Fintype (minimalPrimes Γ(X₁, ⊤))] [DecidableEq (minimalPrimes Γ(X₁, ⊤))] (Λ : Type) [CommRing Λ]
  (f : X₁ ⟶ X) [Etale f] (g₀ : X ⟶ Y) [Etale g₀] (p : minimalPrimes Γ(X, ⊤)) {N : ℕ} [NeZero N]
  {ζ : maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))}
  (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))),
    σ ζ = ζ)
  {ζY : ∀ Q : minimalPrimes Γ(Y, ⊤), maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1))}
  (hζY : ∀ Q, IsPrimitiveRoot (ζY Q) N)
  (hζΓY : ∀ Q : minimalPrimes Γ(Y, ⊤),
    ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))), σ (ζY Q) = ζY Q)
  {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {α : (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))ˣ}
  (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))
    (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))) d)
  {β : ∀ Q : minimalPrimes Γ(Y, ⊤), (maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))ˣ}
  (hβ : ∀ Q, β Q ∈ rad (⊤ : Subgroup (Pi1 (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))) d)
  {gΛ : Λ} (hgΛ : d • gΛ = 0)

set_option maxHeartbeats 1000000 in
include h h₁ hY in
/-- **A piece Kummer class along `f` = a global Kummer class along `f ≫ g₀`** (radicands `u · r_p`, `r_q`). -/
def resLE_kapS_kumD_eq_comp {u : FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))} (sX : Γ(X, ⊤)) (sY : Γ(Y, ⊤))
    (hz : ζ = algebraMap _ (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))
      (algebraMap (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) sX)))
    (hzY : ∀ Q : minimalPrimes Γ(Y, ⊤), ζY Q = algebraMap _ (maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))
      (algebraMap (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 sY)))
    (hs : g₀.appTop sY = sX)
    (hu : (α : maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))) ^ d =
      algebraMap _ (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))) u)
    {Hg : Γ(Y, ⊤)} (hH : IsUnit Hg)
    (hβH : ∀ Q : minimalPrimes Γ(Y, ⊤), (β Q : maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1))) ^ d =
      algebraMap _ (maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))
        (algebraMap (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 Hg)))
    (cY : H Λ (unitSh Λ Y) 1)
    (hcY : ∀ Q : minimalPrimes Γ(Y, ⊤), resLE (piHom (piEquiv hY) Q) 1 cY =
      kappaLH (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)) Λ (kumD (hζY Q) (hζΓY Q) hdN (hβ Q) hgΛ))
    (hd : IsUnit (d : Γ(X₁, ⊤)))
    {r : ∀ q : minimalPrimes Γ(X, ⊤), FractionRing (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤)))}
    (hHp : algebraMap (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))
      (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) (g₀.appTop Hg)) = u * r p)
    (hHq : ∀ q : minimalPrimes Γ(X, ⊤), q ≠ p → algebraMap (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤)))
      (FractionRing (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤)))) (Ideal.Quotient.mk (q : Ideal Γ(X, ⊤)) (g₀.appTop Hg)) = r q)
    (hr : ∀ (p₁ : minimalPrimes Γ(X₁, ⊤)) (q : minimalPrimes Γ(X, ⊤))
      (Ψ : FractionRing (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤))) →+* FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))),
      (∀ a : Γ(X, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk (q : Ideal Γ(X, ⊤)) a)) =
        algebraMap _ _ (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (f.appTop a))) →
      ∃ v : FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))), v ^ d = Ψ (r q)) :
    resLE f 1 (kapS h Λ p (kumD hζ hζΓ hdN hα hgΛ)) = resLE f 1 (resLE g₀ 1 cY) := by
  have e1 : ∀ p₁ : minimalPrimes Γ(X₁, ⊤),
      algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))))
        (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) ((f ≫ g₀).appTop Hg)) =
      algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))))
        (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (f.appTop (g₀.appTop Hg))) := fun p₁ =>
    congrArg (fun x => algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))
      (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) x))
      (appTop_comp' f g₀ Hg)
  have hs' : f.appTop sX = (f ≫ g₀).appTop sY :=
    (congrArg (fun x => f.appTop x) hs).symm.trans (appTop_comp' f g₀ sY).symm
  refine (resLE_kapS_kumD_eq h hY h₁ Λ f (f ≫ g₀) p hζ hζΓ hζY hζΓY hdN hα hβ hgΛ sX sY hz hzY hs' hu hH hβH
    cY hcY hd ?_ ?_).trans (resLE_comp f g₀ cY)
  · intro p₁ _ Ψ hΨ
    obtain ⟨w, hw⟩ := hr p₁ p Ψ hΨ
    have hH0 : algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))))
        (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) ((f ≫ g₀).appTop Hg)) ≠ 0 :=
      (((hH.map (f ≫ g₀).appTop.hom).map (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)))).map
        (algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))))).ne_zero
    have e2 : Ψ (algebraMap (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))
        (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) (g₀.appTop Hg))) = Ψ u * w ^ d :=
      (congrArg Ψ hHp).trans ((Ψ.map_mul _ _).trans (congrArg (Ψ u * ·) hw.symm))
    exact ⟨w⁻¹, eq_mul_inv_pow hH0 (((e1 p₁).trans (hΨ _).symm).trans e2)⟩
  · intro p₁ q hqp _ Ψ hΨ
    obtain ⟨w, hw⟩ := hr p₁ q Ψ hΨ
    exact ⟨w, hw.trans (((congrArg Ψ (hHq q hqp)).symm.trans (hΨ _)).trans (e1 p₁).symm)⟩

end KapDC

end RamanujanPetersson.EtPBC.EtKum

end

end


