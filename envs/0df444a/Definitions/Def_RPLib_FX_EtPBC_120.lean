-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_120
-- name    : RPLib_FX_EtPBC_120
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T22:32:43.404227+00:00
-- url     : https://prove2.me/theorems/bdaf2204-9992-5b2e-b4a8-93604e04d680
-- title:
--   Proper base change for the projective line, library file 120
-- statement:
--   File 120 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_082
import Definitions.Def_RPLib_FX_EtPBC_109

/-!
# Proper base change for the projective line, library file 120

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

end KapSum

section KapB

end KapB

section Piece

end Piece

section GenPieces

universe u'

end GenPieces

section KapD

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
  (f : X₁ ⟶ X) [Etale f] (g : X₁ ⟶ Y) [Etale g] (p : minimalPrimes Γ(X, ⊤)) {N : ℕ} [NeZero N]
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
/-- `resLE_kapS_kumD_eq` on a piece `p₁` not lying over `p`. -/
def resLE_kapS_kumD_eq_off {u : FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))} (sX : Γ(X, ⊤)) (sY : Γ(Y, ⊤))
    (hz : ζ = algebraMap _ (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))
      (algebraMap (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) sX)))
    (hzY : ∀ Q : minimalPrimes Γ(Y, ⊤), ζY Q = algebraMap _ (maxUnram (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)))
      (algebraMap (Γ(Y, ⊤) ⧸ Q.1) (FractionRing (Γ(Y, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 sY)))
    (hs : f.appTop sX = g.appTop sY)
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
    (hon : ∀ (p₁ : minimalPrimes Γ(X₁, ⊤)), (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁) →
      ∀ Ψ : FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) →+* FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))),
      (∀ a : Γ(X, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk (p : Ideal Γ(X, ⊤)) a)) =
        algebraMap _ _ (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (f.appTop a))) →
      ∃ v, Ψ u = algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (g.appTop Hg)) * v ^ d)
    (hoff : ∀ (p₁ : minimalPrimes Γ(X₁, ⊤)) (q : minimalPrimes Γ(X, ⊤)), q ≠ p →
      (q : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁) →
      ∀ Ψ : FractionRing (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤))) →+* FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))),
      (∀ a : Γ(X, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk (q : Ideal Γ(X, ⊤)) a)) =
        algebraMap _ _ (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (f.appTop a))) →
      ∃ v : FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))),
        v ^ d = algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (g.appTop Hg)))
    (p₁ : minimalPrimes Γ(X₁, ⊤)) (hp : ¬ (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁)) :
    resLE (piHom (piEquiv h₁) p₁) 1 (resLE f 1 (kapS h Λ p (kumD hζ hζΓ hdN hα hgΛ))) =
      resLE (piHom (piEquiv h₁) p₁) 1 (resLE g 1 cY) := by
  obtain ⟨Q, hQ⟩ := exists_minimalPrime_le_ker g p₁
  have := etale_kerLift hY h₁ g hQ
  have hinjQ : Function.Injective (CommRingCat.ofHom (kerLift hQ)).hom := injective_of_etale (kerLift hQ)
  obtain ⟨q, hq⟩ := exists_minimalPrime_le_ker f p₁
  have hne : q ≠ p := fun e => hp (e ▸ hq)
  have := etale_kerLift h h₁ f hq
  obtain ⟨v, hv'⟩ := resLE_kapS_kumD_eq_off_v (h := h) (h₁ := h₁) (f := f) (g := g) (p := p) (hoff := hoff)
    (p₁ := p₁) (Q := Q) (hQ := hQ) (q := q) (hq := hq) (hne := hne)
  refine ((resLE_piece h h₁ f p₁ q hq _).trans ?_).trans ((resLE_piece hY h₁ g p₁ Q hQ cY).trans
    (congrArg (resLE (Spec.map (CommRingCat.ofHom (kerLift hQ))) 1) (hcY Q))).symm
  refine (congrArg (resLE (Spec.map (CommRingCat.ofHom (kerLift hq))) 1) (resLE_kapS_ne h Λ hne _)).trans ?_
  refine (map_zero (resLEHom (Spec.map (CommRingCat.ofHom (kerLift hq))) (Λ := Λ) 1)).trans ?_
  exact (resLE_kumD_eq_zero_ring (CommRingCat.ofHom (kerLift hQ)) (hζY Q) (hζΓY Q) hdN (hβ Q) hgΛ hinjQ
    (hzY Q) (H'' := Ideal.Quotient.mk Q.1 Hg) (hβH Q) hv').symm

end KapD

end RamanujanPetersson.EtPBC.EtKum

end

end


