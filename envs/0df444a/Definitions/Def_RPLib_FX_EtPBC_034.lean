-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_034
-- name    : RPLib_FX_EtPBC_034
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:54:49.74288+00:00
-- url     : https://prove2.me/theorems/b60e4e1f-c74a-5573-ac22-26d15c8d8f98
-- title:
--   Proper base change for the projective line, library file 034
-- statement:
--   File 034 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
--   * `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
--   * `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
--   * `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
--   * `S4.Def_RP_EtPBC_A_O2T4a`: S4-EtPBC-A, O2 S5d (O2T4a): `secMap_res` (thetaM moved to O2T4a0 for the 150 user-s cap)
--   * `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_028

/-!
# Proper base change for the projective line, library file 034

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
* `S4.Def_RP_EtPBC_A_O2KapP`: S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map
* `S4.Def_RP_EtPBC_A_O2KapD`: S4-EtPBC-A, O2 M6 (O2KapD): a piece Kummer class against a global Kummer class
* `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
* `S4.Def_RP_EtPBC_A_O2T4a`: S4-EtPBC-A, O2 S5d (O2T4a): `secMap_res` (thetaM moved to O2T4a0 for the 150 user-s cap)
* `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2E5 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)

* generic: **`mapExact_comp_iso`**: for exact `Φ`, `Ψ`, `Φ'` and `τ : Φ ⋙ Ψ ≅ Φ'`, `Ψ(Φ ξ) ∘ τ_B = τ_A ∘ Φ' ξ`
  on `Ext¹` (enough injectives);
* for `m : W' ⟶ W` in `P.Etale`: `Etale m.left`, `etCompCompIso m`, `resCompIso Λ m : res W ⋙ res m ≅ res W'`;
* `diagSec Λ W : Λ_W ⟶ Λ[W]|_W` with `extFree_eq` (`extFree β = diagSec ∘ β|_W`) and `diagSec_sec`;
* **`diagSec_natural`**: `diagSec W' ≫ Λ[m]|_W' = unitRes m.left ≫ (diagSec W)|_W' ≫ (resCompIso m)_{Λ[W]}`.
`extFree_natural` is in O2E5b.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

section Gen

universe w v₁ u₁ v₂ u₂ v₃ u₃

end Gen

section Nat

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {W W' : P.Etale} (m : W' ⟶ W)

/-- **The diagonal section is natural in `W`.** -/
theorem diagSec_natural :
    diagSec Λ W' ≫ (res W'.hom Λ).map (freeMap Λ m) =
      unitRes m.left Λ ≫ (res m.left Λ).map (diagSec Λ W) ≫ (resCompIso Λ m).hom.app (freeSh Λ W) := by
  rw [← cancel_epi (unitIso Λ W'.left).hom]
  apply (freeEquiv Λ (etId W'.left) _).injective
  have hL : freeEquiv Λ (etId W'.left) _ ((unitIso Λ W'.left).hom ≫ diagSec Λ W' ≫
      (res W'.hom Λ).map (freeMap Λ m)) =
      ((freeSh Λ W).obj.map ((etCompTop W').hom ≫ m).op).hom (taut Λ W) := by
    rw [← Category.assoc, freeEquiv_comp, diagSec_sec]
    refine (NatTrans.naturality_apply (φ := (freeMap Λ m).hom) (etCompTop W').hom.op (taut Λ W')).trans ?_
    refine (congrArg (fun z => ((freeSh Λ W).obj.map (etCompTop W').hom.op).hom z) (freeMap_taut m)).trans ?_
    rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hR : freeEquiv Λ (etId W'.left) _ ((unitIso Λ W'.left).hom ≫ unitRes m.left Λ ≫
      (res m.left Λ).map (diagSec Λ W) ≫ (resCompIso Λ m).hom.app (freeSh Λ W)) =
      ((freeSh Λ W).obj.map ((etCompCompIso m).inv.app (etId W'.left) ≫
        (etComp W.hom).map (toTop ((etComp m.left).obj (etId W'.left))) ≫ (etCompTop W).hom).op).hom
        (taut Λ W) := by
    rw [unitRes, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, freeEquiv_comp, freeEquiv_comp,
      AddEquiv.apply_symm_apply, resCompIso_app, oneRes]
    have hn := NatTrans.naturality_apply (φ := (diagSec Λ W).hom)
      (toTop ((etComp m.left).obj (etId W'.left))).op (oneSec Λ W.left)
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [← diagSec_one]
    exact congrArg (fun z => ((freeSh Λ W).obj.map ((etCompCompIso m).inv.app (etId W'.left)).op).hom z) hn
  refine hL.trans (Eq.trans ?_ hR.symm)
  exact congrArg (fun x => ((freeSh Λ W).obj.map x.op).hom (taut Λ W)) (etCompTop_comp m)

end Nat

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2KapP =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2KapP): restriction of a piece Kummer class along an etale map

For `f : X₁ ⟶ X` etale between affine schemes whose rings are finite products of Dedekind domains, and a Kummer
class `kapS p (kumD α)` on the piece `p` of `X` (`α^d = u`):
* `kerMap f p₁ : Γ(X) → Γ(X₁) ⧸ p₁`, `exists_minimalPrime_le_ker`, `kerLift`, **`piHom_comp_eq`**
  (the piece `p₁` of `X₁` maps into the piece `q` of `X` through `Spec (Γ(X₁) ⧸ p₁) ⟶ Spec (Γ(X) ⧸ q)`),
  `injective_of_etale` (an etale map of domains is injective), `resLE_congr`, `resLE_kapS_self`, `resLE_kapS_ne`;
* **`resLE_kapS_kumD_eq_zero`**: if `u` becomes a `d`-th power in the fraction field of every piece of `X₁` lying
  over `p`, then `resLE f 1 (kapS p (kumD α)) = 0`.
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

universe u

section Fac

end Fac

section KappaRes

end KappaRes

section Red

variable {X X₁ : Scheme.{0}} [IsAffine X] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [Fintype (minimalPrimes Γ(X₁, ⊤))] [DecidableEq (minimalPrimes Γ(X₁, ⊤))] (Λ : Type) [CommRing Λ]
  (f : X₁ ⟶ X) [Etale f]

include h h₁ in
theorem etale_kerLift {p₁ : minimalPrimes Γ(X₁, ⊤)} {q : minimalPrimes Γ(X, ⊤)}
    (hq : (q : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁)) :
    Etale (Spec.map (CommRingCat.ofHom (kerLift hq))) := by
  have hfac := piHom_comp_eq h h₁ f p₁ q hq
  have : Etale (Spec.map (CommRingCat.ofHom (kerLift hq)) ≫ piHom (piEquiv h) q) := by
    rw [← hfac]
    infer_instance
  exact Etale.of_comp (Spec.map (CommRingCat.ofHom (kerLift hq))) (piHom (piEquiv h) q)

end Red

section KapP

end KapP

end RamanujanPetersson.EtPBC.EtKum

end

end

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
include h h₁ in
/-- The radical used on a piece of `X₁` not over `p`. -/
theorem resLE_kapS_kumD_eq_off_v {Hg : Γ(Y, ⊤)}
    (hoff : ∀ (p₁ : minimalPrimes Γ(X₁, ⊤)) (q : minimalPrimes Γ(X, ⊤)), q ≠ p →
      (q : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁) →
      ∀ Ψ : FractionRing (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤))) →+* FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))),
      (∀ a : Γ(X, ⊤), Ψ (algebraMap _ _ (Ideal.Quotient.mk (q : Ideal Γ(X, ⊤)) a)) =
        algebraMap _ _ (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (f.appTop a))) →
      ∃ v : FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))),
        v ^ d = algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (g.appTop Hg)))
    (p₁ : minimalPrimes Γ(X₁, ⊤)) (Q : minimalPrimes Γ(Y, ⊤)) (hQ : (Q : Ideal Γ(Y, ⊤)) ≤ RingHom.ker (kerMap g p₁))
    (q : minimalPrimes Γ(X, ⊤)) (hq : (q : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁)) (hne : q ≠ p) :
    ∃ v : FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))), v ^ d = algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) ((CommRingCat.ofHom (kerLift hQ)).hom (Ideal.Quotient.mk Q.1 Hg)) := by
  have := etale_kerLift h h₁ f hq
  have hinj : Function.Injective (CommRingCat.ofHom (kerLift hq)).hom := injective_of_etale (kerLift hq)
  have hiK : Function.Injective ((algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))))).comp (kerLift hq)) :=
    (IsFractionRing.injective _ _).comp hinj
  have hΨ : ∀ a : Γ(X, ⊤), IsFractionRing.lift (K := (FractionRing (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤))))) hiK
      (algebraMap (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤)))) (Ideal.Quotient.mk (q : Ideal Γ(X, ⊤)) a)) =
      algebraMap (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) (Ideal.Quotient.mk (p₁ : Ideal Γ(X₁, ⊤)) (f.appTop a)) :=
    fun a => IsFractionRing.lift_algebraMap hiK _
  obtain ⟨v, hv⟩ := hoff p₁ q hne hq (IsFractionRing.lift (K := (FractionRing (Γ(X, ⊤) ⧸ (q : Ideal Γ(X, ⊤))))) hiK) hΨ
  exact ⟨v, hv⟩

end KapD

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T1 =====
section

/-!
# S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps

* `resFreeIso Λ e T : Λ_U[e⁻¹T] ≅ (Λ[T])|_U` for etale `e : U ⟶ X` (`pullFreeIso` + `pullIsoRes`);
* `resFreeIso_taut`: its value on the tautological section is the pullback of `taut T` along the counit;
* `graph m : etId W.left ⟶ e⁻¹T` for `m : W ⟶ T` in `P.Etale` (adjoint to `W ≅ etComp (etId) ⟶ T`);
* `secMap Λ m := diagSec Λ W ≫ (res W.hom Λ).map Λ[m] : Λ_W ⟶ (Λ[T])|_W`, `secMap_comp`;
* **`secMap_graph`**: `unitIso.hom ≫ secMap m = Λ[graph m] ≫ resFreeIso.hom`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe u

section Res

end Res

section Graph

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} {W T : P.Etale}

/-- **The section map is the free map of the graph** (under `resFreeIso`). -/
theorem secMap_graph (m : W ⟶ T) :
    (unitIso Λ W.left).hom ≫ secMap Λ m = freeMap Λ (graph m) ≫ (resFreeIso Λ W.hom T).hom := by
  apply (freeEquiv Λ (etId W.left) _).injective
  rw [secMap_sec, freeEquiv_freeMap, resFreeIso_taut]
  show _ = (((freeSh Λ T).obj.map ((etComp W.hom).map (graph m)).op).hom
    (((freeSh Λ T).obj.map ((etCompAdj W.hom).counit.app T).op).hom (taut Λ T)))
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp, graph_counit]

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4a =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4a): `secMap_res` (thetaM moved to O2T4a0 for the 150 user-s cap)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
theorem secMap_res {W' W T : P.Etale} (w : W' ⟶ W) (m : W ⟶ T) :
    secMap Λ (w ≫ m) =
      unitRes w.left Λ ≫ (res w.left Λ).map (secMap Λ m) ≫ (resCompIso Λ w).hom.app (freeSh Λ T) := by
  have hn := (resCompIso Λ w).hom.naturality (freeMap Λ m)
  have hd := diagSec_natural (Λ := Λ) w
  simp only [Functor.comp_map] at hn
  calc secMap Λ (w ≫ m) = (diagSec Λ W' ≫ (res W'.hom Λ).map (freeMap Λ w)) ≫ (res W'.hom Λ).map (freeMap Λ m) := by
        rw [secMap, freeMap_comp, Functor.map_comp, Category.assoc]
    _ = _ := by
        rw [hd]
        simp only [secMap, Functor.map_comp, Category.assoc]
        rw [hn]
        rfl

end Theta

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2a =====
section

/-!
# S4-EtPBC-A, L3b (TB2a): section calculus for base change

* `etPull_hom_ext`: maps into `X ×_Y T` agree if their first components agree;
* `etIdPull g : etId X ≅ X ×_Y Y`, `pullUnit g : Λ_X ≅ g^*Λ_Y`, `pullUnit_one`;
* `unit_hom_ext`: maps out of `Λ_X` are determined by the image of `1`;
* transport of pulled-back sections along `pullIsoRes`, `pullCompIso`, `pullCongr`, `(pull g).map`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2

end TB2

section TB2o

/-! Op-form section calculus: restriction maps are op-morphisms `a : op T ⟶ op Z` that are passed through
unchanged, so consecutive steps meet in syntactically equal terms (this keeps kernel checks cheap). -/

variable {Λ : Type u} [CommRing Λ]

theorem secMap_one {P : Scheme.{u}} {W T : P.Etale} (m : W ⟶ T) :
    ((secMap Λ m).hom.app (op (etId W.left))).hom (oneSec Λ W.left) =
      ((freeSh Λ T).obj.map ((etCompTop W).hom ≫ m).op).hom (taut Λ T) := by
  rw [app_oneSec (secMap Λ m), secMap_sec]

theorem secMap_one_graph {P : Scheme.{u}} {W T : P.Etale} (m : W ⟶ T) :
    ((secMap Λ m).hom.app (op (etId W.left))).hom (oneSec Λ W.left) =
      (((res W.hom Λ).obj (freeSh Λ T)).obj.map (graph m).op).hom
        (((freeSh Λ T).obj.map ((etCompAdj W.hom).counit.app T).op).hom (taut Λ T)) :=
  (secMap_one m).trans ((map_congr_apply (freeSh Λ T) (by exact congrArg Quiver.Hom.op (graph_counit m).symm)
    (taut Λ T)).trans ((mapO_comp_apply (freeSh Λ T) ((etCompAdj W.hom).counit.app T).op
      ((etComp W.hom).map (graph m)).op (taut Λ T)).trans (res_obj_map W.hom (freeSh Λ T) (graph m) _).symm))

theorem pull_secMap_secO {P A : Scheme.{u}} {W T : P.Etale} (q : A ⟶ W.left) (m : W ⟶ T) {Z : A.Etale}
    (a : op ((etPull q).obj (etId W.left)) ⟶ op Z) :
    ((((pull q Λ).map (secMap Λ m)).hom.app (op Z)).hom
      ((((pull q Λ).obj (unitSh Λ W.left)).obj.map a).hom (pbSec q (oneSec Λ W.left)))) =
    ((((pull q Λ).obj ((res W.hom Λ).obj (freeSh Λ T))).obj.map (((etPull q).map (graph m)).op ≫ a)).hom
      (pbSec q (((freeSh Λ T).obj.map ((etCompAdj W.hom).counit.app T).op).hom (taut Λ T)))) :=
  (pullMap_pbSecO q (secMap Λ m) a (oneSec Λ W.left)).trans
    ((congrArg (fun z => ((((pull q Λ).obj ((res W.hom Λ).obj (freeSh Λ T))).obj.map a).hom (pbSec q z)))
      (secMap_one_graph m)).trans
    ((congrArg (fun z => ((((pull q Λ).obj ((res W.hom Λ).obj (freeSh Λ T))).obj.map a).hom z))
      (pbSec_restrict q (graph m) _)).trans (mapO_comp_apply _ _ _ _).symm))

end TB2o

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2b =====
section

/-!
# S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

section TB2b

variable {Λ : Type u} [CommRing Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Etale)

/-- `resPullFree_secO` with the restriction map typed over the base `(fromPUnit X).obj V.right` of `V.hom`
(the typing produced by `etCompTop`), so that it meets `secMap_one` and `pullIsoRes_inv_graph` syntactically. -/
theorem resPullFree_secO2 (V : X.Etale) (T : Y.Etale)
    (r : (@Opposite.op (Scheme.Etale ((Functor.fromPUnit X).obj V.right)) ((etPull f).obj T)) ⟶
      op ((etComp V.hom).obj (etId V.left))) :
    ((((res V.hom Λ).map (pullFreeHom Λ f T)).hom.app (op (etId V.left))).hom
        (((freeSh Λ ((etPull f).obj T)).obj.map r).hom (taut Λ ((etPull f).obj T)))) =
      ((((pull f Λ).obj (freeSh Λ T)).obj.map r).hom (pbSec f (taut Λ T))) :=
  resPullFree_secO f V T r

theorem secMap_oneI {P : Scheme.{u}} {W T : P.Etale} (m : W ⟶ T) :
    ((secMap Λ m).hom.app (@op (Scheme.Etale ((𝟭 Scheme).obj W.left)) (etId W.left))).hom (oneSec Λ W.left) =
      ((freeSh Λ T).obj.map ((etCompTop W).hom ≫ m).op).hom (taut Λ T) :=
  secMap_one m

end TB2b

end RamanujanPetersson.EtPBC.EtMV

end

end


