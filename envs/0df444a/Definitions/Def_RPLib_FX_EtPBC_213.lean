-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_213
-- name    : RPLib_FX_EtPBC_213
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T03:14:29.7788+00:00
-- url     : https://prove2.me/theorems/2d476b12-673f-5db5-8753-6dd4eb823a6a
-- title:
--   Proper base change for the projective line, library file 213
-- statement:
--   File 213 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
--   * `S4.Def_RP_EtPBC_A_EGenP`: S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_208

/-!
# Proper base change for the projective line, library file 213

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
* `S4.Def_RP_EtPBC_A_EGenP`: S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_T3dC =====
section

/-!
# S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly

`π : Y ⟶ P`, `f : P' ⟶ P`, `Φ : U ⟶ P'`, `h : U ⟶ Y` with `h ≫ π = Φ ≫ f`, `ι' : Ps ⟶ P'`, `ι = ι' ≫ f`:
* `hsU : U_s ⟶ Y_s` and `rUs : π_{s*} M_{Y_s} ⟶ φs_* M_{U_s}` (restriction on the fibre);
* **`C1`**: `eC M π ι ≫ rUs = ι^*(restriction) ≫ eC M Φ ι'` (both base change maps are restriction of sections);
* `HypT`: the input that T1 + T2 supply (every extension of `Λ` by `π_{s*} M_{Y_s}` is split by such data);
* **`bcSurj_one_push_of_hypT`**: base change is surjective in degree one for `π_* M_Y`, given `HypT`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC RamanujanPetersson.EtPBC.PushKill

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section C1

end C1

section B3

variable {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **Degree-one base change for `π_* M_Y`** (`π` finite), given degree-zero base change for all sheaves
and the input `HypT` of T1 + T2. -/
theorem bcSurj_one_push_of_hypT [IsClosedImmersion (fibι g s)] (hQ : ∀ Q : EtSh Λ P, BCSurj Λ g s 0 Q)
    {Y : Scheme.{u}} (π : Y ⟶ P) [IsFinite π] (N : ModuleCat.{u} Λ) (hT : HypT Λ g s π N) :
    BCSurj Λ g s 1 ((push π Λ).obj (constSh Λ Y N)) := by
  intro β
  obtain ⟨E, a, b, w, hS, rfl⟩ := exists_ses_extClass β
  have hc : IsIso (eC N π (fibι g s)) := isIso_eC π (fibι g s)
  have w' : (inv (eC N π (fibι g s)) ≫ a) ≫ b = 0 := by rw [Category.assoc, w, comp_zero]
  have hS' : (ShortComplex.mk (inv (eC N π (fibι g s)) ≫ a) b w').ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := ShortComplex.mk a b w)
      (S₂ := ShortComplex.mk (inv (eC N π (fibι g s)) ≫ a) b w') (asIso (eC N π (fibι g s))) (Iso.refl E)
      (Iso.refl _) (by simp) (by simp)) hS
  obtain ⟨P', U, f, hf, ι', hι, hci, Φ, hΦ, h, hh, hsurj, κ₀, hκ₀⟩ := hT E _ b w' hS'
  have hm : Mono (mP N π f Φ h hh) := mono_mP π f Φ h hh hsurj
  refine exists_bc_of_ses_kill g s hQ f ι' hι Φ (mP N π f Φ h hh) a b w hS κ₀ ?_
  have h1 : a ≫ κ₀ = eC N π (fibι g s) ≫ rUs N π f Φ h hh ι' (fibι g s) hι := by
    rw [← hκ₀, Category.assoc, IsIso.hom_inv_id_assoc]
  exact h1.trans ((C1 π f Φ h hh ι' (fibι g s) hι).trans (eq_whisker (liftIso_inv_app g s f ι' hι _).symm _))

end B3

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_EGenP =====
section

/-!
# S4-EtPBC-A, R3 (degree `q`): the generic step for any predicate, and `BCSurj (q+1)` for `FGT` sheaves on `P¹_S`

* **`genStepP_of`**: the generic step `GenStepP Λ C` for any predicate `C` that holds for every `π_* M_Y` with `π`
  finite and `M` finite, `Λ` finite (same proof as `genStep_of`, which is the case `C = BCSurj 0`);
* **`bcInj_one_qV`**: base change is injective on germs in degree `1` for every sheaf on `P¹_S` (δ-lemma from degree
  `0`: `bcInj_zero`, `bcSurj_zero_qV`);
* **`bcSurj_succ_fgt_qV`**: if `BCSurj (q+1)` holds for every `π_* M_Y` (`π` finite, `M` finite; `Λ` finite),
  `BCInj (q+1)` and `BCSurj q`
  for every sheaf, then `BCSurj (q+1)` holds for every `FGT` sheaf on `P¹_S`; **`bcSurj_one_fgt_qV`** (`q = 0`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech GenAlg RamanujanPetersson.EtPBC.Z3

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **`BCSurj (q+1)` for every `FGT` sheaf on `P¹_S`** from the curve case `π_* M_Y`. -/
theorem bcSurj_succ_fgt_qV (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gK)] [IsNoetherian S]
    [LocallyOfFiniteType gK] [IsNoetherianRing Λ] [Finite Λ] (q : ℕ)
    (hI : ∀ G : EtSh Λ (PV K gK), BCInj Λ (qV K gK) s (q + 1) G)
    (hS : ∀ G : EtSh Λ (PV K gK), BCSurj Λ (qV K gK) s q G)
    (hC : ∀ {Y : Scheme.{u}} (π : Y ⟶ PV K gK) [IsFinite π] (M : ModuleCat.{u} Λ) [Finite M],
      BCSurj Λ (qV K gK) s (q + 1) ((push π Λ).obj (constSh Λ Y M)))
    (F : EtSh Λ (PV K gK)) (hF : FGT Λ F) : BCSurj Λ (qV K gK) s (q + 1) F := by
  have : IsNoetherian (PV K gK) := {}
  obtain ⟨H, m, hm, hH⟩ := embP_of_fgt (BCSurj Λ (qV K gK) s (q + 1))
    (fun H hH => Delta.surjAt_of_isZero (q + 1) hH)
    (fun H₁ H₂ h₁ h₂ => Delta.surjAt_biprod (bcUnit_comp Λ (qV K gK) s) (q + 1) h₁ h₂)
    (genStepP_of K p (qV K gK ≫ gK) _ fun π _ M _ => hC π M) F hF
  exact bcSurj_succ_of_mono (qV K gK) s m q hH (hI _) (hS _)

end RamanujanPetersson.EtPBC.GenGeo

end

end


