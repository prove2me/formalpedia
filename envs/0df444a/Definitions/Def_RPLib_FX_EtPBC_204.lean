-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_204
-- name    : RPLib_FX_EtPBC_204
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T02:43:43.28893+00:00
-- url     : https://prove2.me/theorems/f690014b-5e65-540c-91a5-99002961d31e
-- title:
--   Proper base change for the projective line, library file 204
-- statement:
--   File 204 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_FBInj`: S4-EtPBC-A, M2 F3: base change on germs of a constant sheaf (degree `0`)
--   * `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
--   * `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
--   * `S4.Def_RP_EtPBC_A_FBCb`: S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective
--   * `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
--   * `S4.Def_RP_EtPBC_A_EPsiRel`: S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres
--   * `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_EGen`: S4-EtPBC-A, M4(E), EGen: the generic step, and `BCSurj 0` for every sheaf on `P¹_S`
--   * `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_199
import Definitions.Def_RPLib_FX_EtPBC_200

/-!
# Proper base change for the projective line, library file 204

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_FBInj`: S4-EtPBC-A, M2 F3: base change on germs of a constant sheaf (degree `0`)
* `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
* `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
* `S4.Def_RP_EtPBC_A_FBCb`: S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective
* `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
* `S4.Def_RP_EtPBC_A_EPsiRel`: S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres
* `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
* `S4.Def_RP_EtPBC_A_EGen`: S4-EtPBC-A, M4(E), EGen: the generic step, and `BCSurj 0` for every sheaf on `P¹_S`
* `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_FBInj =====
section

/-!
# S4-EtPBC-A, M2 F3: base change on germs of a constant sheaf (degree `0`)

For `g : P ⟶ S`, a geometric point `s` of `S`, `C = constSh Λ P M` and an etale neighbourhood `j = (V, v)`:
* `const_comap_germ`: a section `z` of `C` with value `0` at `cpt b` has zero germ at `comapPt f s` via `b`
  (through Mathlib's point isomorphism `comapPtIso` and `cval_germ` at the geometric point `s ≫ f`);
* `sc_bcUnit_comp`: `(u_v ≫ ι^* f)(1) = σ_v^* η_G(f(1))`;
* **`bc_zero_of_cval`**: if `sec0 α` has value `0` at every point of the fibre `P_s`, then `bc_j α = 0`;
* **`res_zero_of_cval`** / **`germ_zero_of_cval`** (universally closed `g`): such a section restricts to `0` on a
  smaller neighbourhood, i.e. its germ in `(g_* C)_s` vanishes.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.PtSec RamanujanPetersson.EtCompact.Supp

universe u

section Comap

end Comap

section BC

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) {M : ModuleCat.{u} Λ}

/-- **Restriction to a smaller neighbourhood** (universally closed `g`). -/
theorem res_zero_of_cval [UniversallyClosed g] (j : Nbhd s)
    (z : (constSh Λ P M).obj.obj (op ((etPull g).obj j.1)))
    (h : ∀ x : fib g s, cval z (fibToNbhd g s j x) = 0) :
    ∃ (j' : Nbhd s) (a : j' ⟶ j), ((constSh Λ P M).obj.map ((etPull g).map a.1).op).hom z = 0 := by
  let α : Ext.{u} ((nbhdSys Λ g s).obj j) (constSh Λ P M) 0 :=
    Ext.addEquiv₀.symm ((freeEquiv Λ ((etPull g).obj j.1) (constSh Λ P M)).symm z)
  have hα : sec0 Λ g s j (constSh Λ P M) α = z :=
    (congrArg (freeEquiv Λ ((etPull g).obj j.1) (constSh Λ P M)) (Ext.addEquiv₀.apply_symm_apply _)).trans
      ((freeEquiv Λ ((etPull g).obj j.1) (constSh Λ P M)).apply_symm_apply z)
  obtain ⟨j', a, ha⟩ := bcInj_zero Λ g s (constSh Λ P M) j α
    (bc_zero_of_cval Λ g s j α (fun x => by rw [hα]; exact h x))
  refine ⟨j', a, ?_⟩
  rw [Delta.res_apply, ← Ext.mk₀_addEquiv₀_apply α, Ext.mk₀_comp_mk₀, Ext.mk₀_eq_zero_iff] at ha
  have e := freeEquiv_freeMap Λ ((etPull g).map a.1) (constSh Λ P M) (Ext.addEquiv₀ α)
  rw [← hα]
  exact e.symm.trans ((congrArg (freeEquiv Λ ((etPull g).obj j'.1) (constSh Λ P M)) ha).trans (map_zero _))

/-- **The germ in `(g_* C)_s` of a section vanishing along the fibre is `0`** (universally closed `g`). -/
theorem germ_zero_of_cval [UniversallyClosed g] (j : Nbhd s)
    (z : (constSh Λ P M).obj.obj (op ((etPull g).obj j.1)))
    (h : ∀ x : fib g s, cval z (fibToNbhd g s j x) = 0) :
    (s.point.toPresheafFiber j.1 j.2 ((push g Λ).obj (constSh Λ P M)).obj).hom z = 0 := by
  obtain ⟨j', a, ha⟩ := res_zero_of_cval Λ g s j z h
  have hw := ConcreteCategory.congr_hom (s.point.toPresheafFiber_w a.1 j'.2 ((push g Λ).obj (constSh Λ P M)).obj) z
  have hj : s.point.fiber.map a.1 j'.2 = j.2 := a.2
  refine (congrArg (fun x => (s.point.toPresheafFiber j.1 x ((push g Λ).obj (constSh Λ P M)).obj).hom z)
    hj.symm).trans (hw.symm.trans ?_)
  change (s.point.toPresheafFiber j'.1 j'.2 ((push g Λ).obj (constSh Λ P M)).obj).hom
    (((constSh Λ P M).obj.map ((etPull g).map a.1).op).hom z) = 0
  rw [ha]
  exact LinearMap.map_zero _

end BC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Psi =====
section

/-!
# S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre

For `π : Y ⟶ P`, a geometric point `t` of `P` and `C = constSh Λ Y M`:
* `cval_sub`, `cval_res`, `germ_res` (restriction to a smaller neighbourhood);
* `cval_eq_of_germ_eq`: equal germs in `(π_* C)_t` have equal values along the fibre `fib π t`;
* **`germ_eq_of_cval`** (universally closed `π`): conversely, equal values give equal germs;
* `psi e x`: the value at `x ∈ fib π t` of a germ `e ∈ (π_* C)_t`; **`psi_germ`**;
* **`eq_of_psi`** (universally closed, quasi-compact `π`): germs with equal values at the closed points of the
  fibre are equal.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y P : Scheme.{u}} (π : Y ⟶ P) (t : GeomPt P) {M : ModuleCat.{u} Λ}

/-- **Equal values along the fibre give equal germs** (universally closed `π`). -/
theorem germ_eq_of_cval [UniversallyClosed π] {j₁ j₂ : Nbhd t}
    (z₁ : (constSh Λ Y M).obj.obj (op ((etPull π).obj j₁.1)))
    (z₂ : (constSh Λ Y M).obj.obj (op ((etPull π).obj j₂.1)))
    (h : ∀ x : fib π t, cval z₁ (fibToNbhd π t j₁ x) = cval z₂ (fibToNbhd π t j₂ x)) :
    (t.point.toPresheafFiber j₁.1 j₁.2 ((push π Λ).obj (constSh Λ Y M)).obj).hom z₁ =
      (t.point.toPresheafFiber j₂.1 j₂.2 ((push π Λ).obj (constSh Λ Y M)).obj).hom z₂ := by
  let j₃ := IsCofiltered.min j₁ j₂
  let a₁ := IsCofiltered.minToLeft j₁ j₂
  let a₂ := IsCofiltered.minToRight j₁ j₂
  have h3 : ∀ x : fib π t, cval (((constSh Λ Y M).obj.map ((etPull π).map a₁.1).op).hom z₁ -
      ((constSh Λ Y M).obj.map ((etPull π).map a₂.1).op).hom z₂) (fibToNbhd π t j₃ x) = 0 := by
    intro x
    refine (cval_sub _ _ _).trans ?_
    rw [cval_res π t a₁ z₁ x, cval_res π t a₂ z₂ x, h x, sub_self]
  have h0 := germ_zero_of_cval Λ π t j₃ _ h3
  have h1 := sub_eq_zero.1 ((LinearMap.map_sub _ _ _).symm.trans h0)
  exact (germ_res π t a₁ z₁).symm.trans (h1.trans (germ_res π t a₂ z₂))

/-- **Germs with equal values at the closed points of the fibre are equal.** -/
theorem eq_of_psi [UniversallyClosed π] [QuasiCompact π]
    (e₁ e₂ : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj ((push π Λ).obj (constSh Λ Y M)).obj)
    (h : ∀ x : fib π t, IsClosed ({x} : Set (fib π t)) → psi π t e₁ x = psi π t e₂ x) : e₁ = e₂ := by
  obtain ⟨X, x, z₁, z₂, h₁, h₂⟩ := t.point.toPresheafFiber_jointly_surjective₂ e₁ e₂
  let j : Nbhd t := ⟨X, x⟩
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  refine germ_eq_of_cval π t (j₁ := j) (j₂ := j) z₁ z₂ fun y => ?_
  by_contra hne
  have hS : IsClosed ((fibToNbhd π t j) ⁻¹' supp (constSh Λ Y M) (z₁ - z₂)) :=
    (isClosed_supp (constSh Λ Y M) (z₁ - z₂)).preimage (fibToNbhd π t j).continuous
  have hmem : ∀ y' : fib π t, y' ∈ (fibToNbhd π t j) ⁻¹' supp (constSh Λ Y M) (z₁ - z₂) ↔
      cval z₁ (fibToNbhd π t j y') ≠ cval z₂ (fibToNbhd π t j y') := by
    intro y'
    refine (mem_supp_iff_cval (T := (etPull π).obj X) (z₁ - z₂) ((fibToNbhd π t j) y')).trans ?_
    exact (congrArg (fun m => m ≠ (0 : M)) (cval_sub z₁ z₂ ((fibToNbhd π t j) y'))).to_iff.trans sub_ne_zero
  obtain ⟨y₀, hy₀, hcl⟩ := hS.exists_closed_singleton ⟨y, (hmem y).2 hne⟩
  refine (hmem y₀).1 hy₀ ?_
  exact (psi_germ π t j z₁ y₀).symm.trans ((congrArg (fun e => psi π t e y₀) h₁).trans
    ((h y₀ hcl).trans ((congrArg (fun e => psi π t e y₀) h₂).symm.trans (psi_germ π t j z₂ y₀))))

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_VPart =====
section

/-!
# S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values

* `vval_locConst₂`: `vval_locConst` with test points over any separably closed field;
* `vv b q := vval b (geomPtAt q).pt`, **`vval_eq_vv`** (`vval b τ = vv b (τ pt)`), **`isLocallyConstant_vv`**;
* `fibInc σ : fib π (σ ≫ ι) ⟶ Y ×_P X` and **`psi_xi_eq_vval`**: `Ψ(ξ_σ b)(x) = vval b (x̄ ≫ fibInc σ)`;
* `ysj j : Y ×_P P_s ⟶ Y ×_P P_V` and **`vval_bc`**: the value of a base-changed class is `cval z ∘ ysj j`;
* **`bc_eq_of_vv`**: a section `z` over `Y ×_P P_V` with `cval z ∘ ysj j = vv b` gives `bc z = b`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Gen

end Gen

section BC

variable {Λ : Type u} [CommRing Λ] {P S Y : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) (π : Y ⟶ P)
  {M : ModuleCat.{u} Λ}

/-- **Base change of a section with the right values.** -/
theorem bc_eq_of_vv [UniversallyClosed π] [QuasiCompact π]
    (b : unitSh Λ (fib g s) ⟶ (pull (fibι g s) Λ).obj ((push π Λ).obj (constSh Λ Y M))) (j : Nbhd s)
    (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj ((etPull g).obj j.1))))
    (hz : ∀ q, cval z (ysj g s π j q) = vv (fibι g s) π b q) :
    bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map
      ((freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M))).symm z) = b := by
  have hφ : freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M))
      ((freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M))).symm z) = z :=
    AddEquiv.apply_symm_apply _ z
  have hval : ∀ (σ : GeomPt (fib g s)) (x : fib π (σ.map (fibι g s))),
      psi π (σ.map (fibι g s)) (xi (fibι g s) σ ((push π Λ).obj (constSh Λ Y M)) b) x =
      psi π (σ.map (fibι g s)) (xi (fibι g s) σ ((push π Λ).obj (constSh Λ Y M))
        (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map
          ((freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M))).symm z))) x := by
    intro σ x
    refine (psi_xi_eq_vval (fibι g s) π b σ x).trans (Eq.trans ?_ (psi_xi_eq_vval (fibι g s) π
      (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map
        ((freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M))).symm z)) σ x).symm)
    refine (vval_eq_vv (fibι g s) π b _).trans (Eq.trans ?_ (vval_bc g s π j
      ((freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M))).symm z) _).symm)
    refine Eq.trans ?_ (congrArg (fun c => cval (T := (etPull π).obj ((etPull g).obj j.1)) c
      (ysj g s π j (((geomPtAt x).pt ≫ fibInc (fibι g s) π σ)
        (default : Spec (CommRingCat.of (geomPtAt x).Ω))))) hφ.symm)
    exact (hz _).symm
  refine (sub_eq_zero.1 ?_).symm
  refine hom_ext_stalk Λ fun y => ?_
  refine stalk_unitSh_hom_ext Λ y ?_
  rw [stalk_sc _ y (etId (fib g s)) (geomPtAt y).top, Functor.map_zero]
  have hxi : xi (fibι g s) (geomPtAt y) ((push π Λ).obj (constSh Λ Y M)) (b -
      bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map
        ((freeEquiv Λ ((etPull g).obj j.1) ((push π Λ).obj (constSh Λ Y M))).symm z)) = 0 := by
    rw [xi_sub]
    exact sub_eq_zero.2 (eq_of_psi π ((geomPtAt y).map (fibι g s)) _ _ fun x _ => hval (geomPtAt y) x)
  exact (germ_eq_zero_of_xi (fibι g s) (geomPtAt y) _ _ hxi).trans rfl

end BC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCb =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective

`Φ : U ⟶ P` finite, `ι : Ps ⟶ P` a closed immersion, `h = pullback.fst Φ ι`, `t` a geometric point of `P`
through `Ps` (`σ₀ ≫ ι = t.pt`): the stalk map of `rU M h Φ` at `t` is bijective (`rStk_bijective`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.SgUnit

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section Stalk

variable {U P Ps : Scheme.{u}} (Φ : U ⟶ P) (ι : Ps ⟶ P)

/-- **The stalk of `rU` at a geometric point through `Ps` is bijective.** -/
theorem rStk_bijective [IsFinite Φ] [IsClosedImmersion ι] (t : GeomPt P) (σ₀ : Spec (CommRingCat.of t.Ω) ⟶ Ps)
    (hσ : σ₀ ≫ ι = t.pt) :
    Function.Bijective
      ((t.point.presheafFiber (A := ModuleCat.{u} Λ)).map (rU M (pullback.fst Φ ι) Φ).hom).hom := by
  have : IsFinite (pullback.fst Φ ι ≫ Φ) := inferInstance
  have hsec : ∀ x : fib Φ t, nuU (pullback.fst Φ ι) Φ t (secU Φ ι t σ₀ hσ x) = x := fun x =>
    congrArg (fun φ => φ.base x) (secU_nuU Φ ι t σ₀ hσ)
  constructor
  · intro e₁ e₂ he
    apply eq_of_psi Φ t
    intro x _
    have h1 := psi_rStk Φ ι t e₁ (secU Φ ι t σ₀ hσ x)
    have h2 := psi_rStk Φ ι t e₂ (secU Φ ι t σ₀ hσ x)
    rw [hsec] at h1 h2
    rw [← h1, ← h2, he]
  · intro e'
    obtain ⟨j, z', rfl⟩ := exists_rep (pullback.fst Φ ι ≫ Φ) t e'
    classical
    let μ := muU (pullback.fst Φ ι) Φ j.1
    let v : ↑(pullback j.1.hom Φ) → M := fun y => if hy : ∃ a, μ a = y then cval z' hy.choose else 0
    obtain ⟨j', a, z, hz⟩ := exists_sec_vals Φ t j v
    refine ⟨(t.point.toPresheafFiber j'.1 j'.2 ((push Φ Λ).obj (constSh Λ U M)).obj).hom z, ?_⟩
    apply eq_of_psi (pullback.fst Φ ι ≫ Φ) t
    intro x _
    refine (psi_rStk Φ ι t _ x).trans ((psi_germ Φ t j' z _).trans ((hz _).trans ?_))
    have hm : μ (fibToNbhd (pullback.fst Φ ι ≫ Φ) t j x) = fibToNbhd Φ t j (nuU (pullback.fst Φ ι) Φ t x) :=
      congrArg (fun φ => φ.base x) (muU_fibToNbhd (pullback.fst Φ ι) Φ t j)
    have hy : ∃ a, μ a = fibToNbhd Φ t j (nuU (pullback.fst Φ ι) Φ t x) := ⟨_, hm⟩
    refine (dif_pos hy).trans ?_
    have hinj := muU_injective (pullback.fst Φ ι) Φ j.1 (hy.choose_spec.trans hm.symm)
    exact (congrArg (cval z') hinj).trans (psi_germ (pullback.fst Φ ι ≫ Φ) t j z' x).symm

end Stalk

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCc =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion

`Φ : U ⟶ P` finite, `ι : Ps ⟶ P` a closed immersion, `φs = pullback.snd Φ ι : U ×_P Ps ⟶ Ps`:
* `rC M Φ ι : Φ_* M_U ⟶ ι_* φs_* M_{U_s}` (restriction of sections to `U_s`);
* `eC M Φ ι : ι^* Φ_* M_U ⟶ φs_* M_{U_s}` its adjoint;
* **`isIso_eC`**: `eC` is an isomorphism (stalks via `rStk_bijective`, closed-immersion counit iso).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.SgUnit

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section BC

variable {U P Ps : Scheme.{u}} (Φ : U ⟶ P) (ι : Ps ⟶ P)

/-- Stalks of `rC` at geometric points through `Ps` are isomorphisms. -/
theorem isIso_stalk_rC [IsFinite Φ] [IsClosedImmersion ι] (s : GeomPt Ps) :
    IsIso (((s.map ι).stalkF Λ).map (rC M Φ ι)) := by
  have h1 : IsIso (((s.map ι).stalkF Λ).map (rU M (pullback.fst Φ ι) Φ)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact rStk_bijective Φ ι (s.map ι) s.pt rfl
  simp only [rC, Functor.map_comp]
  infer_instance

end BC

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_EPsiRel =====
section

/-!
# S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres

For `π : Y ⟶ P` and `C = constSh Λ Y M`:
* `cval_smul`; `psi_add`, `psi_smul`, `psi_zero`: `psi` is linear;
* **`psi_rel`**: the value of `rel W (π_* C) f x l` at `q ∈ fib π x̄` is `Σ l(j, a) · cval (f j) (fibToNbhd ⟨W j, a⟩ q)`;
* **`rel_eq_zero_iff`** (`π` universally closed and quasi-compact): `rel W (π_* C) f x l = 0` iff these sums vanish
  at the closed points of the fibre.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenAlg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y P : Scheme.{u}} {M : ModuleCat.{u} Λ}

variable (π : Y ⟶ P) (t : GeomPt P)

variable {J : Type u} (W : J → P.Etale)

/-- **A combination of germs of `π_* C` vanishes iff its values vanish at the closed points of the fibre.** -/
theorem rel_eq_zero_iff [UniversallyClosed π] [QuasiCompact π]
    (f : ∀ j, ((push π Λ).obj (constSh Λ Y M)).obj.obj (op (W j))) (x : P)
    (l : (Σ j, (geomPtAt x).point.fiber.obj (W j)) →₀ Λ) :
    rel W _ f x l = 0 ↔ ∀ q : fib π (geomPtAt x), IsClosed ({q} : Set (fib π (geomPtAt x))) →
      (l.sum fun p c => c • cval (M := M) (f p.1) (fibToNbhd π (geomPtAt x) ⟨W p.1, p.2⟩ q)) = 0 := by
  constructor
  · intro h q _
    rw [← psi_rel, h]
    exact psi_zero π _ q
  · intro h
    refine eq_of_psi π (geomPtAt x) _ _ fun q hq => ?_
    rw [psi_rel, h q hq]
    exact (psi_zero π _ q).symm

end RamanujanPetersson.EtPBC.GenAlg

end

end

-- ===== S4.Def_RP_EtPBC_A_EF =====
section

/-!
# S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`

* `xmap ξ g : Spec κ(ξ) ×_P V ⟶ Spec κ(ξ) ×_P W`, `xmap_κp` (naturality of `κp`);
* `exists_gen_pt`: every point of `V ×_P Y` generizes to a point over the generic point `yg` of `Y`;
* `exists_κp_pre`: points of `V ×_P Y` over `yg` come from `X'`;
* `exists_beta`: a point of `X'_V` gives a fibre point `β` of `V` with `xmap g e = sx (τ (g β)) pt`;
* `key_pt`: the images of a point over `yg` in `W ×_P Y` are the sheet points `κp (sx (τ (g β)) pt)`;
* **`ef_rel`**: if `f_j` takes the value `[p]` at the sheet point of `p`, every relation of the `z_j` at any point
  `x` is a relation of the `f_j`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech GenAlg

universe u

variable {P : Scheme.{u}} {T : P.Etale} (ξ : T.left)

section Rel

variable {Λ : Type u} [CommRing Λ] (F : EtSh Λ P) {J : Type u} (W : J → P.Etale)
  (z : ∀ j, F.obj.obj (op (W j))) (η : P)

/-- **EF: relations of the `z_j` are relations of the `f_j`.** -/
theorem ef_rel [Finite J] [∀ j, QuasiCompact (W j).hom] (t : (geomPtAt η).point.fiber.obj T)
    (τ : ∀ p : FibPts η W, T ⟶ W p.1) (hτ : ∀ p, (geomPtAt η).point.fiber.map (τ p) t = p.2)
    [IsFinite (πn T (fpt η t))]
    (f : ∀ j, ((push (πn T (fpt η t)) Λ).obj (constSh Λ (Yn T (fpt η t)) (Mq F W z η))).obj.obj (op (W j)))
    (hval : ∀ p : FibPts η W,
      cval (f p.1) (κp (fpt η t) (W p.1) (sx (fpt η t) (W p.1) (τ p) default)) = mkv F W z η p)
    (x : P) (l : FibPts x W →₀ Λ) (hl : GenAlg.rel W F z x l = 0) : GenAlg.rel W _ f x l = 0 := by
  classical
  obtain ⟨V, v, u, hu, h0⟩ := exists_kill F x W z {l} fun c hc => by
    rw [Finset.mem_singleton.1 hc]
    exact hl
  have h0 := h0 l (Finset.mem_singleton_self l)
  refine (rel_eq_zero_iff (πn T (fpt η t)) W f x l).2 fun q _ => ?_
  have hw : ∀ p : FibPts x W, fibToNbhd (πn T (fpt η t)) (geomPtAt x) ⟨W p.1, p.2⟩ q =
      ((etPull (πn T (fpt η t))).map (u p)).left (fibToNbhd (πn T (fpt η t)) (geomPtAt x) ⟨V, v⟩ q) := by
    intro p
    let a : (geomPtAt x).point.fiber.elementsMk V v ⟶ (geomPtAt x).point.fiber.elementsMk (W p.1) p.2 :=
      ⟨u p, hu p⟩
    have h1 := congrArg (fun φ => φ.base q) (fibToNbhd_map (πn T (fpt η t)) (geomPtAt x) a)
    exact h1.symm.trans (Scheme.Hom.comp_apply _ _ q)
  obtain ⟨ν, hνw, hν⟩ := exists_gen_pt (fpt η t) V (fibToNbhd (πn T (fpt η t)) (geomPtAt x) ⟨V, v⟩ q)
  obtain ⟨β, hβ⟩ := key_pt η t V ν hν
  let φ : FibPts x W → FibPts η W := fun p => ⟨p.1, (geomPtAt η).point.fiber.map (u p) β⟩
  have hterm : ∀ p : FibPts x W, cval (M := Mq F W z η) (f p.1)
      (fibToNbhd (πn T (fpt η t)) (geomPtAt x) ⟨W p.1, p.2⟩ q) = mkv F W z η (φ p) := by
    intro p
    let c : (constSh Λ (Yn T (fpt η t)) (Mq F W z η)).obj.obj
        (op ((etPull (πn T (fpt η t))).obj (W p.1))) := f p.1
    let mp := (etPull (πn T (fpt η t))).map (u p)
    calc cval c (fibToNbhd (πn T (fpt η t)) (geomPtAt x) ⟨W p.1, p.2⟩ q)
        = cval c (mp.left (fibToNbhd (πn T (fpt η t)) (geomPtAt x) ⟨V, v⟩ q)) := congrArg (cval c) (hw p)
      _ = cval (((constSh Λ (Yn T (fpt η t)) (Mq F W z η)).obj.map mp.op).hom c)
          (fibToNbhd (πn T (fpt η t)) (geomPtAt x) ⟨V, v⟩ q) := (cval_map mp c _).symm
      _ = cval (((constSh Λ (Yn T (fpt η t)) (Mq F W z η)).obj.map mp.op).hom c) ν :=
          (cval_eq_of_specializes _ hνw).symm
      _ = cval c (mp.left ν) := cval_map mp c ν
      _ = cval c (κp (fpt η t) (W p.1) (sx (fpt η t) (W p.1) (τ (φ p)) default)) :=
          congrArg (cval c) (hβ (W p.1) (u p) (fun b => τ ⟨p.1, b⟩) (fun b => hτ ⟨p.1, b⟩))
      _ = mkv F W z η (φ p) := hval (φ p)
  let c' : FibPts η W →₀ Λ := Finsupp.linearCombination Λ (fun p => Finsupp.single (φ p) (1 : Λ)) l
  have hrel : GenAlg.rel W F z η c' = 0 := by
    have e1 : GenAlg.rel W F z η c' = Finsupp.linearCombination Λ
        (fun p : FibPts x W => GenAlg.germ F η β ((F.obj.map (u p).op).hom (z p.1))) l := by
      refine (Finsupp.apply_linearCombination Λ (GenAlg.rel W F z η) _ l).trans ?_
      refine congrArg (fun v => Finsupp.linearCombination Λ v l) (funext fun p => ?_)
      show GenAlg.rel W F z η (Finsupp.single (φ p) 1) = _
      rw [GenAlg.rel, Finsupp.linearCombination_single, one_smul]
      exact (germ_map F η (u p) β (z p.1)).symm
    exact e1.trans ((Finsupp.apply_linearCombination Λ
      ((geomPtAt η).point.toPresheafFiber V β F.obj).hom _ l).symm.trans ((congrArg _ h0).trans (map_zero _)))
  calc (l.sum fun p c => c • cval (M := Mq F W z η) (f p.1)
        (fibToNbhd (πn T (fpt η t)) (geomPtAt x) ⟨W p.1, p.2⟩ q))
      = l.sum (fun p c => c • mkv F W z η (φ p)) := Finsupp.sum_congr fun p _ => by rw [hterm p]
    _ = Submodule.mkQ (LinearMap.ker (GenAlg.rel W F z η)) c' := by
      rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
      rfl
    _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 hrel

end Rel

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_EGen =====
section

/-!
# S4-EtPBC-A, M4(E), EGen: the generic step, and `BCSurj 0` for every sheaf on `P¹_S`

* **`genStep_of`**: on a noetherian `P` locally of finite type over a perfect field, if `BCSurj 0` holds for every
  `π_* M_Y` with `π` finite, then the generic step `GenStep` holds;
* **`genStep_qV`**: the generic step for `P¹_S ⟶ S` (`S` noetherian of finite type over a perfect field `K`, `s` a
  geometric point with `s ≫ g_K` an isomorphism);
* **`bcSurj_zero_qV`**: base change is surjective in degree `0` for every sheaf on `P¹_S`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech GenAlg RamanujanPetersson.EtPBC.Z3

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **The generic step from `BCSurj 0` for pushforwards of constant sheaves along finite maps.** -/
theorem genStep_of (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (h : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] [NoetherianSpace P] [IsNoetherianRing Λ]
    (hBC : ∀ {Y : Scheme.{u}} (π : Y ⟶ P) [IsFinite π] (M : ModuleCat.{u} Λ),
      BCSurj Λ g s 0 ((push π Λ).obj (constSh Λ Y M))) : GenStep Λ g s := by
  classical
  intro Z hZ hne F hF _
  obtain ⟨J, hJ, W, hW, e, he⟩ := hF
  have : ∀ j, IsAffine (W j).left := hW
  obtain ⟨η, hηZ, V₀, hηV₀, hV₀⟩ := exists_generic_open Z hZ hne
  have hqc : ∀ V : P.Etale, IsAffine V.left → QuasiCompact V.hom := fun V _ => by
    have : CompactSpace V.left := inferInstance
    exact @quasiCompact_of_compactSpace _ _ V.hom this (inferInstanceAs (QuasiSeparatedSpace P))
  have : ∀ j, QuasiCompact (W j).hom := fun j => hqc _ (hW j)
  obtain ⟨T, t, τ, hτ, hgood, huniq⟩ := exists_good F hqc η W hW (gen e)
  have hfin : IsFinite (πn T (fpt η t)) := isFinite_πn T (fpt η t) K p h
  have hfib : ∀ j, Finite ((geomPtAt η).point.fiber.obj (W j)) := fun j => finite_fiber (W j) η
  have hsh : ∀ j, ∃ C : (geomPtAt η).point.fiber.obj (W j) → Set (Up (fpt η t) (W j)),
      (∀ b, IsClopen (C b)) ∧ (∀ u, ∃! b, u ∈ C b) ∧
      (∀ b, κp (fpt η t) (W j) (sx (fpt η t) (W j) (τ ⟨j, b⟩) default) ∈ C b) := fun j => by
    have := hfib j
    exact exists_sheets (W j) η t (fun b => τ ⟨j, b⟩) (fun b => hτ ⟨j, b⟩)
  choose C hCo hCp hCd using hsh
  have hfs : ∀ j, ∃ fj : (constSh Λ (Yn T (fpt η t)) (Mq F W (gen e) η)).obj.obj
      (op ((etPull (πn T (fpt η t))).obj (W j))), ∀ b (u : ((etPull (πn T (fpt η t))).obj (W j)).left),
      u ∈ C j b → cval fj u = mkv F W (gen e) η ⟨j, b⟩ := fun j => by
    have := hfib j
    exact exists_fsec (V := (etPull (πn T (fpt η t))).obj (W j)) (C j) (hCo j) (hCp j) _
  choose f hf using hfs
  let H : EtSh Λ P := (push (πn T (fpt η t)) Λ).obj (constSh Λ (Yn T (fpt η t)) (Mq F W (gen e) η))
  obtain ⟨φ, hφ⟩ := exists_desc e he H (fun j => f j) fun x l hl =>
    LinearMap.mem_ker.2 (ef_rel F W (gen e) η t τ hτ (fun j => f j) (fun q => hf q.1 q.2 _ (hCd q.1 q.2)) x l
      (LinearMap.mem_ker.1 hl))
  have hTo : IsOpen (Set.range T.hom) := by
    have : Etale T.hom := T.prop
    exact T.hom.isOpenMap.isOpen_range
  refine ⟨⟨Set.range T.hom ∩ V₀, hTo.inter V₀.isOpen⟩, H, φ, hBC _ _, ?_, ?_⟩
  · exact ⟨η, ⟨⟨fpt η t, fib_over η t⟩, hηV₀⟩, hηZ⟩
  · rintro x ⟨⟨⟨v, rfl⟩, hxV₀⟩, hxZ⟩
    have hsp : η ⤳ T.hom v := specializes_iff_mem_closure.2 (hV₀ ⟨hxV₀, hxZ⟩)
    have hξv := specializes_of_unique T η t huniq v hsp
    refine mono_stalk e he φ (T.hom v) fun l hl => ?_
    rw [show (fun j => (φ.hom.app (op (W j))).hom (gen e j)) = fun j => f j from funext hφ] at hl
    exact LinearMap.mem_ker.2 (eg_rel F W (gen e) η t τ hτ hgood (fun q => C q.1 q.2)
      (fun q => (hCo q.1 q.2).isClosed) (fun q => hCd q.1 q.2) f (fun q u hu => hf q.1 q.2 u hu) v hξv l
      (LinearMap.mem_ker.1 hl))

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gd =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes

* `graph_left_eq_of_fib`: sections with the same value at a geometric point have meeting graphs there;
* `mem_graph_of_card`: if disjoint graphs of sections `τ i : W ⟶ T` are at least as many as the points of every
  geometric fibre of `T` (finite), every point of `W ×_P T` lies on one of the graphs;
* `isZero_freeSh_of_isEmpty`, `ext_eq_zero_of_isZero`;
* **`isLoc_free_good`**: for `T` quasi-compact separated etale over `P` and `z = c (X = a)` a point where the fibre of
  `T` is as large as any fibre (a good point: constant degree near `z`), every one-point class at `z` with
  coefficients `Λ[T]` is in the subgroup generated by the point classes `PtCls` (the residual of `isLoc_free_decomp`
  is EMPTY).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk RamanujanPetersson.EtPBC.EtDed

universe u w

section GoodGeo

end GoodGeo

section Zero

end Zero

section GenZero

universe w' v₁ u₁ v₂ u₂ v₃ u₃

end GenZero

section Good

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P)
  [IsOpenImmersion c] (a : k) {N : ℕ} [NeZero N] (hN : (N : k) ≠ 0) (hΛ : ∀ x : Λ, N • x = 0)

set_option backward.isDefEq.respectTransparency false in
include hN hΛ in
def clsD_graph_mem {T : P.Etale} {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B)
    [hφE : Etale (Spec.map φ ≫ c)] (hφ : φ.hom.Etale)
    [hded : IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime)
    {Uz : P.Opens} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a))
    (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)
    (hS : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact) (τ : chEt c φ ⟶ T)
    (Y' : H Λ ((res (toD1 c φ a).left Λ).obj (freeSh Λ (etId (chEt c φ).left))) 1) :
    PtCls Λ c hN hΛ T (clsD c φ a hUz hS (freeMap Λ (graph τ) ≫ (resFreeIso Λ (chEt c φ).hom T).hom) Y') := by
  obtain ⟨c', hc'⟩ := clsD_graph c φ a hN hΛ hUz hS hφ ht hP τ Y'
  exact ⟨a, B, φ, hφE, Uz, hUz, hS, τ, c', hφ, hded, ht, hP, hz, hc'⟩

end Good

end RamanujanPetersson.EtPBC.EtMV

end

end


