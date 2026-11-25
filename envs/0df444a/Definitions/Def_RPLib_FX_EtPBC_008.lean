-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_008
-- name    : RPLib_FX_EtPBC_008
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:18:02.147881+00:00
-- url     : https://prove2.me/theorems/bb84b8cb-116b-5f11-a07e-62ecde29a4f9
-- title:
--   Proper base change for the projective line, library file 008
-- statement:
--   File 008 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--   * `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
--   * `S4.Def_RP_EtPBC_A_O2N3`: S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_003

/-!
# Proper base change for the projective line, library file 008

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
* `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
* `S4.Def_RP_EtPBC_A_O2N3`: S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2Fl =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero

For an etale `e : U ⟶ X` and `V : U.Etale`:
* `res e` is additive and exact (left and right adjoint);
* **`lshFreeIso`**: `Λ[e ∘ V] ≅ e_! Λ[V]`.
For `W : P.Etale`:
* **`freeLshIso`**: `Λ[W] ≅ e_! Λ_W` (`e = W.hom`);
* **`extFree`**: `Ext_P(Λ[W], F) ≃ H(W, F|_W)`, with `extFree_comp_mk₀` (natural in `F`) and `ext_free_eq_zero`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ]

section Free

variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e]

instance res_preservesFiniteColimits' : PreservesFiniteColimits (res e Λ) := inferInstance

end Free

section GenFl

universe w₁ v₁ u₁ v₂ u₂

end GenFl

section Obj

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N1a =====
section

/-!
# S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`

For an etale `g : U ⟶ X` and `y : U` (generalizing `GalTr`, which treats open immersions):
* `eE g y`: the geometric points `ȳ ≫ g` and `(g y)‾` are isomorphic (`κ(y)/κ(g y)` is finite separable, so
  `κ(y)^sep` is a separable closure of `κ(g y)`); `sepE g y : κ(g y)^sep ≃ κ(y)^sep`;
* `galTrE g y : Gal y →* Gal (g y)` (conjugation by `sepE`, `galTrE_left`);
* `resTrIsoE g y Λ F : (g^* F)_ȳ ≅ F_(g y)‾`, natural (`resTrIsoE_natural`) and **Galois equivariant**
  (`galRep_resTrE`: `galRep (g^* F) y σ` corresponds to `galRep F (g y) (galTrE σ)`);
* `unitRes g Λ : Λ_U ⟶ g^* Λ_X` (the section `1` goes to the restriction of `1`), `resTrIsoE_unitRes`
  (`1 ↦ 1` on stalks), **`isIso_unitRes`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.GenAlg

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) (y : U)

variable [Etale g]

/-- `κ(g y)^sep ≃ κ(y)^sep`: the `IsSepClosure.equiv` behind `eE`. -/
def sepE : SeparableClosure (X.residueField (g y)) ≃+* SeparableClosure (U.residueField y) :=
  letI : Algebra (X.residueField (g y)) (SeparableClosure (U.residueField y)) :=
    (g.residueFieldMap y ≫ CommRingCat.ofHom (algebraMap (U.residueField y)
      (SeparableClosure (U.residueField y)))).hom.toAlgebra
  haveI : IsSepClosure (X.residueField (g y)) (SeparableClosure (U.residueField y)) :=
    ⟨inferInstance, sep_mapE g y⟩
  (IsSepClosure.equiv (X.residueField (g y)) (SeparableClosure (X.residueField (g y)))
    (SeparableClosure (U.residueField y))).toRingEquiv

theorem eE_hom_left : (eE g y).hom.left = Spec.map (CommRingCat.ofHom ((sepE g y : SeparableClosure
    (X.residueField (g y)) →+* SeparableClosure (U.residueField y)))) := rfl

theorem eE_inv_left : (eE g y).inv.left = Spec.map (CommRingCat.ofHom (((sepE g y).symm : SeparableClosure
    (U.residueField y) →+* SeparableClosure (X.residueField (g y))))) := rfl

theorem sepE_algebraMap (r : X.residueField (g y)) :
    sepE g y (algebraMap _ (SeparableClosure (X.residueField (g y))) r) =
      algebraMap (U.residueField y) (SeparableClosure (U.residueField y)) ((g.residueFieldMap y).hom r) :=
  letI : Algebra (X.residueField (g y)) (SeparableClosure (U.residueField y)) :=
    (g.residueFieldMap y ≫ CommRingCat.ofHom (algebraMap (U.residueField y)
      (SeparableClosure (U.residueField y)))).hom.toAlgebra
  haveI : IsSepClosure (X.residueField (g y)) (SeparableClosure (U.residueField y)) :=
    ⟨inferInstance, sep_mapE g y⟩
  (IsSepClosure.equiv (X.residueField (g y)) (SeparableClosure (X.residueField (g y)))
    (SeparableClosure (U.residueField y))).commutes r

/-- `σ ∈ Gal(κ(y)^sep/κ(y))` transported to `κ(g y)^sep` along `sepE`. -/
def galTrER (σ : Gal y) : SeparableClosure (X.residueField (g y)) ≃+* SeparableClosure (X.residueField (g y)) :=
  (sepE g y).trans (σ.toRingEquiv.trans (sepE g y).symm)

theorem galTrER_apply (σ : Gal y) (x : SeparableClosure (X.residueField (g y))) :
    galTrER g y σ x = (sepE g y).symm (σ (sepE g y x)) := rfl

theorem galTrER_fix (σ : Gal y) (r : X.residueField (g y)) :
    galTrER g y σ (algebraMap _ (SeparableClosure (X.residueField (g y))) r) =
      algebraMap _ (SeparableClosure (X.residueField (g y))) r := by
  rw [galTrER_apply, sepE_algebraMap, AlgEquiv.commutes, ← sepE_algebraMap, RingEquiv.symm_apply_apply]

/-- **The Galois transport** `Gal(y) → Gal(g y)` along the etale map `g`. -/
def galTrE (σ : Gal y) : Gal (g y) :=
  AlgEquiv.ofRingEquiv (f := galTrER g y σ) (fun r => galTrER_fix g y σ r)

theorem galTrE_apply (σ : Gal y) (x : SeparableClosure (X.residueField (g y))) :
    galTrE g y σ x = (sepE g y).symm (σ (sepE g y x)) := rfl

theorem galTrE_left (σ : Gal y) :
    (eE g y).hom.left ≫ galSpec (g y) (galTrE g y σ) ≫ (eE g y).inv.left = galSpec y σ := by
  change Spec.map (CommRingCat.ofHom (sepE g y : SeparableClosure (X.residueField (g y)) →+*
      SeparableClosure (U.residueField y))) ≫ galSpec (g y) (galTrE g y σ) ≫ Spec.map (CommRingCat.ofHom
      ((sepE g y).symm : SeparableClosure (U.residueField y) →+* SeparableClosure (X.residueField (g y)))) =
    galSpec y σ
  rw [galSpec, galSpec, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  change sepE g y ((sepE g y).symm (σ (sepE g y ((sepE g y).symm x)))) = σ x
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

/-! ### `Λ_U ⟶ g^* Λ_X` -/

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N1c =====
section

/-!
# S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)

* `trIso g h Λ F : (g^* F)_ȳ ≅ F_x̄` and `galTrX g h : Gal y → Gal x` for `h : g y = x` (`resTrIsoE`, `galTrE`
  transported along `h`), `galRep_trIso`, `trIso_natural`, `trIso_hom_injective`, `trIso_inv_natural`,
  `trIso_unitRes`, `isoHomInv`, `isoInvHom`;
* **`resHE_kappa`** (NAT): for `g : Spec A' ⟶ Spec A` etale between noetherian integrally closed domains with
  `g η' = η`, `resHE g (κ_A c) = κ_{A'} c'` whenever `trIso (c' (σ|)) = c ((galTrX σ)|)` for all `σ ∈ Gal(η')`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

universe u

section Pt

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {y : U} {x : X} (h : g y = x) (Λ : Type u) [CommRing Λ]

/-- `Gal y → Gal x` for `g y = x`. -/
def galTrX (σ : Gal y) : Gal x := by
  subst h
  exact galTrE g y σ

end Pt

section Kappa

end Kappa

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N3 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map

* `kchar_transport` (field theory): two Kummer characters agree when the two groups act compatibly through
  embeddings `e : L → Ω`, `e' : L' → Ω` and one `σ ∈ Aut Ω`, `e ζ = e' ζ'` is fixed by `σ` and `e (γ^N) = e' (γ'^N)`;
* `val_add_smul`, `kumChi hζ γ c : τ ↦ (kchar γ τ).val • c` (an additive locally constant character when
  `N • c = 0`): `kumChi_mul`, `kumChi_isLocallyConstant`;
* `sepX g h`, `resMapX g h` for `h : g y = x` (`sepE`, `residueFieldMap` transported), `galTrX_apply`,
  `sepX_algebraMap`;
* **`resLE_kappaL_kum`** (NAT for Kummer classes): `resLE g 1 (κ (kumChi ζ γ c)) = κ (kumChi ζ' γ' c)` when
  `sepX (ζ) = ζ'` and `sepX (γ^N) = γ'^N` in `κ(η')^sep`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer

section KumTr

end KumTr

section KumChi

end KumChi

section Sep

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {y : U} {x : X} (h : g y = x)

/-- `κ(x)^sep ≃ κ(y)^sep` for `g y = x` (`sepE` transported along `h`). -/
def sepX : SeparableClosure (X.residueField x) ≃+* SeparableClosure (U.residueField y) := by
  subst h
  exact sepE g y

theorem galTrX_apply (σ : Gal y) (z : SeparableClosure (X.residueField x)) :
    galTrX g h σ z = (sepX g h).symm (σ (sepX g h z)) := by
  subst h
  rfl

theorem sepX_algebraMap (r : X.residueField x) :
    sepX g h (algebraMap _ (SeparableClosure (X.residueField x)) r) =
      algebraMap (U.residueField y) (SeparableClosure (U.residueField y)) (resMapX g h r) := by
  subst h
  exact sepE_algebraMap g y r

end Sep

section KumNat

end KumNat

end RamanujanPetersson.EtCompact.GalTrE

end

end


