-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_021
-- name    : RPLib_FX_EtPBC_021
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:10:52.54845+00:00
-- url     : https://prove2.me/theorems/1576e356-4820-5d6d-9af2-ad88bcd9ee3e
-- title:
--   Proper base change for the projective line, library file 021
-- statement:
--   File 021 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2U`: S4-EtPBC-A, O2 (MV route), U: `Λ[P] ≅ Λ_P`
--   * `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
--   * `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
--   * `S4.Def_RP_EtPBC_A_O2D1`: S4-EtPBC-A, O2 (MV route), M3 step (3): classes of `H²(Spec A, g_* N)` die on a basic open
--   * `S4.Def_RP_EtPBC_A_O2Km2`: S4-EtPBC-A, O2 M6 (O2Km2): splitting `H¹(X, Λ)` along a finite clopen decomposition
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--   * `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
--   * `S4.Def_RP_EtPBC_A_O2N2`: S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)
--   * `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
--   * `S4.Def_RP_EtPBC_A_O2E6b`: S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object
--   * `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
--   * `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
--   * `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--   * `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
--   * `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_013
import Definitions.Def_RPLib_FX_EtPBC_015
import Definitions.Def_RPLib_FX_EtPBC_016
import Definitions.Def_RPLib_FX_EtPBC_017

/-!
# Proper base change for the projective line, library file 021

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2U`: S4-EtPBC-A, O2 (MV route), U: `Λ[P] ≅ Λ_P`
* `S4.Def_RP_EtPBC_A_O2Fl`: S4-EtPBC-A, O2 (MV route), Fl: free sheaves are extensions by zero
* `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
* `S4.Def_RP_EtPBC_A_O2D1`: S4-EtPBC-A, O2 (MV route), M3 step (3): classes of `H²(Spec A, g_* N)` die on a basic open
* `S4.Def_RP_EtPBC_A_O2Km2`: S4-EtPBC-A, O2 M6 (O2Km2): splitting `H¹(X, Λ)` along a finite clopen decomposition
* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
* `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
* `S4.Def_RP_EtPBC_A_O2N2`: S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)
* `S4.Def_RP_EtPBC_A_O2E5`: S4-EtPBC-A, O2 C-plan S4d0: `extFree` is natural in the etale object (degree 1)
* `S4.Def_RP_EtPBC_A_O2E6b`: S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object
* `S4.Def_RP_EtPBC_A_O2Coh`: S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces
* `S4.Def_RP_EtPBC_A_O2T1`: S4-EtPBC-A, O2 S5a: restriction of a free sheaf, graphs and section maps
* `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
* `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
* `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_O2U =====
section

/-!
# S4-EtPBC-A, O2 (MV route), U: `Λ[P] ≅ Λ_P`

* `oneSec`: the section `1` of `Λ_P` over `P`; `freeToUnit : Λ[etId P] ⟶ Λ_P` (`taut ↦ 1`, `freeToUnit_taut`);
* `stalk_freeToUnit`: on stalks the germ of `taut` goes to `oneStalk`; **`isIso_freeToUnit`**, `unitIso`;
* `extUnit F n : H^n(P, F) ≃+ Ext^n(Λ[etId P], F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg
  RamanujanPetersson.EtPBC.FreeStk RamanujanPetersson.EtCompact

universe u

variable (Λ : Type u) [CommRing Λ] (P : Scheme.{u})

variable {Λ P}

/-- **`Λ[P] ⟶ Λ_P` is an isomorphism.** -/
theorem isIso_freeToUnit : IsIso (freeToUnit Λ P) := by
  rw [isIso_iff_stalk]
  intro x
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun v v' h => ?_, fun y => ?_⟩
  · change (((geomPtAt x).stalkF Λ).map (freeToUnit Λ P)).hom v =
      (((geomPtAt x).stalkF Λ).map (freeToUnit Λ P)).hom v' at h
    obtain ⟨c, rfl⟩ := free_top_gen x v
    obtain ⟨c', rfl⟩ := free_top_gen x v'
    have h' := congrArg (constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom h
    rw [stalk_freeToUnit_smul, stalk_freeToUnit_smul] at h'
    rw [h']
  · refine ⟨(constStalkIso Λ (geomPtAt x) (ModuleCat.of Λ Λ)).hom.hom y •
      germ (freeSh Λ (etId P)) x (topPt x) (taut Λ (etId P)), ?_⟩
    change (((geomPtAt x).stalkF Λ).map (freeToUnit Λ P)).hom _ = y
    rw [map_smul, stalk_freeToUnit]
    exact (eq_smul_oneStalk x y).symm

variable (Λ P) in
/-- **`Λ[P] ≅ Λ_P`.** -/
def unitIso : freeSh Λ (etId P) ≅ unitSh Λ P := @asIso _ _ _ _ (freeToUnit Λ P) isIso_freeToUnit

theorem unitIso_hom : (unitIso Λ P).hom = freeToUnit Λ P := rfl

end RamanujanPetersson.EtPBC.EtMV

end

end

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

end Free

section GenFl

universe w₁ v₁ u₁ v₂ u₂

end GenFl

section Obj

variable {P : Scheme.{u}}

variable (Λ) in
/-- **`Λ[W] ≅ e_! Λ_W`** for `e = W.hom`. -/
def freeLshIso (W : P.Etale) : freeSh Λ W ≅ (lsh W.hom Λ).obj (unitSh Λ W.left) :=
  (freeIsoOfIso Λ (etCompTop W)).symm ≪≫ lshFreeIso Λ W.hom (etId W.left) ≪≫
    (lsh W.hom Λ).mapIso (unitIso Λ W.left)

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fl2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`

* `extAdjMap_mk₀_comp`: the adjunction map on `Ext` is natural in the source;
* `lshFreeHom_natural`, `lshFreeInv_natural`: `Λ[e ∘ V] ≅ e_! Λ[V]` is natural in `V`;
* `toW W V : e ∘ V ⟶ W` (`e = W.hom`, `V : W.left.Etale`), `extFreeV : Ext_P(Λ[e ∘ V], F) ≃ Ext_W(Λ[V], F|_W)`;
* **`extFreeV_restrict`**: restricting `β ∈ Ext_P(Λ[W], F)` along `toW W V` is restricting `extFree β ∈ H(W, F|_W)`
  to `V`; **`restrict_eq_zero`**: if `extFree β` dies on `V`, then `β` dies on `e ∘ V`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe w v v' u₁ u₂ u

section Adj

end Adj

variable {Λ : Type u} [CommRing Λ]

section Nat

end Nat

section Obj

variable {P : Scheme.{u}}

theorem freeLshIso_inv (W : P.Etale) :
    (freeLshIso Λ W).inv = ((lsh W.hom Λ).map (unitIso Λ W.left).inv ≫ lshFreeInv Λ W.hom (etId W.left)) ≫
      freeMap Λ (etCompTop W).hom :=
  rfl

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2D1 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 step (3): classes of `H²(Spec A, g_* N)` die on a basic open

`Y = Spec A` (`A` a noetherian integrally closed domain of dimension `≤ 1`), `g = gen A` its generic point.
* `bOpen f = D(f)`, `rD Λ f : Λ[D(f)] ⟶ Λ_Y` (restriction to `D(f)`);
* `exists_bOpen_zero`: a global section of a sheaf with zero stalks at non-closed points and at the generic point
  vanishes on some `D(f)`, `f ≠ 0` (finite support, `f` = product of elements of the supporting primes);
* **`push_two_dies`**: under `H²(η, -) = 0` and `R²g_* = 0`, every `β ∈ H²(Y, g_* N)` dies on some `D(f)`, `f ≠ 0`
  (`β` comes from a global section of `R¹g_* N` along `presB`, `presA`; that section vanishes on some `D(f)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac

variable {A : Type} [CommRing A] [IsDomain A] {Λ : Type} [CommRing Λ]

variable (Λ) in
/-- `Λ[D(f)] ⟶ Λ_{Spec A}`: precomposition with it is restriction to `D(f)`. -/
def rD (f : A) : freeSh Λ (opEt (bOpen f)) ⟶ unitSh Λ (Spec (CommRingCat.of A)) :=
  freeMap Λ (toTop (opEt (bOpen f))) ≫ (unitIso Λ (Spec (CommRingCat.of A))).hom

variable [IsNoetherianRing A] [IsIntegrallyClosed A] [Ring.KrullDimLE 1 A]

/-- **Step (3)**: every class of `H²(Spec A, g_* N)` dies on some `D(f)`, `f ≠ 0`. -/
theorem push_two_dies
    (hη : ∀ (M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))) (e : H Λ M 2), e = 0)
    (hR : ∀ M : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))),
      IsZero (R1 (gen A) Λ (Qt Λ M)))
    (N : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))))
    (β : H Λ ((push (gen A) Λ).obj N) 2) :
    ∃ f : A, f ≠ 0 ∧ (Ext.mk₀ (rD Λ f)).comp β (zero_add 2) = 0 := by
  have := LerayG.pzm (pullAdj (gen A) Λ)
  have : Injective (LerayG.presA (push (gen A) Λ) N).X₂ :=
    LerayG.injective_push (pullAdj (gen A) Λ) (Injective.under N)
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ (LerayG.presA_shortExact (pullAdj (gen A) Λ) N) β
    (Ext.eq_zero_of_injective _) (show 1 + 1 = 2 from rfl)
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ (LerayG.presB_shortExact (push (gen A) Λ) N) x₃
    (H_push_Qt_eq_zero hη hR 0 N _) (show 0 + 1 = 1 from rfl)
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  obtain ⟨f, hf0, hf⟩ := exists_bOpen_zero (R1Gen.hF_R1 N) (R1Gen.isZero_R1_gen N)
    (freeEquiv Λ (etId _) _ ((unitIso Λ (Spec (CommRingCat.of A))).hom ≫ s))
  refine ⟨f, hf0, ?_⟩
  have hz : rD Λ f ≫ s = 0 := by
    apply (freeEquiv Λ (opEt (bOpen f)) _).injective
    rw [map_zero, rD, Category.assoc, freeEquiv_freeMap]
    exact hf
  have e1 : (Ext.mk₀ (rD Λ f)).comp ((Ext.mk₀ s).comp (LerayG.presB_shortExact (push (gen A) Λ) N).extClass
      (zero_add 1)) (zero_add 1) = 0 := by
    rw [Ext.mk₀_comp_mk₀_assoc, hz, Ext.mk₀_zero, Ext.zero_comp]
  rw [← Ext.comp_assoc (Ext.mk₀ (rD Λ f)) _ _ (zero_add 1) (show 1 + 1 = 2 from rfl) (by omega), e1,
    Ext.zero_comp]

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km2): splitting `H¹(X, Λ)` along a finite clopen decomposition

`S : ι → X.Etale` a finite family with `∐ S k ⟶ X` an isomorphism.
* `copIso : cop S ≅ etId X` (when `(cop S).hom` is an isomorphism);
* `toId`, `copι_copIso`; `splitPr k : Λ_X ⟶ Λ[S k]`, `splitIn k : Λ[S k] ⟶ Λ_X`, `sum_split : Σ_k pr_k ≫ in_k = 𝟙`;
* **`h1_split`**: every `c ∈ H¹(X, Λ)` is `Σ_k pr_k^* ((in_k)^* c)` with `(in_k)^* c ∈ Ext¹(Λ[S k], Λ_X)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV

universe u

section Split

variable {X : Scheme.{u}} {ι : Type u} (S : ι → X.Etale) [IsIso (cop S).hom]

variable (Λ : Type u) [CommRing Λ] [Fintype ι] [DecidableEq ι]

/-- The projection `Λ_X ⟶ Λ[S k]`. -/
def splitPr (k : ι) : unitSh Λ X ⟶ freeSh Λ (S k) :=
  (unitIso Λ X).inv ≫ freeMap Λ (copIso S).inv ≫ copPr Λ S k

/-- The inclusion `Λ[S k] ⟶ Λ_X`. -/
def splitIn (k : ι) : freeSh Λ (S k) ⟶ unitSh Λ X :=
  freeMap Λ (toId (S k)) ≫ (unitIso Λ X).hom

end Split

end RamanujanPetersson.EtPBC.EtKum

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

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTr
  RamanujanPetersson.EtCompact.GGerm RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.GenAlg

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) (y : U)

variable [Etale g]

variable (Λ : Type u) [CommRing Λ]

/-! ### `Λ_U ⟶ g^* Λ_X` -/

/-- `Λ_U ⟶ g^* Λ_X`, `1 ↦ 1`. -/
def unitRes : unitSh Λ U ⟶ (res g Λ).obj (unitSh Λ X) :=
  (unitIso Λ U).inv ≫ (freeEquiv Λ (etId U) ((res g Λ).obj (unitSh Λ X))).symm (oneRes g Λ)

theorem unitIso_inv_oneStalk (x : U) :
    (((geomPtAt x).stalkF Λ).map (unitIso Λ U).inv).hom (oneStalk Λ x) =
      germ (freeSh Λ (etId U)) x (topPt x) (taut Λ (etId U)) := by
  rw [← stalk_freeToUnit (Λ := Λ) (P := U) x, ← unitIso_hom]
  exact congrArg (fun φ => ModuleCat.Hom.hom φ (germ (freeSh Λ (etId U)) x (topPt x) (taut Λ (etId U))))
    ((((geomPtAt x).stalkF Λ).map_comp (unitIso Λ U).hom (unitIso Λ U).inv).symm.trans
      ((congrArg (((geomPtAt x).stalkF Λ).map) (unitIso Λ U).hom_inv_id).trans
        (((geomPtAt x).stalkF Λ).map_id _)))

/-- **`1 ↦ 1`**: `resTrIsoE (unitRes_x̄ 1) = 1`. -/
theorem resTrIsoE_unitRes (x : U) :
    (resTrIsoE g x Λ (unitSh Λ X)).hom.hom ((((geomPtAt x).stalkF Λ).map (unitRes g Λ)).hom (oneStalk Λ x)) =
      oneStalk Λ (g x) := by
  have h1 : (((geomPtAt x).stalkF Λ).map (unitRes g Λ)).hom (oneStalk Λ x) =
      germ ((res g Λ).obj (unitSh Λ X)) x (topPt x) (oneRes g Λ) := by
    rw [unitRes, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, unitIso_inv_oneStalk, germ_natural,
      freeEquiv_symm_taut]
  rw [h1, ← gg_eq_germ, oneRes, resTrIsoE_gg, gg_eq_germ, oneStalk_germ]

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

theorem trIso_unitRes :
    (trIso g h Λ (unitSh Λ X)).hom.hom ((((geomPtAt y).stalkF Λ).map (unitRes g Λ)).hom (oneStalk Λ y)) =
      oneStalk Λ x := by
  subst h
  exact resTrIsoE_unitRes g Λ y

end Pt

section Kappa

end Kappa

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N2 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2: constant coefficients (`κ` of characters and their restriction)

* `unitCoc χ : τ ↦ χ τ • 1` (a cocycle for the trivial action on `(Λ_X)_η̄` when `χ` is additive),
  `fibRep_unitSh'`, `unitCoc_isCocycle`, `unitCoc_isLocallyConstant`;
* `kappaL A K Λ hχ hl : H¹(Spec A, Λ)`, the class of an additive locally constant `χ : π₁(A) → Λ`;
* `resLE g n : H^n(X, Λ) → H^n(U, Λ)` for an etale `g : U ⟶ X` (`resHE` and `unitResIso`);
* **`resLE_kappaL`** (NAT for constant coefficients): for `g : Spec A' ⟶ Spec A` etale with `g η' = η`,
  `resLE g 1 (κ χ) = κ χ'` whenever `χ' (σ|) = χ ((galTrX σ)|)` for all `σ ∈ Gal(η')`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec

section Unit

end Unit

section ResL

universe u

end ResL

section NatL

variable {A K A' K' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]
  [CommRing A'] [IsDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K'] [IsIntegrallyClosed A']
  [IsNoetherianRing A'] {Λ : Type} [CommRing Λ]
  (g : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A)) [Etale g] (hg : g (genPt A') = genPt A)

omit [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [IsNoetherianRing A'] in
/-- The Galois action fixes `g^*(1) ∈ (g^* Λ_X)_η̄'`. -/
theorem fibRep_unitRes (τ : Pi1 A' K') :
    EssSurj.fibRep A' K' ((res g Λ).obj (unitSh Λ _)) (PushBC.isLisse_res g isLisse_unitSh) τ
      (gs A' (unitRes g Λ) (oneStalk Λ (genPt A'))) = gs A' (unitRes g Λ) (oneStalk Λ (genPt A')) := by
  obtain ⟨σ, rfl⟩ := genToPi1_surjective A' K' τ
  rw [EssSurj.fibRep_genToPi1]
  have h := LinearMap.congr_fun (galRep_natural Λ (unitRes g Λ) (genPt A') σ) (oneStalk Λ (genPt A'))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, galRep_unitSh, LinearMap.id_apply] at h
  exact h.symm

end NatL

end RamanujanPetersson.EtCompact.GalTrE

end

end

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

variable (Λ) in
/-- The diagonal section `Λ_W ⟶ Λ[W]|_W` (adjoint to `freeLshIso.inv`). -/
def diagSec (W : P.Etale) : unitSh Λ W.left ⟶ (res W.hom Λ).obj (freeSh Λ W) :=
  (lshAdj W.hom Λ).homEquiv _ _ (freeLshIso Λ W).inv

theorem diagSec_sec (W : P.Etale) :
    freeEquiv Λ (etId W.left) _ ((unitIso Λ W.left).hom ≫ diagSec Λ W) =
      ((freeSh Λ W).obj.map (etCompTop W).hom.op).hom (taut Λ W) := by
  have h1 : (unitIso Λ W.left).hom ≫ diagSec Λ W =
      (freeEquiv Λ (etId W.left) _).symm (resTaut Λ W.hom (etId W.left)) ≫
        (res W.hom Λ).map (freeMap Λ (etCompTop W).hom) := by
    rw [diagSec, freeLshIso_inv, Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_unit, lshFreeInv_adj]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [h1, freeEquiv_comp, AddEquiv.apply_symm_apply]
  exact freeMap_taut (etCompTop W).hom

end Nat

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E6b =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d1 (part 2): `extFreeU` is natural in the etale object

* `resHE_comp_mk₀`, `freeEquiv_unitRes`, `unitRes_one`;
* `unitRes_comp`: `1 ↦ 1` along `m.left`, then along `W.hom`, is `1 ↦ 1` along `W'.hom`; `resCompIso_unit`;
* **`extFreeU_natural`**: `extFreeU W' (ξ ∘ Λ[m]) = resLE m.left (extFreeU W ξ)` in degree `1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

theorem freeEquiv_unitRes {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] :
    freeEquiv Λ (etId U) _ ((unitIso Λ U).hom ≫ unitRes g Λ) = oneRes g Λ := by
  rw [unitRes, Iso.hom_inv_id_assoc, AddEquiv.apply_symm_apply]

theorem unitRes_one {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] :
    ((unitRes g Λ).hom.app (op (etId U))).hom (oneSec Λ U) = oneRes g Λ := by
  have h := freeEquiv_comp Λ (etId U) (unitIso Λ U).hom (unitRes g Λ)
  rw [freeEquiv_unitRes, unitIso_hom, freeToUnit, AddEquiv.apply_symm_apply] at h
  exact h.symm

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Coh =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Coh): restriction to an etale `W` as `Λ[W ⟶ X]^*`, and restriction to pieces

* **`unitRes_eq_adj W`**: `Λ_W ⟶ W^* Λ_X` (`1 ↦ 1`) is the adjunction unit followed by
  `W^*(Λ[W] ⟶ Λ[X] ≅ Λ_X)`;
* **`resLE_eq_extFreeU W c`**: `resLE W.hom 1 c = extFreeU W 1 (Λ[W ⟶ X]^* c)`;
* `extFreeU_splitIn`, **`h1_eq_zero_of_pieces`** (a class vanishing on every piece of a clopen decomposition is `0`),
  `splitIn_splitPr`, `resLE_splitPr(_self/_ne)`, **`resLE_kapS_self`**, **`resLE_kapS_ne`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtCompact.GalTrE

universe u

section Coh

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}}

theorem freeLshIso_inv_eq (W : X.Etale) :
    (freeLshIso Λ W).inv = ((lsh W.hom Λ).map (unitIso Λ W.left).inv ≫ lshFreeInv Λ W.hom (etId W.left)) ≫
      freeMap Λ (etCompTop W).hom :=
  rfl

theorem lsh_unit_freeLshIso (W : X.Etale) :
    (lsh W.hom Λ).map (unitIso Λ W.left).hom ≫ (freeLshIso Λ W).inv ≫ freeMap Λ (toTop W) ≫ (unitIso Λ X).hom =
      lshFreeInv Λ W.hom (etId W.left) ≫ freeMap Λ (toTop ((etComp W.hom).obj (etId W.left))) ≫
        (unitIso Λ X).hom := by
  rw [freeLshIso_inv_eq]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Category.assoc (freeMap Λ (etCompTop W).hom), ← freeMap_comp,
    toTop_ext ((etCompTop W).hom ≫ toTop W) (toTop ((etComp W.hom).obj (etId W.left)))]

end Coh

section Pieces

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {ι : Type u} (S : ι → X.Etale) [IsIso (cop S).hom]
  [Fintype ι] [DecidableEq ι]

variable (Λ) in
theorem splitIn_splitPr (k z : ι) : splitIn S Λ k ≫ splitPr S Λ z = freeMap Λ (copι S k) ≫ copPr Λ S z := by
  have h1 : copι S k = toId (S k) ≫ (copIso S).inv := by
    rw [Iso.eq_comp_inv]
    exact copι_copIso S k
  simp only [splitIn, splitPr, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (freeMap Λ (toId (S k))), ← freeMap_comp, ← h1]

end Pieces

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

/-- **The section map** `Λ_W ⟶ Λ[T]|_W` of `m : W ⟶ T`. -/
def secMap (m : W ⟶ T) : unitSh Λ W.left ⟶ (res W.hom Λ).obj (freeSh Λ T) :=
  diagSec Λ W ≫ (res W.hom Λ).map (freeMap Λ m)

theorem secMap_comp {T' : P.Etale} (m : W ⟶ T) (s : T ⟶ T') :
    secMap Λ m ≫ (res W.hom Λ).map (freeMap Λ s) = secMap Λ (m ≫ s) := by
  rw [secMap, secMap, Category.assoc, ← Functor.map_comp, ← freeMap_comp]

end Graph

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

variable {Λ : Type u} [CommRing Λ]

theorem app_oneSec {X : Scheme.{u}} {F : EtSh Λ X} (φ : unitSh Λ X ⟶ F) :
    (φ.hom.app (op (etId X))).hom (oneSec Λ X) = freeEquiv Λ (etId X) F ((unitIso Λ X).hom ≫ φ) := by
  rw [freeEquiv_comp, unitIso_hom, freeToUnit, AddEquiv.apply_symm_apply]

theorem unit_hom_ext {X : Scheme.{u}} {F : EtSh Λ X} {φ ψ : unitSh Λ X ⟶ F}
    (h : (φ.hom.app (op (etId X))).hom (oneSec Λ X) = (ψ.hom.app (op (etId X))).hom (oneSec Λ X)) : φ = ψ := by
  rw [← cancel_epi (unitIso Λ X).hom]
  apply (freeEquiv Λ (etId X) F).injective
  rw [← app_oneSec, ← app_oneSec]
  exact h

variable (Λ) in
/-- `Λ_X ≅ g^*Λ_Y` (through the free sheaves). -/
def pullUnit {X Y : Scheme.{u}} (g : X ⟶ Y) : unitSh Λ X ≅ (pull g Λ).obj (unitSh Λ Y) :=
  (unitIso Λ X).symm ≪≫ freeIsoOfIso Λ (etIdPull g) ≪≫ pullFreeIso Λ g (etId Y) ≪≫
    (pull g Λ).mapIso (unitIso Λ Y)

theorem pullUnit_one {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (((pullUnit Λ g).hom.hom.app (op (etId X))).hom (oneSec Λ X)) =
      ((((pull g Λ).obj (unitSh Λ Y)).obj.map (etIdPull g).hom.op).hom (pbSec g (oneSec Λ Y))) := by
  have e1 : (unitIso Λ X).hom ≫ (pullUnit Λ g).hom =
      freeMap Λ (etIdPull g).hom ≫ pullFreeHom Λ g (etId Y) ≫ (pull g Λ).map (unitIso Λ Y).hom := by
    rw [← freeIsoOfIso_hom]
    exact (unitIso Λ X).hom_inv_id_assoc _
  have e2 : ((((pull g Λ).map (unitIso Λ Y).hom).hom.app (op ((etPull g).obj (etId Y)))).hom
      (freeEquiv Λ _ _ (pullFreeHom Λ g (etId Y)))) = pbSec g (oneSec Λ Y) := by
    rw [pullFreeHom, AddEquiv.apply_symm_apply]
    refine (pbSec_natural g (unitIso Λ Y).hom (taut Λ (etId Y))).symm.trans ?_
    rw [unitIso_hom, freeToUnit_taut]
  rw [app_oneSec, e1, freeEquiv_freeMap, freeEquiv_comp]
  exact congrArg (fun z => ((((pull g Λ).obj (unitSh Λ Y)).obj.map (etIdPull g).hom.op).hom z)) e2

end TB2

section TB2o

/-! Op-form section calculus: restriction maps are op-morphisms `a : op T ⟶ op Z` that are passed through
unchanged, so consecutive steps meet in syntactically equal terms (this keeps kernel checks cheap). -/

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

/-- `unit_hom_ext` for `φ` typed in the world `(𝟭 Scheme).obj A`, against a composite `a1 ≫ a2` (keeps the kernel
check of the KEY identity free of top-level world mismatches). -/
theorem unit_hom_extW2 {A : Scheme.{u}} {F1 F : EtSh Λ A}
    (φ : @Quiver.Hom (EtSh Λ ((𝟭 Scheme).obj A)) _ (unitSh Λ A) F) (a1 : unitSh Λ A ⟶ F1) (a2 : F1 ⟶ F)
    (h : (φ.hom.app (@op (Scheme.Etale ((𝟭 Scheme).obj A)) (etId A))).hom (oneSec Λ A) =
      ((a1 ≫ a2).hom.app (op (etId A))).hom (oneSec Λ A)) : φ = a1 ≫ a2 :=
  unit_hom_ext h

end TB2b

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB3 =====
section

/-!
# S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`

* `pullH Λ g n κ := u ∘ g^*κ ∘ u⁻¹ ∈ H^n(X, Λ)` for `κ ∈ H^n(Y, Λ)` and any `g : X ⟶ Y` (`u := pullUnit Λ g`);
* `secMap_id`, `diagSec_pull` (the KEY identity at `m = 𝟙`);
* **`thetaM_pull`**: `Λ[f⁻¹W] ⟶ f^*Λ[W]` followed by `f^*(thetaM m 1 κ)` equals
  `thetaM (f⁻¹ m) 1 (pullH f_W 1 κ)` followed by `Λ[f⁻¹T] ⟶ f^*Λ[T]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenAlg

universe u

section TB3

variable {Λ : Type u} [CommRing Λ]

variable (Λ) in
/-- Pullback of a class `κ ∈ H^n(Y, Λ)` along any `g : X ⟶ Y`. -/
def pullH {X Y : Scheme.{u}} (g : X ⟶ Y) (n : ℕ) (κ : H Λ (unitSh Λ Y) n) : H Λ (unitSh Λ X) n :=
  (Ext.mk₀ (pullUnit Λ g).hom).comp ((κ.mapExactFunctor (pull g Λ)).comp (Ext.mk₀ (pullUnit Λ g).inv)
    (add_zero n)) (zero_add n)

theorem secMap_id {P : Scheme.{u}} (W : P.Etale) : secMap Λ (𝟙 W) = diagSec Λ W := by
  rw [secMap, freeMap_id, CategoryTheory.Functor.map_id, Category.comp_id]

section GenPL

universe w' v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

end GenPL

end TB3

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L2x =====
section

/-!
# S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps

* `mapExact_iso τ ξ`: isomorphic exact functors act alike on `Ext¹` (`τ : Φ ≅ Φ'`);
* `conjE x a b := mk₀ a ∘ x ∘ mk₀ b`, `conjE_conjE`, `mapExact_conjE`;
* `pullUnit_comp`: `Λ_X ≅ (f ≫ g)^*Λ_Z ≅ f^*g^*Λ_Z` is `Λ_X ≅ f^*Λ_Y ≅ f^*g^*Λ_Z`;
* **`pullH_comp`**: `pullH (f ≫ g) 1 κ = pullH f 1 (pullH g 1 κ)`;
* `pullUnit_res`: for etale `g`, `Λ_U ≅ g^*Λ_X ≅ res g Λ_X` is `unitRes g`;
* **`resLE_eq_pullH`**: for etale `g`, `resLE g 1 e = pullH g 1 e`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE

section IsoGen

universe w v₁ u₁ v₂ u₂

end IsoGen

universe u

section PullX

variable {Λ : Type u} [CommRing Λ]

theorem pullUnit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullUnit Λ (f ≫ g)).hom ≫ (pullCompIso Λ f g).hom.app (unitSh Λ Z) =
      (pullUnit Λ f).hom ≫ (pull f Λ).map (pullUnit Λ g).hom := by
  have hT : ∀ a b : etId X ⟶ (etPull f).obj ((etPull g).obj (etId Z)), a = b := fun a b =>
    (cancel_mono ((etPull f).mapIso (etIdPull g).symm ≪≫ (etIdPull f).symm).hom).1 (toTop_ext _ _)
  apply unit_hom_ext
  have hL : (((pullUnit Λ (f ≫ g)).hom ≫ (pullCompIso Λ f g).hom.app (unitSh Λ Z)).hom.app
      (op (etId X))).hom (oneSec Λ X) =
      ((((pull f Λ).obj ((pull g Λ).obj (unitSh Λ Z))).obj.map
        ((etIdPull (f ≫ g)).hom ≫ (etPullCompIso f g).hom.app (etId Z)).op).hom
        (pbSec f (pbSec g (oneSec Λ Z)))) := by
    refine app2 _ _ (pullUnit_one (f ≫ g)) ?_
    refine (sec_nat ((pullCompIso Λ f g).hom.app (unitSh Λ Z)) (etIdPull (f ≫ g)).hom _).trans ?_
    refine (congrArg _ (pbSec_comp f g (oneSec Λ Z))).trans ?_
    exact sec_map_comp _ _ _ _
  have hR : (((pullUnit Λ f).hom ≫ (pull f Λ).map (pullUnit Λ g).hom).hom.app (op (etId X))).hom
      (oneSec Λ X) =
      ((((pull f Λ).obj ((pull g Λ).obj (unitSh Λ Z))).obj.map
        ((etIdPull f).hom ≫ (etPull f).map (etIdPull g).hom).op).hom (pbSec f (pbSec g (oneSec Λ Z)))) := by
    refine app2 _ _ (pullUnit_one f) ?_
    refine (sec_nat ((pull f Λ).map (pullUnit Λ g).hom) (etIdPull f).hom _).trans ?_
    refine (congrArg _ (pbSec_natural f (pullUnit Λ g).hom (oneSec Λ Y)).symm).trans ?_
    refine (congrArg (fun t => (((((pull f Λ).obj ((pull g Λ).obj (unitSh Λ Z))).obj.map
      (etIdPull f).hom.op).hom) (pbSec f t))) (pullUnit_one g)).trans ?_
    refine (congrArg _ (pbSec_restrict f (etIdPull g).hom (pbSec g (oneSec Λ Z)))).trans ?_
    exact sec_map_comp _ _ _ _
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [hT ((etIdPull (f ≫ g)).hom ≫ (etPullCompIso f g).hom.app (etId Z))
    ((etIdPull f).hom ≫ (etPull f).map (etIdPull g).hom)]

theorem pullUnit_comp_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pullCompIso Λ f g).inv.app (unitSh Λ Z) ≫ (pullUnit Λ (f ≫ g)).inv =
      (pull f Λ).map (pullUnit Λ g).inv ≫ (pullUnit Λ f).inv := by
  rw [← cancel_epi ((pullUnit Λ (f ≫ g)).hom ≫ (pullCompIso Λ f g).hom.app (unitSh Λ Z))]
  conv_rhs => rw [pullUnit_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id, Iso.map_hom_inv_id_assoc]

theorem pullUnit_res {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] :
    (pullUnit Λ g).hom ≫ (pullIsoRes g Λ).hom.app (unitSh Λ X) = unitRes g Λ := by
  apply unit_hom_ext
  refine Eq.trans ?_ (unitRes_one g).symm
  refine app2 _ _ (pullUnit_one g) ?_
  refine (sec_nat ((pullIsoRes g Λ).hom.app (unitSh Λ X)) (etIdPull g).hom _).trans ?_
  refine (congrArg _ (pbSec_res g (oneSec Λ X))).trans ?_
  refine (sec_map_comp (unitSh Λ X) _ ((etComp g).map (etIdPull g).hom) (oneSec Λ X)).trans ?_
  rw [toTop_ext ((etComp g).map (etIdPull g).hom ≫ (etCompAdj g).counit.app (etId X))
    (toTop ((etComp g).obj (etId U)))]
  rfl

end PullX

end RamanujanPetersson.EtPBC.EtMV

end

end


