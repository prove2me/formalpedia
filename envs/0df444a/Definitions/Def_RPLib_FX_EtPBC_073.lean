-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_073
-- name    : RPLib_FX_EtPBC_073
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:38:11.669866+00:00
-- url     : https://prove2.me/theorems/19392374-7e11-5c5d-97fd-44457d020aee
-- title:
--   Proper base change for the projective line, library file 073
-- statement:
--   File 073 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_FBInj`: S4-EtPBC-A, M2 F3: base change on germs of a constant sheaf (degree `0`)
--   * `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
--   * `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
--   * `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
--   * `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
--   * `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2E3`: S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes
--   * `S4.Def_RP_EtPBC_A_O2Gl2i`: S4-EtPBC-A, O2 GLOB (O2Gl2i): stages S2-S3 assembled (pure algebra)
--   * `S4.Def_RP_EtPBC_A_O2T7`: S4-EtPBC-A, O2 S5g: presentations with sections through every fibre point, disjoint graphs, affine
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_062
import Definitions.Def_RPLib_FX_EtPBC_064

/-!
# Proper base change for the projective line, library file 073

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_FBInj`: S4-EtPBC-A, M2 F3: base change on germs of a constant sheaf (degree `0`)
* `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
* `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
* `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
* `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
* `S4.Def_RP_EtPBC_A_O2R4`: S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPBC_A_O2E3`: S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes
* `S4.Def_RP_EtPBC_A_O2Gl2i`: S4-EtPBC-A, O2 GLOB (O2Gl2i): stages S2-S3 assembled (pure algebra)
* `S4.Def_RP_EtPBC_A_O2T7`: S4-EtPBC-A, O2 S5g: presentations with sections through every fibre point, disjoint graphs, affine
-/

set_option autoImplicit false

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

/-- **Base change kills a degree-`0` class whose section vanishes along the fibre.** -/
theorem bc_zero_of_cval (j : Nbhd s) (α : Ext.{u} ((nbhdSys Λ g s).obj j) (constSh Λ P M) 0)
    (h : ∀ x : fib g s, cval (sec0 Λ g s j (constSh Λ P M) α) (fibToNbhd g s j x) = 0) :
    Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j (constSh Λ P M) 0 α = 0 := by
  rw [bc_zero_eq, Ext.mk₀_eq_zero_iff]
  refine hom_ext_stalk Λ fun y => ?_
  refine stalk_unitSh_hom_ext Λ y ?_
  rw [stalk_sc _ y (etId (fib g s)) (geomPtAt y).top, sc_bcUnit_comp, Functor.map_zero]
  have hw := ConcreteCategory.congr_hom ((geomPtAt y).point.toPresheafFiber_w (nbhdSec g s j) (geomPtAt y).top
    ((pull (fibι g s) Λ).obj (constSh Λ P M)).obj)
    ((((pullAdj (fibι g s) Λ).unit.app (constSh Λ P M)).hom.app (op ((etPull g).obj j.1))).hom
      (sec0 Λ g s j (constSh Λ P M) α))
  have he := ConcreteCategory.congr_hom (germ_unit_pushFib Λ (fibι g s) (geomPtAt y) (constSh Λ P M)
    ((etPull g).obj j.1) (fibB g s j y)) (sec0 Λ g s j (constSh Λ P M) α)
  have h0 := const_comap_germ (fibι g s) (geomPtAt y) ((etPull g).obj j.1) (fibB g s j y)
    (sec0 Λ g s j (constSh Λ P M) α) (by rw [cpt_fibB]; exact h y)
  have hz : ((geomPtAt y).point.toPresheafFiber (etId (fib g s)) (geomPtAt y).top
      ((pull (fibι g s) Λ).obj (constSh Λ P M)).obj).hom
      ((((pull (fibι g s) Λ).obj (constSh Λ P M)).obj.map (nbhdSec g s j).op).hom
        ((((pullAdj (fibι g s) Λ).unit.app (constSh Λ P M)).hom.app (op ((etPull g).obj j.1))).hom
          (sec0 Λ g s j (constSh Λ P M) α))) = 0 := by
    refine hw.trans (he.symm.trans ?_)
    change ((comapPt (fibι g s) (geomPtAt y)).sheafFiber.map ((pullAdj (fibι g s) Λ).unit.app (constSh Λ P M)) ≫
      pushFib Λ (fibι g s) (geomPtAt y) ((pull (fibι g s) Λ).obj (constSh Λ P M))).hom
      (((comapPt (fibι g s) (geomPtAt y)).toPresheafFiber ((etPull g).obj j.1) (fibB g s j y)
        (constSh Λ P M).obj).hom (sec0 Λ g s j (constSh Λ P M) α)) = 0
    rw [h0]
    exact LinearMap.map_zero _
  exact hz.trans rfl

end BC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_EY =====
section

/-!
# S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`

* `residueFieldMap_finite`: residue field extensions of etale morphisms are finite;
* `f0 T ξ : Spec κ(ξ) ⟶ P`, `Yn`, `πn`, `g0` (relative normalization), **`isFinite_πn`** (Nagata), `yg` the generic
  point of `Y` (`closure {yg} = univ`);
* `exists_iota`: `fl x t` factors through `Spec κ(fpt x t)`;
* `Xp ξ W := pullback (f0 T ξ) W.hom`, its sections `sx ξ W u` (`u : T ⟶ W`), clopen ranges, **`sx_cover`** (every
  point lies on a section `sx (τ b)`) and **`sx_disj`** (the sections `sx (τ b)` have distinct points).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech

universe u

variable {P : Scheme.{u}} (T : P.Etale) (ξ : T.left)

/-- **`π : Y ⟶ P` is finite** (Nagata, `P` locally of finite type over a perfect field). -/
theorem isFinite_πn (K : Type u) [Field K] (p : ℕ) [ExpChar K p] [PerfectRing K p]
    (h : P ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] : IsFinite (πn T ξ) := by
  have : Etale T.hom := T.prop
  exact Nagata.isFinite_fromNormalization (T.hom ξ) ξ (T.hom.residueFieldMap ξ) K p h
    (residueFieldMap_finite T.hom ξ)

section Sec

end Sec

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_O2S1 =====
section

/-!
# S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes

* `opEt_ext` (maps into `opEt U` are unique), `toOpEt`, `opEtMap`, `freeMap_id`;
* `mvC_shortExact'`: the MV criterion with "surjective onto the fibre of `Z`" instead of "nonempty";
* `locC`, **`locC_shortExact`**: the one-point MV complex `Λ[D ×_P Uo] ⟶ Λ[D] ⊞ Λ[P ∖ z] ⟶ Λ[P]` for an etale `D`
  with one geometric point over `z` and all other points over `Uo` (`Uo ⊆ P ∖ z`);
* `IsLoc Λ F z β` (one-point MV class `ε_loc ∘ κ`), `locSpan Λ F` (the subgroup they generate);
* `exists_good_one`, **`split_step`** (a class dying on `U` differs from a one-point class at `z ∉ U` by a class
  dying on `U ∪ {z}`), **`mem_locSpan_of_dies`** (induction on `#(P ∖ U)`), **`mem_locSpan_P1`**:
  `H²(P¹, F) = locSpan` (with `claimD`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

/-- **MV criterion**, surjectivity form (allows points where every fibre is empty). -/
theorem mvC_shortExact' {W' W U Z : P.Etale} (p₁ : W' ⟶ W) (p₂ : W' ⟶ U) (w : W ⟶ Z) (v : U ⟶ Z)
    (hsq : p₁ ≫ w = p₂ ≫ v) (hZ : ∀ x : P, Subsingleton ((geomPtAt x).point.fiber.obj Z))
    (hgood : ∀ x : P,
      (Subsingleton ((geomPtAt x).point.fiber.obj W) ∧ Function.Bijective ((geomPtAt x).point.fiber.map p₂)) ∨
        (Subsingleton ((geomPtAt x).point.fiber.obj U) ∧ Function.Bijective ((geomPtAt x).point.fiber.map p₁)))
    (hsurj : ∀ x : P, Function.Surjective ((geomPtAt x).point.fiber.map w) ∨
        Function.Surjective ((geomPtAt x).point.fiber.map v)) :
    (mvC Λ p₁ p₂ w v hsq).ShortExact := by
  have hmono : Mono (mvC Λ p₁ p₂ w v hsq).f := by
    rw [mono_iff_stalk]
    intro x
    rw [ModuleCat.mono_iff_injective]
    refine mvC_f_injective p₁ p₂ x ?_
    rcases hgood x with ⟨_, hb⟩ | ⟨_, ha⟩
    · exact Or.inr hb.1
    · exact Or.inl ha.1
  have hepi : Epi (mvC Λ p₁ p₂ w v hsq).g := by
    rw [epi_iff_stalk]
    intro x
    rw [ModuleCat.epi_iff_surjective]
    exact mvC_g_surjective w v x (hsurj x)
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [exact_iff_stalk]
  intro x
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  have := hZ x
  exact mvC_exact_stalk p₁ p₂ w v x (hgood x) y hy

/-- **The one-point MV complex is short exact.** -/
theorem locC_shortExact (D : P.Etale) {Uo Uz : P.Opens} (h : Uo ≤ Uz) (z : P) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z)
    (hD : Subsingleton ((geomPtAt z).point.fiber.obj D)) (hDn : Nonempty ((geomPtAt z).point.fiber.obj D))
    (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = z) :
    (locC Λ D h).ShortExact := by
  refine mvC_shortExact' _ _ _ _ _ (fun x => inferInstance) (fun x => ?_) (fun x => ?_)
  · by_cases hxz : x = z
    · rw [hxz]
      refine Or.inl ⟨hD, ?_⟩
      have : IsEmpty ((geomPtAt z).point.fiber.obj (opEt Uz)) :=
        ⟨fun b => (hz z).1 (mem_of_fib_opEt Uz z b) rfl⟩
      have : IsEmpty ((geomPtAt z).point.fiber.obj (prd D (opEt Uo))) :=
        isEmpty_fib_prd D Uo z (fun hx => (hz z).1 (h hx) rfl)
      exact bij_of_isEmpty _
    · refine Or.inr ⟨inferInstance, ?_⟩
      by_cases hxo : x ∈ Uo
      · obtain ⟨t⟩ := nonempty_fib_opEt Uo x hxo
        exact prW_bijective D (opEt Uo) x t
      · have := isEmpty_fib_of_range D Uo z hDr x hxo hxz
        exact bij_of_isEmpty _
  · by_cases hxz : x = z
    · rw [hxz]
      obtain ⟨d⟩ := hDn
      exact Or.inl (fun _ => ⟨d, Subsingleton.elim _ _⟩)
    · obtain ⟨t⟩ := nonempty_fib_opEt Uz x ((hz x).2 hxz)
      exact Or.inr (fun _ => ⟨t, Subsingleton.elim _ _⟩)

variable (Λ) in
/-- **One-point MV classes at `z`**: `ε_loc ∘ κ` with `ε_loc` the class of `locC`. -/
def IsLoc (F : EtSh Λ P) (z : P) (β : Ext.{u} (freeSh Λ (etId P)) F 2) : Prop :=
  ∃ (Uo Uz : P.Opens) (h : Uo ≤ Uz) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z) (D : P.Etale)
    (hD : Subsingleton ((geomPtAt z).point.fiber.obj D)) (hDn : Nonempty ((geomPtAt z).point.fiber.obj D))
    (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = z) (κ : Ext.{u} (freeSh Λ (prd D (opEt Uo))) F 1),
    β = (locC_shortExact (Λ := Λ) D h z hz hD hDn hDr).extClass.comp κ (show 1 + 1 = 2 from rfl)

end Gen

section P1

end P1

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex

For finitely many points `z k` (`z` injective), one-point neighbourhoods `S k` of `z k` (one geometric point over
`z k`, every other point over `U₀ = P ∖ {z k}`):
* `copPrd S U₀ = ∐ (S k ×_P U₀)`, `copP₁ : copPrd ⟶ cop S`, `copP₂ : copPrd ⟶ U₀`;
* `mvCop Λ S U₀`: the MV complex `Λ[copPrd] ⟶ Λ[cop S] ⊞ Λ[U₀] ⟶ Λ[P]`;
* **`mvCop_shortExact`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} (S : ι → P.Etale) (U₀ : P.Opens)

variable (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)

include hzi hU hD hDn hDr in
/-- **The multi-point MV complex is short exact.** -/
theorem mvCop_shortExact : (mvCop Λ S U₀).ShortExact := by
  refine mvC_shortExact' _ _ _ _ _ (fun x => inferInstance) (fun x => ?_) (fun x => ?_)
  · by_cases hx : x ∈ U₀
    · exact Or.inr ⟨inferInstance, copP₁_bij S U₀ x hx⟩
    · obtain ⟨k₀, rfl⟩ := exists_eq_z_of_not_mem U₀ z hU x hx
      refine Or.inl ⟨fib_cop_sub S U₀ z hzi hU hD hDr k₀, ?_⟩
      have : IsEmpty ((geomPtAt (z k₀)).point.fiber.obj (opEt U₀)) :=
        ⟨fun b => hx (mem_of_fib_opEt U₀ _ b)⟩
      exact bij_of_isEmpty _
  · by_cases hx : x ∈ U₀
    · obtain ⟨t⟩ := nonempty_fib_opEt U₀ x hx
      exact Or.inr (fun _ => ⟨t, Subsingleton.elim _ _⟩)
    · obtain ⟨k₀, rfl⟩ := exists_eq_z_of_not_mem U₀ z hU x hx
      obtain ⟨d⟩ := hDn k₀
      exact Or.inl (fun _ => ⟨(geomPtAt (z k₀)).point.fiber.map (copι S k₀) d, Subsingleton.elim _ _⟩)

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2S2 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die

* `prdMap d X : prd D₁ X ⟶ prd D X` for `d : D₁ ⟶ D`, `prdMap_prW`, `prdMap_prT`;
* **`locC_shrink`**: `ε_loc(D₁) ∘ Λ[prdMap d] = ε_loc(D)`; **`locCls_shrink`**: the class of `κ` through `D` is the
  class of its pullback through `D₁`; `opn_sub`, `opn_nonempty`, `opn_range`, **`isLoc_opn`** (an open of `D`
  containing the points over `z` gives the same class);
* **`mv_res_W`**, **`mv_res_U`**: `ε ∘ Λ[p₁]^* γ = 0`, `ε ∘ Λ[p₂]^* γ = 0` for any MV square; `loc_res_D`,
  `loc_res_U` (the one-point case).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

section Prd

end Prd

section Shrink

end Shrink

section Opn

variable (D : P.Etale) (V : D.left.Opens) (z : P)

/-- **Shrinking a one-point presentation to an open of `D`** containing the points over `z`. -/
theorem isLoc_opn {F : EtSh Λ P} {Uo Uz : P.Opens} (h : Uo ≤ Uz) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z)
    (hD : Subsingleton ((geomPtAt z).point.fiber.obj D)) (hDn : Nonempty ((geomPtAt z).point.fiber.obj D))
    (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = z) (hV : ∀ v : D.left, D.hom v = z → v ∈ V)
    (κ : Ext.{u} (freeSh Λ (prd D (opEt Uo))) F 1) :
    (locC_shortExact (Λ := Λ) D h z hz hD hDn hDr).extClass.comp κ (show 1 + 1 = 2 from rfl) =
      (locC_shortExact (Λ := Λ) (opn D V) h z hz (opn_sub D V z hD) (opn_nonempty D V z hV hDn)
        (opn_range D V z Uo hDr)).extClass.comp
        ((Ext.mk₀ (freeMap Λ (prdMap (opnι D V) (opEt Uo)))).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl) :=
  locCls_shrink h (opnι D V) _ _ κ

end Opn

section Res

end Res

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2R4 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M6a (4): the relation between one-point classes

* `ext_comp_sum`, `ext_sum_comp`, `ext_mk₀_sum` (finite sums and `Ext`);
* `locLe`, `locRng`; `extClass_loc_eq`: the one-point class at `z k` is the multi-point MV class followed by
  `copPr k` (naturality along `mvLocHom`);
* **`relation_sum`**: `Σ_k ε_loc(S k) ∘ (Λ[S k ×_P U₀ ⟶ U₀]^* κ) = 0` for every `κ ∈ Ext¹(Λ[U₀], F)`;
* `isLoc_relation_term`: each summand is a one-point class (`IsLoc`) at `z k`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe w u

section ExtSum

end ExtSum

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι]
  (S : ι → P.Etale) (U₀ : P.Opens)
  (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)
  (Uz : ι → P.Opens) (hz : ∀ k (x : P), x ∈ Uz k ↔ x ≠ z k)

include hzi hU hD hDn hDr hz in
/-- The one-point class at `z k` factors through the multi-point MV class. -/
theorem extClass_loc_eq (k : ι) :
    (locC_shortExact (Λ := Λ) (S k) (locLe U₀ z hU Uz hz k) (z k) (hz k) (hD k) (hDn k) (hDr k)).extClass =
      (mvCop_shortExact (Λ := Λ) S U₀ z hzi hU hD hDn hDr).extClass.comp
        (Ext.mk₀ (copPr Λ (fun j => prd (S j) (opEt U₀)) k)) (add_zero 1) := by
  have e := ShortComplex.ShortExact.extClass_naturality (mvCop_shortExact (Λ := Λ) S U₀ z hzi hU hD hDn hDr)
    (locC_shortExact (Λ := Λ) (S k) (locLe U₀ z hU Uz hz k) (z k) (hz k) (hD k) (hDn k) (hDr k))
    (mvLocHom Λ S U₀ k (locLe U₀ z hU Uz hz k) (locRng S U₀ z hzi hU hDr Uz hz k))
  rw [mvLocHom_τ₁, mvLocHom_τ₃, Ext.mk₀_id_comp] at e
  exact e.symm

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree

* `dg W`: the diagonal of `W ×_P W` (clopen: `isClopen_dg`); `dsec Λ W`: its indicator section of `Λ_W`;
* `shapφ Λ W : Λ[W] ⟶ π_* Λ_W` is the map given by `dsec` (`shapφ_taut`);
* `cval_S`: values of `Σ_a l_a · τ_a^* dsec` along a sheet;
* **`isIso_shapφ`**, **`shapIso`**: `shapφ` is an isomorphism (stalkwise: `stalk_inj`, `stalk_surj`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Dg

end Dg

section Iso

variable (Λ : Type u) [CommRing Λ] (W : P.Etale) [IsSeparated W.hom]

variable [QuasiCompact W.hom]

/-- **Shapiro iso at sheaf level**: `Λ[W] ≅ π_* Λ_W`. -/
def shapIso (n : ℕ) (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n) :
    freeSh Λ W ≅ (push W.hom Λ).obj (unitSh Λ W.left) :=
  @asIso _ _ _ _ (shapφ Λ W) (isIso_shapφ Λ W n hn)

theorem shapIso_hom (n : ℕ) (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n) :
    (shapIso Λ W n hn).hom = shapφ Λ W := rfl

end Iso

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E3 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes

* `fib_injective_of_mono`: a mono of étale objects is injective on geometric fibres;
* `chartLift`, `chartRing`: an affine open `V` of `D` lying over an affine chart `c : Spec R ⟶ P` gives
  `φ_V : R ⟶ Γ(V)` with `Spec φ_V ≫ c = fromSpec ≫ D.hom`, and `φ_V` is étale;
* `A1pt k a`: the point `X = a` of `A¹`; `exists_A1pt_of_closed`: closed points of a chart are of this form;
* `phiG`, `D1`, `d1`: the basic open `Spec Γ(V)_g` as an étale object over `P` through the chart;
* **`isLoc_aff`**: a one-point class at `z ∈ range c` has a presentation `IsLocAff` through `Spec B`,
  `B` a Dedekind domain étale over `k[X]` in which `X - a` generates a prime (the `purity_xi` setting).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtDed

section Mono

end Mono

section Chart

end Chart

section A1

end A1

section D1

end D1

section Aff

variable {k : Type u} [Field k] {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

variable (Λ) in
/-- **Affine Dedekind presentation** of a one-point class at `c (X = a)`: through `Spec B ⟶ A¹ ⟶ P` with `B` a
Dedekind domain étale over `k[X]` in which `X - a` generates a nonzero prime. -/
def IsLocAff (F : EtSh Λ P) (c : A1 k ⟶ P) (a : k) (β : Ext.{u} (freeSh Λ (etId P)) F 2) : Prop :=
  ∃ (B : CommRingCat.{u}) (φ : CommRingCat.of k[X] ⟶ B) (_ : Etale (Spec.map φ ≫ c)),
    φ.hom.Etale ∧ IsDedekindDomain B ∧ φ.hom (X - C a) ≠ 0 ∧ (Ideal.span {φ.hom (X - C a)}).IsPrime ∧
    ∃ (Uo Uz : P.Opens) (h : Uo ≤ Uz) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a))
      (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
      (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
      (hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uo ∨ (chEt c φ).hom v = c (A1pt k a))
      (κ : Ext.{u} (freeSh Λ (prd (chEt c φ) (opEt Uo))) F 1),
      β = (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD hDn hDr).extClass.comp κ
        (show 1 + 1 = 2 from rfl)

end Aff

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2i =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2i): stages S2-S3 assembled (pure algebra)

GLOB/REL PLAN v1, stages S2-S3 (abstract rings). `O = k[X]`, `O' = B₁`, `Y = Γ(Y₀)`, `G = Γ(W₁)`, `κ₀ : Y →ₐ[O] G`
(`G = O'[κ₀ Y]`, Gen), `L = t^e L'` with `L'` a unit of `O'` and `L^N y` integral for every `y`:
* **`exists_S23`**: `N`, `u_S ∈ S = integralClosure O Y` (`u_S ≡ t^N` mod every `J i`), `z` integral over `O'` such that
  `y := liveMod u_S t^N = t^N + (u_S - t^N) e_live` is a non-zero-divisor of `Y`, divides some `c₀ ∈ O ∖ 0`, and
  `toPiQ (κ₀ y) = t^N ũ (1 - t z)` (`ũ = (u₁ on p₁, 1 elsewhere)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section S23

variable {O O' Y G : Type} [CommRing O] [IsDomain O] [CommRing O'] [CommRing Y] [CommRing G]
  [Algebra O O'] [Algebra O Y] [Algebra O' G] [Algebra O G] [IsScalarTower O O' G]
  (hY : ∀ (m : Ideal Y) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing Y]
  (hG : ∀ (m : Ideal G) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing G]
  [DecidableEq (minimalPrimes G)] (κ₀ : Y →ₐ[O] G) (t : O)

include hG in
/-- **Stages S2-S3**: `toPiQ (κ₀ y) = t^N ũ (1 - t z)` for the live modification `y` of the CRT approximation `u_S`. -/
theorem exists_S23 (hgenG : ∀ x : G, x ∈ Algebra.adjoin O' (Set.range κ₀))
    {L L' : O} {e : ℕ} (hL : L = t ^ e * L') (hL' : IsUnit (algebraMap O O' L'))
    (hLY : ∀ y : Y, ∃ N : ℕ, IsIntegral O (L ^ N • y))
    (h1 : ∀ x : O', ∃ c : O, ∃ y : O', x = algebraMap O O' c + algebraMap O O' t * y)
    {ι : Type} [Finite ι] (J : ι → Ideal (integralClosure O Y)) (hJ : Pairwise fun i j => IsCoprime (J i) (J j))
    (hJt : ∀ (n : ℕ) (i : ι), IsCoprime (Ideal.span {algebraMap O (integralClosure O Y) t ^ n}) (J i))
    (htY : ∀ Q : minimalPrimes Y, algebraMap O Y t ∉ (Q : Ideal Y))
    (hinj : ∀ q : minimalPrimes G, Function.Injective fun b : O' => toPiQ (algebraMap O' G b) q)
    (ht : ¬ IsUnit (algebraMap O O' t)) (htG : ∀ q : minimalPrimes G, toPiQ (algebraMap O G t) q ≠ 0)
    (p₁ : minimalPrimes G) {u₁ : FractionRing (G ⧸ (p₁ : Ideal G))} (hu₁ : u₁ ≠ 0) {j : ℕ}
    (hj₁ : ∃ a, algebraMap (G ⧸ (p₁ : Ideal G)) _ a = toPiQ (algebraMap O G t) p₁ ^ j * u₁)
    (hj₂ : ∃ b, algebraMap (G ⧸ (p₁ : Ideal G)) _ b = toPiQ (algebraMap O G t) p₁ ^ j * u₁⁻¹) :
    ∃ (N : ℕ) (uS : integralClosure O Y) (z : PiQ G),
      (∀ i, uS - algebraMap O (integralClosure O Y) t ^ N ∈ J i) ∧
      (letI : Algebra O' (PiQ G) := (toPiQ.comp (algebraMap O' G)).toAlgebra; IsIntegral O' z) ∧
      liveMod hY (uS : Y) (algebraMap O Y t ^ N) ∈ Y⁰ ∧ (∃ c₀ : O, c₀ ≠ 0 ∧ liveMod hY (uS : Y) (algebraMap O Y t ^ N) ∣ algebraMap O Y c₀) ∧
      toPiQ (κ₀ (liveMod hY (uS : Y) (algebraMap O Y t ^ N))) = toPiQ (algebraMap O G t) ^ N * Function.update (1 : PiQ G) p₁ u₁ *
        (1 - toPiQ (algebraMap O G t) * z) := by
  let _ : Algebra O' (PiQ G) := (toPiQ.comp (algebraMap O' G)).toAlgebra
  let _ : Algebra O (PiQ G) := (toPiQ.comp (algebraMap O G)).toAlgebra
  haveI : @IsScalarTower O O' (PiQ G) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun c =>
    congrArg toPiQ (IsScalarTower.algebraMap_apply O O' G c)
  let F : Y →ₐ[O] PiQ G :=
    { toRingHom := toPiQ.comp κ₀.toRingHom
      commutes' := fun c => congrArg toPiQ (κ₀.commutes c) }
  let f : integralClosure O Y →ₐ[O] PiQ G := F.comp (integralClosure O Y).val
  have hS : ∀ y : Y, ∃ N : ℕ, L ^ N • y ∈ integralClosure O Y :=
    fun y => (hLY y).imp fun _ h => (mem_integralClosure_iff O Y).2 h
  have hgen : ∀ x : G, ∃ N : ℕ, algebraMap O (PiQ G) t ^ N * toPiQ x ∈ hatS (O' := O') f := by
    intro x
    let ψ : G →ₐ[O'] PiQ G := { toRingHom := toPiQ, commutes' := fun _ => rfl }
    have hq : toPiQ x ∈ Algebra.adjoin O' (Set.range F) := by
      refine Algebra.adjoin_mono ?_ (mem_adjoin_map (Set.range κ₀) ψ (hgenG x))
      rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, rfl⟩
    exact exists_pow_mul_mem_hatS (integralClosure O Y) F t hL hL' hS hq
  obtain ⟨N, hN⟩ := exists_glob_approx' f t hG h1 J hJ hJt hgen (algebraMap O G t) rfl htG p₁ hu₁ hj₁ hj₂
  obtain ⟨uS, hJu, z, hz, hfu⟩ := hN fun _ => algebraMap O (integralClosure O Y) t ^ N
  have hzI : IsIntegral O' z := isIntegral_of_mem_hatS f hz
  have hc : ∀ q, (1 - algebraMap O (PiQ G) t * z) q ≠ 0 := one_sub_mul_ne_zero f t hinj ht hz
  have hb : ∀ q, Function.update (1 : PiQ G) p₁ u₁ q ≠ 0 := by
    intro q
    by_cases hq : q = p₁
    · subst hq
      rw [Function.update_self]
      exact hu₁
    · rw [Function.update_of_ne hq, Pi.one_apply]
      exact one_ne_zero
  have hκ : ∀ q, F (uS : Y) q ≠ 0 := by
    intro q
    show f uS q ≠ 0
    rw [hfu]
    exact coord_ne_zero htG hb hc N q
  have hv : ∀ Q : minimalPrimes Y, algebraMap O Y t ^ N ∉ (Q : Ideal Y) :=
    fun Q h => htY Q (Q.2.1.1.mem_of_pow_mem N h)
  have hnzd : liveMod hY (uS : Y) (algebraMap O Y t ^ N) ∈ Y⁰ :=
    mem_nonZeroDivisors_of_notMem hY _ (liveMod_notMem hY (uS : Y) _ hv)
  have hint : liveMod hY (uS : Y) (algebraMap O Y t ^ N) ∈ integralClosure O Y := liveMod_mem_integralClosure hY uS.2
    (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem (integralClosure O Y) t) N)
  obtain ⟨c₀, hc₀, hdvd⟩ := exists_dvd_algebraMap (R := O) hnzd (IsIntegral.isAlgebraic hint)
  have hFy : F (liveMod hY (uS : Y) (algebraMap O Y t ^ N)) = F (uS : Y) :=
    funext fun q => map_liveMod hY (uS : Y) (algebraMap O Y t ^ N) ((Pi.evalRingHom _ q).comp F.toRingHom) (hκ q)
  exact ⟨N, uS, z, hJu, hzI, hnzd, ⟨c₀, hc₀, hdvd⟩, hFy.trans hfu⟩

end S23

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T7 =====
section

/-!
# S4-EtPBC-A, O2 S5g: presentations with sections through every fibre point, disjoint graphs, affine

* `secStep`: one more section through a fibre point `t`, keeping a map to the old presentation;
* **`isLoc_secs`**: sections `τ t` through every `t` of a finset of fibre points over `z`;
* **`isLoc_disj`**: shrinking so that the graphs of sections through different fibre points are disjoint;
* **`isLoc_aff_map`**: the affine Dedekind presentation of lib O2E3 `isLoc_aff`, with a map to the old `D`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk RamanujanPetersson.EtPBC.EtDed

universe u

section Secs

variable {P : Scheme.{u}} (Λ : Type u) [CommRing Λ]

/-- **One more section** through a fibre point `t`, keeping a map to the old presentation. -/
theorem secStep {F : EtSh Λ P} {z : P} {Uo Uz : P.Opens} (h : Uo ≤ Uz) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z)
    {D₀ : P.Etale} (hD₀ : Subsingleton ((geomPtAt z).point.fiber.obj D₀))
    (hDn₀ : Nonempty ((geomPtAt z).point.fiber.obj D₀)) (hDr₀ : ∀ v : D₀.left, D₀.hom v ∈ Uo ∨ D₀.hom v = z)
    (κ₀ : Ext.{u} (freeSh Λ (prd D₀ (opEt Uo))) F 1) (hzc : IsClosed ({z} : Set P)) (hG : Subsingleton (Gal z))
    (T : P.Etale) (t : (geomPtAt z).point.fiber.obj T) :
    ∃ (D : P.Etale) (hD : Subsingleton ((geomPtAt z).point.fiber.obj D))
      (hDn : Nonempty ((geomPtAt z).point.fiber.obj D)) (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = z)
      (κ : Ext.{u} (freeSh Λ (prd D (opEt Uo))) F 1) (_ : D ⟶ D₀) (s : D ⟶ T),
      (∀ d, (geomPtAt z).point.fiber.map s d = t) ∧
      (locC_shortExact (Λ := Λ) D₀ h z hz hD₀ hDn₀ hDr₀).extClass.comp κ₀ (show 1 + 1 = 2 from rfl) =
        (locC_shortExact (Λ := Λ) D h z hz hD hDn hDr).extClass.comp κ (show 1 + 1 = 2 from rfl) := by
  obtain ⟨d₀⟩ := hDn₀
  obtain ⟨V, hV, hVn, hVc⟩ := exists_opn_pt z hzc hG (prd D₀ T) (pair z d₀ t)
  let dm : opn (prd D₀ T) V ⟶ D₀ := opnι (prd D₀ T) V ≫ prW D₀ T
  have hw : ∀ v : (opn (prd D₀ T) V).left, (opn (prd D₀ T) V).hom v = D₀.hom (dm.left v) := fun v =>
    (congrArg (fun f : (opn (prd D₀ T) V).left ⟶ P => f v) (MorphismProperty.Over.w dm)).symm.trans
      (Scheme.Hom.comp_apply _ _ _)
  have hDr : ∀ v : (opn (prd D₀ T) V).left, (opn (prd D₀ T) V).hom v ∈ Uo ∨ (opn (prd D₀ T) V).hom v = z :=
    fun v => by rw [hw v]; exact hDr₀ _
  refine ⟨opn (prd D₀ T) V, hV, hVn, hDr,
    (Ext.mk₀ (freeMap Λ (prdMap dm (opEt Uo)))).comp κ₀ (zero_add 1), dm, opnι (prd D₀ T) V ≫ prT D₀ T,
    fun d => ?_, ?_⟩
  · rw [Functor.map_comp_apply, hVc d, pair_snd]
  · exact locCls_shrink h dm _ _ κ₀

/-- **Sections through every fibre point of a finset** `S` (after shrinking the presentation). -/
theorem isLoc_secs {F : EtSh Λ P} {z : P} {Uo Uz : P.Opens} (h : Uo ≤ Uz) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z)
    {D₀ : P.Etale} (hD₀ : Subsingleton ((geomPtAt z).point.fiber.obj D₀))
    (hDn₀ : Nonempty ((geomPtAt z).point.fiber.obj D₀)) (hDr₀ : ∀ v : D₀.left, D₀.hom v ∈ Uo ∨ D₀.hom v = z)
    (κ₀ : Ext.{u} (freeSh Λ (prd D₀ (opEt Uo))) F 1) (hzc : IsClosed ({z} : Set P)) (hG : Subsingleton (Gal z))
    (T : P.Etale) [DecidableEq ((geomPtAt z).point.fiber.obj T)] (S : Finset ((geomPtAt z).point.fiber.obj T)) :
    ∃ (D : P.Etale) (hD : Subsingleton ((geomPtAt z).point.fiber.obj D))
      (hDn : Nonempty ((geomPtAt z).point.fiber.obj D)) (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = z)
      (κ : Ext.{u} (freeSh Λ (prd D (opEt Uo))) F 1) (τ : ∀ t, t ∈ S → (D ⟶ T)),
      (∀ t ht d, (geomPtAt z).point.fiber.map (τ t ht) d = t) ∧
      (locC_shortExact (Λ := Λ) D₀ h z hz hD₀ hDn₀ hDr₀).extClass.comp κ₀ (show 1 + 1 = 2 from rfl) =
        (locC_shortExact (Λ := Λ) D h z hz hD hDn hDr).extClass.comp κ (show 1 + 1 = 2 from rfl) := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨D₀, hD₀, hDn₀, hDr₀, κ₀, fun t ht => absurd ht (Finset.notMem_empty t),
      fun t ht => absurd ht (Finset.notMem_empty t), rfl⟩
  | insert t S htS ih =>
    obtain ⟨D₁, hD₁, hDn₁, hDr₁, κ₁, τ₁, hτ₁, he₁⟩ := ih
    obtain ⟨D, hD, hDn, hDr, κ, dm, s, hs, he⟩ := secStep Λ h hz hD₁ hDn₁ hDr₁ κ₁ hzc hG T t
    refine ⟨D, hD, hDn, hDr, κ, fun t' ht' => if h' : t' = t then s else
      dm ≫ τ₁ t' ((Finset.mem_insert.1 ht').resolve_left h'), fun t' ht' d => ?_, he₁.trans he⟩
    by_cases h' : t' = t
    · beta_reduce
      rw [dif_pos h', hs d, h']
    · beta_reduce
      rw [dif_neg h', Functor.map_comp_apply, hτ₁]

/-- **Disjoint graphs**: shrinking so that graphs of sections through different fibre points do not meet. -/
theorem isLoc_disj {F : EtSh Λ P} {z : P} {Uo Uz : P.Opens} (h : Uo ≤ Uz) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ z)
    {D : P.Etale} (hD : Subsingleton ((geomPtAt z).point.fiber.obj D))
    (hDn : Nonempty ((geomPtAt z).point.fiber.obj D)) (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = z)
    (κ : Ext.{u} (freeSh Λ (prd D (opEt Uo))) F 1) (hG : Subsingleton (Gal z)) (T : P.Etale) [IsSeparated T.hom]
    [Finite ((geomPtAt z).point.fiber.obj T)] (τ : (geomPtAt z).point.fiber.obj T → (D ⟶ T))
    (hτ : ∀ t d, (geomPtAt z).point.fiber.map (τ t) d = t) :
    ∃ (D' : P.Etale) (hD' : Subsingleton ((geomPtAt z).point.fiber.obj D'))
      (hDn' : Nonempty ((geomPtAt z).point.fiber.obj D')) (hDr' : ∀ v : D'.left, D'.hom v ∈ Uo ∨ D'.hom v = z)
      (κ' : Ext.{u} (freeSh Λ (prd D' (opEt Uo))) F 1) (τ' : (geomPtAt z).point.fiber.obj T → (D' ⟶ T)),
      (∀ t d, (geomPtAt z).point.fiber.map (τ' t) d = t) ∧
      (∀ t t', t ≠ t' → ∀ v, v ∉ graphMeet (τ' t) (τ' t')) ∧
      (locC_shortExact (Λ := Λ) D h z hz hD hDn hDr).extClass.comp κ (show 1 + 1 = 2 from rfl) =
        (locC_shortExact (Λ := Λ) D' h z hz hD' hDn' hDr').extClass.comp κ' (show 1 + 1 = 2 from rfl) := by
  let Z : Set D.left := ⋃ p : {p : (geomPtAt z).point.fiber.obj T × (geomPtAt z).point.fiber.obj T // p.1 ≠ p.2},
    graphMeet (τ p.1.1) (τ p.1.2)
  have hZ : IsClosed Z := isClosed_iUnion_of_finite fun p => isClosed_graphMeet _ _
  let V : D.left.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  obtain ⟨d⟩ := id hDn
  have hV : ∀ v : D.left, D.hom v = z → v ∈ V := by
    intro v hv
    rw [eq_fpt_of_over hD d v hv]
    show fpt z d ∉ Z
    simp only [Z, Set.mem_iUnion, not_exists]
    intro p
    exact not_mem_graphMeet hG d (by rw [hτ, hτ]; exact p.2)
  refine ⟨opn D V, opn_sub D V z hD, opn_nonempty D V z hV hDn, opn_range D V z Uo hDr,
    (Ext.mk₀ (freeMap Λ (prdMap (opnι D V) (opEt Uo)))).comp κ (zero_add 1), fun t => opnι D V ≫ τ t,
    fun t d' => ?_, fun t t' htt v hv => ?_, isLoc_opn (Λ := Λ) D V z h hz hD hDn hDr hV κ⟩
  · rw [Functor.map_comp_apply, hτ]
  · have h1 := graphMeet_natural (opnι D V) (τ t) (τ t') hv
    have h2 : (opnι D V).left v ∉ Z := opnι_mem D V v
    exact h2 (Set.mem_iUnion.2 ⟨⟨(t, t'), htt⟩, h1⟩)

end Secs

section AffMap

variable {k : Type u} [Field k] {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} [IsAlgClosed k] (c : A1 k ⟶ P)
  [IsOpenImmersion c]

/-- **The affine Dedekind presentation with a map to the old `D`** (lib O2E3 `isLoc_aff`, keeping `d1`). -/
theorem isLoc_aff_map {F : EtSh Λ P} (a : k) {Uo Uz : P.Opens} (h : Uo ≤ Uz)
    (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a)) {D : P.Etale}
    (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj D))
    (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj D))
    (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = c (A1pt k a)) (κ : Ext.{u} (freeSh Λ (prd D (opEt Uo))) F 1) :
    ∃ (B : CommRingCat.{u}) (φ : CommRingCat.of k[X] ⟶ B) (_ : Etale (Spec.map φ ≫ c)),
      φ.hom.Etale ∧ IsDedekindDomain B ∧ φ.hom (X - C a) ≠ 0 ∧ (Ideal.span {φ.hom (X - C a)}).IsPrime ∧
      ∃ (hD' : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
        (hDn' : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
        (hDr' : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uo ∨ (chEt c φ).hom v = c (A1pt k a))
        (κ' : Ext.{u} (freeSh Λ (prd (chEt c φ) (opEt Uo))) F 1) (_ : chEt c φ ⟶ D),
        (locC_shortExact (Λ := Λ) D h (c (A1pt k a)) hz hD hDn hDr).extClass.comp κ (show 1 + 1 = 2 from rfl) =
          (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD' hDn' hDr').extClass.comp κ'
            (show 1 + 1 = 2 from rfl) := by
  obtain ⟨n⟩ := id hDn
  have hw : D.hom (fpt _ n) = c (A1pt k a) := fib_over _ n
  have hwU : fpt _ n ∈ D.hom ⁻¹ᵁ c.opensRange := by
    show D.hom (fpt _ n) ∈ c.opensRange
    rw [hw]
    exact ⟨_, rfl⟩
  obtain ⟨V, hVa, hwV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens D.left)) hwU
  have hV : IsAffineOpen V := hVa
  have hVc : ∀ v ∈ V, D.hom v ∈ Set.range c := fun v hv => by
    have := hVle hv
    simpa [Scheme.Hom.coe_opensRange] using this
  letI := (chartRing c D hV hVc).hom.toAlgebra
  haveI : Algebra.Etale k[X] Γ(D.left, V) := chartRing_etale c D hV hVc
  let q := hV.primeIdealOf ⟨fpt _ n, hwV⟩
  have hqw : hV.fromSpec q = fpt _ n := hV.fromSpec_primeIdealOf _
  have hpt : Spec.map (chartRing c D hV hVc) q = A1pt k a := by
    rw [spec_chartRing]
    apply c.isOpenEmbedding.injective
    exact (chartLift_apply c D hV hVc q).trans ((congrArg (fun x => D.hom x) hqw).trans hw)
  have hqa : q.asIdeal.under k[X] = Ideal.span {X - C a} := congrArg PrimeSpectrum.asIdeal hpt
  obtain ⟨g, hgq, -, hded, hne, hspan, hprime⟩ := exists_good_away q.asIdeal a hqa
  -- the presentation through `D1`
  have hD₁ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (D1 c hV hVc g)) :=
    ⟨fun b b' => fib_injective_of_mono (d1 c hV hVc g) _ (Subsingleton.elim _ _)⟩
  let v₁ : Spec (CommRingCat.of (Localization.Away g)) :=
    ⟨q.asIdeal.map (algebraMap Γ(D.left, V) (Localization.Away g)), hprime⟩
  have hv₁ : (d1 c hV hVc g).left v₁ = fpt _ n := by
    show hV.fromSpec (Spec.map (locG g) v₁) = fpt _ n
    have : Spec.map (locG g) v₁ = q := PrimeSpectrum.ext
      (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g) q.isPrime
        ((Ideal.disjoint_powers_iff_notMem_of_isPrime g).2 hgq))
    rw [this, hqw]
  obtain ⟨b, -, -⟩ := exists_lift_fib (d1 c hV hVc g) _ n v₁ hv₁
  have hDn₁ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (D1 c hV hVc g)) := ⟨b⟩
  have hDr₁ : ∀ v : (D1 c hV hVc g).left, (D1 c hV hVc g).hom v ∈ Uo ∨ (D1 c hV hVc g).hom v = c (A1pt k a) :=
    fun v => by
      have e := d1_apply c hV hVc g v
      rcases hDr ((d1 c hV hVc g).left v) with h1 | h1
      · exact Or.inl ((congrArg (· ∈ Uo) e).mpr h1)
      · exact Or.inr (e.trans h1)
  have hS := locC_shortExact (Λ := Λ) D h _ hz hD hDn hDr
  have hS₁ := locC_shortExact (Λ := Λ) (D1 c hV hVc g) h _ hz hD₁ hDn₁ hDr₁
  have hφe : Etale (Spec.map (phiG c hV hVc g)) := Etale.of_comp _ c
  refine ⟨CommRingCat.of (Localization.Away g), phiG c hV hVc g, inferInstance,
    (HasRingHomProperty.Spec_iff (P := @Etale)).1 hφe, hded, ?_, ?_, hD₁, hDn₁, hDr₁,
    (Ext.mk₀ (freeMap Λ (prdMap (d1 c hV hVc g) (opEt Uo)))).comp κ (zero_add 1), d1 c hV hVc g, ?_⟩
  · rw [phiG_apply]; exact hne
  · rw [phiG_apply, hspan]; exact hprime
  · exact locCls_shrink h (d1 c hV hVc g) hS₁ hS κ

end AffMap

end RamanujanPetersson.EtPBC.EtMV

end

end


