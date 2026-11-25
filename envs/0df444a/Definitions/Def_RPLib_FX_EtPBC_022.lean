-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_022
-- name    : RPLib_FX_EtPBC_022
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:05:00.182592+00:00
-- url     : https://prove2.me/theorems/5d094d87-14a0-54c4-9c81-ecc0f0aa4617
-- title:
--   Proper base change for the projective line, library file 022
-- statement:
--   File 022 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
--   * `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
--   * `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
--   * `S4.Def_RP_EtPBC_A_CovFbA`: S4-EtPBC-A, R4-T2 (G1d, part 1): lifting morphisms to fibres `Spec G` of chart algebras
--   * `S4.Def_RP_EtPBC_A_Inj0c`: S4-EtPBC-A, G1c: base change is injective on germs in degree `0` (universally closed `g`)
--   * `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
--   * `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
--   * `S4.Def_RP_EtPBC_A_NbExt2`: S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood
--   * `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
--   * `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
--   * `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
--   * `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
--   * `S4.Def_RP_EtPBC_A_ESheet`: S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_EG`: S4-EtPBC-A, M4(E), EG: relations of the sections `f_j` are relations of the generators near `ξ`
--   * `S4.Def_RP_EtPBC_A_O2MVo`: S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`
--   * `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
--   * `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
--   * `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
--   * `S4.Def_RP_EtPBC_A_O2ZarCh`: S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step
--   * `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
--   * `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
--   * `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_018

/-!
# Proper base change for the projective line, library file 022

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
* `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
* `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
* `S4.Def_RP_EtPBC_A_CovFbA`: S4-EtPBC-A, R4-T2 (G1d, part 1): lifting morphisms to fibres `Spec G` of chart algebras
* `S4.Def_RP_EtPBC_A_Inj0c`: S4-EtPBC-A, G1c: base change is injective on germs in degree `0` (universally closed `g`)
* `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
* `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
* `S4.Def_RP_EtPBC_A_NbExt2`: S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood
* `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
* `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
* `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
* `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
* `S4.Def_RP_EtPBC_A_ESheet`: S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`
* `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
* `S4.Def_RP_EtPBC_A_EG`: S4-EtPBC-A, M4(E), EG: relations of the sections `f_j` are relations of the generators near `ξ`
* `S4.Def_RP_EtPBC_A_O2MVo`: S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`
* `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
* `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
* `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
* `S4.Def_RP_EtPBC_A_O2ZarCh`: S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step
* `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
* `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
* `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_PushBC =====
section

/-!
# S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart

For an etale `c : V ⟶ X` and any `j : U ⟶ X`, put `U' = V ×_X U` with `j' = fst : U' ⟶ V`, `i = snd : U' ⟶ U`.
* `etBC`: `etComp c ⋙ etPull j ≅ etPull j' ⋙ etComp i` (`(W → V → X) ×_X U ≅ W ×_V U'` over `U`);
* **`pushResBC`**: `j_* ⋙ c^* ≅ i^* ⋙ j'_*` on etale sheaves (base change for an etale map);
* `stkBC` (`c` an open immersion): `(j_* G)_(c t) ≅ (j'_* (i^* G))_t`;
* **`stalkEquivBC`** (b2 on a chart): for `c : Spec A ⟶ X`, `j` open, `G` lisse, `t` closed,
  `(j_* G)_(c t) ≃ (j'_* (i^* G))_η̄^{II}`;
* on `P¹`: `p1Chart k s` (`chartA1` or `chartA1'`) and `p1Pt k s` with `p1Chart k s (p1Pt k s) = s` (closed if `s` is),
  `nonempty_pb` (`U ×_{P¹} A¹ ≠ ∅` for `U` nonempty), **`stalkEquivP1`**: `(j_* G)_s̄ ≃ (j'_* (i^* G))_η̄^{II}`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.PushBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Gen

end Gen

section Chart

end Chart

section P1

variable (k : Type) [Field k]

/-- The point of the chart `p1Chart k s` over `s`. -/
def p1Pt (s : P1 k) : A1 k := (exists_p1Pt k s).choose

theorem p1Chart_p1Pt (s : P1 k) : p1Chart k s (p1Pt k s) = s := (exists_p1Pt k s).choose_spec

instance nonempty_pb {U : Scheme.{0}} (j : U ⟶ P1 k) [IsOpenImmersion j] [Nonempty U] (s : P1 k) :
    Nonempty (pullback (p1Chart k s) j : Scheme.{0}) := by
  obtain ⟨p, ⟨x, hx⟩, ⟨y, hy⟩⟩ := nonempty_preirreducible_inter (p1Chart k s).isOpenEmbedding.isOpen_range
    j.isOpenEmbedding.isOpen_range ⟨_, p1Pt k s, rfl⟩ (Set.range_nonempty _)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x y (hx.trans hy.symm)
  exact ⟨z⟩

end P1

end RamanujanPetersson.EtCompact.PushBC

end

end

-- ===== S4.Def_RP_EtPBC_A_BCMap =====
section

/-!
# S4-EtPBC-A, L1d: the data of the base change map at a geometric point

For `g : P ⟶ S` and a geometric point `s : Spec Ω ⟶ S`: the fibre `fib g s = P ×_S Spec Ω` with
`fibι : fib g s ⟶ P`; the cofiltered category `Nbhd s` of etale neighbourhoods `(V, v)` of `s`
(`s.point.fiber.Elements`); the system `nbhdSys : (V, v) ↦ Λ[g⁻¹ V]`; and the maps
`bcUnit j : Λ_{P_s} ⟶ ι^* Λ[g⁻¹ V]` (the global section of `ι^* Λ[g⁻¹ V]` obtained from the unit of `ι^* ⊣ ι_*`
restricted along the section `nbhdSec j : P_s ⟶ ι⁻¹(g⁻¹ V)` given by `v`). **`bcUnit_comp`**: they are compatible
with the transition maps, as required by the δ-lemma `Delta.injAt_all`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.PtSec

universe u

section Free

end Free

section OfSec

end OfSec

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

theorem nbhdSys_map {j j' : Nbhd s} (a : j' ⟶ j) :
    (nbhdSys Λ g s).map a = freeMap Λ ((etPull g).map a.1) := rfl

section EtPull

end EtPull

/-- The section `σ_v : P_s ⟶ ι⁻¹(g⁻¹ V)` over `P_s`. -/
def nbhdSec (j : Nbhd s) : etId (fib g s) ⟶ (etPull (fibι g s)).obj ((etPull g).obj j.1) :=
  MorphismProperty.Over.homMk (secL g s j) (secL_snd g s j)

theorem secL_map {j j' : Nbhd s} (a : j' ⟶ j) :
    secL g s j' ≫ ((etPull (fibι g s)).map ((etPull g).map a.1)).left = secL g s j :=
  pullback.hom_ext
    ((Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_fst (fibι g s) ((etPull g).map a.1))).trans
      ((secL_fst_assoc g s j' _).trans ((fibToNbhd_map g s a).trans (secL_fst g s j).symm))))
    ((Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_snd (fibι g s) ((etPull g).map a.1))).trans
      ((secL_snd g s j').trans (secL_snd g s j).symm)))

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAsN1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion

For `a : σ → A` (`σ` finite) and `p = span (range a)`:
* `aeval_monomial_mem_pow`, `aeval_mem_pow_of_coeff`, `mk_aeval_eq`: a polynomial whose coefficients vanish below total
  degree `n` evaluates (at `a`) into `p ^ n`.
* `truncEval a n : MvPowerSeries σ A →+* A ⧸ p ^ n`, `F ↦ mk (aeval a (truncTotal n F))`, `truncEval_compat`.
* **`hatPhi a : MvPowerSeries σ A →+* AdicCompletion p A`**, `evalₐ_hatPhi`, `hatPhi_X`, `hatPhi_C`.
-/

set_option autoImplicit false

open MvPowerSeries

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u v

section HatN1

variable {A : Type u} [CommRing A] {σ : Type v} [Fintype σ] (a : σ → A)

/-- `F ↦ (∑_{deg x < n} coeff x F • a ^ x) mod p ^ n`. -/
def truncEval (n : ℕ) : MvPowerSeries σ A →+* A ⧸ (Ideal.span (Set.range a)) ^ n where
  toFun F := Ideal.Quotient.mk _ (MvPolynomial.aeval a (truncTotal n F))
  map_one' := by
    refine (mk_aeval_eq a (truncTotal n 1) 1 fun x hx => ?_).trans (by rw [map_one, map_one])
    rw [coeff_truncTotal _ hx, ← MvPolynomial.coe_one, MvPolynomial.coeff_coe]
  map_mul' F G := by
    refine (mk_aeval_eq a (truncTotal n (F * G)) (truncTotal n F * truncTotal n G)
      fun x hx => ?_).trans (by rw [map_mul, map_mul])
    rw [coeff_truncTotal _ hx, coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]
  map_zero' := by
    rw [map_zero, map_zero, map_zero]
  map_add' F G := by
    rw [map_add, map_add, map_add]

end HatN1

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFbA =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d, part 1): lifting morphisms to fibres `Spec G` of chart algebras

For a surjection `θ : E ↠ G` and a morphism `w : W ⟶ Spec E` whose ring map `εW w : E → Γ(W)` kills `ker θ`,
**`gW θ w`** `: W ⟶ Spec G` is the induced lift, with `gW θ w ≫ Spec θ = w` (`gW_θ`), naturality in `W` (`gW_comp`)
and compatibility with localizations (`gW_compat`). **`ker_le_εW`**: the kernel condition holds when
`ker θ = (ker χ') E` and `W ⟶ Spec E ⟶ Spec R'` factors through `Spec χ'`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lift

end Lift

section Ker

variable {A B R' E k : Type u} [CommRing A] [CommRing B] [CommRing R'] [CommRing E] [CommRing k]
  [Algebra A B] [Algebra A R'] [Algebra (R' ⊗[A] B) E] (χ' : R' →+* k) {W : Scheme.{u}}

/-- **The kernel condition** for a morphism whose composite to `Spec R'` factors through `Spec χ'`. -/
theorem ker_le_εW {G : Type u} [CommRing G] (θ : E →+* G)
    (kθ : RingHom.ker θ = (RingHom.ker χ').map (rE (A := A) (B := B) (R' := R') (E := E)))
    (w : W ⟶ Spec (CommRingCat.of E)) (v : W ⟶ Spec (CommRingCat.of k))
    (hv : w ≫ Spec.map (CommRingCat.ofHom (rE (A := A) (B := B) (R' := R') (E := E))) =
      v ≫ Spec.map (CommRingCat.ofHom χ')) :
    RingHom.ker θ ≤ RingHom.ker (εW w) := by
  rw [kθ, Ideal.map_le_iff_le_comap]
  intro r hr
  have h := RingHom.congr_fun (εW_rE χ' w v hv) r
  simp only [RingHom.comp_apply] at h
  rw [RingHom.mem_ker.mp hr, map_zero] at h
  exact Ideal.mem_comap.mpr (RingHom.mem_ker.mpr h)

end Ker

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0c =====
section

/-!
# S4-EtPBC-A, G1c: base change is injective on germs in degree `0` (universally closed `g`)

* `fibB j x`: the fibre point `σ_v(x̄)` of `x̄ = geomPtAt x` over `ι⁻¹(g⁻¹ V)`; `cpt_fibB`: its point is `fibToNbhd x`;
* **`fibToNbhd_not_mem_supp`**: if `bc_j α = 0` then no point of `P_s` lands in the support of `sec0 α`;
* `fibCmp`, **`exists_fibToNbhd`**: every point of `g⁻¹ V` over `v` comes from `P_s`;
* **`bcInj_zero`**: for universally closed `g`, `BCInj Λ g s 0 G` for every sheaf `G` (the support of `sec0 α` is closed,
  its image in `V` is closed and misses `v`; shrink `V` to the complement, where every germ vanishes).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- The fibre point `σ_v(x̄)` over `ι⁻¹(g⁻¹ V)`. -/
abbrev fibB (j : Nbhd s) (x : fib g s) :
    (geomPtAt x).point.fiber.obj ((etPull (fibι g s)).obj ((etPull g).obj j.1)) :=
  (geomPtAt x).point.fiber.map (nbhdSec g s j) (geomPtAt x).top

theorem fibCmp_fibToNbhd (j : Nbhd s) :
    fibCmp g s j ≫ fibToNbhd g s j = pullback.fst (pullback.fst j.1.hom g) j.2.left := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (fun φ => fibCmp g s j ≫ φ) (fibToNbhd_fst g s j)).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun φ => φ ≫ j.2.left) (pullback.lift_snd _ _ _ : fibCmp g s j ≫ pullback.snd g s.pt = _)).trans
      (pullback.condition (f := pullback.fst j.1.hom g) (g := j.2.left)).symm)))
  · exact (Category.assoc _ _ _).trans ((congrArg (fun φ => fibCmp g s j ≫ φ) (fibToNbhd_snd g s j)).trans
      (pullback.lift_fst _ _ _ : fibCmp g s j ≫ pullback.fst g s.pt = _))

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_VLoc =====
section

/-!
# S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`

For `ι : X ⟶ P`, `π : Y ⟶ P`, `C = constSh Λ Y M`, `b : Λ_X ⟶ ι^* π_* C` and a separably closed `Ω`:
* `sigPt τ`: the geometric point `τ ≫ π_s` of `X` for `τ : Spec Ω ⟶ Y ×_P X`; `xMor τ`: the `Ω`-point of the fibre
  `fib π (τ ≫ π_s ≫ ι)` given by `τ`;
* `vval b τ := psi (ξ_{sigPt τ}(b)) (xMor τ)`, the value of `b` at `τ`;
* `kap h`: for a local representation `h : U ⟶ ι⁻¹ W`, the map `(Y ×_P X) ×_X U ⟶ π⁻¹ W`;
* **`vval_of_lift`**: along a local representation, `vval b τ = cval z (kap h (l pt))` for any lift `l` of `τ`;
* **`vval_locConst`**: `vval b` is locally constant: every `τ` has an open neighbourhood `N` of its point such that
  `vval b τ' = vval b τ` for all `τ'` with point in `N`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

variable {Λ : Type u} [CommRing Λ] {X P Y : Scheme.{u}} (ι : X ⟶ P) (π : Y ⟶ P) {M : ModuleCat.{u} Λ}
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **The value of `b` at an `Ω`-point `τ` of `Y ×_P X`.** -/
def vval (b : unitSh Λ X ⟶ (pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M)))
    (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι) : M :=
  psi π ((sigPt ι π τ).map ι) (xi ι (sigPt ι π τ) ((push π Λ).obj (constSh Λ Y M)) b)
    (xMor ι π τ (default : Spec (CommRingCat.of Ω)))

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

/-- The map `Y ×_P P_s ⟶ Y ×_P P_V` of a neighbourhood `j = (V, v)`. -/
def ysj (j : Nbhd s) : pullback π (fibι g s) ⟶ pullback (pullback.snd j.1.hom g) π :=
  pullback.lift (pullback.snd π (fibι g s) ≫ fibToNbhd g s j) (pullback.fst π (fibι g s)) (ysj_cond g s π j)

end BC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NbExt2 =====
section

/-!
# S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood

* `ysj_map`: `ysj j' ≫ (restriction along a : j' ⟶ j) = ysj j`;
* `etale_hV`, `nbR` (the neighbourhood `Spec R' ⟶ V ⟶ S` through `x'`), `nbRHom : nbR ⟶ j`;
* **`exists_clopen_nbhd`**: for an affine noetherian neighbourhood `j` and a clopen `O ⊆ Y_s` there is an affine
  noetherian `j' ⟶ j` and a clopen `C ⊆ Y_{j'}` with `ysj j' ⁻¹' C = O`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

section Map

end Map

section Nbhd

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S)
  [IsIso (s.pt ≫ gK)] (j : Nbhd s) [IsAffine j.1.left] (R' : Type u) [CommRing R'] [Algebra Γ(j.1.left, ⊤) R']
  [Algebra.Etale Γ(j.1.left, ⊤) R'] (x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))

/-- The etale `S`-scheme `Spec R' ⟶ V ⟶ S`. -/
def etR : S.Etale :=
  MorphismProperty.Over.mk ⊤ (hV j.1.left R' ≫ (nbh s j)) (by
    have : Etale (nbh s j) := j.1.prop
    have := etale_hV j.1.left R'
    infer_instance)

end Nbhd

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_DescK1 =====
section

/-!
# S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`

`0 → F → E → Λ_X → 0` short exact, `σ ∈ E(T)` with `b σ = 1`:
* `secT σ : Hom(Λ|_T, E|_T)` (the section `1 ↦ σ`), `secT_b`: `secT σ ≫ b = 1`;
* `retT : Hom(E|_T, F|_T)` with `a ≫ retT = 1` (`a_retT`): `x ↦ a⁻¹ (x - secT (b x))`;
* for `ψ : Z ⟶ T`, **`tau : E ⟶ (ψ ≫ T.hom)_* N_Z`** (`F = N_X`) with **`a_tau`**: `a ≫ tau = uC`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescK

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.SgUnit RamanujanPetersson.EtPBC

universe u

section Ret

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {F E : EtSh Λ X}
  (a : F ⟶ E) (b : E ⟶ unitSh Λ X) (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact)
  {T : X.Etale} (σ : E.obj.obj (op T))
  (hσ : (b.hom.app (op T)).hom σ = (constUnit (ModuleCat.of Λ Λ) T).hom 1)

include hσ in
theorem secT_b : secT σ ≫ wh b T = 𝟙 _ := by
  apply (homConstEquiv (ModuleCat.of Λ Λ) (unitSh Λ X) T).injective
  rw [homConstEquiv_apply, homConstEquiv_apply]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact (congrArg (b.hom.app (op T)).hom (secT_one σ)).trans hσ

end Ret

section Tau

end Tau

end RamanujanPetersson.EtPBC.DescK

end

end

-- ===== S4.Def_RP_EtPBC_A_DescK2 =====
section

/-!
# S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`

For `q : Y_s ⟶ P_s` and a short exact `0 → q_* N → E' → Λ → 0` on `P_s`:
* `Epp` (`E'' = q^* E' ⊔_{q^* q_* N} N`), `aPP`, `bPP`, **`shortExact_Epp`**: `0 → N → E'' → Λ → 0`;
* `kap0`, **`a_kap0`**: a map `τ : E'' ⟶ ψ'_* N_Z` extending `uC` gives `κ₀ : E' ⟶ (ψ' ≫ q)_* N_Z` extending `q_*(uC)`;
* `kapU_eq`, `push_uC_comp`, `rU_congr`: `q_*(uC) = rU`;
* **`T1`**: there is a finite etale surjective `T ⟶ Y_s` such that every `ψ : U_s ⟶ T` over `Y_s` yields `κ₀` with
  `a' ≫ κ₀ = rUs` (the input of `T3d.HypT`, up to the lifting `T2`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescK

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.SgUnit RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC

universe u

section RU

end RU

section Gen

end Gen

section Push

variable {Λ : Type u} [CommRing Λ] {Ys Ps : Scheme.{u}} (q : Ys ⟶ Ps) (N : ModuleCat.{u} Λ) {E' : EtSh Λ Ps}
  (a' : (push q Λ).obj (constSh Λ Ys N) ⟶ E') (b' : E' ⟶ unitSh Λ Ps) (w' : a' ≫ b' = 0)
  (hS' : (ShortComplex.mk a' b' w').ShortExact)

include hS' in
/-- **`0 → N → E'' → Λ → 0` is short exact.** -/
theorem shortExact_Epp : (ShortComplex.mk (aPP q N a') (bPP q N a' b' w') (aPP_bPP q N a' b' w')).ShortExact := by
  have hP := hS'.map_of_exact (pull q Λ)
  have hE : Epi ((pull q Λ).map b') := hP.epi_g
  have hMa : Mono (aPP q N a') := @mono_inr_of_mono _ _ _ _ _ _ _ _ hP.mono_f _
  have hEb : Epi (bPP q N a' b' w') := by
    have h1 : Epi ((pull q Λ).map b' ≫ (pullConst Λ q (ModuleCat.of Λ Λ)).hom) :=
      epi_comp' hE (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _))
    rw [← inl_bPP q N a' b' w'] at h1
    exact @epi_of_epi _ _ _ _ _ _ _ h1
  refine ShortComplex.ShortExact.mk' ?_ hMa hEb
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  obtain ⟨A₁, π₁, hπ₁, x₂, x₃, hx'⟩ := (IsPushout.of_hasPushout ((pull q Λ).map a')
    ((pullAdj q Λ).counit.app (constSh Λ Ys N))).hom_eq_add_up_to_refinements x
  have h0 : x₂ ≫ (pull q Λ).map b' ≫ (pullConst Λ q (ModuleCat.of Λ Λ)).hom = 0 := by
    have h1 : (π₁ ≫ x) ≫ bPP q N a' b' w' = 0 := by
      rw [Category.assoc]
      change π₁ ≫ x ≫ bPP q N a' b' w' = 0
      rw [show x ≫ bPP q N a' b' w' = 0 from hx, comp_zero]
    rw [hx', Preadditive.add_comp, Category.assoc, Category.assoc, inl_bPP,
      show pushout.inr _ _ ≫ bPP q N a' b' w' = 0 from aPP_bPP q N a' b' w', comp_zero, add_zero] at h1
    exact h1
  have h2 : x₂ ≫ (pull q Λ).map b' = 0 := by
    have h3 := congrArg (· ≫ (pullConst Λ q (ModuleCat.of Λ Λ)).inv) h0
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id, zero_comp] using h3
  obtain ⟨A₂, π₂, hπ₂, x₁, hx₁⟩ := hP.exact.exact_up_to_refinements x₂ h2
  obtain ⟨y, hy⟩ : ∃ y : A₂ ⟶ (pull q Λ).obj ((push q Λ).obj (constSh Λ Ys N)),
      π₂ ≫ x₂ = y ≫ (pull q Λ).map a' := ⟨x₁, hx₁⟩
  refine ⟨A₂, π₂ ≫ π₁, epi_comp' hπ₂ hπ₁, y ≫ (pullAdj q Λ).counit.app _ + π₂ ≫ x₃, ?_⟩
  change (π₂ ≫ π₁) ≫ x = (y ≫ (pullAdj q Λ).counit.app _ + π₂ ≫ x₃) ≫ pushout.inr _ _
  rw [Category.assoc, hx', Preadditive.comp_add, ← Category.assoc, hy, Category.assoc, pushout.condition,
    Preadditive.add_comp, Category.assoc, Category.assoc]

end Push

section T1

end T1

end RamanujanPetersson.EtPBC.DescK

end

end

-- ===== S4.Def_RP_EtPBC_A_EN =====
section

/-!
# S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point

* `exists_generic_open`: a closed nonempty `Z` in a noetherian scheme has a point `η` and an open `V₀ ∋ η` with
  `V₀ ∩ Z ⊆ closure {η}`;
* `gsum f τ c := Σ c_p · τ_p^* (f p.1) ∈ G(T)`; `germ_gsum` (its germ at `t` is `rel W G f x c`); `gsum_comp`;
* **`exists_good`**: an etale `T` with a point `t` over `x̄`, maps `τ_p` sending `t` to `p`, such that every relation
  `c` of the `f j` at `x̄` has `gsum f τ c = 0` on all of `T`, and `fpt t` is the only point of `T` over `x`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech GenAlg

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} (G : EtSh Λ P)

section Gsum

variable {x : P} {J : Type u} {W : J → P.Etale} (f : ∀ j, G.obj.obj (op (W j)))

/-- One refinement step: kill one relation on a neighbourhood. -/
theorem exists_refine {T : P.Etale} (t : (geomPtAt x).point.fiber.obj T) (τ : ∀ p : FibPts x W, T ⟶ W p.1)
    (hτ : ∀ p, (geomPtAt x).point.fiber.map (τ p) t = p.2) (c : FibPts x W →₀ Λ)
    (hc : GenAlg.rel W G f x c = 0) :
    ∃ (T' : P.Etale) (t' : (geomPtAt x).point.fiber.obj T') (ρ : T' ⟶ T),
      (geomPtAt x).point.fiber.map ρ t' = t ∧ gsum G f (fun p => ρ ≫ τ p) c = 0 := by
  obtain ⟨V, g, b, hb, hs⟩ := exists_nbhd_of_germ_eq_zero G x t (gsum G f τ c) ((germ_gsum G f hτ c).trans hc)
  exact ⟨V, b, g, hb, (gsum_comp G f g τ c).trans hs⟩

end Gsum

end RamanujanPetersson.EtPBC.GenGeo

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

/-- The generic point of `Y`. -/
def yg : Yn T ξ := g0 T ξ default

theorem range_g0 : Set.range (g0 T ξ) = {yg T ξ} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    rfl
  · rintro rfl
    exact ⟨_, rfl⟩

section Sec

variable {T} (W : P.Etale)

/-- **Every point of `X'` lies on a section `sx (τ b)`.** -/
theorem sx_cover (x : P) (t : (geomPtAt x).point.fiber.obj T) (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W))
    (hτ : ∀ b, (geomPtAt x).point.fiber.map (τ b) t = b) (e : Xp (fpt x t) W) :
    ∃ b, e ∈ Set.range (sx (fpt x t) W (τ b)) := by
  obtain ⟨ι, hι⟩ := exists_iota x t
  obtain ⟨l, hl, hle⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (pullback.fst (f0 T (fpt x t)) W.hom) ι e (Subsingleton.elim _ _)
  have hw : (l ≫ pullback.snd (f0 T (fpt x t)) W.hom) ≫ W.hom = (geomPtAt x).pt := by
    calc (l ≫ pullback.snd (f0 T (fpt x t)) W.hom) ≫ W.hom
        = l ≫ pullback.fst (f0 T (fpt x t)) W.hom ≫ f0 T (fpt x t) :=
          (Category.assoc _ _ _).trans (congrArg (l ≫ ·) pullback.condition.symm)
      _ = ι ≫ f0 T (fpt x t) := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f0 T (fpt x t)) hl)
      _ = ι ≫ T.left.fromSpecResidueField (fpt x t) ≫ T.hom := congrArg (ι ≫ ·) (f0_eq T (fpt x t))
      _ = fl x t ≫ T.hom := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ T.hom) hι)
      _ = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf t)
  let β : (geomPtAt x).point.fiber.obj W :=
    (Over.homMk (l ≫ pullback.snd (f0 T (fpt x t)) W.hom) hw :
      CategoryTheory.Over.mk (geomPtAt x).pt ⟶ (Scheme.Etale.forget P).obj W)
  have e1 : fl x t ≫ (τ β).left = l ≫ pullback.snd (f0 T (fpt x t)) W.hom :=
    congrArg (fun z => ((geomPtAt x).liftOf z).left) (hτ β)
  have hl2 : ι ≫ sx (fpt x t) W (τ β) = l := by
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (ι ≫ ·) (sx_fst _ W _)).trans
        ((Category.comp_id ι).trans hl.symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (ι ≫ ·) (sx_snd _ W _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (τ β).left) hι).trans e1)))
  refine ⟨β, ι default, ?_⟩
  rw [← Scheme.Hom.comp_apply, hl2, hle]

theorem sx_μx (u : T ⟶ W) : sx ξ W u ≫ μx ξ W = T.left.fromSpecResidueField ξ ≫ (sec u).left := by
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (sx ξ W u ≫ ·) (pullback.lift_fst _ _ _)).trans
      ((sx_snd ξ W u).trans ((congrArg (T.left.fromSpecResidueField ξ ≫ ·) (sec_fst u)).symm.trans
        (Category.assoc _ _ _).symm)))
  · exact (Category.assoc _ _ _).trans ((congrArg (sx ξ W u ≫ ·) (pullback.lift_snd _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ T.left.fromSpecResidueField ξ) (sx_fst ξ W u)).trans
        ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (T.left.fromSpecResidueField ξ ≫ ·) (sec_snd u)).symm.trans (Category.assoc _ _ _).symm))))))

end Sec

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_ESheet =====
section

/-!
# S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`

* `Nn ξ W` the relative normalization of `W` in `X' = Spec κ(ξ) ×_P W`; `Up ξ W := W ×_P Y`;
  `κp : X' ⟶ Up`, `ψn : Up ⟶ Nn` (inverse of `normalizationPullback`, `W` etale), `κp_ψn : κp ≫ ψn = toNormalization`;
* **`exists_sheets`**: a clopen partition `C b` of `Up` indexed by the fibre points `b` of `W` over `x̄`, with
  `κp (sx (τ b) pt) ∈ C b`;
* **`exists_fsec`**: a section of the constant sheaf with value `n i` on the `i`-th set of a finite clopen partition.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech

universe u

variable {P : Scheme.{u}} {T : P.Etale} (ξ : T.left) (W : P.Etale)

/-- `W ×_P Y`. -/
abbrev Up : Scheme.{u} := pullback W.hom (πn T ξ)

/-- `X' ⟶ W ×_P Y`. -/
def κp : Xp ξ W ⟶ Up ξ W :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ g0 T ξ)
    (pullback.condition.symm.trans ((congrArg (pullback.fst (f0 T ξ) W.hom ≫ ·) (g0_π T ξ).symm).trans
      (Category.assoc _ _ _).symm))

/-- `W ×_P Y ⟶ Nn` (normalization commutes with etale base change). -/
def ψn : Up ξ W ⟶ Nn ξ W :=
  haveI : Etale W.hom := W.prop
  (pullbackSymmetry W.hom (πn T ξ)).hom ≫ inv ((f0 T ξ).normalizationPullback W.hom)

end RamanujanPetersson.EtPBC.GenGeo

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

/-- **A point of `X'_V` gives a fibre point `β` of `V` with `xmap g e = sx (τ (g β)) pt`.** -/
theorem exists_beta (x : P) (t : (geomPtAt x).point.fiber.obj T) (V : P.Etale) (e : Xp (fpt x t) V) :
    ∃ β : (geomPtAt x).point.fiber.obj V, ∀ (W : P.Etale) (g : V ⟶ W)
      (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W)), (∀ b, (geomPtAt x).point.fiber.map (τ b) t = b) →
      xmap (fpt x t) g e = sx (fpt x t) W (τ ((geomPtAt x).point.fiber.map g β)) default := by
  obtain ⟨ι, hι⟩ := exists_iota x t
  obtain ⟨l, hl, hle⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    (pullback.fst (f0 T (fpt x t)) V.hom) ι e (Subsingleton.elim _ _)
  have hw : (l ≫ pullback.snd (f0 T (fpt x t)) V.hom) ≫ V.hom = (geomPtAt x).pt := by
    calc (l ≫ pullback.snd (f0 T (fpt x t)) V.hom) ≫ V.hom
        = l ≫ pullback.fst (f0 T (fpt x t)) V.hom ≫ f0 T (fpt x t) :=
          (Category.assoc _ _ _).trans (congrArg (l ≫ ·) pullback.condition.symm)
      _ = ι ≫ f0 T (fpt x t) := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f0 T (fpt x t)) hl)
      _ = ι ≫ T.left.fromSpecResidueField (fpt x t) ≫ T.hom := congrArg (ι ≫ ·) (f0_eq T (fpt x t))
      _ = fl x t ≫ T.hom := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ T.hom) hι)
      _ = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf t)
  let β : (geomPtAt x).point.fiber.obj V :=
    (Over.homMk (l ≫ pullback.snd (f0 T (fpt x t)) V.hom) hw :
      CategoryTheory.Over.mk (geomPtAt x).pt ⟶ (Scheme.Etale.forget P).obj V)
  refine ⟨β, fun W g τ hτ => ?_⟩
  have e1 : fl x t ≫ (τ ((geomPtAt x).point.fiber.map g β)).left =
      (l ≫ pullback.snd (f0 T (fpt x t)) V.hom) ≫ g.left :=
    congrArg (fun z => ((geomPtAt x).liftOf z).left) (hτ ((geomPtAt x).point.fiber.map g β))
  have hl2 : ι ≫ sx (fpt x t) W (τ ((geomPtAt x).point.fiber.map g β)) = l ≫ xmap (fpt x t) g := by
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (ι ≫ ·) (sx_fst _ W _)).trans
        ((Category.comp_id ι).trans (hl.symm.trans ((congrArg (l ≫ ·) (xmap_fst _ g)).symm.trans
          (Category.assoc _ _ _).symm))))
    · exact (Category.assoc _ _ _).trans ((congrArg (ι ≫ ·) (sx_snd _ W _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hι).trans (e1.trans
          ((Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (xmap_snd _ g)).symm.trans
            (Category.assoc _ _ _).symm))))))
  rw [← hle, ← Scheme.Hom.comp_apply, ← hl2, Scheme.Hom.comp_apply, Subsingleton.elim (ι default) default]

section Rel

end Rel

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_EG =====
section

/-!
# S4-EtPBC-A, M4(E), EG: relations of the sections `f_j` are relations of the generators near `ξ`

* `dT ξ : Spec κ(ξ) ⟶ T ×_P Y` (the diagonal point), `dT_map`: its images in `W ×_P Y` are the sheet points;
* `exists_fib_preimage`: a point of `T ×_P Y` over `fpt t'` is `fibToNbhd ⟨T, t'⟩ q` for some `q`;
* **`eg_rel`**: at a point `x = T.hom v` with `ξ ⤳ v`, every relation of the `f_j` is a relation of the `z_j`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech GenAlg

universe u

variable {P : Scheme.{u}} {T : P.Etale} (ξ : T.left)

/-- The diagonal point `Spec κ(ξ) ⟶ T ×_P Y`. -/
def dT : Spec (T.left.residueField ξ) ⟶ pullback T.hom (πn T ξ) :=
  pullback.lift (T.left.fromSpecResidueField ξ) (g0 T ξ) ((f0_eq T ξ).symm.trans (g0_π T ξ).symm)

/-- **Points of `T ×_P Y` over `fpt t'` come from the fibre `fib π x̄`.** -/
theorem exists_fib_preimage (x : P) (t' : (geomPtAt x).point.fiber.obj T) (zz : ↑(pullback T.hom (πn T ξ)))
    (hz : pullback.fst T.hom (πn T ξ) zz = fpt x t') :
    ∃ q : fib (πn T ξ) (geomPtAt x),
      fibToNbhd (πn T ξ) (geomPtAt x) ((geomPtAt x).point.fiber.elementsMk T t') q = zz := by
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst T.hom (πn T ξ))
    (g := fl x t') zz default hz
  let m : pullback (pullback.fst T.hom (πn T ξ)) (fl x t') ⟶ fib (πn T ξ) (geomPtAt x) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.snd T.hom (πn T ξ)) (pullback.snd _ _) (by
      calc (pullback.fst (pullback.fst T.hom (πn T ξ)) (fl x t') ≫ pullback.snd T.hom (πn T ξ)) ≫ πn T ξ
          = pullback.fst (pullback.fst T.hom (πn T ξ)) (fl x t') ≫ pullback.fst T.hom (πn T ξ) ≫ T.hom :=
            (Category.assoc _ _ _).trans (congrArg _ pullback.condition.symm)
        _ = (pullback.snd (pullback.fst T.hom (πn T ξ)) (fl x t') ≫ fl x t') ≫ T.hom :=
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ T.hom) pullback.condition)
        _ = pullback.snd (pullback.fst T.hom (πn T ξ)) (fl x t') ≫ (geomPtAt x).pt :=
            (Category.assoc _ _ _).trans (congrArg _ (Over.w ((geomPtAt x).liftOf t'))))
  have hm : m ≫ fibToNbhd (πn T ξ) (geomPtAt x) ((geomPtAt x).point.fiber.elementsMk T t') =
      pullback.fst _ _ := by
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (fibToNbhd_fst _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_snd _ _ _)).trans
          pullback.condition.symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (m ≫ ·) (fibToNbhd_snd _ _ _)).trans
        (pullback.lift_fst _ _ _))
  exact ⟨m w, (Scheme.Hom.comp_apply _ _ w).symm.trans ((congrArg (fun φ => φ.base w) hm).trans hw1)⟩

section Rel

end Rel

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_O2MVo =====
section

/-!
# S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`

* `toTop W : W ⟶ etId P`, `toTop_ext`; the fibre of `etId P` is a singleton (`topPt`, `fpt_topPt`);
* `opEt U := opn (etId P) U`: its fibre over `x̄` is subsingleton, nonempty iff `x ∈ U` (`opPt`, `mem_of_fib_opEt`);
* `prd_fib_ext`; `prW_bijective` (`x ∈ U`), `prT_bijective` (`x ∉ U`) for `prd W (opEt U)`;
* **`mvOpen_shortExact`**: `0 → Λ[W ×_P U] → Λ[W] ⊞ Λ[U] → Λ[P] → 0` is short exact when every `x ∉ U` has exactly
  one fibre point of `W` over `x̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo

universe u

variable {P : Scheme.{u}}

theorem prW_bijective (W T : P.Etale) (x : P) [Subsingleton ((geomPtAt x).point.fiber.obj T)]
    (t : (geomPtAt x).point.fiber.obj T) : Function.Bijective ((geomPtAt x).point.fiber.map (prW W T)) := by
  refine ⟨fun c c' h => prd_fib_ext x h (Subsingleton.elim _ _), fun a => ⟨pair x a t, ?_⟩⟩
  exact fiber_ext _ (pair_fst x a t)

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

theorem copP₁_bij (x : P) (hx : x ∈ U₀) :
    Function.Bijective ((geomPtAt x).point.fiber.map (copP₁ S U₀)) := by
  obtain ⟨t⟩ := nonempty_fib_opEt U₀ x hx
  have hb : ∀ k, Function.Bijective ((geomPtAt x).point.fiber.map (prW (S k) (opEt U₀))) :=
    fun k => prW_bijective (S k) (opEt U₀) x t
  have hc : ∀ k c, (geomPtAt x).point.fiber.map (copP₁ S U₀)
      ((geomPtAt x).point.fiber.map (copι (fun k => prd (S k) (opEt U₀)) k) c) =
      (geomPtAt x).point.fiber.map (copι S k) ((geomPtAt x).point.fiber.map (prW (S k) (opEt U₀)) c) := by
    intro k c
    rw [← FunctorToTypes.map_comp_apply, copι_copP₁, FunctorToTypes.map_comp_apply]
  refine ⟨fun a a' h => ?_, fun a => ?_⟩
  · obtain ⟨k, c, rfl⟩ := fib_cop_surj _ x a
    obtain ⟨k', c', rfl⟩ := fib_cop_surj _ x a'
    rw [hc, hc] at h
    obtain rfl := fib_cop_idx S x _ _ h
    rw [(hb k).1 (fib_cop_inj S x k h)]
  · obtain ⟨k, b, rfl⟩ := fib_cop_surj S x a
    obtain ⟨c, rfl⟩ := (hb k).2 b
    exact ⟨_, hc k c⟩

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

variable {D₁ D : P.Etale} (d : D₁ ⟶ D) (X : P.Etale)

theorem prdMap_prW : prdMap d X ≫ prW D X = prW D₁ X ≫ d :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

end Prd

section Shrink

end Shrink

section Opn

end Opn

section Res

end Res

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree

* `shObj s`, `shι s`: a map `s : N ⟶ W` of etale `P`-schemes gives a sheet `N ⟶ N ×_P W` over `W`.
* `sheet_cover`: sheets that biject onto every geometric fibre cover `N ×_P W`; `sheet_sep`: distinct sheets
  do not meet; `shι_cancel`.
* **`push_epi`**: if `W` is quasi-compact separated etale over `P` with `n` points in every geometric fibre, then
  `push W.hom` preserves epimorphisms (stalk lifts on a splitting neighbourhood, glued over the sheets), and
  **`push_preservesFiniteColimits_of_deg`**.
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

section Sheet

variable {W N : P.Etale}

/-- A point of `N ×_P W` on the sheet through its fibre point. -/
theorem sheet_pt {ι : Type*} (σ : ι → (N ⟶ W))
    (hbij : ∀ (y : P) (v : (geomPtAt y).point.fiber.obj N),
      Function.Bijective fun p => (geomPtAt y).point.fiber.map (σ p) v) (u : (prd N W).left) :
    ∃ p, ∃ v : N.left, (shP (σ p)).left v = u := by
  obtain ⟨c, hc⟩ := exists_fib_over (prd N W) u
  obtain ⟨p, hp⟩ := (hbij _ ((geomPtAt ((prd N W).hom u)).point.fiber.map (prW N W) c)).2
    ((geomPtAt ((prd N W).hom u)).point.fiber.map (prT N W) c)
  have hc' : (geomPtAt ((prd N W).hom u)).point.fiber.map (shP (σ p))
      ((geomPtAt ((prd N W).hom u)).point.fiber.map (prW N W) c) = c := by
    refine prd_fib_ext ((prd N W).hom u) ?_ ?_
    · rw [← Functor.map_comp_apply, shP_prW, Functor.map_id_apply]
    · rw [← Functor.map_comp_apply, shP_prT]
      exact hp
  exact ⟨p, _, (fib_left_map (shP (σ p)) _ _).symm.trans ((congrArg (fpt _) hc').trans hc)⟩

/-- Sheets `c ≫ e ≫ τ p` through sheets `τ p` that are pairwise distinct at every geometric point. -/
theorem sep_of {T L M₀ : P.Etale} {ι : Type*} (τ : ι → (T ⟶ W))
    (hinj : ∀ (y : P) (v : (geomPtAt y).point.fiber.obj T) (p q : ι),
      (geomPtAt y).point.fiber.map (τ p) v = (geomPtAt y).point.fiber.map (τ q) v → p = q)
    (c : L ⟶ M₀) (e : M₀ ⟶ T) (S : Scheme.{u}) (g : S ⟶ L.left) (p q : ι)
    (hg : g ≫ (c ≫ e ≫ τ p).left = g ≫ (c ≫ e ≫ τ q).left) (s : S) : p = q := by
  have h3 : (g ≫ c.left ≫ e.left) ≫ (τ p).left = (g ≫ c.left ≫ e.left) ≫ (τ q).left := by
    simp only [Category.assoc]
    exact hg
  have hm := mem_agr_of_comp_eq (τ p) (τ q) _ h3 s
  obtain ⟨v, hv⟩ := exists_fib_over T ((g ≫ c.left ≫ e.left) s)
  rw [← hv] at hm
  exact hinj _ v p q ((mem_agr_iff (τ p) (τ q) _ v).1 hm)

end Sheet

section Lift

end Lift

end RamanujanPetersson.EtPBC.EtShap

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

variable (W : P.Etale)

theorem agr_iff (x : P) {T N : P.Etale} (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W))
    (t : (geomPtAt x).point.fiber.obj T) (hτ : ∀ p, (geomPtAt x).point.fiber.map (τ p) t = p)
    (g : N ⟶ T) (b : (geomPtAt x).point.fiber.obj N) (hb : (geomPtAt x).point.fiber.map g b = t)
    (a q : (geomPtAt x).point.fiber.obj W) : fpt x b ∈ agr (g ≫ τ a) (g ≫ τ q) ↔ a = q := by
  rw [mem_agr_iff, Functor.map_comp_apply, Functor.map_comp_apply, hb, hτ, hτ]

end Dg

section Iso

end Iso

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPi1_FunA =====
section

/-!
# S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change

`A → A'`, `K → K'` compatible (`A → K → K'`, `A → A' → K'`), `ι : K̄ →ₐ[K] K̄'` any `K`-embedding.

* `bcField f = K'(roots of f)` in `K̄'` (splitting field, finite, Galois when `f` is separable);
* `rootSet_bc`: the roots of `f` in `K̄'` are the `ι`-images of its roots in `K̄`;
* `icMap`: `integralClosure A L → integralClosure A' L'` induced by `ι`;
* `bcField_unram`: for `L ∈ unramSet A K` the splitting field of `L` over `K'` has trivial inertia over `A'`
  (an inertia element restricts, via `ι`, to an inertia element of `Gal(L/K)`, which is trivial);
* `map_mem_maxUnram`: `ι (K_U(A)) ⊆ K_U(A')`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace EtPi1

open GalCover Lefschetz Polynomial

noncomputable section

section FunA

variable {A K A' K' : Type} [CommRing A] [Field K] [Algebra A K]
  [CommRing A'] [Field K'] [Algebra A' K'] [Algebra K K'] [Algebra A A'] [Algebra A K']
  [IsScalarTower A K K'] [IsScalarTower A A' K']
  (ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure K')

instance bcField_finiteDimensional (f : K[X]) : FiniteDimensional K' (bcField (K' := K') f) := by
  let g : K'[X] := f.map (algebraMap K K')
  haveI : g.IsSplittingField K' (bcField (K' := K') f) := bcField_isSplittingField f
  exact IsSplittingField.finiteDimensional _ g

theorem bcField_isGalois {f : K[X]} (hf : f.Separable) : IsGalois K' (bcField (K' := K') f) := by
  have hg : (f.map (algebraMap K K')).Separable := hf.map
  exact IsGalois.of_separable_splitting_field hg

end FunA

end

end EtPi1
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtPBC_A_O2ZarCh =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step

GLOB/REL PLAN v1 (file LocU+ZarCh). `c : A1 k ⟶ P` an open immersion, `D = chEt c φ` (`φ : k[X] ⟶ B`).
* `subsingleton_fib_toDF`, `nonempty_fib_toDF`, `range_toDF`: the one-point chart conditions survive a shrink
  `D_f ⟶ D` when `f` does not vanish at the special point;
* `isLocalization_away_toDF`, `comap_injective_toDF`: O2Pb (Zar) for `toDF`;
* `etale_chEt_locF`, `isOpenImmersion_chEt_locF`: `D_g := chEt c (k[X] ⟶ k[X]_g)` is an open of `P`;
  `opnDg c g := c(D(g))` its range;
* `liftDg`, `toDg`: `D_f ⟶ D_g` over `P` when `φ g` is a unit in `B_f`;
* `secD`, `secD_prT`: the section `opEt U ⟶ D ×_P U` for an open immersion `D` whose range contains `U`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtDeg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtPBC.EtShap

universe u

section Shrink

end Shrink

section Dg

variable {k : Type u} [Field k] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]

variable {B : CommRingCat.{u}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (f : B) (g : k[X])
  (hg : IsUnit (algebraMap B (Localization.Away f) (φ.hom g)))

/-- `D_f ⟶ D_g` over `P`. -/
def toDg : chEt c (φ ≫ locF f) ⟶ chEt c (locF (B := CommRingCat.of k[X]) g) :=
  MorphismProperty.Over.homMk (Spec.map (liftDg φ f g hg)) (by
    show Spec.map (liftDg φ f g hg) ≫ Spec.map (locF (B := CommRingCat.of k[X]) g) ≫ c = Spec.map (φ ≫ locF f) ≫ c
    rw [← Category.assoc, ← Spec.map_comp, locF_liftDg])

end Dg

section Sec

end Sec

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP2 =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)

GLOB/REL PLAN v1 stage S4 data: for `G = g₀ c₀' t` (an opaque variable with `hGdef`), the `D_G` and
`D₂ := D₁_{c₀'}` instances (`isAffine_prdG`, `isAffine_prdUo`, Km6 instances), the `D₂` fibre data (ZarCh) and `hD₂`,
`hR₂₁`, then `pp_core` (O2PP1).
* helpers: `dvd_of_Gdef`, `tdvd_of_Gdef`, `ne_zero_of_Gdef`, `hpt_of_ne_zero`, `isUnit_locF_self`, `hzU_of`,
  `hUo_of_range`, `mem_opnDg_or`, `mem_opnDg_prd'`, `nontrivial_of_fpt`;
* **`pp_G`** (DEF): the target class at `D₁` lies in `Gr`, from the S2-S3 output and `c₀'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Helpers

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {a : k} {Uo Uz : P.Opens}

/-- `hUo` of `isAffine_prdUo` for a chart over `U₀ ∪ {c(a)}`. -/
theorem hUo_of_range {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
    (hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uo ∨ (chEt c φ).hom v = c (A1pt k a))
    (hzU : c (A1pt k a) ∉ Uo) (u : Spec B) :
    (chEt c φ).hom u ∈ Uo ↔ φ.hom (X - C a) ∉ u.asIdeal := by
  have hcu : (chEt c φ).hom u = c (Spec.map φ u) := rfl
  constructor
  · intro hu ht
    have h0 : X - C a ∈ (Spec.map φ u).asIdeal := ht
    have h1 : Spec.map φ u = A1pt k a := eq_A1pt_of_mem h0
    rw [hcu, h1] at hu
    exact hzU hu
  · intro ht
    rcases hDr u with h1 | h1
    · exact h1
    · exfalso
      have h2 : Spec.map φ u = A1pt k a := c.isOpenEmbedding.injective (hcu.symm.trans h1)
      have h3 : X - C a ∈ (Spec.map φ u).asIdeal := by
        rw [h2]
        exact Ideal.mem_span_singleton_self _
      exact ht h3

end Helpers

section PPG

end PPG

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L5b =====
section

/-!
# S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma

Generic setting: `i : S ⟶ P` a closed immersion with a retraction `g` (`i ≫ g = 𝟙`), `W : P.Etale`.
* `Vs = W ×_P S` (`etPull i`), `Zs = Vs ×_S P` (`etPull g`), `Es = W ×_P Zs` (`prd`);
* `jz : Vs ⟶ Zs` (`v ↦ (v, i v)`), `τz : Vs ⟶ Es` (`v ↦ (w v, jz v)`), `δz : Vs ⟶ Es ×_P S` (an open immersion:
  an etale section of `rz`, `δz_rz`);
* `Og Q = (κ '' (range δz)ᶜ)ᶜ ∩ Es⁻¹ Q` (`κ = pullback.fst _ i`, a closed immersion), `Dg = opn Es Og`,
  `wg : Dg ⟶ Zs`;
* **`fl_graph`**: at `x̄` with `x̄ = (x̄ ≫ g) ≫ i`, a point `d` of `Es` off `κ '' (range δz)ᶜ` is `τz` of its `Zs`-part;
* **`graph_unique`**, **`graph_exists`** (`x ∈ Q`): `wg` is bijective on fibres over such `x̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo

universe u

section Graph

variable {P S : Scheme.{u}} (i : S ⟶ P) (g : P ⟶ S) (W : P.Etale)

variable {i g} (hig : i ≫ g = 𝟙 S)

theorem δz_fst : (δz W hig).left ≫ pullback.fst (Es i g W).hom i = τz W hig := pullback.lift_fst _ _ _

theorem δz_snd : (δz W hig).left ≫ pullback.snd (Es i g W).hom i = (Vs i W).hom := pullback.lift_snd _ _ _

variable (i g) in
/-- The retraction `Es ×_P S ⟶ Vs`. -/
def rz : (etPull i).obj (Es i g W) ⟶ Vs i W :=
  MorphismProperty.Over.homMk (pullback.lift (pullback.fst (Es i g W).hom i ≫ (prW W (Zs i g W)).left)
    (pullback.snd (Es i g W).hom i)
    ((Category.assoc _ _ _).trans ((whisker_eq _ (MorphismProperty.Over.w (prW W (Zs i g W)))).trans
      pullback.condition)))
    (pullback.lift_snd _ _ _)

variable [IsClosedImmersion i]

/-- The bad closed set `κ '' (range δz)ᶜ`. -/
abbrev Bz : Set (Es i g W).left := pullback.fst (Es i g W).hom i '' (Set.range (δz W hig).left)ᶜ

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gen1 =====
section

/-!
# S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`

* `ptCls_comp`: `PtCls c R x → PtCls c T (x ∘ Λ[r])`; `compSub r G` (`x ↦ x ∘ Λ[r]` pulled back subgroup).
* `isClosed_of_isLoc`: an `IsLoc` point is closed.
* chart facts for any open immersion `c : A¹ ⟶ P¹`: `chart_ne_genPt`, `chart_hclA`, `chart_hGal`, `chart_hclc`,
  `A1_hpt`, `exists_A1pt_of_mem_range`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtCompact.PushStk RamanujanPetersson.EtCompact.PushBC

section PtCompSub

end PtCompSub

section CompSub

variable {Λ : Type} [CommRing Λ] {P : Scheme.{0}}

/-- The subgroup of classes `x` with `x ∘ Λ[r] ∈ G`. -/
def compSub {R T : P.Etale} (r : R ⟶ T) (G : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ T) 2)) :
    AddSubgroup (Ext.{0} (freeSh Λ (etId P)) (freeSh Λ R) 2) :=
  G.comap (AddMonoidHom.mk' (fun x => x.comp (Ext.mk₀ (freeMap Λ r)) (add_zero 2))
    (fun a b => Ext.add_comp a b _ _))

end CompSub

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtMV

end

end


