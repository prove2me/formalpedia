-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_050
-- name    : RPLib_FX_EtPBC_050
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:12:58.171359+00:00
-- url     : https://prove2.me/theorems/31027105-1deb-5eb3-8b40-a065449234bb
-- title:
--   Proper base change for the projective line, library file 050
-- statement:
--   File 050 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
--   * `S4.Def_RP_EtPBC_A_CovG1`: S4-EtPBC-A, R4-T2 (A2a): sections of `O(d)` of a two-chart cover and their lifting along transitions
--   * `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
--   * `S4.Def_RP_EtPBC_A_Z1Two`: S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_LocFlat`: S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)
--   * `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
--   * `S4.Def_RP_EtPBC_A_Z4Glue`: S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`
--   * `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
--   * `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_FBInj`: S4-EtPBC-A, M2 F3: base change on germs of a constant sheaf (degree `0`)
--   * `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
--   * `S4.Def_RP_EtPBC_A_Z4FibC`: S4-EtPBC-A, (Z) geometric layer 13 (G-f, part 3): the `π₀` extension theorem
--   * `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
--   * `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
--   * `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
--   * `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
--   * `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
--   * `S4.Def_RP_EtPBC_A_EPsiRel`: S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres
--   * `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
--   * `S4.Def_RP_EtPBC_A_O2MV`: S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves
--   * `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
--   * `S4.Def_RP_EtPBC_A_O2E2`: S4-EtPBC-A, O2 C-plan S4b (ring level): a good basic open of an etale `k[X]`-algebra at a point over `X = a`
--   * `S4.Def_RP_EtPBC_A_O2Km5`: S4-EtPBC-A, O2 M6 (O2Km5): global sections of an affine scheme etale over `Spec A`
--   * `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
--   * `S4.Def_RP_EtPBC_A_O2E8`: S4-EtPBC-A, O2 C-plan S4d2 (Ext level): purity for `Ext¹(Λ[W₁], Λ_P)`, and changing `Uo` to `Uz`
--   * `S4.Def_RP_EtPBC_A_O2Km6`: S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`
--   * `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
--   * `S4.Def_RP_EtPBC_A_O2LocU`: S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class
--   * `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
--   * `S4.Def_RP_EtPBC_A_O2PP4b`: S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_042

/-!
# Proper base change for the projective line, library file 050

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
* `S4.Def_RP_EtPBC_A_CovG1`: S4-EtPBC-A, R4-T2 (A2a): sections of `O(d)` of a two-chart cover and their lifting along transitions
* `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
* `S4.Def_RP_EtPBC_A_Z1Two`: S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module
* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_LocFlat`: S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)
* `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
* `S4.Def_RP_EtPBC_A_Z4Glue`: S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`
* `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
* `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_FBInj`: S4-EtPBC-A, M2 F3: base change on germs of a constant sheaf (degree `0`)
* `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
* `S4.Def_RP_EtPBC_A_Z4FibC`: S4-EtPBC-A, (Z) geometric layer 13 (G-f, part 3): the `π₀` extension theorem
* `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
* `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
* `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
* `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
* `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
* `S4.Def_RP_EtPBC_A_EPsiRel`: S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres
* `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
* `S4.Def_RP_EtPBC_A_O2MV`: S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves
* `S4.Def_RP_EtPBC_A_O2L1`: S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes
* `S4.Def_RP_EtPBC_A_O2E2`: S4-EtPBC-A, O2 C-plan S4b (ring level): a good basic open of an etale `k[X]`-algebra at a point over `X = a`
* `S4.Def_RP_EtPBC_A_O2Km5`: S4-EtPBC-A, O2 M6 (O2Km5): global sections of an affine scheme etale over `Spec A`
* `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
* `S4.Def_RP_EtPBC_A_O2E8`: S4-EtPBC-A, O2 C-plan S4d2 (Ext level): purity for `Ext¹(Λ[W₁], Λ_P)`, and changing `Uo` to `Uz`
* `S4.Def_RP_EtPBC_A_O2Km6`: S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`
* `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
* `S4.Def_RP_EtPBC_A_O2LocU`: S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class
* `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
* `S4.Def_RP_EtPBC_A_O2PP4b`: S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer
-/

set_option autoImplicit false

set_option linter.defProp false

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

section EtPull

end EtPull

theorem unitSec_map {j j' : Nbhd s} (a : j' ⟶ j) :
    (((pull (fibι g s) Λ).map ((nbhdSys Λ g s).map a)).hom.app
        (op ((etPull (fibι g s)).obj ((etPull g).obj j'.1)))).hom (unitSec Λ g s j') =
      ((fibFree Λ g s j).obj.map ((etPull (fibι g s)).map ((etPull g).map a.1)).op).hom
        (unitSec Λ g s j) := by
  have h1 := freeEquiv_comp Λ ((etPull g).obj j'.1)
    ((pullAdj (fibι g s) Λ).unit.app ((nbhdSys Λ g s).obj j'))
    ((push (fibι g s) Λ).map ((pull (fibι g s) Λ).map ((nbhdSys Λ g s).map a)))
  have h2 := freeEquiv_freeMap Λ ((etPull g).map a.1) ((push (fibι g s) Λ).obj (fibFree Λ g s j))
    ((pullAdj (fibι g s) Λ).unit.app ((nbhdSys Λ g s).obj j))
  have h3 := (pullAdj (fibι g s) Λ).unit_naturality ((nbhdSys Λ g s).map a)
  exact h1.symm.trans ((congrArg _ h3).trans h2)

/-- **Compatibility of the base change units with restriction.** -/
theorem bcUnit_comp {j j' : Nbhd s} (a : j' ⟶ j) :
    bcUnit Λ g s j' ≫ (pull (fibι g s) Λ).map ((nbhdSys Λ g s).map a) = bcUnit Λ g s j := by
  rw [bcUnit, bcUnit, ofSec_comp]
  congr 1
  have hn := congrArg (fun f => f.hom (unitSec Λ g s j'))
    (((pull (fibι g s) Λ).map ((nbhdSys Λ g s).map a)).hom.naturality (nbhdSec g s j').op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  rw [fibSec, hn, unitSec_map, fibSec, ← nbhdSec_comp g s a, op_comp, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_CovG1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2a): sections of `O(d)` of a two-chart cover and their lifting along transitions

* `TwoCov.u` (the coordinate `t` on the overlap), **`TwoCov.sec C d`**: the pairs `(x₀, x₁)` with
  `ψ₀ x₀ = u^d ψ₁ x₁` (global sections of `O(d)`);
* `TwoCovHom.u_map`, **`TwoCovHom.secMap`**: a transition maps sections to sections;
* **`TwoCovHom.secMap_surj`**: if every element of `ker ρ` is `ψ₀ k₀ - u^d ψ₁ k₁` with `kᵢ ∈ ker ρᵢ`, sections lift;
* **`TwoCovHom.hker_of_gens`**: that hypothesis from generators `ψ₀ (g j)` of `ker ρ` whose multiples split.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Sec

end Sec

section Hom

variable {B₀ B₁ N b₀ b₁ n : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing b₀] [CommRing b₁]
  [CommRing n] {φ₀ : B₀ →+* N} {φ₁ : B₁ →+* N} {t₀ : B₀} {t₁ : B₁} {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n} {τ₀ : b₀}
  {τ₁ : b₁} {π₀ : B₀ →+* b₀} {π₁ : B₁ →+* b₁} {π : N →+* n} {C' : TwoCov φ₀ φ₁ t₀ t₁}
  {C : TwoCov φb₀ φb₁ τ₀ τ₁} (H : TwoCovHom π₀ π₁ π C' C)

theorem TwoCovHom.secMap_coe (hτ₀ : π₀ t₀ = τ₀) (d : ℕ) (x : C'.sec d) :
    ((H.secMap hτ₀ d x : C.sec d) : C.E₀ × C.E₁) = (H.ρ₀ x.1.1, H.ρ₁ x.1.2) :=
  rfl

/-- **Sections lift** when `H¹` of the kernel vanishes. -/
theorem TwoCovHom.secMap_surj (hτ₀ : π₀ t₀ = τ₀) (d : ℕ)
    (hker : ∀ δ ∈ RingHom.ker H.ρ, ∃ k₀ ∈ RingHom.ker H.ρ₀, ∃ k₁ ∈ RingHom.ker H.ρ₁,
      δ = C'.ψ₀ k₀ - C'.u ^ d * C'.ψ₁ k₁) :
    Function.Surjective (H.secMap hτ₀ d) := by
  rintro ⟨⟨x₀, x₁⟩, hx⟩
  obtain ⟨y₀, rfl⟩ := H.s₀ x₀
  obtain ⟨y₁, rfl⟩ := H.s₁ x₁
  have e₀ : H.ρ (C'.ψ₀ y₀) = C.ψ₀ (H.ρ₀ y₀) := RingHom.congr_fun H.d₀ _
  have e₁ : H.ρ (C'.ψ₁ y₁) = C.ψ₁ (H.ρ₁ y₁) := RingHom.congr_fun H.d₁ _
  have hx' : C.ψ₀ (H.ρ₀ y₀) = C.u ^ d * C.ψ₁ (H.ρ₁ y₁) := hx
  have hδ : C'.ψ₀ y₀ - C'.u ^ d * C'.ψ₁ y₁ ∈ RingHom.ker H.ρ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_pow, H.u_map hτ₀, e₀, e₁, hx', sub_self]
  obtain ⟨k₀, hk₀, k₁, hk₁, he⟩ := hker _ hδ
  refine ⟨⟨(y₀ - k₀, y₁ - k₁), ?_⟩, ?_⟩
  · rw [TwoCov.mem_sec, map_sub, map_sub, mul_sub]
    linear_combination he
  · apply Subtype.ext
    rw [TwoCovHom.secMap_coe]
    simp only [map_sub, RingHom.mem_ker.1 hk₀, RingHom.mem_ker.1 hk₁, sub_zero]

end Hom

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovG3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`

Charts `Bᵢ` with ring maps `ιBᵢ : R → Bᵢ` (agreeing in `N`) and `Jᵢ = p Bᵢ`, `JN = p N`:
* level maps **`lι₀`**, **`lι₁`** (`R → Eᵢ` at level `k`), **`lI`** (the ideal `p E`), `lι_compat`, `lhv`;
* along a transition: `lρι₀`, **`ker_ρ`** (`ker ρ = p^(k+1) E'`), `lq₀`, `lq₁`, `lqI` (`p^(k+1) · p E' = 0`), `lI_comap`;
* **`good_tower`**: generators with the same exponents at every level of `tower`;
* **`secMap_surj_tower`**: one `d₀` such that `secMap (towerHom k) d` is surjective for all `k` and `d ≥ d₀`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R)

variable {k : ℕ} {C' : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ (k + 1)} {C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k}
  (H : TwoCovHom (down J₀ k) (down J₁ k) (down JN k) C' C)

theorem lI_comap (hJ₀ : J₀ = p.map ιB₀) : (lI ιB₀ p C).comap H.ρ ≤ lI ιB₀ p C' := by
  have hmap : lI ιB₀ p C = (lI ιB₀ p C').map H.ρ := by
    simp only [lI]
    rw [Ideal.map_map, ← RingHom.comp_assoc, H.d₀, RingHom.comp_assoc, lρι₀ ιB₀ H]
  rw [hmap, Ideal.comap_map_of_surjective _ H.s, sup_le_iff]
  refine ⟨le_rfl, ?_⟩
  change RingHom.ker H.ρ ≤ _
  rw [ker_ρ ιB₀ p H hJ₀]
  exact Ideal.map_mono (Ideal.pow_le_self (Nat.succ_ne_zero k))

end Lv

section Tower

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z1Two =====
section

/-!
# S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module

Algebraic form of "`H⁰(P¹_A, 𝓕)` is finite over `A` for a coherent `𝓕`" (`A` noetherian), with `𝓕` given by
a finite `A[t]`-module `M₀`, a finite `A[s]`-module `M₁` (both written as `A[X]`-modules) and `A`-linear maps
`φ₀ : M₀ → N`, `φ₁ : M₁ → N` into the module over the overlap, where `X` acts on `N` as `t` and
`t • φ₁ (s • m) = φ₁ m`.

* `xTors M`: the `X`-power torsion; **`xTors_fg`**: it is finite over `A` for `M` finite over `A[X]`.
* `pow_smul_iter`, **`exists_refl`**: `X^D • φ₁ (c • w) = q • φ₁ w` with `deg q ≤ D` when `deg c ≤ D`.
* `twoChart φ₀ φ₁ := {(a, b) | φ₀ a = φ₁ b}` and **`twoChart_fg`**: it is finite over `A`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Z1

universe u v w w'

variable {A : Type u} [CommRing A]

section TwoChart

variable {M₁ : Type w} {N : Type w'} [AddCommGroup M₁] [Module A[X] M₁] [Module A M₁] [IsScalarTower A A[X] M₁]
  [AddCommGroup N] [Module A[X] N] [Module A N] [IsScalarTower A A[X] N]

/-- **`H⁰` over the two charts is finite over `A`** (`A` noetherian, `M₀`, `M₁` finite over `A[X]`). -/
theorem twoChart_fg [IsNoetherianRing A] {M₀ : Type v} [AddCommGroup M₀] [Module A[X] M₀] [Module A M₀]
    [IsScalarTower A A[X] M₀] [Module.Finite A[X] M₀] [Module.Finite A[X] M₁]
    (φ₀ : M₀ →ₗ[A[X]] N) (φ₁ : M₁ →ₗ[A] N) (h₁ : ∀ m, (X : A[X]) • φ₁ ((X : A[X]) • m) = φ₁ m)
    (hgen : ∀ m : M₁, ∃ (d : ℕ) (a : M₀), φ₀ a = (X ^ d : A[X]) • φ₁ m)
    (hk₀ : ∀ a, φ₀ a = 0 → a ∈ xTors (A := A) M₀) (hk₁ : ∀ b, φ₁ b = 0 → b ∈ xTors (A := A) M₁) :
    (twoChart φ₀ φ₁).FG := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A[X]) (M := M₀)
  obtain ⟨m, w, hw⟩ := Module.Finite.exists_fin (R := A[X]) (M := M₁)
  choose d a' ha' using fun j => hgen (w j)
  let v : Fin n ⊕ Fin m → M₀ := Sum.elim s fun j => (X ^ (Finset.univ.sup d - d j) : A[X]) • a' j
  have hvl : ∀ i, v (Sum.inl i) = s i := fun _ => rfl
  have hv : ∀ j, φ₀ (v (Sum.inr j)) = (X ^ Finset.univ.sup d : A[X]) • φ₁ (w j) := by
    intro j
    show φ₀ ((X ^ (Finset.univ.sup d - d j) : A[X]) • a' j) = _
    rw [map_smul, ha', smul_smul, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := d) (Finset.mem_univ j))]
  obtain ⟨M, hMfg, hM⟩ := exists_fg_of_twoChart (A := A) (φ₀ ∘ₗ Fintype.linearCombination A[X] v)
  refine Submodule.fg_of_fg_map_of_fg_inf_ker ((φ₀.restrictScalars A) ∘ₗ LinearMap.fst A M₀ M₁) ?_ ?_
  · refine hMfg.of_le ?_
    rintro _ ⟨⟨x₀, x₁⟩, hx, rfl⟩
    have hx' : φ₀ x₀ = φ₁ x₁ := (mem_twoChart φ₀ φ₁ _).1 hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A[X]).1 (hs ▸ Submodule.mem_top (x := x₀))
    obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun A[X]).1 (hw ▸ Submodule.mem_top (x := x₁))
    choose q hq hq' using fun j => exists_refl φ₁ h₁ (Finset.univ.sup fun j => (c' j).natDegree) (c' j)
      (Finset.le_sup (f := fun j => (c' j).natDegree) (Finset.mem_univ j)) (w j)
    have hπ0 : (φ₀ ∘ₗ Fintype.linearCombination A[X] v) (Sum.elim c 0) = φ₀ x₀ := by
      rw [LinearMap.comp_apply, Fintype.linearCombination_apply, Fintype.sum_sum_type, ← hc]
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero, hvl]
    have key := hM (Sum.elim c 0) ((Finset.univ.sup fun j => (c' j).natDegree) + Finset.univ.sup d)
      (Sum.elim 0 q) ?_ ?_
    · rw [hπ0] at key
      exact key
    · intro i
      cases i with
      | inl i => simp
      | inr j => exact (hq j).trans (Nat.le_add_right _ _)
    · rw [hπ0, hx', ← hc', map_sum, Finset.smul_sum, LinearMap.comp_apply, Fintype.linearCombination_apply,
        Fintype.sum_sum_type, map_add, map_sum, map_sum]
      simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, map_zero, Finset.sum_const_zero,
        zero_add, map_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hv j, add_comm, pow_add, mul_smul, hq' j, smul_comm]
  · refine Submodule.FG.of_le (((xTors_fg M₀).prod (xTors_fg M₁))) ?_
    rintro ⟨x₀, x₁⟩ ⟨hx, hk⟩
    have h0 : φ₀ x₀ = 0 := hk
    have h1 : φ₁ x₁ = 0 := ((mem_twoChart φ₀ φ₁ _).1 hx).symm.trans h0
    exact ⟨hk₀ x₀ h0, hk₁ x₁ h1⟩

end TwoChart

end RamanujanPetersson.EtPBC.Z1

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts

* **`hE`** `⊆ L₀ × L₁` (fractions `x / T₁ᵃ T₀ᵇ`, `x ∈ Gam (a + b)`); **`hψ₀ : hE₀ →+* hE`**, **`hψ₁ : hE₁ →+* hE`**;
* `ρ₀_fB`, `ρ₁_fB`, **`famB_mem`**: `(fB₀ b₀, fB₁ b₁) ∈ Gam d` when `φ₀ b₀ = φ₀ t₀ ^ d * φ₁ b₁`;
* **`liftN₀ : N →+* L₀`**, **`liftN₁ : N →+* L₁`** (from `N = B₀[1/t₀] = B₁[1/t₁]`), `liftN₀_φ₀`, `liftN₁_φ₁`,
  `liftN₀_inv`, `liftN₁_inv`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat2

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

theorem liftN₁_φ₁ (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁)) (b : B₁) :
    liftN₁ C hφ₁ hu₁ (φ₁ b) = jL₁ C (fB₁ C b) := by
  letI := φ₁.toAlgebra
  haveI := isLocalization_of_isAwayMap φ₁ t₁ hφ₁ hu₁
  exact IsLocalization.Away.lift_eq t₁ (g := (jL₁ C).comp (fB₁ C))
    (IsLocalization.Away.algebraMap_isUnit (sFm C)) b

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_LocFlat =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)

For a local ring `(A, 𝔪)` and a finite `A`-module `M`:
* `lf_li_flat`: over a local ring, a family in a flat module whose combinations with a coefficient outside `𝔪`
  never lie in `𝔪 • M` is linearly independent (Mathlib's `linearIndependent_of_flat`, residue field form removed);
* `lf_coef_mem`: if `M ⧸ I M` is flat over `A ⧸ I` (`I ≠ ⊤`), a relation `∑ gᵢ vᵢ = 0` among lifts of a residue
  basis has all `gᵢ ∈ I`;
* **`free_of_quot_flat'`**: `M ⧸ Iₖ M` flat over `A ⧸ Iₖ` for a family `Iₖ ≠ ⊤` with `⋂ Iₖ = 0` ⇒ `M` free;
* **`free_of_quot_flat`** (`A` noetherian, `J ≠ ⊤`): `M ⧸ J^(k+1) M` flat over `A ⧸ J^(k+1)` for all `k` ⇒ `M` free.
-/

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace RamanujanPetersson.EtPBC.Cov

universe u

section LocFlat

variable {A M : Type u} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]

/-- **Local flatness criterion** (family form): if `M ⧸ Iₖ M` is flat over `A ⧸ Iₖ` for ideals `Iₖ ≠ ⊤` with zero
intersection, the finite module `M` is free. -/
theorem free_of_quot_flat' [Module.Finite A M] (I : ℕ → Ideal A) (hI : ∀ k, I k ≠ ⊤)
    (hK : ∀ a : A, (∀ k, a ∈ I k) → a = 0)
    (hfl : ∀ k, Module.Flat (A ⧸ I k) (M ⧸ (I k • ⊤ : Submodule A M))) : Module.Free A M := by
  let w := Module.Free.chooseBasis (ResidueField A) (ResidueField A ⊗[A] M)
  obtain ⟨v, eq⟩ :=
    (TensorProduct.mk_surjective A M (ResidueField A) Ideal.Quotient.mk_surjective).comp_left w
  have h0 : ∀ (s : Finset (Module.Free.ChooseBasisIndex (ResidueField A) (ResidueField A ⊗[A] M)))
      (c : Module.Free.ChooseBasisIndex (ResidueField A) (ResidueField A ⊗[A] M) → A),
      ∑ i ∈ s, c i • v i ∈ (maximalIdeal A) • (⊤ : Submodule A M) → ∀ i ∈ s, c i ∈ maximalIdeal A := by
    intro s c hc i hi
    rw [← lf_mk_eq_zero_iff, ← lf_res_sum v s c] at hc
    rw [← residue_eq_zero_iff]
    exact linearIndependent_iff'.mp w.linearIndependent s (fun j => residue A (c j))
      (Eq.trans (Finset.sum_congr rfl fun j _ =>
        congrArg (fun x => residue A (c j) • x) (congr_fun eq j).symm) hc) i hi
  refine .of_basis <| .mk (v := v) ?_ (by exact (span_eq_top_of_tmul_eq_basis _ w <| congr_fun eq).ge)
  rw [linearIndependent_iff']
  intro s g hg i hi
  exact hK _ fun k => lf_coef_mem (I k) (hI k) (hfl k) v h0 s g hg i hi

end LocFlat

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr14 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts

With `fh = σh ⊗ id : C ⊗ B → Ah ⊗ B`, `f' = σ ⊗ id : C ⊗ B → R' ⊗ B`, `θh : Pres (gmap fh gC) → Q` restricting to
`kap res` on `Ah ⊗ B`:
* `exists_cov`, **`hκT`** (the compatibility needed by `resid`), `lamT` (`lamT_apply`, `lamT_hlam`);
* **`resid_surj_T`**, **`resid_ker_T`**: the residue `resid fh f' gC θh (kap χ') _` is onto with kernel
  `Jt B χ' · Pres (gmap f' gC)`, when `ker θh = pI · Pres` with `pI ≤ ker res`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

variable {K A R' B Ah C Q : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Ah] [Algebra A Ah] [CommRing C] [Algebra A C] [CommRing Q]
  (χ : A →+* K) (χ' : R' →+* K) (res : Ah →+* K)
  (hres : ∀ a, res (algebraMap A Ah a) = χ a) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a)
  (ν : K →+* Q) (βQ : B →+* Q) (hβ : ∀ a, βQ (algebraMap A B a) = ν (χ a))

variable {r : ℕ} (σh : C →ₐ[A] Ah) (σ : C →ₐ[A] R') (gC : Fin r → MvPolynomial (Fin r) (C ⊗[A] B))
  (θh : Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC) →+* Q)

theorem lamT_apply (s : K →+* R') (hs : ∀ k, χ' (s k) = k) (x : Ah ⊗[A] B) :
    lamT χ χ' res hres hχ' σ gC s hs x = algebraMap ((R' ⊗[A] B) ⧸ Jt B χ')
      (Pres (gmap (Ideal.Quotient.mk (Jt B χ')) (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC)))
      (lamQ χ χ' res s hres hχ' hs x) :=
  rfl

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4Glue =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`

* `chU_sup`: `D₊(X₀) ⊔ D₊(X₁) = ⊤`; `Yc_sup`: `Y₀ ⊔ Y₁ = ⊤`.
* `struct_res`: the structure map `Γ(V) → Γ(Y, ⊤)` restricts to the chart structures; `map_map`.
* **`glueRing : secAlg φY0 φY1 →+* Γ(Y, ⊤)`** (sheaf gluing), `glueRing_res0`, `glueRing_res1`, `eq_of_res`,
  `glueRing_struct`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace HomogeneousLocalization
open RamanujanPetersson.EtCompact
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K]

variable {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}} (π : Y ⟶ PV K gV)

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

theorem mem_eqLocus (x : Z2.secAlg (φY0 K gV π) (φY1 K gV π)) :
    x.1 ∈ RingHom.eqLocus
      (RingHom.comp (Y.sheaf.obj.map (homOfLE inf_le_left : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 0).op).hom
        (RingHom.fst (Y.sheaf.obj.obj <| op (Yc K gV π 0)) (Y.sheaf.obj.obj <| op (Yc K gV π 1))))
      (RingHom.comp (Y.sheaf.obj.map (homOfLE inf_le_right : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 1).op).hom
        (RingHom.snd (Y.sheaf.obj.obj <| op (Yc K gV π 0)) (Y.sheaf.obj.obj <| op (Yc K gV π 1)))) :=
  x.2

/-- The glued section (ring map). -/
def glueRing : Z2.secAlg (φY0 K gV π) (φY1 K gV π) →+* Γ(Y, ⊤) :=
  (Y.presheaf.map (homOfLE (Yc_sup K gV π).ge : (⊤ : Y.Opens) ⟶ Yc K gV π 0 ⊔ Yc K gV π 1).op).hom.comp
    ((Y.sheaf.objSupIsoProdEqLocus (Yc K gV π 0) (Yc K gV π 1)).inv.hom.comp
      ((Z2.secAlg (φY0 K gV π) (φY1 K gV π)).val.toRingHom.codRestrict _ (mem_eqLocus K gV π)))

theorem glueRing_res0 (x : Z2.secAlg (φY0 K gV π) (φY1 K gV π)) :
    Y.presheaf.map (homOfLE le_top : Yc K gV π 0 ⟶ ⊤).op (glueRing K gV π x) = x.1.1 := by
  have := Y.sheaf.objSupIsoProdEqLocus_inv_fst (Yc K gV π 0) (Yc K gV π 1) ⟨x.1, mem_eqLocus K gV π x⟩
  exact (map_map (X := Y) (le_top : Yc K gV π 0 ≤ ⊤) (Yc_sup K gV π).ge _).trans this

theorem glueRing_res1 (x : Z2.secAlg (φY0 K gV π) (φY1 K gV π)) :
    Y.presheaf.map (homOfLE le_top : Yc K gV π 1 ⟶ ⊤).op (glueRing K gV π x) = x.1.2 := by
  have := Y.sheaf.objSupIsoProdEqLocus_inv_snd (Yc K gV π 0) (Yc K gV π 1) ⟨x.1, mem_eqLocus K gV π x⟩
  exact (map_map (X := Y) (le_top : Yc K gV π 1 ≤ ⊤) (Yc_sup K gV π).ge _).trans this

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCh =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`

For `V` affine, `π : Y ⟶ P¹_V` finite, a `K`-point `x` of `V` and a finite etale `q : T ⟶ Y_x`, the charts
`Γ(Y_x, fx⁻¹ Yᵢ)` and `Γ(T, q⁻¹ fx⁻¹ Yᵢ)` satisfy every hypothesis of `CoverLiftAt`. **`nonempty_liftD`**: under
`CoverLiftAt K Γ(V) χ` (`χ` the point `x`), the lift data `LiftD` (= `CoverLift` at these charts) exist.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V)

attribute [local instance] algKY

section Cover

variable {T : Scheme.{u}} (q : T ⟶ Yx K gV π x)

attribute [local instance] algT

/-- **The lift data** of the fibre cover `q` (the conclusion `CoverLift` of `CoverLiftAt` at these charts). -/
abbrev LiftD (hx : x ≫ gV = 𝟙 _) : Type (u + 1) :=
  @CoverLift K _ Γ(V, ⊤) _ (algKV K gV) (χV K gV x hx) Γ(Y, Yc K gV π 0) Γ(Y, Yc K gV π 1)
    Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) _ _ _ _ _ _ _ _ _ (φY0 K gV π) (φY1 K gV π)
    Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ Yc K gV π 0) Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ Yc K gV π 1)
    Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)) _ _ _ _ _ _
    ((fx K gV π x).app (Yc K gV π 0)).hom ((fx K gV π x).app (Yc K gV π 1)).hom
    ((fx K gV π x).app (Yc K gV π 0 ⊓ Yc K gV π 1)).hom Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 0))
    Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 1)) Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)))
    _ _ _ _ _ _ (ψT0 K gV π x q) (ψT1 K gV π x q)

end Cover

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovY =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`

For an affine open `U ⊆ Y` (with `Γ(V) → Γ(Y, U)` the structure map), **`chY hU hA`** `: Spec (R' ⊗ Γ(Y, U)) ⟶ Y_{V'}`
is the base change of `hU.fromSpec` along `Y_{V'} ⟶ Y` (**`isPullback_chY`**), an open immersion with range
`fst⁻¹ U` (**`opensRange_chY`**), compatible with restrictions (**`chY_res`**).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

section Chart

variable {U : Y.Opens} (hU : IsAffineOpen U) [Algebra Γ(V, ⊤) Γ(Y, U)]
  (hA : CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(Y, U)) = strU K gV π U)

/-- **The chart `Spec (R' ⊗ Γ(Y, U)) ⟶ Y_{V'}`.** -/
def chY : Spec (CommRingCat.of (R' ⊗[Γ(V, ⊤)] Γ(Y, U))) ⟶ YV K gV π R' :=
  pullback.lift (Spec.map (CommRingCat.ofHom (S := R' ⊗[Γ(V, ⊤)] Γ(Y, U))
      Algebra.TensorProduct.includeRight.toRingHom) ≫ hU.fromSpec)
    (Spec.map (CommRingCat.ofHom (S := R' ⊗[Γ(V, ⊤)] Γ(Y, U)) Algebra.TensorProduct.includeLeftRingHom))
    (chY_w K gV π R' hU hA)

end Chart

section Res

end Res

end RamanujanPetersson.EtPBC.Cov

end

end

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

/-- `(u_v ≫ ι^* f)(1) = σ_v^* η_G(f(1))`. -/
theorem sc_bcUnit_comp (j : Nbhd s) (G : EtSh Λ P) (f : (nbhdSys Λ g s).obj j ⟶ G) :
    sc (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map f) (etId (fib g s)) =
      ((((pull (fibι g s) Λ).obj G).obj.map (nbhdSec g s j).op).hom
        ((((pullAdj (fibι g s) Λ).unit.app G).hom.app (op ((etPull g).obj j.1))).hom
          (freeEquiv Λ ((etPull g).obj j.1) G f))) := by
  have hn := ConcreteCategory.congr_hom
    (((pull (fibι g s) Λ).map f).hom.naturality (nbhdSec g s j).op) (unitSec Λ g s j)
  have hp := pull_unitSec Λ g s j G f
  exact (congrArg (((pull (fibι g s) Λ).map f).hom.app (op (etId (fib g s)))).hom
    (sc_ofSec (fibSec Λ g s j))).trans
    (hn.trans (congrArg (((pull (fibι g s) Λ).obj G).obj.map (nbhdSec g s j).op).hom hp))

end BC

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

/-- **The value along a local representation.** -/
theorem vval_of_lift (b : unitSh Λ X ⟶ (pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M)))
    {W : P.Etale} {U : X.Etale} (h : U ⟶ (etPull ι).obj W) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj W)))
    (hb : sc b U = (((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj.map h.op).hom
        ((((pullAdj ι Λ).unit.app ((push π Λ).obj (constSh Λ Y M))).hom.app (op W)).hom z))
    (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι)
    (l : Spec (CommRingCat.of Ω) ⟶ pullback (pullback.snd π ι) U.hom) (hl : l ≫ pullback.fst _ _ = τ) :
    vval ι π b τ = cval z (kap ι π h (l (default : Spec (CommRingCat.of Ω)))) := by
  have e1 := xi_of_pullRep ι π b h z hb (sigPt ι π τ) (liftPt ι π τ l hl)
  have hpt := congrArg (fun φ => φ.base (default : Spec (CommRingCat.of Ω))) (xMor_fibToNbhd ι π h τ l hl)
  exact (congrArg (fun e => psi π ((sigPt ι π τ).map ι) e (xMor ι π τ (default : Spec (CommRingCat.of Ω)))) e1).trans
    ((psi_germ π ((sigPt ι π τ).map ι)
      ⟨W, (fiberMapIso ι (sigPt ι π τ)).inv.app W ((sigPt ι π τ).point.fiber.map h (liftPt ι π τ l hl))⟩ z _).trans
      (congrArg (cval z) hpt))

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibC =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 13 (G-f, part 3): the `π₀` extension theorem

* `fibLift` (the fibre map of `exists_etale_idem_Y`), `fibLift_fst`, `fibLift_snd`; `chart_eq` (on a chart, the
  pulled-back idempotent is computed in `κ(p) ⊗ Γ(Y, U)`).
* **`exists_clopen_ext`**: `V` affine noetherian over `K`, `π : Y ⟶ P¹_V` finite, `x : Spec K ⟶ V` a `K`-point
  (`x ≫ gV = 𝟙`), `C₀ ⊆ Y_x` clopen. Then there are an etale `Γ(V)`-algebra `R'`, a lift `x' : Spec K ⟶ Spec R'` of
  `x` and a clopen `C ⊆ Y ×_V Spec R'` whose preimage in `Y_x` (under `yxMap`) is `C₀`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algYV

section Chart

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (x : Spec (CommRingCat.of K) ⟶ V)
  {R' : Type u} [CommRing R'] [Algebra Γ(V, ⊤) R'] (P : Ideal R') [P.IsPrime] [P.LiesOver (px K x)]
  (hbij : Function.Bijective (Ideal.ResidueField.mapₐ (px K x) P (Algebra.ofId _ _) (P.over_def (px K x))))

omit [IsAffine V] in
/-- The fibre map of `exists_etale_idem_Y`. -/
abbrev fibLift : R' ⊗[Γ(V, ⊤)] Z2.secAlg (φY0 K gV π) (φY1 K gV π) →ₐ[Γ(V, ⊤)]
    ((px K x).ResidueField ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) × ((px K x).ResidueField ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 1)) :=
  Algebra.TensorProduct.lift
    (((Z2.fibreUnit (px K x) Γ(Y, Yc K gV π 0) Γ(Y, Yc K gV π 1)).comp
      (AlgEquiv.ofBijective _ hbij).symm.toAlgHom).comp
      (IsScalarTower.toAlgHom Γ(V, ⊤) R' P.ResidueField)) (Z2.fibreMap (px K x) (φY0 K gV π) (φY1 K gV π))
    (fun _ _ => Commute.all _ _)

end Chart

section Main

end Main

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG3 =====
section

/-!
# S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective

* Generic (any coequifibered `α : 𝒪_X ⟶ F` on affine opens): `glD H` (the relative gluing data),
  `cover_toBase` (`Spec F(U) ⟶ U₀ ⟶ X` is `Spec α_U ≫ U.fromSpec`), `prop_toBase` (a Zariski-local property holds
  for `toBase` once it holds for every `Spec α_U`), `isFinite_toBase`, `etale_toBase`, `surjective_toBase`.
* For `V` etale and surjective over `X` with `V.hom` affine: `surj_comap`, the instance
  `Module.FaithfullyFlat Γ(X, U) (CU V U)`, and for the descended presheaf `FU`:
  **`U0`**, **`toU0`** `: U0 ⟶ X` with `IsFinite`, `Etale`, `Surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Base

end Base

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom]

instance faithfullyFlat_CU [Surjective V.hom] (U : X.AffineZariskiSite) :
    Module.FaithfullyFlat Γ(X, U.1) (CU V U) :=
  Module.FaithfullyFlat.of_comap_surjective (surj_comap V U)

end Cover

end RamanujanPetersson.EtPBC.DescG

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

theorem eC_eq : eC M Φ ι = (pull ι Λ).map (rC M Φ ι) ≫ (pullAdj ι Λ).counit.app _ :=
  Adjunction.homEquiv_counit _ _ _ _

end BC

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dB =====
section

/-!
# S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`

* `isClosedImmersion_of_isIso_comp`: a point `σ : Spec Ω ⟶ V` with `σ ≫ gV` an isomorphism is a closed immersion;
* `sec_ext_cval`: sections of a constant sheaf are determined by their values;
* `rUq`, `cval_rUq`: restriction along a commutative triangle; `cval_pushCompIso_inv`;
* `resAdj_symm_app`, `mR_app`, `cval_mR`: the transpose `mR` on sections and values (kernel-cheap: generic lemmas);
* `mS : π_* M_Y ⟶ f_* Φ_* M_U` (restriction along `h : U ⟶ Y`, `h ≫ π = Φ ≫ f`), `mP := (f^* ⊣ f_*)`-adjoint;
* **`mono_mP`**: for `f` etale and `U ⟶ P' ×_P Y` surjective, `mP : f^* π_* M_Y ⟶ Φ_* M_U` is a monomorphism.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.FBC

universe u

section Geo0

end Geo0

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

section RUq

end RUq

section M

variable {P P' Y U : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (Φ : U ⟶ P') (h : U ⟶ Y) (hh : h ≫ π = Φ ≫ f)

variable [Etale f]

theorem cval_mR (W : P'.Etale) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj ((etComp f).obj W))))
    (u : ((etPull Φ).obj W).left) :
    cval (((mR M π f Φ h hh).hom.app (op W)).hom z) u = cval z (thU π f Φ h hh W u) :=
  (congrArg (fun t => cval (M := M) (T := (etPull Φ).obj W) t u) (mR_app π f Φ h hh W z)).trans <|
    (cval_map ((etPull Φ).map ((etCompAdj f).unit.app W)) _ u).trans <|
      (cval_mS π f Φ h hh ((etComp f).obj W) z _).trans
        (congrArg (cval z) (thU_apply π f Φ h hh W u).symm)

theorem mR_injective (hs : Function.Surjective ⇑(pullback.lift Φ h hh.symm : U ⟶ pullback f π))
    (W : P'.Etale) : Function.Injective ((mR M π f Φ h hh).hom.app (op W)) := by
  intro z₁ z₂ hz
  have hz' := (mc_apply ((mR M π f Φ h hh).hom.app (op W)) z₁).symm.trans
    (hz.trans (mc_apply ((mR M π f Φ h hh).hom.app (op W)) z₂))
  refine sec_ext_cval (M := M) (T := (etPull π).obj ((etComp f).obj W)) z₁ z₂ fun q => ?_
  obtain ⟨u, rfl⟩ := thU_surjective π f Φ h hh hs W q
  exact (cval_mR π f Φ h hh W z₁ u).symm.trans
    ((congrArg (fun t => cval (M := M) (T := (etPull Φ).obj W) t u) hz').trans (cval_mR π f Φ h hh W z₂ u))

theorem mono_mR (hs : Function.Surjective ⇑(pullback.lift Φ h hh.symm : U ⟶ pullback f π)) :
    Mono (mR M π f Φ h hh) := by
  have : ∀ V : (P'.Etale)ᵒᵖ, Mono ((mR M π f Φ h hh).hom.app V) := fun ⟨W⟩ =>
    (ModuleCat.mono_iff_injective _).2 (mR_injective π f Φ h hh hs W)
  have : Mono (mR M π f Φ h hh).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono (f := mR M π f Φ h hh)

/-- **`mP` is a monomorphism** when `U ⟶ P' ×_P Y` is surjective. -/
theorem mono_mP (hs : Function.Surjective ⇑(pullback.lift Φ h hh.symm : U ⟶ pullback f π)) :
    Mono (mP M π f Φ h hh) := by
  have h1 := mono_mR (M := M) π f Φ h hh hs
  have h0 : Mono ((pullIsoRes f Λ).hom.app ((push π Λ).obj (constSh Λ Y M))) :=
    IsIso.mono_of_iso _
  rw [mP_eq]
  exact mono_comp _ _

end M

end RamanujanPetersson.EtPBC.T3d

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

theorem a_retT (W : (Over T)ᵒᵖ) (y : ((Over.forget T).op ⋙ F.obj).obj W) :
    ((retT a b hab hS σ hσ).app W).hom (((wh a T).app W).hom y) = y := by
  apply wsec_inj a b hab hS W
  rw [retT_app, piT_apply, wsec_fg a b hab W y, map_zero, sub_zero]

/-- `res a ≫ retT = 𝟙` as maps of sheaves on `T`. -/
theorem res_a_retT : (res T.hom Λ).map a ≫ homOverEquiv E F T (retT a b hab hS σ hσ) = 𝟙 _ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun W => ModuleCat.hom_ext (LinearMap.ext fun y =>
    a_retT a b hab hS σ hσ (op ((overOf T).obj W.unop)) y)))

end Ret

section Tau

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {N : ModuleCat.{u} Λ} {E : EtSh Λ X}
  (a : constSh Λ X N ⟶ E) (b : E ⟶ unitSh Λ X) (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact)
  {T : X.Etale} (σ : E.obj.obj (op T))
  (hσ : (b.hom.app (op T)).hom σ = (constUnit (ModuleCat.of Λ Λ) T).hom 1) {Z : Scheme.{u}} (ψ : Z ⟶ T.left)

/-- **`a ≫ τ = uC`**. -/
theorem a_tau : a ≫ tau a b hab hS σ hσ ψ = uC (ψ ≫ T.hom) N := by
  have h2 : (resAdj T.hom Λ).unit.app (constSh Λ X N) ≫ (push T.hom Λ).map (d0 N ψ) =
      uC (ψ ≫ T.hom) N ≫ (pushCompIso Λ ψ T.hom).inv.app _ :=
    ((resAdj T.hom Λ).homEquiv_unit _ _ (d0 N ψ)).symm.trans (Equiv.apply_symm_apply _ _)
  have h3 : (push T.hom Λ).map ((res T.hom Λ).map a) ≫
      (push T.hom Λ).map (homOverEquiv E (constSh Λ X N) T (retT a b hab hS σ hσ) ≫ d0 N ψ) =
      (push T.hom Λ).map (d0 N ψ) := by
    rw [← Functor.map_comp, ← Category.assoc, res_a_retT, Category.id_comp]
  have h1 := (resAdj T.hom Λ).unit_naturality a
  calc a ≫ tau a b hab hS σ hσ ψ
      = (a ≫ (resAdj T.hom Λ).unit.app E) ≫
          (push T.hom Λ).map (homOverEquiv E (constSh Λ X N) T (retT a b hab hS σ hσ) ≫ d0 N ψ) ≫
            (pushCompIso Λ ψ T.hom).hom.app (constSh Λ Z N) := (Category.assoc _ _ _).symm
    _ = ((resAdj T.hom Λ).unit.app (constSh Λ X N) ≫ (push T.hom Λ).map ((res T.hom Λ).map a)) ≫
          (push T.hom Λ).map (homOverEquiv E (constSh Λ X N) T (retT a b hab hS σ hσ) ≫ d0 N ψ) ≫
            (pushCompIso Λ ψ T.hom).hom.app (constSh Λ Z N) := eq_whisker h1.symm _
    _ = (resAdj T.hom Λ).unit.app (constSh Λ X N) ≫ ((push T.hom Λ).map ((res T.hom Λ).map a) ≫
          (push T.hom Λ).map (homOverEquiv E (constSh Λ X N) T (retT a b hab hS σ hσ) ≫ d0 N ψ)) ≫
            (pushCompIso Λ ψ T.hom).hom.app (constSh Λ Z N) := by
        simp only [Category.assoc]
    _ = ((resAdj T.hom Λ).unit.app (constSh Λ X N) ≫ (push T.hom Λ).map (d0 N ψ)) ≫
            (pushCompIso Λ ψ T.hom).hom.app (constSh Λ Z N) := by
        rw [h3, Category.assoc]
    _ = uC (ψ ≫ T.hom) N := by
        rw [h2, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end Tau

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

end Gsum

/-- **A good splitting neighbourhood.** -/
theorem exists_good [IsNoetherianRing Λ] (hqc : ∀ V : P.Etale, IsAffine V.left → QuasiCompact V.hom) (x : P)
    {J : Type u} [Finite J] (W : J → P.Etale) (hW : ∀ j, IsAffine (W j).left) (f : ∀ j, G.obj.obj (op (W j))) :
    ∃ (T : P.Etale) (t : (geomPtAt x).point.fiber.obj T) (τ : ∀ p : FibPts x W, T ⟶ W p.1),
      (∀ p, (geomPtAt x).point.fiber.map (τ p) t = p.2) ∧
      (∀ c, GenAlg.rel W G f x c = 0 → gsum G f τ c = 0) ∧ (∀ v, T.hom v = x → v = fpt x t) := by
  classical
  have : ∀ j, QuasiCompact (W j).hom := fun j => hqc _ (hW j)
  have : Finite (FibPts x W) := finite_fibPts x W
  have hfg : (LinearMap.ker (GenAlg.rel W G f x)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨T₀, t₀, τ₀, hτ₀, h₀⟩ := exists_kill G x W f s fun c hc => by
    have : c ∈ LinearMap.ker (GenAlg.rel W G f x) := hs ▸ Submodule.subset_span hc
    exact LinearMap.mem_ker.1 this
  obtain ⟨j', ρ, hj'⟩ := exists_affine_le (geomPtAt x) (⟨T₀, t₀⟩ : Nbhd (geomPtAt x))
  let T₁ := j'.1
  let t₁ : (geomPtAt x).point.fiber.obj T₁ := j'.2
  let τ₁ : ∀ p : FibPts x W, T₁ ⟶ W p.1 := fun p => ρ.1 ≫ τ₀ p
  have hτ₁ : ∀ p, (geomPtAt x).point.fiber.map (τ₁ p) t₁ = p.2 := fun p =>
    (map_comp_fib ρ.1 (τ₀ p) t₁).trans
      ((congrArg (fun z => (geomPtAt x).point.fiber.map (τ₀ p) z) ρ.2).trans (hτ₀ p))
  have hker : ∀ c, GenAlg.rel W G f x c = 0 → gsum G f τ₁ c = 0 := by
    intro c hc
    have hle : LinearMap.ker (GenAlg.rel W G f x) ≤ LinearMap.ker (gsum G f τ₀) := by
      rw [← hs, Submodule.span_le]
      intro d hd
      exact h₀ d hd
    have h := hle hc
    rw [LinearMap.mem_ker] at h
    exact (gsum_comp G f ρ.1 τ₀ c).trans ((congrArg _ h).trans (map_zero _))
  have : QuasiCompact T₁.hom := hqc T₁ hj'
  obtain ⟨O, hO, hOu⟩ := exists_opens_unique T₁ x t₁
  obtain ⟨t₂, ht₂, hft₂⟩ := exists_lift_fib (opnι T₁ O) x t₁ ⟨_, hO⟩ rfl
  refine ⟨opn T₁ O, t₂, fun p => opnι T₁ O ≫ τ₁ p, fun p => (map_comp_fib _ (τ₁ p) t₂).trans
      ((congrArg (fun z => (geomPtAt x).point.fiber.map (τ₁ p) z) ht₂).trans (hτ₁ p)),
    fun c hc => (gsum_comp G f _ τ₁ c).trans ((congrArg _ (hker c hc)).trans (map_zero _)), ?_⟩
  intro v hv
  refine opnι_injective T₁ O ?_
  exact (hOu _ (opnι_mem T₁ O v) hv).trans (congrArg (opnι T₁ O).left hft₂).symm

end RamanujanPetersson.EtPBC.GenGeo

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

theorem psi_zero (q : fib π t) :
    psi π t (0 : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj ((push π Λ).obj (constSh Λ Y M)).obj) q = 0 := by
  have h := psi_add π t (0 : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj
    ((push π Λ).obj (constSh Λ Y M)).obj) 0 q
  rw [add_zero] at h
  exact left_eq_add.1 h

/-- `psi` at `q` as a linear map on the stalk at `x̄`. -/
def psiS (x : P) (q : fib π (geomPtAt x)) : stalk Λ ((push π Λ).obj (constSh Λ Y M)) x →ₗ[Λ] M where
  toFun e := psi π (geomPtAt x) e q
  map_add' e₁ e₂ := psi_add π _ e₁ e₂ q
  map_smul' c e := psi_smul π _ c e q

variable {J : Type u} (W : J → P.Etale)

/-- **Values of a combination of germs.** -/
theorem psi_rel (f : ∀ j, ((push π Λ).obj (constSh Λ Y M)).obj.obj (op (W j))) (x : P)
    (l : (Σ j, (geomPtAt x).point.fiber.obj (W j)) →₀ Λ) (q : fib π (geomPtAt x)) :
    psi π (geomPtAt x) (rel W _ f x l) q =
      l.sum fun p c => c • cval (M := M) (f p.1) (fibToNbhd π (geomPtAt x) ⟨W p.1, p.2⟩ q) := by
  change psiS π x q (rel W _ f x l) = _
  rw [rel, Finsupp.apply_linearCombination, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun p _ => ?_
  congr 1
  exact psi_germ π (geomPtAt x) ⟨W p.1, p.2⟩ (f p.1) q

end RamanujanPetersson.EtPBC.GenAlg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Fs =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves

For `W : P.Etale` and `x : P`, the stalk of `Λ[W]` at `x̄ = geomPtAt x` is the free module on the geometric fibre of
`W` over `x̄`:
* `fibDesc`: the map `presheafFiber (Λ[Hom(-, W)]) → (fibre →₀ Λ)`, `h ↦ fiber.map h b` at `(V, b)`;
* `stalkFree`: the induced map out of the stalk of `Λ[W]`, `stalkFree_germ` (germ of the tautological section at `a`
  goes to `single a 1`);
* `freeLin W x : (fibre →₀ Λ) →ₗ stalk`, `a ↦ germ_a(taut)`; **`freeStalkEquiv`** (bijective);
* `freeMap_taut`, **`freeLin_natural`**: the stalk map of `Λ[w]` is `lmapDomain (fiber.map w)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FreeStk

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

theorem stalkFree_freeLin (W : P.Etale) (x : P) (l : (geomPtAt x).point.fiber.obj W →₀ Λ) :
    (stalkFree Λ W x).hom (freeLin Λ W x l) = l := by
  induction l using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | single a c =>
    rw [freeLin, Finsupp.linearCombination_single, map_smul, stalkFree_germ, Finsupp.smul_single_one]

theorem freeLin_injective (W : P.Etale) (x : P) : Function.Injective (freeLin Λ W x) :=
  Function.LeftInverse.injective (stalkFree_freeLin W x)

end RamanujanPetersson.EtPBC.FreeStk

end

end

-- ===== S4.Def_RP_EtPBC_A_O2MV =====
section

/-!
# S4-EtPBC-A, O2 (MV route), MV: the Mayer-Vietoris sequence of free sheaves

For a commutative square `p₁ ≫ w = p₂ ≫ v` of `P.Etale` (`W' ⟶ W, U ⟶ Z`):
* `freeMap_comp`; `stalk_freeMap_injective`/`_surjective` (fibre map injective/surjective ⇒ stalk map so);
* `mvC`: the short complex `Λ[W'] ⟶ Λ[W] ⊞ Λ[U] ⟶ Λ[Z]` (maps `(Λ[p₁], -Λ[p₂])`, `Λ[w] + Λ[v]`);
* **`mvC_shortExact`**: short exact when every fibre of `Z` is subsingleton and at every point either the fibre of
  `W` is a singleton and `p₂` is bijective on fibres, or the fibre of `U` is a singleton and `p₁` is so;
* **`mv_exists`**: a class `β ∈ Ext^{n+1}(Λ[Z], F)` killed by `Λ[w]` and `Λ[v]` is `ε.comp κ`, `κ ∈ Ext^n(Λ[W'], F)`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.GenAlg
  RamanujanPetersson.EtPBC.FreeStk

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}}

theorem stalk_freeMap_injective {W' W : P.Etale} (w : W' ⟶ W) (x : P)
    (hw : Function.Injective ((geomPtAt x).point.fiber.map w)) :
    Function.Injective (((geomPtAt x).stalkF Λ).map (freeMap Λ w)).hom := by
  intro v v' h
  obtain ⟨l, rfl⟩ := freeLin_surjective (Λ := Λ) W' x v
  obtain ⟨l', rfl⟩ := freeLin_surjective (Λ := Λ) W' x v'
  rw [freeLin_natural, freeLin_natural] at h
  exact congrArg _ (Finsupp.mapDomain_injective hw (freeLin_injective W x h))

section Stalks

end Stalks

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), L1: base change of Mayer-Vietoris classes

* `mvMapHom`, **`mv_naturality`**: a morphism of MV data gives a morphism of MV complexes, so
  `ε₁ ∘ Λ[a'] = Λ[c] ∘ ε₂` in `Ext¹`.
* `mvPullHom`: `mvC(f⁻¹ data) ⟶ f^* mvC(data)` (an isomorphism), `mvPull_shortExact`;
  **`mapExact_mv`**: `f^*` of `ε.comp κ` is `ε(f⁻¹ data).comp (f^* κ)`.
* `freeToUnit_bcUnit`, **`bc_mv`**: the base change of `ε.comp κ` at a neighbourhood `j` of `s` is
  `σ_j^*(ε(ι⁻¹ data).comp (ι^* κ))`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe u

section Nat

end Nat

section Pull

end Pull

section BC

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- `Λ[P_s] ≅ Λ_{P_s} → ι^*Λ[g⁻¹V]` is `Λ[σ_j]` followed by `Λ[ι⁻¹g⁻¹V] ≅ ι^*Λ[g⁻¹V]`. -/
theorem freeToUnit_bcUnit (j : Nbhd s) :
    freeToUnit Λ (fib g s) ≫ bcUnit Λ g s j =
      freeMap Λ (nbhdSec g s j) ≫ pullFreeHom Λ (fibι g s) ((etPull g).obj j.1) := by
  apply (freeEquiv Λ (etId (fib g s)) ((pull (fibι g s) Λ).obj (freeSh Λ ((etPull g).obj j.1)))).injective
  refine (freeEquiv_comp Λ (etId (fib g s)) (freeToUnit Λ (fib g s)) (bcUnit Λ g s j)).trans ?_
  refine Eq.trans ?_
    (freeEquiv_freeMap Λ (nbhdSec g s j) _ (pullFreeHom Λ (fibι g s) ((etPull g).obj j.1))).symm
  have h1 : freeEquiv Λ (etId (fib g s)) (unitSh Λ (fib g s)) (freeToUnit Λ (fib g s)) = oneSec Λ (fib g s) :=
    AddEquiv.apply_symm_apply _ _
  have h2 : freeEquiv Λ ((etPull (fibι g s)).obj ((etPull g).obj j.1)) _
      (pullFreeHom Λ (fibι g s) ((etPull g).obj j.1)) = pullTaut Λ (fibι g s) ((etPull g).obj j.1) :=
    AddEquiv.apply_symm_apply _ _
  rw [h1, h2]
  refine (PtSec.sc_ofSec (fibSec Λ g s j)).trans ?_
  exact congrArg (((fibFree Λ g s j).obj.map (nbhdSec g s j).op).hom)
    (freeEquiv_unit (Λ := Λ) (fibι g s) ((etPull g).obj j.1))

end BC

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E2 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4b (ring level): a good basic open of an etale `k[X]`-algebra at a point over `X = a`

`B` etale over `k[X]`, `q` a prime of `B` over `(X - a)`. **`exists_good_away`**: some `g ∉ q` makes `R = B_g` a
Dedekind domain in which `q R` is the only prime over `(X - a)` and `q R = (X - a) R` (so `(X - a)` is prime in `R`):
the setting of the purity theorem `EtCompact.Pur.purity_xi`.
* `exists_away_isDomain'` (`B_{g h}` is a domain for every `h ∉ q`), `algebraMap_injective_of_flat`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.EtPBC.EtDed

open Polynomial

section Away'

end Away'

section Chart

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k[X] B] [Algebra.Etale k[X] B]

/-- **A good basic open at a point over `X = a`**: `B_g` is a Dedekind domain, `(X - a)` is nonzero in it and
generates the prime `q B_g`. -/
theorem exists_good_away (q : Ideal B) [hq : q.IsPrime] (a : k) (hqa : q.under k[X] = Ideal.span {X - C a}) :
    ∃ g ∉ q, IsDomain (Localization.Away g) ∧ IsDedekindDomain (Localization.Away g) ∧
      algebraMap k[X] (Localization.Away g) (X - C a) ≠ 0 ∧
      Ideal.span {algebraMap k[X] (Localization.Away g) (X - C a)} = q.map (algebraMap B (Localization.Away g)) ∧
      (q.map (algebraMap B (Localization.Away g))).IsPrime := by
  classical
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k[X] B
  have hpmax : (Ideal.span {X - C a} : Ideal k[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)
  have hp : (q.under k[X]).IsMaximal := hqa ▸ hpmax
  have : IsDomain (Localization.AtPrime q) := isDomain_atPrime k[X] B q (X - C a) hqa (X_sub_C_ne_zero a) hp
  obtain ⟨g₁, hg₁q, hg₁⟩ := exists_away_isDomain' q
  -- the other primes over `(X - a)`
  let S := (q.under k[X]).primesOver B
  have hSf : S.Finite := Algebra.QuasiFinite.finite_primesOver (q.under k[X])
  have hsep : ∀ n ∈ S, n ≠ q → ∃ x, x ∈ n ∧ x ∉ q := by
    intro n hn hne
    by_contra hall
    push Not at hall
    have : n.IsPrime := hn.1
    exact hne (Algebra.QuasiFinite.eq_of_le_of_under_eq n q (fun x hx => hall x hx) hn.2.over.symm)
  choose! gn hgn hgnq using hsep
  let T := hSf.toFinset.filter (fun n => n ≠ q)
  let g₂ : B := ∏ n ∈ T, gn n
  have hT : ∀ n ∈ T, n ∈ S ∧ n ≠ q := fun n hn => by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hn
    exact hn
  have hg₂q : g₂ ∈ q.primeCompl := Submonoid.prod_mem _ (fun n hn => hgnq n (hT n hn).1 (hT n hn).2)
  have hg₂n : ∀ n ∈ S, n ≠ q → g₂ ∈ n := by
    intro n hn hne
    have hnT : n ∈ T := by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hn, hne⟩
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem gn hnT
    rw [show g₂ = gn n * d from hd]
    exact Ideal.mul_mem_right _ _ (hgn n hn hne)
  let g := g₁ * g₂
  have hgq : g ∉ q := q.primeCompl.mul_mem hg₁q hg₂q
  have hdom : IsDomain (Localization.Away g) := hg₁ g₂ hg₂q
  let R := Localization.Away g
  have hinj : Function.Injective (algebraMap k[X] R) := algebraMap_injective_of_flat
  have hded : IsDedekindDomain R := isDedekindDomain_of_unramified k[X] R hinj
  have ht0 : algebraMap k[X] R (X - C a) ≠ 0 := fun h => X_sub_C_ne_zero a (hinj (h.trans (map_zero _).symm))
  have hdisj : Disjoint (↑(Submonoid.powers g) : Set B) ↑q := by
    refine Set.disjoint_left.2 (fun x hx hxq => ?_)
    obtain ⟨n, rfl⟩ := hx
    exact hgq (hq.mem_of_pow_mem n hxq)
  let q' := q.map (algebraMap B R)
  have hq' : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) R q hq hdisj
  have hcq : q'.comap (algebraMap B R) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) R hq hdisj
  have hund : q'.under k[X] = q.under k[X] := by
    show q'.comap (algebraMap k[X] R) = q.comap (algebraMap k[X] B)
    rw [IsScalarTower.algebraMap_eq k[X] B R, ← Ideal.comap_comap, hcq]
  have htq : algebraMap k[X] R (X - C a) ∈ q' := by
    have : X - C a ∈ q'.under k[X] := by
      rw [hund, hqa]
      exact Ideal.mem_span_singleton_self _
    exact this
  have hq'ne : q' ≠ ⊥ := fun h => ht0 (by rw [h] at htq; exact htq)
  have hq'max : q'.IsMaximal := hq'.isMaximal hq'ne
  have huniq : ∀ n : Ideal R, n.IsMaximal → algebraMap k[X] R (X - C a) ∈ n → n = q' := by
    intro n hn htn
    let n₀ := n.comap (algebraMap B R)
    have hn₀ : n₀.IsPrime := Ideal.IsPrime.comap _
    have hgn₀ : g ∉ n₀ := fun h => hn.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (IsLocalization.Away.algebraMap_isUnit g))
    have hun : n₀.under k[X] = q.under k[X] := by
      have hle : Ideal.span {X - C a} ≤ n₀.under k[X] := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        show algebraMap B R (algebraMap k[X] B (X - C a)) ∈ n
        rw [← IsScalarTower.algebraMap_apply]
        exact htn
      rw [hqa]
      exact (hpmax.eq_of_le (Ideal.IsPrime.comap _).ne_top hle).symm
    have hn₀S : n₀ ∈ S := ⟨hn₀, ⟨hun.symm⟩⟩
    have hn₀q : n₀ = q := by
      by_contra hne
      exact hgn₀ (Ideal.mul_mem_left _ _ (hg₂n n₀ hn₀S hne))
    rw [← IsLocalization.map_under (Submonoid.powers g) R n]
    show n₀.map (algebraMap B R) = q'
    rw [hn₀q]
  have hund' : q'.under k[X] = Ideal.span {X - C a} := hund.trans hqa
  have hspan := span_eq_of_unique k[X] R q' (X - C a) hund' (hund' ▸ hpmax) huniq
  exact ⟨g, hgq, hdom, hded, ht0, hspan, hq'⟩

end Chart

end RamanujanPetersson.EtPBC.EtDed


end

-- ===== S4.Def_RP_EtPBC_A_O2Km5 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km5): global sections of an affine scheme etale over `Spec A`

`X` affine, `g : X ⟶ Spec A` etale.
* `gamAlg g : Algebra A Γ(X, ⊤)` (through `ΓSpecIso` and `g.appTop`), **`etale_gamAlg`**;
* `isNoetherianRing_gam`; for a Jacobson PID `A` (not a field): **`isDomain_loc_gam`** (localizations at maximal
  ideals are domains) and **`isDedekindDomain_gam`** (`Γ ⧸ p` is Dedekind for minimal primes `p`) — the hypotheses
  of `h1_exists_kappa` (O2Km4).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

universe u

section Gam

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (CommRingCat.of A)) [Etale g]

variable [IsDomain A] [IsPrincipalIdealRing A] [IsJacobsonRing A] (hA : ¬IsField A)

include g hA in
theorem isDomain_loc_gam (m : Ideal Γ(X, ⊤)) [hm : m.IsMaximal] : IsDomain (Localization.AtPrime m) := by
  letI := gamAlg g
  have := etale_gamAlg g
  exact isDomain_loc_of_etale A hA Γ(X, ⊤) m hm

end Gam

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E4 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`

For a presentation `IsLocAff` through `D = Spec B ⟶ A¹ ⟶ P` (`c` the chart, `t = φ (X - a)`):
* `locT φ a : B ⟶ B_t`, `W1 c φ a := Spec B_t` over `P`, `toD1 : W1 ⟶ chEt c φ`;
* `mem_Uo_iff`: a point `u` of `Spec B` lands in `Uo` iff `t ∉ u`;
* **`isoT`**: `W1 ≅ D ×_P Uo` in `P.Etale`, with `isoT_hom_prW`, `isoT_inv_toD1`;
* `locT_cls`: the class `ε_loc ∘ κ` is `εT ∘ κ₁` with `εT := ε_loc ∘ Λ[isoT.inv]`, `κ₁ := Λ[isoT.hom]^* κ`;
* `locT_res_D`, `locT_res_U`: classes restricted from `D` or from `Uz` die under `εT`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

universe u

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

section T

variable {k : Type u} [Field k] {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{u}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)

variable {a}

variable {Uo : P.Opens} (hUo : ∀ u : Spec B, (chEt c φ).hom u ∈ Uo ↔ φ.hom (X - C a) ∉ u.asIdeal)

include hUo

section Cls

variable {Uz : P.Opens} (h : Uo ≤ Uz) (hS : (locC Λ (chEt c φ) h).ShortExact) {F : EtSh Λ P}

/-- Classes restricted from `D = Spec B` die under `εT`. -/
theorem locT_res_D (γ : Ext.{u} (freeSh Λ (chEt c φ)) F 1) :
    (hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUo).inv)) (add_zero 1)).comp
      ((Ext.mk₀ (freeMap Λ (toD1 c φ a))).comp γ (zero_add 1)) (show 1 + 1 = 2 from rfl) = 0 := by
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀_assoc, ← freeMap_comp, isoT_inv_toD1]
  exact loc_res_D h (chEt c φ) hS γ

end Cls

end T

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E8 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4d2 (Ext level): purity for `Ext¹(Λ[W₁], Λ_P)`, and changing `Uo` to `Uz`

* `prdMapR e : prd D X₁ ⟶ prd D X` (second factor), `prdMapR_prW`, `prdMapR_prT`;
* `toD1_cancel`: `toD1` is a monomorphism;
* **`uChange`**: `ε_loc(D, Uo ≤ Uz) ∘ Λ[isoT_Uo⁻¹] = ε_loc(D, Uz ≤ Uz) ∘ Λ[isoT_Uz⁻¹]`;
* `xiP Λ c a hN hΛ c' : Ext¹(Λ[Wa], Λ_P)` (the chart Kummer class);
* **`purity_Ext`**: `κ₁ = Λ[toD1]^* γ₀ + Λ[toWa]^* xiP(c')` for every `κ₁ ∈ Ext¹(Λ[W₁], Λ_P)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo

section PrdR

universe u

end PrdR

section Cancel

variable {k : Type} [Field k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)

variable {a} {Uo Uz : P.Opens} (h : Uo ≤ Uz)
  (hUo : ∀ u : Spec B, (chEt c φ).hom u ∈ Uo ↔ φ.hom (X - C a) ∉ u.asIdeal)
  (hUz : ∀ u : Spec B, (chEt c φ).hom u ∈ Uz ↔ φ.hom (X - C a) ∉ u.asIdeal)

theorem prdMapR_isoT : prdMapR (chEt c φ) (opEtMap h) ≫ (isoT c φ hUz).inv = (isoT c φ hUo).inv :=
  toD1_cancel c φ a (by rw [Category.assoc, isoT_inv_toD1, prdMapR_prW, isoT_inv_toD1])

/-- **Changing `Uo` to `Uz`** in the class through `W₁`. -/
theorem uChange (hS : (locC Λ (chEt c φ) h).ShortExact) (hSz : (locC Λ (chEt c φ) (le_refl Uz)).ShortExact) :
    hS.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUo).inv)) (add_zero 1) =
      hSz.extClass.comp (Ext.mk₀ (freeMap Λ (isoT c φ hUz).inv)) (add_zero 1) := by
  have hnat := mv_naturality (prdMapR (chEt c φ) (opEtMap h)) (𝟙 (chEt c φ)) (𝟙 (opEt Uz)) (𝟙 (etId P))
    (by rw [Category.comp_id, prdMapR_prW]) (opEt_ext _ _) (toTop_ext _ _) (toTop_ext _ _) hS hSz
  rw [freeMap_id, Ext.mk₀_id_comp] at hnat
  rw [← hnat, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← freeMap_comp, prdMapR_isoT c φ h hUo hUz]

end Cancel

section PurE

end PurE

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km6 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`

`D = Spec B` etale over `𝔸¹ ⊆ P` (`chEt c φ`), `D_o := D ×_P Uo` affine, `R` etale over `P` with `R.left` affine and
constant geometric fibre size `n` over `D_o`; `W := D_o ×_P R` (the Shapiro scheme).
* generic instances: `W` affine, `W ⟶ D_o` quasi-compact and separated (from O2Km1);
* `shG : W.left ⟶ Spec k[X]`, **`etale_shG`**; `Γ(W, ⊤)` noetherian, `isDomain_loc_W` (localizations at maximal
  ideals are domains), `Γ(W, ⊤) ⧸ p` Dedekind (O2Km5 with `A = k[X]`);
* (the Kummer decomposition of `Ext¹(Λ[D_o], Λ[R]) ≃ H¹(W)` is `h1_exists_kappa (isDomain_loc_W ..)` / O2Km9; a
  separate `shap_exists_kappa` here cost 550 user-s under `lean -o` and was dropped).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur

universe u

section Inst

end Inst

section Assembly

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]

variable [IsAffine (prd (chEt c φ) (opEt Uo)).left]

theorem isDomain_loc_W (m : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal] :
    IsDomain (Localization.AtPrime m) :=
  isDomain_loc_gam (shG c φ R) (Polynomial.not_isField k) m

end Assembly

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2h =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`

GLOB/REL PLAN v1, stage S4. `d = d₂₁ ≫ d₀ : D₂ ⟶ D₁ ⟶ D_{g₀}` with `Γ(W₂) = Γ(W₁)[1/s]` along `d₂₁` (Zariski) and
`d₂₁.left = Spec.map ι`; `H · ρ(r)^N = ρ y` on `Y₁`, `(prdMap d₀)^* y = r^N ũ (1 - r z)` in `Π_q Frac(Γ(W₁) ⧸ q)`
(`ũ = (u₁ on p₁, 1 elsewhere)`, `z` integral over `B₁`):
* **`exists_S4`**: `e`, a monic `g ∈ B₂[X]` of positive degree with `g(e q) = 0` (`he`), and for the piece `p₂` over `p₁`:
  `m^* H = Ψ u₁ (1 + bK(φ₂ r) e p₂)` (`hHp`, any compatible `Ψ`), `m^* H = 1 + bK(φ₂ r) e q` for `q ≠ p₂` (`hHq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section S4GenB

end S4GenB

section S4

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  [IsAffine (prd (chEt c φ₁) (opEt Uo)).left]
  {B₂ : CommRingCat.{0}} (φ₂ : CommRingCat.of k[X] ⟶ B₂) [Etale (Spec.map φ₂ ≫ c)]
  [IsAffine (prd (chEt c φ₂) (opEt Uo)).left]
  (hD₂ : ∀ v : (prd (chEt c φ₂) (opEt Uo)).left, (prd (chEt c φ₂) (opEt Uo)).hom v ∈ opnDg c G)
  (d₂₁ : chEt c φ₂ ⟶ chEt c φ₁) (d₀ : chEt c φ₁ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))

/-- `r ≠ 0` is nonzero on every piece of `W₂`. -/
def toPiQ_bW_ne_zero {r : k[X]} (hr : r ≠ 0)
    (q : minimalPrimes Γ(((etPull (prd (chEt c φ₂) (opEt Uo)).hom).obj R).left, ⊤)) :
    toPiQ ((bW (Spec.map φ₂ ≫ c) (opEt Uo) R).hom (φ₂.hom r)) q ≠ 0 := by
  have e := toPiQ_gamMap_ne_zero (shG c φ₂ (Uo := Uo) R) hr q
  exact fun h0 => e ((congrArg (fun x => toPiQ x q) (gamMap_shG c R φ₂ r)).trans h0)

end S4

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2LocU =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2LocU): changing the open of a one-point MV class

GLOB/REL PLAN v1 (4). For `U₁ ≤ U₀ ≤ Uz` and `D : P.Etale`:
* `locC_opn`: `ε(D, U₁ ≤ Uz) ∘ Λ[prdMapR D (opEtMap h₁₀)] = ε(D, U₀ ≤ Uz)`;
* `locCls_opn`: `ε(D, U₀) ∘ κ = ε(D, U₁) ∘ Λ[prdMapR] ∘ κ`;
* **`locCls_opn_map`**: `ε(D, U₀) ∘ Λ[m] ∘ κ = ε(D, U₁) ∘ Λ[m'] ∘ κ` when `prdMapR ≫ m = m'`;
* **`locCls_opn_toOpEt`**: for `σ : opEt U₁ ⟶ T` and `D ×_P U₀` over `U₁`:
  `ε(D, U₀) ∘ Λ[toOpEt ≫ σ] ∘ κ = ε(D, U₁) ∘ Λ[prT ≫ σ] ∘ κ`.
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

section LocU

variable {U₁ U₀ Uz : P.Opens} (h₁₀ : U₁ ≤ U₀) (h : U₀ ≤ Uz) (h₁ : U₁ ≤ Uz) (D : P.Etale)

/-- The class of `κ` through `U₀` is the class of its pullback through `U₁`. -/
theorem locCls_opn (hS₁ : (locC Λ D h₁).ShortExact) (hS : (locC Λ D h).ShortExact) {F : EtSh Λ P}
    (κ : Ext.{u} (freeSh Λ (prd D (opEt U₀))) F 1) :
    hS.extClass.comp κ (show 1 + 1 = 2 from rfl) =
      hS₁.extClass.comp ((Ext.mk₀ (freeMap Λ (prdMapR D (opEtMap h₁₀)))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) := by
  rw [← locC_opn h₁₀ h h₁ D hS₁ hS, Ext.comp_assoc_of_second_deg_zero]

end LocU

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1a =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point

GLOB/REL PLAN v1, stage S2 input (`h1` of `exists_approx_crt`, O2Ap1). Over an algebraically closed `k`:
* `exists_const_add_mul`: if `B` is unramified and essentially of finite type over `k[X]` and `q` is the only maximal
  ideal containing `t = X - a`, then every `x : B` is `c₀ + t·y` with `c₀ ∈ k[X]`;
* `chart_h1`: the same for a chart `Spec B ⟶ A¹ ⟶ P` with exactly one geometric point over `c(X = a)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtDeg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDed

universe u

section Alg

variable {k : Type u} [Field k]

variable {B : Type u} [CommRing B] [Algebra k[X] B] [Algebra.EssFiniteType k[X] B]
  [Algebra.FormallyUnramified k[X] B]

theorem exists_const_add_mul [IsAlgClosed k] (a : k) (q : Ideal B) [q.IsMaximal]
    (hq : algebraMap k[X] B (X - C a) ∈ q)
    (huniq : ∀ n : Ideal B, n.IsMaximal → algebraMap k[X] B (X - C a) ∈ n → n = q) (x : B) :
    ∃ c₀ : k[X], ∃ y : B, x = algebraMap k[X] B c₀ + algebraMap k[X] B (X - C a) * y := by
  let p : Ideal k[X] := Ideal.span {X - C a}
  have hpm : p.IsMaximal := isMaximal_span_X_sub_C a
  have hunder : q.under k[X] = p := span_X_sub_C_eq_of_mem a _ hq
  have hspan := span_eq_of_unique k[X] B q (X - C a) hunder (hunder ▸ hpm) huniq
  have hmap : p.map (algebraMap k[X] B) = q := by
    rw [Ideal.map_span, Set.image_singleton]; exact hspan
  have : (p.map (algebraMap k[X] B)).IsMaximal := hmap ▸ inferInstance
  let : Field (k[X] ⧸ p) := Ideal.Quotient.field p
  have : Module.Free (k[X] ⧸ p) (B ⧸ p.map (algebraMap k[X] B)) := Module.Free.of_divisionRing _ _
  have : Module.Finite (k[X] ⧸ p) (B ⧸ p.map (algebraMap k[X] B)) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  have : IsAlgClosed (k[X] ⧸ p) :=
    IsAlgClosed.of_ringEquiv k _ (quotientSpanXSubCAlgEquiv a).symm.toRingEquiv
  obtain ⟨κ, hκ⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k[X] ⧸ p)
    (K := B ⧸ p.map (algebraMap k[X] B))).2 (Ideal.Quotient.mk _ x)
  obtain ⟨c₀, rfl⟩ := Ideal.Quotient.mk_surjective κ
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.eq, hmap, ← hspan,
    Ideal.mem_span_singleton'] at hκ
  obtain ⟨y, hy⟩ := hκ
  exact ⟨c₀, -y, by rw [mul_neg, mul_comm, hy]; ring⟩

end Alg

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4b =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer

* `exists_hj_pair'`: `exists_hj_pair` (O2PP4a) with `u = x / y` given as an equation;
* `isUnit_locF_comp_of_dvd`: `r ∣ F` is a unit on `D_{φ F}`;
* `wm_gamMap_pow_mul`: `(wm (prdMap dm))^*` of `r = t^e r'` along `shG`;
* `isUnit_gamMap_shG`: units of `B₁` stay units on `W₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section HJ'

end HJ'

section ChartS1

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {Uo : P.Opens} (R : P.Etale) [IsAffine R.left] {a : k}

theorem isUnit_gamMap_shG {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
    [IsAffine (prd (chEt c φ₁) (opEt Uo)).left] {r : k[X]} (h : IsUnit (φ₁.hom r)) :
    IsUnit (gamMap (shG c φ₁ (Uo := Uo) R) r) := by
  rw [gamMap_shG c R φ₁ r]
  exact h.map _

end ChartS1

end RamanujanPetersson.EtPBC.EtKum

end

end


