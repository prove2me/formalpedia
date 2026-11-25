-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_010
-- name    : RPLib_FX_EtPBC_010
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T18:40:03.90695+00:00
-- url     : https://prove2.me/theorems/b16a78ac-0227-53d1-a440-f35ad46b2ae4
-- title:
--   Proper base change for the projective line, library file 010
-- statement:
--   File 010 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Kummer_Lev`: S4-Kummer, part K5b: Kummer roots at a constant level `F_m = F ⊗ 𝔽_{q^m}`
--   * `S4.Def_RP_EtCompact_GalTr`: S4-EtCompact (b3a): Galois actions on stalks along etale maps and isomorphisms of geometric points
--   * `S4.Def_RP_EtCompact_GGerm`: S4-EtCompact, (c) T1 SpOne part 1: germs of global sections
--   * `S4.Def_RP_EtPBC_A_FreeSh`: S4-EtPBC-A, L1a: free sheaves on objects of the small etale site
--   * `S4.Def_RP_EtPBC_A_ConstVal`: S4-EtPBC-A, M2a: values of sections of a constant sheaf
--   * `S4.Def_RP_EtPBC_A_CovAs1b`: S4-EtPBC-A, R4-T2 (A3 assembly, As1b): finiteness and noetherianity of base-changed charts
--   * `S4.Def_RP_EtPBC_A_Z1Core`: S4-EtPBC-A, (Z1) algebraic core: a degree bound on the two charts of `P¹_A`
--   * `S4.Def_RP_EtPBC_A_Z1Two`: S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module
--   * `S4.Def_RP_EtPBC_A_CovUnr`: S4-EtPBC-A, R4-T2 (A2c-5c): unramified at the primes over `J` (Nakayama on `Ω`)
--   * `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
--   * `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
--   * `S4.Def_RP_EtPBC_A_CovPr7`: S4-EtPBC-A, R4-T2 (A3g): flat descent of vanishing tensors to finitely generated subalgebras
--   * `S4.Def_RP_EtPBC_A_CovAs5b`: S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`
--   * `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
--   * `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_StkRD`: S4-EtPBC-A, L1b: stalks of derived pushforwards
--   * `S4.Def_RP_EtPBC_A_SecCoc`: S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes
--   * `S4.Def_RP_EtPBC_A_SecNat`: S4-EtPBC-A, L1c': naturality of `secExt` in the etale object
--   * `S4.Def_RP_EtPBC_A_FBInj`: S4-EtPBC-A, M2 F3: base change on germs of a constant sheaf (degree `0`)
--   * `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
--   * `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
--   * `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
--   * `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
--   * `S4.Def_RP_EtPBC_A_PushKill`: S4-EtPBC-A, R4-T3c: effacement through an etale neighbourhood by a pushout
--   * `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--   * `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
--   * `S4.Def_RP_EtPBC_A_ESheet`: S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_EPsiRel`: S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres
--   * `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_O2E1`: S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain
--   * `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
--   * `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
--   * `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
--   * `S4.Def_RP_EtPBC_A_O2P2`: S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)
--   * `S4.Def_RP_EtPBC_A_O2Gl1d`: S4-EtPBC-A, O2 GLOB (O2Gl1d): transfer of `u` to the shrunk chart, CRT ideals at the bad points
--   * `S4.Def_RP_EtPBC_A_O2PP4a`: S4-EtPBC-A, O2 PP' (O2PP4a): generic glue for the S1 layer
--   * `S4.Def_RP_EtPBC_A_O2PP4b`: S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_001
import Definitions.Def_RPLib_FX_EtPBC_002
import Definitions.Def_RPLib_FX_EtPBC_003
import Definitions.Def_RPLib_FX_EtPBC_004

/-!
# Proper base change for the projective line, library file 010

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Kummer_Lev`: S4-Kummer, part K5b: Kummer roots at a constant level `F_m = F ⊗ 𝔽_{q^m}`
* `S4.Def_RP_EtCompact_GalTr`: S4-EtCompact (b3a): Galois actions on stalks along etale maps and isomorphisms of geometric points
* `S4.Def_RP_EtCompact_GGerm`: S4-EtCompact, (c) T1 SpOne part 1: germs of global sections
* `S4.Def_RP_EtPBC_A_FreeSh`: S4-EtPBC-A, L1a: free sheaves on objects of the small etale site
* `S4.Def_RP_EtPBC_A_ConstVal`: S4-EtPBC-A, M2a: values of sections of a constant sheaf
* `S4.Def_RP_EtPBC_A_CovAs1b`: S4-EtPBC-A, R4-T2 (A3 assembly, As1b): finiteness and noetherianity of base-changed charts
* `S4.Def_RP_EtPBC_A_Z1Core`: S4-EtPBC-A, (Z1) algebraic core: a degree bound on the two charts of `P¹_A`
* `S4.Def_RP_EtPBC_A_Z1Two`: S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module
* `S4.Def_RP_EtPBC_A_CovUnr`: S4-EtPBC-A, R4-T2 (A2c-5c): unramified at the primes over `J` (Nakayama on `Ω`)
* `S4.Def_RP_EtPBC_A_CovEt`: S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`
* `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
* `S4.Def_RP_EtPBC_A_CovPr7`: S4-EtPBC-A, R4-T2 (A3g): flat descent of vanishing tensors to finitely generated subalgebras
* `S4.Def_RP_EtPBC_A_CovAs5b`: S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`
* `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
* `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_StkRD`: S4-EtPBC-A, L1b: stalks of derived pushforwards
* `S4.Def_RP_EtPBC_A_SecCoc`: S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes
* `S4.Def_RP_EtPBC_A_SecNat`: S4-EtPBC-A, L1c': naturality of `secExt` in the etale object
* `S4.Def_RP_EtPBC_A_FBInj`: S4-EtPBC-A, M2 F3: base change on germs of a constant sheaf (degree `0`)
* `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
* `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
* `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
* `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
* `S4.Def_RP_EtPBC_A_PushKill`: S4-EtPBC-A, R4-T3c: effacement through an etale neighbourhood by a pushout
* `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
* `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
* `S4.Def_RP_EtPBC_A_ESheet`: S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`
* `S4.Def_RP_EtPBC_A_EPsiRel`: S4-EtPBC-A, M4(E), EPsiRel: relations in `π_* C` are read off on the closed points of the fibres
* `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
* `S4.Def_RP_EtPBC_A_O2E1`: S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain
* `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
* `S4.Def_RP_EtPBC_A_O2N1a`: S4-EtPBC-A, O2 M5 N1a: Galois transport along an etale map, and `Λ_U ≅ g^* Λ_X` with `1 ↦ 1`
* `S4.Def_RP_EtPBC_A_O2N1c`: S4-EtPBC-A, O2 M5 N1c: point transport and restriction of `κ`-classes along an etale map (NAT)
* `S4.Def_RP_EtPBC_A_O2P2`: S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)
* `S4.Def_RP_EtPBC_A_O2Gl1d`: S4-EtPBC-A, O2 GLOB (O2Gl1d): transfer of `u` to the shrunk chart, CRT ideals at the bad points
* `S4.Def_RP_EtPBC_A_O2PP4a`: S4-EtPBC-A, O2 PP' (O2PP4a): generic glue for the S1 layer
* `S4.Def_RP_EtPBC_A_O2PP4b`: S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_Kummer_Lev =====
section

/-!
# S4-Kummer, part K5b: Kummer roots at a constant level `F_m = F ⊗ 𝔽_{q^m}`

`A = Rfin(F)`, `K = F`, `F_m = Fc Fq F K̄ m ⊆ K̄ = AlgebraicClosure F`.

* `valuation_comap`: valuations are transported along a ring isomorphism of Dedekind domains that commutes with the maps to
  a common fraction field.
* `isIntegral_iff_mem_Rfin` (constant field extension `F'/F`): `x ∈ F'` is integral over `Rfin(F)` iff `x ∈ Rfin(F')`.
* `Fc_eq_constLevel`: `F_m = constLevel F p (e m)` when `#Fq = p ^ e`; `Fc_mem_unramSet`.
* `perfect_Rfin`: residue fields of `Rfin(F)` at maximal ideals are perfect (finite).
* `forall_dvd_ord_iff`: for `a ∈ F_m^×` and `N` invertible: `N ∣ ord_v a` at every finite place `v` of `F_m` iff every
  `N`-th root of `a` lies in `K_U = maxUnram (Rfin F) F`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain
open scoped Polynomial

namespace RamanujanPetersson
namespace Kummer

noncomputable section

section Transport

variable {B1 B2 M : Type*} [CommRing B1] [IsDedekindDomain B1] [CommRing B2] [IsDedekindDomain B2]
  [Field M] [Algebra B1 M] [Algebra B2 M] [IsFractionRing B1 M] [IsFractionRing B2 M]

/-- **Transport of valuations** along `e : B1 ≃+* B2` compatible with the maps to `M`. -/
theorem valuation_comap (e : B1 ≃+* B2) (he : ∀ b, algebraMap B2 M (e b) = algebraMap B1 M b)
    (w : HeightOneSpectrum B2) (x : M) :
    (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).valuation M x = w.valuation M x := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B1) x
  rw [map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_comap, intValuation_comap, ← he a, ← he s,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

end Transport

section Generic

open PicDescent

end Generic

section GenericLev

end GenericLev

section Lev

open PicDescent

end Lev

end

end Kummer
end RamanujanPetersson


end

-- ===== S4.Def_RP_EtCompact_GalTr =====
section

/-!
# S4-EtCompact (b3a): Galois actions on stalks along etale maps and isomorphisms of geometric points

* `resFib_stalkAut`: the germ isomorphism `resFib g t : (res g F)_t ≅ F_(t ≫ g)` intertwines the action of an
  automorphism `τ` of `Spec Ω` over `U` on both sides;
* `autHom_ptIso`: across an isomorphism `e` of geometric points, `τ` on the target corresponds to
  `e.hom.left ≫ τ ≫ e.inv.left` on the source (`ptIso e`), and `stalkAut_ptIso` on stalks;
* for an open immersion `g` and `y : U`: `sepO g y : Ω_(g y) ≃ Ω_y` (behind `StkTr.mapPtIso`), the Galois transport
  `galTr g y : Gal (g y) → Gal y` (`galTrHom`, `galTr_left`), `resTrIso g y Λ F : (g^* F)_y ≅ F_(g y)` and
  **`stalkAut_resTr`**: `resTrIso` carries `galRep (g^* F) y (galTr σ)` to `galRep F (g y) σ`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTr

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Res

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] (t : GeomPt U)

theorem liftX_autHom {τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω)} (hτ : τ ≫ t.pt = t.pt)
    {W : U.Etale} (b : t.point.fiber.obj W) :
    liftX g t ((t.autHom τ hτ).hom.app W b) =
      ((t.map g).autHom τ (map_aut g t hτ)).hom.app ((etComp g).obj W) (liftX g t b) :=
  Over.OverMorphism.ext rfl

variable (Λ : Type u) [CommRing Λ]

/-- **`resFib` is equivariant** for automorphisms `τ` of `Spec Ω` over `U`. -/
theorem resFib_stalkAut {τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω)} (hτ : τ ≫ t.pt = t.pt)
    (F : EtSh Λ X) :
    (t.stalkAut Λ τ hτ).app ((res g Λ).obj F) ≫ resFib g t Λ F =
      resFib g t Λ F ≫ ((t.map g).stalkAut Λ τ (map_aut g t hτ)).app F := by
  refine GrothendieckTopology.Point.presheafFiber_hom_ext _ (fun W b => ?_)
  erw [← Category.assoc, germ_stalkAut, germ_resFib, germ_resFib_assoc, germ_stalkAut, liftX_autHom]

end Res

section Pt

end Pt

section Open

end Open

end RamanujanPetersson.EtCompact.GalTr

end

end

-- ===== S4.Def_RP_EtCompact_GGerm =====
section

/-!
# S4-EtCompact, (c) T1 SpOne part 1: germs of global sections

For a geometric point `t` of `Y` and a global section `z` of `F` (a section over `etId Y`),
**`gg t F z`** is its germ at `t` (over `etId Y` at the unique fibre element `t.top`).
* `toEtId_ext` (maps to `etId Y` are unique), `germ_restrict` (the germ of a restriction of `z` is `gg z`);
* `map_gg` (sheaf maps), `sheafFiber_gg` (morphisms of points), `resFib_gg` (stalks of a restriction),
  `resTrIso_gg`, `resTrIso_inv_gg`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

universe u

namespace RamanujanPetersson.EtCompact.GGerm

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTr

variable {Λ : Type u} [CommRing Λ]

section Gen

variable {Y : Scheme.{u}}

/-- The germ of a restriction of a global section is its global germ. -/
theorem germ_restrict (t : GeomPt Y) (F : EtSh Λ Y) {W : Y.Etale} (a : t.point.fiber.obj W) (f : W ⟶ etId Y)
    (z : F.obj.obj (op (etId Y))) :
    (t.point.toPresheafFiber W a F.obj).hom ((F.obj.map f.op).hom z) = gg t F z := by
  have h := GrothendieckTopology.Point.toPresheafFiber_w (A := ModuleCat.{u} Λ) t.point f a F.obj
  rw [t.eq_top (t.point.fiber.map f a)] at h
  exact congrArg (fun φ => ModuleCat.Hom.hom φ z) h

/-- Morphisms of points on global germs. -/
theorem sheafFiber_gg {t₁ t₂ : GeomPt Y} (f : t₁.point ⟶ t₂.point) (F : EtSh Λ Y)
    (z : F.obj.obj (op (etId Y))) :
    ((GrothendieckTopology.Point.Hom.sheafFiber (A := ModuleCat.{u} Λ) f).app F).hom (gg t₂ F z) =
      gg t₁ F z := by
  have e1 : t₂.point.toPresheafFiber (etId Y) t₂.top F.obj ≫
      (GrothendieckTopology.Point.Hom.presheafFiber (A := ModuleCat.{u} Λ) f).app F.obj =
      t₁.point.toPresheafFiber (etId Y) (f.hom.app (etId Y) t₂.top) F.obj := by
    simp only [GrothendieckTopology.Point.Hom.presheafFiber_app,
      GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc]
  rw [t₁.eq_top (f.hom.app (etId Y) t₂.top)] at e1
  exact congrArg (fun φ => ModuleCat.Hom.hom φ z) e1

end Gen

section Res

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] (t : GeomPt U)

/-- `resFib` on the global germ of a restricted global section. -/
theorem resFib_gg (F : EtSh Λ X) (r : (etComp g).obj (etId U) ⟶ etId X) (z : F.obj.obj (op (etId X))) :
    (resFib g t Λ F).hom (gg t ((res g Λ).obj F) ((F.obj.map r.op).hom z)) = gg (t.map g) F z :=
  (resFib_germ g t Λ F (etId U) t.top ((F.obj.map r.op).hom z)).trans
    (germ_restrict (t.map g) F (liftX g t t.top) r z)

end Res

section Tr

end Tr

end RamanujanPetersson.EtCompact.GGerm

end

end

-- ===== S4.Def_RP_EtPBC_A_FreeSh =====
section

/-!
# S4-EtPBC-A, L1a: free sheaves on objects of the small etale site

For `W : X.Etale`, `freeSh Λ W` is the sheafification of `V ↦ Λ[Hom(V, W)]`. It represents evaluation at `W`:
`freeEquiv Λ W F : (freeSh Λ W ⟶ F) ≃+ F(W)`, natural in `F` and in `W`. With Mathlib's `Ext`, the groups
`Ext^q(freeSh Λ W, F)` are the cohomology of `W` with coefficients in `F` and carry long exact sequences in `F`;
the stalks of derived pushforwards are computed with them (unit S4-EtPBC-A, layer L1).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

/-- Maps of presheaves out of `freePre Λ W` are elements of `P(W)`. -/
def preEquiv (W : X.Etale) (P : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ) :
    (freePre Λ W ⟶ P) ≃ P.obj (op W) where
  toFun α := α.app (op W) (ModuleCat.freeMk (𝟙 W))
  invFun m :=
    { app := fun V => ModuleCat.freeDesc (TypeCat.ofHom (fun h : (unop V ⟶ W) => (P.map h.op).hom m))
      naturality := by
        intro V V' f
        apply ModuleCat.free_hom_ext
        intro h
        simp [freePre] }
  left_inv α := by
    ext V : 2
    apply ModuleCat.free_hom_ext
    intro h
    have e := NatTrans.naturality_apply (φ := α) h.op (ModuleCat.freeMk (R := Λ) (𝟙 W))
    have e2 : (freePre Λ W).map h.op (ModuleCat.freeMk (R := Λ) (𝟙 W)) = ModuleCat.freeMk h := by
      simp [freePre]
    rw [e2] at e
    refine Eq.trans ?_ e.symm
    exact ModuleCat.freeDesc_apply _ _
  right_inv m := by
    simp

theorem preEquiv_apply (W : X.Etale) (P : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ) (α : freePre Λ W ⟶ P) :
    preEquiv Λ W P α = α.app (op W) (ModuleCat.freeMk (𝟙 W)) := rfl

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_ConstVal =====
section

/-!
# S4-EtPBC-A, M2a: values of sections of a constant sheaf

For `c ∈ M_Y(T)` and `w ∈ T.left`, `cval c w ∈ M` is the value of `c` near `w` (a local constant representation
`c|_V = constUnit n` exists by local surjectivity of the sheafification unit).
* **`cval_germ`**: at ANY geometric point `t` and fibre point `a` over `w`, `constStalkIso (germ_a c) = cval c w`;
* `cval_map` (restriction), `cval_constUnit`, `cval_add`, `cval_zero`, **`isLocallyConstant_cval`**;
* `mem_supp_iff_cval`: `w ∈ supp c ↔ cval c w ≠ 0`;
* **`exists_indicator`**: for a clopen `O ⊆ T.left` and `n ∈ M` a section with values `n` on `O` and `0` off `O`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} {M : ModuleCat.{u} Λ}

/-- The value of `c` at `w`. -/
def cval {T : Y.Etale} (c : (constSh Λ Y M).obj.obj (op T)) (w : T.left) : M :=
  (exists_locRep c w).choose

theorem cval_spec {T : Y.Etale} (c : (constSh Λ Y M).obj.obj (op T)) (w : T.left) :
    ∃ (V : Y.Etale) (f : V ⟶ T) (v : V.left), f.left v = w ∧
      ((constSh Λ Y M).obj.map f.op).hom c = (constUnit M V).hom (cval c w) :=
  (exists_locRep c w).choose_spec

/-- **Germs of a section of a constant sheaf are its values**, at every geometric point. -/
theorem cval_germ (t : GeomPt Y) {T : Y.Etale} (c : (constSh Λ Y M).obj.obj (op T)) (a : t.point.fiber.obj T) :
    (constStalkIso Λ t M).hom.hom ((t.point.toPresheafFiber T a (constSh Λ Y M).obj).hom c) =
      cval c ((t.liftOf a).left (default : Spec (CommRingCat.of t.Ω))) := by
  obtain ⟨V, f, v, hv, hc⟩ := cval_spec c ((t.liftOf a).left (default : Spec (CommRingCat.of t.Ω)))
  obtain ⟨b, hb, -⟩ := exists_lift_fib' t f a v hv
  have h1 := congrArg (fun φ => φ.hom c) (t.point.toPresheafFiber_w f b (constSh Λ Y M).obj)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [hb] at h1
  have h2 := congrArg (fun φ => φ.hom (cval c ((t.liftOf a).left (default : Spec (CommRingCat.of t.Ω))))) (constUnit_germ t M V b)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [← h1, hc, h2]
  change ((constStalkIso Λ t M).inv ≫ (constStalkIso Λ t M).hom).hom _ = _
  rw [Iso.inv_hom_id]
  rfl

theorem cval_eq (t : GeomPt Y) {T : Y.Etale} (c : (constSh Λ Y M).obj.obj (op T)) (a : t.point.fiber.obj T)
    {w : T.left} (hw : (t.liftOf a).left (default : Spec (CommRingCat.of t.Ω)) = w) :
    cval c w = (constStalkIso Λ t M).hom.hom ((t.point.toPresheafFiber T a (constSh Λ Y M).obj).hom c) := by
  rw [← hw]
  exact (cval_germ t c a).symm

/-- Values of restrictions. -/
theorem cval_map {V T : Y.Etale} (f : V ⟶ T) (c : (constSh Λ Y M).obj.obj (op T)) (v : V.left) :
    cval (((constSh Λ Y M).obj.map f.op).hom c) v = cval c (f.left v) := by
  obtain ⟨a, ha⟩ := exists_fib_over V v
  have hv' : ((geomPtAt (V.hom v)).liftOf ((geomPtAt (V.hom v)).point.fiber.map f a)).left
      (default : Spec (CommRingCat.of (geomPtAt (V.hom v)).Ω)) =
      f.left v := by
    exact congrArg (fun p => f.left p) ha
  have h1 := congrArg (fun φ => φ.hom c) ((geomPtAt (V.hom v)).point.toPresheafFiber_w f a (constSh Λ Y M).obj)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [cval_eq _ _ a ha, cval_eq _ c _ hv']
  exact congrArg (fun z => (constStalkIso Λ (geomPtAt (V.hom v)) M).hom.hom z) h1

theorem cval_constUnit {T : Y.Etale} (n : M) (w : T.left) : cval ((constUnit M T).hom n) w = n := by
  obtain ⟨a, ha⟩ := exists_fib_over T w
  have h2 := congrArg (fun φ => φ.hom n) (constUnit_germ (geomPtAt (T.hom w)) M T a)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : (constStalkIso Λ (geomPtAt (T.hom w)) M).hom.hom ((constStalkIso Λ (geomPtAt (T.hom w)) M).inv.hom n) = n := by
    change ((constStalkIso Λ _ M).inv ≫ (constStalkIso Λ _ M).hom).hom n = n
    rw [Iso.inv_hom_id]
    rfl
  exact (cval_eq _ _ a ha).trans ((congrArg (fun z => (constStalkIso Λ (geomPtAt (T.hom w)) M).hom.hom z) h2).trans h3)

theorem cval_add {T : Y.Etale} (c c' : (constSh Λ Y M).obj.obj (op T)) (w : T.left) :
    cval (c + c') w = cval c w + cval c' w := by
  obtain ⟨a, ha⟩ := exists_fib_over T w
  exact (cval_eq _ _ a ha).trans ((congrArg (fun z => (constStalkIso Λ (geomPtAt (T.hom w)) M).hom.hom z)
    (map_add _ c c')).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) (cval_eq _ c a ha).symm (cval_eq _ c' a ha).symm)))

theorem cval_zero {T : Y.Etale} (w : T.left) : cval (0 : (constSh Λ Y M).obj.obj (op T)) w = 0 := by
  obtain ⟨a, ha⟩ := exists_fib_over T w
  exact (cval_eq _ _ a ha).trans ((congrArg (fun z => (constStalkIso Λ (geomPtAt (T.hom w)) M).hom.hom z)
    (map_zero _)).trans (map_zero _))

theorem cval_sum {T : Y.Etale} {ι : Type*} (s : Finset ι) (c : ι → (constSh Λ Y M).obj.obj (op T)) (w : T.left) :
    cval (∑ i ∈ s, c i) w = ∑ i ∈ s, cval (c i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact cval_zero w
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, cval_add, ih]

/-- **Values are locally constant.** -/
theorem isLocallyConstant_cval {T : Y.Etale} (c : (constSh Λ Y M).obj.obj (op T)) :
    IsLocallyConstant (cval c) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun w => ?_
  obtain ⟨V, f, v, hv, hc⟩ := cval_spec c w
  refine ⟨Set.range f.left, f.left.isOpenMap.isOpen_range, ⟨v, hv⟩, ?_⟩
  rintro _ ⟨v', rfl⟩
  rw [← cval_map, hc, cval_constUnit]

/-- The support of a section of a constant sheaf is where its value is nonzero. -/
theorem mem_supp_iff_cval {T : Y.Etale} (c : (constSh Λ Y M).obj.obj (op T)) (w : T.left) :
    w ∈ supp (constSh Λ Y M) c ↔ cval c w ≠ 0 := by
  constructor
  · rintro ⟨y, a, ha, hne⟩ h0
    apply hne
    have e : (constStalkIso Λ (geomPtAt y) M).hom.hom
        (((geomPtAt y).point.toPresheafFiber T a (constSh Λ Y M).obj).hom c) = 0 :=
      (cval_eq (geomPtAt y) c a ha).symm.trans h0
    have e2 := congrArg (fun z => (constStalkIso Λ (geomPtAt y) M).inv.hom z) e
    simp only [map_zero] at e2
    refine Eq.trans ?_ e2
    change _ = ((constStalkIso Λ (geomPtAt y) M).hom ≫ (constStalkIso Λ (geomPtAt y) M).inv).hom _
    rw [Iso.hom_inv_id]
    rfl
  · intro h
    obtain ⟨a, ha⟩ := exists_fib_over T w
    exact ⟨T.hom w, a, ha, fun h0 => h ((cval_eq _ _ a ha).trans
      ((congrArg (fun z => (constStalkIso Λ (geomPtAt (T.hom w)) M).hom.hom z) h0).trans (map_zero _)))⟩

/-- **Indicator sections** of clopen subsets. -/
theorem exists_indicator {T : Y.Etale} (O : Set T.left) (hO : IsClopen O) (n : M) :
    ∃ c : (constSh Λ Y M).obj.obj (op T), ∀ w : T.left, cval c w = O.indicator (fun _ => n) w := by
  classical
  let R : Sieve T :=
    { arrows := fun _ f => Set.range f.left ⊆ O ∨ Set.range f.left ⊆ Oᶜ
      downward_closed := fun {_ _} {f} hf g => by
        have hs : Set.range (g ≫ f).left ⊆ Set.range f.left := by
          rintro _ ⟨z, rfl⟩
          exact ⟨g.left z, rfl⟩
        rcases hf with hf | hf
        · exact Or.inl (hs.trans hf)
        · exact Or.inr (hs.trans hf) }
  let U₁ : T.left.Opens := ⟨O, hO.isOpen⟩
  let U₂ : T.left.Opens := ⟨Oᶜ, hO.isClosed.isOpen_compl⟩
  have hU₁ : Set.range (opnι T U₁).left ⊆ O := by
    rintro _ ⟨z, rfl⟩
    exact opnι_mem T U₁ z
  have hU₂ : Set.range (opnι T U₂).left ⊆ Oᶜ := by
    rintro _ ⟨z, rfl⟩
    exact opnι_mem T U₂ z
  have hR : R ∈ Y.smallEtaleTopology T := (mem_smallEtale_iff T R).2 fun w => by
    by_cases hw : w ∈ O
    · obtain ⟨z, hz⟩ : w ∈ Set.range U₁.ι := (Scheme.Opens.range_ι U₁).symm ▸ hw
      exact ⟨opn T U₁, opnι T U₁, z, Or.inl hU₁, hz⟩
    · obtain ⟨z, hz⟩ : w ∈ Set.range U₂.ι := (Scheme.Opens.range_ι U₂).symm ▸ hw
      exact ⟨opn T U₂, opnι T U₂, z, Or.inr hU₂, hz⟩
  let x : ∀ ⦃V : Y.Etale⦄ (f : V ⟶ T), R f → (constSh Λ Y M).obj.obj (op V) :=
    fun V f _ => if Set.range f.left ⊆ O then (constUnit M V).hom n else 0
  have hx : ∀ ⦃V₁ V₂ W : Y.Etale⦄ (f₁ : V₁ ⟶ T) (f₂ : V₂ ⟶ T) (h₁ : R f₁) (h₂ : R f₂) (g₁ : W ⟶ V₁)
      (g₂ : W ⟶ V₂), g₁ ≫ f₁ = g₂ ≫ f₂ → ((constSh Λ Y M).obj.map g₁.op).hom (x f₁ h₁) =
        ((constSh Λ Y M).obj.map g₂.op).hom (x f₂ h₂) := by
    intro V₁ V₂ W f₁ f₂ h₁ h₂ g₁ g₂ e
    by_cases hW : IsEmpty W.left
    · refine sep_eq (constSh Λ Y M) ⊥ ((mem_smallEtale_iff W ⊥).2 fun w => (hW.false w).elim) _ _ ?_
      intro _ _ hf
      exact hf.elim
    obtain ⟨w0⟩ := not_isEmpty_iff.1 hW
    have hp : f₁.left (g₁.left w0) = f₂.left (g₂.left w0) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun φ => φ.left w0) e
    by_cases c₁ : Set.range f₁.left ⊆ O <;> by_cases c₂ : Set.range f₂.left ⊆ O
    · simp only [x, c₁, c₂, if_true]
      rw [SgUnit.cU_map, SgUnit.cU_map]
    · exfalso
      rcases h₂ with h₂ | h₂
      · exact c₂ h₂
      · exact h₂ ⟨g₂.left w0, rfl⟩ (hp ▸ c₁ ⟨g₁.left w0, rfl⟩)
    · exfalso
      rcases h₁ with h₁ | h₁
      · exact c₁ h₁
      · exact h₁ ⟨g₁.left w0, rfl⟩ (hp.symm ▸ c₂ ⟨g₂.left w0, rfl⟩)
    · simp only [x, c₁, c₂, if_false, map_zero]
  obtain ⟨c, hc, -⟩ := existsUnique_glueS (constSh Λ Y M) R hR x hx
  refine ⟨c, fun w => ?_⟩
  by_cases hw : w ∈ O
  · obtain ⟨z, hz⟩ : w ∈ Set.range U₁.ι := (Scheme.Opens.range_ι U₁).symm ▸ hw
    have h1 := hc (opnι T U₁) (Or.inl hU₁)
    simp only [x, hU₁, if_true] at h1
    have e1 : cval c ((opnι T U₁).left z) = n :=
      (cval_map (opnι T U₁) c z).symm.trans ((congrArg (fun d => cval d z) h1).trans (cval_constUnit (T := opn T U₁) n z))
    rw [Set.indicator_of_mem hw]
    exact hz ▸ e1
  · obtain ⟨z, hz⟩ : w ∈ Set.range U₂.ι := (Scheme.Opens.range_ι U₂).symm ▸ hw
    have hn : ¬ Set.range (opnι T U₂).left ⊆ O := fun h => hw (h ⟨z, hz⟩)
    have h1 := hc (opnι T U₂) (Or.inr hU₂)
    simp only [x, hn, if_false] at h1
    have e1 : cval c ((opnι T U₂).left z) = 0 :=
      (cval_map (opnι T U₂) c z).symm.trans ((congrArg (fun d => cval d z) h1).trans (cval_zero (Λ := Λ) (M := M) (T := opn T U₂) z))
    rw [Set.indicator_of_notMem hw]
    exact hz ▸ e1

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs1b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As1b): finiteness and noetherianity of base-changed charts

For an `A[X]`-algebra `B` (with `A → A[X] → B` a tower) and any `A`-algebra `S`:
* `eval_map_bc`: `eval₂ (S → S ⊗ B) (1 ⊗ X) (c.map (algebraMap A S)) = 1 ⊗ c` for `c : A[X]`.
* `fin_bc_aux` (generic `f`), **`fin_bc`**: if `B` is finite over `A[X]`, then `S ⊗[A] B` is finite over `S[X]` via `X ↦ 1 ⊗ X`.
* **`noeth_bc`**: if moreover `S` is noetherian, `S ⊗[A] B` is noetherian.
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section BCFin

variable {A S B : Type u} [CommRing A] [CommRing S] [Algebra A S] [CommRing B] [Algebra A[X] B] [Algebra A B]
  [IsScalarTower A A[X] B]

/-- **Base change of a finite `A[X]`-algebra**: `S ⊗[A] B` is finite over `S[X]` (`X ↦ 1 ⊗ X`). -/
theorem fin_bc [Module.Finite A[X] B] :
    (eval₂RingHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B)
      ((1 : S) ⊗ₜ[A] algebraMap A[X] B X)).Finite :=
  fin_bc_aux _ eval_map_bc (fun s₀ => by
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Algebra.TensorProduct.includeLeftRingHom_apply])

/-- **Base-changed charts are noetherian** over a noetherian `S`. -/
theorem noeth_bc [Module.Finite A[X] B] [IsNoetherianRing S] : IsNoetherianRing (S ⊗[A] B) := by
  letI := (eval₂RingHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B)
      ((1 : S) ⊗ₜ[A] algebraMap A[X] B X)).toAlgebra
  haveI : Module.Finite S[X] (S ⊗[A] B) := fin_bc (A := A) (S := S) (B := B)
  exact IsNoetherianRing.of_finite S[X] (S ⊗[A] B)

end BCFin

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z1Core =====
section

/-!
# S4-EtPBC-A, (Z1) algebraic core: a degree bound on the two charts of `P¹_A`

* **`exists_deg_bound`**: for a finitely generated `A[X]`-submodule `K ⊆ A[X]^r` there is `e` such that
  whenever `X^D • p - q ∈ K` with `deg q ≤ D`, the vector `p` is congruent mod `K` to a vector of degree `< e`.
* **`exists_fg_of_twoChart`**: for `A` noetherian and an `A[X]`-linear `π : A[X]^r → N`, all elements `π p`
  with `X^D • π p = π q`, `deg q ≤ D` (the sections of the image sheaf over both charts of `P¹_A`, written in
  the coordinate `X` of the first chart) lie in one finitely generated `A`-submodule of `N`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Z1

universe u v w

variable {A : Type u} [CommRing A]

/-- **Finiteness on the two charts**: the elements `π p` that are also sections over the second chart lie in
one finitely generated `A`-submodule. -/
theorem exists_fg_of_twoChart [IsNoetherianRing A] {N : Type w} [AddCommGroup N] [Module A[X] N] [Module A N]
    [IsScalarTower A A[X] N] {ι : Type v} [Fintype ι] (π : (ι → A[X]) →ₗ[A[X]] N) :
    ∃ M : Submodule A N, M.FG ∧ ∀ (p : ι → A[X]) (D : ℕ) (q : ι → A[X]),
      (∀ i, (q i).natDegree ≤ D) → (X ^ D : A[X]) • π p = π q → π p ∈ M := by
  classical
  obtain ⟨e, he⟩ := exists_deg_bound (LinearMap.ker π) (IsNoetherian.noetherian _)
  have : Module.Finite A (degreeLT A e) := Module.Finite.equiv (degreeLTEquiv A e).symm
  let Ψ : (ι → degreeLT A e) →ₗ[A] (ι → A[X]) :=
    LinearMap.pi fun i => (degreeLT A e).subtype ∘ₗ LinearMap.proj i
  refine ⟨LinearMap.range ((π.restrictScalars A) ∘ₗ Ψ), ?_, ?_⟩
  · rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · intro p D q hq hpq
    have hk : (X ^ D : A[X]) • p - q ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hpq, sub_self]
    obtain ⟨p', hp', hpp'⟩ := he D p q hq hk
    have h1 : π p = π p' := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hpp'
      exact hpp'
    refine LinearMap.mem_range.2 ⟨fun i => ⟨p' i, mem_degreeLT.2 (hp' i)⟩, ?_⟩
    rw [h1]
    rfl

end RamanujanPetersson.EtPBC.Z1

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

/-- **Reflection**: `X^D • φ₁ (c • w) = q • φ₁ w` with `deg q ≤ D` for `deg c ≤ D`. -/
theorem exists_refl (φ₁ : M₁ →ₗ[A] N) (h₁ : ∀ m, (X : A[X]) • φ₁ ((X : A[X]) • m) = φ₁ m) (D : ℕ) (c : A[X])
    (hc : c.natDegree ≤ D) (w : M₁) :
    ∃ q : A[X], q.natDegree ≤ D ∧ (X ^ D : A[X]) • φ₁ (c • w) = q • φ₁ w := by
  have hC₁ : ∀ (a : A) (y : M₁), (C a : A[X]) • y = a • y := fun a y => by
    rw [← algebraMap_eq, algebraMap_smul]
  have hCN : ∀ (a : A) (y : N), (C a : A[X]) • y = a • y := fun a y => by
    rw [← algebraMap_eq, algebraMap_smul]
  refine ⟨∑ k ∈ Finset.range (D + 1), C (c.coeff k) * X ^ (D - k), ?_, ?_⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun k _ => (natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)
  · conv_lhs => rw [c.as_sum_range' (D + 1) (Nat.lt_succ_of_le hc)]
    rw [Finset.sum_smul, Finset.sum_smul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [← C_mul_X_pow_eq_monomial, mul_smul, hC₁, map_smul, mul_smul, hCN, smul_comm,
      ← Nat.sub_add_cancel hk', pow_add, mul_smul, pow_smul_iter φ₁ h₁ k w, Nat.sub_add_cancel hk']

end TwoChart

end RamanujanPetersson.EtPBC.Z1

end

end

-- ===== S4.Def_RP_EtPBC_A_CovUnr =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5c): unramified at the primes over `J` (Nakayama on `Ω`)

For `B → E` and an ideal `J` of `B` with `E ⧸ JE` formally unramified over `B`:
* `tmul_D_eq_zero`: `1 ⊗ dx = 0` in `(E ⧸ JE) ⊗ Ω[E⁄B]` for `x ∈ JE`;
* `omega_le_smul`: `Ω[E⁄B] = JE • Ω[E⁄B]` (conormal sequence);
* **`unr_elt`** (`E` of finite type): some `r ≡ 1 mod JE` kills `Ω[E⁄B]`;
* **`unr_of_notMem`**: if `r` kills `Ω[E⁄B]`, `E` is unramified over `B` at every prime not containing `r`;
* **`unr_at`**: `E` is unramified over `B` at every prime containing `JE`.
-/

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Unr

variable {B E : Type u} [CommRing B] [CommRing E] [Algebra B E]

variable (J : Ideal B)

variable [Algebra.FormallyUnramified B (E ⧸ J.map (algebraMap B E))]

/-- **`Ω[E⁄B] = JE • Ω[E⁄B]`** when `E ⧸ JE` is formally unramified over `B`. -/
theorem omega_le_smul : (⊤ : Submodule E Ω[E⁄B]) ≤ J.map (algebraMap B E) • ⊤ := by
  intro ω _
  have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange B E (E ⧸ J.map (algebraMap B E))
    Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := (hex ((1 : E ⧸ J.map (algebraMap B E)) ⊗ₜ[E] ω)).1 (Subsingleton.elim _ _)
  obtain ⟨z, rfl⟩ := Ideal.toCotangent_surjective _ y
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent] at hy
  have hz : (z : E) ∈ J.map (algebraMap B E) := by
    exact Ideal.Quotient.eq_zero_iff_mem.1 (RingHom.mem_ker.1 z.2)
  rw [tmul_D_eq_zero J _ hz] at hy
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul Ω[E⁄B] (J.map (algebraMap B E))) hy
  rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] at h2
  exact (Submodule.Quotient.mk_eq_zero _).1 h2.symm

/-- **Nakayama**: some `r ≡ 1 mod JE` kills `Ω[E⁄B]`. -/
theorem unr_elt [Algebra.FiniteType B E] :
    ∃ r : E, r - 1 ∈ J.map (algebraMap B E) ∧ ∀ ω : Ω[E⁄B], r • ω = 0 := by
  obtain ⟨r, hr, h⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    (J.map (algebraMap B E)) (⊤ : Submodule E Ω[E⁄B]) Module.Finite.fg_top (omega_le_smul J)
  exact ⟨r, hr, fun ω => h ω trivial⟩

end Unr

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovEt =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E3c3): the completed chart `Ê₀` is etale near `p`

* **`et_near₀`**: there is `s ∈ Ê₀` with `s ≡ 1 mod J₀ Ê₀` and `Ê₀[1/s]` etale over `B₀` (via `β₀`).
  Flatness of `Ê₀ ⧸ J₀^(k+1)` over `B₀ ⧸ J₀^(k+1)` comes from `θ₀ k` (`fq_flat`), freeness near `V(J₀)` from the
  local criterion (`lf_mem_freeLocus`), the unit `r` killing `Ω` from `unr_elt`, and etaleness from `fq_etale` (`et_gen`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Et₀

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N} {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN} {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- Generic step: `D(g)` free and `M ⧸ J M` formally unramified give an etale `M[1/s]`, `s ≡ 1 mod J M`. -/
theorem et_gen {B M : Type u} [CommRing B] [CommRing M] [Algebra B M] [IsNoetherianRing B] [Module.Finite B M]
    (J : Ideal B) [Algebra.FormallyUnramified B (M ⧸ (J ^ (0 + 1)).map (algebraMap B M))] (g : B)
    (hg1 : g - 1 ∈ J) (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B)) ⊆ Module.freeLocus B M) :
    ∃ s : M, s - 1 ∈ J.map (algebraMap B M) ∧ Algebra.Etale B (Localization.Away s) := by
  obtain ⟨r, hr1, hr⟩ := unr_elt (E := M) (J ^ (0 + 1))
  rw [zero_add, pow_one] at hr1
  refine ⟨algebraMap B M g * r, ?_, fq_etale g hg r hr⟩
  have hs1 : algebraMap B M g * r - 1 = (algebraMap B M g - 1) * r + (r - 1) := by ring
  rw [hs1]
  refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) hr1
  have h2 := Ideal.mem_map_of_mem (algebraMap B M) hg1
  rwa [map_sub, map_one] at h2

end Et₀

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs4b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap

* `exists_presN`: if `E` is presented as `Pres g` over `P`, `f : P → P'` is a localization away from `t` with `f t` a
  unit, and `q : E → E'` is a localization away from `t` compatible with `bN : P' → E'`, then `E' ≅ Pres (gmap f g)`
  (via `presN`, bijective by `away_bij`).
* `exists_subst`: a `P`-isomorphism `Pres g ≅ Pres g'` is `presIso` of substitution data `u v` (with all four
  membership witnesses).
* `chart_pres`: a finite etale `b : P → E` is presented by a square system with etale and finite witnesses.
* **`two_chart_pres`**: the two charts `E₀, E₁` of a cover glued along `E`, their base changes to the overlap and
  substitution data between the two overlap presentations, all in one package.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section PresN

end PresN

section Subst

variable {P : Type u} [CommRing P] {r r' : ℕ} (g : Fin r → MvPolynomial (Fin r) P)
  (g' : Fin r' → MvPolynomial (Fin r') P)

/-- **An isomorphism of presentations comes from substitution data.** -/
theorem exists_subst (m : Pres g ≃+* Pres g')
    (hm : ∀ a, m (algebraMap P (Pres g) a) = algebraMap P (Pres g') a) :
    ∃ (u : Fin r' → MvPolynomial (Fin r) P) (v : Fin r → MvPolynomial (Fin r') P)
      (hu : ∀ j, MvPolynomial.bind₁ u (g' j) ∈ Ideal.span (Set.range g))
      (hv : ∀ i, MvPolynomial.bind₁ v (g i) ∈ Ideal.span (Set.range g'))
      (huv : ∀ i, MvPolynomial.bind₁ u (v i) - MvPolynomial.X i ∈ Ideal.span (Set.range g))
      (hvu : ∀ j, MvPolynomial.bind₁ v (u j) - MvPolynomial.X j ∈ Ideal.span (Set.range g')),
      ∀ x, presIso g g' u v hu hv huv hvu x = m x := by
  have hm' : ∀ a, m.symm (algebraMap P (Pres g') a) = algebraMap P (Pres g) a := fun a => by
    rw [← hm, RingEquiv.symm_apply_apply]
  choose v hvX using fun i => Ideal.Quotient.mk_surjective
    (m (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X i)))
  choose u huX using fun j => Ideal.Quotient.mk_surjective
    (m.symm (Ideal.Quotient.mk (Ideal.span (Set.range g')) (MvPolynomial.X j)))
  have Bv : ∀ x, Ideal.Quotient.mk (Ideal.span (Set.range g')) (MvPolynomial.bind₁ v x) =
      m (Ideal.Quotient.mk (Ideal.span (Set.range g)) x) :=
    mk_bind₁_eq g g' m.toRingHom (fun a => hm a) v (fun i => hvX i)
  have Bu : ∀ x, Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.bind₁ u x) =
      m.symm (Ideal.Quotient.mk (Ideal.span (Set.range g')) x) :=
    mk_bind₁_eq g' g m.symm.toRingHom (fun a => hm' a) u (fun j => huX j)
  have hu : ∀ j, MvPolynomial.bind₁ u (g' j) ∈ Ideal.span (Set.range g) := fun j =>
    Ideal.Quotient.eq_zero_iff_mem.mp (by rw [Bu, presRel_zero g' j, map_zero])
  have hv : ∀ i, MvPolynomial.bind₁ v (g i) ∈ Ideal.span (Set.range g') := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.mp (by rw [Bv, presRel_zero g i, map_zero])
  have huv : ∀ i, MvPolynomial.bind₁ u (v i) - MvPolynomial.X i ∈ Ideal.span (Set.range g) := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, Bu, hvX i, RingEquiv.symm_apply_apply, sub_self])
  have hvu : ∀ j, MvPolynomial.bind₁ v (u j) - MvPolynomial.X j ∈ Ideal.span (Set.range g') := fun j =>
    Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_sub, Bv, huX j, RingEquiv.apply_symm_apply, sub_self])
  refine ⟨u, v, hu, hv, huv, hvu, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [presIso_mk, Bv]

end Subst

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr7 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3g): flat descent of vanishing tensors to finitely generated subalgebras

For a flat `A`-algebra `S` (in use: `S = Â`, flat by `AdicCompletion.flat_of_isNoetherian`) and an `A`-module `B`:

* **`exists_fg_lift`**: finitely many elements of `S ⊗[A] B` all come from `C₀ ⊗[A] B` for one f.g. `C₀ ≤ S`.
* **`desc_one`** / **`desc_fg`**: finitely many elements of `C₀ ⊗[A] B` whose images in `S ⊗[A] B` vanish already
  vanish in `C ⊗[A] B` for a f.g. `C` with `C₀ ≤ C` (equational criterion for vanishing + flatness of `S`).
* **`rTensor_inclusion_mono`**: such a vanishing persists along any larger subalgebra.
* **`tmap_id_apply`**, **`desc_mvPoly`**: the same for finitely many polynomials over `C₀ ⊗[A] B` (`B` an algebra),
  coefficientwise, with the ring maps `Algebra.TensorProduct.map (inclusion h) (AlgHom.id A B)`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section Mod

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B : Type u} [AddCommGroup B] [Module A B]

theorem desc_fg [Module.Flat A S] {ι : Type*} [Finite ι] (C₀ : Subalgebra A S) (hC₀ : C₀.FG)
    (x : ι → C₀ ⊗[A] B) (hx : ∀ k, C₀.val.toLinearMap.rTensor B (x k) = 0) :
    ∃ (C : Subalgebra A S) (h : C₀ ≤ C), C.FG ∧
      ∀ k, (Subalgebra.inclusion h).toLinearMap.rTensor B (x k) = 0 := by
  classical
  have := Fintype.ofFinite ι
  choose T hT using fun k => desc_one C₀ (x k) (hx k)
  refine ⟨C₀ ⊔ Algebra.adjoin A (↑(Finset.univ.biUnion T) : Set S), le_sup_left,
    hC₀.sup (Subalgebra.fg_adjoin_finset _), fun k => hT k _ le_sup_left fun z hz => ?_⟩
  have hz' : z ∈ Algebra.adjoin A (↑(Finset.univ.biUnion T) : Set S) :=
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hz⟩))
  first
    | exact SetLike.le_def.mp le_sup_right hz'
    | exact Algebra.mem_sup_right hz'
    | exact (le_sup_right (a := C₀)) hz'

end Mod

section Alg

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B : Type u} [CommRing B] [Algebra A B]

theorem desc_mvPoly [Module.Flat A S] {σ : Type*} (C₀ : Subalgebra A S) (hC₀ : C₀.FG)
    (p : Finset (MvPolynomial σ (C₀ ⊗[A] B)))
    (hp : ∀ q ∈ p, MvPolynomial.map (Algebra.TensorProduct.map C₀.val (AlgHom.id A B)).toRingHom q = 0) :
    ∃ (C : Subalgebra A S) (h : C₀ ≤ C), C.FG ∧ ∀ q ∈ p,
      MvPolynomial.map (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A B)).toRingHom q = 0 := by
  classical
  obtain ⟨C, h, hfg, hC⟩ := desc_fg (ι := Σ q : p, (q.1.support : Finset (σ →₀ ℕ))) C₀ hC₀
    (fun i => i.1.1.coeff i.2.1) (by
      rintro ⟨q, m⟩
      have e := congrArg (MvPolynomial.coeff m.1) (hp q.1 q.2)
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at e
      rw [← tmap_id_apply]
      exact e)
  refine ⟨C, h, hfg, fun q hq => ?_⟩
  ext m
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
  by_cases hm : m ∈ q.support
  · have e := hC ⟨⟨q, hq⟩, ⟨m, hm⟩⟩
    rw [← tmap_id_apply] at e
    exact e
  · have e0 : q.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    rw [e0, map_zero]

end Alg

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs5b =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`

* `exists_lift_monics`: finitely many monic polynomials over `S ⊗ B` come from monic ones over `C ⊗ B`, `C` f.g.
* `bcC φ C = id_C ⊗ φ : C ⊗ B → C ⊗ N`; `tvC_bcC`, `tiC_bcC` and their polynomial forms `map_tvC_bcC`,
  `map_tiC_bcC`: `bcC` commutes with `tvC` (to `S`) and with `tiC` (to a larger `D`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section LiftB

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B : Type u} [CommRing B] [Algebra A B]

/-- Finitely many monic polynomials over `S ⊗ B` come from monic polynomials over `C ⊗ B`, `C` f.g. -/
theorem exists_lift_monics {ι : Type*} [Finite ι] (q : ι → Polynomial (S ⊗[A] B)) (hq : ∀ k, (q k).Monic) :
    ∃ C : Subalgebra A S, C.FG ∧
      ∀ k, ∃ qC : Polynomial (C ⊗[A] B), qC.Monic ∧ qC.map (tvC B C) = q k := by
  classical
  rcases subsingleton_or_nontrivial (S ⊗[A] B) with hs | hs
  · exact ⟨⊥, Subalgebra.fg_bot, fun k =>
      ⟨1, Polynomial.monic_one, Polynomial.ext fun _ => Subsingleton.elim _ _⟩⟩
  · obtain ⟨C, hC, hz⟩ := exists_fg_lift (A := A) (S := S) (B := B) (ι := Σ k : ι, (q k).support)
      (fun i => (q i.1).coeff i.2.1)
    refine ⟨C, hC, fun k => ?_⟩
    have hl : q k ∈ Polynomial.lifts (tvC B C) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : n ∈ (q k).support
      · obtain ⟨x, hx⟩ := hz ⟨k, ⟨n, hn⟩⟩
        exact ⟨x, (tmap_id_apply C.val x).trans hx⟩
      · have h0 : (q k).coeff n = 0 := by
          first
            | exact Polynomial.notMem_support_iff.mp hn
            | exact Polynomial.not_mem_support_iff.mp hn
        rw [h0]
        exact ⟨0, map_zero _⟩
    obtain ⟨qC, hmap, -, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (hq k)
    exact ⟨qC, hmon, hmap⟩

end LiftB

section BC

end BC

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

theorem hκT (hσ : ∀ c, χ' (σ c) = res (σh c))
    (hθk : ∀ x, θh (algebraMap (Ah ⊗[A] B) (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC))
      x) = kap χ ν βQ hβ res hres x) :
    (kap χ ν βQ hβ χ' hχ').comp (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom =
      (θh.comp (algebraMap (Ah ⊗[A] B)
        (Pres (gmap (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom gC)))).comp
        (Algebra.TensorProduct.map σh (AlgHom.id A B)).toRingHom :=
  RingHom.ext fun x => (kap_map χ ν βQ hβ χ' hχ' res hres σh σ hσ x).trans (hθk _).symm

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4Base =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`

* `isoSpec_inv_appTop'`, `eq_Spec_map` (a morphism `Spec R ⟶ V`, `V` affine, is `Spec` of its ring map).
* `pushout_inl_surj`, `pushout_inl_ker`: in a pushout of commutative rings along a surjection `g : A ↠ C`, the map
  `inl : B → P` is surjective with kernel `(ker g) B`.
* `hV V R' : Spec R' ⟶ V`, `hV_appTop`; `YV K gV π R' = Y ×_V Spec R'` with its `Γ(V)`-algebra structure `algYV`;
  `fR : R' →ₐ Γ(Y_{V'}, ⊤)`, `gS : secAlg →ₐ Γ(Y_{V'}, ⊤)`, **`PhiY = lift fR gS`**; `isClopen_PhiY`: for an
  idempotent `e'` of `R' ⊗ secAlg`, `D(PhiY e')` is clopen.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

/-- In a pushout of commutative rings, the base change of a surjection is surjective. -/
theorem pushout_inl_surj {A B C P : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C} {inl : B ⟶ P} {inr : C ⟶ P}
    (h : IsPushout f g inl inr) (hg : Function.Surjective g.hom) : Function.Surjective inl.hom := by
  have he : Function.Surjective (Polynomial.eval₂RingHom g.hom (0 : C)) := by
    intro c
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨Polynomial.C a, by simp⟩
  intro y
  obtain ⟨q, hq⟩ := pushout_surj h.flip 0 he y
  refine ⟨q.coeff 0, ?_⟩
  rw [← hq, Polynomial.coe_eval₂RingHom, map_zero, Polynomial.eval₂_at_zero]

section Base

end Base

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_StkRD =====
section

/-!
# S4-EtPBC-A, L1b: stalks of derived pushforwards

For `g : P ⟶ S`, a geometric point `s` of `S` and an injective resolution `I` of `F`, the stalk at `s`
of `R^q g_* F` is the fibre (a filtered colimit over the etale neighbourhoods `V` of `s`) of the presheaf
`V ↦ H^q(I^•(g⁻¹ V))` (`stalkRDIso`, `preHomologyObjIso`). Both the stalk functor and the presheaf fibre
functor are exact, so they commute with homology.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S)

/-- The complex of sections `K(W)`. -/
abbrev secCx {X : Scheme.{u}} (K : CochainComplex (EtSh Λ X) ℕ) (W : X.Etale) :
    CochainComplex (ModuleCat.{u} Λ) ℕ :=
  ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⋙
    (evaluation _ _).obj (op W)).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

variable (s : GeomPt S)

/-- The stalk of the homology sheaf of `g_* K` is the fibre of the presheaf homology of `V ↦ K(g⁻¹ V)`. -/
def stalkHomologyIso (K : CochainComplex (EtSh Λ P) ℕ) (q : ℕ) :
    (s.stalkF Λ).obj ((((push g Λ).mapHomologicalComplex _).obj K).homology q) ≅
      s.point.presheafFiber.obj ((preCx Λ g K).homology q) :=
  (((((push g Λ).mapHomologicalComplex _).obj K).sc q).mapHomologyIso (s.stalkF Λ)).symm ≪≫
    (Iso.refl _ : _ ≅ (((preCx Λ g K).sc q).map s.point.presheafFiber).homology) ≪≫
    ((preCx Λ g K).sc q).mapHomologyIso s.point.presheafFiber

/-- Presheaf homology is computed sectionwise. -/
def preHomologyObjIso (K : CochainComplex (EtSh Λ P) ℕ) (q : ℕ) (V : S.Etale) :
    ((preCx Λ g K).homology q).obj (op V) ≅ (secCx Λ K ((etPull g).obj V)).homology q :=
  (((preCx Λ g K).sc q).mapHomologyIso ((evaluation _ _).obj (op V))).symm ≪≫
    (Iso.refl _ : _ ≅ ((secCx Λ K ((etPull g).obj V)).sc q).homology)

/-- **Stalks of derived pushforwards**: `(R^q g_* F)_s ≅ colim_(V ∋ s) H^q(I^•(g⁻¹ V))`. -/
def stalkRDIso {F : EtSh Λ P} (I : InjectiveResolution F) (q : ℕ) :
    (s.stalkF Λ).obj (((push g Λ).rightDerived q).obj F) ≅
      s.point.presheafFiber.obj ((preCx Λ g I.cocomplex).homology q) :=
  (s.stalkF Λ).mapIso (I.isoRightDerivedObj (push g Λ) q) ≪≫ stalkHomologyIso Λ g s I.cocomplex q

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_SecCoc =====
section

/-!
# S4-EtPBC-A, L1c (part 1): cocycles of `I^•(W)` as `Ext` classes

For an injective resolution `I` of `F`, `W : X.Etale` and `p : ℕ`: `secSc Λ I W p` is the short complex `sc (p+1)` of
the complex of sections `I^•(W)`; `cocExtFun` sends a cocycle `z` (an element of `ker g`) to the class
`InjectiveResolution.extMk` of the map `Λ[W] ⟶ I^(p+1)` given by `z` (`freeEquiv`); it is additive (`cocExtFun_add`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {F : EtSh Λ X} (I : InjectiveResolution F)

/-- `I^p(W) → I^(p+1)(W) → I^(p+2)(W)` (as `sc (p+1)`). -/
abbrev secSc (W : X.Etale) (p : ℕ) : ShortComplex (ModuleCat.{u} Λ) :=
  (secCx Λ I.cocomplex W).sc (p + 1)

/-- A cocycle as a section of `I^(p+1)` over `W`. -/
def cocSec {W : X.Etale} {p : ℕ} (z : LinearMap.ker (secSc Λ I W p).g.hom) :
    (I.cocomplex.X (p + 1)).val.obj (op W) := z.1

theorem cocSec_d {W : X.Etale} {p : ℕ} (z : LinearMap.ker (secSc Λ I W p).g.hom) :
    (I.cocomplex.d (p + 1) ((ComplexShape.up ℕ).next (p + 1))).hom.app (op W) (cocSec Λ I z) = 0 := z.2

theorem cocSec_zero {W : X.Etale} {p : ℕ} : cocSec Λ I (0 : LinearMap.ker (secSc Λ I W p).g.hom) = 0 := rfl

theorem cocSec_add {W : X.Etale} {p : ℕ} (a b : LinearMap.ker (secSc Λ I W p).g.hom) :
    cocSec Λ I (a + b) = cocSec Λ I a + cocSec Λ I b := rfl

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_SecNat =====
section

/-!
# S4-EtPBC-A, L1c': naturality of `secExt` in the etale object

`secExt_π`: `secExt` of the class of a cycle `c` is `cocExt c`. `secExt_nat`: for `w : W' ⟶ W` and a morphism of short
complexes `φ : I^•(W)_(p+1) ⟶ I^•(W')_(p+1)` that restricts along `w` in the middle,
`secExt W' (H(φ) x) = Λ[w]^* (secExt W x)`. `germExt`: the presheaf `V ↦ H^(p+1)(I^•(g⁻¹ V))` at `V` is
`Ext^(p+1)(Λ[g⁻¹ V], F)`, naturally in `V` (`germExt_map`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves

universe u

section Sec

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} {F : EtSh Λ X} (I : InjectiveResolution F)

/-- A cycle as an element of `ker g`. -/
def cycKer (W : X.Etale) (p : ℕ) (c : (secSc Λ I W p).cycles) : LinearMap.ker (secSc Λ I W p).g.hom :=
  (secSc Λ I W p).moduleCatCyclesIso.hom c

theorem cocSec_cycles (W : X.Etale) (p : ℕ) (c : (secSc Λ I W p).cycles) :
    cocSec Λ I (cycKer Λ I W p c) = (secSc Λ I W p).iCycles c := by
  have h := ConcreteCategory.congr_hom (secSc Λ I W p).moduleCatCyclesIso_hom_i c
  simp only [CategoryTheory.comp_apply] at h
  exact h

end Sec

section Germ

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) {F : EtSh Λ P} (I : InjectiveResolution F)

/-- The short complex of presheaves `V ↦ (I^p → I^(p+1) → I^(p+2))(g⁻¹ V)`. -/
abbrev preSc (p : ℕ) : ShortComplex ((S.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ) := (preCx Λ g I.cocomplex).sc (p + 1)

end Germ

end RamanujanPetersson.EtPBC

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

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X) {M : ModuleCat.{u} Λ}

/-- **A section of a constant sheaf with value `0` at `cpt b` has zero germ at `comapPt f s` via `b`.** -/
theorem const_comap_germ (V : Y.Etale) (b : (comapPt f s).fiber.obj V)
    (z : (constSh Λ Y M).obj.obj (op V)) (h : cval z (cpt f s (V := V) b) = 0) :
    ((comapPt f s).toPresheafFiber V b (constSh Λ Y M).obj).hom z = 0 := by
  have e1 := cval_eq (s.map f) z ((fiberMapIso f s).inv.app V b) (pt_fiberMapIso_inv f s V b)
  have hg : ((s.map f).point.toPresheafFiber V ((fiberMapIso f s).inv.app V b) (constSh Λ Y M).obj).hom z = 0 := by
    have e2 := congrArg (fun w => (constStalkIso Λ (s.map f) M).inv.hom w) (e1.symm.trans h)
    simp only [map_zero] at e2
    refine Eq.trans ?_ e2
    change _ = ((constStalkIso Λ (s.map f) M).hom ≫ (constStalkIso Λ (s.map f) M).inv).hom _
    rw [Iso.hom_inv_id]
    rfl
  have hc := congrArg (fun φ => φ.hom z) (germ_comapPtIso f s (constSh Λ Y M).obj V b)
  have hl : (comapPtIso f s).hom.presheafFiber.app (constSh Λ Y M).obj ≫
      (comapPtIso f s).inv.presheafFiber.app (constSh Λ Y M).obj = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← Point.Hom.presheafFiber_comp, Iso.inv_hom_id, Point.Hom.presheafFiber_id]
    rfl
  calc ((comapPt f s).toPresheafFiber V b (constSh Λ Y M).obj).hom z
      = ((comapPtIso f s).hom.presheafFiber.app (constSh Λ Y M).obj ≫
          (comapPtIso f s).inv.presheafFiber.app (constSh Λ Y M).obj).hom
          (((comapPt f s).toPresheafFiber V b (constSh Λ Y M).obj).hom z) := by rw [hl]; rfl
    _ = ((comapPtIso f s).inv.presheafFiber.app (constSh Λ Y M).obj).hom
          (((s.map f).point.toPresheafFiber V ((fiberMapIso f s).inv.app V b) (constSh Λ Y M).obj).hom z) :=
        congrArg ((comapPtIso f s).inv.presheafFiber.app (constSh Λ Y M).obj).hom hc
    _ = 0 := by rw [hg, map_zero]

end Comap

section BC

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

theorem cval_sub {Λ : Type u} [CommRing Λ] {Z : Scheme.{u}} {M : ModuleCat.{u} Λ} {T : Z.Etale}
    (c c' : (constSh Λ Z M).obj.obj (op T)) (w : T.left) :
    cval (c - c') w = cval c w - cval c' w := by
  have h := cval_add (c - c') c' w
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

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

theorem kap_cond {W : P.Etale} {U : X.Etale} (h : U ⟶ (etPull ι).obj W) :
    (pullback.snd (pullback.snd π ι) U.hom ≫ h.left ≫ pullback.fst W.hom ι) ≫ W.hom =
      (pullback.fst (pullback.snd π ι) U.hom ≫ pullback.fst π ι) ≫ π :=
  kap_cond_aux ι π h.left (MorphismProperty.Over.w h)

/-- The map `(Y ×_P X) ×_X U ⟶ π⁻¹ W` of a local representation `h : U ⟶ ι⁻¹ W`. -/
def kap {W : P.Etale} {U : X.Etale} (h : U ⟶ (etPull ι).obj W) :
    pullback (pullback.snd π ι) U.hom ⟶ pullback W.hom π :=
  pullback.lift (pullback.snd _ _ ≫ h.left ≫ pullback.fst W.hom ι) (pullback.fst _ _ ≫ pullback.fst π ι)
    (kap_cond ι π h)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCa =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values

* `cval_uC`: values of `uC g M : M_X ⟶ g_* M_Y` (the section pulled back to `V ×_X Y`);
* `muU h Φ V : V ×_P U₁ ⟶ V ×_P U₂`, `kapU` (the same into `(V ×_P U₂) ×_{U₂} U₁`), `kapU_nat`;
* **`rU h Φ M : Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}`** with **`cval_rU`** (`cval (rU z) w = cval z (muU w)`);
* `nuU h Φ t : fib (h ≫ Φ) t ⟶ fib Φ t`, `muU_fibToNbhd`, **`cval_rU_fib`**;
* `muU_injective` for a closed immersion `h`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.SgUnit

universe u

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

/-- **Values of `uC g M`**: the section `z` pulled back to `V ×_X Y`. -/
theorem cval_uC {X Y : Scheme.{u}} (g : Y ⟶ X) {V : X.Etale} (z : (constSh Λ X M).obj.obj (op V))
    (w : ((etPull g).obj V).left) :
    cval (((uC g M).hom.app (op V)).hom z) w = cval z (pullback.fst V.hom g w) := by
  obtain ⟨V₁, f, v₁, hv, hc⟩ := cval_spec z (pullback.fst V.hom g w)
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f.left) (g := pullback.fst V.hom g) v₁ w hv
  have hcond : pullback.fst f.left (pullback.fst V.hom g) ≫ V₁.hom =
      (pullback.snd f.left (pullback.fst V.hom g) ≫ pullback.snd V.hom g) ≫ g := by
    rw [← MorphismProperty.Over.w f, ← Category.assoc, pullback.condition, Category.assoc, pullback.condition,
      Category.assoc]
  let κ : pullback f.left (pullback.fst V.hom g) ⟶ pullback V₁.hom g :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd V.hom g) hcond
  have hκ : κ ≫ ((etPull g).map f).left = pullback.snd f.left (pullback.fst V.hom g) := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((whisker_eq κ (etPull_map_left_fst g f)).trans
        ((pullback.lift_fst_assoc _ _ _ _).trans pullback.condition))
    · exact (Category.assoc _ _ _).trans ((whisker_eq κ (etPull_map_left_snd g f)).trans
        (pullback.lift_snd _ _ _))
  have hw : ((etPull g).map f).left (κ p) = w := (congrArg (fun φ => φ.base p) hκ).trans hp2
  have h1 := cval_map ((etPull g).map f) (((uC g M).hom.app (op V)).hom z) (κ p)
  have h2 : ((constSh Λ Y M).obj.map ((etPull g).map f).op).hom (((uC g M).hom.app (op V)).hom z) =
      (constUnit M ((etPull g).obj V₁)).hom (cval z (pullback.fst V.hom g w)) :=
    (app_map (uC g M) f z).symm.trans ((congrArg (fun y => ((uC g M).hom.app (op V₁)).hom y) hc).trans
      (uC_constUnit g M V₁ _))
  calc cval (((uC g M).hom.app (op V)).hom z) w
      = cval (((uC g M).hom.app (op V)).hom z) (((etPull g).map f).left (κ p)) := by rw [hw]
    _ = cval (((constSh Λ Y M).obj.map ((etPull g).map f).op).hom (((uC g M).hom.app (op V)).hom z)) (κ p) :=
        h1.symm
    _ = cval ((constUnit M ((etPull g).obj V₁)).hom (cval z (pullback.fst V.hom g w))) (κ p) := by rw [h2]
    _ = cval z (pullback.fst V.hom g w) := cval_constUnit _ _

section RU

end RU

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_LshEt =====
section

/-!
# S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`

For an etale `e : U ⟶ X`, a geometric point `x` of `X` and a module `J`, the restriction
`res e (x_* J)` of the skyscraper sheaf is assembled from the skyscraper sheaves `l_* J` at the
lifts `l` of `x` along `e` (`pr`, `assemble`, `assemble_pr`, `hom_ext_pr`). Hence:
* `injective_res_sky`: `res e (x_* J)` is injective for `J` injective;
* `res e` preserves injective objects (every injective is a retract of its god sheaf);
* **`lsh e Λ = e_!` preserves monomorphisms** (Mathlib's
  `preservesMonomorphisms_of_adjunction_of_preservesInjectiveObjects`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite
open RamanujanPetersson.EtCompact

noncomputable section

namespace RamanujanPetersson.EtSheaves.LshEt

universe u

variable {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] (x : GeomPt X)

/-- The geometric point of `U` given by a lift. -/
def liftPt (l : Lifts e x) : GeomPt U where
  Ω := x.Ω
  pt := l.1

theorem fl_ext {Y : Scheme.{u}} (s : GeomPt Y) {W : Y.Etale} {c c' : s.point.fiber.obj W}
    (h : fl s c = fl s c') : c = c' :=
  Over.OverMorphism.ext h

theorem fl_w {Y : Scheme.{u}} (s : GeomPt Y) {W : Y.Etale} (c : s.point.fiber.obj W) :
    fl s c ≫ W.hom = s.pt :=
  Over.w (c : Over.mk s.pt ⟶ (Scheme.Etale.forget Y).obj W)

/-- The lift of `x` through an `X`-map `b` from `x` to `W`. -/
def liftOf {W : U.Etale} (b : x.point.fiber.obj ((etComp e).obj W)) : Lifts e x :=
  ⟨fl x b ≫ W.hom, (Category.assoc _ _ _).trans (fl_w x b)⟩

variable {Λ : Type u} [CommRing Λ] (J : ModuleCat.{u} Λ)

/-- Maps into sections of `res e (x_* J)` from components. -/
def rLift {W : (U.Etale)ᵒᵖ} {P : ModuleCat.{u} Λ}
    (p : x.point.fiber.obj ((etComp e).obj W.unop) → (P ⟶ J)) :
    P ⟶ ((res e Λ).obj (x.point.skyscraperSheaf J)).obj.obj W :=
  Pi.lift p

/-- Maps into sections of a skyscraper sheaf from components. -/
def sLift {Y : Scheme.{u}} (Φ : GrothendieckTopology.Point.{u} Y.smallEtaleTopology) {W : (Y.Etale)ᵒᵖ}
    {P : ModuleCat.{u} Λ} (p : Φ.fiber.obj W.unop → (P ⟶ J)) :
    P ⟶ (Φ.skyscraperSheaf J).obj.obj W :=
  Pi.lift p

@[reassoc]
theorem rLift_π {W : (U.Etale)ᵒᵖ} {P : ModuleCat.{u} Λ}
    (p : x.point.fiber.obj ((etComp e).obj W.unop) → (P ⟶ J)) (b) :
    rLift e x J p ≫ rπ e x J W b = p b :=
  Pi.lift_π _ _

@[reassoc]
theorem sLift_π {Y : Scheme.{u}} (Φ : GrothendieckTopology.Point.{u} Y.smallEtaleTopology) {W : (Y.Etale)ᵒᵖ}
    {P : ModuleCat.{u} Λ} (p : Φ.fiber.obj W.unop → (P ⟶ J)) (c) :
    sLift J Φ p ≫ sπ J Φ W c = p c :=
  Pi.lift_π _ _

theorem r_hom_ext {W : (U.Etale)ᵒᵖ} {P : ModuleCat.{u} Λ}
    {f g : P ⟶ ((res e Λ).obj (x.point.skyscraperSheaf J)).obj.obj W}
    (h : ∀ b, f ≫ rπ e x J W b = g ≫ rπ e x J W b) : f = g :=
  Pi.hom_ext _ _ h

theorem s_hom_ext {Y : Scheme.{u}} (Φ : GrothendieckTopology.Point.{u} Y.smallEtaleTopology) {W : (Y.Etale)ᵒᵖ}
    {P : ModuleCat.{u} Λ} {f g : P ⟶ (Φ.skyscraperSheaf J).obj.obj W}
    (h : ∀ c, f ≫ sπ J Φ W c = g ≫ sπ J Φ W c) : f = g :=
  Pi.hom_ext _ _ h

end RamanujanPetersson.EtSheaves.LshEt

end

end

-- ===== S4.Def_RP_EtPBC_A_PushKill =====
section

/-!
# S4-EtPBC-A, R4-T3c: effacement through an etale neighbourhood by a pushout

Abstract part: an adjunction `Rl ⊣ R` (`Rl = f_!`, `R = f^*`) with `Rl` preserving monomorphisms, functors
`L : C ⥤ D` (`ι^*`), `L'' : C' ⥤ D` (`ι'^*`) and `κ : R ⋙ L'' ≅ L`. For a mono `m : R G ⟶ H` the pushout
`E = Rl H ⊔_{Rl R G} G` (along the counit) receives a mono `pushI : G ⟶ E`, and `L(pushI)` factors through
`L''(m)` (`pushI_fac`, from the triangle identity). Hence a class killed by `L''(m)` is killed by `L(pushI)`
(`kill_pushI`).

Geometric part (**`exists_bc_of_push_kill`**): for `g : P ⟶ S`, an etale `f : P' ⟶ P` with a lift `ι'` of the
fibre inclusion and a mono `m : f^* G ⟶ H` on `P'`, every `β ∈ H^1(P_s, ι^* G)` killed by `ι'^*(m)` is the base
change of a germ, provided base change is surjective in degree `0` for every sheaf on `P` (G1). No change of
the base `S` is needed: the effacement `G ⟶ E` lives on `P` (`f_!` preserves monos, `LshEt`).
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.PushKill

universe w v₁ u₁ v₂ u₂ v₃ u₃

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {C' : Type u₂} [Category.{v₂} C'] [Abelian C']
  {D : Type u₃} [Category.{v₃} D] [Abelian D] [HasExt.{w} D]
  {R : C ⥤ C'} {Rl : C' ⥤ C} (adj : Rl ⊣ R) [Rl.PreservesMonomorphisms]
  {L : C ⥤ D} {L'' : C' ⥤ D} (κ : R ⋙ L'' ≅ L)
  {G : C} {H : C'} (m : R.obj G ⟶ H) [Mono m]

omit [Abelian C'] [Abelian D] [HasExt D] [Rl.PreservesMonomorphisms] [Mono m] in
/-- **`L(pushI)` factors through `L''(m)`.** -/
theorem pushI_fac : κ.inv.app G ≫ L''.map m ≫ pushT adj κ m = L.map (pushI adj m) := by
  have h1 : L''.map m ≫ L''.map (adj.unit.app H) =
      L''.map (adj.unit.app (R.obj G)) ≫ L''.map (R.map (Rl.map m)) := by
    rw [← L''.map_comp, ← L''.map_comp]
    congr 1
    exact adj.unit.naturality m
  have h2 : L''.map (R.map (Rl.map m)) ≫ κ.hom.app (Rl.obj H) =
      κ.hom.app (Rl.obj (R.obj G)) ≫ L.map (Rl.map m) :=
    κ.hom.naturality (Rl.map m)
  have h3 : L.map (Rl.map m) ≫ L.map (pushout.inl (Rl.map m) (adj.counit.app G)) =
      L.map (adj.counit.app G) ≫ L.map (pushI adj m) := by
    rw [← L.map_comp, ← L.map_comp, pushout.condition]
  have h4 : κ.hom.app (Rl.obj (R.obj G)) ≫ L.map (adj.counit.app G) =
      L''.map (R.map (adj.counit.app G)) ≫ κ.hom.app G :=
    (κ.hom.naturality (adj.counit.app G)).symm
  have h5 : L''.map (adj.unit.app (R.obj G)) ≫ L''.map (R.map (adj.counit.app G)) = 𝟙 _ := by
    rw [← L''.map_comp, adj.right_triangle_components]
    exact L''.map_id _
  rw [pushT, reassoc_of% h1, reassoc_of% h2, h3, reassoc_of% h4, reassoc_of% h5, Iso.inv_hom_id_app_assoc]

/-- **A class killed by `L''(m)` is killed by `L(pushI)`.** -/
theorem kill_pushI {B : D} {n : ℕ} (β : Ext B (L.obj G) n)
    (hβ : (β.comp (Ext.mk₀ (κ.inv.app G)) (add_zero n)).comp (Ext.mk₀ (L''.map m)) (add_zero n) = 0) :
    β.comp (Ext.mk₀ (L.map (pushI adj m))) (add_zero n) = 0 := by
  rw [← pushI_fac adj κ m, ← Ext.mk₀_comp_mk₀, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_third_deg_zero, hβ, Ext.zero_comp]

end Abstract

section Geo

open AlgebraicGeometry RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

end Geo

end RamanujanPetersson.EtPBC.PushKill

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

/-- **Sections of a constant sheaf are determined by their values.** -/
theorem sec_ext_cval {Y : Scheme.{u}} {T : Y.Etale} (c₁ c₂ : (constSh Λ Y M).obj.obj (op T))
    (h : ∀ w, cval c₁ w = cval c₂ w) : c₁ = c₂ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_germs (constSh Λ Y M) (c₁ - c₂) fun x a => ?_
  refine germ_eq_zero_of_not_mem_supp (constSh Λ Y M) _ x a ?_
  rw [mem_supp_iff_cval, cval_sub, h, sub_self]
  exact fun h0 => h0 rfl

section RUq

end RUq

theorem cval_pushCompIso_inv {W X Y : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ Y) (V : Y.Etale)
    (z : (constSh Λ W M).obj.obj (op ((etPull (g ≫ f)).obj V))) (w : ((etPull g).obj ((etPull f).obj V)).left) :
    cval ((((pushCompIso Λ g f).inv.app (constSh Λ W M)).hom.app (op V)).hom z) w =
      cval z (((etPullCompIso g f).inv.app V).left w) := by
  have e : ((pushCompIso Λ g f).inv.app (constSh Λ W M)).hom.app (op V) =
      (constSh Λ W M).obj.map ((etPullCompIso g f).inv.app V).op := by
    simp [pushCompIso]; rfl
  rw [e]
  exact cval_map _ z w

section M

end M

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG5 =====
section

/-!
# S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`

* `sheet_cover`: the sheets `sheetE ν : V ⟶ U0E` cover `U0E` (every prime of `B(U)` comes from a sheet).
* `cU_kL`, `cval_dif_sheet`, `dif_sheet`: if `gi ≫ sheetE i = gj ≫ sheetE j` then `dif gi gj = j - i`
  (pointwise: the pair `(gi, gj)` lands in `Spec (C ⊗ C)` over an affine `U`, and `key_sheet`).
* `exists_sigma`: the sections `e + a(ν)` on the sheets glue to `σ ∈ E(U₀)`; `b_sigma`: `b σ` is the pull-back of `q`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Gen

end Gen

section Pt

end Pt

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] [Surjective V.hom] {Λ : Type u} [CommRing Λ]
  {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

omit [Fintype M] [DecidableEq M] in
theorem constUnit_map {W W' : X.Etale} (g : W' ⟶ W) (n : M) :
    ((constSh Λ X M).obj.map g.op).hom ((constUnit M W).hom n) = (constUnit M W').hom n :=
  T3d.sec_ext_cval _ _ fun w => by rw [cval_map, cval_constUnit, cval_constUnit]

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

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

theorem cval_pushCompIso_inv_push {Z W X Y : Scheme.{u}} (F : Z ⟶ W) (g : W ⟶ X) (f : X ⟶ Y) (V : Y.Etale)
    (z : (constSh Λ Z M).obj.obj (op ((etPull F).obj ((etPull (g ≫ f)).obj V))))
    (w : ((etPull F).obj ((etPull g).obj ((etPull f).obj V))).left) :
    cval ((((pushCompIso Λ g f).inv.app ((push F Λ).obj (constSh Λ Z M))).hom.app (op V)).hom z) w =
      cval z (((etPull F).map ((etPullCompIso g f).inv.app V)).left w) := by
  have e : ((pushCompIso Λ g f).inv.app ((push F Λ).obj (constSh Λ Z M))).hom.app (op V) =
      (constSh Λ Z M).obj.map ((etPull F).map ((etPullCompIso g f).inv.app V)).op := by
    first
      | (simp [pushCompIso]; rfl)
      | rfl
      | simp [pushCompIso]
  rw [e]
  exact cval_map _ z w

section C1

end C1

section B3

end B3

end RamanujanPetersson.EtPBC.T3d

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

/-- **Sections of the constant sheaf with prescribed values on a finite clopen partition.** -/
theorem exists_fsec {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} {M : ModuleCat.{u} Λ} {V : Y.Etale} {ι : Type*}
    [Finite ι] (C : ι → Set V.left) (hC : ∀ i, IsClopen (C i)) (hU : ∀ u, ∃! i, u ∈ C i) (n : ι → M) :
    ∃ f : (constSh Λ Y M).obj.obj (op V), ∀ i u, u ∈ C i → cval f u = n i := by
  classical
  have := Fintype.ofFinite ι
  choose c hc using fun i => exists_indicator (Λ := Λ) (C i) (hC i) (n i)
  refine ⟨∑ i, c i, fun i u hu => ?_⟩
  rw [cval_sum, Finset.sum_eq_single i]
  · rw [hc]
    exact Set.indicator_of_mem hu _
  · intro j _ hji
    rw [hc]
    refine Set.indicator_of_notMem ?_ _
    intro hj
    exact hji ((hU u).unique hj hu)
  · intro h
    exact absurd (Finset.mem_univ i) h

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

theorem cval_smul {T : Y.Etale} (c : Λ) (z : (constSh Λ Y M).obj.obj (op T)) (w : T.left) :
    cval (c • z) w = c • cval z w := by
  obtain ⟨a, ha⟩ := exists_fib_over T w
  exact (cval_eq _ _ a ha).trans ((congrArg (fun z => (constStalkIso Λ (geomPtAt (T.hom w)) M).hom.hom z)
    (map_smul _ c z)).trans ((map_smul _ _ _).trans (congrArg (c • ·) (cval_eq _ z a ha).symm)))

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

theorem cval_eq_of_specializes {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}} {M : ModuleCat.{u} Λ} {V : Y.Etale}
    (c : (constSh Λ Y M).obj.obj (op V)) {ν w : V.left} (h : ν ⤳ w) : cval c ν = cval c w :=
  h.mem_open ((isLocallyConstant_cval c).isOpen_fiber (cval c w)) rfl

section Rel

end Rel

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_O2E1 =====
section

/-!
# S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain

`A` Dedekind, `B` of finite type and formally unramified over `A` (e.g. etale).
* **`maximalIdeal_eq_map`**: at a prime `q` over a maximal `p`, `𝔪(B_q) = p B_q` (Mathlib's proof for finite `B`,
  with the Artinian fibre from `FormallyUnramified.finite_of_free`);
* **`isDedekindDomain_of_unramified`**: a domain `B` (with `A ↪ B`) is a Dedekind domain (incomparability from
  `Algebra.QuasiFinite.eq_of_le_of_under_eq` instead of integrality);
* **`isDomain_atPrime`**: if `B` is flat and `q` lies over `(π) ≠ 0`, then `B_q` is a domain (`𝔪 = (π)`, `π` regular,
  Krull intersection);
* **`exists_away_isDomain`**: if `B` is noetherian and `B_q` is a domain, some `B_g` (`g ∉ q`) is a domain;
* **`span_eq_of_unique`**: if `q` is the only maximal ideal containing `π`, then `π B = q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.EtPBC.EtDed

open IsLocalRing

section Max

end Max

section Ded

end Ded

section Dom

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A noetherian local ring whose maximal ideal is generated by a regular element is a domain. -/
theorem isDomain_of_span_regular (t : R) (ht : maximalIdeal R = Ideal.span {t}) (hreg : IsRegular t) :
    IsDomain R := by
  have : NoZeroDivisors R := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n, u, hu, rfl⟩ := exists_pow_mul_unit t ht x hne.1
    obtain ⟨m, v, hv, rfl⟩ := exists_pow_mul_unit t ht y hne.2
    have h1 : t ^ (n + m) * (u * v) = 0 := by rw [← hxy, pow_add]; ring
    have h2 : t ^ (n + m) = 0 := by
      have := (hu.mul hv).mul_left_eq_zero.1 h1
      exact this
    have h3 : IsRegular (t ^ (n + m)) := hreg.pow _
    have h4 : (1 : R) = 0 := h3.left (show t ^ (n + m) * 1 = t ^ (n + m) * 0 by rw [h2, zero_mul, zero_mul])
    exact one_ne_zero h4
  exact NoZeroDivisors.to_isDomain R

end Dom

section Loc

end Loc

section Away

end Away

section Span

end Span

end RamanujanPetersson.EtPBC.EtDed


end

-- ===== S4.Def_RP_EtPBC_A_O2P1 =====
section

/-!
# S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)

`B` Dedekind with fraction field `K`, `Bt = B[1/t]`, `(t)` prime.

* `locPt p hp`: the height-one prime `p Bt` of a localization; `valuation_locPt` (same valuation on `K`);
* `dvd_log_of_mem_maxUnram`: a root `α ∈ maxUnram Bt K` of `u ∈ K` gives `d ∣ log v_p(u)` for `t ∉ p`;
* `valuation_algebraMap_bot`, `root_mem_maxUnram_self`: `d ∣ log v(u)` at every height-one prime of `B` puts every
  `d`-th root of `u` in `maxUnram B K` (`root_mem_maxUnram_of_dvd` with `M = ⊥`, model `B`);
* `exists_root_unit`: `d`-th roots of units of `B` lie in `maxUnram B K`;
* **`root_mem_maxUnram_twist`**: for `α ∈ maxUnram Bt K` with `α ^ d = u`, there is `m : ℤ` such that every `d`-th root
  of `u t^m` lies in `maxUnram B K`.
-/

set_option autoImplicit false

open IsDedekindDomain

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer

section VC

end VC

section Root

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Kummer roots over `R` itself**: if `d` is invertible in `R` and `d ∣ log v(u)` at every height-one prime of
`R`, every `d`-th root of `u` lies in `maxUnram R K`. -/
theorem root_mem_maxUnram_self {d : ℕ} [NeZero d] (hd : IsUnit (d : R)) {u : K} (hu0 : u ≠ 0)
    (hdiv : ∀ v : HeightOneSpectrum R, (d : ℤ) ∣ WithZero.log (v.valuation K u))
    {γ : AlgebraicClosure K} (hγ : γ ^ d = algebraMap K (AlgebraicClosure K) u) : γ ∈ maxUnram R K := by
  let M : IntermediateField K (AlgebraicClosure K) := ⊥
  have : IsDedekindDomain (integralClosure R M) := integralClosure.isDedekindDomain (A := R) (K := K) (L := M)
  have : IsFractionRing (integralClosure R M) M :=
    integralClosure.isFractionRing_of_finite_extension (A := R) K M
  have hKM : ∀ x : M, ∃ k : K, algebraMap K M k = x := fun x => by
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 x.2
    exact ⟨k, Subtype.ext hk⟩
  have hinjKM : Function.Injective (algebraMap K M) := (algebraMap K M).injective
  haveI : FaithfulSMul R M := (faithfulSMul_iff_algebraMap_injective R M).2 (by
    rw [IsScalarTower.algebraMap_eq R K M]
    exact hinjKM.comp (IsFractionRing.injective R K))
  haveI : IsFractionRing R M := IsFractionRing.of_field R M (fun z => by
    obtain ⟨k, rfl⟩ := hKM z
    obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    exact ⟨a, s, by rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]⟩)
  -- the model: `R ≃ integralClosure R M`
  have hsurj : Function.Surjective (algebraMap R (integralClosure R M)) := fun x => by
    obtain ⟨k, hk⟩ := hKM (x : M)
    have hint : IsIntegral R k := by
      have h1 : IsIntegral R (algebraMap K M k) := by rw [hk]; exact x.2
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K M) hinjKM).1 h1
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨r, Subtype.ext ?_⟩
    rw [← hk, ← hr, ← IsScalarTower.algebraMap_apply R K M]
    rfl
  have hinj : Function.Injective (algebraMap R (integralClosure R M)) := fun a b hab => by
    have h := congrArg (fun y : integralClosure R M => (y : M)) hab
    exact (IsFractionRing.injective R M) h
  let eR : R ≃+* integralClosure R M := RingEquiv.ofBijective (algebraMap R _) ⟨hinj, hsurj⟩
  have heR : ∀ r, algebraMap (integralClosure R M) M (eR r) = algebraMap R M r := fun r =>
    (IsScalarTower.algebraMap_apply R (integralClosure R M) M r).symm
  have ha0 : algebraMap K M u ≠ 0 := (map_ne_zero _).2 hu0
  refine root_mem_maxUnram_of_dvd R (bot_mem_unramSet R K) hd ha0 (fun v => ?_) hγ
  have h1 := hdiv (HeightOneSpectrum.comap (eR : R →+* integralClosure R M) eR.surjective v)
  rwa [← valuation_algebraMap_bot (M := M), valuation_comap eR heR v] at h1

/-- **`d`-th roots of units are unramified.** -/
theorem exists_root_unit {d : ℕ} [NeZero d] (hd : IsUnit (d : R)) {b : R} (hb : IsUnit b) :
    ∃ γ : AlgebraicClosure K, γ ∈ maxUnram R K ∧ γ ^ d = algebraMap R (AlgebraicClosure K) b := by
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R (AlgebraicClosure K) b) (NeZero.pos d)
  refine ⟨γ, root_mem_maxUnram_self hd (u := algebraMap R K b) ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2
    hb.ne_zero) (fun v => ?_) (by rw [hγ, ← IsScalarTower.algebraMap_apply]), hγ⟩
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.2 (fun hm => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hb)),
    WithZero.log_one]
  exact dvd_zero _

end Root

section Twist

end Twist

end RamanujanPetersson.EtCompact.Pur

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

theorem resTrIsoE_natural {F G : EtSh Λ X} (φ : F ⟶ G) :
    ((geomPtAt y).stalkF Λ).map ((res g Λ).map φ) ≫ (resTrIsoE g y Λ G).hom =
      (resTrIsoE g y Λ F).hom ≫ ((geomPtAt (g y)).stalkF Λ).map φ := by
  rw [resTrIsoE_hom, resTrIsoE_hom]
  erw [reassoc_of% (resFib_natural g (geomPtAt y) Λ φ),
    (ptIsoSheafFiber Λ (GPtIso.ptIso (eE g y))).inv.naturality φ]
  exact (Category.assoc _ _ _).symm

theorem resTrIsoE_natural_apply {F G : EtSh Λ X} (φ : F ⟶ G) (v : stalk Λ ((res g Λ).obj F) y) :
    (resTrIsoE g y Λ G).hom.hom ((((geomPtAt y).stalkF Λ).map ((res g Λ).map φ)).hom v) =
      (((geomPtAt (g y)).stalkF Λ).map φ).hom ((resTrIsoE g y Λ F).hom.hom v) :=
  congrArg (fun ψ => ModuleCat.Hom.hom ψ v) (resTrIsoE_natural g y Λ φ)

/-! ### `Λ_U ⟶ g^* Λ_X` -/

theorem gg_eq_germ {P : Scheme.{u}} (G : EtSh Λ P) (x : P) (z : G.obj.obj (op (etId P))) :
    gg (geomPtAt x) G z = germ G x (topPt x) z := by
  rw [gg, germ, Subsingleton.elim (geomPtAt x).top (topPt x)]

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

theorem trIso_natural {F G : EtSh Λ X} (φ : F ⟶ G) (v : stalk Λ ((res g Λ).obj F) y) :
    (trIso g h Λ G).hom.hom ((((geomPtAt y).stalkF Λ).map ((res g Λ).map φ)).hom v) =
      (((geomPtAt x).stalkF Λ).map φ).hom ((trIso g h Λ F).hom.hom v) := by
  subst h
  exact resTrIsoE_natural_apply g y Λ φ v

theorem trIso_inv_natural {F G : EtSh Λ X} (φ : F ⟶ G) (u : stalk Λ F x) :
    (((geomPtAt y).stalkF Λ).map ((res g Λ).map φ)).hom ((trIso g h Λ F).inv.hom u) =
      (trIso g h Λ G).inv.hom ((((geomPtAt x).stalkF Λ).map φ).hom u) := by
  apply trIso_hom_injective g h Λ G
  rw [trIso_natural, isoInvHom, isoInvHom]

end Pt

section Kappa

end Kappa

end RamanujanPetersson.EtCompact.GalTrE

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P2 =====
section

/-!
# S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)

* `exists_cdec`: a locally constant additive `χ : G → Λ` with finite image (`N • Λ = 0`) is
  `σ ↦ ∑ i, (c i σ).val • g i` with `c i : G → ZMod (d i)` additive locally constant, `d i ∣ N`, `d i • g i = 0`;
* `zvHom hg : ZMod d →+ Λ`, `a ↦ a.val • g` (`d • g = 0`), `zvHom_intCast`, `zvHom_apply`;
* `kchar_npow`, `kchar_inv`, `kchar_zpow`: `kchar (γ ^ m) = m * kchar γ`; `mem_rad_of_pow_eq`;
* `kumChi_twist`: `kumChi_d α g = kumChi_d (α τ^{(N/d) m}) g + kumChi_N τ ((-m) • g)`;
* `exists_tau`: an `N`-th root `τ` of `t` in `maxUnram Bt K`;
* **`cyc_twist`**: every locally constant additive `c : π₁(Bt) → ZMod d` gives `(c σ).val • g` as a Kummer character
  `kumChi_d α g` with `α ^ d = u ∈ K` having a `d`-th root in `maxUnram B K`, plus `kumChi_N τ ((-m) • g)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Cdec

end Cdec

section Zv

end Zv

section KZ

end KZ

section Twist2

end Twist2

section Cyc

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  {t : B} [IsLocalization.Away t Bt]
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]

variable (Bt K) in
/-- An `N`-th root of `t` in `maxUnram Bt K` (`t` is a unit of `Bt`). -/
theorem exists_tau {N : ℕ} [NeZero N] (hN : IsUnit (N : B)) :
    ∃ τ : (maxUnram Bt K)ˣ, (τ : maxUnram Bt K) ^ N = algebraMap K (maxUnram Bt K) (algebraMap B K t) := by
  have hN' : IsUnit (N : Bt) := by simpa using hN.map (algebraMap B Bt)
  obtain ⟨γ, hγm, hγ⟩ := exists_root_unit (R := Bt) (K := K) hN' (IsLocalization.Away.algebraMap_isUnit t)
  have hγ' : γ ^ N = algebraMap K (AlgebraicClosure K) (algebraMap B K t) := by
    rw [hγ, IsScalarTower.algebraMap_apply Bt K (AlgebraicClosure K), ← IsScalarTower.algebraMap_apply B Bt K]
  have ht0 : algebraMap B K t ≠ 0 := by
    intro h
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := Bt) t).map (algebraMap Bt K)
    rw [← IsScalarTower.algebraMap_apply, h] at hu
    exact not_isUnit_zero hu
  let γ1 : maxUnram Bt K := ⟨γ, hγm⟩
  have hγ1 : γ1 ^ N = algebraMap K (maxUnram Bt K) (algebraMap B K t) :=
    Subtype.ext (by rw [IntermediateField.coe_pow]; exact hγ')
  have hγ10 : γ1 ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne N)] at hγ1
    exact ht0 ((map_eq_zero_iff _ (algebraMap K (maxUnram Bt K)).injective).1 hγ1.symm)
  exact ⟨Units.mk0 γ1 hγ10, hγ1⟩

end Cyc

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1d =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1d): transfer of `u` to the shrunk chart, CRT ideals at the bad points

GLOB/REL PLAN v1, stages S1-S2 (pure algebra).
* `dvd_of_psi`, `psi_ne_zero`, **`exists_pow_mul_psi_pair`**: along `Ψ : Frac(G ⧸ p) →+* Frac A₁` induced by `κ : G →+* A₁`,
  `u = x / y` with `x ∣ c_x`, `y ∣ c_y` and `κ c_x = τ^e w₁`, `κ c_y = τ^e' w₂` (`wᵢ` units) gives
  `τ^(e+e') (Ψ u)^{±1}` integral (the `hj₁`, `hj₂` of `exists_glob_approx`, O2Gl1b);
* `isCoprime_span_map`, `pairwise_isCoprime_X_sub_C`, `isCoprime_X_sub_C_pow_span`: the CRT hypotheses `hJ`, `hJt`
  for `J i = (X - a_i) S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Psi

variable {G A₁ K₁ : Type*} [CommRing G] [CommRing A₁] [IsDomain A₁] [Field K₁] [Algebra A₁ K₁]
  [IsFractionRing A₁ K₁] (p : Ideal G) [p.IsPrime] (κ : G →+* A₁) (Ψ : FractionRing (G ⧸ p) →+* K₁)
  (hΨ : ∀ a, Ψ (algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p a)) = algebraMap A₁ K₁ (κ a))

include hΨ in
/-- **`τ^(e+e') (Ψ u)^{±1}` are integral** for `u = x / y`, `x ∣ c_x`, `y ∣ c_y`. -/
theorem exists_pow_mul_psi_pair {x y cx cy : G} {τ w₁ w₂ : A₁} {e e' : ℕ}
    (hx : Ideal.Quotient.mk p x ∣ Ideal.Quotient.mk p cx) (hy : Ideal.Quotient.mk p y ∣ Ideal.Quotient.mk p cy)
    (hx0 : Ideal.Quotient.mk p x ≠ 0) (hy0 : Ideal.Quotient.mk p y ≠ 0)
    (hcx : κ cx = τ ^ e * w₁) (hcy : κ cy = τ ^ e' * w₂) (hw₁ : IsUnit w₁) (hw₂ : IsUnit w₂) :
    (∃ a : A₁, algebraMap A₁ K₁ a = algebraMap A₁ K₁ τ ^ (e + e') *
        Ψ (algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p x) / algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p y))) ∧
    (∃ b : A₁, algebraMap A₁ K₁ b = algebraMap A₁ K₁ τ ^ (e + e') *
        (Ψ (algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p x) / algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p y)))⁻¹) := by
  have hΨu : Ψ (algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p x) / algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p y)) =
      algebraMap A₁ K₁ (κ x) / algebraMap A₁ K₁ (κ y) := by
    rw [map_div₀, hΨ, hΨ]
  have hy' : κ y ∣ τ ^ e' * w₂ := by rw [← hcy]; exact dvd_of_psi p κ Ψ hΨ hy
  have hx' : κ x ∣ τ ^ e * w₁ := by rw [← hcx]; exact dvd_of_psi p κ Ψ hΨ hx
  obtain ⟨a, ha⟩ := pow_mul_div_mem_range (K := K₁) (x := κ x) hy' hw₂ (psi_ne_zero p κ Ψ hΨ hy0)
  obtain ⟨b, hb⟩ := pow_mul_div_mem_range (K := K₁) (x := κ y) hx' hw₁ (psi_ne_zero p κ Ψ hΨ hx0)
  refine ⟨⟨τ ^ e * a, ?_⟩, ⟨τ ^ e' * b, ?_⟩⟩
  · rw [hΨu, map_mul, ha, map_pow, pow_add]; ring
  · rw [hΨu, inv_div, map_mul, hb, map_pow, pow_add]; ring

end Psi

section CRT

end CRT

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4a): generic glue for the S1 layer

* `comp_symm_sum_mem`, `comp_symm_dite_mem`, `mem_of_eq_mem`: membership of `ε ∘ θ⁻¹(Σ_i v_i)` in an additive
  subgroup from the summands (the piece sum of the PPT transfer, characters `if p ≤ ker then kumD else 0`);
* `exists_hj_pair`: `hj₁`, `hj₂` of `pp_chart` in `toPiQ` form from `u = x / y`, `x ∣ c_x`, `y ∣ c_y`
  (`exists_pow_mul_psi_pair` along a ring map `σ`), `fracMap_ne_zero`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC.EtMV

universe w v u

section ExtMem

end ExtMem

section HJ

variable {G G₁ : Type} [CommRing G] [CommRing G₁] (p : Ideal G) [p.IsPrime] (p₁ : minimalPrimes G₁)
  (σ : G →+* G₁) (Ψ : FractionRing (G ⧸ p) →+* FractionRing (G₁ ⧸ p₁.1))
  (hΨ : ∀ a : G, Ψ (algebraMap _ _ (Ideal.Quotient.mk p a)) = algebraMap _ _ (Ideal.Quotient.mk p₁.1 (σ a)))

include hΨ in
/-- **`hj₁`, `hj₂` of `pp_chart`** (`toPiQ` form) for `u = x / y`, `x ∣ c_x`, `y ∣ c_y`, `σ c = τ^e w` (`w` unit). -/
theorem exists_hj_pair {x y cx cy : G} {τ w₁ w₂ : G₁} {e e' : ℕ}
    (hx : Ideal.Quotient.mk p x ∣ Ideal.Quotient.mk p cx) (hy : Ideal.Quotient.mk p y ∣ Ideal.Quotient.mk p cy)
    (hx0 : Ideal.Quotient.mk p x ≠ 0) (hy0 : Ideal.Quotient.mk p y ≠ 0)
    (hcx : σ cx = τ ^ e * w₁) (hcy : σ cy = τ ^ e' * w₂) (hw₁ : IsUnit w₁) (hw₂ : IsUnit w₂) :
    (∃ b, algebraMap (G₁ ⧸ p₁.1) _ b = toPiQ τ p₁ ^ (e + e') *
        Ψ (algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p x) / algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p y))) ∧
    (∃ b, algebraMap (G₁ ⧸ p₁.1) _ b = toPiQ τ p₁ ^ (e + e') *
        (Ψ (algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p x) / algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p y)))⁻¹) := by
  have : p₁.1.IsPrime := p₁.2.1.1
  have hΨ' : ∀ a : G, Ψ (algebraMap _ _ (Ideal.Quotient.mk p a)) =
      algebraMap (G₁ ⧸ p₁.1) (FractionRing (G₁ ⧸ p₁.1)) (((Ideal.Quotient.mk p₁.1).comp σ) a) := hΨ
  have hcx' : ((Ideal.Quotient.mk p₁.1).comp σ) cx = Ideal.Quotient.mk p₁.1 τ ^ e * Ideal.Quotient.mk p₁.1 w₁ := by
    rw [RingHom.comp_apply, hcx, map_mul, map_pow]
  have hcy' : ((Ideal.Quotient.mk p₁.1).comp σ) cy = Ideal.Quotient.mk p₁.1 τ ^ e' * Ideal.Quotient.mk p₁.1 w₂ := by
    rw [RingHom.comp_apply, hcy, map_mul, map_pow]
  exact exists_pow_mul_psi_pair p ((Ideal.Quotient.mk p₁.1).comp σ) Ψ hΨ' hx hy hx0 hy0 hcx' hcy'
    (hw₁.map _) (hw₂.map _)

end HJ

end RamanujanPetersson.EtPBC.EtKum

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

variable {G G₁ : Type} [CommRing G] [CommRing G₁] (p : minimalPrimes G) (p₁ : minimalPrimes G₁)
  (σ : G →+* G₁) (Ψ : FractionRing (G ⧸ p.1) →+* FractionRing (G₁ ⧸ p₁.1))
  (hΨ : ∀ a : G, Ψ (algebraMap _ _ (Ideal.Quotient.mk p.1 a)) = algebraMap _ _ (Ideal.Quotient.mk p₁.1 (σ a)))

include hΨ in
/-- `exists_hj_pair` with `u = x / y` as an equation (pieces as `minimalPrimes`). -/
theorem exists_hj_pair' {x y cx cy : G} {τ w₁ w₂ : G₁} {e e' : ℕ} {u : FractionRing (G ⧸ p.1)}
    (hu : u = algebraMap (G ⧸ p.1) _ (Ideal.Quotient.mk p.1 x) / algebraMap (G ⧸ p.1) _ (Ideal.Quotient.mk p.1 y))
    (hx : Ideal.Quotient.mk p.1 x ∣ Ideal.Quotient.mk p.1 cx) (hy : Ideal.Quotient.mk p.1 y ∣ Ideal.Quotient.mk p.1 cy)
    (hx0 : Ideal.Quotient.mk p.1 x ≠ 0) (hy0 : Ideal.Quotient.mk p.1 y ≠ 0)
    (hcx : σ cx = τ ^ e * w₁) (hcy : σ cy = τ ^ e' * w₂) (hw₁ : IsUnit w₁) (hw₂ : IsUnit w₂) :
    (∃ b, algebraMap (G₁ ⧸ p₁.1) _ b = toPiQ τ p₁ ^ (e + e') * Ψ u) ∧
    (∃ b, algebraMap (G₁ ⧸ p₁.1) _ b = toPiQ τ p₁ ^ (e + e') * (Ψ u)⁻¹) := by
  have : p.1.IsPrime := p.2.1.1
  subst hu
  exact exists_hj_pair p.1 p₁ σ Ψ hΨ hx hy hx0 hy0 hcx hcy hw₁ hw₂

end HJ'

section ChartS1

end ChartS1

end RamanujanPetersson.EtPBC.EtKum

end

end


