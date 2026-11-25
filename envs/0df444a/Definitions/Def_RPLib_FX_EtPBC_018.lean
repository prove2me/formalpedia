-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_018
-- name    : RPLib_FX_EtPBC_018
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:02:37.955115+00:00
-- url     : https://prove2.me/theorems/5ede0333-6e76-5898-8e3d-c5a2a03f74fb
-- title:
--   Proper base change for the projective line, library file 018
-- statement:
--   File 018 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
--   * `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
--   * `S4.Def_RP_EtPBC_A_CovL1`: S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map
--   * `S4.Def_RP_EtPBC_A_CovEtL`: S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)
--   * `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
--   * `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovFbA`: S4-EtPBC-A, R4-T2 (G1d, part 1): lifting morphisms to fibres `Spec G` of chart algebras
--   * `S4.Def_RP_EtPBC_A_CovFbC`: S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover
--   * `S4.Def_RP_EtPBC_A_Inj0a`: S4-EtPBC-A, G1a: germs of a pulled-back section control the support
--   * `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
--   * `S4.Def_RP_EtPBC_A_Xi`: S4-EtPBC-A, M2 F5: the germ `ξ_s(b)` of a section of a pullback
--   * `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
--   * `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
--   * `S4.Def_RP_EtPBC_A_FinGenA`: S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes
--   * `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
--   * `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
--   * `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
--   * `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
--   * `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
--   * `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
--   * `S4.Def_RP_EtPBC_A_NagC`: S4-EtPBC-A, M4(N3): the relative normalization of a finite field point is finite
--   * `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
--   * `S4.Def_RP_EtPBC_A_ESheet`: S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_CovNbB`: S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`
--   * `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
--   * `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
--   * `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
--   * `S4.Def_RP_EtPBC_A_O2P2`: S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)
--   * `S4.Def_RP_EtPBC_A_O2Tr1`: S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open
--   * `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
--   * `S4.Def_RP_EtPBC_A_O2Km1`: S4-EtPBC-A, O2 M6 (O2Km1): the Shapiro scheme `W = D_o ×_P R` is affine
--   * `S4.Def_RP_EtPBC_A_O2Km6`: S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`
--   * `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
--   * `S4.Def_RP_EtPBC_A_O2ZarCh`: S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step
--   * `S4.Def_RP_EtPBC_A_O2Gl0`: S4-EtPBC-A, O2 GLOB (O2Gl0): stage S0 of the global step
--   * `S4.Def_RP_EtPBC_A_O2Km9a`: S4-EtPBC-A, O2 M6 (O2Km9a): roots of unity on the Shapiro pieces
--   * `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
--   * `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
--   * `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
--   * `S4.Def_RP_EtPBC_A_O2PP3a`: S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points
--   * `S4.Def_RP_EtPBC_A_O2L1a`: S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--   * `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
--   * `S4.Def_RP_EtPBC_A_O2L6b1`: S4-EtPBC-A, L6b1: the `K`-rational fibre `ι' : P¹_K ⟶ P¹_S` and the horizontal section `σ'` of `ι'^* Zz`
--   * `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_007
import Definitions.Def_RPLib_FX_EtPBC_010
import Definitions.Def_RPLib_FX_EtPBC_013

/-!
# Proper base change for the projective line, library file 018

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
* `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
* `S4.Def_RP_EtPBC_A_CovL1`: S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map
* `S4.Def_RP_EtPBC_A_CovEtL`: S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)
* `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
* `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovFbA`: S4-EtPBC-A, R4-T2 (G1d, part 1): lifting morphisms to fibres `Spec G` of chart algebras
* `S4.Def_RP_EtPBC_A_CovFbC`: S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover
* `S4.Def_RP_EtPBC_A_Inj0a`: S4-EtPBC-A, G1a: germs of a pulled-back section control the support
* `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
* `S4.Def_RP_EtPBC_A_Xi`: S4-EtPBC-A, M2 F5: the germ `ξ_s(b)` of a section of a pullback
* `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
* `S4.Def_RP_EtPBC_A_VPart`: S4-EtPBC-A, M2 F7/F9a: the value function on points, and base change from a section with the same values
* `S4.Def_RP_EtPBC_A_FinGenA`: S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes
* `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
* `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
* `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
* `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
* `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
* `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
* `S4.Def_RP_EtPBC_A_NagC`: S4-EtPBC-A, M4(N3): the relative normalization of a finite field point is finite
* `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
* `S4.Def_RP_EtPBC_A_ESheet`: S4-EtPBC-A, M4(E), ESheet: the sheets of `W ×_P Y` and the sections `f_j`
* `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
* `S4.Def_RP_EtPBC_A_CovNbB`: S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`
* `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
* `S4.Def_RP_EtPBC_A_O2S1`: S4-EtPBC-A, O2 M5 C-split: every class of `H²(P¹, F)` is a sum of one-point MV classes
* `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
* `S4.Def_RP_EtPBC_A_O2P2`: S4-EtPBC-A, O2 M5 P2: purity for Kummer characters (group level)
* `S4.Def_RP_EtPBC_A_O2Tr1`: S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open
* `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
* `S4.Def_RP_EtPBC_A_O2Km1`: S4-EtPBC-A, O2 M6 (O2Km1): the Shapiro scheme `W = D_o ×_P R` is affine
* `S4.Def_RP_EtPBC_A_O2Km6`: S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`
* `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
* `S4.Def_RP_EtPBC_A_O2ZarCh`: S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step
* `S4.Def_RP_EtPBC_A_O2Gl0`: S4-EtPBC-A, O2 GLOB (O2Gl0): stage S0 of the global step
* `S4.Def_RP_EtPBC_A_O2Km9a`: S4-EtPBC-A, O2 M6 (O2Km9a): roots of unity on the Shapiro pieces
* `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
* `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
* `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
* `S4.Def_RP_EtPBC_A_O2PP3a`: S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points
* `S4.Def_RP_EtPBC_A_O2L1a`: S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
* `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
* `S4.Def_RP_EtPBC_A_O2L6b1`: S4-EtPBC-A, L6b1: the `K`-rational fibre `ι' : P¹_K ⟶ P¹_S` and the horizontal section `σ'` of `ι'^* Zz`
* `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
-/

set_option autoImplicit false

set_option linter.defProp false

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

theorem exists_p1Pt (s : P1 k) : ∃ t : A1 k, p1Chart k s t = s := by
  have h : s ∈ (p1Chart k s).opensRange := by
    unfold p1Chart
    split_ifs with h
    · exact h
    · exact (P1.cover k s).resolve_left h
  rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at h
  exact h

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

theorem nbhdSys_obj (j : Nbhd s) : (nbhdSys Λ g s).obj j = freeSh Λ ((etPull g).obj j.1) := rfl

section EtPull

end EtPull

@[reassoc]
theorem fibToNbhd_fst (j : Nbhd s) : fibToNbhd g s j ≫ pullback.fst j.1.hom g = pullback.snd g s.pt ≫ j.2.left :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem fibToNbhd_snd (j : Nbhd s) : fibToNbhd g s j ≫ pullback.snd j.1.hom g = pullback.fst g s.pt :=
  pullback.lift_snd _ _ _

theorem fibToNbhd_map {j j' : Nbhd s} (a : j' ⟶ j) :
    fibToNbhd g s j' ≫ ((etPull g).map a.1).left = fibToNbhd g s j :=
  pullback.hom_ext
    ((Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_fst g a.1)).trans
      ((fibToNbhd_fst_assoc g s j' _).trans ((whisker_eq _ (nbhd_hom_w s a)).trans (fibToNbhd_fst g s j).symm))))
    ((Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_snd g a.1)).trans
      ((fibToNbhd_snd g s j').trans (fibToNbhd_snd g s j).symm)))

/-- The section `P_s ⟶ ι⁻¹(g⁻¹ V)` as a morphism of schemes. -/
def secL (j : Nbhd s) : fib g s ⟶ pullback (pullback.snd j.1.hom g) (fibι g s) :=
  pullback.lift (fibToNbhd g s j) (𝟙 _) ((fibToNbhd_snd g s j).trans (Category.id_comp _).symm)

@[reassoc]
theorem secL_fst (j : Nbhd s) : secL g s j ≫ pullback.fst (pullback.snd j.1.hom g) (fibι g s) = fibToNbhd g s j :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem secL_snd (j : Nbhd s) : secL g s j ≫ pullback.snd (pullback.snd j.1.hom g) (fibι g s) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- `ι^* Λ[g⁻¹ V]`. -/
abbrev fibFree (j : Nbhd s) : EtSh Λ (fib g s) := (pull (fibι g s) Λ).obj ((nbhdSys Λ g s).obj j)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_CovL1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map

* `isLocalization_of_isAwayMap`, `isAwayMap_of_isLocalization`, `isAwayMap_comp_equiv`: `IsAwayMap` at a unit is
  `IsLocalization.Away`.
* For `N = B₀[1/t₀]` and a `B₀`-algebra `E₀`, the base change `N ⊗[B₀] E₀` is `E₀[1/t₀]` (Mathlib
  `IsLocalization.Away.tensorRight`, with `Algebra.TensorProduct.rightAlgebra`). Given `f₀ : E₀ → e₀` and
  `g : e₀ → e` with `g τ` a unit, `τ = f₀ t₀`, **`red`** `: N ⊗[B₀] E₀ → e` is the induced map;
  `red_eq`, `red_alg`, **`red_surj`**, **`red_ker`** (`ker red = (ker f₀) · (N ⊗ E₀)` when `g` is an away map).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Away

end Away

section Red

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B₀ : Type u} (N : Type u) {E₀ e₀ e : Type u} [CommRing B₀] [CommRing N] [CommRing E₀] [CommRing e₀] [CommRing e]
  [Algebra B₀ N] [Algebra B₀ E₀] (t₀ : B₀) [IsLocalization.Away t₀ N]
  (f₀ : E₀ →+* e₀) (g : e₀ →+* e) (τ : e₀) (hτ : f₀ (algebraMap B₀ E₀ t₀) = τ) (hu : IsUnit (g τ))

/-- The reduction map over `N`. -/
theorem red_alg (h : N →+* e) (hh : h.comp (algebraMap B₀ N) = (g.comp f₀).comp (algebraMap B₀ E₀)) :
    (red N t₀ f₀ g τ hτ hu).comp (algebraMap N (N ⊗[B₀] E₀)) = h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t₀)
  ext b
  have e1 : algebraMap N (N ⊗[B₀] E₀) (algebraMap B₀ N b) =
      algebraMap E₀ (N ⊗[B₀] E₀) (algebraMap B₀ E₀ b) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  simp only [RingHom.comp_apply]
  rw [e1, red_eq]
  exact (congrArg (fun k => k b) hh).symm

theorem red_surj (hf : Function.Surjective f₀) (hg : ∀ y : e, ∃ (k : ℕ) (a : e₀), g τ ^ k * y = g a) :
    Function.Surjective (red N t₀ f₀ g τ hτ hu) := by
  intro y
  obtain ⟨k, a, hk⟩ := hg y
  obtain ⟨a', rfl⟩ := hf a
  obtain ⟨w, hw⟩ := IsLocalization.map_units (N ⊗[B₀] E₀)
    (⟨algebraMap B₀ E₀ t₀ ^ k, k, rfl⟩ : Submonoid.powers (algebraMap B₀ E₀ t₀))
  have hw' : (w : N ⊗[B₀] E₀) = algebraMap E₀ (N ⊗[B₀] E₀) (algebraMap B₀ E₀ t₀ ^ k) := hw
  refine ⟨↑w⁻¹ * algebraMap E₀ (N ⊗[B₀] E₀) a', ?_⟩
  have h1 : red N t₀ f₀ g τ hτ hu (w : N ⊗[B₀] E₀) = g τ ^ k := by
    rw [hw', red_eq, map_pow, map_pow, hτ]
  have h2 : red N t₀ f₀ g τ hτ hu (↑w⁻¹ : N ⊗[B₀] E₀) * g τ ^ k = 1 := by
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  rw [map_mul, red_eq, ← hk, ← mul_assoc, h2, one_mul]

theorem red_ker (hg0 : ∀ a : e₀, g a = 0 → ∃ k : ℕ, τ ^ k * a = 0) :
    RingHom.ker (red N t₀ f₀ g τ hτ hu) = (RingHom.ker f₀).map (algebraMap E₀ (N ⊗[B₀] E₀)) := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (algebraMap B₀ E₀ t₀)) x
    obtain ⟨k, hk⟩ := s.2
    have hk' : algebraMap B₀ E₀ t₀ ^ k = ↑s := hk
    have hxa : x * algebraMap E₀ (N ⊗[B₀] E₀) (algebraMap B₀ E₀ t₀ ^ k) = algebraMap E₀ (N ⊗[B₀] E₀) a := by
      rw [hk']; exact hs
    have h1 : g (f₀ a) = 0 := by
      rw [← red_eq N t₀ f₀ g τ hτ hu, ← hxa, map_mul, hx, zero_mul]
    obtain ⟨k', hk'⟩ := hg0 _ h1
    have h2 : algebraMap B₀ E₀ t₀ ^ k' * a ∈ RingHom.ker f₀ := by
      rw [RingHom.mem_ker, map_mul, map_pow, hτ, hk']
    obtain ⟨w, hw⟩ := IsLocalization.map_units (N ⊗[B₀] E₀)
      (⟨algebraMap B₀ E₀ t₀ ^ (k' + k), k' + k, rfl⟩ : Submonoid.powers (algebraMap B₀ E₀ t₀))
    have hw' : (w : N ⊗[B₀] E₀) = algebraMap E₀ (N ⊗[B₀] E₀) (algebraMap B₀ E₀ t₀ ^ (k' + k)) := hw
    have h3 : x * (w : N ⊗[B₀] E₀) = algebraMap E₀ (N ⊗[B₀] E₀) (algebraMap B₀ E₀ t₀ ^ k' * a) := by
      rw [hw', pow_add, map_mul, map_mul, ← hxa, mul_left_comm]
    have h4 : x * (w : N ⊗[B₀] E₀) ∈ (RingHom.ker f₀).map (algebraMap E₀ (N ⊗[B₀] E₀)) := by
      rw [h3]; exact Ideal.mem_map_of_mem _ h2
    have h5 := Ideal.mul_mem_right (↑w⁻¹ : N ⊗[B₀] E₀) _ h4
    rwa [mul_assoc, Units.mul_inv, mul_one] at h5
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, red_eq, RingHom.mem_ker.mp ha, map_zero]

end Red

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovEtL =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)

* `etK B M`: the ideal of the (closed) non-etale locus of a finitely presented `B`-algebra `M`;
  `etK_of_away` (`M[1/s]` etale gives `s ∈ etK`), `etK_le_iff` (`etK ≤ q` iff `M` is not etale at `q`),
  `etale_of_etK` (`etK = ⊤` gives `M` etale).
* `loc_compat`: along `ψ ∘ β₀ = β ∘ φ` with `φ`, `ψ` away maps at `t`, `β₀ t`, etale-at transports (`loc_etaleAt`).
* **`glob_etale`**: finite covers `βᵢ : Bᵢ → Eᵢ` of the two charts of `P¹_R`, glued over `N`, that are etale on a basic
  open `D(sᵢ)` with `sᵢ ≡ 1 mod m Eᵢ` (`m ≤ jac R`) are etale (`glob` on the non-etale ideals).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section EtK

variable (B M : Type u) [CommRing B] [CommRing M] [Algebra B M]

variable {B M} [Algebra.FinitePresentation B M]

theorem etale_of_etK (h : etK B M = ⊤) : Algebra.Etale B M := by
  refine Algebra.etaleLocus_eq_univ_iff_etale.1 (Set.eq_univ_of_forall fun q => ?_)
  by_contra hq
  have h1 := (etK_le_iff q).2 hq
  rw [h, top_le_iff] at h1
  exact q.isPrime.ne_top h1

end EtK

end RamanujanPetersson.EtPBC.Cov

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

theorem mk_aeval_eq {n : ℕ} (P Q : MvPolynomial σ A)
    (h : ∀ x : σ →₀ ℕ, x.degree < n → P.coeff x = Q.coeff x) :
    Ideal.Quotient.mk ((Ideal.span (Set.range a)) ^ n) (MvPolynomial.aeval a P) =
      Ideal.Quotient.mk ((Ideal.span (Set.range a)) ^ n) (MvPolynomial.aeval a Q) := by
  rw [Ideal.Quotient.eq, ← map_sub]
  exact aeval_mem_pow_of_coeff a (P - Q) fun x hx => by
    rw [MvPolynomial.coeff_sub, h x hx, sub_self]

end HatN1

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibB =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`

* `ψx K x : Γ(V) → K`, `px K x = ker ψx` (prime), `ker_appTop_eq`, `κx : κ(p) → K`, `κx_algebraMap`.
* For `P` over `p` with `κ(p) ≅ κ(P)` (`hbij`): `χx : R' → K`, `χx_algebraMap`, **`hxχ`**:
  `Spec χx ≫ hV V R' = x`, `xχ_appTop`.
* **`yxMap K gV π R' x x' hx' : Y_x ⟶ Y ×_V Spec R'`**, `yxMap_fR`, `yxMap_gS`, `yxMap_PhiY_tmul`.
* `exists_fibreRing`: a ring map `κ(p) ⊗ Γ(Y, U) → Γ(Y_x, fx⁻¹ U)`, `c ⊗ b ↦ c · fx^* b`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Res

variable (K : Type u) [Field K] {V : Scheme.{u}} (x : Spec (CommRingCat.of K) ⟶ V)

theorem ker_appTop_eq : RingHom.ker x.appTop.hom = px K x := by
  ext a
  rw [RingHom.mem_ker, RingHom.mem_ker]
  have hinj := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
  constructor
  · intro h
    change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (x.appTop.hom a) = 0
    rw [h, map_zero]
  · intro h
    exact hinj (h.trans (map_zero _).symm)

theorem κx_unit : (px K x).primeCompl ≤ (IsUnit.submonoid K).comap (ψx K x) := fun _ ha =>
  (IsUnit.mem_submonoid_iff _).mpr
    (isUnit_iff_ne_zero.mpr fun h => (Ideal.mem_primeCompl_iff.mp ha) (RingHom.mem_ker.mpr h))

end Res

section Map

end Map

end RamanujanPetersson.EtPBC.Z3

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

variable {E G : Type u} [CommRing E] [CommRing G] (θ : E →+* G) (sθ : Function.Surjective θ) {W : Scheme.{u}}

theorem liftW_θ (w : W ⟶ Spec (CommRingCat.of E)) (hk : RingHom.ker θ ≤ RingHom.ker (εW w)) (e : E) :
    liftW θ sθ w hk (θ e) = εW w e :=
  θ.liftOfSurjective_comp_apply sθ ⟨εW w, hk⟩ e

/-- **The lift `W ⟶ Spec G`** of `w : W ⟶ Spec E` through the closed immersion `Spec θ`. -/
def gW (w : W ⟶ Spec (CommRingCat.of E)) (hk : RingHom.ker θ ≤ RingHom.ker (εW w)) :
    W ⟶ Spec (CommRingCat.of G) :=
  W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (liftW θ sθ w hk))

theorem gW_θ (w : W ⟶ Spec (CommRingCat.of E)) (hk : RingHom.ker θ ≤ RingHom.ker (εW w)) :
    gW θ sθ w hk ≫ Spec.map (CommRingCat.ofHom θ) = w := by
  refine Eq.trans ?_ (toSpecΓ_SpecMap_appTop w)
  rw [gW, Category.assoc, ← Spec.map_comp]
  refine congrArg (W.toSpecΓ ≫ ·) (congrArg Spec.map ?_)
  ext e
  exact liftW_θ θ sθ w hk e

theorem ker_comp {W' : Scheme.{u}} (f : W' ⟶ W) (w : W ⟶ Spec (CommRingCat.of E))
    (hk : RingHom.ker θ ≤ RingHom.ker (εW w)) : RingHom.ker θ ≤ RingHom.ker (εW (f ≫ w)) := by
  intro e he
  rw [RingHom.mem_ker, εW_comp, RingHom.comp_apply, RingHom.mem_ker.mp (hk he), map_zero]

/-- **Naturality of the lift.** -/
theorem gW_comp {W' : Scheme.{u}} (f : W' ⟶ W) (w : W ⟶ Spec (CommRingCat.of E))
    (hk : RingHom.ker θ ≤ RingHom.ker (εW w)) :
    f ≫ gW θ sθ w hk = gW θ sθ (f ≫ w) (ker_comp θ f w hk) := by
  rw [gW, gW, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp]
  refine congrArg (W'.toSpecΓ ≫ ·) (congrArg Spec.map ?_)
  ext g
  obtain ⟨e, rfl⟩ := sθ g
  show f.appTop.hom (liftW θ sθ w hk (θ e)) = liftW θ sθ (f ≫ w) (ker_comp θ f w hk) (θ e)
  rw [liftW_θ, liftW_θ, εW_comp, RingHom.comp_apply]

end Lift

section Ker

variable {A B R' E k : Type u} [CommRing A] [CommRing B] [CommRing R'] [CommRing E] [CommRing k]
  [Algebra A B] [Algebra A R'] [Algebra (R' ⊗[A] B) E] (χ' : R' →+* k) {W : Scheme.{u}}

theorem εW_rE (w : W ⟶ Spec (CommRingCat.of E)) (v : W ⟶ Spec (CommRingCat.of k))
    (hv : w ≫ Spec.map (CommRingCat.ofHom (rE (A := A) (B := B) (R' := R') (E := E))) =
      v ≫ Spec.map (CommRingCat.ofHom χ')) :
    (εW w).comp (rE (A := A) (B := B)) = (εW v).comp χ' := by
  rw [← εW_SpecMap, ← εW_SpecMap, hv]

end Ker

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFbC =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover

* `hxL_of`: a ring map `χ' : R' → K` over `x` gives a lift `Spec χ'` of `x`.
* **`fromSpec_yx`**: for a chart `U` of `Y` and `θ : E → Γ(T, q⁻¹ fx⁻¹ U)` as in `CoverLift`,
  `T_U ⟶ T ⟶ Y_x ⟶ Y_{V'}` equals `Spec θ ≫ Spec (alg) ≫ chY`.
* `mono_yxMap`: `Y_x ⟶ Y_{V'}` is a monomorphism.
* `pb_key`: the square of a chart of the pulled back gluing cover.
* `gW_congr`: `gW` only depends on `w`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

universe u

/-- `gW` depends only on the morphism `w`. -/
theorem gW_congr {E G : Type u} [CommRing E] [CommRing G] (θ : E →+* G) (sθ : Function.Surjective θ)
    {W : Scheme.{u}} {w w' : W ⟶ Spec (CommRingCat.of E)} (h : w = w')
    (hk : RingHom.ker θ ≤ RingHom.ker (εW w)) (hk' : RingHom.ker θ ≤ RingHom.ker (εW w')) :
    gW θ sθ w hk = gW θ sθ w' hk' := by
  subst h
  rfl

section Chart

attribute [local instance] algT

end Chart

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0a =====
section

/-!
# S4-EtPBC-A, G1a: germs of a pulled-back section control the support

For `f : X ⟶ Y`, a geometric point `s` of `X`, a sheaf `G` on `Y`, `V : Y.Etale`, a fibre point `b` of `s` over
`f⁻¹ V` and `z ∈ G(V)`:
* `cpt f s b : V.left`, the point of `V` under `b`; `cpt_map` (naturality in `V`);
* **`comap_germ_eq_zero`**: if the germ of `η_G(z) ∈ (f^* G)(f⁻¹ V)` at `b` vanishes, so does the germ of `z` at `b`
  for the point `comapPt f s` of `Y` (Mathlib's stalk isomorphism `(f^* G)_s ≅ G_{s ≫ f}`, `comapIso_hom_app`);
* `exists_nbhd_of_comap_germ`: such a germ vanishes on an etale neighbourhood;
* **`cpt_not_mem_supp`**: then `cpt b` is not in the support `supp G z`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X)

theorem cpt_map {V W : Y.Etale} (g : W ⟶ V) (b : s.point.fiber.obj ((etPull f).obj W)) :
    cpt f s (s.point.fiber.map ((etPull f).map g) b) = g.left (cpt f s b) := by
  have h : (s.liftOf (s.point.fiber.map ((etPull f).map g) b)).left =
      (s.liftOf b).left ≫ ((etPull f).map g).left := rfl
  have h2 := etPull_map_left_fst f g
  simp only [cpt, h]
  exact congrArg (fun φ => φ.base ((s.liftOf b).left (default : Spec (CommRingCat.of s.Ω)))) h2

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

/-- The value at `x ∈ fib π t` of a germ `e ∈ (π_* C)_t`. -/
def psi (e : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj ((push π Λ).obj (constSh Λ Y M)).obj) (x : fib π t) : M :=
  cval (exists_rep π t e).choose_spec.choose (fibToNbhd π t (exists_rep π t e).choose x)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_Xi =====
section

/-!
# S4-EtPBC-A, M2 F5: the germ `ξ_s(b)` of a section of a pullback

For `f : X ⟶ Y`, a geometric point `s` of `X`, a sheaf `G` on `Y` and `b : Λ_X ⟶ f^* G`:
* **`pullStalkIso_germ`**: the stalk isomorphism `(f^* G)_s ≅ G_{s ≫ f}` sends the germ of `η_G(z)` at `b'` to the germ
  of `z` at the corresponding fibre point of `s ≫ f`;
* `xi f s G b ∈ G_{s ≫ f}`: the image of the germ of `b(1)`; `xi_sub`, `germ_eq_zero_of_xi`;
* **`xi_bc`**: for `f = ι : P_s ⟶ P`, `ξ(u_v ≫ ι^* φ)` is the germ of `φ(1)` at the neighbourhood point.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Xi

variable {Λ : Type u} [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X)

theorem xi_sub (G : EtSh Λ Y) (b b' : unitSh Λ X ⟶ (pull f Λ).obj G) :
    xi f s G (b - b') = xi f s G b - xi f s G b' := by
  unfold xi
  rw [sc_sub]
  exact (congrArg ((pullStalkIso f Λ s).hom.app G).hom (LinearMap.map_sub _ _ _)).trans (LinearMap.map_sub _ _ _)

end Xi

section XiBC

end XiBC

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

/-- The `Ω`-point of the fibre `fib π (τ ≫ π_s ≫ ι)` given by `τ`. -/
def xMor (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι) :
    Spec (CommRingCat.of Ω) ⟶ fib π ((sigPt ι π τ).map ι) :=
  pullback.lift (τ ≫ pullback.fst π ι) (𝟙 _) (xPt_cond ι π τ)

theorem fibToNbhd_comp_fst (s' : GeomPt P) (j : Nbhd s') (x : Spec (CommRingCat.of s'.Ω) ⟶ fib π s')
    (hx : x ≫ pullback.snd π s'.pt = 𝟙 _) :
    x ≫ fibToNbhd π s' j ≫ pullback.fst j.1.hom π = (s'.liftOf j.2).left := by
  exact (congrArg (x ≫ ·) (fibToNbhd_fst π s' j)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (s'.liftOf j.2).left) hx).trans (Category.id_comp _)))

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

theorem ysj_cond (j : Nbhd s) :
    (pullback.snd π (fibι g s) ≫ fibToNbhd g s j) ≫ pullback.snd j.1.hom g = pullback.fst π (fibι g s) ≫ π :=
  (Category.assoc _ _ _).trans ((congrArg (pullback.snd π (fibι g s) ≫ ·) (fibToNbhd_snd g s j)).trans
    pullback.condition.symm)

end BC

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FinGenA =====
section

/-!
# S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes

* **`exists_affine_le`**: every etale neighbourhood of a geometric point is refined by one with affine total space;
* `exists_repG_aff`, `exists_pullRepG_aff`, `exists_fg_aff`: the representations of `FinGen` over affines;
* **`bcSurj_of_fg_aff`**: `BCSurj 0` for `G` from `BCSurj 0` for the subsheaves `ker (coker φ)` generated by finitely
  many sections `φ : ∐ Λ[W x] ⟶ G` with every `(W x).left` affine.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

/-- **Every etale neighbourhood is refined by an affine one.** -/
theorem exists_affine_le {T : Scheme.{u}} (t : GeomPt T) (j : Nbhd t) :
    ∃ (j' : Nbhd t) (_ : j' ⟶ j), IsAffine j'.1.left := by
  obtain ⟨p0⟩ : Nonempty (Spec (CommRingCat.of t.Ω)) := ⟨default⟩
  have hsub : ∀ p : Spec (CommRingCat.of t.Ω), p = p0 := fun p =>
    Subsingleton.elim (α := PrimeSpectrum t.Ω) _ _
  obtain ⟨R, f, hf, ⟨y, hy⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := j.1.left)
    (x := nbv t j p0) (U := ⊤) (by simp)
  have : IsOpenImmersion f := hf
  have hR : Set.range (nbv t j) ⊆ Set.range f := by
    rintro _ ⟨p, rfl⟩
    exact ⟨y, by rw [hsub p]; exact hy⟩
  let v : Spec (CommRingCat.of t.Ω) ⟶ Spec R := IsOpenImmersion.lift f (nbv t j) hR
  have hv : v ≫ f = nbv t j := IsOpenImmersion.lift_fac f (nbv t j) hR
  let E : T.Etale := MorphismProperty.Over.mk ⊤ (f ≫ nbh t j) (by
    have : Etale (nbh t j) := j.1.prop
    infer_instance)
  have hvE : v ≫ (f ≫ nbh t j) = t.pt := by rw [← Category.assoc, hv, nbv_w]
  let j' : Nbhd t := t.point.fiber.elementsMk E (Over.homMk v hvE :
    CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget T).obj E)
  let a : E ⟶ j.1 := MorphismProperty.Over.homMk f rfl trivial
  refine ⟨j', ⟨a, fiber_ext t ((liftOf_map_left' t a j'.2).trans hv)⟩, ?_⟩
  show IsAffine (Spec R)
  infer_instance

section Gen

variable {Λ : Type u} [CommRing Λ] {X P : Scheme.{u}} (ι : X ⟶ P)

theorem exists_repG_aff (t : GeomPt P) (G : EtSh Λ P)
    (e : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj G.obj) :
    ∃ (j : Nbhd t) (z : G.obj.obj (op j.1)), IsAffine j.1.left ∧
      (t.point.toPresheafFiber j.1 j.2 G.obj).hom z = e := by
  obtain ⟨j, z, hz⟩ := exists_repG t G e
  obtain ⟨j', a, hj'⟩ := exists_affine_le t j
  have hw : G.obj.map a.1.op ≫ t.point.toPresheafFiber j'.1 j'.2 G.obj = t.point.toPresheafFiber j.1 j.2 G.obj :=
    (t.point.toPresheafFiber_w a.1 j'.2 G.obj).trans (congrArg (fun x => t.point.toPresheafFiber j.1 x G.obj) a.2)
  exact ⟨j', (G.obj.map a.1.op).hom z, hj', (congrArg (fun φ => φ.hom z) hw).trans hz⟩

end Gen

section Red

end Red

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

section RU

variable {U₁ U₂ P : Scheme.{u}} (h : U₁ ⟶ U₂) (Φ : U₂ ⟶ P)

theorem muU_fibToNbhd (t : GeomPt P) (j : Nbhd t) :
    fibToNbhd (h ≫ Φ) t j ≫ muU h Φ j.1 = nuU h Φ t ≫ fibToNbhd Φ t j := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (muU_fst h Φ j.1)).trans ((fibToNbhd_fst (h ≫ Φ) t j).trans ?_))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (whisker_eq _ (fibToNbhd_fst Φ t j))).symm
    exact (pullback.lift_snd_assoc _ _ _ _).symm
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (muU_snd h Φ j.1)).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker (fibToNbhd_snd (h ≫ Φ) t j) h).trans ?_)))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (whisker_eq _ (fibToNbhd_snd Φ t j))).symm
    exact (pullback.lift_fst _ _ _).symm

end RU

end RamanujanPetersson.EtPBC.FBC

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

section C1

variable {P P' Y U Ps : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (Φ : U ⟶ P') (h : U ⟶ Y)
  (hh : h ≫ π = Φ ≫ f) (ι' : Ps ⟶ P')

/-- The point maps of the two composites in `C1s` agree. -/
theorem C1s_key (V : P.Etale) :
    ((etPull (pullback.snd Φ ι')).map ((etPullCompIso ι' f).inv.app V)).left ≫
    muq (hsU π f Φ h hh ι' (ι' ≫ f) rfl) (pullback.snd π (ι' ≫ f)) (pullback.snd Φ ι')
      (hsU_snd π f Φ h hh ι' (ι' ≫ f) rfl) ((etPull (ι' ≫ f)).obj V) ≫
    ((etPullCompIso (pullback.snd π (ι' ≫ f)) (ι' ≫ f)).inv.app V).left ≫
    muq (pullback.fst π (ι' ≫ f)) π (pullback.snd π (ι' ≫ f) ≫ (ι' ≫ f)) pullback.condition V =
  ((etPullCompIso (pullback.snd Φ ι') ι').inv.app ((etPull f).obj V)).left ≫
    muq (pullback.fst Φ ι') Φ (pullback.snd Φ ι' ≫ ι') pullback.condition ((etPull f).obj V) ≫
    ((etPullCompIso Φ f).inv.app V).left ≫ muq h π (Φ ≫ f) hh V := by
  have kd := muq_fst (pullback.fst π (ι' ≫ f)) π (pullback.snd π (ι' ≫ f) ≫ (ι' ≫ f)) pullback.condition V
  have kc := etPullCompIso_inv_fst (pullback.snd π (ι' ≫ f)) (ι' ≫ f) V
  have kb := muq_fst_assoc (hsU π f Φ h hh ι' (ι' ≫ f) rfl) (pullback.snd π (ι' ≫ f)) (pullback.snd Φ ι')
    (hsU_snd π f Φ h hh ι' (ι' ≫ f) rfl) ((etPull (ι' ≫ f)).obj V) (pullback.fst V.hom (ι' ≫ f))
  have ka := etPull_map_left_fst_assoc (pullback.snd Φ ι') ((etPullCompIso ι' f).inv.app V)
    (pullback.fst V.hom (ι' ≫ f))
  have kx := etPullCompIso_inv_fst ι' f V
  have kd' := muq_fst h π (Φ ≫ f) hh V
  have kc' := etPullCompIso_inv_fst Φ f V
  have kb' := muq_fst_assoc (pullback.fst Φ ι') Φ (pullback.snd Φ ι' ≫ ι') pullback.condition
    ((etPull f).obj V) (pullback.fst V.hom f)
  have ka' := etPullCompIso_inv_fst_assoc (pullback.snd Φ ι') ι' ((etPull f).obj V) (pullback.fst V.hom f)
  have sd := muq_snd (pullback.fst π (ι' ≫ f)) π (pullback.snd π (ι' ≫ f) ≫ (ι' ≫ f)) pullback.condition V
  have sc := etPullCompIso_inv_snd_assoc (pullback.snd π (ι' ≫ f)) (ι' ≫ f) V (pullback.fst π (ι' ≫ f))
  have sb := muq_snd_assoc (hsU π f Φ h hh ι' (ι' ≫ f) rfl) (pullback.snd π (ι' ≫ f)) (pullback.snd Φ ι')
    (hsU_snd π f Φ h hh ι' (ι' ≫ f) rfl) ((etPull (ι' ≫ f)).obj V) (pullback.fst π (ι' ≫ f))
  have shs := hsU_fst π f Φ h hh ι' (ι' ≫ f) rfl
  have sa := etPull_map_left_snd_assoc (pullback.snd Φ ι') ((etPullCompIso ι' f).inv.app V)
    (pullback.fst Φ ι' ≫ h)
  have sd' := muq_snd h π (Φ ≫ f) hh V
  have sc' := etPullCompIso_inv_snd_assoc Φ f V h
  have sb' := muq_snd_assoc (pullback.fst Φ ι') Φ (pullback.snd Φ ι' ≫ ι') pullback.condition
    ((etPull f).obj V) h
  have sa' := etPullCompIso_inv_snd_assoc (pullback.snd Φ ι') ι' ((etPull f).obj V) (pullback.fst Φ ι' ≫ h)
  apply pullback.hom_ext
  · exact ((assoc4 _ _ _ _ _).trans <| (whisker_eq _ (whisker_eq _ (whisker_eq _ kd))).trans <|
      (whisker_eq _ (whisker_eq _ kc)).trans <| (whisker_eq _ kb).trans <| ka.trans ((Category.assoc _ _ _).trans (whisker_eq _ kx))).trans
      ((assoc4 _ _ _ _ _).trans <| (whisker_eq _ (whisker_eq _ (whisker_eq _ kd'))).trans <|
        (whisker_eq _ (whisker_eq _ kc')).trans <| (whisker_eq _ kb').trans ka').symm
  · exact ((assoc4 _ _ _ _ _).trans <| (whisker_eq _ (whisker_eq _ (whisker_eq _ sd))).trans <|
      (whisker_eq _ (whisker_eq _ sc)).trans <| (whisker_eq _ sb).trans <|
        (whisker_eq _ (whisker_eq _ shs)).trans sa).trans
      ((assoc4 _ _ _ _ _).trans <| (whisker_eq _ (whisker_eq _ (whisker_eq _ sd'))).trans <|
        (whisker_eq _ (whisker_eq _ sc')).trans <| (whisker_eq _ sb').trans sa').symm

end C1

section B3

end B3

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

include hS in
theorem wsec_exact (W : (Over T)ᵒᵖ) (x : ((Over.forget T).op ⋙ E.obj).obj W)
    (hx : ((wh b T).app W).hom x = 0) : ∃ y, ((wh a T).app W).hom y = x :=
  sec_exact (S := ShortComplex.mk a b hab) hS ((Over.forget T).obj W.unop) x hx

include hS in
theorem wsec_inj (W : (Over T)ᵒᵖ) : Function.Injective ((wh a T).app W).hom :=
  sec_inj (S := ShortComplex.mk a b hab) hS ((Over.forget T).obj W.unop)

include hab in
theorem wsec_fg (W : (Over T)ᵒᵖ) (y : ((Over.forget T).op ⋙ F.obj).obj W) :
    ((wh b T).app W).hom (((wh a T).app W).hom y) = 0 :=
  sec_fg (S := ShortComplex.mk a b hab) ((Over.forget T).obj W.unop) y

theorem secT_one : ((secT σ).app (op (Over.mk (𝟙 T)))).hom ((constUnit (ModuleCat.of Λ Λ) T).hom 1) = σ := by
  have h1 : constUnit (ModuleCat.of Λ Λ) T ≫ (secT σ).app (op (Over.mk (𝟙 T))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ σ) := by
    rw [← homConstEquiv_apply, secT, LinearEquiv.apply_symm_apply]
  have h2 := congrArg (fun φ => φ.hom (1 : Λ)) h1
  exact h2.trans (one_smul Λ σ)

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

theorem inl_bPP : pushout.inl _ _ ≫ bPP q N a' b' w' = (pull q Λ).map b' ≫ (pullConst Λ q (ModuleCat.of Λ Λ)).hom :=
  pushout.inl_desc _ _ _

theorem aPP_bPP : aPP q N a' ≫ bPP q N a' b' w' = 0 :=
  pushout.inr_desc _ _ _

variable {Z : Scheme.{u}} (ψ' : Z ⟶ Ys) (τ : Epp q N a' ⟶ (push ψ' Λ).obj (constSh Λ Z N))

/-- **`a' ≫ κ₀ = q_*(uC)`** when `τ` extends `uC`. -/
theorem a_kap0 (hτ : aPP q N a' ≫ τ = uC ψ' N) :
    a' ≫ kap0 q N a' ψ' τ = (push q Λ).map (uC ψ' N) ≫ (pushCompIso Λ ψ' q).hom.app _ := by
  have h1 : a' ≫ (pullAdj q Λ).homEquiv _ _ (pushout.inl _ _ ≫ τ) =
      (pullAdj q Λ).homEquiv _ _ ((pull q Λ).map a' ≫ pushout.inl _ _ ≫ τ) :=
    ((pullAdj q Λ).homEquiv_naturality_left a' _).symm
  have h2 : (pull q Λ).map a' ≫ pushout.inl _ _ ≫ τ =
      (pullAdj q Λ).counit.app (constSh Λ Ys N) ≫ uC ψ' N := by
    rw [← Category.assoc, pushout.condition, Category.assoc]
    exact whisker_eq _ hτ
  have h3 : (pullAdj q Λ).homEquiv _ _ ((pullAdj q Λ).counit.app (constSh Λ Ys N) ≫ uC ψ' N) =
      (push q Λ).map (uC ψ' N) :=
    ((pullAdj q Λ).homEquiv_naturality_right _ _).trans ((eq_whisker (((pullAdj q Λ).homEquiv_unit _ _ _).trans
      ((pullAdj q Λ).right_triangle_components _)) _).trans (Category.id_comp _))
  calc a' ≫ kap0 q N a' ψ' τ
      = (a' ≫ (pullAdj q Λ).homEquiv _ _ (pushout.inl _ _ ≫ τ)) ≫ (pushCompIso Λ ψ' q).hom.app _ :=
        (Category.assoc _ _ _).symm
    _ = _ := by rw [h1, h2, h3]

end Push

section T1

end T1

end RamanujanPetersson.EtPBC.DescK

end

end

-- ===== S4.Def_RP_EtPBC_A_EGeoB =====
section

/-!
# S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections

* `exists_common_nbhd`: finitely many etale neighbourhoods of `t` have a common affine refinement;
* `FibPts x W := Σ j, fibre of W j over x̄`, finite (`finite_fibPts`); **`exists_split`**: an affine `T` with a point
  `t` over `x̄` and maps `τ p : T ⟶ W p.1` sending `t` to `p.2`, for all `p : FibPts x W`;
* `exists_opens_unique`, `specializes_of_unique`: shrinking `T` so that `fpt t` is its only point over `x`; then every
  point of `T` over a specialisation of `x` is a specialisation of `fpt t`;
* `prd W T` (`W ×_P T`), `prW`, `prT`, `sec τ` (the section of `prT` given by `τ : T ⟶ W`), `pair a t`;
* **`exists_eq_tau`**: if every point of `W` over `x̄` is `τ b (t)` and `fpt t ⤳ fpt t'` (`t'` over `ȳ`), every point
  `a` of `W` over `ȳ` is `τ b (t')` for some `b`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech

universe u

variable {P : Scheme.{u}}

/-- **Shrinking so that `fpt t` is the only point over `x`.** -/
theorem exists_opens_unique (T : P.Etale) [QuasiCompact T.hom] (x : P) (t : (geomPtAt x).point.fiber.obj T) :
    ∃ O : T.left.Opens, fpt x t ∈ O ∧ ∀ v ∈ O, T.hom v = x → v = fpt x t := by
  classical
  have hS : {v | T.hom v = x ∧ v ≠ fpt x t}.Finite :=
    (T.hom.finite_preimage_singleton x).subset fun v hv => hv.1
  let C : Set T.left := ⋃ v ∈ hS.toFinset, closure {v}
  have hC : IsClosed C := isClosed_biUnion_finset fun v _ => isClosed_closure
  refine ⟨⟨Cᶜ, hC.isOpen_compl⟩, ?_, ?_⟩
  · show fpt x t ∉ C
    simp only [C, Set.mem_iUnion, not_exists]
    intro v hv hcl
    rw [Set.Finite.mem_toFinset] at hv
    have h1 : v ⤳ fpt x t := specializes_iff_mem_closure.2 hcl
    exact hv.2 (eq_of_specializes_of_etale T.hom h1 (hv.1.trans (fib_over x t).symm))
  · intro v hv hvx
    by_contra hne
    exact hv (Set.mem_biUnion (hS.mem_toFinset.2 ⟨hvx, hne⟩) (subset_closure rfl))

section Prd

variable (W T : P.Etale)

variable {W T}

theorem sec_snd (τ : T ⟶ W) : (sec τ).left ≫ pullback.snd W.hom T.hom = 𝟙 _ := pullback.lift_snd _ _ _

theorem sec_fst (τ : T ⟶ W) : (sec τ).left ≫ pullback.fst W.hom T.hom = τ.left := pullback.lift_fst _ _ _

theorem pair_fst (y : P) (a : (geomPtAt y).point.fiber.obj W) (t : (geomPtAt y).point.fiber.obj T) :
    fl y (pair y a t) ≫ pullback.fst W.hom T.hom = fl y a := pullback.lift_fst _ _ _

theorem pair_snd (y : P) (a : (geomPtAt y).point.fiber.obj W) (t : (geomPtAt y).point.fiber.obj T) :
    (geomPtAt y).point.fiber.map (prT W T) (pair y a t) = t :=
  fiber_ext _ (pullback.lift_snd _ _ _)

/-- **Points of `W ×_P T` over `fpt t` lie on the sections**, if every point of `W` over `x̄` is some `τ b (t)`. -/
theorem cover_gen (x : P) (t : (geomPtAt x).point.fiber.obj T) (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W))
    (hτ : ∀ b, (geomPtAt x).point.fiber.map (τ b) t = b) (e : (prd W T).left)
    (he : pullback.snd W.hom T.hom e = fpt x t) : ∃ b, e ∈ Set.range (sec (τ b)).left := by
  obtain ⟨c, hc, rfl⟩ := exists_lift_fib (prT W T) x t e he
  let b := (geomPtAt x).point.fiber.map (prW W T) c
  refine ⟨b, fpt x t, ?_⟩
  have h1 : c = (geomPtAt x).point.fiber.map (sec (τ b)) t := by
    refine fiber_ext _ ?_
    change fl x c = fl x t ≫ (sec (τ b)).left
    have e1 : fl x t ≫ (τ b).left = fl x c ≫ pullback.fst W.hom T.hom :=
      congrArg (fun z => ((geomPtAt x).liftOf z).left) (hτ b)
    have e2 : fl x c ≫ pullback.snd W.hom T.hom = fl x t :=
      congrArg (fun z => ((geomPtAt x).liftOf z).left) hc
    refine pullback.hom_ext ?_ ?_
    · exact e1.symm.trans ((congrArg (fl x t ≫ ·) (sec_fst (τ b)).symm).trans (Category.assoc _ _ _).symm)
    · exact e2.trans ((Category.comp_id _).symm.trans
        ((congrArg (fl x t ≫ ·) (sec_snd (τ b))).symm.trans (Category.assoc _ _ _).symm))
  exact (congrArg (fpt x) h1).symm

end Prd

end RamanujanPetersson.EtPBC.GenGeo

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

theorem germ_gsum {T : P.Etale} {t : (geomPtAt x).point.fiber.obj T} {τ : ∀ p : FibPts x W, T ⟶ W p.1}
    (hτ : ∀ p, (geomPtAt x).point.fiber.map (τ p) t = p.2) (c : FibPts x W →₀ Λ) :
    GenAlg.germ G x t (gsum G f τ c) = GenAlg.rel W G f x c := by
  rw [GenAlg.rel, gsum, GenAlg.germ, Finsupp.apply_linearCombination]
  exact congrArg (fun v => Finsupp.linearCombination Λ v c) (funext fun p =>
    (germ_map G x (τ p) t (f p.1)).trans (congrArg (fun b => GenAlg.germ G x b (f p.1)) (hτ p)))

theorem gsum_comp {T' T : P.Etale} (ρ : T' ⟶ T) (τ : ∀ p : FibPts x W, T ⟶ W p.1) (c : FibPts x W →₀ Λ) :
    gsum G f (fun p => ρ ≫ τ p) c = (G.obj.map ρ.op).hom (gsum G f τ c) := by
  rw [gsum, gsum, Finsupp.apply_linearCombination]
  exact congrArg (fun v => Finsupp.linearCombination Λ v c) (funext fun p =>
    congrArg (fun φ => φ.hom (f p.1)) (G.obj.map_comp (τ p).op ρ.op))

end Gsum

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_NagC =====
section

/-!
# S4-EtPBC-A, M4(N3): the relative normalization of a finite field point is finite

* `finite_integralClosure_of_gen`: `A` of finite type over a perfect field `K`, `F` a field generated (as a field)
  by the image of `A`, `L` finite over `F` ⇒ the integral closure of `A` in `L` is a finite `A`-module (via `NagB`
  for the domain `A ⧸ ker`);
* **`isFinite_fromNormalization`**: `X` locally of finite type over a perfect field, `y : X`, `φ : κ(y) ⟶ κ(ξ)` a
  finite extension ⇒ the relative normalization of `Spec κ(ξ) ⟶ Spec κ(y) ⟶ X` is finite over `X`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace RamanujanPetersson.EtPBC.Nagata

universe u

end RamanujanPetersson.EtPBC.Nagata

namespace RamanujanPetersson.EtPBC.Nagata

universe v

variable {X : Scheme.{v}} (y : X) {T : Scheme.{v}} (ξ : T) (φ : X.residueField y ⟶ T.residueField ξ)

/-- The sections of `Spec κ(ξ) ⟶ X` over an open containing `y`. -/
theorem appLE_eq {U : X.Opens} (hy : y ∈ U) (hle : ⊤ ≤ (Spec.map φ ≫ X.fromSpecResidueField y) ⁻¹ᵁ U) :
    (Spec.map φ ≫ X.fromSpecResidueField y).appLE U ⊤ hle =
      X.presheaf.germ U y hy ≫ X.residue y ≫ φ ≫ (Scheme.ΓSpecIso _).inv := by
  have hf : Spec.map φ ≫ X.fromSpecResidueField y = Spec.map (X.residue y ≫ φ) ≫ X.fromSpecStalk y := by
    simp [Scheme.fromSpecResidueField, Spec.map_comp]
  have key : ∀ (g : Spec (T.residueField ξ) ⟶ X) (_ : g = Spec.map (X.residue y ≫ φ) ≫ X.fromSpecStalk y)
      (hle : ⊤ ≤ g ⁻¹ᵁ U), g.appLE U ⊤ hle =
        X.presheaf.germ U y hy ≫ (X.residue y ≫ φ) ≫ (Scheme.ΓSpecIso _).inv := by
    rintro g rfl hle; exact appLE_fromSpecStalk y (X.residue y ≫ φ) hy hle
  rw [key _ hf hle, Category.assoc]

theorem subsingleton_sec {U : X.Opens} (hy : y ∉ U) :
    Subsingleton Γ(Spec (T.residueField ξ), (Spec.map φ ≫ X.fromSpecResidueField y) ⁻¹ᵁ U) :=
  ⟨fun s t => TopCat.Presheaf.section_ext (Spec (T.residueField ξ)).sheaf _ s t
    fun z hz => (not_mem_preimage y ξ φ hy z hz).elim⟩

end RamanujanPetersson.EtPBC.Nagata

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

/-- The relative normalization `Y` of `P` in `Spec κ(ξ)`. -/
abbrev Yn : Scheme.{u} := (f0 T ξ).normalization

/-- `π : Y ⟶ P`. -/
abbrev πn : Yn T ξ ⟶ P := (f0 T ξ).fromNormalization

/-- `g₀ : Spec κ(ξ) ⟶ Y`. -/
abbrev g0 : Spec (T.left.residueField ξ) ⟶ Yn T ξ := (f0 T ξ).toNormalization

theorem g0_π : g0 T ξ ≫ πn T ξ = f0 T ξ := (f0 T ξ).toNormalization_fromNormalization

section Sec

variable {T} (W : P.Etale)

/-- The section of `X' ⟶ Spec κ(ξ)` given by `u : T ⟶ W`. -/
def sx (u : T ⟶ W) : Spec (T.left.residueField ξ) ⟶ Xp ξ W :=
  pullback.lift (𝟙 _) (T.left.fromSpecResidueField ξ ≫ u.left)
    ((Category.id_comp _).trans ((f0_eq T ξ).trans
      ((congrArg (T.left.fromSpecResidueField ξ ≫ ·) (MorphismProperty.Over.w u).symm).trans
        (Category.assoc _ _ _).symm)))

theorem sx_fst (u : T ⟶ W) : sx ξ W u ≫ pullback.fst (f0 T ξ) W.hom = 𝟙 _ := pullback.lift_fst _ _ _

theorem sx_snd (u : T ⟶ W) : sx ξ W u ≫ pullback.snd (f0 T ξ) W.hom = T.left.fromSpecResidueField ξ ≫ u.left :=
  pullback.lift_snd _ _ _

theorem isOpen_range_sx (u : T ⟶ W) : IsOpen (Set.range (sx ξ W u)) :=
  isOpen_range_section _ _ (sx_fst ξ W u)

theorem isClosed_range_sx [IsAffine W.left] (u : T ⟶ W) : IsClosed (Set.range (sx ξ W u)) := by
  have hW : IsSeparated W.hom := Scheme.instIsSeparatedOfIsSeparated (X := W.left) (Y := P) W.hom
  have hS : IsSeparated (pullback.fst (f0 T ξ) W.hom) := by
    set_option backward.isDefEq.respectTransparency.types false in infer_instance
  exact @isClosed_range_section _ _ _ (pullback.fst (f0 T ξ) W.hom) hS (sx_fst ξ W u)

/-- The comparison map `X' ⟶ W ×_P T`. -/
def μx : Xp ξ W ⟶ (prd W T).left :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ T.left.fromSpecResidueField ξ)
    (pullback.condition.symm.trans ((congrArg (pullback.fst (f0 T ξ) W.hom ≫ ·) (f0_eq T ξ)).trans
      (Category.assoc _ _ _).symm))

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

/-- The relative normalization of `W` in `X' = Spec κ(ξ) ×_P W`. -/
abbrev Nn : Scheme.{u} := (pullback.snd (f0 T ξ) W.hom).normalization

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

/-- `Spec κ(ξ) ×_P V ⟶ Spec κ(ξ) ×_P W`. -/
def xmap {V W : P.Etale} (g : V ⟶ W) : Xp ξ V ⟶ Xp ξ W :=
  pullback.map (f0 T ξ) V.hom (f0 T ξ) W.hom (𝟙 _) g.left (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (MorphismProperty.Over.w g).symm)

theorem xmap_fst {V W : P.Etale} (g : V ⟶ W) :
    xmap ξ g ≫ pullback.fst (f0 T ξ) W.hom = pullback.fst (f0 T ξ) V.hom :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem xmap_snd {V W : P.Etale} (g : V ⟶ W) :
    xmap ξ g ≫ pullback.snd (f0 T ξ) W.hom = pullback.snd (f0 T ξ) V.hom ≫ g.left :=
  pullback.lift_snd _ _ _

section Rel

end Rel

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_CovNbB =====
section

/-!
# S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`

* `g_main`: the abstract pullback bookkeeping (no heavy terms): an iso `κ : P' ×_P Y ≅ Y_V'`, a finite surjective
  `ρ' : U' ⟶ Y_V'`, a retract `e, e'` of `Y_s` and a lift `ψ'` over `Y_x` give the `LiftT` tail;
* `surj_χ'`, `isClosedImmersion_xL`: the lift `Spec K ⟶ Spec R'` of `x` is a closed immersion;
* **`liftT_core`**, **`liftT_of_coverLiftAt`**: `CoverLiftAt` at `xV` gives `T2.LiftT (qV K gK) s π`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.Cov

universe u

section Gen

variable {P P' Y Ps YV Yx U' Tl : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (κ : pullback f π ⟶ YV) [IsIso κ]
  (ρ' : U' ⟶ YV)

variable (ι' : Ps ⟶ P') (ι : Ps ⟶ P) (hι : ι' ≫ f = ι) (ys : pullback π ι ⟶ pullback f π)
  (hys1 : ys ≫ pullback.fst f π = pullback.snd π ι ≫ ι') (hys2 : ys ≫ pullback.snd f π = pullback.fst π ι)

include hys1 hys2 in
theorem g_hk : pullback.fst (ρ' ≫ inv κ ≫ pullback.fst f π) ι' ≫ ρ' ≫ inv κ =
    T3d.hsU π f _ _ (g_hh π f κ ρ') ι' ι hι ≫ ys := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [hys1, pullback.condition (f := ρ' ≫ inv κ ≫ pullback.fst f π) (g := ι'),
      ← T3d.hsU_snd π f _ _ (g_hh π f κ ρ') ι' ι hι, Category.assoc]
  · simp only [Category.assoc]
    rw [hys2, T3d.hsU_fst]

include hys1 hys2 in
theorem g_hM (y : Yx ⟶ YV) (e : pullback π ι ⟶ Yx) (hsq : ys ≫ κ = e ≫ y) :
    pullback.fst (ρ' ≫ inv κ ≫ pullback.fst f π) ι' ≫ ρ' =
      (T3d.hsU π f _ _ (g_hh π f κ ρ') ι' ι hι ≫ e) ≫ y := by
  calc _ = (pullback.fst (ρ' ≫ inv κ ≫ pullback.fst f π) ι' ≫ ρ' ≫ inv κ) ≫ κ := by
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    _ = _ := by rw [g_hk π f κ ρ' ι' ι hι ys hys1 hys2, Category.assoc, hsq, Category.assoc]

end Gen

section Aux

end Aux

section Chi

attribute [local instance] algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

end Chi

section Main

attribute [local instance] algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

end Main

end RamanujanPetersson.EtPBC

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

theorem fibFun_w (W : P.Etale) (x : P) ⦃V V' : P.Etale⦄ (f : V ⟶ V') (b : (geomPtAt x).point.fiber.obj V) :
    (freePre Λ W).map f.op ≫ fibFun Λ W x V b = fibFun Λ W x V' ((geomPtAt x).point.fiber.map f b) := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun h c => ?_)
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ (Finsupp.single h c)) =
    Finsupp.mapDomain _ (Finsupp.single h c)
  rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
  congr 1

end RamanujanPetersson.EtPBC.FreeStk

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

variable (Λ) in
/-- **The one-point MV complex** `Λ[D ×_P Uo] ⟶ Λ[D] ⊞ Λ[Uz] ⟶ Λ[P]`. -/
abbrev locC (D : P.Etale) {Uo Uz : P.Opens} (h : Uo ≤ Uz) : ShortComplex (EtSh Λ P) :=
  mvC Λ (prW D (opEt Uo)) (prT D (opEt Uo) ≫ opEtMap h) (toTop D) (toTop (opEt Uz)) (toTop_ext _ _)

theorem isEmpty_fib_prd (D : P.Etale) (Uo : P.Opens) (x : P) (hx : x ∉ Uo) :
    IsEmpty ((geomPtAt x).point.fiber.obj (prd D (opEt Uo))) :=
  ⟨fun c => hx (mem_of_fib_opEt Uo x ((geomPtAt x).point.fiber.map (prT D (opEt Uo)) c))⟩

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

/-- `copPrd ⟶ cop S`. -/
def copP₁ : copPrd S U₀ ⟶ cop S := copDesc (fun k => prW (S k) (opEt U₀) ≫ copι S k)

/-- `copPrd ⟶ U₀`. -/
def copP₂ : copPrd S U₀ ⟶ opEt U₀ := copDesc (fun k => prT (S k) (opEt U₀))

theorem copι_copP₁ (k : ι) :
    copι (fun k => prd (S k) (opEt U₀)) k ≫ copP₁ S U₀ = prW (S k) (opEt U₀) ≫ copι S k :=
  copι_desc _ k

theorem copι_copP₂ (k : ι) : copι (fun k => prd (S k) (opEt U₀)) k ≫ copP₂ S U₀ = prT (S k) (opEt U₀) :=
  copι_desc _ k

variable (z : ι → P) (hzi : Function.Injective z) (hU : ∀ x : P, x ∈ U₀ ↔ ∀ k, x ≠ z k)
  (hD : ∀ k, Subsingleton ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDn : ∀ k, Nonempty ((geomPtAt (z k)).point.fiber.obj (S k)))
  (hDr : ∀ k (v : (S k).left), (S k).hom v ∈ U₀ ∨ (S k).hom v = z k)

include hzi hU hD hDr in
theorem fib_cop_sub (k₀ : ι) : Subsingleton ((geomPtAt (z k₀)).point.fiber.obj (cop S)) := by
  refine ⟨fun a a' => ?_⟩
  obtain ⟨k, b, rfl⟩ := fib_cop_surj S _ a
  obtain ⟨k', b', rfl⟩ := fib_cop_surj S _ a'
  have e1 := fib_cop_idx_z S U₀ z hzi hU hDr k₀ k b
  have e2 := fib_cop_idx_z S U₀ z hzi hU hDr k₀ k' b'
  subst e1 e2
  exact congrArg _ (@Subsingleton.elim _ (hD _) b b')

end RamanujanPetersson.EtPBC.EtMV

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

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Λ : Type} [AddCommGroup Λ]

/-- **Twisting a level-`d` Kummer character by `τ`** (`τ ^ N` fixed, `d ∣ N`, `d • g = 0`). -/
theorem kumChi_twist {N d : ℕ} [NeZero N] [NeZero d] {ζ : E} (hζ : IsPrimitiveRoot ζ N)
    (hζd : IsPrimitiveRoot (ζ ^ (N / d)) d) (hdN : d ∣ N) {α τ : Eˣ}
    (hα : α ∈ rad (⊤ : Subgroup (E ≃ₐ[K] E)) d) (hτ : τ ∈ rad (⊤ : Subgroup (E ≃ₐ[K] E)) N) (m : ℤ)
    {g : Λ} (hg : d • g = 0) (σ : E ≃ₐ[K] E) :
    kumChi hζd α g σ = kumChi hζd (α * (τ ^ (N / d)) ^ m) g σ + kumChi hζ τ ((-m) • g) σ := by
  have hτd : τ ^ (N / d) ∈ rad (⊤ : Subgroup (E ≃ₐ[K] E)) d := by
    intro s hs
    rw [Units.val_pow_eq_pow_val, ← pow_mul, Nat.div_mul_cancel hdN]
    exact hτ s hs
  have hτm : (τ ^ (N / d)) ^ m ∈ rad (⊤ : Subgroup (E ≃ₐ[K] E)) d := (rad _ d).zpow_mem hτd m
  unfold kumChi
  set σ' : (⊤ : Subgroup (E ≃ₐ[K] E)) := ⟨σ, Subgroup.mem_top σ⟩
  rw [kchar_mul_left hζd hα hτm, kchar_zpow hζd hτd, KumDec.kchar_level hζ hζd hτd hτ rfl,
    ← zvHom_apply hg, ← zvHom_apply hg, map_add]
  have e : (m : ZMod d) * (((kchar hζ τ σ').val : ℕ) : ZMod d) = ((m * ((kchar hζ τ σ').val : ℤ) : ℤ) : ZMod d) := by
    push_cast
    ring
  rw [e, zvHom_intCast, add_assoc, ← natCast_zsmul, smul_smul, ← add_smul,
    show m * ((kchar hζ τ σ').val : ℤ) + ((kchar hζ τ σ').val : ℤ) * -m = 0 by ring, zero_smul, add_zero]

end Twist2

section Cyc

end Cyc

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Tr1 =====
section

/-!
# S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open

* `agr τ₁ τ₂`: for `τ₁ τ₂ : T ⟶ W` over `P` (`W` separated etale), the range of the pull-back of the diagonal of `W`
  along `(τ₁, τ₂)`: closed (`isClosed_agr`), and a fibre point `v` of `T` has `τ₁ v = τ₂ v` iff `fpt v ∈ agr τ₁ τ₂`
  (`mem_agr_iff`).
* **`exists_split_inj`**: for `x ∈ U₀` and `W` quasi-compact separated etale, an etale `T` over `U₀` with a point `t`
  over `x̄` and maps `τ p : T ⟶ W` (`p` in the fibre of `W` over `x̄`) with `τ p (t) = p`, pairwise distinct at every
  geometric point of `T`.
* `locSec τ = Σ_p τ_p^* taut`; `stalkFree_locSec_apply` (all coefficients of its germ are `1` where the `τ_p` biject
  onto the fibre); `stalkFree_injective`.
* **`exists_tr`**: if every geometric fibre of `W` over `U₀` has `n` points, there is a section `s ∈ Λ[W](U₀)` whose
  germ at every geometric point of `U₀` is the sum of all points of the fibre (the trace `Λ[U₀] ⟶ Λ[W]`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtTr

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk
  RamanujanPetersson.EtPBC.EtMV

universe u

variable {P : Scheme.{u}}

section Agr

variable {T W : P.Etale} (τ₁ τ₂ : T ⟶ W)

theorem comp_eq_of_range_sub {S : Scheme.{u}} (g : S ⟶ T.left) (hg : Set.range g ⊆ agr τ₁ τ₂) :
    g ≫ τ₁.left = g ≫ τ₂.left := by
  have hm := IsOpenImmersion.lift_fac
    (pullback.snd (pullback.diagonal W.hom) (pullback.lift τ₁.left τ₂.left (agr_w τ₁ τ₂))) g hg
  rw [← hm, Category.assoc, Category.assoc, agr_eq]

/-- **Fibre points agree iff the underlying point lies in the agreement locus.** -/
theorem mem_agr_iff (y : P) (v : (geomPtAt y).point.fiber.obj T) :
    fpt y v ∈ agr τ₁ τ₂ ↔ (geomPtAt y).point.fiber.map τ₁ v = (geomPtAt y).point.fiber.map τ₂ v := by
  constructor
  · intro h
    refine fiber_ext _ ?_
    show fl y v ≫ τ₁.left = fl y v ≫ τ₂.left
    refine comp_eq_of_range_sub τ₁ τ₂ (fl y v) ?_
    rintro _ ⟨s, rfl⟩
    rwa [Subsingleton.elim s default]
  · intro h
    have h1 : fl y v ≫ τ₁.left = fl y v ≫ τ₂.left := congrArg (fun c => ((geomPtAt y).liftOf c).left) h
    exact mem_agr_of_comp_eq τ₁ τ₂ (fl y v) h1 default

end Agr

section Loc

end Loc

end RamanujanPetersson.EtPBC.EtTr

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

theorem shP_prW (s : N ⟶ W) : shP s ≫ prW N W = 𝟙 N :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

theorem shP_prT (s : N ⟶ W) : shP s ≫ prT N W = s :=
  MorphismProperty.Over.Hom.ext (pullback.lift_snd _ _ _)

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

theorem pt_eq2 {M M₀ : P.Etale} (ι : M ⟶ M₀) (σ : M₀ ⟶ W) (v : M.left) :
    ((etPull W.hom).map ι).left ((shP (ι ≫ σ)).left v) = (shι σ).left (ι.left v) := by
  exact congrArg (fun f => f v) (lift_comp_core ι σ).symm

end Dg

section Iso

variable (Λ : Type u) [CommRing Λ] (W : P.Etale) [IsSeparated W.hom]

omit [IsSeparated W.hom] in
theorem ind_dg {N : P.Etale} (τ₁ τ₂ : N ⟶ W) (v : N.left) (u : ↥(pullback W.hom W.hom))
    (hu : u = pullback.lift τ₁.left τ₂.left (agr_w τ₁ τ₂) v) :
    (dg W).indicator (fun _ => (1 : Λ)) u = (agr τ₁ τ₂).indicator (fun _ => (1 : Λ)) v := by
  subst hu
  by_cases h : v ∈ agr τ₁ τ₂
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((lift_mem_dg_iff W τ₁ τ₂ v).2 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((lift_mem_dg_iff W τ₁ τ₂ v).1 h'))]

end Iso

end RamanujanPetersson.EtPBC.EtShap

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

theorem spec_locT_comp : Spec.map (φ ≫ locT φ a) ≫ c = Spec.map (locT φ a) ≫ Spec.map φ ≫ c := by
  rw [Spec.map_comp, Category.assoc]

instance etale_locT : Etale (Spec.map (φ ≫ locT φ a) ≫ c) := by
  rw [spec_locT_comp]; infer_instance

theorem range_locT (u : Spec B) : u ∈ Set.range (Spec.map (locT φ a)) ↔ φ.hom (X - C a) ∉ u.asIdeal := by
  have e : Set.range (Spec.map (locT φ a)) =
      Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (φ.hom (X - C a))))) := rfl
  rw [e, PrimeSpectrum.localization_away_comap_range (Localization.Away (φ.hom (X - C a))) (φ.hom (X - C a))]
  exact PrimeSpectrum.mem_basicOpen _ _

section Cls

end Cls

end T

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km1): the Shapiro scheme `W = D_o ×_P R` is affine

* `isAffineHom_of_isAffine_source`: a morphism from an affine scheme to a separated scheme is affine;
* `isAffine_etPull`: `D ×_P R` is affine for affine `D`, `R` over a separated `P`; `isAffineHom_etPull`: its
  structure map to `D` is affine (hence quasi-compact and separated: `quasiCompact_etPull`, `isSeparated_etPull'`);
* `isAffine_prdUo`: `D ×_P Uo ≅ Spec B_t` is affine for an affine Dedekind presentation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV

universe u

section Affine

variable {P : Scheme.{u}} [P.IsSeparated] (D R : P.Etale) [IsAffine R.left]

theorem quasiCompact_etPull : QuasiCompact ((etPull D.hom).obj R).hom := by
  have := isAffineHom_etPull D R
  infer_instance

theorem isSeparated_etPull' : IsSeparated ((etPull D.hom).obj R).hom := by
  have := isAffineHom_etPull D R
  exact IsSeparated.of_isAffineHom _

theorem isAffine_etPull [IsAffine D.left] : IsAffine ((etPull D.hom).obj R).left := by
  let f : R.left ⟶ P := R.hom
  let g : D.left ⟶ P := D.hom
  have : IsAffineHom (pullback.snd f g) := isAffineHom_etPull D R
  have h : IsAffine (pullback f g) := isAffine_of_isAffineHom (pullback.snd f g)
  exact h

end Affine

section Prd

end Prd

end RamanujanPetersson.EtPBC.EtKum

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

variable {P : Scheme.{u}} [P.IsSeparated] (D R : P.Etale) [IsAffine R.left]

instance qc_W : QuasiCompact ((etPull D.hom).obj R).hom := quasiCompact_etPull D R

instance sep_W : IsSeparated ((etPull D.hom).obj R).hom := isSeparated_etPull' D R

instance isAffine_W [IsAffine D.left] : IsAffine ((etPull D.hom).obj R).left := isAffine_etPull D R

end Inst

section Assembly

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]

instance etale_shG : Etale (shG c φ (Uo := Uo) R) := by
  have h1 : Etale ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).hom := ((etPull _).obj R).prop
  have h2 : Etale (prW (chEt c φ) (opEt Uo)).left := by
    change Etale (pullback.fst (chEt c φ).hom (opEt Uo).hom)
    infer_instance
  have h3 : Etale (Spec.map φ) := Etale.of_comp (Spec.map φ) c
  unfold shG
  exact @Etale.etale_comp _ _ _ _ _ h1 (@Etale.etale_comp _ _ _ _ _ h2 h3)

end Assembly

end RamanujanPetersson.EtPBC.EtKum

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

instance bcField_isSplittingField (f : K[X]) :
    (f.map (algebraMap K K')).IsSplittingField K' (bcField (K' := K') f) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

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

/-- `c(D(g))`. -/
def opnDg (g : k[X]) : P.Opens := (chEt c (locF (B := CommRingCat.of k[X]) g)).hom.opensRange

variable {B : CommRingCat.{u}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (f : B) (g : k[X])
  (hg : IsUnit (algebraMap B (Localization.Away f) (φ.hom g)))

theorem locF_liftDg : locF (B := CommRingCat.of k[X]) g ≫ liftDg φ f g hg = φ ≫ locF f := by
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, liftDg,
    CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, IsLocalization.Away.lift_eq,
    RingHom.comp_apply]

end Dg

section Sec

end Sec

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl0 =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl0): stage S0 of the global step

GLOB/REL PLAN v1, stage S0. For a cofinite open `U₀` of `P` and a chart `c : A1 k ⟶ P`:
* `exists_g_mem_of_ne`, `exists_g_of_finite`: finitely many nonzero primes of `k[X]`, none equal to `(X - a)`, have a
  common element `g` with `g(a) ≠ 0`;
* `A1pt_injective`, `exists_g_chart`: there is `g₀` with `g₀(a) ≠ 0` and `c(D(g₀)) ⊆ U₀ ∪ {c(X = a)}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtDeg

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtPBC.EtShap

universe u

section Alg

variable {k : Type u} [Field k]

theorem exists_g_of_finite (a : k) (F : Set (PrimeSpectrum k[X])) (hF : F.Finite)
    (hbot : ∀ y ∈ F, y.asIdeal ≠ ⊥) (ha : ∀ y ∈ F, y.asIdeal ≠ Ideal.span {X - C a}) :
    ∃ g : k[X], g.eval a ≠ 0 ∧ ∀ y ∈ F, g ∈ y.asIdeal := by
  classical
  have hex : ∀ y : PrimeSpectrum k[X], ∃ g : k[X], g.eval a ≠ 0 ∧ (y ∈ F → g ∈ y.asIdeal) := by
    intro y
    by_cases hy : y ∈ F
    · obtain ⟨g, hg, hga⟩ := exists_g_mem_of_ne a y (hbot y hy) (ha y hy)
      exact ⟨g, hga, fun _ => hg⟩
    · exact ⟨1, by simp, fun h => absurd h hy⟩
  choose g hga hg using hex
  refine ⟨∏ y ∈ hF.toFinset, g y, ?_, fun y hy => ?_⟩
  · rw [eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun y _ => hga y
  · exact y.asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem g (hF.mem_toFinset.mpr hy)) (hg y hy)

end Alg

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Km9a =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km9a): roots of unity on the Shapiro pieces

Setting of O2Km6 (`D = Spec B` over `𝔸¹ ⊆ P`, `D_o = D ×_P Uo` affine, `R` affine with constant degree `n` over
`D_o`, `W = D_o ×_P R`), plus a primitive `N`-th root of unity `ζ0 ∈ k` and `N • Λ = 0`.
* `fW p : k →+* Frac(Γ(W) ⧸ p)`, `ζW p`, `hζW` (primitive), `hζWΓ` (fixed by `π₁`);
  (the hypotheses `hζ`, `hζΓ` of `ext_mem_of_kum`, O2Km9b).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Zeta

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]

/-- `k ⟶ Frac(Γ(W, ⊤) ⧸ p)` (through `shG : W ⟶ Spec k[X]`). -/
noncomputable def fW (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) :
    k →+* FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) :=
  (algebraMap _ _).comp ((Ideal.Quotient.mk p.1).comp
    (((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv ≫ (shG c φ R).appTop).hom.comp Polynomial.C))

end Zeta

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PPTd =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks

For chart neighbourhoods `D = chEt c φ`, `D₁ = chEt c φ₁` and any `dm : D₁ ⟶ D` in `P.Etale`:
* `left_spec_map`: `dm.left ≫ Spec.map φ = Spec.map φ₁`; **`shG_wm`**: `wm (prdMap dm) ≫ shG c φ = shG c φ₁`;
* `sXW c φ R ζ0 ∈ Γ(W)` (the image of `ζ0 ∈ k`), `ζW_eq`, **`wm_appTop_sXW`**;
* **`locCls_kapS_chart`**: `locCls_kapS_shrink` (O2PPTc) with the roots of unity `ζW` of O2Km9a on both sides;
* **`piece_unique_away`**: if `Γ(X₁) = Γ(X)[1/s]` along `f`, at most one piece of `X₁` lies over a piece of `X`
  (applies to `toDF` by `isLocalization_away_toDF`, O2ZarCh).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section Away

end Away

section Chart

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
  {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
  {Uo : P.Opens} (R : P.Etale) [IsAffine R.left] (dm : chEt c φ₁ ⟶ chEt c φ)

set_option backward.isDefEq.respectTransparency false in
theorem shG_eq : shG c φ (Uo := Uo) R = wD (chEt c φ) (opEt Uo) R ≫ Spec.map φ := by
  unfold shG wD
  rw [Category.assoc]
  rfl

/-- The image of `ζ0 ∈ k` in `Γ(W)`. -/
def sXW (ζ0 : k) : Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k[X])).inv ≫ (shG c φ (Uo := Uo) R).appTop).hom (Polynomial.C ζ0)

end Chart

section ChartPPT

end ChartPPT

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2b =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3

GLOB/REL PLAN v1, stage S3 (geometric part). `D_G := chEt c (k[X] ⟶ k[X]_G)` for `G = g₀ c₀' t` (`g₀ ∣ G`,
`t = X - a ∣ G`):
* `toDG : D_G ⟶ D_{g₀}`; `chG_mem`: `D_G` lies over `U₀` (no point over `z`), so `opnDg c G ≤ U₀`;
* `sigG : opEt (c(D(G))) ⟶ D_G ×_P U₀` and `mG := toOpEt ≫ sigG` (the map `m` of `uk_diff`), `mG_prT` (`hm`),
  `mG_prdMap` (`m ≫ (D_G ⟶ D_{g₀}) = (D₂ ⟶ D_{g₀})`, maps into `D ×_P X` are determined by `prT` for `D` open);
* `gamMap_shG`, `appTop_gamMap`, `isUnit_rho`: a divisor of `G^n` in `Γ(Y₀)` becomes a unit on `Y₁ = (D_G ×_P U₀) ×_P R`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section Mono

end Mono

section ChG

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {g₀ G : k[X]} (hG₀ : g₀ ∣ G)

/-- `k[X]_{g₀} ⟶ k[X]_G`. -/
def liftG : CommRingCat.of (Localization.Away g₀) ⟶ CommRingCat.of (Localization.Away G) :=
  CommRingCat.ofHom (IsLocalization.Away.lift g₀ (g := algebraMap k[X] (Localization.Away G)) (isUnit_locF_of_dvd hG₀))

theorem locF_liftG : locF (B := CommRingCat.of k[X]) g₀ ≫ liftG hG₀ = locF (B := CommRingCat.of k[X]) G := by
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  show IsLocalization.Away.lift g₀ (g := algebraMap k[X] (Localization.Away G)) (isUnit_locF_of_dvd hG₀)
    (algebraMap k[X] (Localization.Away g₀) x) = algebraMap k[X] (Localization.Away G) x
  exact IsLocalization.Away.lift_eq _ (isUnit_locF_of_dvd hG₀) x

variable {a : k} {Uo : P.Opens}
  (hg₀ : ∀ v : (chEt c (locF (B := CommRingCat.of k[X]) g₀)).left,
    (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v ∈ Uo ∨ (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v = c (A1pt k a))
  (hGt : X - C a ∣ G)

/-- A point `c q` with `G ∉ q` lies in `c(D(G))`. -/
theorem mem_opnDg {x : P} {q : A1 k} (hx : x = c q) (hq : G ∉ q.asIdeal) : x ∈ opnDg c G := by
  have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away G) G
  have hq' : q ∈ Set.range (PrimeSpectrum.comap (algebraMap k[X] (Localization.Away G))) := by
    rw [hr]; exact hq
  obtain ⟨w, hw⟩ := hq'
  refine ⟨w, ?_⟩
  rw [hx, ← hw]
  rfl

end ChG

section Sec

end Sec

section Gam

end Gam

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals

REL PLAN v2 (s126) + s128 fix. At a bad point `c(b)` (`G = (X - C b)^m G_b`, `G_b(b) ≠ 0`, `c(b) ∉ U₀`), the chart
`D' := D_{G_b} = chEt c (locF G_b)` satisfies the hypotheses of `bad_term_zero'` (O2Bd5):
* fibres: **`subsingleton_fib_of_mono`**, **`nonempty_fib_of_mem`** (generic);
* **`bad_pt`**, **`badCh_r₁`** (`hDr₁`), **`badCh_r`** (`hDr`), **`badCh_D'`** (`hD'`), **`badCh_hUo`**, **`isAffine_badCh`**,
  **`badCh_hta`** (`hta`), **`badCh_n`** (`hDn`);
* CRT ideals `J b := (X - C b) S`: **`span_coprime_pow`** (`hJt`), **`pairwise_span_coprime`** (`hJ`) of `exists_S23_chart`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Cech

section Fib

end Fib

section BadCh

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {G Gb : k[X]} {b : k} {m : ℕ}
  (hGf : G = (X - C b) ^ m * Gb)

theorem gb_not_mem (v : (chEt c (locF (B := CommRingCat.of k[X]) Gb)).left) :
    Gb ∉ (Spec.map (locF (B := CommRingCat.of k[X]) Gb) v).asIdeal := fun h =>
  v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.1 h) (isUnit_locF_of_dvd (dvd_refl Gb)))

end BadCh

section BadCh2

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {G Gb : k[X]} {b : k} {m : ℕ}
  (hGf : G = (X - C b) ^ m * Gb)

include hGf in
/-- **`hta`**: `X - C a` is a unit on `D_{G_b}` when `X - C a ∣ G` and `a ≠ b`. -/
theorem badCh_hta {a : k} (hab : a ≠ b) (hGt : X - C a ∣ G) :
    IsUnit ((locF (B := CommRingCat.of k[X]) Gb).hom (X - C a)) := by
  have h1 : X - C a ∣ (X - C b) ^ m * Gb := hGf ▸ hGt
  rcases (prime_X_sub_C a).dvd_or_dvd h1 with h2 | h2
  · exfalso
    have h3 := (prime_X_sub_C a).dvd_of_dvd_pow h2
    rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero] at h3
    exact hab h3
  · exact isUnit_locF_of_dvd h2

/-- **`hDs`** for `D_{G_b}`. -/
theorem badCh_s (x : P) : Subsingleton ((geomPtAt x).point.fiber.obj (chEt c (locF (B := CommRingCat.of k[X]) Gb))) :=
  subsingleton_fib_of_mono _ x

end BadCh2

section JAlg

end JAlg

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP3a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points

GLOB/REL PLAN v1: `exists_S23B` / `exists_S23_chart` (O2Gl2j) with `t = X - a` and `J_b = (X - b)` for the points
`b` with `p b` (`p b → b ≠ a`), so that no `J`-family has to be built at the chart level (instance paths on
`integralClosure k[X] Γ(Y₀)` built outside the generic lemma made the chart-level unification time out).
* helpers: `ne_zero_right_of_eq`, `dvd_map_of_eq`, `badJ`, `badJ_pairwise`, `badJ_coprime`, `badJ_mem`;
* **`exists_S23B_bad`** (generic rings) and **`exists_S23_chart_bad`** (the chart instance).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section PP3Helpers

section BadJ

variable {k : Type} [Field k] {S : Type} [CommRing S] [Algebra k[X] S]

theorem badJ_pairwise (p : k → Prop) : Pairwise fun i j => IsCoprime (badJ (S := S) p i) (badJ p j) :=
  pairwise_span_coprime Subtype.val_injective

theorem badJ_coprime {a : k} (p : k → Prop) (hp : ∀ b, p b → b ≠ a) (n : ℕ) (i : Subtype p) :
    IsCoprime (Ideal.span {algebraMap k[X] S (X - C a) ^ n}) (badJ p i) :=
  span_coprime_pow (hp i.1 i.2).symm n

end BadJ

end PP3Helpers

section S23BBad

end S23BBad

section S23Bad

end S23Bad

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1a =====
section

/-!
# S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`

For maps `p₁ : A' → A`, `p₂ : A' → B`, `w : A → C`, `v : B → C` with `w ∘ p₁ = v ∘ p₂`, the complex
`Λ[A'] → Λ[A] ⊕ Λ[B] → Λ[C]`, `l ↦ (p₁ l, -p₂ l)`, `(p, q) ↦ w p + v q`, is exact (and the first map injective,
the last surjective) when every `c : C` satisfies `MVG1` (one point of `A` over `c`, `p₂` bijective over `c`) or
`MVG2` (one point of `B` over `c`, `p₁` bijective over `c`): `mv_inj`, `mv_surj`, `mv_exact`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

section MVComb

universe u₀ u₁ u₂ u₃ u₄

variable {Λ : Type u₀} [CommRing Λ] {A' : Type u₁} {A : Type u₂} {B : Type u₃} {C : Type u₄}
  (p₁ : A' → A) (p₂ : A' → B) (w : A → C) (v : B → C)

variable (hsq : ∀ a', w (p₁ a') = v (p₂ a')) (hg : ∀ c, MVG1 p₂ w v c ∨ MVG2 p₁ w v c)
include hsq hg

theorem mvE₁_p₂ (a : A) : Finsupp.mapDomain p₂ (mvE₁ Λ p₁ p₂ w v a) = mvG Λ p₂ w v (w a) := by
  by_cases h1 : MVG1 p₂ w v (w a)
  · rw [mvE₁, dif_neg (fun h => h.1 h1), mvG, dif_neg (fun h => h.1 h1), Finsupp.mapDomain_zero]
  · obtain ⟨hs, hb, hu⟩ := (hg (w a)).resolve_left h1
    have he : ∃ a', p₁ a' = a := (hu a rfl).exists
    rw [mvE₁, dif_pos ⟨h1, he⟩, mvG, dif_pos ⟨h1, hb⟩, Finsupp.mapDomain_single]
    congr 1
    apply hs
    · rw [← hsq, Classical.choose_spec he]
    · exact Classical.choose_spec hb

theorem mvE₂_p₂ (b : B) :
    Finsupp.mapDomain p₂ (mvE₂ Λ p₂ w v b) = mvG Λ p₂ w v (v b) - Finsupp.single b 1 := by
  by_cases h1 : MVG1 p₂ w v (v b)
  · have he : ∃ a', p₂ a' = b := (h1.2.2 b rfl).exists
    rw [mvE₂, dif_pos ⟨h1, he⟩, mvG, dif_neg (fun h => h.1 h1), Finsupp.mapDomain_single,
      Classical.choose_spec he, zero_sub, Finsupp.single_neg]
  · obtain ⟨hs, _, _⟩ := (hg (v b)).resolve_left h1
    have hb : ∃ b', v b' = v b := ⟨b, rfl⟩
    rw [mvE₂, dif_neg (fun h => h1 h.1), mvG, dif_pos ⟨h1, hb⟩, Finsupp.mapDomain_zero,
      hs _ b (Classical.choose_spec hb) rfl, sub_self]

theorem mv_exact (p : A →₀ Λ) (q : B →₀ Λ) (h : Finsupp.mapDomain w p + Finsupp.mapDomain v q = 0) :
    ∃ l : A' →₀ Λ, Finsupp.mapDomain p₁ l = p ∧ Finsupp.mapDomain p₂ l = -q := by
  have I1 : ∀ p : A →₀ Λ, Finsupp.mapDomain p₁ (Finsupp.linearCombination Λ (mvE₁ Λ p₁ p₂ w v) p) =
      p - Finsupp.linearCombination Λ (mvF Λ p₂ w v) (Finsupp.mapDomain w p) := by
    intro p
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p p' hp hp' =>
      rw [map_add, Finsupp.mapDomain_add, hp, hp', Finsupp.mapDomain_add, map_add]; abel
    | single a m =>
      rw [Finsupp.linearCombination_single, Finsupp.mapDomain_smul, mvE₁_p₁ p₁ p₂ w v hsq hg,
        Finsupp.mapDomain_single, Finsupp.linearCombination_single, smul_sub, Finsupp.smul_single_one]
  have I2 : ∀ q : B →₀ Λ, Finsupp.mapDomain p₁ (Finsupp.linearCombination Λ (mvE₂ Λ p₂ w v) q) =
      - Finsupp.linearCombination Λ (mvF Λ p₂ w v) (Finsupp.mapDomain v q) := by
    intro q
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add q q' hq hq' =>
      rw [map_add, Finsupp.mapDomain_add, hq, hq', Finsupp.mapDomain_add, map_add, neg_add]
    | single b m =>
      rw [Finsupp.linearCombination_single, Finsupp.mapDomain_smul, mvE₂_p₁ p₁ p₂ w v hsq hg,
        Finsupp.mapDomain_single, Finsupp.linearCombination_single, smul_neg]
  have I3 : ∀ p : A →₀ Λ, Finsupp.mapDomain p₂ (Finsupp.linearCombination Λ (mvE₁ Λ p₁ p₂ w v) p) =
      Finsupp.linearCombination Λ (mvG Λ p₂ w v) (Finsupp.mapDomain w p) := by
    intro p
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p p' hp hp' => rw [map_add, Finsupp.mapDomain_add, hp, hp', Finsupp.mapDomain_add, map_add]
    | single a m =>
      rw [Finsupp.linearCombination_single, Finsupp.mapDomain_smul, mvE₁_p₂ p₁ p₂ w v hsq hg,
        Finsupp.mapDomain_single, Finsupp.linearCombination_single]
  have I4 : ∀ q : B →₀ Λ, Finsupp.mapDomain p₂ (Finsupp.linearCombination Λ (mvE₂ Λ p₂ w v) q) =
      Finsupp.linearCombination Λ (mvG Λ p₂ w v) (Finsupp.mapDomain v q) - q := by
    intro q
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add q q' hq hq' =>
      rw [map_add, Finsupp.mapDomain_add, hq, hq', Finsupp.mapDomain_add, map_add]; abel
    | single b m =>
      rw [Finsupp.linearCombination_single, Finsupp.mapDomain_smul, mvE₂_p₂ p₁ p₂ w v hsq hg,
        Finsupp.mapDomain_single, Finsupp.linearCombination_single, smul_sub, Finsupp.smul_single_one]
  have hF := congrArg (Finsupp.linearCombination Λ (mvF Λ p₂ w v)) h
  have hG := congrArg (Finsupp.linearCombination Λ (mvG Λ p₂ w v)) h
  rw [map_add, map_zero] at hF hG
  refine ⟨Finsupp.linearCombination Λ (mvE₁ Λ p₁ p₂ w v) p + Finsupp.linearCombination Λ (mvE₂ Λ p₂ w v) q,
    ?_, ?_⟩
  · rw [Finsupp.mapDomain_add, I1, I2]
    calc p - Finsupp.linearCombination Λ (mvF Λ p₂ w v) (Finsupp.mapDomain w p) +
          -Finsupp.linearCombination Λ (mvF Λ p₂ w v) (Finsupp.mapDomain v q) =
        p - (Finsupp.linearCombination Λ (mvF Λ p₂ w v) (Finsupp.mapDomain w p) +
          Finsupp.linearCombination Λ (mvF Λ p₂ w v) (Finsupp.mapDomain v q)) := by abel
      _ = p := by rw [hF, sub_zero]
  · rw [Finsupp.mapDomain_add, I3, I4]
    calc Finsupp.linearCombination Λ (mvG Λ p₂ w v) (Finsupp.mapDomain w p) +
          (Finsupp.linearCombination Λ (mvG Λ p₂ w v) (Finsupp.mapDomain v q) - q) =
        (Finsupp.linearCombination Λ (mvG Λ p₂ w v) (Finsupp.mapDomain w p) +
          Finsupp.linearCombination Λ (mvG Λ p₂ w v) (Finsupp.mapDomain v q)) - q := by abel
      _ = -q := by rw [hG, zero_sub]

end MVComb

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

variable (Λ) in
/-- `(f^* G)|_{W_X} ≅ f_W^*(G|_W)` for `W_X = W ×_Y X` and `f_W : W_X ⟶ W`. -/
def tauIso : pull f Λ ⋙ res ((etPull f).obj W).hom Λ ≅ res W.hom Λ ⋙ pull (fW f W) Λ :=
  Functor.isoWhiskerLeft (pull f Λ) (pullIsoRes ((etPull f).obj W).hom Λ).symm ≪≫
    (pullCompIso Λ ((etPull f).obj W).hom f).symm ≪≫ pullCongr Λ (etPull_sq f W) ≪≫
    pullCompIso Λ (fW f W) W.hom ≪≫
    Functor.isoWhiskerRight (pullIsoRes W.hom Λ) (pull (fW f W) Λ)

theorem etPullCompIso_inv_fst {A B C : Scheme.{u}} (g : A ⟶ B) (f : B ⟶ C) (V : C.Etale) :
    ((etPullCompIso g f).inv.app V).left ≫ pullback.fst V.hom (g ≫ f) =
      pullback.fst ((etPull f).obj V).hom g ≫ pullback.fst V.hom f := by
  have h : ((etPullCompIso g f).inv.app V).left ≫ ((etPullCompIso g f).hom.app V).left = 𝟙 _ :=
    congrArg (fun φ => φ.left) ((etPullCompIso g f).inv_hom_id_app V)
  exact ((congrArg (fun k => ((etPullCompIso g f).inv.app V).left ≫ k) (etPullCompIso_hom_fst_fst g f V)).symm.trans
    (Category.assoc _ _ _).symm).trans ((congrArg (fun k => k ≫ pullback.fst ((etPull f).obj V).hom g ≫
      pullback.fst V.hom f) h).trans (Category.id_comp _))

variable (Λ) in
/-- The component of `tauIso` at `G`, as a composite of typed components. -/
def tauApp2 (G : EtSh Λ Y) :
    (res ((etPull f).obj W).hom Λ).obj ((pull f Λ).obj G) ⟶ (pull (fW f W) Λ).obj ((res W.hom Λ).obj G) :=
  tauAppG Λ f W ((etPull f).obj W) (fW f W) (etPull_sq f W) G

end TB2b

end RamanujanPetersson.EtPBC.EtMV

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

/-- `W ×_P Zs`. -/
abbrev Es : P.Etale := prd W (Zs i g W)

variable {i g} (hig : i ≫ g = 𝟙 S)

theorem jz_fst : jz W hig ≫ pullback.fst (Vs i W).hom g = 𝟙 _ := pullback.lift_fst _ _ _

theorem jz_snd : jz W hig ≫ pullback.snd (Vs i W).hom g = (Vs i W).hom ≫ i := pullback.lift_snd _ _ _

/-- `v ↦ (w v, jz v)`. -/
def τz : (Vs i W).left ⟶ pullback W.hom (Zs i g W).hom :=
  pullback.lift (pullback.fst W.hom i) (jz W hig) (pullback.condition.trans (jz_snd W hig).symm)

theorem τz_fst : τz W hig ≫ pullback.fst W.hom (Zs i g W).hom = pullback.fst W.hom i := pullback.lift_fst _ _ _

theorem τz_snd : τz W hig ≫ pullback.snd W.hom (Zs i g W).hom = jz W hig := pullback.lift_snd _ _ _

theorem τz_hom : τz W hig ≫ (Es i g W).hom = (Vs i W).hom ≫ i :=
  (pullback.lift_snd_assoc _ _ _ _).trans (jz_snd W hig)

/-- The section `Vs ⟶ Es ×_P S`. -/
def δz : Vs i W ⟶ (etPull i).obj (Es i g W) :=
  MorphismProperty.Over.homMk (pullback.lift (τz W hig) (Vs i W).hom (τz_hom W hig)) (pullback.lift_snd _ _ _)

variable [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- The `Zs`-points over `x̄ = (x̄ ≫ g) ≫ i` are recovered from their `Vs`-component. -/
theorem fl_Zs (x : P) (hx : (geomPtAt x).pt = ((geomPtAt x).pt ≫ g) ≫ i)
    (c : (geomPtAt x).point.fiber.obj (Zs i g W)) :
    (fl x c ≫ pullback.fst (Vs i W).hom g) ≫ jz W hig = fl x c := by
  have hc : fl x c ≫ pullback.snd (Vs i W).hom g = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf c)
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((whisker_eq _ (jz_fst W hig)).trans (Category.comp_id _))
  · calc ((fl x c ≫ pullback.fst (Vs i W).hom g) ≫ jz W hig) ≫ pullback.snd (Vs i W).hom g
          = (fl x c ≫ pullback.fst (Vs i W).hom g) ≫ ((Vs i W).hom ≫ i) :=
            (Category.assoc _ _ _).trans (whisker_eq _ (jz_snd W hig))
      _ = (fl x c ≫ (pullback.fst (Vs i W).hom g ≫ (Vs i W).hom)) ≫ i :=
            (Category.assoc _ _ _).symm.trans (eq_whisker (Category.assoc _ _ _) _)
      _ = ((fl x c ≫ pullback.snd (Vs i W).hom g) ≫ g) ≫ i :=
            eq_whisker ((whisker_eq _ pullback.condition).trans (Category.assoc _ _ _).symm) _
      _ = fl x c ≫ pullback.snd (Vs i W).hom g :=
            (eq_whisker (eq_whisker hc _) _).trans (hx.symm.trans hc.symm)

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b1 =====
section

/-!
# S4-EtPBC-A, L6b1: the `K`-rational fibre `ι' : P¹_K ⟶ P¹_S` and the horizontal section `σ'` of `ι'^* Zz`

* `toPull f m hm : T' ⟶ (etPull f).obj Y'` from `m : T'.left ⟶ Y'.left` over `f` (`toPull_fst`, `toPull_comp`,
  `toPull_map`);
* `sK = inv (s.pt ≫ gS) ≫ s.pt : Spec K ⟶ S`, `ιP : P¹_K ⟶ P¹_S` (`ιP_pr`, `ιP_qV`, `ptz_ιP : ptz ≫ ιP = sK ≫ σz`);
* for a `K`-point `v'` of `Vs = W ×_P S` over `sK`: `σ₀ v' : P¹_K ⟶ Zz` and `σP v' : etId P¹_K ⟶ ιP^* Zz`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3

universe u

section ToPull

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Y' : Y.Etale} {T' : X.Etale} (m : T'.left ⟶ Y'.left)
  (hm : m ≫ Y'.hom = T'.hom ≫ f)

theorem toPull_fst : (toPull f m hm).left ≫ pullback.fst Y'.hom f = m := pullback.lift_fst _ _ _

theorem toPull_comp {T'' : X.Etale} (n : T'' ⟶ T') :
    n ≫ toPull f m hm = toPull f (n.left ≫ m) ((Category.assoc _ _ _).trans ((whisker_eq _ hm).trans
      ((Category.assoc _ _ _).symm.trans (eq_whisker (MorphismProperty.Over.w n) _)))) :=
  etPull_hom_ext f ((Category.assoc _ _ _).trans ((whisker_eq _ (toPull_fst f m hm)).trans
    (toPull_fst f _ _).symm))

theorem toPull_map {Y'' : Y.Etale} (k : Y' ⟶ Y'') :
    toPull f m hm ≫ (etPull f).map k = toPull f (m ≫ k.left) ((Category.assoc _ _ _).trans
      ((whisker_eq _ (MorphismProperty.Over.w k)).trans hm)) :=
  etPull_hom_ext f ((Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_fst f k)).trans
    ((Category.assoc _ _ _).symm.trans ((eq_whisker (toPull_fst f m hm) _).trans (toPull_fst f _ _).symm))))

theorem toPull_ext {m m' : T'.left ⟶ Y'.left} (hm : m ≫ Y'.hom = T'.hom ≫ f) (hm' : m' ≫ Y'.hom = T'.hom ≫ f)
    (h : m = m') : toPull f m hm = toPull f m' hm' := by
  subst h; rfl

end ToPull

section Fib

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b2 =====
section

/-!
# S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`

For a chart `D = chEt c φ` (`B` Dedekind, `(X - a)` a nonzero prime) and `s' : D ⟶ ιP^* W`:
* the point `d₀ = (X - a)` of `D` over `z = c a` and its `K`-point `δ₀` (`δ₀_hom : δ₀ ≫ D.hom = ptz`);
* `wK = s'(d₀)`, the `K`-point `v'` of `Vs` over `sK` (`v'_hom`), `gE₀ : D ⟶ Es` (`v ↦ (s' v, σ₀ v)`);
* `Vb = gE₀⁻¹(Og)`, `Db = opn D Vb` (`d₀ ∈ Vb`), its fibre at `z` (subsingleton, nonempty) and `hSb`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum

section Sq

end Sq

section Pt

variable {K : Type} [Field K] [IsAlgClosed K] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)]

theorem d₀_closed [IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0)
    (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) : IsClosed ({d₀ c a φ hP} : Set (chEt c φ).left) :=
  (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr (d₀_max a φ ht hP)

end Pt

section Fib

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end


