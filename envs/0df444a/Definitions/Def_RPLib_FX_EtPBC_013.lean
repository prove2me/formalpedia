-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_013
-- name    : RPLib_FX_EtPBC_013
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T17:55:43.343775+00:00
-- url     : https://prove2.me/theorems/1aa1d362-413a-5fd3-9c9b-bb7daecdd496
-- title:
--   Proper base change for the projective line, library file 013
-- statement:
--   File 013 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
--   * `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
--   * `S4.Def_RP_EtPBC_A_CovEtL`: S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)
--   * `S4.Def_RP_EtPBC_A_CovFbA`: S4-EtPBC-A, R4-T2 (G1d, part 1): lifting morphisms to fibres `Spec G` of chart algebras
--   * `S4.Def_RP_EtPBC_A_Inj0c`: S4-EtPBC-A, G1c: base change is injective on germs in degree `0` (universally closed `g`)
--   * `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
--   * `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
--   * `S4.Def_RP_EtPBC_A_NbExt2`: S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood
--   * `S4.Def_RP_EtPBC_A_NbExt3`: S4-EtPBC-A, M2 F8b + F9: surjectivity of base change in degree 0 for `π_* M_Y`
--   * `S4.Def_RP_EtPBC_A_FinGen`: S4-EtPBC-A, M3: a section of `ι^* G` over a quasi-compact `X` comes from finitely many sections of `G`
--   * `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
--   * `S4.Def_RP_EtPBC_A_FBCb`: S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective
--   * `S4.Def_RP_EtPBC_A_PushKill`: S4-EtPBC-A, R4-T3c: effacement through an etale neighbourhood by a pushout
--   * `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
--   * `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
--   * `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
--   * `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
--   * `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
--   * `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
--   * `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_H1Q`: S4-EtPBC-A, R2 for `P¹_S`: degree-1 base change for every sheaf, given the curve case
--   * `S4.Def_RP_EtPBC_A_T2I`: S4-EtPBC-A, R4-T2 interface: `HypT` from T1 and the lifting statement `LiftT`
--   * `S4.Def_RP_EtPBC_A_O2MVo`: S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`
--   * `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
--   * `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
--   * `S4.Def_RP_EtPBC_A_O2Tr1`: S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open
--   * `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
--   * `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
--   * `S4.Def_RP_EtPBC_A_O2E8`: S4-EtPBC-A, O2 C-plan S4d2 (Ext level): purity for `Ext¹(Λ[W₁], Λ_P)`, and changing `Uo` to `Uz`
--   * `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
--   * `S4.Def_RP_EtPBC_A_O2Km6`: S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`
--   * `S4.Def_RP_EtPBC_A_O2UK2b`: S4-EtPBC-A, O2 M6 (O2UK2b): the `d`-th root of `1 + t e` on the pieces over an etale `B → B'`
--   * `S4.Def_RP_EtPBC_A_O2Pb`: S4-EtPBC-A, O2 GLOB (O2Pb): the pullback square of `wm (prdMap d X)` and what it gives on global sections
--   * `S4.Def_RP_EtPBC_A_O2ZarCh`: S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step
--   * `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
--   * `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
--   * `S4.Def_RP_EtPBC_A_O2Gl2f`: S4-EtPBC-A, O2 GLOB (O2Gl2f): the side conditions of stages S3-S4
--   * `S4.Def_RP_EtPBC_A_O2Gl2k`: S4-EtPBC-A, O2 GLOB (O2Gl2k): stage S4 with `H` and `D₂ := (D₁)_{φ₁ c₀'}` fixed
--   * `S4.Def_RP_EtPBC_A_O2Gl3a`: S4-EtPBC-A, O2 GLOB (O2Gl3a): chart facts for the `uk_diff` call on `D₂`
--   * `S4.Def_RP_EtPBC_A_O2Gl3b`: S4-EtPBC-A, O2 GLOB (O2Gl3b): the point over `z` on a chart (inputs `χ`, `hχ`, `ht`, `hd` of `uk_diff`)
--   * `S4.Def_RP_EtPBC_A_O2T5`: S4-EtPBC-A, O2 S5e: splitting off finitely many disjoint sections
--   * `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
--   * `S4.Def_RP_EtPBC_A_O2T9b`: S4-EtPBC-A, O2 S6a (O2T9b): the residual of a one-point class is a one-point class with EMPTY fibre
--   * `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
--   * `S4.Def_RP_EtPBC_A_O2Rel5`: S4-EtPBC-A, O2 REL (O2Rel5): the relation over all points outside a cofinite open
--   * `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
--   * `S4.Def_RP_EtPBC_A_O2PP4b`: S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer
--   * `S4.Def_RP_EtPBC_A_O2PP5a`: S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`
--   * `S4.Def_RP_EtPBC_A_O2Mob`: S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity
--   * `S4.Def_RP_EtPBC_A_O2L1a`: S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--   * `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
--   * `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
--   * `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
--   * `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
--   * `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
--   * `S4.Def_RP_EtPBC_A_O2L6b1`: S4-EtPBC-A, L6b1: the `K`-rational fibre `ι' : P¹_K ⟶ P¹_S` and the horizontal section `σ'` of `ι'^* Zz`
--   * `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
--   * `S4.Def_RP_EtPBC_A_FibP1`: S4-EtPBC-A, G0: the fibre of a `P¹`-bundle at a rational point, and base change in degrees `≥ 4`
--   * `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
--   * `S4.Def_RP_EtPBC_A_O1G1`: S4-EtPBC-A, O1 glue: **degree-1 base change on `P¹_S`**
--   * `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
--   * `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_005
import Definitions.Def_RPLib_FX_EtPBC_006
import Definitions.Def_RPLib_FX_EtPBC_009
import Definitions.Def_RPLib_FX_EtPBC_011

/-!
# Proper base change for the projective line, library file 013

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
* `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
* `S4.Def_RP_EtPBC_A_CovEtL`: S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)
* `S4.Def_RP_EtPBC_A_CovFbA`: S4-EtPBC-A, R4-T2 (G1d, part 1): lifting morphisms to fibres `Spec G` of chart algebras
* `S4.Def_RP_EtPBC_A_Inj0c`: S4-EtPBC-A, G1c: base change is injective on germs in degree `0` (universally closed `g`)
* `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
* `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
* `S4.Def_RP_EtPBC_A_NbExt2`: S4-EtPBC-A, M2 F8a: extending a clopen of `Y_s` to an etale neighbourhood
* `S4.Def_RP_EtPBC_A_NbExt3`: S4-EtPBC-A, M2 F8b + F9: surjectivity of base change in degree 0 for `π_* M_Y`
* `S4.Def_RP_EtPBC_A_FinGen`: S4-EtPBC-A, M3: a section of `ι^* G` over a quasi-compact `X` comes from finitely many sections of `G`
* `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
* `S4.Def_RP_EtPBC_A_FBCb`: S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective
* `S4.Def_RP_EtPBC_A_PushKill`: S4-EtPBC-A, R4-T3c: effacement through an etale neighbourhood by a pushout
* `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
* `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
* `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
* `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
* `S4.Def_RP_EtPBC_A_EN`: S4-EtPBC-A, M4(E), EN: a splitting neighbourhood that kills the relations at the generic point
* `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
* `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
* `S4.Def_RP_EtPBC_A_H1Q`: S4-EtPBC-A, R2 for `P¹_S`: degree-1 base change for every sheaf, given the curve case
* `S4.Def_RP_EtPBC_A_T2I`: S4-EtPBC-A, R4-T2 interface: `HypT` from T1 and the lifting statement `LiftT`
* `S4.Def_RP_EtPBC_A_O2MVo`: S4-EtPBC-A, O2 (MV route), MVo: Mayer-Vietoris for an open `U ⊆ P` and `W : P.Etale`
* `S4.Def_RP_EtPBC_A_O2R2`: S4-EtPBC-A, O2 (MV route), M6a (2): the multi-point MV complex
* `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
* `S4.Def_RP_EtPBC_A_O2Tr1`: S4-EtPBC-A, O2 M6b (O2Tr1): the trace section of a separated etale `W` of constant degree over an open
* `S4.Def_RP_EtPBC_A_O2Sh1`: S4-EtPBC-A, O2 M6 (O2Sh1): `π_*` is exact for a separated etale `π` of constant degree
* `S4.Def_RP_EtPBC_A_O2Sh2`: S4-EtPBC-A, O2 M6 (O2Sh2): `Λ[W] ≅ π_* Λ_W` for a separated etale `π = W.hom` of constant degree
* `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
* `S4.Def_RP_EtPBC_A_O2E8`: S4-EtPBC-A, O2 C-plan S4d2 (Ext level): purity for `Ext¹(Λ[W₁], Λ_P)`, and changing `Uo` to `Uz`
* `S4.Def_RP_EtPBC_A_O2Th1a`: S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality
* `S4.Def_RP_EtPBC_A_O2Km6`: S4-EtPBC-A, O2 M6 (O2Km6): Kummer data for `Ext¹_P(Λ[D ×_P Uo], Λ[R])`
* `S4.Def_RP_EtPBC_A_O2UK2b`: S4-EtPBC-A, O2 M6 (O2UK2b): the `d`-th root of `1 + t e` on the pieces over an etale `B → B'`
* `S4.Def_RP_EtPBC_A_O2Pb`: S4-EtPBC-A, O2 GLOB (O2Pb): the pullback square of `wm (prdMap d X)` and what it gives on global sections
* `S4.Def_RP_EtPBC_A_O2ZarCh`: S4-EtPBC-A, O2 GLOB (O2ZarCh): the chart toolbox for the global step
* `S4.Def_RP_EtPBC_A_O2PPTd`: S4-EtPBC-A, O2 GLOB (O2PPTd): the chart form of the piece transfer, and Zariski shrinks
* `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
* `S4.Def_RP_EtPBC_A_O2Gl2f`: S4-EtPBC-A, O2 GLOB (O2Gl2f): the side conditions of stages S3-S4
* `S4.Def_RP_EtPBC_A_O2Gl2k`: S4-EtPBC-A, O2 GLOB (O2Gl2k): stage S4 with `H` and `D₂ := (D₁)_{φ₁ c₀'}` fixed
* `S4.Def_RP_EtPBC_A_O2Gl3a`: S4-EtPBC-A, O2 GLOB (O2Gl3a): chart facts for the `uk_diff` call on `D₂`
* `S4.Def_RP_EtPBC_A_O2Gl3b`: S4-EtPBC-A, O2 GLOB (O2Gl3b): the point over `z` on a chart (inputs `χ`, `hχ`, `ht`, `hd` of `uk_diff`)
* `S4.Def_RP_EtPBC_A_O2T5`: S4-EtPBC-A, O2 S5e: splitting off finitely many disjoint sections
* `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
* `S4.Def_RP_EtPBC_A_O2T9b`: S4-EtPBC-A, O2 S6a (O2T9b): the residual of a one-point class is a one-point class with EMPTY fibre
* `S4.Def_RP_EtPBC_A_O2Bd4`: S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`
* `S4.Def_RP_EtPBC_A_O2Rel5`: S4-EtPBC-A, O2 REL (O2Rel5): the relation over all points outside a cofinite open
* `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
* `S4.Def_RP_EtPBC_A_O2PP4b`: S4-EtPBC-A, O2 PP' (O2PP4b): chart helpers for the S1 layer
* `S4.Def_RP_EtPBC_A_O2PP5a`: S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`
* `S4.Def_RP_EtPBC_A_O2Mob`: S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity
* `S4.Def_RP_EtPBC_A_O2L1a`: S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
* `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
* `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
* `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
* `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
* `S4.Def_RP_EtPBC_A_O2Gen1`: S4-EtPBC-A, O2 Gen1: point classes along maps, chart facts on `P¹`
* `S4.Def_RP_EtPBC_A_O2L6b1`: S4-EtPBC-A, L6b1: the `K`-rational fibre `ι' : P¹_K ⟶ P¹_S` and the horizontal section `σ'` of `ι'^* Zz`
* `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L6b3`: S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`
* `S4.Def_RP_EtPBC_A_FibP1`: S4-EtPBC-A, G0: the fibre of a `P¹`-bundle at a rational point, and base change in degrees `≥ 4`
* `S4.Def_RP_EtPBC_A_O2L7b1`: S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
* `S4.Def_RP_EtPBC_A_O1G1`: S4-EtPBC-A, O1 glue: **degree-1 base change on `P¹_S`**
* `S4.Def_RP_EtPBC_A_O2L7b2`: S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
* `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
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

theorem isLisse_res {Λ : Type u} [CommRing Λ] {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {F : EtSh Λ X}
    (hF : IsLisse Λ F) : IsLisse Λ ((res g Λ).obj F) :=
  (hF.pull g).of_iso ((pullIsoRes g Λ).app F)

end Gen

section Chart

end Chart

section P1

variable (k : Type) [Field k]

instance (s : P1 k) : IsOpenImmersion (p1Chart k s) := by
  unfold p1Chart
  split_ifs <;> infer_instance

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

/-- The fibre inclusion `ι : P_s ⟶ P`. -/
abbrev fibι : fib g s ⟶ P := pullback.fst g s.pt

/-- `(V, v) ↦ Λ[g⁻¹ V]`. -/
def nbhdSys : Nbhd s ⥤ EtSh Λ P :=
  CategoryOfElements.π s.point.fiber ⋙ etPull g ⋙ freeFun Λ P

theorem nbhd_w (j : Nbhd s) : j.2.left ≫ j.1.hom = s.pt := Over.w j.2

@[reassoc]
theorem nbhd_hom_w {j j' : Nbhd s} (a : j' ⟶ j) : j'.2.left ≫ a.1.left = j.2.left :=
  congrArg CommaMorphism.left a.2

section EtPull

end EtPull

/-- The point `v` of `V` over `s` as a map `P_s ⟶ g⁻¹ V`. -/
def fibToNbhd (j : Nbhd s) : fib g s ⟶ pullback j.1.hom g :=
  pullback.lift (pullback.snd g s.pt ≫ j.2.left) (pullback.fst g s.pt)
    ((Category.assoc _ _ _).trans ((whisker_eq _ (nbhd_w s j)).trans pullback.condition.symm))

end RamanujanPetersson.EtPBC

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

theorem etK_le_iff (q : PrimeSpectrum M) : etK B M ≤ q.asIdeal ↔ q ∉ Algebra.etaleLocus B M := by
  have h1 : q ∈ PrimeSpectrum.zeroLocus (etK B M : Set M) ↔ etK B M ≤ q.asIdeal :=
    PrimeSpectrum.mem_zeroLocus q _
  rw [← h1, etK, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    (Algebra.isOpen_etaleLocus (R := B) (A := M)).isClosed_compl.closure_eq, Set.mem_compl_iff]

end EtK

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

variable {E G : Type u} [CommRing E] [CommRing G] (θ : E →+* G) (sθ : Function.Surjective θ) {W : Scheme.{u}}

theorem εW_comp {W' : Scheme.{u}} (f : W' ⟶ W) (w : W ⟶ Spec (CommRingCat.of E)) :
    εW (f ≫ w) = f.appTop.hom.comp (εW w) := by
  show ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫ (f ≫ w).appTop).hom = _
  rw [Scheme.Hom.comp_appTop]; rfl

theorem εW_SpecMap {E' : Type u} [CommRing E'] (ψ : E →+* E') (w : W ⟶ Spec (CommRingCat.of E')) :
    εW (w ≫ Spec.map (CommRingCat.ofHom ψ)) = (εW w).comp ψ := by
  have h : CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of E')).inv ≫ w.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫ (w ≫ Spec.map (CommRingCat.ofHom ψ)).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Hom.comp_appTop]
  exact (congrArg CommRingCat.Hom.hom h).symm

/-- The lift `G → Γ(W)` of `εW w` through `θ`. -/
def liftW (w : W ⟶ Spec (CommRingCat.of E)) (hk : RingHom.ker θ ≤ RingHom.ker (εW w)) : G →+* Γ(W, ⊤) :=
  θ.liftOfSurjective sθ ⟨εW w, hk⟩

end Lift

section Ker

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

/-- The fibre of `g⁻¹ V ⟶ V` over `v`, mapped to `P_s`. -/
def fibCmp (j : Nbhd s) : pullback (pullback.fst j.1.hom g) j.2.left ⟶ fib g s :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd j.1.hom g) (pullback.snd _ _)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun φ => pullback.fst (pullback.fst j.1.hom g) j.2.left ≫ φ)
        (pullback.condition (f := j.1.hom) (g := g)).symm).trans
      ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun φ => φ ≫ j.1.hom) (pullback.condition (f := pullback.fst j.1.hom g) (g := j.2.left))).trans
      ((Category.assoc _ _ _).trans
      (congrArg (fun φ => pullback.snd (pullback.fst j.1.hom g) j.2.left ≫ φ) (nbhd_w (s := s) j)))))))

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

/-- Germs are invariant under restriction. -/
theorem germ_res {j j' : Nbhd t} (a : j' ⟶ j) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj j.1))) :
    (t.point.toPresheafFiber j'.1 j'.2 ((push π Λ).obj (constSh Λ Y M)).obj).hom
        (((constSh Λ Y M).obj.map ((etPull π).map a.1).op).hom z) =
      (t.point.toPresheafFiber j.1 j.2 ((push π Λ).obj (constSh Λ Y M)).obj).hom z := by
  have hw := ConcreteCategory.congr_hom (t.point.toPresheafFiber_w a.1 j'.2 ((push π Λ).obj (constSh Λ Y M)).obj) z
  have hj : t.point.fiber.map a.1 j'.2 = j.2 := a.2
  exact hw.trans
    (congrArg (fun y => (t.point.toPresheafFiber j.1 y ((push π Λ).obj (constSh Λ Y M)).obj).hom z) hj)

theorem exists_rep (e : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj ((push π Λ).obj (constSh Λ Y M)).obj) :
    ∃ (j : Nbhd t) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj j.1))),
      (t.point.toPresheafFiber j.1 j.2 ((push π Λ).obj (constSh Λ Y M)).obj).hom z = e := by
  obtain ⟨X, x, z, hz⟩ := t.point.toPresheafFiber_jointly_surjective e
  exact ⟨⟨X, x⟩, z, hz⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NbExt1 =====
section

/-!
# S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods

Plain-morphism version: a neighbourhood is given by `hj : V ⟶ S` and `v : Spec Ω ⟶ V` with `v ≫ hj = s.pt`.
* `pMapV : V ×_S P ≅ P¹_V`, `piVV : Y_V ⟶ P¹_V` (finite), `xV = (s ≫ g_K)⁻¹ ≫ v : Spec K ⟶ V`;
* `fibV : P_s ⟶ V ×_S P`, `ysV : Y_s ⟶ Y_V` (definitionally `ysj` for a `Nbhd`);
* `eYV : Y_s ⟶ Y_x` and `eY'V : Y_x ⟶ Y_s` with **`eYV_eY'V`** (`eYV ≫ eY'V = 𝟙`);
* for an etale `Γ(V)`-algebra `R'` and a lift `x'` of `xV`: `kapV : Y_{V'} ⟶ Y ×_V Spec R'` with
  **`ysV_kapV`**: `ysV' ≫ kapV = eYV ≫ yxMap`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S)
  {Y : Scheme.{u}} (π : Y ⟶ PV K gK) {V : Scheme.{u}} (hj : V ⟶ S)

variable [IsIso (s.pt ≫ gK)] (v : Spec (CommRingCat.of s.Ω) ⟶ V)

theorem xV_g (hv : v ≫ hj = s.pt) : xV K gK s v ≫ hj ≫ gK = 𝟙 _ := by
  unfold xV
  rw [Category.assoc, reassoc_of% hv, IsIso.inv_hom_id]

section Ext

end Ext

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

/-- The point of a neighbourhood, typed over `j.1.left`. -/
def nbv {S : Scheme.{u}} (s : GeomPt S) (j : Nbhd s) : Spec (CommRingCat.of s.Ω) ⟶ j.1.left := j.2.left

/-- The structure map of a neighbourhood, typed from `j.1.left`. -/
def nbh {S : Scheme.{u}} (s : GeomPt S) (j : Nbhd s) : j.1.left ⟶ S := j.1.hom

theorem nbv_w {S : Scheme.{u}} (s : GeomPt S) (j : Nbhd s) : nbv s j ≫ nbh s j = s.pt := nbhd_w s j

section Nbhd

end Nbhd

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NbExt3 =====
section

/-!
# S4-EtPBC-A, M2 F8b + F9: surjectivity of base change in degree 0 for `π_* M_Y`

* `exists_affine_nbhd`: an affine noetherian neighbourhood of `s` (S locally noetherian);
* `exists_sec_vv`: a section `z` over some `Y_j` with `cval z ∘ ysj j = vv b` (induction over the finitely many values,
  each step `exists_clopen_nbhd` + `exists_indicator` + restriction);
* **`bcSurj_push_const`**: `BCSurj Λ (qV K gK) s 0 (π_* M_Y)` for `π : Y ⟶ P¹_S` finite.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtPBC.Z3

universe u

/-- An affine noetherian etale neighbourhood of `s` (an open affine of `S`). -/
theorem exists_affine_nbhd {S : Scheme.{u}} [IsLocallyNoetherian S] (s : GeomPt S) :
    ∃ j : Nbhd s, IsAffine j.1.left ∧ IsNoetherianRing Γ(j.1.left, ⊤) := by
  obtain ⟨p0⟩ : Nonempty (Spec (CommRingCat.of s.Ω)) := ⟨default⟩
  have hsub : ∀ p : Spec (CommRingCat.of s.Ω), p = p0 := fun p =>
    Subsingleton.elim (α := PrimeSpectrum s.Ω) _ _
  obtain ⟨R, f, hf, ⟨y, hy⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := S)
    (x := s.pt p0) (U := ⊤) (by simp)
  haveI : IsOpenImmersion f := hf
  have hR : Set.range s.pt ⊆ Set.range f := by
    rintro _ ⟨p, rfl⟩
    exact ⟨y, by rw [hsub p]; exact hy⟩
  let E : S.Etale := MorphismProperty.Over.mk ⊤ f inferInstance
  let v : Spec (CommRingCat.of s.Ω) ⟶ Spec R := IsOpenImmersion.lift f s.pt hR
  have hv : v ≫ f = s.pt := IsOpenImmersion.lift_fac f s.pt hR
  refine ⟨s.point.fiber.elementsMk E (Over.homMk v hv :
    CategoryTheory.Over.mk s.pt ⟶ (Scheme.Etale.forget S).obj E), ?_, ?_⟩
  · show IsAffine (Spec R)
    infer_instance
  · have := isLocallyNoetherian_of_isOpenImmersion f
    show IsNoetherianRing Γ(Spec R, ⊤)
    exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_FinGen =====
section

/-!
# S4-EtPBC-A, M3: a section of `ι^* G` over a quasi-compact `X` comes from finitely many sections of `G`

* `exists_repG`, **`exists_pullRepG`**: local representation of a section of `ι^* G` (any sheaf `G`);
* **`exists_fg`**: for `X` compact, finitely many sections `z x ∈ G(W x)` (`x ∈ t`) such that `b ≫ ι^* p = 0` for every
  `p : G ⟶ Q` killing them;
* `etSh_hasColimitsOfShape_discrete`: fast instance for finite coproducts in `EtSh Λ Q`;
* **`bcSurj_of_fg`**: `BCSurj 0` for `G` follows from `BCSurj 0` for the subsheaves `ker (coker φ)` generated by
  finitely many sections `φ : ∐ Λ[W x] ⟶ G`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {X P : Scheme.{u}} (ι : X ⟶ P)

theorem exists_repG (t : GeomPt P) (G : EtSh Λ P) (e : (t.point.presheafFiber (A := ModuleCat.{u} Λ)).obj G.obj) :
    ∃ (j : Nbhd t) (z : G.obj.obj (op j.1)), (t.point.toPresheafFiber j.1 j.2 G.obj).hom z = e := by
  obtain ⟨W, w, z, hz⟩ := t.point.toPresheafFiber_jointly_surjective e
  exact ⟨⟨W, w⟩, z, hz⟩

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

/-- The fibre map `fib (h ≫ Φ) t ⟶ fib Φ t`. -/
def nuU (t : GeomPt P) : fib (h ≫ Φ) t ⟶ fib Φ t :=
  pullback.lift (pullback.fst _ _ ≫ h) (pullback.snd _ _) ((Category.assoc _ _ _).trans pullback.condition)

end RU

end RamanujanPetersson.EtPBC.FBC

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

/-- A section of `nuU` when `t` factors through `ι`. -/
def secU (t : GeomPt P) (σ₀ : Spec (CommRingCat.of t.Ω) ⟶ Ps) (hσ : σ₀ ≫ ι = t.pt) :
    fib Φ t ⟶ fib (pullback.fst Φ ι ≫ Φ) t :=
  pullback.lift (pullback.lift (pullback.fst Φ t.pt) (pullback.snd Φ t.pt ≫ σ₀)
      (pullback.condition.trans (by rw [Category.assoc, hσ])))
    (pullback.snd Φ t.pt) (by rw [← Category.assoc, pullback.lift_fst, pullback.condition])

end Stalk

end RamanujanPetersson.EtPBC.FBC

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

end Abstract

section Geo

open AlgebraicGeometry RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- `ι'^* ∘ f^* ≅ ι^*` for a lift `ι'` of the fibre inclusion through `f`. -/
def liftIso {P' : Scheme.{u}} (f : P' ⟶ P) (ι' : fib g s ⟶ P') (hι : ι' ≫ f = fibι g s) :
    pull f Λ ⋙ pull ι' Λ ≅ pull (fibι g s) Λ :=
  (pullCompIso Λ ι' f).symm ≪≫ pullCongr Λ hι

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

/-- The fibre inclusion is a closed immersion when the geometric point is. -/
theorem isClosedImmersion_fibι {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S) [IsClosedImmersion s.pt] :
    IsClosedImmersion (fibι g s) := by
  unfold fibι
  infer_instance

end Geo0

section RUq

end RUq

section M

end M

end RamanujanPetersson.EtPBC.T3d

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

end C1

section B3

variable {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

theorem liftIso_inv_app {P' : Scheme.{u}} (f : P' ⟶ P) (ι' : fib g s ⟶ P') (hι : ι' ≫ f = fibι g s)
    (G : EtSh Λ P) :
    (liftIso g s f ι' hι).inv.app G = (pullCongr Λ hι).inv.app G ≫ (pullCompIso Λ ι' f).hom.app G := by
  rw [liftIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]

end B3

end RamanujanPetersson.EtPBC.T3d

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

/-- `N ⟶ E''`. -/
abbrev aPP : constSh Λ Ys N ⟶ Epp q N a' := pushout.inr _ _

/-- `E'' ⟶ Λ`. -/
def bPP : Epp q N a' ⟶ unitSh Λ Ys :=
  pushout.desc ((pull q Λ).map b' ≫ (pullConst Λ q (ModuleCat.of Λ Λ)).hom) 0 (by
    rw [← Functor.map_comp_assoc, w', Functor.map_zero, zero_comp, comp_zero])

variable {Z : Scheme.{u}} (ψ' : Z ⟶ Ys) (τ : Epp q N a' ⟶ (push ψ' Λ).obj (constSh Λ Z N))

/-- `κ₀ : E' ⟶ (ψ' ≫ q)_* N_Z`, the adjunct of `E'' ⟶ ψ'_* N_Z` restricted to `q^* E'`. -/
def kap0 : E' ⟶ (push (ψ' ≫ q) Λ).obj (constSh Λ Z N) :=
  (pullAdj q Λ).homEquiv _ _ (pushout.inl _ _ ≫ τ) ≫ (pushCompIso Λ ψ' q).hom.app _

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

section Prd

variable (W T : P.Etale)

/-- The first projection. -/
def prW : prd W T ⟶ W := MorphismProperty.Over.homMk (pullback.fst W.hom T.hom) pullback.condition

/-- The second projection. -/
def prT : prd W T ⟶ T := MorphismProperty.Over.homMk (pullback.snd W.hom T.hom) rfl

variable {W T}

/-- The section of `prT` given by `τ : T ⟶ W`. -/
def sec (τ : T ⟶ W) : T ⟶ prd W T :=
  MorphismProperty.Over.homMk (pullback.lift τ.left (𝟙 _) (by rw [MorphismProperty.Over.w τ, Category.id_comp]))
    ((pullback.lift_snd_assoc _ _ _ _).trans (Category.id_comp _))

/-- The point of `W ×_P T` over `ȳ` with components `a`, `t`. -/
def pair (y : P) (a : (geomPtAt y).point.fiber.obj W) (t : (geomPtAt y).point.fiber.obj T) :
    (geomPtAt y).point.fiber.obj (prd W T) :=
  (Over.homMk (pullback.lift (fl y a) (fl y t)
      ((Over.w ((geomPtAt y).liftOf a)).trans (Over.w ((geomPtAt y).liftOf t)).symm))
    (by
      exact (pullback.lift_snd_assoc _ _ _ _).trans (Over.w ((geomPtAt y).liftOf t))) :
    CategoryTheory.Over.mk (geomPtAt y).pt ⟶ (Scheme.Etale.forget P).obj (prd W T))

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

/-- `c ↦ Σ c_p · τ_p^* (f p.1)`. -/
def gsum {T : P.Etale} (τ : ∀ p : FibPts x W, T ⟶ W p.1) : (FibPts x W →₀ Λ) →ₗ[Λ] G.obj.obj (op T) :=
  Finsupp.linearCombination Λ fun p => (G.obj.map (τ p).op).hom (f p.1)

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

theorem f0_eq : f0 T ξ = T.left.fromSpecResidueField ξ ≫ T.hom :=
  T.hom.SpecMap_residueFieldMap_fromSpecResidueField ξ

instance : QuasiCompact (f0 T ξ) := by
  rw [quasiCompact_iff]
  intro U _ _
  apply Set.Subsingleton.isCompact
  intro a _ b _
  exact Subsingleton.elim a b

section Sec

variable {T} (W : P.Etale)

/-- `X' := Spec κ(ξ) ×_P W`. -/
abbrev Xp : Scheme.{u} := pullback (f0 T ξ) W.hom

instance etale_fst : Etale (pullback.fst (f0 T ξ) W.hom) := by
  have : Etale W.hom := W.prop
  infer_instance

end Sec

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

section Rel

variable {Λ : Type u} [CommRing Λ] (F : EtSh Λ P) {J : Type u} (W : J → P.Etale)
  (z : ∀ j, F.obj.obj (op (W j))) (η : P)

/-- The module `M := Λ[fibre points at η̄] ⧸ (relations at η̄)`. -/
abbrev Mq : ModuleCat.{u} Λ := ModuleCat.of Λ ((FibPts η W →₀ Λ) ⧸ LinearMap.ker (GenAlg.rel W F z η))

/-- The class of a fibre point in `M`. -/
def mkv (p : FibPts η W) : Mq F W z η := Submodule.mkQ (LinearMap.ker (GenAlg.rel W F z η)) (Finsupp.single p 1)

end Rel

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_H1Q =====
section

/-!
# S4-EtPBC-A, R2 for `P¹_S`: degree-1 base change for every sheaf, given the curve case

* `isAffineHom_to_fib`: maps from affine schemes to a geometric fibre of a separated morphism are affine;
* **`bcSurj_one_qV`**: `BCSurj 1` for every sheaf on `P¹_S` at `s`, given `BCSurj 1` for every `π_* M_Y` with
  `π : Y ⟶ P¹_S` finite and `M` finite (`Λ` finite; the curve case R4).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.GenGeo

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

variable {Λ : Type u} [CommRing Λ] {S : Scheme.{u}}

/-- Maps from affine schemes to a geometric fibre of a separated morphism are affine. -/
theorem isAffineHom_to_fib {P : Scheme.{u}} (g : P ⟶ S) [IsSeparated g] (s : GeomPt S) {Z : Scheme.{u}}
    (h : Z ⟶ fib g s) (hZ : IsAffine Z) : IsAffineHom h := by
  have : IsSeparated (pullback.snd g s.pt) := inferInstance
  have : IsAffineHom (h ≫ pullback.snd g s.pt) := inferInstance
  exact IsAffineHom.of_comp (f := h) (g := pullback.snd g s.pt)

end RamanujanPetersson.EtPBC.GenGeo

end

end

-- ===== S4.Def_RP_EtPBC_A_T2I =====
section

/-!
# S4-EtPBC-A, R4-T2 interface: `HypT` from T1 and the lifting statement `LiftT`

* **`LiftT g s π`** (the remaining input, pure geometry): every finite etale surjective `T ⟶ Y_s` is dominated, over
  `Y_s`, by the fibre `U_s` of a finite `U ⟶ P'` over an etale neighbourhood `P' ⟶ P` of the fibre, with `U`
  covering `P' ×_P Y`.
* **`hypT_of_liftT`**: `T1` turns `LiftT` into `T3d.HypT` (given compactness of `Y_s` and affineness of etale maps
  from affine schemes to `Y_s`); `hypT_of_liftT'` discharges both for `g` separated, `fib g s` compact, `π` finite.
* **`bcSurj_one_push_of_liftT`**: degree-one base change for `π_* N_Y` from degree zero and `LiftT`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.T2

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- **T2, the lifting input**: every finite etale surjective cover `T` of `Y_s` is dominated over `Y_s` by `U_s`,
for a finite `Φ : U ⟶ P'` over an etale `f : P' ⟶ P` with a closed lift `ι'` of the fibre and `U ↠ P' ×_P Y`. -/
def LiftT {Y : Scheme.{u}} (π : Y ⟶ P) : Prop :=
  ∀ T : (pullback π (fibι g s)).Etale, IsFinite T.hom → Surjective T.hom →
    ∃ (P' U : Scheme.{u}) (f : P' ⟶ P) (_ : Etale f) (ι' : fib g s ⟶ P') (hι : ι' ≫ f = fibι g s)
      (_ : IsClosedImmersion ι') (Φ : U ⟶ P') (_ : IsFinite Φ) (h : U ⟶ Y) (hh : h ≫ π = Φ ≫ f)
      (_ : Function.Surjective ⇑(pullback.lift Φ h hh.symm : U ⟶ pullback f π))
      (ψ : pullback Φ ι' ⟶ T.left), ψ ≫ T.hom = T3d.hsU π f Φ h hh ι' (fibι g s) hι

theorem compactSpace_fibY [CompactSpace (fib g s)] {Y : Scheme.{u}} (π : Y ⟶ P) [IsFinite π] :
    CompactSpace (pullback π (fibι g s) : Scheme.{u}) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd π (fibι g s))

end RamanujanPetersson.EtPBC.T2

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

theorem prd_fib_ext {W T : P.Etale} (x : P) {c c' : (geomPtAt x).point.fiber.obj (prd W T)}
    (h1 : (geomPtAt x).point.fiber.map (prW W T) c = (geomPtAt x).point.fiber.map (prW W T) c')
    (h2 : (geomPtAt x).point.fiber.map (prT W T) c = (geomPtAt x).point.fiber.map (prT W T) c') : c = c' := by
  have e1 : ((geomPtAt x).liftOf c).left ≫ pullback.fst W.hom T.hom =
      ((geomPtAt x).liftOf c').left ≫ pullback.fst W.hom T.hom :=
    congrArg (fun d => ((geomPtAt x).liftOf d).left) h1
  have e2 : ((geomPtAt x).liftOf c).left ≫ pullback.snd W.hom T.hom =
      ((geomPtAt x).liftOf c').left ≫ pullback.snd W.hom T.hom :=
    congrArg (fun d => ((geomPtAt x).liftOf d).left) h2
  exact fiber_ext _ (pullback.hom_ext e1 e2)

theorem prT_bijective (W T : P.Etale) (x : P) (hT : IsEmpty ((geomPtAt x).point.fiber.obj T)) :
    Function.Bijective ((geomPtAt x).point.fiber.map (prT W T)) :=
  ⟨fun c _ _ => (hT.false ((geomPtAt x).point.fiber.map (prT W T) c)).elim, fun t => (hT.false t).elim⟩

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

/-- The pieces `S k ×_P U₀`, glued. -/
abbrev copPrd : P.Etale := cop (fun k => prd (S k) (opEt U₀))

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

/-- `D₁ ×_P X ⟶ D ×_P X` induced by `d : D₁ ⟶ D`. -/
def prdMap : prd D₁ X ⟶ prd D X :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst D₁.hom X.hom ≫ d.left) (pullback.snd D₁.hom X.hom)
      ((Category.assoc _ _ _).trans ((congrArg (fun t => pullback.fst D₁.hom X.hom ≫ t)
        (MorphismProperty.Over.w d)).trans pullback.condition)))
    (pullback.lift_snd_assoc _ _ _ _)

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

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.EtMV

universe u

variable {P : Scheme.{u}}

section Agr

variable {T W : P.Etale} (τ₁ τ₂ : T ⟶ W)

/-- **The agreement locus** of `τ₁, τ₂` (pull-back of the diagonal of `W`). -/
def agr : Set T.left :=
  Set.range (pullback.snd (pullback.diagonal W.hom) (pullback.lift τ₁.left τ₂.left (agr_w τ₁ τ₂)))

theorem agr_eq : pullback.snd (pullback.diagonal W.hom) (pullback.lift τ₁.left τ₂.left (agr_w τ₁ τ₂)) ≫ τ₁.left =
    pullback.snd (pullback.diagonal W.hom) (pullback.lift τ₁.left τ₂.left (agr_w τ₁ τ₂)) ≫ τ₂.left := by
  have h := pullback.condition (f := pullback.diagonal W.hom) (g := pullback.lift τ₁.left τ₂.left (agr_w τ₁ τ₂))
  have h1 := congrArg (· ≫ pullback.fst W.hom W.hom) h
  have h2 := congrArg (· ≫ pullback.snd W.hom W.hom) h
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, pullback.lift_fst, pullback.lift_snd,
    Category.comp_id] at h1 h2
  exact h1.symm.trans h2

theorem mem_agr_of_comp_eq {S : Scheme.{u}} (g : S ⟶ T.left) (h : g ≫ τ₁.left = g ≫ τ₂.left) (s : S) :
    g s ∈ agr τ₁ τ₂ := by
  have hl : (g ≫ τ₁.left) ≫ pullback.diagonal W.hom = g ≫ pullback.lift τ₁.left τ₂.left (agr_w τ₁ τ₂) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      exact (congrArg (g ≫ ·) (pullback.lift_fst τ₁.left τ₂.left (agr_w τ₁ τ₂))).symm
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
      exact (congrArg (g ≫ ·) (pullback.lift_snd τ₁.left τ₂.left (agr_w τ₁ τ₂))).symm
  refine ⟨pullback.lift (g ≫ τ₁.left) g hl s, ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]

variable [IsSeparated W.hom] in
theorem isClosed_agr : IsClosed (agr τ₁ τ₂) :=
  (pullback.snd (pullback.diagonal W.hom) (pullback.lift τ₁.left τ₂.left (agr_w τ₁ τ₂))).isClosedEmbedding.isClosed_range

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

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Sheet

variable {W N : P.Etale}

/-- The same map over `P`. -/
def shP (s : N ⟶ W) : N ⟶ prd N W :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 _) s.left (sh_lift_w s))
    (by show _ ≫ pullback.snd N.hom W.hom ≫ W.hom = _; rw [pullback.lift_snd_assoc, sh_w])

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

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtTr

universe u

variable {P : Scheme.{u}}

section Dg

variable (W : P.Etale)

theorem lift_mem_dg_iff {T : P.Etale} (τ₁ τ₂ : T ⟶ W) (v : T.left) :
    pullback.lift τ₁.left τ₂.left (agr_w τ₁ τ₂) v ∈ dg W ↔ v ∈ agr τ₁ τ₂ := by
  rw [agr, Scheme.Pullback.range_snd]
  exact Iff.rfl

end Dg

section Iso

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

variable {a}

instance isOpenImmersion_fstUo (Uo : P.Opens) : IsOpenImmersion (pullback.fst (chEt c φ).hom (opEt Uo).hom) :=
  MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ (isOpenImmersion_opEt Uo)

theorem range_fstUo (Uo : P.Opens) (u : Spec B) :
    u ∈ Set.range (pullback.fst (chEt c φ).hom (opEt Uo).hom) ↔ (chEt c φ).hom u ∈ Uo := by
  rw [IsOpenImmersion.range_pullbackFst]
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]
    exact opnι_mem (etId P) Uo v
  · intro hu
    refine ⟨⟨_, hu⟩, ?_⟩
    show (Uo.ι ≫ 𝟙 P) ⟨_, hu⟩ = _
    rw [Category.comp_id]
    exact Scheme.Opens.ι_apply Uo ⟨_, hu⟩

section Cls

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

variable {P : Scheme.{u}} (D : P.Etale) {X₁ X : P.Etale} (e : X₁ ⟶ X)

/-- `D ×_P X₁ ⟶ D ×_P X` induced by `e : X₁ ⟶ X`. -/
def prdMapR : prd D X₁ ⟶ prd D X :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst D.hom X₁.hom) (pullback.snd D.hom X₁.hom ≫ e.left)
      (pullback.condition.trans ((congrArg (fun t => pullback.snd D.hom X₁.hom ≫ t)
        (MorphismProperty.Over.w e)).symm.trans (Category.assoc _ _ _).symm)))
    ((pullback.lift_snd_assoc _ _ _ _).trans ((Category.assoc _ _ _).trans
      (congrArg (fun t => pullback.snd D.hom X₁.hom ≫ t) (MorphismProperty.Over.w e))))

theorem prdMapR_prW : prdMapR D e ≫ prW D X = prW D X₁ :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

end PrdR

section Cancel

end Cancel

section PurE

end PurE

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Th1a =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1a): over-`D₀` maps for Shapiro over a fixed base, and their naturality

Fix `D₀ R : P.Etale` with `W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`.
For `τ : T ⟶ D₀` (any `T : P.Etale` over `D₀`):
* **`theta Λ D₀ R n hn τ : Ext¹_P(Λ[T], Λ[R]) ≃+ H¹(T ×_P R, Λ)`** (extension by zero to `D₀`, Shapiro for
  `W₀ ⟶ D₀`, pullback of free sheaves, `T ×_{D₀} W₀ ≅ T ×_P R`);
* **`theta_natural`**: for `m : T₁ ⟶ T₂` with `m ≫ τ₂ = τ₁`,
  `θ_{τ₁}(Λ[m]^* x) = resLE (wm R m) (θ_{τ₂} x)` (`wm R m : T₁ ×_P R ⟶ T₂ ×_P R`);
* `extFreeV_natural` (naturality of `extFreeV` in `V`), `shapExt_symm_natural`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.GalTrE

universe u

section ExtV

end ExtV

section ShapNat

end ShapNat

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} (D₀ R : P.Etale)

variable {R} in
/-- `T₁ ×_P R ⟶ T₂ ×_P R`. -/
def wm {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) : ((etPull T₁.hom).obj R).left ⟶ ((etPull T₂.hom).obj R).left :=
  (prdMapR R m).left

instance etale_wm {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) : Etale (wm (R := R) m) :=
  show Etale (prdMapR R m).left from inferInstance

theorem wm_fst {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) :
    wm (R := R) m ≫ pullback.fst R.hom T₂.hom = pullback.fst R.hom T₁.hom :=
  pullback.lift_fst _ _ _

theorem wm_snd {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) :
    wm (R := R) m ≫ pullback.snd R.hom T₂.hom = pullback.snd R.hom T₁.hom ≫ m.left :=
  pullback.lift_snd _ _ _

theorem wm_comp {T₁ T₂ T₃ : P.Etale} (m : T₁ ⟶ T₂) (m' : T₂ ⟶ T₃) :
    wm (R := R) m ≫ wm (R := R) m' = wm (R := R) (m ≫ m') := by
  apply pullback.hom_ext
  · rw [Category.assoc, wm_fst, wm_fst, wm_fst]
  · rw [Category.assoc, wm_snd R m', ← Category.assoc, wm_snd R m, Category.assoc, wm_snd R (m ≫ m')]
    rfl

variable {D₀} in
/-- `T ×_P R` as an etale `W₀`-scheme. -/
def ovrW {T : P.Etale} (τ : T ⟶ D₀) : ((etPull D₀.hom).obj R).left.Etale := Scheme.Etale.mk (wm (R := R) τ)

variable {D₀} in
/-- `T ×_P R ⟶ (T over D₀) ×_{D₀} W₀`. -/
def ιInv {T : P.Etale} (τ : T ⟶ D₀) :
    ((etPull T.hom).obj R).left ⟶ ((etPull ((etPull D₀.hom).obj R).hom).obj (ovr τ)).left :=
  pullback.lift (pullback.snd R.hom T.hom) (wm (R := R) τ) (wm_snd R τ).symm

variable {D₀} in
theorem ιInv_fst {T : P.Etale} (τ : T ⟶ D₀) :
    ιInv R τ ≫ pullback.fst (ovr τ).hom ((etPull D₀.hom).obj R).hom = pullback.snd R.hom T.hom :=
  pullback.lift_fst _ _ _

variable {D₀} in
theorem ιInv_snd {T : P.Etale} (τ : T ⟶ D₀) :
    ιInv R τ ≫ pullback.snd (ovr τ).hom ((etPull D₀.hom).obj R).hom = wm (R := R) τ :=
  pullback.lift_snd _ _ _

variable {D₀} in
theorem ιHom_wm {T : P.Etale} (τ : T ⟶ D₀) :
    ιHom R τ ≫ wm (R := R) τ = pullback.snd (ovr τ).hom ((etPull D₀.hom).obj R).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, wm_fst, ιHom_fst]
  · rw [Category.assoc, wm_snd, ← Category.assoc, ιHom_snd]
    exact pullback.condition

variable {D₀} in
/-- **`(T over D₀) ×_{D₀} W₀ ≅ T ×_P R` over `W₀`.** -/
def ovrι {T : P.Etale} (τ : T ⟶ D₀) : (etPull ((etPull D₀.hom).obj R).hom).obj (ovr τ) ≅ ovrW R τ :=
  MorphismProperty.Over.isoMk
    { hom := ιHom R τ
      inv := ιInv R τ
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, ιInv_fst, ιHom_snd, Category.id_comp]
        · rw [Category.assoc, ιInv_snd, ιHom_wm, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, ιHom_fst, ← Category.assoc, ιInv_snd, wm_fst, Category.id_comp]
        · rw [Category.assoc, ιHom_snd, ιInv_fst, Category.id_comp] }
    (ιHom_wm R τ)

variable {D₀}

/-- `T₁ ×_P R ⟶ T₂ ×_P R` over `W₀`. -/
def ovrMapW {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) {τ₁ : T₁ ⟶ D₀} {τ₂ : T₂ ⟶ D₀} (h : m ≫ τ₂ = τ₁) :
    ovrW R τ₁ ⟶ ovrW R τ₂ :=
  MorphismProperty.Over.homMk (wm (R := R) m)
    (by
      subst h
      exact wm_comp R m τ₂)

end Theta

end RamanujanPetersson.EtPBC.EtShap

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

instance qc_R : QuasiCompact R.hom := by
  let f : R.left ⟶ P := R.hom
  have : IsAffineHom f := isAffineHom_of_isAffine_source f
  have h : QuasiCompact f := inferInstance
  exact h

instance sep_R : IsSeparated R.hom := by
  let f : R.left ⟶ P := R.hom
  have : IsAffineHom f := isAffineHom_of_isAffine_source f
  have h : IsSeparated f := IsSeparated.of_isAffineHom f
  exact h

end Inst

section Assembly

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left]

/-- The structure map of the Shapiro scheme `W = (D ×_P Uo) ×_P R` to `𝔸¹ = Spec k[X]`. -/
noncomputable def shG : ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left ⟶ Spec (CommRingCat.of k[X]) :=
  ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).hom ≫ (prW (chEt c φ) (opEt Uo)).left ≫ Spec.map φ

end Assembly

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UK2b =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UK2b): the `d`-th root of `1 + t e` on the pieces over an etale `B → B'`

`D = Spec B` etale over `P` (through `hB`), `X R : P.Etale`, `W := (D ×_P X) ×_P R`; `wD : W ⟶ D`,
`bW : B ⟶ Γ(W)`, `bK p : B →+* Frac(Γ(W) ⧸ p)`.
* `wm_wD`: `wm (prdMap d X) ≫ wD D X = wD D₁ X ≫ d.left`;
* `uk_root'`: O2UK1 `uk_root` with an explicit ring map `ι : B ⟶ B'` (`Spec ι` etale);
* **`exists_pow_of_uk`**: for `D₁ ⟶ Spec B'` and a piece `p₁` of `W₁ := (D₁ ×_P X) ×_P R`, every `Ψ` compatible with
  `wm (prdMap d X)` sends `1 + t e` (`e` a root of `g` over `B`) to a `d`-th power.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.GenGeo

universe u

section WD

variable {P : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
theorem wm_wD {D₁ D : P.Etale} (d : D₁ ⟶ D) (X R : P.Etale) :
    wm (R := R) (prdMap d X) ≫ wD D X R = wD D₁ X R ≫ d.left := by
  unfold wD
  rw [← Category.assoc, wm_snd, Category.assoc, Category.assoc]
  exact congrArg (fun t => pullback.snd R.hom (prd D₁ X).hom ≫ t) (pullback.lift_fst _ _ _)

end WD

section Ring

variable {P : Scheme.{u}} {B : CommRingCat.{u}} (hB : Spec B ⟶ P) [Etale hB] (X R : P.Etale)

/-- `B →+* Frac(Γ(W) ⧸ p)`. -/
def bK (p : minimalPrimes Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤)) :
    B →+* FractionRing (Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤) ⧸ p.1) :=
  (algebraMap _ _).comp ((Ideal.Quotient.mk p.1).comp (bW hB X R).hom)

variable {B' : CommRingCat.{u}} (ι : B ⟶ B') [Etale (Spec.map ι)]

variable {D₁ : P.Etale} (d₁ : D₁ ⟶ Scheme.Etale.mk (Spec.map ι ≫ hB))

/-- `B' →+* Frac(Γ(W₁) ⧸ p₁)`. -/
def bK₁ (p₁ : minimalPrimes Γ(((etPull (prd D₁ X).hom).obj R).left, ⊤)) : B' →+* FractionRing (Γ(((etPull (prd D₁ X).hom).obj R).left, ⊤) ⧸ p₁.1) :=
  (algebraMap _ _).comp ((Ideal.Quotient.mk p₁.1).comp (bW₁ hB X R ι d₁).hom)

end Ring

section UK

end UK

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Pb =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Pb): the pullback square of `wm (prdMap d X)` and what it gives on global sections

GLOB/REL PLAN v1 (2). For `d : D₁ ⟶ D` and `X R : P.Etale`, `W := (D ×_P X) ×_P R`, `W₁ := (D₁ ×_P X) ×_P R`:
* `isPullback_wm`, `isPullback_prdMap`, **`isPullback_wD`**: `W₁ = D₁ ×_D W` (through `wm (prdMap d X)`, `wD`);
* `mem_closure_of_isPushout`, `mem_adjoin_of_isPushout`: in a pushout of rings the two legs generate;
* **`appTop_mem_closure`** (Gen): `Γ(W₁)` is generated by the images of `Γ(W)` and `Γ(D₁)` (all affine);
* `isPushout_bW`: for `D = Spec B`, `D₁ = Spec B'`, `d.left = Spec.map ι`, the square `bW, ι, wm^*, bW'` is a
  pushout of rings;
* **`isLocalization_away_wm`** (Zar): for `B' = B_f`, `Γ(W) → Γ(W₁)` is `IsLocalization.Away (bW f)`;
  `comap_injective_wm`: so `Ideal.comap` along it is injective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.GenGeo

universe u

section Ring

end Ring

section Pb

variable {P : Scheme.{u}} (R : P.Etale)

/-- `T₁ ×_P R = T₁ ×_{T₂} (T₂ ×_P R)`. -/
theorem isPullback_wm {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) :
    IsPullback (wm (R := R) m) (pullback.snd R.hom T₁.hom) (pullback.snd R.hom T₂.hom) m.left :=
  IsPullback.of_right
    (by rw [wm_fst, MorphismProperty.Over.w m]; exact IsPullback.of_hasPullback R.hom T₁.hom)
    (wm_snd (R := R) m) (IsPullback.of_hasPullback R.hom T₂.hom)

end Pb

end RamanujanPetersson.EtPBC.EtKum

end

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

instance isOpenImmersion_chEt_locF (g : k[X]) :
    IsOpenImmersion (chEt c (locF (B := CommRingCat.of k[X]) g)).hom :=
  show IsOpenImmersion (Spec.map (locF (B := CommRingCat.of k[X]) g) ≫ c) from inferInstance

end Dg

section Sec

variable {P : Scheme.{u}}

/-- The section `opEt U ⟶ D ×_P U` of an open immersion `D` whose range contains `U`. -/
def secD (D : P.Etale) [IsOpenImmersion D.hom] (U : P.Opens) (hU : ∀ x ∈ U, x ∈ Set.range D.hom) :
    opEt U ⟶ prd D (opEt U) :=
  MorphismProperty.Over.homMk
    (pullback.lift (IsOpenImmersion.lift D.hom (opEt U).hom (by
        rintro _ ⟨v, rfl⟩
        exact hU _ (by
          show (U.ι ≫ 𝟙 P) v ∈ U
          rw [Category.comp_id]
          exact opnι_mem (etId P) U v))) (𝟙 _) ((IsOpenImmersion.lift_fac _ _ _).trans (Category.id_comp _).symm))
    ((pullback.lift_snd_assoc _ _ _ _).trans (Category.id_comp _))

end Sec

end RamanujanPetersson.EtPBC.EtDeg

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
theorem left_spec_map : dm.left ≫ Spec.map φ = Spec.map φ₁ := by
  rw [← cancel_mono c, Category.assoc]
  exact MorphismProperty.Over.w dm

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

variable {P : Scheme.{0}}

/-- Maps into `D ×_P X` are determined by `prT` when `D ⟶ P` is an open immersion. -/
theorem eq_of_prT {D X Z : P.Etale} [IsOpenImmersion D.hom] (f g : Z ⟶ prd D X)
    (hfg : f ≫ prT D X = g ≫ prT D X) : f = g :=
  MorphismProperty.Over.Hom.ext ((cancel_mono (pullback.snd D.hom X.hom)).1 (congrArg (fun q => q.left) hfg))

end Mono

section ChG

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {g₀ G : k[X]} (hG₀ : g₀ ∣ G)

theorem isUnit_locF_of_dvd {r : k[X]} (hr : r ∣ G) : IsUnit ((locF (B := CommRingCat.of k[X]) G).hom r) :=
  isUnit_of_dvd_unit (map_dvd (algebraMap k[X] (Localization.Away G)) hr) (IsLocalization.Away.algebraMap_isUnit G)

end ChG

section Sec

end Sec

section Gam

end Gam

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2f =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2f): the side conditions of stages S3-S4

* `mem_opnDg_prd` (`hD₂`): `D₂ ×_P U₀` lies over `c(D(g₀ c₀' t))` when `g₀, c₀'` are units on `D₂`;
* `not_isUnit_t`: `t = X - a` is not a unit on a chart with a point over `z = c(a)`;
* `etale_wD`, `injective_bW_piece`: for a domain `B`, `B ↪ Frac(Γ(W) ⧸ q)` on every piece (flatness), the `hinj` of
  `one_sub_mul_ne_zero` (O2Gl2c).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Cech

section Pts

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {a : k} {Uo Uz : P.Opens}
  (h : Uo ≤ Uz) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a))

theorem eq_A1pt_of_mem {q : A1 k} (ht : X - C a ∈ q.asIdeal) : q = A1pt k a := by
  apply PrimeSpectrum.ext
  have hm : (Ideal.span {X - C a} : Ideal k[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)
  exact (hm.eq_of_le q.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ht)).symm

/-- `t = X - a` is not a unit on a chart with a point over `z`. -/
theorem not_isUnit_t {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
    (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ))) : ¬ IsUnit (φ.hom (X - C a)) := by
  obtain ⟨a'⟩ := hDn
  let w : Spec B := fpt (c (A1pt k a)) a'
  have hw : (chEt c φ).hom w = c (A1pt k a) := fib_over (c (A1pt k a)) a'
  have h2 : Spec.map φ w = A1pt k a := c.isOpenEmbedding.injective hw
  have h3 : X - C a ∈ (Spec.map φ w).asIdeal := by
    rw [h2]; exact Ideal.mem_span_singleton_self _
  exact fun hu => w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.1 h3) hu)

end Pts

section Inj

variable {P : Scheme.{0}}

instance etale_wD (D X R : P.Etale) : Etale (wD D X R) := by
  have h1 : Etale ((etPull (prd D X).hom).obj R).hom := ((etPull (prd D X).hom).obj R).prop
  have : Etale X.hom := X.prop
  have h2 : Etale (pullback.fst D.hom X.hom) := inferInstance
  unfold wD
  exact @Etale.etale_comp _ _ _ _ _ h1 h2

end Inj

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2k =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2k): stage S4 with `H` and `D₂ := (D₁)_{φ₁ c₀'}` fixed

GLOB/REL PLAN v1, stage S4. From the S2-S3 output (`y ∣ c₀ = t^{e₀} c₀'`, `hy`, `hz`) and `G := g₀ c₀' t`:
* **`isUnit_locF_of_dvd_pow`**, **`dvd_G_pow`**: `c₀` and `t` are units of `k[X]_G`;
* **`exists_S4H`**: a unit `H` on `Y_G` with `H ρ(t)^N = ρ(y)` (`isUnit_rho`, `exists_Hg`) and the `e`, `g`, `he`, `hHp`, `hHq`
  of `uk_diff` on `D₂ = chEt c (φ₁ ≫ locF (φ₁ c₀'))` with `d₂₁ = toDF` (`exists_S4`, `isLocalization_away_toDF`).
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

section Units

variable {k : Type} [Field k]

/-- A divisor of a power of `G` is a unit of `k[X]_G`. -/
theorem isUnit_locF_of_dvd_pow {G r : k[X]} {n : ℕ} (h : r ∣ G ^ n) :
    IsUnit ((locF (B := CommRingCat.of k[X]) G).hom r) := by
  have h1 : IsUnit ((locF (B := CommRingCat.of k[X]) G).hom G) := IsLocalization.Away.algebraMap_isUnit G
  have h2 : IsUnit ((locF (B := CommRingCat.of k[X]) G).hom (G ^ n)) := by
    rw [map_pow]
    exact h1.pow n
  exact isUnit_of_dvd_unit (map_dvd _ h) h2

end Units

section ToDF

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (f : B)

theorem toDF_left : (toDF c φ f).left = Spec.map (locF f) := rfl

end ToDF

section S4H

end S4H

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl3a =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3a): chart facts for the `uk_diff` call on `D₂`

* **`not_mem_fpt_of_eval_ne_zero`**: `g(a) ≠ 0` ⇒ `φ g` is not in the prime of a fibre point over `c(a)`
  (so `D₂ := (D₁)_{φ₁ c₀'}` keeps the point over `z`: `nonempty_fib_toDF`);
* **`wm_mG_sXW`**: `m^*` carries the root of unity `sXW` on `Y_G` to the one on `W₂` (`hs` of `uk_diff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Cech

section Pts3

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {a : k}

theorem not_mem_fpt_of_eval_ne_zero {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]
    (n : (geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)) {g : k[X]} (hg : g.eval a ≠ 0) :
    φ.hom g ∉ (fpt (c (A1pt k a)) n).asIdeal := by
  intro hm
  have hw : (chEt c φ).hom (fpt (c (A1pt k a)) n) = c (A1pt k a) := fib_over (c (A1pt k a)) n
  have h2 : Spec.map φ (fpt (c (A1pt k a)) n) = A1pt k a := c.isOpenEmbedding.injective hw
  have h3 : g ∈ (Spec.map φ (fpt (c (A1pt k a)) n)).asIdeal := Ideal.mem_comap.2 hm
  rw [h2] at h3
  exact hg (Polynomial.dvd_iff_isRoot.1 (Ideal.mem_span_singleton.1 h3))

end Pts3

section SXW

end SXW

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl3b =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3b): the point over `z` on a chart (inputs `χ`, `hχ`, `ht`, `hd` of `uk_diff`)

For a chart `chEt c φ` with a fibre point `n` over `z = c(a)`:
* **`fpt_mem_t`**: `φ (X - C a)` lies in the prime of `n`;
* **`exists_chi`**: the residue map `χ : B → κ(n)` with `χ(φ t) = 0` and `(chEt c φ).hom ⟨ker χ⟩ = z`;
* **`isUnit_natCast_of_prim`**: `d ∣ N`, `ζ0 ∈ k` a primitive `N`-th root ⇒ `d` is a unit of `B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Cech

section ZPt

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {a : k}
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]

theorem fpt_mem_t (n : (geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)) :
    φ.hom (X - C a) ∈ (fpt (c (A1pt k a)) n).asIdeal := by
  have hw : (chEt c φ).hom (fpt (c (A1pt k a)) n) = c (A1pt k a) := fib_over (c (A1pt k a)) n
  have h2 : Spec.map φ (fpt (c (A1pt k a)) n) = A1pt k a := c.isOpenEmbedding.injective hw
  have h3 : X - C a ∈ (Spec.map φ (fpt (c (A1pt k a)) n)).asIdeal := by
    rw [h2]; exact Ideal.mem_span_singleton_self _
  exact Ideal.mem_comap.1 h3

end ZPt

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T5 =====
section

/-!
# S4-EtPBC-A, O2 S5e: splitting off finitely many disjoint sections

* `secLiftOI g σ h`: a section `σ` of `N` lifted through an open immersion `g : R ⟶ N` containing its range;
* **`clsD_splitAll`**: for sections `σ i` (`i ∈ S`, a finset) of a separated etale `N` over `D = Spec B` with
  pairwise disjoint ranges, `clsD f Y` is a sum of section summands `clsD (Λ[σ i] ≫ f) Y'` plus one residual
  summand `clsD (Λ[g] ≫ f) Y_R` through an open immersion `g : R ⟶ N` missing every range `σ i`, `i ∈ S`;
  `R` is affine when `N` is (`isAffine_opn_secV`: section ranges are clopen).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

section LiftOI

end LiftOI

section Aff

variable {X : Scheme.{u}}

/-- The range of a section of an etale object is open. -/
theorem isOpen_range_section {R : X.Etale} (τ : etId X ⟶ R) : IsOpen (Set.range τ.left) := by
  have : Etale R.hom := R.prop
  have hw : τ.left ≫ R.hom = 𝟙 X := MorphismProperty.Over.w τ
  have : Etale (τ.left ≫ R.hom) := by rw [hw]; exact (etId X).prop
  have : Etale τ.left := Etale.of_comp τ.left R.hom
  exact τ.left.isOpenMap.isOpen_range

/-- Removing the (clopen) range of a section keeps an affine etale object affine. -/
theorem isAffine_opn_secV {R : X.Etale} [IsSeparated R.hom] (τ : etId X ⟶ R) [IsAffine R.left] :
    IsAffine (opn R (secV τ)).left := by
  have hj : IsClosed (Set.range (secV τ).ι) := by
    rw [Scheme.Opens.range_ι]
    exact (isOpen_range_section τ).isClosed_compl
  have h : IsAffine (secV τ).toScheme := isAffine_of_isClosed_range (secV τ).ι hj
  exact h

end Aff

section SplitAll

end SplitAll

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T6 =====
section

/-!
# S4-EtPBC-A, O2 S5f: geometry of graphs of sections

For `m : W ⟶ T` in `P.Etale`, `graph m : etId W.left ⟶ (etPull W.hom).obj T` (lib O2T1):
* `graph_fst`, `graph_snd`, `graph_left_eq_sec` (it is EGeoB's `sec m`), **`graph_cover`** (points over `fpt d`
  lie on graphs of sections through every fibre point);
* `graphMeet m m'` (where the graphs meet), closed for separated `T`; `graph_meet_eq`, **`not_mem_graphMeet`**
  (graphs of sections through different fibre points do not meet at `fpt d`), `disjoint_graph`;
* `pullMap d`, **`graph_natural`**, **`graphMeet_natural`** (meeting loci pull back along `d : W' ⟶ W`);
* `eq_fpt_of_over`: `fpt d` is the only point over `z` when the fibre over `z` is a singleton.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

section GraphGeo

variable {P : Scheme.{u}} {W' W T : P.Etale}

/-- `fpt d` is the only point over `z` when the fibre over `z` is a singleton. -/
theorem eq_fpt_of_over {z : P} {D : P.Etale} (hD : Subsingleton ((geomPtAt z).point.fiber.obj D))
    (d : (geomPtAt z).point.fiber.obj D) (v : D.left) (hv : D.hom v = z) : v = fpt z d := by
  subst hv
  obtain ⟨a, ha⟩ := exists_fib_over D v
  rw [← Subsingleton.elim a d, ha]

end GraphGeo

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T9b =====
section

/-!
# S4-EtPBC-A, O2 S6a (O2T9b): the residual of a one-point class is a one-point class with EMPTY fibre

* `PtCls Λ c hN hΛ T x`: `x = pcD c' ∘ Λ[s]` for an affine Dedekind presentation `Spec B` of a point `c (X = a)`;
* **`isLoc_free_res`**: a one-point class `β` at `z = c (X = a)` with coefficients `Λ[T]` (`T` separated, finite fibre)
  is `β' ∘ Λ[r]` modulo point classes, `r : R ⟶ T`, `β'` a one-point class at `z` for `Λ[R]` and `R` with EMPTY fibre
  over `z`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtDed

section PtCls

end PtCls

section Emp

/-- No point of `etComp e R` lies over `z` if no point of `R` maps to `z`. -/
theorem isEmpty_fib_etComp {X Y : Scheme.{0}} (e : Y ⟶ X) [Etale e] (R : Y.Etale) (z : X)
    (h : ∀ r : R.left, e (R.hom r) ≠ z) : IsEmpty ((geomPtAt z).point.fiber.obj ((etComp e).obj R)) := by
  refine ⟨fun d => h (fpt z d) ?_⟩
  have h1 := fib_over z d
  have h2 : ((etComp e).obj R).hom = R.hom ≫ e := rfl
  rw [h2] at h1
  exact h1

end Emp

section Res

end Res

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd4): bad-point data with NO chart map to `D_{g₀}`; `exists_S4H'`

s128 fix of REL PLAN v2: a bad point `c(b)` has `g₀(b) = 0` (`c(D(g₀)) ⊆ U₀ ∪ {z}`), so no chart `D' ∋ b` maps to
`D_{g₀}`. The map `W(D') → Y₀` is `m^* ∘ ρ` instead (`m := mG : D' ×_P U₀ ⟶ D_G ×_P U₀`, `ρ := (prdMap (toDG c hG₀))^*`):
* **`wD_hom`**, **`shG_wm_any`**: `wm m ≫ shG φ₁ = shG φ₂` for ANY `m : D₂ ×_P U₀ ⟶ D₁ ×_P U₀` between chart products;
* **`mG_rho_gamMap`**, **`mG_H_any`**: `m^* (ρ r) = bW'(φ' r)`; the `H`-relation pulled back along `m`;
* **`exists_bad_e'`**: `exists_bad_e` (O2Bd2) without `d : D' ⟶ D_{g₀}`;
* **`exists_S4H'`**: `exists_S4H` (O2Gl2k) for a generic `G` (`hG₀ : g₀ ∣ G`), also returning `H ρ(t)^N = ρ(y)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section WDHom

variable {P : Scheme.{0}}

set_option backward.isDefEq.respectTransparency false in
theorem wD_hom (D X R : P.Etale) :
    wD D X R ≫ D.hom = pullback.snd R.hom (prd D X).hom ≫ (prd D X).hom := by
  unfold wD
  rw [Category.assoc, pullback.condition]
  rfl

end WDHom

section AnyM

end AnyM

section BadChart'

end BadChart'

section S4H'

end S4H'

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel5 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel5): the relation over all points outside a cofinite open

REL PLAN v2 (s126), file R3, index plumbing. For a cofinite open `U₀` whose outside points are closed, the points
`x ∉ U₀`, `x ≠ z₀` form a finite index type with relation nbhds `opEt (U₀ ∪ {x})` and opens `{x}ᶜ`:
* **`mem_opEt_hom`**: `(opEt U).hom v ∈ U`;
* **`term_mem_cofinite`**: the term at `z₀` lies in `G` when every point `x ∉ U₀`, `x ≠ z₀` is good or its term
  (for ANY open `V = U₀ ∪ {x}`) is `0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo

universe u

variable {Λ : Type u} [CommRing Λ] {P : Scheme.{u}} (U₀ : P.Opens)

theorem mem_opEt_hom (U : P.Opens) (v : (opEt U).left) : (opEt U).hom v ∈ U := by
  show (U.ι ≫ 𝟙 P) _ ∈ U
  rw [Category.comp_id]
  exact opnι_mem (etId P) U _

end RamanujanPetersson.EtPBC.EtMV

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

theorem hpt_of_ne_zero {G : k[X]} (hG0 : G ≠ 0) (hpt : ∀ y : A1 k, y.asIdeal ≠ ⊥ → ∃ b, y = A1pt k b) :
    ∀ y : A1 k, G ∈ y.asIdeal → ∃ b, y = A1pt k b := fun y hy => hpt y fun hb => by
  rw [hb] at hy
  exact hG0 (Ideal.mem_bot.1 hy)

theorem isUnit_locF_self {B : CommRingCat.{0}} (f : B) : IsUnit ((locF f).hom f) :=
  IsLocalization.Away.algebraMap_isUnit f

theorem hzU_of (h : Uo ≤ Uz) (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a)) : c (A1pt k a) ∉ Uo :=
  fun hm => (hz _).1 (h hm) rfl

/-- A chart with a fibre point is nonempty, so its ring is nontrivial. -/
theorem nontrivial_of_fpt {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (f : B)
    {x : P} (n : (geomPtAt x).point.fiber.obj (chEt c (φ ≫ locF f))) : Nontrivial (Localization.Away f) := by
  have w : PrimeSpectrum (Localization.Away f) := fpt x n
  exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨w⟩

end Helpers

section PPG

end PPG

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

end HJ'

section ChartS1

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {Uo : P.Opens} (R : P.Etale) [IsAffine R.left] {a : k}

theorem isUnit_locF_comp_of_dvd {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) {F r : k[X]} (hr : r ∣ F) :
    IsUnit ((φ ≫ locF (φ.hom F)).hom r) := by
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  exact isUnit_of_dvd_unit (map_dvd _ (map_dvd φ.hom hr)) (IsLocalization.Away.algebraMap_isUnit (φ.hom F))

end ChartS1

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP5a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`

* `prdTo`, `prdMapR_prdTo`: for `D` over `U₁ ∪ {z}` and `z ∉ U₀ ⊇ U₁`, `D ×_P U₀ ⟶ D ×_P U₁` splits `prdMapR`;
* `locCls_up`: `ε(D, U₁)∘κ = ε(D, U₀)∘Λ[prdTo]∘κ`;
* **`isLoc_chart`**: an `IsLoc` class at `z = c(a)` is `ε(chEt c φ, U₀)∘κ` for a chart `φ` with `B` a domain,
  given `g₀(a) ≠ 0` and `D_{g₀} ⊆ U₀ ∪ {z}` (`isLoc_aff_map`, shrink to `D_{φ g₀}`, `locCls_opn`, `locCls_up`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtDeg

universe u

section Up

variable {P : Scheme.{u}}

theorem hom_mem_of_map {X : P.Etale} {U : P.Opens} (f : X ⟶ opEt U) (v : X.left) : X.hom v ∈ U := by
  have hw : X.hom v = U.ι (f.left v) :=
    (congrArg (fun g : X.left ⟶ P => g v) (opEt_left_comp f)).symm.trans (Scheme.Hom.comp_apply _ _ _)
  rw [hw]
  exact opnι_mem (etId P) U (f.left v)

theorem prd_mem_of (D : P.Etale) {U₀ U₁ : P.Opens} {z : P} (hDr : ∀ v : D.left, D.hom v ∈ U₁ ∨ D.hom v = z)
    (hzU : z ∉ U₀) : ∀ v : (prd D (opEt U₀)).left, (prd D (opEt U₀)).hom v ∈ U₁ := fun v => by
  have hw : (prd D (opEt U₀)).hom v = D.hom ((prW D (opEt U₀)).left v) :=
    (congrArg (fun f : (prd D (opEt U₀)).left ⟶ P => f v) (MorphismProperty.Over.w (prW D (opEt U₀)))).symm.trans
      (Scheme.Hom.comp_apply _ _ _)
  have hU := hom_mem_of_map (prT D (opEt U₀)) v
  rcases hDr ((prW D (opEt U₀)).left v) with h | h
  · rw [hw]
    exact h
  · rw [hw, h] at hU
    exact absurd hU hzU

theorem prd_ext {Z D X : P.Etale} (f g : Z ⟶ prd D X) (h1 : f ≫ prW D X = g ≫ prW D X)
    (h2 : f ≫ prT D X = g ≫ prT D X) : f = g :=
  MorphismProperty.Over.Hom.ext (pullback.hom_ext (congrArg (fun t => t.left) h1) (congrArg (fun t => t.left) h2))

variable (D : P.Etale) {U₀ U₁ : P.Opens} (hD : ∀ v : (prd D (opEt U₀)).left, (prd D (opEt U₀)).hom v ∈ U₁)

/-- `D ×_P U₀ ⟶ D ×_P U₁` when `D ×_P U₀` lies over `U₁`. -/
def prdTo : prd D (opEt U₀) ⟶ prd D (opEt U₁) :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst D.hom (opEt U₀).hom) (toOpEt (prd D (opEt U₀)) U₁ hD).left
      (pullback.condition.trans (MorphismProperty.Over.w (toOpEt (prd D (opEt U₀)) U₁ hD)).symm))
    ((pullback.lift_snd_assoc _ _ _ _).trans (MorphismProperty.Over.w (toOpEt (prd D (opEt U₀)) U₁ hD)))

theorem prdTo_prW : prdTo D hD ≫ prW D (opEt U₁) = prW D (opEt U₀) :=
  MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)

theorem prdMapR_prdTo (h₁₀ : U₁ ≤ U₀) : prdMapR D (opEtMap h₁₀) ≫ prdTo D hD = 𝟙 (prd D (opEt U₁)) :=
  prd_ext _ _ (by rw [Category.assoc, prdTo_prW, prdMapR_prW, Category.id_comp]) (opEt_ext _ _)

end Up

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Mob =====
section

/-!
# S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity

* `mobA c`: the shear `X₀ ↦ X₀ + c X₁`, `X₁ ↦ X₁`; `mobG c` the graded ring hom; `mobP c := Proj.map (mobG c)`,
  an isomorphism of `P¹` with inverse `mobP (-c)`.
* **`chartM c := chartA1 ≫ mobP c`**: an open immersion `A¹ ⟶ P¹` whose range is `P¹ ∖ {mobP c ∞}`
  (`mem_range_chartM`); `c ↦ mobP c ∞` is injective (`mobP_infPt_injective`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

section Mob

variable {K : Type} [Field K]

theorem irr_le_comap_mobG (c : K) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K)).comap (mobG c) :=
  (HomogeneousIdeal.irrelevant_le _).2 fun _ hi _ hx =>
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi ((mobG c).map_mem hx)

end Mob

end RamanujanPetersson.EtCompact

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

open Classical in
variable (Λ) in
/-- The point of `B` over `c` in case 2. -/
def mvG (c : C) : B →₀ Λ :=
  if h : ¬ MVG1 p₂ w v c ∧ ∃ b, v b = c then Finsupp.single (Classical.choose h.2) 1 else 0

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

theorem etPull_sq : ((etPull f).obj W).hom ≫ f = fW f W ≫ W.hom := by
  rw [etPull_obj_hom]
  exact pullback.condition.symm

variable (Λ) in
/-- The composite `(f^*G)|_V ⟶ f_V^*(G|_W)` for an etale `X`-scheme `V` with `f_V : V ⟶ W` over `f`. -/
def tauAppG (V : X.Etale) (fV : V.left ⟶ W.left) (sq : V.hom ≫ f = fV ≫ W.hom) (G : EtSh Λ Y) :
    (res V.hom Λ).obj ((pull f Λ).obj G) ⟶ (pull fV Λ).obj ((res W.hom Λ).obj G) :=
  (pullIsoRes V.hom Λ).inv.app ((pull f Λ).obj G) ≫ pullCompInv Λ V.hom f G ≫ (pullCongr Λ sq).hom.app G ≫
    pullCompHom Λ fV W.hom G ≫ (pull fV Λ).map ((pullIsoRes W.hom Λ).hom.app G)

theorem appN5f {X : Scheme.{u}} {F0 F1 F2 F3 F4 F5 : EtSh Λ X} (a1 : F0 ⟶ F1) (a2 : F1 ⟶ F2) (a3 : F2 ⟶ F3)
    (a4 : F3 ⟶ F4) (a5 : F4 ⟶ F5) {V : X.Etaleᵒᵖ} {s0 : F0.obj.obj V} {s1 : F1.obj.obj V} {s2 : F2.obj.obj V}
    {s3 : F3.obj.obj V} {s4 : F4.obj.obj V} {s5 : F5.obj.obj V}
    (h1 : (a1.hom.app V).hom s0 = s1) (h2 : (a2.hom.app V).hom s1 = s2) (h3 : (a3.hom.app V).hom s2 = s3)
    (h4 : (a4.hom.app V).hom s3 = s4) (h5 : (a5.hom.app V).hom s4 = s5) (t : F0 ⟶ F5)
    (ht : a1 ≫ a2 ≫ a3 ≫ a4 ≫ a5 = t) : (t.hom.app V).hom s0 = s5 := by
  subst ht h1 h2 h3 h4 h5
  rfl

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

instance pull_pfc_TB3 {X Y : Scheme.{u}} (g : X ⟶ Y) : PreservesFiniteColimits (pull g Λ) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

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

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {Φ Φ' : C ⥤ D} [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [Φ'.Additive] [PreservesFiniteLimits Φ'] [PreservesFiniteColimits Φ']

theorem mapExact_iso_aux (τ : Φ ≅ Φ') {S : ShortComplex C} (hS : S.ShortExact) {A : C} (c : A ⟶ S.X₃) :
    (((Ext.mk₀ c).comp hS.extClass (zero_add 1)).mapExactFunctor Φ).comp (Ext.mk₀ (τ.hom.app S.X₁)) (add_zero 1) =
      (Ext.mk₀ (τ.hom.app A)).comp (((Ext.mk₀ c).comp hS.extClass (zero_add 1)).mapExactFunctor Φ')
        (zero_add 1) := by
  let f : S.map Φ ⟶ S.map Φ' :=
    { τ₁ := τ.hom.app S.X₁, τ₂ := τ.hom.app S.X₂, τ₃ := τ.hom.app S.X₃
      comm₁₂ := (τ.hom.naturality S.f).symm
      comm₂₃ := (τ.hom.naturality S.g).symm }
  have hn := ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact Φ) (hS.map_of_exact Φ') f
  have hc : Φ.map c ≫ τ.hom.app _ = τ.hom.app A ≫ Φ'.map c := τ.hom.naturality c
  refine (congrArg (fun x => Ext.comp x (Ext.mk₀ (τ.hom.app S.X₁)) (add_zero 1))
    (mapExact_comp_extClass (Φ' := Φ) hS c)).trans ?_
  refine (Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by norm_num)).trans ?_
  refine (congrArg (fun x => Ext.comp (Ext.mk₀ (Φ.map c)) x (zero_add 1)) hn).trans ?_
  refine (Ext.mk₀_comp_mk₀_assoc _ _ _).trans ?_
  refine (congrArg (fun g => Ext.comp (Ext.mk₀ g) (hS.map_of_exact Φ').extClass (zero_add 1)) hc).trans ?_
  refine (Ext.mk₀_comp_mk₀_assoc _ _ _).symm.trans ?_
  exact congrArg (fun x => Ext.comp (Ext.mk₀ (τ.hom.app A)) x (zero_add 1)) (mapExact_comp_extClass hS c).symm

/-- **Isomorphic exact functors act alike on `Ext¹`.** -/
theorem mapExact_iso [EnoughInjectives C] (τ : Φ ≅ Φ') {A B : C} (ξ : Ext.{w} A B 1) :
    (ξ.mapExactFunctor Φ).comp (Ext.mk₀ (τ.hom.app B)) (add_zero 1) =
      (Ext.mk₀ (τ.hom.app A)).comp (ξ.mapExactFunctor Φ') (zero_add 1) := by
  obtain ⟨γ, rfl⟩ := Ext.covariant_sequence_exact₁ (X := A) (hS := injPres_shortExact B) ξ
    (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨c, rfl⟩ := (Ext.mk₀_bijective _ _).2 γ
  exact mapExact_iso_aux τ (injPres_shortExact B) c

theorem conjE_of_iso [EnoughInjectives C] (τ : Φ ≅ Φ') {A B : C} (ξ : Ext.{w} A B 1) :
    ξ.mapExactFunctor Φ' = conjE (ξ.mapExactFunctor Φ) (τ.inv.app A) (τ.hom.app B) := by
  unfold conjE
  rw [mapExact_iso τ ξ, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_app, Ext.mk₀_id_comp]

end IsoGen

universe u

section PullX

variable {Λ : Type u} [CommRing Λ]

theorem sec_nat {X : Scheme.{u}} {F G : EtSh Λ X} (φ : F ⟶ G) {V V' : X.Etale} (r : V' ⟶ V)
    (x : F.obj.obj (op V)) :
    (φ.hom.app (op V')).hom ((F.obj.map r.op).hom x) = (G.obj.map r.op).hom ((φ.hom.app (op V)).hom x) :=
  congrArg (fun ψ => ψ.hom x) (φ.hom.naturality r.op)

theorem sec_map_comp {X : Scheme.{u}} (F : EtSh Λ X) {V V' V'' : X.Etale} (r : V' ⟶ V) (r' : V'' ⟶ V')
    (x : F.obj.obj (op V)) :
    (F.obj.map r'.op).hom ((F.obj.map r.op).hom x) = (F.obj.map (r' ≫ r).op).hom x := by
  rw [op_comp, Functor.map_comp]
  rfl

end PullX

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

/-- `W ×_P S`. -/
abbrev Vs : S.Etale := (etPull i).obj W

/-- `(W ×_P S) ×_S P`. -/
abbrev Zs : P.Etale := (etPull g).obj (Vs i W)

variable {i g} (hig : i ≫ g = 𝟙 S)

/-- `v ↦ (v, i v)`. -/
def jz : (Vs i W).left ⟶ pullback (Vs i W).hom g :=
  pullback.lift (𝟙 _) ((Vs i W).hom ≫ i) ((Category.id_comp _).trans
    (((Category.comp_id _).symm.trans (whisker_eq _ hig.symm)).trans (Category.assoc _ _ _).symm))

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7a =====
section

/-!
# S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
* `Delta.bcImg`: the germ image `{β | ∃ j α, bc j α = β}` is an additive subgroup (cofiltered `J`);
* `etPullId`: `etPull (𝟙 X) ≅ 𝟭`; `pushId`: `push (𝟙 X) ≅ 𝟭`; `pushEquiv e` for an isomorphism `e`;
* **`pull_isEquivalence`**: `e^*` is an equivalence for an isomorphism `e`;
* **`pull_ext_bijective`**: `e^*` is bijective on `Ext^n`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

section L7a

variable {Λ : Type u} [CommRing Λ]

variable (Λ) in
/-- Equal morphisms have isomorphic pushforward functors. -/
def pushCongr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') : push f Λ ≅ push f' Λ :=
  eqToIso (by rw [h])

end L7a

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

end CompSub

section Chart

variable {k : Type} [Field k]

theorem chart_ne_genPt (c : A1 k ⟶ P1 k) [IsOpenImmersion c] (b : k) : c (A1pt k b) ≠ P1.genPt k := by
  intro h
  have h1 : A1pt k b = GenBr.genPt k[X] := c.isOpenEmbedding.injective (h.trans (map_genPt k k[X] c).symm)
  have h2 : Ideal.span {X - C b} = (⊥ : Ideal k[X]) := congrArg PrimeSpectrum.asIdeal h1
  exact X_sub_C_ne_zero b (Ideal.span_singleton_eq_bot.1 h2)

theorem chart_hclA (c : A1 k ⟶ P1 k) [IsOpenImmersion c] (b : k) : IsClosed ({c (A1pt k b)} : Set (P1 k)) :=
  P1.isClosed_of_ne_genPt k _ (chart_ne_genPt c b)

theorem chart_hGal [IsAlgClosed k] (c : A1 k ⟶ P1 k) [IsOpenImmersion c] (b : k) :
    Subsingleton (Gal (c (A1pt k b))) :=
  P1.gal_closed k _ (chart_hclA c b)

end Chart

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

/-- A morphism into a pullback etale object from a morphism over `f`. -/
def toPull : T' ⟶ (etPull f).obj Y' :=
  MorphismProperty.Over.homMk (pullback.lift m T'.hom hm) (pullback.lift_snd _ _ _)

end ToPull

section Fib

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)]

variable (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale)

/-- `z = c a`. -/
abbrev zc : P1 K := c (A1pt K a)

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

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (W : Y.Etale) {D : X.Etale} (s' : D ⟶ (etPull f).obj W)

theorem pullPt_sq : (s'.left ≫ pullback.fst W.hom f) ≫ W.hom = D.hom ≫ f :=
  (Category.assoc _ _ _).trans ((whisker_eq s'.left pullback.condition).trans
    ((Category.assoc _ _ _).symm.trans (eq_whisker (MorphismProperty.Over.w s') f)))

end Sq

section Pt

variable {K : Type} [Field K] [IsAlgClosed K] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K)
  {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)]

/-- The point `X = a` of `D = chEt c φ`. -/
def d₀ (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) : (chEt c φ).left :=
  (⟨Ideal.span {φ.hom (X - C a)}, hP⟩ : PrimeSpectrum B)

end Pt

section Fib

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L6b3 =====
section

/-!
# S4-EtPBC-A, L6b3: the morphism of MV data `locC(D♭) ⟶ ιP^* MVZ` on `P¹_K`

`a' : D♭ ×_P Uz' ⟶ ιP^* DzO`, `a : D♭ ⟶ ιP^* Dz`, `b : Uz' ⟶ ιP^*(Zz ×_P Uz)`, `c := σP`, with the four squares
`h₁ .. h₄` (all proved on underlying scheme maps through `toPull`), and **`mvTheta_Db`**:
`Λ[σP] ∘ (ιP^*MVZ-class of κ, r) = (locC D♭-class of a'^*κ, a ≫ r)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Polynomial Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

section Mor

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gS)] (c : A1 K ⟶ P1 K) [IsOpenImmersion c] (a : K) (W : (PV K gS).Etale) {B : CommRingCat.{0}} (φ : CommRingCat.of K[X] ⟶ B) [Etale (Spec.map φ ≫ c)] [IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) (Uz' : (P1 K).Opens) (hUz' : ∀ x : P1 K, x ∈ Uz' ↔ x ≠ zc c a)

theorem prW_left' {P : Scheme.{0}} (W T : P.Etale) : (prW W T).left = pullback.fst W.hom T.hom := rfl

theorem opEtMap_refl_left : (opEtMap (le_refl Uz')).left = 𝟙 _ :=
  (cancel_mono (Uz'.ι ≫ 𝟙 (P1 K))).mp ((MorphismProperty.Over.w (opEtMap (le_refl Uz'))).trans
    (Category.id_comp _).symm)

end Mor

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_FibP1 =====
section

/-!
# S4-EtPBC-A, G0: the fibre of a `P¹`-bundle at a rational point, and base change in degrees `≥ 4`

* `nbhdTop s`: the trivial etale neighbourhood `(S, s)`;
* `bcSurj_of_subsingleton`: base change is surjective on germs when the target `H^q(P_s, ι^* G)` is trivial;
* for `g = pullback.snd : P¹_K ×_K S ⟶ S` and a geometric point `s` with `s.pt ≫ gS` an isomorphism (a `K`-rational
  point, `K = K̄`): **`fibToP1`** `: P_s ⟶ P¹_K` is an isomorphism, `fibH` transports `H^q`, and
  **`p1Bundle_bcSurj_add_four`**: base change is surjective on germs in degrees `q + 4` for every sheaf.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

universe u

section Gen

variable {Λ : Type u} [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- The trivial etale neighbourhood `(S, s)` of `s`. -/
def nbhdTop : Nbhd s := s.point.fiber.elementsMk (etId S) s.top

end Gen

section P1Bundle

variable (K : Type u) [Field K] {S : Scheme.{u}} (gS : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S)

/-- The fibre of `P¹_K ×_K S ⟶ S` at `s`, mapped to `P¹_K`. -/
def fibToP1 : fib (pullback.snd (P1.toSpecK K) gS) s ⟶ P1 K :=
  fibι (pullback.snd (P1.toSpecK K) gS) s ≫ pullback.fst (P1.toSpecK K) gS

theorem fibToP1_eq :
    fibToP1 K gS s = (pullbackLeftPullbackSndIso (P1.toSpecK K) gS s.pt).hom ≫ pullback.fst _ _ :=
  (pullbackLeftPullbackSndIso_hom_fst (P1.toSpecK K) gS s.pt).symm

instance fibToP1_isIso [IsIso (s.pt ≫ gS)] : IsIso (fibToP1 K gS s) := by
  rw [fibToP1_eq]
  infer_instance

end P1Bundle

section P1Vanish

end P1Vanish

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7b1 =====
section

/-!
# S4-EtPBC-A, O2 L7b1: the transport `Tr` from `P¹_K` to the fibre `P_s`
For a `K`-rational geometric point `s` (`[IsIso (s.pt ≫ gS)]`), `e := fibToP1 : P_s ⟶ P¹_K` is an isomorphism with
`e ≫ ιP = ι` (`fibToP1_ιP`). Base change identifications `isoE X : e^*ιP^*X ⟶ ι^*X` (natural, invertible),
the section `σG` of `ιP^*(qV^*V)` through a `K`-point `v'` of `V`, the neighbourhood `jG = (V, v')` of `s`, and
**`nbhdSec_eq`**: `nbhdSec jG = c₀ ≫ e^*σG ≫ isoE`. **`TrE`**: `Ext²(Λ[P¹], Λ[ιP^*R]) → Ext²(Λ_{P_s}, ι^*Λ[R])`,
`x ↦ u ∘ e^*x ∘ v`; **`TrE_surjective`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe u

section Gen

variable {X Y : Scheme.{u}}

@[reassoc]
theorem etIdPull_hom_fst (g : X ⟶ Y) : (etIdPull g).hom.left ≫ pullback.fst (etId Y).hom g = g :=
  pullback.lift_fst _ _ _

end Gen

section GenSurj

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w} C}
  {D : Type u₂} [Category.{v₂} D] [Abelian D] {hD : HasExt.{w} D}

/-- `x ↦ u ∘ F x ∘ v` is surjective when `F` is surjective on `Ext` and `u`, `v` are isomorphisms. -/
theorem surj_conj_gen (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A B : C} {A' B' : D} (n : ℕ)
    (hF : Function.Surjective (fun x : Ext.{w} A B n => x.mapExactFunctor F))
    (u : A' ⟶ F.obj A) [IsIso u] (v : F.obj B ⟶ B') [IsIso v] :
    Function.Surjective (fun x : Ext.{w} A B n =>
      (Ext.mk₀ u).comp ((x.mapExactFunctor F).comp (Ext.mk₀ v) (add_zero n)) (zero_add n)) := by
  intro β
  obtain ⟨x, hx⟩ := hF ((Ext.mk₀ (inv u)).comp (β.comp (Ext.mk₀ (inv v)) (add_zero n)) (zero_add n))
  refine ⟨x, ?_⟩
  have hx' : x.mapExactFunctor F =
      (Ext.mk₀ (inv u)).comp (β.comp (Ext.mk₀ (inv v)) (add_zero n)) (zero_add n) := hx
  simp only [hx', Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc, IsIso.hom_inv_id,
    IsIso.inv_hom_id, Ext.comp_mk₀_id, Ext.mk₀_id_comp]

end GenSurj

section Fib

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O1G1 =====
section

/-!
# S4-EtPBC-A, O1 glue: **degree-1 base change on `P¹_S`**

* `coverLiftAt₂_ft`: `CoverLiftAt₂` for a finite-type algebra over a perfect field (Artin approximation `artinApproxAt`
  fed into `coverLiftAt₂_of_approx`);
* `liftT_qV`: the lifting property `LiftT (qV K gK) s π` for every finite `π : Y ⟶ P¹_S`, from an affine noetherian
  etale neighbourhood of `s`;
* **`bcSurj_one_PV`**: `BCSurj 1` for every sheaf on `P¹_S` at a geometric point `s` with `s ≫ g_K` an isomorphism
  (`S` noetherian, locally of finite type over a perfect field `K`, `Λ` finite noetherian).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

/-- The `K`-algebra of sections of an affine scheme locally of finite type over `K` is of finite type. -/
theorem finiteType_algKV (K : Type u) [Field K] {V : Scheme.{u}} [IsAffine V] (gV : V ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType gV] : @Algebra.FiniteType K Γ(V, ⊤) _ _ (algKV K gV) := by
  change RingHom.FiniteType (gV.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  exact RingHom.FiniteType.comp (HasRingHomProperty.appTop @LocallyOfFiniteType gV inferInstance)
    (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)

end RamanujanPetersson.EtPBC.Cov

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.Cov

universe u

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7b2 =====
section

/-!
# S4-EtPBC-A, O2 L7b2: transport of family MV-theta classes
**`TrE_mvTheta`**: for an MV square over `qV^*V` on `P = P¹_K ×_K S` and a `K`-point `v'` of `V` over `s`, the
transport `TrE` of the `P¹_K`-class `Λ[σG] ∘ ιP^*(ε ∘ θ(p₁, κ) ∘ Λ[r])` is the base change at `jG = (V, v')` of the
family class `ε ∘ θ(p₁, κ) ∘ Λ[r]`. Proof: `mvThetaR_pull` along `e`, `bc_mvThetaR` at `jG`, and `mvTheta_map` along
the base change identifications `isoE` (`nbhdSec_eq`, `isoE_natural`, `isoE_left_fW`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE

universe w v₀ u₀

/-- Pull the last degree-zero factor out of an MV-theta class. -/
theorem cls_tail {C : Type u₀} [Category.{v₀} C] [Abelian C] [HasExt.{w} C] {A B D E F : C}
    (ε : Ext.{w} A B 1) (θ : Ext.{w} B D 1) (f : D ⟶ E) (g : E ⟶ F) :
    ε.comp (θ.comp (Ext.mk₀ (f ≫ g)) (add_zero 1)) (show 1 + 1 = 2 from rfl) =
      (ε.comp (θ.comp (Ext.mk₀ f) (add_zero 1)) (show 1 + 1 = 2 from rfl)).comp (Ext.mk₀ g) (add_zero 2) := by
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero θ, ← Ext.comp_assoc_of_third_deg_zero ε]

section GenTr

universe w' v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w'} C}
  {D : Type u₂} [Category.{v₂} D] [Abelian D] {hD : HasExt.{w'} D}

theorem trE_head_gen (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A X0 Z : C} {A' W Z' : D} (u : A' ⟶ F.obj A) (σ : A ⟶ X0) (x : Ext.{w'} X0 Z 2) (v : F.obj Z ⟶ Z')
    (u0 : A' ⟶ W) (p : W ⟶ F.obj X0) (h : u ≫ F.map σ = u0 ≫ p) :
    (Ext.mk₀ u).comp ((((Ext.mk₀ σ).comp x (zero_add 2)).mapExactFunctor F).comp (Ext.mk₀ v) (add_zero 2))
        (zero_add 2) =
      (Ext.mk₀ u0).comp (((Ext.mk₀ p).comp (x.mapExactFunctor F) (zero_add 2)).comp (Ext.mk₀ v) (add_zero 2))
        (zero_add 2) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀_assoc, h, ← Ext.mk₀_comp_mk₀_assoc, ← Ext.comp_assoc_of_third_deg_zero]

end GenTr

section TrMV

end TrMV

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L8b =====
section

/-!
# S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
* `TrG_surjective`, **`TrG_natural`** (`TrG G (x ∘ ιP^*m) = TrG H x ∘ ι^*m`);
* **`bcSurj_two_fgt`**: `BCSurj 2` for every `FGT` sheaf on `P¹_S` (`surjAt_coprod`, `bcSurj_two_free`, `bcSurj_two_of_epi`);
* `NT`, **`kill_lift`**: for `T` affine over `P¹_K`, every `κ ∈ Ext¹(Λ[T], ιP^*G)` is `κH ∘ ιP^*m` with `m : H ⟶ G`,
  `H` an `FGT` sheaf (`exists_kill` on `T`, `extFree_comp_mk₀`, the covariant exact sequence).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section GenSurjG

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w} C}
  {D : Type u₂} [Category.{v₂} D] [Abelian D] {hD : HasExt.{w} D}

/-- `x ↦ u ∘ F x ∘ v` is surjective when `F` is surjective on `Ext` and `u`, `v` are isomorphisms. -/
theorem surj_conj_genG (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A B : C} {A' B' : D} (n : ℕ)
    (hF : Function.Surjective (fun x : Ext.{w} A B n => x.mapExactFunctor F))
    (u : A' ⟶ F.obj A) [IsIso u] (v : F.obj B ⟶ B') [IsIso v] :
    Function.Surjective (fun x : Ext.{w} A B n =>
      (Ext.mk₀ u).comp ((x.mapExactFunctor F).comp (Ext.mk₀ v) (add_zero n)) (zero_add n)) := by
  intro β
  obtain ⟨x, hx⟩ := hF ((Ext.mk₀ (inv u)).comp (β.comp (Ext.mk₀ (inv v)) (add_zero n)) (zero_add n))
  refine ⟨x, ?_⟩
  have hx' : x.mapExactFunctor F =
      (Ext.mk₀ (inv u)).comp (β.comp (Ext.mk₀ (inv v)) (add_zero n)) (zero_add n) := hx
  simp only [hx', Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc, IsIso.hom_inv_id,
    IsIso.inv_hom_id, Ext.comp_mk₀_id, Ext.mk₀_id_comp]

end GenSurjG

section TrG

end TrG

end RamanujanPetersson.EtPBC.EtMV

end

end


