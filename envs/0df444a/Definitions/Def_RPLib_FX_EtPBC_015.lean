-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_015
-- name    : RPLib_FX_EtPBC_015
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T18:42:04.380485+00:00
-- url     : https://prove2.me/theorems/ea57deb8-1042-5c0f-af3a-9f0b0a68ad85
-- title:
--   Proper base change for the projective line, library file 015
-- statement:
--   File 015 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_PtSec`: S4-EtCompact, E7 (O9c-2): global sections of sheaves supported on finitely many closed points
--   * `S4.Def_RP_EtPBC_A_CovAs2`: S4-EtPBC-A, R4-T2 (A3 assembly, As2): the level-0 cover over generic charts, and the fibre kernel
--   * `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
--   * `S4.Def_RP_EtPBC_A_CovLim2`: S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level
--   * `S4.Def_RP_EtPBC_A_LocFlat`: S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)
--   * `S4.Def_RP_EtPBC_A_CovAsN2`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables
--   * `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
--   * `S4.Def_RP_EtPBC_A_CovAs5a`: S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra
--   * `S4.Def_RP_EtPBC_A_CovAs5b`: S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`
--   * `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_Z4Glue`: S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`
--   * `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
--   * `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
--   * `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_CovFbC`: S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover
--   * `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
--   * `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
--   * `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
--   * `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
--   * `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
--   * `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
--   * `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
--   * `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
--   * `S4.Def_RP_EtPBC_A_DeltaK`: S4-EtPBC-A, R4-T3a: one class killed by a monomorphism comes from a germ
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--   * `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
--   * `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
--   * `S4.Def_RP_EtPBC_A_CovNbA`: S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed
--   * `S4.Def_RP_EtPBC_A_NagA`: S4-EtPBC-A, M4(N1): integral closures over a finite type domain over a perfect field (integrally closed case)
--   * `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
--   * `S4.Def_RP_EtPBC_A_O2M4b`: S4-EtPBC-A, O2 (MV route), M4 (b): every class of `H²(P¹, F)` is a Mayer-Vietoris class
--   * `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
--   * `S4.Def_RP_EtPBC_A_O2E3`: S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes
--   * `S4.Def_RP_EtPBC_A_O2Th1b`: S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)
--   * `S4.Def_RP_EtPBC_A_O2UK1`: S4-EtPBC-A, O2 M6 (O2UK1): `1 + t e` is a `d`-th power over an etale neighbourhood (ring level)
--   * `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
--   * `S4.Def_RP_EtPBC_A_O2Pb`: S4-EtPBC-A, O2 GLOB (O2Pb): the pullback square of `wm (prdMap d X)` and what it gives on global sections
--   * `S4.Def_RP_EtPBC_A_O2Gl1c`: S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2
--   * `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
--   * `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
--   * `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
--   * `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
--   * `S4.Def_RP_EtPBC_A_O2TB1`: S4-EtPBC-A, L3a (TB1): pulled-back sections
--   * `S4.Def_RP_EtPBC_A_O2L5a`: S4-EtPBC-A, L5a (Geo1): the horizontal section through a closed point of `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_30
import Definitions.Def_RPLib_FX_EtPBC_005
import Definitions.Def_RPLib_FX_EtPBC_006
import Definitions.Def_RPLib_FX_EtPBC_007
import Definitions.Def_RPLib_FX_EtPBC_009
import Definitions.Def_RPLib_FX_EtPBC_010
import Definitions.Def_RPLib_FX_EtPBC_011
import Definitions.Def_RPLib_FX_EtPBC_012

/-!
# Proper base change for the projective line, library file 015

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_PtSec`: S4-EtCompact, E7 (O9c-2): global sections of sheaves supported on finitely many closed points
* `S4.Def_RP_EtPBC_A_CovAs2`: S4-EtPBC-A, R4-T2 (A3 assembly, As2): the level-0 cover over generic charts, and the fibre kernel
* `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
* `S4.Def_RP_EtPBC_A_CovLim2`: S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level
* `S4.Def_RP_EtPBC_A_LocFlat`: S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)
* `S4.Def_RP_EtPBC_A_CovAsN2`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables
* `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
* `S4.Def_RP_EtPBC_A_CovAs5a`: S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra
* `S4.Def_RP_EtPBC_A_CovAs5b`: S4-EtPBC-A, R4-T2 (A3 assembly, As5b): monic families and base change along `φ` at the level of `C`
* `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_Z4Glue`: S4-EtPBC-A, (Z) geometric layer 9 (G-e, part 1): gluing the two charts of `Y`
* `S4.Def_RP_EtPBC_A_Z4Base`: S4-EtPBC-A, (Z) geometric layer 10 (G-e, part 2): the idempotent on `Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
* `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
* `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_CovFbC`: S4-EtPBC-A, R4-T2 (G1d, part 3): the chart identity and the pullback square of the fibre cover
* `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
* `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
* `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
* `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
* `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
* `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
* `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
* `S4.Def_RP_EtPBC_A_LshEt`: S4-EtPBC-A, T3b: `e_!` preserves monomorphisms for every etale `e`
* `S4.Def_RP_EtPBC_A_DeltaK`: S4-EtPBC-A, R4-T3a: one class killed by a monomorphism comes from a germ
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
* `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
* `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
* `S4.Def_RP_EtPBC_A_CovNbA`: S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed
* `S4.Def_RP_EtPBC_A_NagA`: S4-EtPBC-A, M4(N1): integral closures over a finite type domain over a perfect field (integrally closed case)
* `S4.Def_RP_EtPBC_A_O2D3`: S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`
* `S4.Def_RP_EtPBC_A_O2M4b`: S4-EtPBC-A, O2 (MV route), M4 (b): every class of `H²(P¹, F)` is a Mayer-Vietoris class
* `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
* `S4.Def_RP_EtPBC_A_O2E3`: S4-EtPBC-A, O2 C-plan S4c1 (scheme level): affine Dedekind presentations of one-point classes
* `S4.Def_RP_EtPBC_A_O2Th1b`: S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)
* `S4.Def_RP_EtPBC_A_O2UK1`: S4-EtPBC-A, O2 M6 (O2UK1): `1 + t e` is a `d`-th power over an etale neighbourhood (ring level)
* `S4.Def_RP_EtPi1_FunA`: S4-EtPi1, O8 (part 1): unramified extensions stay unramified under base change
* `S4.Def_RP_EtPBC_A_O2Pb`: S4-EtPBC-A, O2 GLOB (O2Pb): the pullback square of `wm (prdMap d X)` and what it gives on global sections
* `S4.Def_RP_EtPBC_A_O2Gl1c`: S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2
* `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
* `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
* `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
* `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
* `S4.Def_RP_EtPBC_A_O2TB1`: S4-EtPBC-A, L3a (TB1): pulled-back sections
* `S4.Def_RP_EtPBC_A_O2L5a`: S4-EtPBC-A, L5a (Geo1): the horizontal section through a closed point of `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_PtSec =====
section

/-!
# S4-EtCompact, E7 (O9c-2): global sections of sheaves supported on finitely many closed points

`Y` locally noetherian and quasi-compact, `S` a finite set of closed points with trivial `Gal`, `Q` with zero stalks
off `S`:
* `h0Pt Q S : H^0(Y, Q) → ∏_{s ∈ S} Q_s̄` (the stalk values `α_s̄(1)`); `h0Pt_injective`;
* `sc_homEquiv`: `c(1)` over the terminal object is the adjunct of `c`; `h0Eval_ofSec`: the map attached to a global
  section `q` has stalk value the germ of `q`;
* **`h0Pt_surjective`** (sections with prescribed germs, `Cech.exists_ux_eq`), **`h0PtEquiv`**;
* on `P¹`: **`P1.h0BdEquiv`**: `H^0(P¹, Q) ≃ ∏_{s ∉ U} Q_s̄` for the boundary sheaf `Q = coker(j_! G → j_* G)` of a
  nonempty open `j : U ⟶ P¹` with finite complement `S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.PtSec

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact Cech Supp

universe u

end RamanujanPetersson.EtCompact.PtSec

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact PtSec

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

instance P1.compactSpace : CompactSpace (P1 k) := QuasiCompact.compactSpace_of_compactSpace (P1.toSpecK k)

end RamanujanPetersson.EtCompact.CurveHn

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As2): the level-0 cover over generic charts, and the fibre kernel

* `eqvG J β hs hk : B ⧸ J ^ (0 + 1) ≃+* F` for `β` surjective with `ker β = J` (`eqvG_mk`), `eqvG_comm`;
* **`baseG`**: a fibre cover `Eᵢ` over `Fᵢ` gives a level-0 two-chart cover `LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0`
  (CovL4 `base` with generic ideals);
* **`ker_kap`**: for `χ` surjective and `ker βQ = (ker χ) B`, `ker kap = (ker χ') (R' ⊗ B)`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section EqvG

end EqvG

section BaseG

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] (φ₀ : B₀ →+* N) (φ₁ : B₁ →+* N)
  (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN) (t₀ : B₀) (t₁ : B₁)
  {F₀ F₁ F₀₁ : Type u} [CommRing F₀] [CommRing F₁] [CommRing F₀₁]
  (β₀ : B₀ →+* F₀) (β₁ : B₁ →+* F₁) (β₀₁ : N →+* F₀₁)
  (hβs₀ : Function.Surjective β₀) (hβs₁ : Function.Surjective β₁) (hβs₀₁ : Function.Surjective β₀₁)
  (hk₀ : RingHom.ker β₀ = J₀) (hk₁ : RingHom.ker β₁ = J₁) (hk₀₁ : RingHom.ker β₀₁ = JN)
  (φb₀ : F₀ →+* F₀₁) (φb₁ : F₁ →+* F₀₁)

/-- **The fibre cover at level `0`** over generic charts. -/
def baseG (hρ₀ : φb₀.comp β₀ = β₀₁.comp φ₀) (hρ₁ : φb₁.comp β₁ = β₀₁.comp φ₁)
    (E₀ E₁ E₀₁ : Type u) [CommRing E₀] [CommRing E₁] [CommRing E₀₁] [Algebra F₀ E₀] [Algebra F₁ E₁]
    [Algebra F₀₁ E₀₁] (het₀ : Algebra.Etale F₀ E₀) (het₁ : Algebra.Etale F₁ E₁) (hf₀ : Module.Finite F₀ E₀)
    (hf₁ : Module.Finite F₁ E₁) (ψ₀ : E₀ →+* E₀₁) (ψ₁ : E₁ →+* E₀₁)
    (hψ₀ : ψ₀.comp (algebraMap F₀ E₀) = (algebraMap F₀₁ E₀₁).comp φb₀)
    (hψ₁ : ψ₁.comp (algebraMap F₁ E₁) = (algebraMap F₀₁ E₀₁).comp φb₁)
    (aw₀ : IsAwayMap ψ₀ (algebraMap F₀ E₀ (β₀ t₀)))
    (aw₁ : IsAwayMap ψ₁ (algebraMap F₁ E₁ (β₁ t₁))) : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0 where
  E₀ := CommRingCat.of E₀
  E₁ := CommRingCat.of E₁
  E := CommRingCat.of E₀₁
  a₀ := (algebraMap F₀ E₀).comp (eqvG J₀ β₀ hβs₀ hk₀).toRingHom
  a₁ := (algebraMap F₁ E₁).comp (eqvG J₁ β₁ hβs₁ hk₁).toRingHom
  a := (algebraMap F₀₁ E₀₁).comp (eqvG JN β₀₁ hβs₀₁ hk₀₁).toRingHom
  et₀ := RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (eqvG J₀ β₀ hβs₀ hk₀).bijective)
    (RingHom.etale_algebraMap.2 het₀)
  et₁ := RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective (eqvG J₁ β₁ hβs₁ hk₁).bijective)
    (RingHom.etale_algebraMap.2 het₁)
  fin₀ := RingHom.Finite.comp (RingHom.finite_algebraMap.2 hf₀) (eqvG J₀ β₀ hβs₀ hk₀).finite
  fin₁ := RingHom.Finite.comp (RingHom.finite_algebraMap.2 hf₁) (eqvG J₁ β₁ hβs₁ hk₁).finite
  ψ₀ := ψ₀
  ψ₁ := ψ₁
  hψ₀ := by
    rw [← RingHom.comp_assoc, hψ₀, RingHom.comp_assoc,
      eqvG_comm φ₀ J₀ JN h₀ β₀ β₀₁ hβs₀ hβs₀₁ hk₀ hk₀₁ φb₀ hρ₀, ← RingHom.comp_assoc]
  hψ₁ := by
    rw [← RingHom.comp_assoc, hψ₁, RingHom.comp_assoc,
      eqvG_comm φ₁ J₁ JN h₁ β₁ β₀₁ hβs₁ hβs₀₁ hk₁ hk₀₁ φb₁ hρ₁, ← RingHom.comp_assoc]
  aw₀ := by
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      eqvG_mk]
    exact aw₀
  aw₁ := by
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      eqvG_mk]
    exact aw₁

end BaseG

section KerKap

variable {K A R' B Q : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Q] (χ : A →+* K) (ν : K →+* Q) (βQ : B →+* Q) (hβ : ∀ a, βQ (algebraMap A B a) = ν (χ a))
  (χ' : R' →+* K) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a)

/-- **The fibre kernel**: `ker kap = (ker χ') (R' ⊗ B)` when `χ` is surjective and `ker βQ = (ker χ) B`. -/
theorem ker_kap (hχs : Function.Surjective χ) (hk : RingHom.ker βQ = (RingHom.ker χ).map (algebraMap A B)) :
    RingHom.ker (kap χ ν βQ hβ χ' hχ') = Jt B χ' := by
  refine le_antisymm (fun z hz => ?_) (fun a ha => RingHom.mem_ker.mpr (Jt_le_ker_kap χ ν βQ hβ χ' hχ' a ha))
  obtain ⟨b, hb⟩ := exists_one_tmul χ χ' hχ' hχs z
  have h0 := Jt_le_ker_kap χ ν βQ hβ χ' hχ' _ hb
  rw [map_sub, RingHom.mem_ker.mp hz, zero_sub, neg_eq_zero, kap_tmul, map_one, map_one, one_mul] at h0
  have hbJ : (1 : R') ⊗ₜ[A] b ∈ Jt B χ' := by
    apply one_tmul_mem_Jt χ χ' hχ'
    rw [← hk]
    exact RingHom.mem_ker.mpr h0
  have e : z = (z - (1 : R') ⊗ₜ[A] b) + (1 : R') ⊗ₜ[A] b := by ring
  rw [e]
  exact add_mem hb hbJ

end KerKap

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovG2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions

For a two-chart cover `C` with ring maps `ιᵢ : R → Eᵢ` (agreeing on the overlap) and an ideal `I` of the overlap:
* **`TwoCov.Good C ι₀ I m y e`**: `E₀` is generated over `R[t]` by `m` modulo `ψ₀⁻¹ I`, and `ψ₀ mᵢ ≡ u^{eᵢ} ψ₁ yᵢ`
  modulo `I` (transition exponents `eᵢ`);
* **`TwoCov.h1_mod`**: then `H¹(O(d)) = 0` modulo `I` for `d ≥ max eᵢ`;
* **`TwoCov.good_zero`**: `Good` holds (any `I`, `I = ⊥` included) when `E₀` is finite over `R[t]`;
* **`TwoCovHom.good_lift`**: `Good` lifts along a transition with the SAME exponents (so `d` is uniform);
* **`TwoCovHom.hker_of_h1`**, **`TwoCovHom.secMap_surj_of_h1`**: `H¹ = 0` modulo `I'` and a kernel generated by
  `q` with `q · I' = 0` give the kernel hypothesis of `secMap_surj`: sections lift.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Good

variable {b₀ b₁ n : Type u} [CommRing b₀] [CommRing b₁] [CommRing n] {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n}
  {τ₀ : b₀} {τ₁ : b₁} (C : TwoCov φb₀ φb₁ τ₀ τ₁) {R : Type u} [CommRing R] (ι₀ : R →+* C.E₀) (I : Ideal C.E)

variable {C I} {d : ℕ}

variable (ι₁ : R →+* C.E₁) (hι : C.ψ₀.comp ι₀ = C.ψ₁.comp ι₁)
include hι

omit hι in
theorem TwoCov.PI_t (hv : C.u * C.ψ₁ (C.a₁ τ₁) = 1) {x : C.E₀} (h : C.PI I d x) :
    C.PI I d (C.a₀ τ₀ * x) := by
  intro k
  cases k with
  | zero =>
    refine ⟨C.a₀ τ₀ * x, 0, ?_⟩
    simp only [pow_zero, one_mul, map_zero, mul_zero, sub_zero, sub_self]
    exact I.zero_mem
  | succ k =>
    obtain ⟨x₀, x₁, hx⟩ := h k
    refine ⟨x₀, x₁, ?_⟩
    have e : C.ψ₁ (C.a₁ τ₁) ^ (k + 1) * C.ψ₀ (C.a₀ τ₀ * x) = C.ψ₁ (C.a₁ τ₁) ^ k * C.ψ₀ x := by
      rw [map_mul]
      change C.ψ₁ (C.a₁ τ₁) ^ (k + 1) * (C.u * C.ψ₀ x) = _
      linear_combination (C.ψ₁ (C.a₁ τ₁) ^ k * C.ψ₀ x) * hv
    rw [e]
    exact hx

end Good

section Zero

variable {b₀ b₁ n : Type u} [CommRing b₀] [CommRing b₁] [CommRing n] {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n}
  {τ₀ : b₀} {τ₁ : b₁} (C : TwoCov φb₀ φb₁ τ₀ τ₁) {R : Type u} [CommRing R] (ι₀ : R →+* C.E₀) (I : Ideal C.E)

/-- **Generators exist** when `E₀` is finite over `R[t]` (via `ι₀` and `t = a₀ τ₀`). -/
theorem TwoCov.good_zero (hv : C.u * C.ψ₁ (C.a₁ τ₁) = 1) (hfin : (eval₂RingHom ι₀ (C.a₀ τ₀)).Finite) :
    ∃ (r : ℕ) (m : Fin r → C.E₀) (y : Fin r → C.E₁) (e : Fin r → ℕ), C.Good ι₀ I m y e := by
  letI := (eval₂RingHom ι₀ (C.a₀ τ₀)).toAlgebra
  haveI : Module.Finite R[X] C.E₀ := hfin
  obtain ⟨r, m, hm⟩ := Module.Finite.exists_fin (R := R[X]) (M := C.E₀)
  have hy : ∀ i, ∃ (k : ℕ) (b : C.E₁), C.ψ₀ (m i) = C.u ^ k * C.ψ₁ b := by
    intro i
    obtain ⟨k, b, hb⟩ := C.aw₁.1 (C.ψ₀ (m i))
    refine ⟨k, b, ?_⟩
    rw [← hb]
    have hp : (C.u * C.ψ₁ (C.a₁ τ₁)) ^ k = 1 := by rw [hv, one_pow]
    linear_combination (-C.ψ₀ (m i)) * hp
  choose e y hey using hy
  refine ⟨r, m, y, e, fun x => ?_, fun i => ?_⟩
  · have hx : x ∈ Submodule.span R[X] (Set.range m) := by rw [hm]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R[X]).1 hx
    refine ⟨c, ?_⟩
    have e2 : ∑ i, eval₂ ι₀ (C.a₀ τ₀) (c i) * m i = x := by
      rw [← hc]
      rfl
    rw [e2, sub_self, map_zero]
    exact I.zero_mem
  · rw [hey i, sub_self]
    exact I.zero_mem

end Zero

section Lift

end Lift

section Ker

end Ker

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level

For families `σ : Fin r → (∀ k, E₀ k) × (∀ k, E₁ k)`:
* **`lev C ιB₀ ιB₁ σ m c`** `= ∑ cᵢ σᵢ` at level `m`; `lev_fst`, `lev_snd`, `lev_add`, `lev_sub`, `lev_zero`, `lev_comb`;
* `lev_mem`: it is a section of `O(d)` when the `σᵢ` are in `Gam`; `lev_ρ₀`, `lev_ρ₁`: compatibility;
* `lev_congr`: coefficients congruent modulo `p^(m+1)` give the same level-`m` combination;
* **`levF`**, `levF_mem`: the family of all levels lies in `Gam`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lev

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (p : Ideal R) {r : ℕ} (σ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁))

theorem lev_fst (m : ℕ) (c : Fin r → R) :
    (lev C ιB₀ ιB₁ σ m c).1 = ∑ i, lι₀ ιB₀ (C m) (c i) * (σ i).1 m := by
  simp only [lev, Prod.fst_sum]

end Lev

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

/-- Linear independence over a local ring from the residue criterion, for a flat module. -/
theorem lf_li_flat {R N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup N] [Module R N] [Module.Flat R N]
    {ι : Type*} (v : ι → N)
    (h : ∀ (s : Finset ι) (c : ι → R), ∑ i ∈ s, c i • v i ∈ (maximalIdeal R) • (⊤ : Submodule R N) →
      ∀ i ∈ s, c i ∈ maximalIdeal R) :
    LinearIndependent R v :=
  Module.IsLocalRing.linearIndependent_of_flat v (lf_li_res v h)

end LocFlat

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAsN2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables

`Xid σ A = span (range X)`.
* `one_le_order_of_mem_Xid`, `le_order_of_mem_pow`, `coeff_zero_of_mem_Xid_pow`: `F ∈ Xid ^ m` kills coefficients of
  total degree `< m`.
* `mem_Xid_pow_of_coeff` (`σ` finite): the converse (decomposition `F = ∑ X i * G i`).
* `smod_Xid_iff`, **`isPrecomplete_Xid`**: `IsPrecomplete (Xid σ A) (MvPowerSeries σ A)`.
-/

set_option autoImplicit false

open MvPowerSeries

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u v

section HatN2

variable {A : Type u} [CommRing A] {σ : Type v}

theorem le_order_of_mem_pow : ∀ (m : ℕ) {F : MvPowerSeries σ A}, F ∈ (Xid σ A) ^ m → (m : ℕ∞) ≤ F.order
  | 0, F, _ => by simp
  | m + 1, F, hF => by
    rw [pow_succ] at hF
    refine Submodule.mul_induction_on hF (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · calc ((m + 1 : ℕ) : ℕ∞) = (m : ℕ∞) + ((1 : ℕ) : ℕ∞) := by push_cast; rfl
        _ ≤ x.order + y.order := add_le_add (le_order_of_mem_pow m hx) (one_le_order_of_mem_Xid hy)
        _ ≤ (x * y).order := le_order_mul
    · exact le_trans (le_min hx hy) min_order_le_add

theorem coeff_zero_of_mem_Xid_pow {m : ℕ} {F : MvPowerSeries σ A} (hF : F ∈ (Xid σ A) ^ m)
    (x : σ →₀ ℕ) (hx : x.degree < m) : coeff x F = 0 :=
  coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hx) (le_order_of_mem_pow m hF))

end HatN2

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

variable {P P' E' : Type u} [CommRing P] [CommRing P'] [CommRing E'] {r : ℕ}
  (f : P →+* P') (g : Fin r → MvPolynomial (Fin r) P) (bN : P' →+* E') (θ : Pres g →+* E')

theorem presN_algebraMap (hθ : θ.comp (algebraMap P (Pres g)) = bN.comp f) (a : P') :
    presN f g bN θ hθ (algebraMap P' (Pres (gmap f g)) a) = bN a :=
  presLift_algebraMap _ _ _ _ a

end PresN

section Subst

end Subst

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs5a =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As5a): lifting polynomials and memberships to a f.g. subalgebra

For a flat `A`-algebra `S` and an `A`-algebra `B`, with `tvC B C : C ⊗ B → S ⊗ B` and, for `C ≤ D`,
`tiC B h : C ⊗ B → D ⊗ B`:
* `exists_lift_polys`: finitely many polynomials over `S ⊗ B` come from one f.g. `C`;
* `exists_lift_monic`: a monic polynomial over `S ⊗ B` comes from a monic one over `C ⊗ B`;
* **`desc_mem`**: finitely many ideal memberships `x_k ∈ (g)` over `S ⊗ B` already hold over `C ⊗ B` for a f.g.
  `C ≥ C₀` (cofactors lifted by `exists_lift_polys`, the identities descended by `desc_mvPoly`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section Lift

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]

variable {B : Type u} [CommRing B] [Algebra A B]

theorem tvC_tiC {C D : Subalgebra A S} (h : C ≤ D) (x : C ⊗[A] B) : tvC B D (tiC B h x) = tvC B C x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    first
      | rfl
      | simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem tiC_tiC {C D E : Subalgebra A S} (h : C ≤ D) (h' : D ≤ E) (x : C ⊗[A] B) :
    tiC B h' (tiC B h x) = tiC B (h.trans h') x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    first
      | rfl
      | simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

end Lift

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

end LiftB

section BC

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  {B N : Type u} [CommRing B] [Algebra A B] [CommRing N] [Algebra A N] (φ : B →ₐ[A] N)

theorem tiC_bcC {C D : Subalgebra A S} (h : C ≤ D) (x : C ⊗[A] B) :
    tiC N h (bcC φ C x) = bcC φ D (tiC B h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    first
      | rfl
      | simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end BC

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Y =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`

For `π : Y ⟶ P¹_V` (`V` affine):
* `isAffineOpen_Qc`, `isAffineOpen_Yc`: the charts `Qᵢ` of `P¹_V` and `Yᵢ = π⁻¹ Qᵢ` are affine;
* `σY i j : Γ(V)[X] → Γ(Y, Yᵢ)` (`X ↦ π^*(Xⱼ/Xᵢ)`), **`finite_σY`** (`π` finite);
* `pull_res` (restriction commutes with pullback), **`basicOpen_tY`**, **`basicOpen_sY`**: `D(t) = D(s) = Y₀ ⊓ Y₁`;
* **`trans_Y`**: `t|_{Y₀₁} · s|_{Y₀₁} = 1`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization
open RamanujanPetersson.EtCompact

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K))

theorem isAffineOpen_Qc [IsAffine V] (i : Fin 2) : IsAffineOpen (Qc K gV i) := by
  have := isAffine_Wc K gV i
  rw [← image_jW, Scheme.Hom.image_top_eq_opensRange]
  exact isAffineOpen_opensRange _

variable {Y : Scheme.{u}} (π : Y ⟶ PV K gV)

/-- `Γ(V)[X] → Γ(Y, Yᵢ)`, `X ↦ π^*(Xⱼ/Xᵢ)`. -/
abbrev σY (i j : Fin 2) : Polynomial Γ(V, ⊤) →+* Γ(Y, Yc K gV π i) :=
  (π.app (Qc K gV i)).hom.comp (Polynomial.eval₂RingHom (ac K gV i).hom (tc K gV i j))

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Alg =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`

`A = Γ(V)`, `B₀ = Γ(Y, Y₀)`, `B₁ = Γ(Y, Y₁)`, `N = Γ(Y, Y₀ ⊓ Y₁)`:
* `A[X]`-structures `algX0` (via `t`), `algX1` (via `s`), `algXN` (via `t`); `A`-structures `algA0`, `algA1`, `algAN`
  (structure maps of `Y ⟶ V`); towers `tow0`, `tow1`, `towN`; `res_struct`.
* `φY0 : B₀ →ₐ[A[X]] N`, `φY1 : B₁ →ₐ[A] N` (restrictions); `hts_Y`, `hs0_Y`, `hs1_Y`, `hz0_Y`, `hz1_Y`.
* **`exists_etale_idem_Y`**: chart elements idempotent mod `p` and agreeing mod `p` on the overlap come from an
  idempotent of `R' ⊗_A secAlg φY0 φY1` after an etale `R'` with a prime over `p` with the same residue field.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace HomogeneousLocalization
open RamanujanPetersson.EtCompact
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

/-- Restriction `Γ(Y₀) → Γ(Y₀₁)`. -/
abbrev resY0 : Γ(Y, Yc K gV π 0) ⟶ Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) :=
  Y.presheaf.map (homOfLE inf_le_left : Yc K gV π 0 ⊓ Yc K gV π 1 ⟶ Yc K gV π 0).op

end RamanujanPetersson.EtPBC.Z3

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

theorem Yc_sup : Yc K gV π 0 ⊔ Yc K gV π 1 = ⊤ := by
  show π ⁻¹ᵁ (pr K gV ⁻¹ᵁ chU K 0) ⊔ π ⁻¹ᵁ (pr K gV ⁻¹ᵁ chU K 1) = ⊤
  rw [← Scheme.Hom.preimage_sup, ← Scheme.Hom.preimage_sup, chU_sup]
  rfl

theorem struct_res (i : Fin 2) :
    ac K gV i ≫ π.app (Qc K gV i) = (π ≫ qV K gV).appTop ≫ Y.presheaf.map (homOfLE le_top : Yc K gV π i ⟶ ⊤).op := by
  rw [ac, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_map _ _ _).symm

end RamanujanPetersson.EtPBC.Z3

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

section Base

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

/-- The structure map `Γ(V) → Γ(Y_{V'}, ⊤)`. -/
abbrev strV : Γ(V, ⊤) ⟶ Γ(YV K gV π R', ⊤) :=
  (pullback.fst (π ≫ qV K gV) (hV V R') ≫ π ≫ qV K gV).appTop

end Base

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibA =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`

For `x : Spec K ⟶ V` with `x ≫ gV = 𝟙` (so `Γ(V) → Γ(Spec K)` is surjective):
* `Yx = Y ×_V Spec K`, `fx`, `sx`; for an open `U ⊆ Y`: `TU = Y_x ×_Y U`, `jT` (open immersion onto `fx⁻¹ U`), `kT`,
  `isPullback_T`, `isPushout_T` (`U` affine).
* **`fx_app_surj`**: `Γ(Y, U) → Γ(Y_x, fx⁻¹ U)` is surjective, **`ker_fx_app`**: its kernel is `(ker x^*) Γ(Y, U)`
  (`U` affine).
* `strU`, `strU_ρ`, `appTop_surj`, `isAffineOpen_Y01`, `Yx_sup`, `eq_of_res_x` (separation on the two charts of `Y_x`),
  `fx_res`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Fib

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

theorem strU_ρ (U : Y.Opens) :
    strU K gV π U ≫ U.ι.appLE U ⊤ U.ι_preimage_self.ge = (U.ι ≫ π ≫ qV K gV).appTop := by
  rw [strU, Category.assoc, Scheme.Hom.map_appLE, appLE_top_top]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]

variable (x : Spec (CommRingCat.of K) ⟶ V)

/-- Pulling back commutes with restriction to `U`. -/
theorem fx_res (U : Y.Opens) (s : Γ(Y, ⊤)) :
    (fx K gV π x).app U (Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) =
      (Yx K gV π x).presheaf.map (homOfLE le_top : fx K gV π x ⁻¹ᵁ U ⟶ ⊤).op ((fx K gV π x).appTop s) := by
  have h := Scheme.Hom.naturality (fx K gV π x) (homOfLE le_top : U ⟶ ⊤).op
  exact congrArg (fun φ => φ.hom s) h

variable (U : Y.Opens)

/-- `T_U = Y_x ×_Y U`. -/
abbrev TU : Scheme.{u} := pullback (fx K gV π x) U.ι

/-- `T_U ⟶ Y_x` (an open immersion onto `fx⁻¹ U`). -/
abbrev jT : TU K gV π x U ⟶ Yx K gV π x := pullback.fst (fx K gV π x) U.ι

/-- `T_U ⟶ U`. -/
abbrev kT : TU K gV π x U ⟶ U.toScheme := pullback.snd (fx K gV π x) U.ι

theorem image_jT : jT K gV π x U ''ᵁ ⊤ = fx K gV π x ⁻¹ᵁ U := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι]

theorem isPullback_T :
    IsPullback (kT K gV π x U) (jT K gV π x U ≫ sx K gV π x) (U.ι ≫ π ≫ qV K gV) x :=
  (IsPullback.of_hasPullback (fx K gV π x) U.ι).flip.paste_vert (IsPullback.of_hasPullback (π ≫ qV K gV) x)

end Fib

end RamanujanPetersson.EtPBC.Z3

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

end Res

section Map

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']
  (x : Spec (CommRingCat.of K) ⟶ V) (x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
  (hx' : x' ≫ hV V R' = x)

/-- **The comparison map `Y_x ⟶ Y ×_V Spec R'`** induced by a lift `x'` of `x`. -/
def yxMap : Yx K gV π x ⟶ YV K gV π R' :=
  pullback.lift (fx K gV π x) (sx K gV π x ≫ x') (by rw [Category.assoc, hx']; exact pullback.condition)

end Map

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

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V)

/-- The `K`-algebra structure on sections of the fibre `Y_x`. -/
abbrev algKY (W : (Yx K gV π x).Opens) : Algebra K Γ(Yx K gV π x, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (sx K gV π x).appTop ≫
    (Yx K gV π x).presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom.toAlgebra

attribute [local instance] algKY

/-- The fibre restriction `Γ(Y_x, fx⁻¹ Y₀) → Γ(Y_x, fx⁻¹ Y₀₁)`. -/
abbrev ρx0 : Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ Yc K gV π 0) →+*
    Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)) :=
  ((Yx K gV π x).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op).hom

/-- The fibre restriction `Γ(Y_x, fx⁻¹ Y₁) → Γ(Y_x, fx⁻¹ Y₀₁)`. -/
abbrev ρx1 : Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ Yc K gV π 1) →+*
    Γ(Yx K gV π x, fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)) :=
  ((Yx K gV π x).presheaf.map (homOfLE (Scheme.Hom.preimage_mono _ inf_le_right)).op).hom

section Cover

variable {T : Scheme.{u}} (q : T ⟶ Yx K gV π x)

attribute [local instance] algT

/-- The restriction `Γ(T, q⁻¹ fx⁻¹ Y₀) → Γ(T, q⁻¹ fx⁻¹ Y₀₁)`. -/
abbrev ψT0 : Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 0)) →+*
    Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1))) :=
  (T.presheaf.map (homOfLE (Scheme.Hom.preimage_mono q (Scheme.Hom.preimage_mono _ inf_le_left))).op).hom

/-- The restriction `Γ(T, q⁻¹ fx⁻¹ Y₁) → Γ(T, q⁻¹ fx⁻¹ Y₀₁)`. -/
abbrev ψT1 : Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 1)) →+*
    Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1))) :=
  (T.presheaf.map (homOfLE (Scheme.Hom.preimage_mono q (Scheme.Hom.preimage_mono _ inf_le_right))).op).hom

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

theorem fromSpec_str {U : Y.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ π ≫ qV K gV = Spec.map (strU K gV π U) ≫ V.isoSpec.inv := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec (π ≫ qV K gV) (isAffineOpen_top V) hU (by simp),
    IsAffineOpen.fromSpec_top]
  rfl

section Chart

end Chart

section Res

end Res

/-- The open `fst⁻¹ U` of `Y_{V'}`. -/
abbrev oV (U : Y.Opens) : (YV K gV π R').Opens := pullback.fst (π ≫ qV K gV) (hV V R') ⁻¹ᵁ U

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

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V) [IsAffine V]

/-- **A ring map over `x` lifts `x`.** -/
theorem hxL_of {R' : Type u} [CommRing R'] [Algebra Γ(V, ⊤) R'] (χ' : R' →+* K)
    (hχ : ∀ a : Γ(V, ⊤), χ' (algebraMap Γ(V, ⊤) R' a) = ψx K x a) :
    Spec.map (CommRingCat.ofHom χ') ≫ hV V R' = x := by
  have hc : CommRingCat.ofHom (algebraMap Γ(V, ⊤) R') ≫ CommRingCat.ofHom χ' =
      x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    ext a
    exact hχ a
  rw [hV, ← Category.assoc, ← Spec.map_comp, hc, ← eq_Spec_map]

section Chart

attribute [local instance] algKY algT

end Chart

end RamanujanPetersson.EtPBC.Cov

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

/-- The fibre point of `sigPt τ` over `U` given by a lift `l` of `τ`. -/
def liftPt {U : X.Etale} (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι)
    (l : Spec (CommRingCat.of Ω) ⟶ pullback (pullback.snd π ι) U.hom) (hl : l ≫ pullback.fst _ _ = τ) :
    (sigPt ι π τ).point.fiber.obj U :=
  (Over.homMk (l ≫ pullback.snd _ _) (lift_cond ι π τ l hl) :
    CategoryTheory.Over.mk (sigPt ι π τ).pt ⟶ (Scheme.Etale.forget X).obj U)

theorem liftPt_left {U : X.Etale} (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι)
    (l : Spec (CommRingCat.of Ω) ⟶ pullback (pullback.snd π ι) U.hom) (hl : l ≫ pullback.fst _ _ = τ) :
    ((sigPt ι π τ).liftOf (liftPt ι π τ l hl)).left = l ≫ pullback.snd _ _ := rfl

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

@[reassoc]
theorem pMapV_q : pMapV K gK hj ≫ qV K (hj ≫ gK) = pullback.fst hj (qV K gK) := by
  unfold pMapV
  rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd]

/-- `Y_V ⟶ P¹_V`. -/
def piVV : pullback (pullback.snd hj (qV K gK)) π ⟶ PV K (hj ≫ gK) :=
  pullback.fst _ π ≫ pMapV K gK hj

instance [IsFinite π] : IsFinite (piVV K gK π hj) := by unfold piVV; infer_instance

variable [IsIso (s.pt ≫ gK)] (v : Spec (CommRingCat.of s.Ω) ⟶ V)

/-- `P_s ⟶ V ×_S P` of `v`. -/
def fibV (hv : v ≫ hj = s.pt) : fib (qV K gK) s ⟶ pullback hj (qV K gK) :=
  pullback.lift (pullback.snd _ _ ≫ v) (pullback.fst _ _) (fibV_cond K gK s hj v hv)

section Ext

variable [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

/-- `(Spec R' ×_V V) ×_S P ⟶ V ×_S P`. -/
def pmapR : pullback (hV V R' ≫ hj) (qV K gK) ⟶ pullback hj (qV K gK) :=
  pullback.lift (pullback.fst _ _ ≫ hV V R') (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])

/-- `Y_{V'} ⟶ Y_V`. -/
def ymapR : pullback (pullback.snd (hV V R' ≫ hj) (qV K gK)) π ⟶ pullback (pullback.snd hj (qV K gK)) π :=
  pullback.lift (pullback.fst _ _ ≫ pmapR K gK hj R') (pullback.snd _ _)
    (by rw [Category.assoc, pmapR, pullback.lift_snd, pullback.condition])

variable (x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R')) (v' : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of R'))

theorem fibV_pmapR (hv' : v' ≫ hV V R' = v) (hv : v ≫ hj = s.pt) :
    fibV K gK s (hV V R' ≫ hj) v' (hvR s hj v R' v' hv' hv) ≫ pmapR K gK hj R' = fibV K gK s hj v hv := by
  apply pullback.hom_ext
  · simp only [fibV, pmapR, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hv']
  · simp only [fibV, pmapR, Category.assoc, pullback.lift_snd]

end Ext

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG1 =====
section

/-!
# S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart

For a short exact sequence `0 → F →a E →b Q → 0` of etale sheaves on `X`, an etale `V` and `e ∈ E(V)` whose
restrictions along any two maps `W ⟶ V` have the same image in `Q`:
* `dif a b hab hS e he W w₁ w₂ ∈ F(W)` with `a (dif) = w₁^* e - w₂^* e` (`f_dif`, unique: `dif_eq`);
  `dif_self`, `dif_add` (cocycle), `dif_map` (naturality); `he_of_glob` (the hypothesis from a global section).
* Charts: `σ : Spec A ⟶ X` etale, `τ : Spec C ⟶ V` over `σ` (`hτ`), `C` etale over `A`. `etS σ R` (= `Spec R` as
  an etale `X`-object for an etale `A`-algebra `R`), `homS σ φ`, `kmap σ τ hτ φ : etS σ R ⟶ V`, `homS_kmap`,
  `cval_comap`.
* For `F = M_X` (`M` finite): `cU` (the values of `dif` on `Spec (C ⊗[A] C)`), `cU_diag`, `cU_coc`, and
  **`datU : Datum A C M`** (`DescB.mkDatum`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Dif

variable {Λ : Type u} [CommRing Λ] {X : Scheme.{u}} {F E Q : EtSh Λ X} (a : F ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) {V : X.Etale} (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

theorem f_dif (W : X.Etale) (w₁ w₂ : W ⟶ V) :
    (a.hom.app (op W)).hom (dif a b hab hS e he W w₁ w₂) = difX e W w₁ w₂ :=
  (sec_exact hS W (difX e W w₁ w₂) (g_difX b e he W w₁ w₂)).choose_spec

theorem dif_eq (W : X.Etale) (w₁ w₂ : W ⟶ V) (x : F.obj.obj (op W))
    (hx : (a.hom.app (op W)).hom x = difX e W w₁ w₂) : dif a b hab hS e he W w₁ w₂ = x :=
  sec_inj hS W ((f_dif a b hab hS e he W w₁ w₂).trans hx.symm)

theorem dif_self (W : X.Etale) (w₁ : W ⟶ V) : dif a b hab hS e he W w₁ w₁ = 0 :=
  dif_eq a b hab hS e he W w₁ w₁ 0 (by rw [map_zero, difX, sub_self])

theorem dif_add (W : X.Etale) (w₁ w₂ w₃ : W ⟶ V) :
    dif a b hab hS e he W w₁ w₃ = dif a b hab hS e he W w₁ w₂ + dif a b hab hS e he W w₂ w₃ :=
  dif_eq a b hab hS e he W w₁ w₃ _ (by
    rw [map_add, f_dif, f_dif]
    simp only [difX]
    abel)

theorem dif_map {W W' : X.Etale} (h : W' ⟶ W) (w₁ w₂ : W ⟶ V) :
    (F.obj.map h.op).hom (dif a b hab hS e he W w₁ w₂) = dif a b hab hS e he W' (h ≫ w₁) (h ≫ w₂) := by
  refine (dif_eq a b hab hS e he W' _ _ _ ?_).symm
  have hn := congrArg (fun φ => φ.hom (dif a b hab hS e he W w₁ w₂)) (a.hom.naturality h.op)
  simp only [ModuleCat.comp_apply] at hn
  rw [hn, f_dif]
  simp only [difX]
  rw [map_sub, op_comp, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.comp_apply,
    ModuleCat.comp_apply]

end Dif

section Chart

variable {X : Scheme.{u}} {A : Type u} [CommRing A] (σ : Spec (CommRingCat.of A) ⟶ X) [Etale σ]

variable {C : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] {V : X.Etale}
  (τ : Spec (CommRingCat.of C) ⟶ V.left)
  (hτ : τ ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ σ)

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ}

variable {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q) (hab : a ≫ b = 0)
  (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

/-- The values of the difference cocycle on `Spec (C ⊗[A] C)`. -/
def cU (P : PrimeSpectrum (C ⊗[A] C)) : M :=
  cval (dif a b hab hS e he (etS σ (C ⊗[A] C)) (kmap σ τ hτ (j1 A C)) (kmap σ τ hτ (j2 A C))) P

end Chart

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG2 =====
section

/-!
# S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens

* Cross-chart maps `homX σ σ' ρA hσ φ hφ : etS σ' R' ⟶ etS σ R` (for `Spec ρA ≫ σ = σ'`), `homX_kmap`,
  `cval_comapX`; **`datU_compat`**: `psiMap ρA φC hφC (datU ...).ε m = (datU' ...).ε m`.
* On affine opens `U` of `X` (for `V` etale over `X` with `V.hom` affine): `CU V U = Γ(V, V.hom⁻¹ U)` as an etale
  `Γ(X, U)`-algebra, the chart datum `datA`, restriction maps `mapU`, the functor
  **`FU : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat`**, `alphaU : 𝒪_X ⟶ FU` and **`coequifibered_alphaU`**.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Cross

end Cross

section Pres

end Pres

section Glue

variable {X : Scheme.{u}}

theorem algebraMap_CU (V : X.Etale) (U : X.AffineZariskiSite) (x : Γ(X, U.1)) :
    algebraMap Γ(X, U.1) (CU V U) x = (V.hom.app U.1).hom x := rfl

variable (V : X.Etale) [IsAffineHom V.hom]

instance (U : X.AffineZariskiSite) : Algebra.Etale Γ(X, U.1) (CU V U) := by
  have h := HasRingHomProperty.appLE @Etale (f := V.hom) inferInstance ⟨U.1, U.2⟩
    ⟨_, U.2.preimage V.hom⟩ le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact RingHom.etale_algebraMap.1 h

theorem htauU (U : X.AffineZariskiSite) :
    tauU V U ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (CU V U))) ≫ U.2.fromSpec := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec V.hom U.2 (U.2.preimage V.hom) le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact h.symm

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M] {E Q : EtSh Λ X}
  (a : constSh Λ X M ⟶ E) (b : E ⟶ Q) (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact)
  (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

theorem hphiV {U U' : X.AffineZariskiSite} (h : U'.1 ≤ U.1) (x : Γ(X, U.1)) :
    phiV V h (algebraMap Γ(X, U.1) (CU V U) x) = algebraMap Γ(X, U'.1) (CU V U') (rhoX h x) :=
  (congrArg (fun g => g.hom x) (V.hom.naturality (homOfLE h).op)).symm

end Glue

end RamanujanPetersson.EtPBC.DescG

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

variable {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)

set_option backward.isDefEq.respectTransparency false in
theorem prop_toBase (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hP : ∀ U : X.AffineZariskiSite, P (Spec.map (α.app (op U)))) : P (glD H).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq ((glD H).toBase ⁻¹ᵁ U).ι ((glD H).cover.f U)
      (by simpa using congr($(toBase_preimage H U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso P e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso P _ U.2.isoSpec.hom]
  convert! hP U
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e]
  exact cover_toBase H U

end Base

section Cover

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_FBCv =====
section

/-!
# S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre

For `π : Y ⟶ P` finite, a geometric point `t` of `P`, a neighbourhood `j` of `t` and any `v : π⁻¹(j) → M`, after
refining `j` there is a section `z` of `M_Y` over `π⁻¹(j')` whose values along the fibre `fib π t` are those of `v`.
* `PhiU`: `R' ⊗_{Γ(W)} Γ(U) → Γ(U')` for a square `U' → U → W`, `U' → Spec R' → W`; `comap_PhiU_left/right`;
* `exists_sec_vals_aff` (affine `j`), **`exists_sec_vals`** (Stacks 00UL via
  `Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.FBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.Z3

universe u

section Phi

variable {W U U' : Scheme.{u}} [IsAffine W] (g : U ⟶ W) (R' : Type u) [CommRing R'] [Algebra Γ(W, ⊤) R']
  (f₁ : U' ⟶ Spec (CommRingCat.of R')) (f₂ : U' ⟶ U) [Algebra Γ(W, ⊤) Γ(U, ⊤)] [Algebra Γ(W, ⊤) Γ(U', ⊤)]

/-- `R' → Γ(U', ⊤)` along `f₁`. -/
def fRU (h' : algebraMap Γ(W, ⊤) Γ(U', ⊤) = (f₁ ≫ hV W R').appTop.hom) : R' →ₐ[Γ(W, ⊤)] Γ(U', ⊤) where
  toRingHom := f₁.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
  commutes' a := by
    show f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (algebraMap Γ(W, ⊤) R' a)) =
      algebraMap Γ(W, ⊤) Γ(U', ⊤) a
    rw [h', Scheme.Hom.comp_appTop, hV_appTop]
    rfl

end Phi

section Main

end Main

end RamanujanPetersson.EtPBC.FBC

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

@[reassoc]
theorem kapL_fst (V : P.Etale) : kapL h Φ V ≫ pullback.fst (pullback.snd V.hom Φ) h = muU h Φ V :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem kapL_snd (V : P.Etale) : kapL h Φ V ≫ pullback.snd (pullback.snd V.hom Φ) h = pullback.snd V.hom (h ≫ Φ) :=
  pullback.lift_snd _ _ _

/-- `V ×_P U₁ ⟶ (V ×_P U₂) ×_{U₂} U₁` in `U₁.Etale`. -/
def kapU (V : P.Etale) : (etPull (h ≫ Φ)).obj V ⟶ (etPull h).obj ((etPull Φ).obj V) :=
  MorphismProperty.Over.homMk (kapL h Φ V) (kapL_snd h Φ V) trivial

theorem kapU_left (V : P.Etale) : (kapU h Φ V).left = kapL h Φ V := rfl

theorem kapU_nat {V' V : P.Etale} (a : V' ⟶ V) :
    kapU h Φ V' ≫ (etPull h).map ((etPull Φ).map a) = (etPull (h ≫ Φ)).map a ≫ kapU h Φ V := by
  apply MorphismProperty.Over.Hom.ext
  show kapL h Φ V' ≫ ((etPull h).map ((etPull Φ).map a)).left = ((etPull (h ≫ Φ)).map a).left ≫ kapL h Φ V
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_fst h ((etPull Φ).map a))).trans
      ((kapL_fst_assoc h Φ V' _).trans ?_))
    refine Eq.trans ?_ ((Category.assoc _ _ _).trans (whisker_eq _ (kapL_fst h Φ V))).symm
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_fst Φ a)).trans
        ((muU_fst_assoc h Φ V' _).trans ?_))
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (whisker_eq _ (muU_fst h Φ V))).symm
      exact (etPull_map_left_fst (h ≫ Φ) a).symm
    · refine (Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_snd Φ a)).trans
        ((muU_snd h Φ V').trans ?_))
      refine Eq.trans ?_ ((Category.assoc _ _ _).trans (whisker_eq _ (muU_snd h Φ V))).symm
      exact ((Category.assoc _ _ _).symm.trans (eq_whisker (etPull_map_left_snd (h ≫ Φ) a) h)).symm
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (etPull_map_left_snd h ((etPull Φ).map a))).trans
      ((kapL_snd h Φ V').trans ?_))
    exact ((Category.assoc _ _ _).trans ((whisker_eq _ (kapL_snd h Φ V)).trans
      (etPull_map_left_snd (h ≫ Φ) a))).symm

/-- A retraction of `kapL`. -/
def kapR (V : P.Etale) : pullback (pullback.snd V.hom Φ) h ⟶ pullback V.hom (h ≫ Φ) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc])

theorem kapL_kapR (V : P.Etale) : kapL h Φ V ≫ kapR h Φ V = 𝟙 _ := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (pullback.lift_fst _ _ _)).trans ?_)
    refine ((Category.assoc _ _ _).symm.trans ((eq_whisker (kapL_fst h Φ V) _).trans (muU_fst h Φ V))).trans ?_
    exact (Category.id_comp _).symm
  · refine (Category.assoc _ _ _).trans ((whisker_eq _ (pullback.lift_snd _ _ _)).trans ?_)
    exact (kapL_snd h Φ V).trans (Category.id_comp _).symm

/-- `muU` is injective on points when `h` is a closed immersion. -/
theorem muU_injective [IsClosedImmersion h] (V : P.Etale) : Function.Injective (muU h Φ V) := by
  intro y₁ y₂ hy
  have h1 : kapL h Φ V y₁ = kapL h Φ V y₂ := by
    apply (pullback.fst (pullback.snd V.hom Φ) h).isEmbedding.injective
    exact (congrArg (fun φ => φ.base y₁) (kapL_fst h Φ V)).trans
      (hy.trans (congrArg (fun φ => φ.base y₂) (kapL_fst h Φ V)).symm)
  have e1 := congrArg (fun φ => φ.base y₁) (kapL_kapR h Φ V)
  have e2 := congrArg (fun φ => φ.base y₂) (kapL_kapR h Φ V)
  exact e1.symm.trans ((congrArg (kapR h Φ V) h1).trans e2)

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

variable {Λ : Type u} [CommRing Λ] (J : ModuleCat.{u} Λ)

omit [Etale e] in
/-- Components of maps into the skyscraper sheaves at lifts depend only on the underlying map. -/
theorem app_π_congr {G : EtSh Λ U} (h : ∀ l, G ⟶ (liftPt e x l).point.skyscraperSheaf J)
    (W : (U.Etale)ᵒᵖ) (l l' : Lifts e x) (hl : l = l') (c : (liftPt e x l).point.fiber.obj W.unop)
    (c' : (liftPt e x l').point.fiber.obj W.unop)
    (hc : fl (liftPt e x l) c = fl (liftPt e x l') c') :
    (h l).hom.app W ≫ sπ J (liftPt e x l).point W c =
      (h l').hom.app W ≫ sπ J (liftPt e x l').point W c' := by
  subst hl
  obtain rfl : c = c' := fl_ext _ hc
  rfl

end RamanujanPetersson.EtSheaves.LshEt

end

end

-- ===== S4.Def_RP_EtPBC_A_DeltaK =====
section

/-!
# S4-EtPBC-A, R4-T3a: one class killed by a monomorphism comes from a germ

Abstract `δ`-functor setting of `Delta` (`L` exact, `A : J ⥤ C`, `B`, `u`).

* **`exists_bc_of_kill`**: for `0 → X₁ → X₂ → X₃ → 0` short exact with base change surjective on germs in degree `q`
  for `X₃`, every class `β ∈ Ext^(q+1)(B, L X₁)` with `β ∘ L(f) = 0` is the base change of a germ.
  (Effacement of one class: `X₂ = ρ_* M_U` for a finite etale cover `ρ` killing `β` on the fibre.)
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {J : Type u₃} [Category.{v₃} J]
  {L : C ⥤ D} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {A : J ⥤ C} {B : D} {u : ∀ j, B ⟶ L.obj (A.obj j)}

/-- **A class killed by `L(f)` comes from a germ** when base change is surjective in degree `q` for the cokernel. -/
theorem exists_bc_of_kill {S : ShortComplex C} (hSE : S.ShortExact) {q : ℕ}
    (hS₃ : SurjAt L A B u q S.X₃) (β : Ext B (L.obj S.X₁) (q + 1))
    (hβ : β.comp (Ext.mk₀ (L.map S.f)) (add_zero (q + 1)) = 0) :
    ∃ (j : J) (α : Ext (A.obj j) S.X₁ (q + 1)), bc L A B u j S.X₁ (q + 1) α = β := by
  obtain ⟨γ, hγ⟩ := Ext.covariant_sequence_exact₁ (X := B) (hSE.map_of_exact L) β hβ rfl
  obtain ⟨j, α, hα⟩ := hS₃ γ
  exact ⟨j, α.comp hSE.extClass rfl, by rw [bc_comp_extClass, hα]; exact hγ⟩

end RamanujanPetersson.EtPBC.Delta

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

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] (U : X.AffineZariskiSite)

instance isOpenImmersion_tauU : IsOpenImmersion (tauU V U) :=
  IsAffineOpen.isOpenImmersion_fromSpec (U.2.preimage V.hom)

theorem range_tauU_sub {Z : Scheme.{u}} (g : Z ⟶ V.left) (hg : ∀ z, vh V (g z) ∈ U.1) :
    Set.range g ⊆ Set.range (tauU V U) := by
  rintro _ ⟨z, rfl⟩
  exact (Set.ext_iff.1 (U.2.preimage V.hom).range_fromSpec (g z)).2 (hg z)

/-- A map landing over `U`, lifted to the chart `Spec (CU V U)`. -/
def liftU {Z : Scheme.{u}} (g : Z ⟶ V.left) (hg : ∀ z, vh V (g z) ∈ U.1) :
    Z ⟶ Spec (CommRingCat.of (CU V U)) :=
  IsOpenImmersion.lift (tauU V U) g (range_tauU_sub V U g hg)

@[reassoc]
theorem liftU_fac {Z : Scheme.{u}} (g : Z ⟶ V.left) (hg : ∀ z, vh V (g z) ∈ U.1) :
    liftU V U g hg ≫ tauU V U = g :=
  IsOpenImmersion.lift_fac (tauU V U) g (range_tauU_sub V U g hg)

theorem liftU_alg {Z : Scheme.{u}} (g : Z ⟶ V.left) (hg : ∀ z, vh V (g z) ∈ U.1) :
    liftU V U g hg ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (CU V U))) ≫ U.2.fromSpec =
      g ≫ vh V :=
  (whisker_eq _ (htauU V U)).symm.trans ((Category.assoc _ _ _).symm.trans (eq_whisker (liftU_fac V U g hg) V.hom))

theorem liftU_eq {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ V.left) (h : g₁ ≫ vh V = g₂ ≫ vh V)
    (hg₁ : ∀ z, vh V (g₁ z) ∈ U.1) (hg₂ : ∀ z, vh V (g₂ z) ∈ U.1) :
    liftU V U g₁ hg₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (CU V U))) =
      liftU V U g₂ hg₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (CU V U))) :=
  (cancel_mono U.2.fromSpec).1 ((Category.assoc _ _ _).trans ((liftU_alg V U g₁ hg₁).trans (h.trans
    ((liftU_alg V U g₂ hg₂).symm.trans (Category.assoc _ _ _).symm))))

/-- A pair of maps over `U` as a map to `Spec (C ⊗_A C)`. -/
def kL {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ V.left) (h : g₁ ≫ vh V = g₂ ≫ vh V)
    (hg₁ : ∀ z, vh V (g₁ z) ∈ U.1) (hg₂ : ∀ z, vh V (g₂ z) ∈ U.1) :
    Z ⟶ Spec (CommRingCat.of (CU V U ⊗[Γ(X, U.1)] CU V U)) :=
  pullback.lift (liftU V U g₁ hg₁) (liftU V U g₂ hg₂) (liftU_eq V U g₁ g₂ h hg₁ hg₂) ≫
    (pullbackSpecIso Γ(X, U.1) (CU V U) (CU V U)).hom

end Pt

section Cover

end Cover

end RamanujanPetersson.EtPBC.DescG

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

theorem piT_apply (W : (Over T)ᵒᵖ) (x : ((Over.forget T).op ⋙ E.obj).obj W) :
    piT b σ W x = x - ((secT σ).app W).hom (((wh b T).app W).hom x) := rfl

theorem piT_nat {W W' : (Over T)ᵒᵖ} (f : W ⟶ W') (x : ((Over.forget T).op ⋙ E.obj).obj W) :
    (((Over.forget T).op ⋙ E.obj).map f).hom (piT b σ W x) =
      piT b σ W' ((((Over.forget T).op ⋙ E.obj).map f).hom x) := by
  have hs := congrArg (fun φ => φ.hom (((wh b T).app W).hom x)) ((secT σ).naturality f)
  have hb := congrArg (fun φ => φ.hom x) ((wh b T).naturality f)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hs hb
  rw [piT_apply, piT_apply, map_sub, ← hs, ← hb]

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

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} {U₁ U₂ P : Scheme.{u}} (h : U₁ ⟶ U₂) (Φ : U₂ ⟶ P)

theorem kapU_inv (V : P.Etale) : kapU h Φ V ≫ (etPullCompIso h Φ).inv.app V = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  change kapL h Φ V ≫ ((etPullCompIso h Φ).inv.app V).left = 𝟙 _
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((whisker_eq _ (T3d.etPullCompIso_inv_fst h Φ V)).trans
      ((kapL_fst_assoc h Φ V _).trans ((muU_fst h Φ V).trans (Category.id_comp _).symm)))
  · exact (Category.assoc _ _ _).trans ((whisker_eq _ (T3d.etPullCompIso_inv_snd h Φ V)).trans
      ((kapL_snd h Φ V).trans (Category.id_comp _).symm))

end RU

section Gen

end Gen

section Push

end Push

section T1

end T1

end RamanujanPetersson.EtPBC.DescK

end

end

-- ===== S4.Def_RP_EtPBC_A_CovNbA =====
section

/-!
# S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed

* `kapInv`, **`IsIso (kapV ..)`**: `Y_{V'} = (Spec R' ×_S P) ×_P Y ≅ Y_V ×_V Spec R'`;
* **`isPullback_fibV`**: `P_s ⟶ W ×_S P` is the base change of `w : Spec Ω ⟶ W`; so it is a closed immersion
  when `w` is (`isClosedImmersion_fibV`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S)

section Kap

end Kap

section Fib

variable [IsIso (s.pt ≫ gK)]

/-- **The fibre inclusion of a neighbourhood is a base change of the point.** -/
theorem isPullback_fibV {W : Scheme.{u}} (hw : W ⟶ S) (w : Spec (CommRingCat.of s.Ω) ⟶ W) (hv : w ≫ hw = s.pt) :
    IsPullback (fibV K gK s hw w hv) (pullback.snd (qV K gK) s.pt) (pullback.fst hw (qV K gK)) w := by
  refine IsPullback.of_right (h₁₂ := pullback.snd hw (qV K gK)) (h₂₂ := hw) (v₁₃ := qV K gK) ?_ ?_
    (IsPullback.of_hasPullback hw (qV K gK)).flip
  · convert IsPullback.of_hasPullback (qV K gK) s.pt using 1 <;> first | exact pullback.lift_snd _ _ _ | exact hv
  · exact pullback.lift_fst _ _ _

end Fib

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NagA =====
section

/-!
# S4-EtPBC-A, M4(N1): integral closures over a finite type domain over a perfect field (integrally closed case)

* `finite_of_comp_injective`: if `ι ∘ f` is finite, `ι` injective and the source noetherian, then `f` is finite;
* `iterateFrobenius_finite`: for a finite type algebra `A` over a perfect field, `a ↦ a ^ p ^ e` is finite;
* **`finite_integralClosure_of_isIntegrallyClosed`**: `A` a noetherian integrally closed domain of finite type over a
  perfect field, `L` finite over `Frac A` ⇒ the integral closure of `A` in `L` is a finite `A`-module (separable
  part: `IsIntegralClosure.finite`; inseparable part: Frobenius `b ↦ b ^ p ^ e` into the separable closure).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Nagata

open Polynomial

section Frob

end Frob

section N1

variable (K A F L : Type*) [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
  [IsIntegrallyClosed A] [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F] [Field L] [Algebra F L]
  [Algebra A L] [IsScalarTower A F L] [FiniteDimensional F L] (p : ℕ) [ExpChar K p] [PerfectRing K p]

include K F p in
/-- **Finiteness of the integral closure** (`A` integrally closed). -/
theorem finite_integralClosure_of_isIntegrallyClosed : Module.Finite A (integralClosure A L) := by
  have : ExpChar A p := expChar_of_injective_algebraMap (algebraMap K A).injective p
  have : ExpChar F p := expChar_of_injective_algebraMap (IsFractionRing.injective A F) p
  have : ExpChar L p := expChar_of_injective_algebraMap (algebraMap F L).injective p
  have : ExpChar (separableClosure F L) p :=
    expChar_of_injective_algebraMap (algebraMap F (separableClosure F L)).injective p
  have hBs : Module.Finite A (integralClosure A (separableClosure F L)) :=
    IsIntegralClosure.finite A F (separableClosure F L) (integralClosure A (separableClosure F L))
  have : IsScalarTower A (separableClosure F L) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e := IsPurelyInseparable.exponent (separableClosure F L) L
  have hmem : ∀ b : integralClosure A L, iterateFrobenius L p e (b : L) ∈ separableClosure F L := fun b => by
    obtain ⟨c, hc⟩ := IsPurelyInseparable.exponent_def' (separableClosure F L) p (b : L)
    rw [iterateFrobenius_def, ← hc]
    exact c.2
  have hint : ∀ b : integralClosure A L,
      IsIntegral A (⟨iterateFrobenius L p e (b : L), hmem b⟩ : separableClosure F L) := fun b =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (separableClosure F L) L)
      (algebraMap (separableClosure F L) L).injective).1 (by
        show IsIntegral A (iterateFrobenius L p e (b : L))
        rw [iterateFrobenius_def]
        exact b.2.pow _)
  let ι : integralClosure A L →+* integralClosure A (separableClosure F L) :=
    { toFun := fun b => ⟨⟨iterateFrobenius L p e (b : L), hmem b⟩, hint b⟩
      map_one' := Subtype.ext (Subtype.ext (map_one (iterateFrobenius L p e)))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul (iterateFrobenius L p e) (x : L) (y : L)))
      map_zero' := Subtype.ext (Subtype.ext (map_zero (iterateFrobenius L p e)))
      map_add' := fun x y => Subtype.ext (Subtype.ext (map_add (iterateFrobenius L p e) (x : L) (y : L))) }
  have hι : Function.Injective ι := fun x y hxy => by
    have h : iterateFrobenius L p e (x : L) = iterateFrobenius L p e (y : L) :=
      congrArg (fun z : integralClosure A (separableClosure F L) => ((z : separableClosure F L) : L)) hxy
    exact Subtype.ext ((iterateFrobenius L p e).injective h)
  have hcomm : ι.comp (algebraMap A (integralClosure A L)) =
      (algebraMap A (integralClosure A (separableClosure F L))).comp (iterateFrobenius A p e) := by
    ext a
    show iterateFrobenius L p e (algebraMap A L a) = algebraMap A L (iterateFrobenius A p e a)
    simp only [iterateFrobenius_def, map_pow]
  have hfin : (ι.comp (algebraMap A (integralClosure A L))).Finite := by
    rw [hcomm]
    exact RingHom.Finite.comp (RingHom.finite_algebraMap.2 hBs) (iterateFrobenius_finite K p A e)
  exact RingHom.finite_algebraMap.1 (finite_of_comp_injective _ ι hι hfin)

end N1

end RamanujanPetersson.EtPBC.Nagata

end

end

-- ===== S4.Def_RP_EtPBC_A_O2D3 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M3 step (5): Claim D on `P¹`

* `A1.exists_closed_mem`: a nonzero `f ∈ k[X]` is a unit at some closed point (`k` infinite);
* `two_dies_A1`: the `k[X]` instance of `two_dies` (`k = k̄`, `ℓ ≠ char k`, `ℓ^m Λ = 0`);
* `chartEt k`: the chart `A¹ ⟶ P¹` as an étale object; `chart_dies`: `β ∈ Ext²(Λ_{P¹}, F)` dies on
  `chart ∘ D(f)` (restrict to the chart with `extFree`, apply `two_dies_A1`, come back with `restrict_eq_zero`);
* `U' k f := chart ''ᵁ D(f)`, `toU'`: `opEt (U' k f) ⟶ chart ∘ D(f)` (open immersion lift);
* **`claimD`**: every `β ∈ Ext²(Λ[P¹], F)` dies on the open `U' k f` of `P¹` for some `f ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.EtCompact.CurveHn

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

section GenDies

universe w₁ v₁ u₁

end GenDies

/-- `chart ∘ D(f) ⟶ P¹` factors through the chart. -/
theorem chart_toTop_eq (f : k[X]) :
    freeMap Λ (toTop ((etComp (chartEt k).hom).obj (opEt (bOpen f)))) =
      freeMap Λ (toW (chartEt k) (opEt (bOpen f))) ≫ freeMap Λ (toTop (chartEt k)) := by
  rw [← freeMap_comp, toTop_ext (toTop ((etComp (chartEt k).hom).obj (opEt (bOpen f))))
    (toW (chartEt k) (opEt (bOpen f)) ≫ toTop (chartEt k))]

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2M4b =====
section

/-!
# S4-EtPBC-A, O2 (MV route), M4 (b): every class of `H²(P¹, F)` is a Mayer-Vietoris class

* `exists_good_opn`: an etale object `N` with chosen fibre points `n z` over a finite set `Zs` of closed points
  (Galois-trivial) has an open `V ⊆ N` whose geometric fibre over every `z ∈ Zs` is a singleton (remove the closed
  discrete set `N⁻¹(Zs) ∖ {fpt (n z)}`);
* `genPt_mem_U'`, `isClosed_of_not_mem_U'`, `finite_compl_U'`: `P¹ ∖ chart(D(f))` is a finite set of closed points;
* **`mv_two`** (M4): for every `β ∈ Ext²(Λ[P¹], F)` there are `f ≠ 0` and an MV-good `W` for the open `U' k f`
  with `β|_W = 0` and `β = ε ∘ κ`, `ε` the MV class of `0 → Λ[W ×_P U'] → Λ[W] ⊞ Λ[U'] → Λ → 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtCompact.CurveHn RamanujanPetersson.EtPBC.GenGeo

section Shrink

universe u

end Shrink

variable (k : Type) [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ]

theorem finite_compl_U' (f : k[X]) (hf : f ≠ 0) : ((U' k f : Set (P1 k))ᶜ).Finite := by
  have : AlgebraicGeometry.IsNoetherian (P1 k) := ⟨⟩
  exact finite_of_isClosed_pts (U' k f).isOpen.isClosed_compl (fun x hx => isClosed_of_not_mem_U' k f hf x hx)

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N4 =====
section

/-!
# S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)

* `algebraMap_residueFieldIso_inv_residueFieldMap` (category level): for `φ : R ⟶ S` and `y : Spec S`,
  `R → κ(φ y) → κ(y)` equals `R → S → κ(y)`;
* `resMapX_spec`, `resMapX_toGen`: `resMapX (Spec.map φ) h (toGen A a) = toGen A' (φ a)`;
* `resMapX_fracIso`: for `ψ : K → K'` extending `φ`, `resMapX (fracIso A K k) = fracIso A' K' (ψ k)`;
* `sepX_genEmb_algebraMap`: `sepX (genEmb (k)) = genEmb (ψ k)` for `k ∈ K`;
* **`resLE_kappaL_kum_field`**: NAT for Kummer classes along `Spec.map φ` when `ζ` and `γ^N` come from `K`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer

section Cat

universe u

theorem resMapX_spec {R S : CommRingCat.{u}} (φ : R ⟶ S) [Etale (Spec.map φ)] {y : Spec S} {x : Spec R}
    (h : Spec.map φ y = x) (r : R) :
    resMapX (Spec.map φ) h ((CommRingCat.ofHom (algebraMap R _) ≫ (Scheme.Spec.residueFieldIso R x).inv).hom r) =
      (CommRingCat.ofHom (algebraMap S _) ≫ (Scheme.Spec.residueFieldIso S y).inv).hom (φ.hom r) := by
  subst h
  exact congrArg (fun f => f.hom r) (algebraMap_residueFieldIso_inv_residueFieldMap φ y)

end Cat

section Gen

end Gen

end RamanujanPetersson.EtCompact.GalTrE

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

variable (k : Type u) [Field k]

theorem eq_A1pt [IsAlgClosed k] (p : A1 k) (hp : p.asIdeal.IsMaximal) : ∃ a : k, p = A1pt k a := by
  obtain ⟨a, ha⟩ := exists_X_sub_C_mem' k p.asIdeal
  refine ⟨a, PrimeSpectrum.ext ?_⟩
  have hm : (Ideal.span {X - C a} : Ideal k[X]).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)
  exact (hm.eq_of_le hp.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ha)).symm

/-- **Closed points of a chart** are the points `X = a`. -/
theorem exists_A1pt_of_closed [IsAlgClosed k] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c] {z : P}
    (hzc : z ∈ Set.range c) (hzcl : IsClosed ({z} : Set P)) : ∃ a : k, c (A1pt k a) = z := by
  obtain ⟨p, rfl⟩ := hzc
  have hpre : (c : A1 k → P) ⁻¹' {c p} = {p} :=
    Set.ext fun y => ⟨fun h => c.isOpenEmbedding.injective h, fun h => by rw [h]; rfl⟩
  have hcl : IsClosed ({p} : Set (A1 k)) := by
    rw [← hpre]
    exact hzcl.preimage c.continuous
  obtain ⟨a, ha⟩ := eq_A1pt k p ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).1 hcl)
  exact ⟨a, by rw [ha]⟩

end A1

section D1

variable {k : Type u} [Field k] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {D : P.Etale} {V : D.left.Opens} (hV : IsAffineOpen V) (hVc : ∀ v ∈ V, D.hom v ∈ Set.range c)
  (g : Γ(D.left, V))

include c hV hVc

theorem phiG_fac : Spec.map (phiG c hV hVc g) ≫ c = Spec.map (locG g) ≫ hV.fromSpec ≫ D.hom := by
  rw [phiG, Spec.map_comp, Category.assoc, spec_chartRing, chartLift_fac]

instance etale_phiG : Etale (Spec.map (phiG c hV hVc g) ≫ c) := by
  rw [phiG_fac]; infer_instance

/-- `Spec Γ(V)_g` as an étale object over `P` (through the chart). -/
abbrev D1 : P.Etale := Scheme.Etale.mk (Spec.map (phiG c hV hVc g) ≫ c)

/-- `Spec Γ(V)_g ⟶ D`. -/
def d1 : D1 c hV hVc g ⟶ D :=
  MorphismProperty.Over.homMk (Spec.map (locG g) ≫ hV.fromSpec)
    ((Category.assoc _ _ _).trans (phiG_fac c hV hVc g).symm)

theorem phiG_apply (x : k[X]) :
    letI := (chartRing c D hV hVc).hom.toAlgebra
    (phiG c hV hVc g).hom x = algebraMap k[X] (Localization.Away g) x := by
  letI := (chartRing c D hV hVc).hom.toAlgebra
  rw [IsScalarTower.algebraMap_apply k[X] Γ(D.left, V) (Localization.Away g)]
  rfl

end D1

section Aff

end Aff

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Th1b =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1b): Shapiro over a FIXED base `D₀` (definitions `thetaV`, `theta`, `thX`)

For `τ : T ⟶ D₀` (`W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`):
* **`theta Λ R n hn τ : Ext¹_P(Λ[T], Λ[R]) ≃+ H¹(T ×_P R, Λ)`**;
* `thX`: the `W₀`-level class (`theta_apply`, naturality: O2Th1c).
* (surgery) `theta := thetaGen ..` with generic `thXEGen`/`thetaGen` and `extFreeUT`.
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

section GenTheta

universe w₁ v₁ u₁ v₂ u₂ u₃

/-- Generic `theta`: `thXEGen` followed by `E`. -/
def thetaGen {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] {h₁ : HasExt.{w₁} C₁}
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] {h₂ : HasExt.{w₁} C₂} {M : Type u₃} [Add M]
    {A₀ A₁ B : C₁} {X X' Y : C₂} (e₁ : A₁ ≅ A₀) (Θ : Ext.{w₁} A₁ B 1 ≃+ Ext.{w₁} X Y 1) (e₂ : X' ≅ X)
    (E : Ext.{w₁} X' Y 1 ≃+ M) : Ext.{w₁} A₀ B 1 ≃+ M :=
  (thXEGen e₁ Θ e₂).trans E

end GenTheta

section Theta

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UK1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UK1): `1 + t e` is a `d`-th power over an etale neighbourhood (ring level)

Km DESIGN v3 step UK, ring level. Let `χ : B → K` be a point with `χ t = 0`, `d` a unit of `B`, and `g ∈ B[X]` monic of
degree `n > 0`. In the coordinates `y_0 … y_{n-1}` of `B[X] ⧸ (g)`, the equation `(Σ y_i X^i)^d = 1 + t X` is the
system `ukF g d t` (coefficients of the remainder mod `g`). At `y₀ = (1, 0, …, 0)` its Jacobian is `d · 1`
(`uk_jac`, computed with dual numbers, `aeval_dual`) and its value is `-t · (X mod g)`, divisible by `det² = d^{2n}`.
* **`uk_root`** (Tougeron, `tougeron_nbhd_strong`): there are an etale `B → B'` with a point `χ'` over `χ` and
  `y : Fin n → B'` such that `(Σ y_i e^i)^d = 1 + t e` for every root `e` of `g` in every `B'`-algebra.
* `exists_monic_of_isIntegral`: an integral element has a monic equation of positive degree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC.Cov

universe u v

section Dual

end Dual

section UK

variable {B : Type u} [CommRing B]

theorem uk_dvd (g : B[X]) (hg : g.Monic) (d : ℕ) (t : B) {S : Type v} [CommRing S] [Algebra B S]
    (φ : MvPolynomial (Fin g.natDegree) B →ₐ[B] S) (hφ : ∀ j, φ (ukF g d t j) = 0) :
    g.map (algebraMap B S) ∣ (∑ i : Fin g.natDegree, C (φ (MvPolynomial.X i)) * X ^ (i : ℕ)) ^ d - 1 -
      C (algebraMap B S t) * X := by
  rw [← modByMonic_eq_zero_iff_dvd (hg.map _), ← ukP_map, ← map_gM g φ,
    ← map_modByMonic (φ : MvPolynomial (Fin g.natDegree) B →+* S) (hg.map MvPolynomial.C)]
  ext j
  rw [coeff_map, coeff_zero]
  by_cases hj : j < g.natDegree
  · exact hφ ⟨j, hj⟩
  · have hc : (ukP g.natDegree d t %ₘ
        g.map (MvPolynomial.C : B →+* MvPolynomial (Fin g.natDegree) B)).coeff j = 0 := by
      by_cases h1 : g.map (MvPolynomial.C : B →+* MvPolynomial (Fin g.natDegree) B) = 1
      · rw [h1, modByMonic_one, coeff_zero]
      · apply coeff_eq_zero_of_natDegree_lt
        have := natDegree_modByMonic_lt (ukP g.natDegree d t) (hg.map MvPolynomial.C) h1
        rw [natDegree_map_eq_of_injective (MvPolynomial.C_injective _ _)] at this
        omega
    rw [hc, map_zero]

theorem uk_eval (g : B[X]) (hg : g.Monic) (d : ℕ) (t : B) {S : Type v} [CommRing S] [Algebra B S]
    (φ : MvPolynomial (Fin g.natDegree) B →ₐ[B] S) (hφ : ∀ j, φ (ukF g d t j) = 0) (e : S)
    (he : aeval e g = 0) :
    (∑ i : Fin g.natDegree, φ (MvPolynomial.X i) * e ^ (i : ℕ)) ^ d = 1 + algebraMap B S t * e := by
  obtain ⟨r, hr⟩ := uk_dvd g hg d t φ hφ
  have h := congrArg (eval e) hr
  rw [eval_mul, eval_map_algebraMap, he, zero_mul] at h
  simp only [eval_sub, eval_pow, eval_finsetSum, eval_mul, eval_C, eval_X, eval_one] at h
  linear_combination h

end UK

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

theorem map_mem_bcField {L : IntermediateField K (AlgebraicClosure K)} (f : K[X]) [f.IsSplittingField K L]
    (y : L) : ι y ∈ bcField (K' := K') f := by
  have h1 : (y : AlgebraicClosure K) ∈ Algebra.adjoin K (f.rootSet (AlgebraicClosure K)) := by
    rw [adjoin_rootSet_eq L f]
    exact y.2
  have h2 : ι y ∈ Algebra.adjoin K (ι '' f.rootSet (AlgebraicClosure K)) := by
    rw [← AlgHom.map_adjoin]
    exact Subalgebra.mem_map.2 ⟨_, h1, rfl⟩
  rw [← rootSet_bc ι f] at h2
  exact Algebra.adjoin_le (S := ((bcField (K' := K') f).restrictScalars K).toSubalgebra)
    (fun w hw => IntermediateField.subset_adjoin K' _ hw) h2

end FunA

end

end EtPi1
end RamanujanPetersson


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

/-- In a pushout of commutative rings, the ring is generated over the right leg by the image of the left leg. -/
theorem mem_adjoin_of_isPushout {Z X Y Q : CommRingCat.{u}} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ Q}
    {inr : Y ⟶ Q} (h : IsPushout f g inl inr) [Algebra Y Q] (hY : algebraMap Y Q = inr.hom) (x : Q) :
    x ∈ Algebra.adjoin Y (Set.range inl.hom) := by
  have hx := mem_closure_of_isPushout h x
  refine (Subring.closure_le (t := (Algebra.adjoin Y (Set.range inl.hom)).toSubring)).2
    (Set.union_subset (fun _ hz => Algebra.subset_adjoin hz) ?_) hx
  rintro _ ⟨y, rfl⟩
  rw [← hY]
  exact Subalgebra.algebraMap_mem _ y

end Ring

section Pb

end Pb

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1c =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2

GLOB/REL PLAN v1, stage S1. For an affine `X` with `g : X ⟶ Spec A` etale (`A` a domain, e.g. `A = k[X]`):
* `gamMap g : A →+* Γ(X)`;
* `exists_frac_dvd` (3a): `u ≠ 0` in `Frac(Γ(X) ⧸ p)` is `x / y` with `x ∣ c_x`, `y ∣ c_y`, `c_x, c_y ∈ A ∖ 0`;
* `toPiQ_gamMap_ne_zero`: a nonzero `r ∈ A` is nonzero on every piece (flatness);
* `exists_L` (3b): one `L ≠ 0` with `L^N y` integral over `A` for every `y`;
* `mem_adjoin_wm` (Gen): `Γ(W₁) = B'[Γ(W)]` along a chart map `d` with `d.left = Spec.map ι`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap

open scoped nonZeroDivisors

universe u

section Gam

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec (CommRingCat.of A)) [Etale g]

theorem gamAlg_algebraMap : @algebraMap A Γ(X, ⊤) _ _ (gamAlg g) = gamMap g := rfl

end Gam

section Gen

end Gen

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

end ChG

section Sec

end Sec

section Gam

theorem appTop_gamMap {A : Type} [CommRing A] {X₁ X₂ : Scheme.{0}} [IsAffine X₁] [IsAffine X₂] (hm : X₁ ⟶ X₂)
    (g₂ : X₂ ⟶ Spec (CommRingCat.of A)) [Etale g₂] (g₁ : X₁ ⟶ Spec (CommRingCat.of A)) [Etale g₁]
    (hg : hm ≫ g₂ = g₁) (r : A) : hm.appTop (gamMap g₂ r) = gamMap g₁ r := by
  subst hg
  show (((Scheme.ΓSpecIso _).inv ≫ g₂.appTop) ≫ hm.appTop).hom r = ((Scheme.ΓSpecIso _).inv ≫ (hm ≫ g₂).appTop).hom r
  rfl

end Gam

end RamanujanPetersson.EtPBC.EtKum

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

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.GalTrE RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.FreeStk

universe u

section GraphGeo

variable {P : Scheme.{u}} {W' W T : P.Etale}

theorem isClosed_graphMeet [IsSeparated T.hom] (m m' : W ⟶ T) : IsClosed (graphMeet m m') :=
  (isClosed_range_sec (graph m')).preimage (graph m).left.continuous

end GraphGeo

end RamanujanPetersson.EtPBC.EtMV

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

end BadCh

section BadCh2

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {G Gb : k[X]} {b : k} {m : ℕ}
  (hGf : G = (X - C b) ^ m * Gb)

/-- **`hDn`**: `D_{G_b}` has a point over `c(b)` when `G_b(b) ≠ 0`. -/
theorem badCh_n (hb : Gb.eval b ≠ 0) :
    Nonempty ((geomPtAt (c (A1pt k b))).point.fiber.obj (chEt c (locF (B := CommRingCat.of k[X]) Gb))) := by
  have hr := PrimeSpectrum.localization_away_comap_range (Localization.Away Gb) Gb
  have hq : A1pt k b ∈ Set.range (PrimeSpectrum.comap (algebraMap k[X] (Localization.Away Gb))) := by
    rw [hr]
    intro hm
    have h1 : X - C b ∣ Gb := Ideal.mem_span_singleton.1 hm
    rw [dvd_iff_isRoot] at h1
    exact hb h1
  obtain ⟨w, hw⟩ := hq
  exact nonempty_fib_of_mem (chEt c (locF (B := CommRingCat.of k[X]) Gb)) _ w (by rw [← hw]; rfl)

end BadCh2

section JAlg

end JAlg

end RamanujanPetersson.EtPBC.EtKum

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

end Alg

section Chart

variable {k : Type u} [Field k] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{u}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)]

theorem chEt_hom_eq_of_mem (a : k) (v : (chEt c φ).left) (hv : φ.hom (X - C a) ∈ v.asIdeal) :
    (chEt c φ).hom v = c (A1pt k a) := by
  show c (Spec.map φ v) = c (A1pt k a)
  congr 1
  apply PrimeSpectrum.ext
  show v.asIdeal.comap φ.hom = Ideal.span {X - C a}
  have : v.asIdeal.IsPrime := v.isPrime
  exact span_X_sub_C_eq_of_mem a _ hv

end Chart

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB1 =====
section

/-!
# S4-EtPBC-A, L3a (TB1): pulled-back sections

* `pbSec f x`: the section `f^* x` of `f^* F` over `f⁻¹ V` (unit of `f^* ⊣ f_*`);
* `pbSec_natural`, `pbSec_restrict`: naturality in `F` and in `V`;
* `pbSec_comp`: `pullCompIso` sends `(g ≫ f)^* x` to `g^* f^* x` (restricted along `etPullCompIso`);
* `pbSec_res`: for etale `g`, `pullIsoRes` sends `g^* x` to `x` restricted along the counit of `etComp ⊣ etPull`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC

universe u

section Pb

variable {Λ : Type u} [CommRing Λ]

theorem pbSec_natural {X Y : Scheme.{u}} (f : X ⟶ Y) {F G : EtSh Λ Y} (φ : F ⟶ G) {V : Y.Etale}
    (x : F.obj.obj (op V)) :
    pbSec f ((φ.hom.app (op V)).hom x) =
      (((pull f Λ).map φ).hom.app (op ((etPull f).obj V))).hom (pbSec f x) :=
  congrArg (fun ψ => (ψ.hom.app (op V)).hom x) ((pullAdj f Λ).unit.naturality φ)

theorem pbSec_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) {F : EtSh Λ Y} {V V' : Y.Etale} (r : V' ⟶ V)
    (x : F.obj.obj (op V)) :
    pbSec f ((F.obj.map r.op).hom x) =
      ((((pull f Λ).obj F).obj.map ((etPull f).map r).op).hom (pbSec f x)) :=
  congrArg (fun ψ => ψ.hom x) (((pullAdj f Λ).unit.app F).hom.naturality r.op)

theorem pbSec_comp {W X Y : Scheme.{u}} (g : W ⟶ X) (f : X ⟶ Y) {F : EtSh Λ Y} {V : Y.Etale}
    (x : F.obj.obj (op V)) :
    (((pullCompIso Λ g f).hom.app F).hom.app (op ((etPull (g ≫ f)).obj V))).hom (pbSec (g ≫ f) x) =
      (((pull g Λ).obj ((pull f Λ).obj F)).obj.map ((etPullCompIso g f).hom.app V).op).hom
        (pbSec g (pbSec f x)) := by
  have h := congrArg (fun ψ => (ψ.hom.app (op V)).hom x)
    (Adjunction.unit_leftAdjointUniq_hom_app (pullAdj (g ≫ f) Λ)
      (((pullAdj f Λ).comp (pullAdj g Λ)).ofNatIsoRight (pushCompIso Λ g f)) F)
  have hu : (((pullAdj f Λ).comp (pullAdj g Λ)).ofNatIsoRight (pushCompIso Λ g f)).unit.app F =
      ((pullAdj f Λ).comp (pullAdj g Λ)).unit.app F ≫ (pushCompIso Λ g f).hom.app _ := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
  rw [hu, Adjunction.comp_unit_app] at h
  exact h

theorem pbSec_res {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {F : EtSh Λ X} {V : X.Etale}
    (x : F.obj.obj (op V)) :
    (((pullIsoRes g Λ).hom.app F).hom.app (op ((etPull g).obj V))).hom (pbSec g x) =
      (F.obj.map ((etCompAdj g).counit.app V).op).hom x := by
  have h := congrArg (fun ψ => (ψ.hom.app (op V)).hom x)
    (Adjunction.unit_leftAdjointUniq_hom_app (pullAdj g Λ) (resAdj g Λ) F)
  exact h

end Pb

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L5a =====
section

/-!
# S4-EtPBC-A, L5a (Geo1): the horizontal section through a closed point of `P¹_K`

`K` algebraically closed, `z` a closed point of `P¹_K`:
* `pt_factor`: a morphism `Spec Ω ⟶ X` hitting `z` factors through the `K`-point of `z` (`pointOfClosedPoint`);
* `σz : S ⟶ P¹_S`, `t ↦ (z, t)`, a section of `qV` (`σz_qV`, `σz_pr`);
* **`geom_factor`**: a morphism `x : Spec Ω ⟶ P¹_S` with `pr (x pt) = z` is `(x ≫ qV) ≫ σz`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.Z3

universe u

section PtFactor

end PtFactor

section Sec

variable (K : Type u) [Field K] [IsAlgClosed K] {S : Scheme.{u}} (gS : S ⟶ Spec (CommRingCat.of K))
  (z : P1 K) (hz : IsClosed ({z} : Set (P1 K)))

/-- The `K`-point of the closed point `z`. -/
abbrev ptz : Spec (CommRingCat.of K) ⟶ P1 K := pointOfClosedPoint (P1.toSpecK K) z hz

end Sec

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

instance lft_chEt : LocallyOfFiniteType ((chEt c φ).hom ≫ P1.toSpecK K) := by
  change LocallyOfFiniteType ((Spec.map φ ≫ c) ≫ P1.toSpecK K)
  infer_instance

end Pt

section Fib

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end


