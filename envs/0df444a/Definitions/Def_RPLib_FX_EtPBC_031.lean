-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_031
-- name    : RPLib_FX_EtPBC_031
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T19:28:51.638008+00:00
-- url     : https://prove2.me/theorems/f913f93a-6136-5ddb-8531-9c142d3834a7
-- title:
--   Proper base change for the projective line, library file 031
-- statement:
--   File 031 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovL1`: S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map
--   * `S4.Def_RP_EtPBC_A_CovPr11`: S4-EtPBC-A, R4-T2 (A3k): the residue map of an approximated presentation
--   * `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
--   * `S4.Def_RP_EtPBC_A_CovLim2`: S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level
--   * `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
--   * `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
--   * `S4.Def_RP_EtPBC_A_CovAsN3`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN3): the adic completion of a noetherian ring is noetherian
--   * `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
--   * `S4.Def_RP_EtPBC_A_CovAs6c`: S4-EtPBC-A, R4-T2 (A3 assembly, As6c): residue maps of the approximated overlap, generic identities
--   * `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
--   * `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
--   * `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
--   * `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
--   * `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
--   * `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
--   * `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
--   * `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
--   * `S4.Def_RP_EtPBC_A_T3dA`: S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--   * `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
--   * `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
--   * `S4.Def_RP_EtPBC_A_CovNbA`: S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed
--   * `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
--   * `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
--   * `S4.Def_RP_EtPBC_A_CovNbB`: S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`
--   * `S4.Def_RP_EtPBC_A_O2Ap1`: S4-EtPBC-A, O2 M6 (O2Ap1): approximating a function on an etale neighbourhood by a function from below
--   * `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
--   * `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
--   * `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
--   * `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
--   * `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
--   * `S4.Def_RP_EtPBC_A_O2E8`: S4-EtPBC-A, O2 C-plan S4d2 (Ext level): purity for `Ext¹(Λ[W₁], Λ_P)`, and changing `Uo` to `Uz`
--   * `S4.Def_RP_EtPBC_A_O2Th1c`: S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`
--   * `S4.Def_RP_EtPBC_A_O2Km1`: S4-EtPBC-A, O2 M6 (O2Km1): the Shapiro scheme `W = D_o ×_P R` is affine
--   * `S4.Def_RP_EtPBC_A_O2Pb`: S4-EtPBC-A, O2 GLOB (O2Pb): the pullback square of `wm (prdMap d X)` and what it gives on global sections
--   * `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
--   * `S4.Def_RP_EtPBC_A_O2Gl2d`: S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`
--   * `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
--   * `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
--   * `S4.Def_RP_EtPBC_A_O2Bd2`: S4-EtPBC-A, O2 REL (O2Bd2): `H = 1 + t_i e` on every piece at a bad point
--   * `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
--   * `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
--   * `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
--   * `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
--   * `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_014
import Definitions.Def_RPLib_FX_EtPBC_023
import Definitions.Def_RPLib_FX_EtPBC_027

/-!
# Proper base change for the projective line, library file 031

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovL1`: S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map
* `S4.Def_RP_EtPBC_A_CovPr11`: S4-EtPBC-A, R4-T2 (A3k): the residue map of an approximated presentation
* `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
* `S4.Def_RP_EtPBC_A_CovLim2`: S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level
* `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
* `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
* `S4.Def_RP_EtPBC_A_CovAsN3`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN3): the adic completion of a noetherian ring is noetherian
* `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
* `S4.Def_RP_EtPBC_A_CovAs6c`: S4-EtPBC-A, R4-T2 (A3 assembly, As6c): residue maps of the approximated overlap, generic identities
* `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
* `S4.Def_RP_EtPBC_A_Z4FibB`: S4-EtPBC-A, (Z) geometric layer 12 (G-f, part 2): residue maps and the comparison map `Y_x ⟶ Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovY`: S4-EtPBC-A, R4-T2 (G1b): affine charts of `Y_{V'} = Y ×_V Spec R'`
* `S4.Def_RP_EtPBC_A_Psi`: S4-EtPBC-A, M2 F4: values of germs of `π_* C` along the fibre
* `S4.Def_RP_EtPBC_A_VLoc`: S4-EtPBC-A, M2 F6b: the value function of a section of `ι^* π_* C` on `Ω`-points of `Y ×_P X`
* `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
* `S4.Def_RP_EtPBC_A_DescG1`: S4-EtPBC-A, R4-T1b (geometric part 1): the descent datum of an extension on an affine chart
* `S4.Def_RP_EtPBC_A_DescG2`: S4-EtPBC-A, R4-T1c (part 1): the descended algebras form a coequifibered presheaf on affine opens
* `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
* `S4.Def_RP_EtPBC_A_T3dA`: S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
* `S4.Def_RP_EtPBC_A_DescK1`: S4-EtPBC-A, R4-T1e (part 1): a section over `T` splits the extension over `T`
* `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
* `S4.Def_RP_EtPBC_A_CovNbA`: S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed
* `S4.Def_RP_EtPBC_A_EY`: S4-EtPBC-A, M4(E), EY: the finite cover `Y` and the sections of `Spec κ(ξ) ×_P W`
* `S4.Def_RP_EtPBC_A_EF`: S4-EtPBC-A, M4(E), EF: relations of the generators hold for the sections `f_j`
* `S4.Def_RP_EtPBC_A_CovNbB`: S4-EtPBC-A, R4-T2 (G2): the cover lifting property at a neighbourhood gives `LiftT`
* `S4.Def_RP_EtPBC_A_O2Ap1`: S4-EtPBC-A, O2 M6 (O2Ap1): approximating a function on an etale neighbourhood by a function from below
* `S4.Def_RP_EtPBC_A_O2S2`: S4-EtPBC-A, O2 C-plan S2: shrinking one-point MV classes; restricted classes die
* `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
* `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
* `S4.Def_RP_EtPBC_A_O2N4`: S4-EtPBC-A, O2 M5 P0: `resMapX` on ring elements (the bridge to field-level Kummer data)
* `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
* `S4.Def_RP_EtPBC_A_O2E8`: S4-EtPBC-A, O2 C-plan S4d2 (Ext level): purity for `Ext¹(Λ[W₁], Λ_P)`, and changing `Uo` to `Uz`
* `S4.Def_RP_EtPBC_A_O2Th1c`: S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`
* `S4.Def_RP_EtPBC_A_O2Km1`: S4-EtPBC-A, O2 M6 (O2Km1): the Shapiro scheme `W = D_o ×_P R` is affine
* `S4.Def_RP_EtPBC_A_O2Pb`: S4-EtPBC-A, O2 GLOB (O2Pb): the pullback square of `wm (prdMap d X)` and what it gives on global sections
* `S4.Def_RP_EtPBC_A_O2Gl2b`: S4-EtPBC-A, O2 GLOB (O2Gl2b): the charts of stage S3
* `S4.Def_RP_EtPBC_A_O2Gl2d`: S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`
* `S4.Def_RP_EtPBC_A_O2T6`: S4-EtPBC-A, O2 S5f: geometry of graphs of sections
* `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
* `S4.Def_RP_EtPBC_A_O2Bd2`: S4-EtPBC-A, O2 REL (O2Bd2): `H = 1 + t_i e` on every piece at a bad point
* `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
* `S4.Def_RP_EtPBC_A_O2TB2a`: S4-EtPBC-A, L3b (TB2a): section calculus for base change
* `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
* `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
* `S4.Def_RP_EtPBC_A_O2L6b2`: S4-EtPBC-A, L6b2: the `D` side of the comparison on `P¹_K`
-/

set_option autoImplicit false

set_option linter.defProp false

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

theorem isNilpotent_ker_red (hg0 : ∀ a : e₀, g a = 0 → ∃ k : ℕ, τ ^ k * a = 0)
    (hk : IsNilpotent (RingHom.ker f₀)) : IsNilpotent (RingHom.ker (red N t₀ f₀ g τ hτ hu)) := by
  rw [red_ker N t₀ f₀ g τ hτ hu hg0]
  exact NilLift.isNilpotent_map _ hk

end Red

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr11 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3k): the residue map of an approximated presentation

Setting: a square system `gC` over `Cc`, pushed to `S` (the completed side, `fh`) and to `S'` (the approximated
side, `f'`); `θh : Pres (gmap fh gC) → Q` a ring map (in the application surjective, kernel `p · Pres`).
* `pres_eval_self`: a ring map out of `Pres g` evaluates polynomials through its values on constants and variables.
* **`resid fh f' gC θh κ' hκ : Pres (gmap f' gC) →+* Q`**: coefficients by `κ'`, variables to `θh (Z j)`; it exists
  as soon as `κ' ∘ f' = θh ∘ algebraMap ∘ fh` (`resid_hz`). `resid_algebraMap`, `resid_X`, `resid_comp_presMap`.
* **`resid_surj`**: surjective if `θh` is and `κ'` reaches the constants of `θh`.
* **`resid_ker`** (headline): `ker (resid ..) = J · Pres (gmap f' gC)` from a map `q` out of `Pres (gmap f' gC)` with
  kernel in `J · Pres`, a coefficient map `lam : S → T` killing `I` (`ker θh = I · Pres (gmap fh gC)`) and sections.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Gen

end Gen

variable {Cc S S' : Type u} [CommRing Cc] [CommRing S] [CommRing S'] {r : ℕ} {Q : Type u} [CommRing Q]

variable (fh : Cc →+* S) (f' : Cc →+* S') (gC : Fin r → MvPolynomial (Fin r) Cc) (θh : Pres (gmap fh gC) →+* Q)
  (κ' : S' →+* Q) (hκ : κ'.comp f' = (θh.comp (algebraMap S (Pres (gmap fh gC)))).comp fh)

theorem resid_algebraMap (a : S') : resid fh f' gC θh κ' hκ (algebraMap S' (Pres (gmap f' gC)) a) = κ' a :=
  presLift_algebraMap _ _ _ _ a

theorem resid_X (j : Fin r) :
    resid fh f' gC θh κ' hκ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = θh (Ideal.Quotient.mk _ (MvPolynomial.X j)) :=
  presLift_X _ _ _ _ j

theorem resid_comp_presMap : (resid fh f' gC θh κ' hκ).comp (presMap f' gC) = θh.comp (presMap fh gC) := by
  apply pres_ringHom_ext
  · intro c
    exact (congrArg (resid fh f' gC θh κ' hκ) (presMap_algebraMap f' gC c)).trans
      ((resid_algebraMap fh f' gC θh κ' hκ (f' c)).trans
        ((RingHom.congr_fun hκ c).trans (congrArg θh (presMap_algebraMap fh gC c)).symm))
  · intro j
    exact (congrArg (resid fh f' gC θh κ' hκ) (presMap_X f' gC j)).trans
      ((resid_X fh f' gC θh κ' hκ j).trans (congrArg θh (presMap_X fh gC j)).symm)

theorem resid_surj (hθ : Function.Surjective θh)
    (hcov : ∀ s : S, ∃ a : S', κ' a = θh (algebraMap S (Pres (gmap fh gC)) s)) :
    Function.Surjective (resid fh f' gC θh κ' hκ) := by
  have key : ∀ x : MvPolynomial (Fin r) S, θh (Ideal.Quotient.mk _ x) ∈ (resid fh f' gC θh κ' hκ).range := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C s =>
      obtain ⟨a, ha⟩ := hcov s
      exact RingHom.mem_range.mpr ⟨algebraMap S' _ a, (resid_algebraMap fh f' gC θh κ' hκ a).trans ha⟩
    | add p q hp hq =>
      simp only [map_add]
      exact add_mem hp hq
    | mul_X p j hp =>
      simp only [map_mul]
      exact mul_mem hp (RingHom.mem_range.mpr ⟨_, resid_X fh f' gC θh κ' hκ j⟩)
  intro y
  obtain ⟨x, rfl⟩ := hθ y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact key p

/-- **Kernel of the residue map** (abstract target `T`, so no quotient of a quotient is elaborated here): if `q`
has kernel inside `J · Pres (gmap f' gC)`, then `ker (resid ..) = J · Pres (gmap f' gC)`. -/
theorem resid_ker (hθ : Function.Surjective θh) (J : Ideal S') (hJ : ∀ a ∈ J, κ' a = 0)
    {T : Type u} [CommRing T] (q : Pres (gmap f' gC) →+* T)
    (hq : RingHom.ker q ≤ J.map (algebraMap S' (Pres (gmap f' gC))))
    (lam : S →+* T) (hlam : ∀ c, lam (fh c) = q (algebraMap S' (Pres (gmap f' gC)) (f' c)))
    (I : Ideal S) (hI : RingHom.ker θh = I.map (algebraMap S (Pres (gmap fh gC)))) (hlamI : I ≤ RingHom.ker lam)
    (hsec : ∀ a : S', ∃ s : S, θh (algebraMap S (Pres (gmap fh gC)) s) = κ' a ∧
      lam s = q (algebraMap S' (Pres (gmap f' gC)) a)) :
    RingHom.ker (resid fh f' gC θh κ' hκ) = J.map (algebraMap S' (Pres (gmap f' gC))) := by
  have hev : ∀ p : MvPolynomial (Fin r) Cc, MvPolynomial.eval₂ (lam.comp fh)
      (fun i => q (Ideal.Quotient.mk _ (MvPolynomial.X i))) p = q (Ideal.Quotient.mk _ (MvPolynomial.map f' p)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂_C, RingHom.comp_apply, hlam, MvPolynomial.map_C]
      try rfl
    | add p q' hp hq' =>
      simp only [MvPolynomial.eval₂_add, hp, hq', map_add]
    | mul_X p j hp =>
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hp, map_mul, MvPolynomial.map_X]
  have hzφ : ∀ j, MvPolynomial.eval₂ lam (fun i => q (Ideal.Quotient.mk _ (MvPolynomial.X i))) (gmap fh gC j) = 0 :=
    fun j => by
      have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (gmap f' gC))) (MvPolynomial.map f' (gC j)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
      exact (eval₂_gmap fh gC lam _ j).trans ((hev (gC j)).trans ((congrArg q h0).trans (map_zero q)))
  let φ := presLift (gmap fh gC) lam (fun i => q (Ideal.Quotient.mk _ (MvPolynomial.X i))) hzφ
  have hk : RingHom.ker θh ≤ RingHom.ker φ := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap]
    exact RingHom.mem_ker.mpr ((presLift_algebraMap _ lam _ hzφ s).trans (RingHom.mem_ker.mp (hlamI hs)))
  let ρ : Q →+* T :=
    (Ideal.Quotient.lift (RingHom.ker θh) φ (fun a ha => RingHom.mem_ker.mp (hk ha))).comp
      (RingHom.quotientKerEquivOfSurjective hθ).symm.toRingHom
  have hρ : ∀ x, ρ (θh x) = φ x := fun x => by
    have e : (RingHom.quotientKerEquivOfSurjective hθ).symm (θh x) = Ideal.Quotient.mk _ x :=
      (RingEquiv.symm_apply_eq _).mpr (RingHom.quotientKerEquivOfSurjective_apply_mk hθ x).symm
    first
      | (simp only [ρ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
          Ideal.Quotient.lift_mk])
      | (show Ideal.Quotient.lift (RingHom.ker θh) φ _ ((RingHom.quotientKerEquivOfSurjective hθ).symm (θh x)) = φ x
         rw [e, Ideal.Quotient.lift_mk])
  have hρq : ρ.comp (resid fh f' gC θh κ' hκ) = q := by
    apply pres_ringHom_ext
    · intro a
      obtain ⟨s, h1, h2⟩ := hsec a
      exact (congrArg ρ ((resid_algebraMap fh f' gC θh κ' hκ a).trans h1.symm)).trans
        ((hρ _).trans ((presLift_algebraMap _ lam _ hzφ s).trans h2))
    · intro j
      exact (congrArg ρ (resid_X fh f' gC θh κ' hκ j)).trans ((hρ _).trans (presLift_X _ lam _ hzφ j))
  refine le_antisymm (fun x hx => hq ?_) ?_
  · rw [RingHom.mem_ker] at hx ⊢
    exact (RingHom.congr_fun hρq x).symm.trans ((congrArg ρ hx).trans (map_zero ρ))
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, resid_algebraMap]
    exact hJ a ha

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

theorem TwoCov.PI_eval (hv : C.u * C.ψ₁ (C.a₁ τ₁) = 1) {x : C.E₀} (h : C.PI I d x) (c : R[X]) :
    C.PI I d (eval₂ ι₀ (C.a₀ τ₀) c * x) := by
  induction c using Polynomial.induction_on with
  | C a =>
    rw [eval₂_C]
    exact TwoCov.PI_C ι₀ ι₁ hι a h
  | add p q hp hq =>
    rw [eval₂_add, add_mul]
    exact TwoCov.PI_add hp hq
  | monomial k a hk =>
    have e : eval₂ ι₀ (C.a₀ τ₀) (Polynomial.C a * X ^ (k + 1)) * x =
        C.a₀ τ₀ * (eval₂ ι₀ (C.a₀ τ₀) (Polynomial.C a * X ^ k) * x) := by
      simp only [eval₂_mul, eval₂_C, eval₂_X_pow]
      ring
    rw [e]
    exact TwoCov.PI_t hv hk

end Good

section Zero

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

theorem lev_add (m : ℕ) (c c' : Fin r → R) :
    lev C ιB₀ ιB₁ σ m (c + c') = lev C ιB₀ ιB₁ σ m c + lev C ιB₀ ιB₁ σ m c' := by
  refine Prod.ext ?_ ?_
  · simp only [lev_fst, Prod.fst_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  · simp only [lev_snd, Prod.snd_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem lev_sub (m : ℕ) (c c' : Fin r → R) :
    lev C ιB₀ ιB₁ σ m (c - c') = lev C ιB₀ ιB₁ σ m c - lev C ιB₀ ιB₁ σ m c' := by
  refine Prod.ext ?_ ?_
  · simp only [lev_fst, Prod.fst_sub, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  · simp only [lev_snd, Prod.snd_sub, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lev_zero (m : ℕ) : lev C ιB₀ ιB₁ σ m 0 = 0 := by
  refine Prod.ext ?_ ?_
  · simp [lev_fst]
  · simp [lev_snd]

/-- Combinations with coefficients `∑ᵢ αᵢ cᵢ`. -/
theorem lev_comb {g : ℕ} (α : Fin g → R) (m : ℕ) (c : Fin g → Fin r → R) :
    lev C ιB₀ ιB₁ σ m (fun l => ∑ i, α i * c i l) =
      ∑ i, (lι₀ ιB₀ (C m) (α i) * (lev C ιB₀ ιB₁ σ m (c i)).1,
        lι₁ ιB₁ (C m) (α i) * (lev C ιB₀ ιB₁ σ m (c i)).2) := by
  refine Prod.ext ?_ ?_
  · simp only [lev_fst, Prod.fst_sum, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  · simp only [lev_snd, Prod.snd_sum, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

end Lev

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat5 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations

* `ιP : R →+* ∏E₀ × ∏E₁`, `ιh₀ = β₀ ∘ ιB₀`, `ιh₁ = β₁ ∘ ιB₁`, **`levF_eq`** (`levF σ a = ∑ ιP (aᵢ) σᵢ`),
  **`frac₀_lin`**, **`frac₁_lin`**: fractions of `R`-combinations are combinations of fractions.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lin

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- **`levF σ a = ∑ ιP (aᵢ) σᵢ`.** -/
theorem levF_eq {r : ℕ} (σ : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)) (a : Fin r → R) :
    levF C ιB₀ ιB₁ σ a = ∑ i, ιP C ιB₀ ιB₁ (a i) * σ i := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · show (lev C ιB₀ ιB₁ σ k a).1 = (∑ i, ιP C ιB₀ ιB₁ (a i) * σ i).1 k
    rw [lev_fst, Prod.fst_sum, Finset.sum_apply]
    rfl
  · show (lev C ιB₀ ιB₁ σ k a).2 = (∑ i, ιP C ιB₀ ιB₁ (a i) * σ i).2 k
    rw [lev_snd, Prod.snd_sum, Finset.sum_apply]
    rfl

end Lin

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

theorem evalₐ_hatPhi (n : ℕ) (F : MvPowerSeries σ A) :
    AdicCompletion.evalₐ (Ideal.span (Set.range a)) n (hatPhi a F) =
      Ideal.Quotient.mk _ (MvPolynomial.aeval a (truncTotal n F)) :=
  AdicCompletion.evalₐ_liftRingHom _ _ _ n F

theorem hatPhi_X (i : σ) :
    hatPhi a (X i) = algebraMap A (AdicCompletion (Ideal.span (Set.range a)) A) (a i) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_hatPhi, AlgHom.commutes, Ideal.Quotient.algebraMap_eq]
  refine (mk_aeval_eq a (truncTotal n (X i)) (MvPolynomial.X i) fun x hx => ?_).trans
    (by rw [MvPolynomial.aeval_X])
  rw [coeff_truncTotal _ hx, ← MvPolynomial.coe_X, MvPolynomial.coeff_coe]

theorem hatPhi_C (c : A) :
    hatPhi a (C c) = algebraMap A (AdicCompletion (Ideal.span (Set.range a)) A) c := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_hatPhi, AlgHom.commutes, Ideal.Quotient.algebraMap_eq]
  refine (mk_aeval_eq a (truncTotal n (C c)) (MvPolynomial.C c) fun x hx => ?_).trans (by simp)
  rw [coeff_truncTotal _ hx, ← MvPolynomial.coe_C, MvPolynomial.coeff_coe]

end HatN1

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAsN3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, AsN3): the adic completion of a noetherian ring is noetherian

* `map_Xid_hatPhi`: `(X_σ).map hatPhi = p Â`.
* `hatPhi_surjective` (`p = span (range a)` f.g.): `hatPhi a` is surjective
  (`surjective_of_mk_map_comp_surjective`, `isPrecomplete_Xid`, `ker_evalOneₐ_eq_map`).
* `hat_noeth_of_gen`, **`hat_noeth`**: `IsNoetherianRing (AdicCompletion p A)` for `A` noetherian.
-/

set_option autoImplicit false

open MvPowerSeries

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u v

section HatN3

variable {A : Type u} [CommRing A] {σ : Type v} [Fintype σ] (a : σ → A)

theorem map_Xid_hatPhi :
    (Xid σ A).map (hatPhi a) =
      (Ideal.span (Set.range a)).map (algebraMap A (AdicCompletion (Ideal.span (Set.range a)) A)) := by
  rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
  congr 2
  funext i
  exact hatPhi_X a i

end HatN3

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

theorem presN_bij (t : P) (hf : IsAwayMap f t) (hu : IsUnit (f t))
    (hθ : θ.comp (algebraMap P (Pres g)) = bN.comp f) (hb : IsAwayMap θ (algebraMap P (Pres g) t)) :
    Function.Bijective (presN f g bN θ hθ) :=
  away_bij (presMap f g) θ (algebraMap P (Pres g) t) (presMap_away f t hf g) hb
    (by rw [presMap_algebraMap]; exact hu.map _) (presN f g bN θ hθ) (presN_presMap f g bN θ hθ)

/-- **The overlap is presented by the base-changed system.** -/
theorem exists_presN {E : Type u} [CommRing E] (t : P) (hf : IsAwayMap f t) (hu : IsUnit (f t)) (b : P →+* E)
    (q : E →+* E') (hq : q.comp b = bN.comp f) (aw : IsAwayMap q (b t)) (e : Pres g ≃+* E)
    (he : ∀ a, e (algebraMap P (Pres g) a) = b a) :
    ∃ eN : Pres (gmap f g) ≃+* E', (∀ a, eN (algebraMap P' (Pres (gmap f g)) a) = bN a) ∧
      ∀ x, eN (presMap f g x) = q (e x) := by
  have hθ : (q.comp (e : Pres g →+* E)).comp (algebraMap P (Pres g)) = bN.comp f := by
    refine RingHom.ext fun a => ?_
    show q (e (algebraMap P (Pres g) a)) = bN (f a)
    rw [he]
    exact DFunLike.congr_fun hq a
  exact ⟨RingEquiv.ofBijective (presN f g bN (q.comp (e : Pres g →+* E)) hθ)
      (presN_bij f g bN (q.comp (e : Pres g →+* E)) t hf hu hθ (awayMap_of_equiv g q b t aw e he)),
    fun a => presN_algebraMap f g bN (q.comp (e : Pres g →+* E)) hθ a,
    fun x => presN_presMap f g bN (q.comp (e : Pres g →+* E)) hθ x⟩

end PresN

section Subst

end Subst

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs6c =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As6c): residue maps of the approximated overlap, generic identities

* `resid_mk_map`: `resid` on the class of `map f' w` is `θh` on the class of `map fh w`.
* `comp_presMap_X`: from `θ' ∘ presMap f' = θh ∘ presMap fh`, the values on the variables agree.
* `kap_comp_tsC`: the coefficient hypothesis of `resid` for `fh = tvC B C`, `f' = tsC σ B`, `κ' = kap`.
* `phib_K`, `fib_coeff`: the fibre gluing maps are `K`-linear, and the coefficient identity of `ctheta0`/`ctheta1`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open TensorProduct

universe u

section ResidMap

variable {Cc S S' : Type u} [CommRing Cc] [CommRing S] [CommRing S'] {r : ℕ} {Q : Type u} [CommRing Q]
  (fh : Cc →+* S) (f' : Cc →+* S') (gC : Fin r → MvPolynomial (Fin r) Cc) (θh : Pres (gmap fh gC) →+* Q)
  (κ' : S' →+* Q) (hκ : κ'.comp f' = (θh.comp (algebraMap S (Pres (gmap fh gC)))).comp fh)

theorem resid_mk_map (w : MvPolynomial (Fin r) Cc) :
    resid fh f' gC θh κ' hκ (Ideal.Quotient.mk _ (MvPolynomial.map f' w)) =
      θh (Ideal.Quotient.mk _ (MvPolynomial.map fh w)) := by
  have h1 : ((resid fh f' gC θh κ' hκ).comp (algebraMap S' (Pres (gmap f' gC)))).comp f' =
      (θh.comp (algebraMap S (Pres (gmap fh gC)))).comp fh := by
    rw [← hκ]
    exact RingHom.ext fun c => resid_algebraMap fh f' gC θh κ' hκ (f' c)
  have h2 : (fun j => resid fh f' gC θh κ' hκ (Ideal.Quotient.mk _ (MvPolynomial.X j))) =
      (fun j => θh (Ideal.Quotient.mk _ (MvPolynomial.X j))) := funext (resid_X fh f' gC θh κ' hκ)
  rw [← pres_eval_self (resid fh f' gC θh κ' hκ) (MvPolynomial.map f' w),
    ← pres_eval_self θh (MvPolynomial.map fh w), MvPolynomial.eval₂_map, MvPolynomial.eval₂_map, h1, h2]

end ResidMap

section CompX

end CompX

section Kap

end Kap

section Fib

end Fib

end RamanujanPetersson.EtPBC.Cov

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

theorem res_struct_hom (i : Fin 2) (h : Yc K gV π 0 ⊓ Yc K gV π 1 ≤ Yc K gV π i) :
    ac K gV i ≫ π.app (Qc K gV i) ≫ Y.presheaf.map (homOfLE h).op = strN K gV π := by
  rw [ac, Scheme.Hom.app_eq_appLE, ← Category.assoc, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map]

/-- `Γ(V)`-structure on `Γ(Y₀₁)`. -/
@[instance_reducible]
def algAN : Algebra Γ(V, ⊤) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) := (strN K gV π).hom.toAlgebra

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN

theorem tow0 : IsScalarTower Γ(V, ⊤) (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    change (π.app (Qc K gV 0)).hom ((ac K gV 0).hom a) =
      (π.app (Qc K gV 0)).hom (Polynomial.eval₂ (ac K gV 0).hom (tc K gV 0 1) (Polynomial.C a))
    rw [Polynomial.eval₂_C]

theorem tow1 : IsScalarTower Γ(V, ⊤) (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    change (π.app (Qc K gV 1)).hom ((ac K gV 1).hom a) =
      (π.app (Qc K gV 1)).hom (Polynomial.eval₂ (ac K gV 1).hom (tc K gV 1 0) (Polynomial.C a))
    rw [Polynomial.eval₂_C]

attribute [local instance] tow0 tow1

/-- The restriction `Γ(Y₀) → Γ(Y₀₁)` as a `Γ(V)[X]`-algebra map. -/
def φY0 : Γ(Y, Yc K gV π 0) →ₐ[Polynomial Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) where
  __ := (resY0 K gV π).hom
  commutes' _ := rfl

theorem algX0_X : algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X =
    π.app (Qc K gV 0) (tc K gV 0 1) := by
  change (π.app (Qc K gV 0)).hom (Polynomial.eval₂ (ac K gV 0).hom (tc K gV 0 1) Polynomial.X) = _
  rw [Polynomial.eval₂_X]

theorem algX1_X : algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X =
    π.app (Qc K gV 1) (tc K gV 1 0) := by
  change (π.app (Qc K gV 1)).hom (Polynomial.eval₂ (ac K gV 1).hom (tc K gV 1 0) Polynomial.X) = _
  rw [Polynomial.eval₂_X]

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

variable (x : Spec (CommRingCat.of K) ⟶ V)

variable (U : Y.Opens)

/-- **The kernel of `Γ(Y, U) → Γ(Y_x, fx⁻¹ U)` is `(ker x^*) Γ(Y, U)`** (`U` affine). -/
theorem ker_fx_app [IsAffine V] (hx : x ≫ gV = 𝟙 _) (hU : IsAffineOpen U) :
    RingHom.ker ((fx K gV π x).app U).hom = (RingHom.ker x.appTop.hom).map (strU K gV π U).hom := by
  have hinj := appLE_injective_of_eq (jT K gV π x U) (image_jT K gV π x U) (top_le_jT K gV π x U)
  have hker := pushout_inl_ker (isPushout_T K gV π x U hU) (appTop_surj K gV x hx)
  have hρ := ConcreteCategory.bijective_of_isIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge)
  ext b
  have key : ((jT K gV π x U).appLE (fx K gV π x ⁻¹ᵁ U) ⊤ (top_le_jT K gV π x U)).hom
      (((fx K gV π x).app U).hom b) =
      (kT K gV π x U).appTop.hom ((U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom b) :=
    congrArg (fun φ => φ.hom b) (jT_fx K gV π x U)
  have e1 : b ∈ RingHom.ker ((fx K gV π x).app U).hom ↔
      (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom b ∈ RingHom.ker (kT K gV π x U).appTop.hom := by
    rw [RingHom.mem_ker, RingHom.mem_ker, ← key]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      exact hinj (h.trans (map_zero _).symm)
  rw [e1, hker, ← strU_ρ, CommRingCat.hom_comp, ← Ideal.map_map, ← Ideal.mem_comap,
    Ideal.comap_map_of_bijective _ hρ]

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

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 algYV

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']
  (x : Spec (CommRingCat.of K) ⟶ V) (x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R'))
  (hx' : x' ≫ hV V R' = x)

theorem yxMap_fR (r : R') :
    (yxMap K gV π R' x x' hx').appTop (fR K gV π R' r) =
      (sx K gV π x).appTop (x'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv r)) := by
  have h := congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom r))
    (pullback.lift_snd (fx K gV π x) (sx K gV π x ≫ x')
      (by rw [Category.assoc, hx']; exact pullback.condition))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h

end Map

end RamanujanPetersson.EtPBC.Z3

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

include hA in
theorem chY_w : (Spec.map (CommRingCat.ofHom (S := R' ⊗[Γ(V, ⊤)] Γ(Y, U))
      Algebra.TensorProduct.includeRight.toRingHom) ≫ hU.fromSpec) ≫ π ≫ qV K gV =
    Spec.map (CommRingCat.ofHom (S := R' ⊗[Γ(V, ⊤)] Γ(Y, U)) Algebra.TensorProduct.includeLeftRingHom) ≫
      hV V R' := by
  rw [Category.assoc, fromSpec_str K gV π hU, ← hA, hV, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
    (CommRingCat.isPushout_tensorProduct Γ(V, ⊤) R' Γ(Y, U)).w]

end Chart

section Res

end Res

end RamanujanPetersson.EtPBC.Cov

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

/-- Values along the fibre are invariant under restriction. -/
theorem cval_res {j j' : Nbhd t} (a : j' ⟶ j) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj j.1)))
    (x : fib π t) :
    cval (((constSh Λ Y M).obj.map ((etPull π).map a.1).op).hom z) (fibToNbhd π t j' x) =
      cval z (fibToNbhd π t j x) :=
  (cval_map ((etPull π).map a.1) z (fibToNbhd π t j' x)).trans
    (congrArg (cval z) (congrArg (fun φ => φ.base x) (fibToNbhd_map π t a)))

/-- **Equal germs have equal values along the fibre.** -/
theorem cval_eq_of_germ_eq {j₁ j₂ : Nbhd t} (z₁ : (constSh Λ Y M).obj.obj (op ((etPull π).obj j₁.1)))
    (z₂ : (constSh Λ Y M).obj.obj (op ((etPull π).obj j₂.1)))
    (h : (t.point.toPresheafFiber j₁.1 j₁.2 ((push π Λ).obj (constSh Λ Y M)).obj).hom z₁ =
      (t.point.toPresheafFiber j₂.1 j₂.2 ((push π Λ).obj (constSh Λ Y M)).obj).hom z₂) (x : fib π t) :
    cval z₁ (fibToNbhd π t j₁ x) = cval z₂ (fibToNbhd π t j₂ x) := by
  have h3 := (germ_res π t (IsCofiltered.minToLeft j₁ j₂) z₁).trans
    (h.trans (germ_res π t (IsCofiltered.minToRight j₁ j₂) z₂).symm)
  obtain ⟨W, f, w, hw, hs⟩ := (t.point.toPresheafFiber_eq_iff' (IsCofiltered.min j₁ j₂).1
    (IsCofiltered.min j₁ j₂).2 _ _).1 h3
  let j₄ : Nbhd t := ⟨W, w⟩
  let a : j₄ ⟶ IsCofiltered.min j₁ j₂ := ⟨f, hw⟩
  have e1 := (cval_res π t a (((constSh Λ Y M).obj.map ((etPull π).map (IsCofiltered.minToLeft j₁ j₂).1).op).hom z₁)
    x).trans (cval_res π t (IsCofiltered.minToLeft j₁ j₂) z₁ x)
  have e2 := (cval_res π t a (((constSh Λ Y M).obj.map ((etPull π).map (IsCofiltered.minToRight j₁ j₂).1).op).hom z₂)
    x).trans (cval_res π t (IsCofiltered.minToRight j₁ j₂) z₂ x)
  refine e1.symm.trans (Eq.trans ?_ e2)
  exact congrArg (fun c => cval (M := M) (T := (etPull π).obj W) c (fibToNbhd π t j₄ x)) hs

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

theorem xMor_fibToNbhd {W : P.Etale} {U : X.Etale} (h : U ⟶ (etPull ι).obj W)
    (τ : Spec (CommRingCat.of Ω) ⟶ pullback π ι)
    (l : Spec (CommRingCat.of Ω) ⟶ pullback (pullback.snd π ι) U.hom) (hl : l ≫ pullback.fst _ _ = τ) :
    xMor ι π τ ≫ fibToNbhd π ((sigPt ι π τ).map ι)
        ⟨W, (fiberMapIso ι (sigPt ι π τ)).inv.app W ((sigPt ι π τ).point.fiber.map h (liftPt ι π τ l hl))⟩ =
      l ≫ kap ι π h := by
  apply pullback.hom_ext
  · have e1 := left_fiberMapIso_inv ι (sigPt ι π τ) W ((sigPt ι π τ).point.fiber.map h (liftPt ι π τ l hl))
    have e2 := liftOf_map_left' (sigPt ι π τ) h (liftPt ι π τ l hl)
    have e3 : kap ι π h ≫ pullback.fst W.hom π =
        pullback.snd (pullback.snd π ι) U.hom ≫ h.left ≫ pullback.fst W.hom ι := pullback.lift_fst _ _ _
    refine (Category.assoc _ _ _).trans ((fibToNbhd_comp_fst π ((sigPt ι π τ).map ι) _ (xMor ι π τ)
      (pullback.lift_snd _ _ _)).trans (e1.trans ?_))
    refine ((congrArg (· ≫ pullback.fst W.hom ι) (e2.trans (congrArg (· ≫ h.left)
      (liftPt_left ι π τ l hl)))).trans ?_).trans (Category.assoc _ _ _).symm
    exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans (congrArg (l ≫ ·) e3.symm)
  · have e4 : kap ι π h ≫ pullback.snd W.hom π =
        pullback.fst (pullback.snd π ι) U.hom ≫ pullback.fst π ι := pullback.lift_snd _ _ _
    refine (Category.assoc _ _ _).trans ((congrArg (xMor ι π τ ≫ ·) (fibToNbhd_snd π _ _)).trans
      ((pullback.lift_fst _ _ _).trans ?_))
    exact ((congrArg (· ≫ pullback.fst π ι) hl).symm.trans (Category.assoc _ _ _)).trans
      ((congrArg (l ≫ ·) e4.symm).trans (Category.assoc _ _ _).symm)

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

/-- `Y_s ⟶ Y_V` (definitionally `ysj` for a neighbourhood). -/
def ysV (hv : v ≫ hj = s.pt) : pullback π (fibι (qV K gK) s) ⟶ pullback (pullback.snd hj (qV K gK)) π :=
  pullback.lift (pullback.snd _ _ ≫ fibV K gK s hj v hv) (pullback.fst _ _) (ysV_cond K gK s π hj v hv)

theorem eYV_cond (hv : v ≫ hj = s.pt) :
    ysV K gK s π hj v hv ≫ piVV K gK π hj ≫ qV K (hj ≫ gK) =
      (pullback.snd π (fibι (qV K gK) s) ≫ pullback.snd (qV K gK) s.pt ≫ s.pt ≫ gK) ≫ xV K gK s v := by
  simp only [piVV_q, ysV, fibV, xV, pullback.lift_fst_assoc, pullback.lift_fst, Category.assoc, sg_inv_assoc]

/-- `Y_s ⟶ Y_x`. -/
def eYV (hv : v ≫ hj = s.pt) : pullback π (fibι (qV K gK) s) ⟶ Yx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) :=
  pullback.lift (ysV K gK s π hj v hv)
    (pullback.snd π (fibι (qV K gK) s) ≫ pullback.snd (qV K gK) s.pt ≫ s.pt ≫ gK) (eYV_cond K gK s π hj v hv)

theorem eY'V_cond (hv : v ≫ hj = s.pt) :
    (fx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ pullback.snd (pullback.snd hj (qV K gK)) π) ≫ π =
      fibW K gK s π hj v hv ≫ fibι (qV K gK) s := by
  rw [Category.assoc, ← pullback.condition (f := pullback.snd hj (qV K gK)) (g := π), fibW, pullback.lift_fst]

/-- `Y_x ⟶ Y_s`. -/
def eY'V (hv : v ≫ hj = s.pt) : Yx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ⟶ pullback π (fibι (qV K gK) s) :=
  pullback.lift (fx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ pullback.snd _ π) (fibW K gK s π hj v hv)
    (eY'V_cond K gK s π hj v hv)

section Ext

variable [IsAffine V] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

variable (x' : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R')) (v' : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of R'))

theorem ysV_ymapR (hv' : v' ≫ hV V R' = v) (hv : v ≫ hj = s.pt) :
    ysV K gK s π (hV V R' ≫ hj) v' (hvR s hj v R' v' hv' hv) ≫ ymapR K gK π hj R' =
      ysV K gK s π hj v hv := by
  apply pullback.hom_ext
  · simp only [ysV, ymapR, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      fibV_pmapR K gK s hj v R' v' hv' hv]
  · simp only [ysV, ymapR, Category.assoc, pullback.lift_snd]

/-- **The comparison square**: `ysV' ≫ kapV = eYV ≫ yxMap`. -/
theorem ysV_kapV (hx' : x' ≫ hV V R' = xV K gK s v) (hvx : (s.pt ≫ gK) ≫ x' = v') (hv : v ≫ hj = s.pt) :
    ysV K gK s π (hV V R' ≫ hj) v' (hvR s hj v R' v' (hv'_of K gK s v R' x' v' hx' hvx) hv) ≫
      kapV K gK π hj R' =
      eYV K gK s π hj v hv ≫ yxMap K (hj ≫ gK) (piVV K gK π hj) R' (xV K gK s v) x' hx' := by
  apply pullback.hom_ext
  · have e1 : kapV K gK π hj R' ≫ pullback.fst _ _ = ymapR K gK π hj R' := pullback.lift_fst _ _ _
    have e2 : yxMap K (hj ≫ gK) (piVV K gK π hj) R' (xV K gK s v) x' hx' ≫ pullback.fst _ _ =
        fx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) := pullback.lift_fst _ _ _
    have e3 : eYV K gK s π hj v hv ≫ fx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) = ysV K gK s π hj v hv :=
      pullback.lift_fst _ _ _
    rw [Category.assoc, Category.assoc, e1, e2, e3,
      ysV_ymapR K gK s π hj v R' v' (hv'_of K gK s v R' x' v' hx' hvx) hv]
  · have e1 : kapV K gK π hj R' ≫ pullback.snd _ _ = pullback.fst _ π ≫ pullback.fst _ (qV K gK) :=
      pullback.lift_snd _ _ _
    have e2 : yxMap K (hj ≫ gK) (piVV K gK π hj) R' (xV K gK s v) x' hx' ≫ pullback.snd _ _ =
        sx K (hj ≫ gK) (piVV K gK π hj) (xV K gK s v) ≫ x' := pullback.lift_snd _ _ _
    rw [Category.assoc, Category.assoc, e1, e2]
    simp only [eYV, ysV, fibV, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
      pullback.lift_fst]
    rw [← hvx, Category.assoc]

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

theorem isLocallyConstant_cU : IsLocallyConstant (cU σ τ hτ a b hab hS e he) :=
  isLocallyConstant_cval (dif a b hab hS e he (etS σ (C ⊗[A] C)) (kmap σ τ hτ (j1 A C)) (kmap σ τ hτ (j2 A C)))

theorem cU_diag (P : PrimeSpectrum C) :
    cU σ τ hτ a b hab hS e he
      (PrimeSpectrum.comap (Algebra.TensorProduct.lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom P) = 0 := by
  rw [cU, cval_comap, dif_map, homS_kmap, homS_kmap, Algebra.TensorProduct.lmul'_comp_includeLeft,
    Algebra.TensorProduct.lmul'_comp_includeRight, dif_self]
  exact cval_zero _

theorem cU_coc (P : PrimeSpectrum (C ⊗[A] (C ⊗[A] C))) :
    cU σ τ hτ a b hab hS e he (PrimeSpectrum.comap (e13 A C).toRingHom P) =
      cU σ τ hτ a b hab hS e he (PrimeSpectrum.comap (e12 A C).toRingHom P) +
        cU σ τ hτ a b hab hS e he (PrimeSpectrum.comap (e23 A C).toRingHom P) := by
  have a1 : (e13 A C).comp (j1 A C) = (e12 A C).comp (j1 A C) :=
    AlgHom.ext fun c => (e12_j1 A C c).symm
  have a2 : (e12 A C).comp (j2 A C) = (e23 A C).comp (j1 A C) :=
    AlgHom.ext fun c => by simp [Algebra.TensorProduct.map_tmul]
  have a3 : (e13 A C).comp (j2 A C) = (e23 A C).comp (j2 A C) :=
    AlgHom.ext fun c => by simp [Algebra.TensorProduct.map_tmul]
  rw [cU, cU, cU, cval_comap, cval_comap, cval_comap, dif_map, dif_map, dif_map]
  simp only [homS_kmap]
  rw [a1, a2, a3, dif_add (w₂ := kmap σ τ hτ ((e23 A C).comp (j1 A C)))]
  exact cval_add _ _ _

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

variable {X : Scheme.{u}} {A A' : Type u} [CommRing A] [CommRing A'] (σ : Spec (CommRingCat.of A) ⟶ X) [Etale σ]
  (σ' : Spec (CommRingCat.of A') ⟶ X) [Etale σ'] (ρA : A →+* A')
  (hσ : Spec.map (CommRingCat.ofHom ρA) ≫ σ = σ')

variable {C C' : Type u} [CommRing C] [Algebra A C] [Algebra.Etale A C] [CommRing C'] [Algebra A' C']
  [Algebra.Etale A' C'] {V : X.Etale}
  (τ : Spec (CommRingCat.of C) ⟶ V.left) (hτ : τ ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ σ)
  (τ' : Spec (CommRingCat.of C') ⟶ V.left)
  (hτ' : τ' ≫ V.hom = Spec.map (CommRingCat.ofHom (algebraMap A' C')) ≫ σ')
  (φC : C →+* C') (hφC : ∀ x, φC (algebraMap A C x) = algebraMap A' C' (ρA x))
  (hτφ : Spec.map (CommRingCat.ofHom φC) ≫ τ = τ')

variable {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q)
  (hab : a ≫ b = 0) (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

include hσ hτφ in
theorem cU_compat (P : PrimeSpectrum (C' ⊗[A'] C')) :
    cU σ' τ' hτ' a b hab hS e he P =
      cU σ τ hτ a b hab hS e he (PrimeSpectrum.comap (psiMap ρA φC hφC) P) := by
  rw [cU, cU, cval_comapX σ σ' ρA hσ (psiMap ρA φC hφC) (psiMap_algebraMap ρA φC hφC), dif_map,
    homX_kmap σ σ' ρA hσ τ hτ τ' hτ' φC hτφ _ _ (j1 A C) (j1 A' C') (psiMap_j1 ρA φC hφC),
    homX_kmap σ σ' ρA hσ τ hτ τ' hτ' φC hτφ _ _ (j2 A C) (j2 A' C') (psiMap_j2 ρA φC hφC)]

end Cross

section Pres

end Pres

section Glue

end Glue

end RamanujanPetersson.EtPBC.DescG

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

variable (M) in
/-- **`Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}`**: pull a section back along `V ×_P U₁ ⟶ V ×_P U₂`. -/
def rU : (push Φ Λ).obj (constSh Λ U₂ M) ⟶ (push (h ≫ Φ) Λ).obj (constSh Λ U₁ M) :=
  ObjectProperty.homMk
    { app := fun V => (uC h M).hom.app (op ((etPull Φ).obj V.unop)) ≫
        (constSh Λ U₁ M).obj.map (kapU h Φ V.unop).op
      naturality := fun {V V'} f => by
        ext z
        exact (congrArg (fun y => ((constSh Λ U₁ M).obj.map (kapU h Φ V'.unop).op).hom y)
          (app_map (uC h M) ((etPull Φ).map f.unop) z)).trans
          ((map_map_apply (constSh Λ U₁ M) _ _ _).trans
          ((congrArg (fun φ => ((constSh Λ U₁ M).obj.map φ.op).hom
            (((uC h M).hom.app (op ((etPull Φ).obj V.unop))).hom z)) (kapU_nat h Φ f.unop)).trans
          (map_map_apply (constSh Λ U₁ M) _ _ _).symm)) }

end RU

end RamanujanPetersson.EtPBC.FBC

end

end

-- ===== S4.Def_RP_EtPBC_A_T3dA =====
section

/-!
# S4-EtPBC-A, R4-T3d (part A): classes as extensions, and the kill by an extension

* `sesPb`: pulling the injective presentation `0 → A → I → I/A → 0` back along `x : X ⟶ I/A`;
* **`exists_ses_extClass`**: every `β ∈ Ext¹(X, A)` is the class of a short exact `0 → A → E → X → 0`;
* **`exists_bc_of_ses_kill`**: for `f : P' ⟶ P` etale with a closed lift `ι'` of the fibre inclusion, `Φ : U ⟶ P'`
  finite and a mono `m : f^* G ⟶ Φ_* M_U`, the class of an extension `0 → ι^* G →a E → Λ → 0` on `P_s` is a germ
  as soon as `(ι^* G ⟶ ι'^* f^* G ⟶ ι'^* Φ_* M_U ≅ φs_* M_{U_s})` extends along `a`.
-/

set_option autoImplicit false

open CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.T3d

universe w v₁ u₁

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

section Pb

end Pb

variable [HasExt.{w} C] [EnoughInjectives C]

/-- **Every class in `Ext¹(X, A)` is the class of an extension `0 → A → E → X → 0`.** -/
theorem exists_ses_extClass {X A : C} (β : Ext.{w} X A 1) :
    ∃ (E : C) (a : A ⟶ E) (b : E ⟶ X) (w : a ≫ b = 0) (hS : (ShortComplex.mk a b w).ShortExact),
      hS.extClass = β := by
  let i := Injective.ι A
  let p := cokernel.π i
  have hip : i ≫ p = 0 := cokernel.condition i
  have h : (ShortComplex.mk i p hip).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i))
      inferInstance inferInstance
  have h0 : β.comp (Ext.mk₀ i) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ X h β h0 (zero_add 1)
  obtain ⟨x, rfl⟩ := (Ext.mk₀_bijective X (cokernel i)).2 x₃
  exact ⟨_, _, _, _, sesPb_shortExact i p x hip h, (extClass_sesPb i p x hip h).trans hx₃⟩

end Abstract

section Geo

open AlgebraicGeometry RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.PushKill RamanujanPetersson.EtPBC.FBC

universe u

end Geo

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

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] (U : X.AffineZariskiSite)

@[reassoc]
theorem kL_j2 {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ V.left) (h : g₁ ≫ vh V = g₂ ≫ vh V)
    (hg₁ : ∀ z, vh V (g₁ z) ∈ U.1) (hg₂ : ∀ z, vh V (g₂ z) ∈ U.1) :
    kL V U g₁ g₂ h hg₁ hg₂ ≫ Spec.map (CommRingCat.ofHom (j2 Γ(X, U.1) (CU V U)).toRingHom) =
      liftU V U g₂ hg₂ := by
  have : CommRingCat.ofHom (j2 Γ(X, U.1) (CU V U)).toRingHom =
      CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight :
        CU V U →ₐ[Γ(X, U.1)] CU V U ⊗[Γ(X, U.1)] CU V U)) := rfl
  rw [this, kL, Category.assoc, pullbackSpecIso_hom_snd, pullback.lift_snd]

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

include hσ in
theorem b_piT (W : (Over T)ᵒᵖ) (x : ((Over.forget T).op ⋙ E.obj).obj W) :
    ((wh b T).app W).hom (piT b σ W x) = 0 := by
  rw [piT_apply, map_sub, b_secT b σ hσ, sub_self]

include hS hσ in
theorem exists_retT (W : (Over T)ᵒᵖ) (x : ((Over.forget T).op ⋙ E.obj).obj W) :
    ∃ y, ((wh a T).app W).hom y = piT b σ W x :=
  wsec_exact a b hab hS W _ (b_piT b σ hσ W x)

/-- The retraction `E|_T ⟶ F|_T`. -/
def retT : HomOver E F T where
  app W := ModuleCat.ofHom
    { toFun := fun x => (exists_retT a b hab hS σ hσ W x).choose
      map_add' := fun x y => wsec_inj a b hab hS W
        ((exists_retT a b hab hS σ hσ W (x + y)).choose_spec.trans ((map_add (piT b σ W) x y).trans
          ((congrArg₂ (· + ·) (exists_retT a b hab hS σ hσ W x).choose_spec.symm
            (exists_retT a b hab hS σ hσ W y).choose_spec.symm).trans (map_add ((wh a T).app W).hom _ _).symm)))
      map_smul' := fun c x => wsec_inj a b hab hS W
        ((exists_retT a b hab hS σ hσ W (c • x)).choose_spec.trans ((map_smul (piT b σ W) c x).trans
          ((congrArg (c • ·) (exists_retT a b hab hS σ hσ W x).choose_spec.symm).trans
            (map_smul ((wh a T).app W).hom _ _).symm))) }
  naturality {W W'} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply wsec_inj a b hab hS W'
    change ((wh a T).app W').hom
        (exists_retT a b hab hS σ hσ W' ((((Over.forget T).op ⋙ E.obj).map f).hom x)).choose =
      ((wh a T).app W').hom ((((Over.forget T).op ⋙ F.obj).map f).hom
        (exists_retT a b hab hS σ hσ W x).choose)
    have ha := congrArg (fun φ => φ.hom (exists_retT a b hab hS σ hσ W x).choose) ((wh a T).naturality f)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ha
    exact (exists_retT a b hab hS σ hσ W' _).choose_spec.trans ((piT_nat b σ f x).symm.trans
      ((congrArg (((Over.forget T).op ⋙ E.obj).map f).hom (exists_retT a b hab hS σ hσ W x).choose_spec.symm).trans
        ha.symm))

end Ret

section Tau

end Tau

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

variable {W T}

/-- **Points over specialisations lie on the sections.** -/
theorem exists_eq_tau [IsAffine W.left] (x : P) (t : (geomPtAt x).point.fiber.obj T)
    (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W)) (hτ : ∀ b, (geomPtAt x).point.fiber.map (τ b) t = b)
    (y : P) (t' : (geomPtAt y).point.fiber.obj T) (hs : fpt x t ⤳ fpt y t') (a : (geomPtAt y).point.fiber.obj W) :
    ∃ b, a = (geomPtAt y).point.fiber.map (τ b) t' := by
  have hW : IsSeparated W.hom := Scheme.instIsSeparatedOfIsSeparated (X := W.left) (Y := P) W.hom
  have hS : IsSeparated (pullback.snd W.hom T.hom) := by
    set_option backward.isDefEq.respectTransparency.types false in infer_instance
  have hcl : ∀ b, IsClosed (Set.range (sec (τ b)).left) := fun b =>
    @isClosed_range_section _ _ _ (pullback.snd W.hom T.hom) hS (sec_snd (τ b))
  have hsnd : pullback.snd W.hom T.hom (fpt y (pair y a t')) = fpt y t' := by
    have := congrArg (fun z => fpt y z) (pair_snd y a t')
    exact this
  obtain ⟨b, hb⟩ := mem_range_of_specializes (pullback.snd W.hom T.hom) (fun b => (sec (τ b)).left) hcl
    (fpt x t) (cover_gen x t τ hτ) (fpt y (pair y a t')) (hsnd ▸ hs)
  exact ⟨b, eq_of_mem_sec y (τ b) a t' hb⟩

end Prd

end RamanujanPetersson.EtPBC.GenGeo

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

variable {Y : Scheme.{u}} (π : Y ⟶ PV K gK) {V : Scheme.{u}} (hj : V ⟶ S) [IsAffine V] (R' : Type u) [CommRing R']
  [Algebra Γ(V, ⊤) R']

/-- **The inverse of `kapV`.** -/
def kapInv : YV K (hj ≫ gK) (piVV K gK π hj) R' ⟶ pullback (pullback.snd (hV V R' ≫ hj) (qV K gK)) π :=
  pullback.lift (kapP K gK π hj R') (pullback.fst _ _ ≫ pullback.snd _ π) (kapInv_cond K gK π hj R')

theorem kapV_kapInv : kapV K gK π hj R' ≫ kapInv K gK π hj R' = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [kapV, kapInv, kapP, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · simp only [kapV, kapInv, kapP, ymapR, pmapR, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, Category.id_comp]
  · simp only [kapV, kapInv, ymapR, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, Category.id_comp]

theorem kapInv_kapV : kapInv K gK π hj R' ≫ kapV K gK π hj R' = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · have e : pullback.snd (piVV K gK π hj ≫ qV K (hj ≫ gK)) (hV V R') ≫ hV V R' =
            pullback.fst (piVV K gK π hj ≫ qV K (hj ≫ gK)) (hV V R') ≫ pullback.fst (pullback.snd hj (qV K gK)) π ≫
              pullback.fst hj (qV K gK) := by
          rw [← pullback.condition, piVV_q]
        simp only [kapV, kapInv, kapP, ymapR, pmapR, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, Category.id_comp]
        exact e
      · simp only [kapV, kapInv, kapP, ymapR, pmapR, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, Category.id_comp]
    · simp only [kapV, kapInv, ymapR, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, Category.id_comp]
  · simp only [kapV, kapInv, kapP, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, pullback.lift_fst,
      Category.id_comp]

end Kap

section Fib

variable [IsIso (s.pt ≫ gK)]

theorem isClosedImmersion_fibV {W : Scheme.{u}} (hw : W ⟶ S) (w : Spec (CommRingCat.of s.Ω) ⟶ W)
    (hv : w ≫ hw = s.pt) [IsClosedImmersion w] : IsClosedImmersion (fibV K gK s hw w hv) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_fibV K gK s hw w hv).flip ‹_›

end Fib

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

section Sec

variable {T} (W : P.Etale)

/-- **The sections `sx (τ b)` pass through distinct points.** -/
theorem sx_disj (x : P) (t : (geomPtAt x).point.fiber.obj T) (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W))
    (hτ : ∀ b, (geomPtAt x).point.fiber.map (τ b) t = b) (b b' : (geomPtAt x).point.fiber.obj W)
    (h : sx (fpt x t) W (τ b) default = sx (fpt x t) W (τ b') default) : b = b' := by
  have hsec : ∀ c, (sec (τ c)).left (fpt x t) = μx (fpt x t) W (sx (fpt x t) W (τ c) default) := by
    intro c
    rw [← Scheme.Hom.comp_apply, sx_μx, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hpair : fl x (pair x b' t) = fl x t ≫ (sec (τ b')).left := by
    have e1 : fl x t ≫ (τ b').left = fl x b' := congrArg (fun z => ((geomPtAt x).liftOf z).left) (hτ b')
    have e2 : fl x (pair x b' t) ≫ pullback.snd W.hom T.hom = fl x t :=
      congrArg (fun z => ((geomPtAt x).liftOf z).left) (pair_snd x b' t)
    refine pullback.hom_ext ?_ ?_
    · exact (pair_fst x b' t).trans (e1.symm.trans ((congrArg (fl x t ≫ ·) (sec_fst (τ b')).symm).trans
        (Category.assoc _ _ _).symm))
    · exact e2.trans ((Category.comp_id _).symm.trans
        ((congrArg (fl x t ≫ ·) (sec_snd (τ b'))).symm.trans (Category.assoc _ _ _).symm))
  have hmem : fpt x (pair x b' t) ∈ Set.range (sec (τ b)).left := by
    refine ⟨fpt x t, ?_⟩
    have h1 : fpt x (pair x b' t) = (sec (τ b')).left (fpt x t) := by
      show fl x (pair x b' t) default = _
      rw [hpair, Scheme.Hom.comp_apply]
      rfl
    rw [h1, hsec, hsec, h]
  exact ((eq_of_mem_sec x (τ b) b' t hmem).trans (hτ b)).symm

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

/-- **Images of a point over `yg` are sheet points.** -/
theorem key_pt (x : P) (t : (geomPtAt x).point.fiber.obj T) (V : P.Etale) (ν : Up (fpt x t) V)
    (hν : pullback.snd V.hom (πn T (fpt x t)) ν = yg T (fpt x t)) :
    ∃ β : (geomPtAt x).point.fiber.obj V, ∀ (W : P.Etale) (g : V ⟶ W)
      (τ : (geomPtAt x).point.fiber.obj W → (T ⟶ W)), (∀ b, (geomPtAt x).point.fiber.map (τ b) t = b) →
      ((etPull (πn T (fpt x t))).map g).left ν =
        κp (fpt x t) W (sx (fpt x t) W (τ ((geomPtAt x).point.fiber.map g β)) default) := by
  obtain ⟨e, rfl⟩ := exists_κp_pre (fpt x t) V ν hν
  obtain ⟨β, hβ⟩ := exists_beta x t V e
  refine ⟨β, fun W g τ hτ => ?_⟩
  have hm : κp (fpt x t) V ≫ ((etPull (πn T (fpt x t))).map g).left = xmap (fpt x t) g ≫ κp (fpt x t) W :=
    (xmap_κp (fpt x t) g).symm
  exact ((Scheme.Hom.comp_apply _ _ e).symm.trans (congrArg (fun φ => φ.base e) hm)).trans
    ((Scheme.Hom.comp_apply _ _ e).trans (congrArg (fun y => (κp (fpt x t) W).base y) (hβ W g τ hτ)))

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

end Gen

section Aux

variable (K : Type u) [Field K] {S : Scheme.{u}} (gK : S ⟶ Spec (CommRingCat.of K)) (s : GeomPt S) [IsIso (s.pt ≫ gK)]
  {Y : Scheme.{u}} (π : Y ⟶ PV K gK) {W : Scheme.{u}} (hw : W ⟶ S) (w : Spec (CommRingCat.of s.Ω) ⟶ W)
  (hv : w ≫ hw = s.pt)

theorem ysV_fst : ysV K gK s π hw w hv ≫ pullback.fst (pullback.snd hw (qV K gK)) π =
    pullback.snd π (fibι (qV K gK) s) ≫ fibV K gK s hw w hv :=
  pullback.lift_fst _ _ _

theorem ysV_snd : ysV K gK s π hw w hv ≫ pullback.snd (pullback.snd hw (qV K gK)) π =
    pullback.fst π (fibι (qV K gK) s) :=
  pullback.lift_snd _ _ _

end Aux

section Chi

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

end Chi

section Main

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

end Main

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Ap1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Ap1): approximating a function on an etale neighbourhood by a function from below

Pure algebra for Km DESIGN v3 (Rel): `O → O'` with `O' = O + t O'` (trivial residue extension along `t`, e.g.
`k[X] → B_w` for an etale neighbourhood), an `O`-algebra `S` (functions on `R`), an `O'`-algebra `Q` (functions on
the generic fibre of `W = D_o ×_P R`) and `f : S →ₐ[O] Q`; `hatS f = O'[f S] ⊆ Q`.
* `exists_pow_dense`: `x = c + t^n y` in `O'`;
* `hatS_dense`: every `q ∈ hatS f` is `f s + t^n x` with `x ∈ hatS f`;
* **`exists_approx`**: if `s ∈ hatS f` has an inverse `v` with `t^c v ∈ hatS f`, then `f u = s (1 - t z)` for some
  `u ∈ S`, `z ∈ hatS f`;
* `isIntegral_of_mem_hatS`: elements of `hatS f` are integral over `O'` when `S` is integral over `O`;
* `exists_crt`, **`exists_approx_crt`**: the same with `u` prescribed modulo finitely many pairwise coprime ideals
  of `S` that are coprime to every `(t^n)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Approx

variable {O O' S Q : Type*} [CommRing O] [CommRing O'] [CommRing S] [CommRing Q]
  [Algebra O O'] [Algebra O S] [Algebra O' Q] [Algebra O Q] [IsScalarTower O O' Q]
  (f : S →ₐ[O] Q) (t : O)

/-- **Approximation with prescribed residues** modulo ideals `J i` of `S` coprime to every `(t^n)`. -/
theorem exists_approx_crt (h1 : ∀ x : O', ∃ c : O, ∃ y : O', x = algebraMap O O' c + algebraMap O O' t * y)
    {ι : Type*} [Finite ι] (J : ι → Ideal S) (r : ι → S) (hJ : Pairwise fun i j => IsCoprime (J i) (J j))
    (hJt : ∀ (n : ℕ) (i : ι), IsCoprime (Ideal.span {algebraMap O S t ^ n}) (J i))
    {s v : Q} (hs : s ∈ hatS (O' := O') f) (hsv : s * v = 1) {c : ℕ}
    (hv : algebraMap O Q t ^ c * v ∈ hatS (O' := O') f) :
    ∃ u : S, (∀ i, u - r i ∈ J i) ∧ ∃ z ∈ hatS (O' := O') f, f u = s * (1 - algebraMap O Q t * z) := by
  obtain ⟨u₀, x, hx, hux⟩ := hatS_dense f t h1 (c + 1) hs
  let I : Option ι → Ideal S := fun o => o.elim (Ideal.span {algebraMap O S t ^ (c + 1)}) J
  have hI : Pairwise fun i j => IsCoprime (I i) (I j) := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact hJt (c + 1) j
    · exact (hJt (c + 1) i).symm
    · exact hJ fun e => hij (congrArg some e)
  obtain ⟨u, hu⟩ := exists_crt I hI (fun o => o.elim u₀ r)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hu none)
  refine ⟨u, fun i => hu (some i), (algebraMap O Q t ^ c * v) * (x - f w), Subalgebra.mul_mem _ hv
    (Subalgebra.sub_mem _ hx (mem_hatS f w)), ?_⟩
  have hu' : u = u₀ + w * algebraMap O S t ^ (c + 1) := by
    have h := hw
    change w * algebraMap O S t ^ (c + 1) = u - u₀ at h
    rw [h]; ring
  have e : f u = s - algebraMap O Q t ^ (c + 1) * (x - f w) := by
    rw [hu', map_add, map_mul, map_pow, AlgHom.commutes, hux]; ring
  rw [e]
  linear_combination (algebraMap O Q t ^ (c + 1) * (x - f w)) * hsv

end Approx

end RamanujanPetersson.EtPBC.EtKum

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

end Opn

section Res

variable {W' W U Z : P.Etale} {p₁ : W' ⟶ W} {p₂ : W' ⟶ U} {w : W ⟶ Z} {v : U ⟶ Z} {hsq : p₁ ≫ w = p₂ ≫ v}

variable {Uo Uz : P.Opens} (h : Uo ≤ Uz) (D : P.Etale)

theorem loc_res_D (hS : (locC Λ D h).ShortExact) {F : EtSh Λ P} (γ : Ext.{u} (freeSh Λ D) F 1) :
    hS.extClass.comp ((Ext.mk₀ (freeMap Λ (prW D (opEt Uo)))).comp γ (zero_add 1)) (show 1 + 1 = 2 from rfl) = 0 :=
  mv_res_W hS γ _

end Res

end RamanujanPetersson.EtPBC.EtMV

end

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

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  (S : Submonoid B) [IsLocalization S Bt] (hS : S ≤ nonZeroDivisors B)
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]

/-- **Valuations of a localization**: `v_{p Bt} = v_p` on `K`. -/
theorem valuation_locPt (p : HeightOneSpectrum B) (hp : Disjoint (S : Set B) p.asIdeal) (x : K) :
    (locPt (Bt := Bt) S hS p hp).valuation K x = p.valuation K x := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  rw [map_div₀, map_div₀, IsScalarTower.algebraMap_apply B Bt K a, IsScalarTower.algebraMap_apply B Bt K s,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_locPt, intValuation_locPt]

end VC

section Root

end Root

section Twist

end Twist

end RamanujanPetersson.EtCompact.Pur

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2a =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3

GLOB/REL PLAN v1, stage S3 (pure algebra).
* `isUnit_of_mul_eq_one_of_isIntegral`: `t z = 1` with `z` integral over `R ↪ K` makes `t` a unit (so `1 - t z ≠ 0`
  for `z ∈ hatS` when `t` is not a unit);
* `liveIdem`, `liveMod`: on a reduced Noetherian `Y` (`Y ≅ Π Y ⧸ Q`), `x' := v + (x - v) e_live` with `e_live` the
  idempotent of the pieces where `x` is not identically zero; `liveMod_notMem` / `mem_nonZeroDivisors_of_notMem`
  (`x'` is a non-zero-divisor when `v` is), `map_liveMod` (`κ x' = κ x` for every `κ` into a domain with `κ x ≠ 0`),
  `liveMod_mem_integralClosure`;
* `exists_glob_approx'`: `exists_glob_approx` with `N` chosen before the CRT targets `r`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Inv

end Inv

section Live

variable {Y : Type*} [CommRing Y] (h : ∀ (m : Ideal Y) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [IsNoetherianRing Y]

open Classical in
theorem mk_liveMod (x v : Y) (Q : minimalPrimes Y) :
    Ideal.Quotient.mk (Q : Ideal Y) (liveMod h x v) =
      if x ∈ (Q : Ideal Y) then Ideal.Quotient.mk (Q : Ideal Y) v else Ideal.Quotient.mk (Q : Ideal Y) x := by
  unfold liveMod
  rw [map_add, map_mul, map_sub, liveIdem_mk]
  split_ifs with hx
  · ring
  · ring

/-- **`κ x' = κ x`** for every `κ` into a domain with `κ x ≠ 0`. -/
theorem map_liveMod (x v : Y) {K : Type*} [CommRing K] [IsDomain K] (κ : Y →+* K) (hκ : κ x ≠ 0) :
    κ (liveMod h x v) = κ x := by
  classical
  have : (RingHom.ker κ).IsPrime := RingHom.ker_isPrime κ
  obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal Y) ≤ RingHom.ker κ)
  have hxQ : x ∉ Q := fun hx => hκ (hQle hx)
  have he : liveIdem h x - 1 ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
    have e := liveIdem_mk h x ⟨Q, hQ⟩
    rw [if_neg hxQ] at e
    rw [e, sub_self]
  have he' : κ (liveIdem h x) = 1 := by
    have e := hQle he
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at e
    exact e
  unfold liveMod
  rw [map_add, map_mul, he', map_sub]
  ring

theorem liveMod_mem_integralClosure {R : Type*} [CommRing R] [Algebra R Y] {x v : Y}
    (hx : x ∈ integralClosure R Y) (hv : v ∈ integralClosure R Y) : liveMod h x v ∈ integralClosure R Y :=
  add_mem hv (mul_mem (sub_mem hx hv) (isIntegral_of_isIdempotentElem (isIdempotentElem_liveIdem h x)))

end Live

section Glob'

end Glob'

end RamanujanPetersson.EtPBC.EtKum

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

end Cat

section Gen

variable {A K A' K' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing A'] [IsDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K']
  (φ : CommRingCat.of A ⟶ CommRingCat.of A') [Etale (Spec.map φ)] (h : Spec.map φ (genPt A') = genPt A)

theorem resMapX_fracIso (ψ : K →+* K') (hψ : ∀ a : A, ψ (algebraMap A K a) = algebraMap A' K' (φ.hom a))
    (k : K) : resMapX (Spec.map φ) h (fracIso A K k) = fracIso A' K' (ψ k) := by
  have e : (resMapX (Spec.map φ) h).comp (fracIso A K).toRingHom = (fracIso A' K').toRingHom.comp ψ :=
    IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a => by
      show resMapX (Spec.map φ) h (fracIso A K (algebraMap A K a)) = fracIso A' K' (ψ (algebraMap A K a))
      rw [UnramMain.fracIso_algebraMap', hψ, UnramMain.fracIso_algebraMap']
      exact resMapX_toGen φ h a)
  exact RingHom.congr_fun e k

end Gen

end RamanujanPetersson.EtCompact.GalTrE

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

theorem isoTl_fst : (isoTl c φ hUo).hom ≫ pullback.fst (chEt c φ).hom (opEt Uo).hom = Spec.map (locT φ a) := by
  exact @IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _ (Spec.map (locT φ a))
    (pullback.fst (chEt c φ).hom (opEt Uo).hom) inferInstance (isOpenImmersion_fstUo c φ Uo) (range_eqT c φ hUo)

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

end PrdR

section Cancel

variable {k : Type} [Field k] {Λ : Type} [CommRing Λ] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] (a : k)

theorem toD1_cancel {Y : P.Etale} {f g : Y ⟶ W1 c φ a} (h : f ≫ toD1 c φ a = g ≫ toD1 c φ a) : f = g :=
  MorphismProperty.Over.Hom.ext ((cancel_mono (Spec.map (locT φ a))).1 (congrArg (fun m => m.left) h))

end Cancel

section PurE

end PurE

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Th1c =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`

For `τ : T ⟶ D₀` (`W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`):
* `theta_apply`: `θ_τ x = extFreeU (thX x)` (via `thXE`, `theta_eq_thXE`, `thXE_eq`);
* **`theta_natural`**: for `m : T₁ ⟶ T₂` with `m ≫ τ₂ = τ₁`,
  `θ_{τ₁}(Λ[m]^* x) = resLE (wm m) (θ_{τ₂} x)`.
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

section Gen

end Gen

section GenNat

universe w₁ v₁ u₁

end GenNat

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} {D₀ : P.Etale} (R : P.Etale)

variable [QuasiCompact ((etPull D₀.hom).obj R).hom] [IsSeparated ((etPull D₀.hom).obj R).hom]
  (n : ℕ) (hn : ∀ y : D₀.left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull D₀.hom).obj R)) = n)

/-- Square 1 of `thX_natural` (morphisms only). -/
theorem thX_natural_h1 {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) {τ₁ : T₁ ⟶ D₀} {τ₂ : T₂ ⟶ D₀} (h : m ≫ τ₂ = τ₁) :
    freeMap Λ (ovrMapW R m h) ≫ freeMap Λ (ovrι R τ₂).inv =
      freeMap Λ (ovrι R τ₁).inv ≫ freeMap Λ ((etPull ((etPull D₀.hom).obj R).hom).map (ovrMap m h)) := by
  rw [← freeMap_comp, ovrι_natural, freeMap_comp]

end Theta

end RamanujanPetersson.EtPBC.EtShap

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

end Affine

section Prd

variable {k : Type u} [Field k] {P : Scheme.{u}} (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{u}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {a : k} {Uo : P.Opens}
  (hUo : ∀ u : Spec B, (chEt c φ).hom u ∈ Uo ↔ φ.hom (X - C a) ∉ u.asIdeal)

include hUo in
/-- `D ×_P Uo ≅ Spec B_t` is affine. -/
theorem isAffine_prdUo : IsAffine (prd (chEt c φ) (opEt Uo)).left := by
  have : IsAffine (pullback (chEt c φ).hom (opEt Uo).hom) := IsAffine.of_isIso (isoTl c φ hUo).inv
  exact this

end Prd

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

/-- **`W₁ = D₁ ×_D W`**. -/
theorem isPullback_wD {D₁ D : P.Etale} (d : D₁ ⟶ D) (X : P.Etale) :
    IsPullback (wm (R := R) (prdMap d X)) (wD D₁ X R) (wD D X R) d.left := by
  unfold wD
  exact (isPullback_wm R (prdMap d X)).paste_vert (isPullback_prdMap d X)

/-- The ring pushout square for `D = Spec B`, `D₁ = Spec B'`, `d.left = Spec.map ι`. -/
theorem isPushout_bW {B B' : CommRingCat.{u}} (hB : Spec B ⟶ P) [Etale hB] (hB' : Spec B' ⟶ P) [Etale hB']
    (ι : B ⟶ B') (d : Scheme.Etale.mk hB' ⟶ Scheme.Etale.mk hB) (hd : d.left = Spec.map ι) (X : P.Etale)
    [IsAffine ((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left] :
    IsPushout (bW hB X R) ι (wm (R := R) (prdMap d X)).appTop (bW hB' X R) := by
  have : IsAffine (Scheme.Etale.mk hB).left := inferInstanceAs (IsAffine (Spec B))
  have : IsAffine (Scheme.Etale.mk hB').left := inferInstanceAs (IsAffine (Spec B'))
  refine (isPushout_appTop_of_isPullback (isPullback_wD R d X)).of_iso (Scheme.ΓSpecIso B) (Iso.refl _)
    (Scheme.ΓSpecIso B') (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm
  · rw [hd]; exact Scheme.ΓSpecIso_naturality ι
  · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm

end Pb

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

variable {a : k} {Uo : P.Opens}
  (hg₀ : ∀ v : (chEt c (locF (B := CommRingCat.of k[X]) g₀)).left,
    (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v ∈ Uo ∨ (chEt c (locF (B := CommRingCat.of k[X]) g₀)).hom v = c (A1pt k a))
  (hGt : X - C a ∣ G)

include hG₀ hg₀ hGt in
theorem opnDg_le : opnDg c G ≤ Uo := by
  rintro x ⟨v, rfl⟩
  exact chG_mem c hG₀ hg₀ hGt v

include hG₀ hg₀ hGt in
theorem hUo_G (u : Spec (CommRingCat.of (Localization.Away G))) :
    (chEt c (locF (B := CommRingCat.of k[X]) G)).hom u ∈ Uo ↔ (locF (B := CommRingCat.of k[X]) G).hom (X - C a) ∉ u.asIdeal :=
  ⟨fun _ hm => u.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (isUnit_locF_of_dvd hGt)), fun _ => chG_mem c hG₀ hg₀ hGt u⟩

include hG₀ hg₀ hGt in
theorem isAffine_prdG : IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left :=
  isAffine_prdUo c _ (hUo_G c hG₀ hg₀ hGt)

end ChG

section Sec

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {G : k[X]} {Uo : P.Opens}
  (hle : opnDg c G ≤ Uo)

theorem mG_prT (D₂ : P.Etale) (hD₂ : ∀ v : (prd D₂ (opEt Uo)).left, (prd D₂ (opEt Uo)).hom v ∈ opnDg c G) :
    mG c hle D₂ hD₂ ≫ prT (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo) = prT D₂ (opEt Uo) :=
  opEt_ext _ _

theorem mG_prdMap {g₀ : k[X]} (hG₀ : g₀ ∣ G) (D₂ : P.Etale)
    (hD₂ : ∀ v : (prd D₂ (opEt Uo)).left, (prd D₂ (opEt Uo)).hom v ∈ opnDg c G)
    (d : D₂ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀)) :
    mG c hle D₂ hD₂ ≫ prdMap (toDG c hG₀) (opEt Uo) = prdMap d (opEt Uo) :=
  eq_of_prT _ _ (opEt_ext _ _)

end Sec

section Gam

end Gam

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2d =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`

GLOB/REL PLAN v1, stage S4 (ring level). `ρ := (wm (prdMap (toDG c hG₀) (opEt U₀))).appTop : Γ(Y₀) → Γ(Y₁)`,
`m := mG c hle D₂ hD₂` (O2Gl2b), `D₂ = chEt c φ₂`, `d : D₂ ⟶ D_{g₀}`:
* `prdMap_comp`, `wm_prdMap_comp_appTop`: `prdMap` is functorial (target an open chart);
* `wm_mG_appTop`: `m^* ∘ ρ = (prdMap d)^*`; `wm_mG_gamMap`: `m^* ρ (r) = bW (φ₂ r)` for `r ∈ k[X]`;
* `exists_Hg`: `H := ũ' t^{-N}` is a unit; **`wm_mG_H`**: `m^* H · bW(φ₂ t)^N = (prdMap d)^* ũ'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtShap
  RamanujanPetersson.EtPBC.EtDeg

section Fun

variable {P : Scheme.{0}}

theorem wm_prdMap_comp_appTop (R : P.Etale) {D₂ D₁ D : P.Etale} [IsOpenImmersion D.hom] (d₁ : D₂ ⟶ D₁) (d₀ : D₁ ⟶ D)
    (X : P.Etale) (y : Γ(((etPull (prd D X).hom).obj R).left, ⊤)) :
    (wm (R := R) (prdMap (d₁ ≫ d₀) X)).appTop y =
      (wm (R := R) (prdMap d₁ X)).appTop ((wm (R := R) (prdMap d₀ X)).appTop y) := by
  rw [prdMap_comp, ← wm_comp]
  rfl

end Fun

section H

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c] {Uo : P.Opens}
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {B₂ : CommRingCat.{0}} (φ₂ : CommRingCat.of k[X] ⟶ B₂) [Etale (Spec.map φ₂ ≫ c)]
  [IsAffine (prd (chEt c φ₂) (opEt Uo)).left]
  (hD₂ : ∀ v : (prd (chEt c φ₂) (opEt Uo)).left, (prd (chEt c φ₂) (opEt Uo)).hom v ∈ opnDg c G)
  (d : chEt c φ₂ ⟶ chEt c (locF (B := CommRingCat.of k[X]) g₀))

theorem wm_mG_appTop
    (y : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) :
    (wm (R := R) (mG c hle (chEt c φ₂) hD₂)).appTop ((wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop y) =
      (wm (R := R) (prdMap d (opEt Uo))).appTop y := by
  rw [← mG_prdMap c hle hG₀ (chEt c φ₂) hD₂ d, ← wm_comp]
  rfl

end H

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

set_option backward.isDefEq.respectTransparency false in
/-- **Graphs through different fibre points do not meet over `z`.** -/
theorem not_mem_graphMeet {z : P} (hG : Subsingleton (Gal z)) {m m' : W ⟶ T}
    (d : (geomPtAt z).point.fiber.obj W)
    (hne : (geomPtAt z).point.fiber.map m d ≠ (geomPtAt z).point.fiber.map m' d) :
    fpt z d ∉ graphMeet m m' := by
  have := hG
  rintro ⟨u, hu⟩
  obtain ⟨rfl, h2⟩ := graph_meet_eq m' m hu
  exact hne (fiber_eq_of_pt z _ _ ((fib_left_map m z d).trans (h2.symm.trans (fib_left_map m' z d).symm)))

set_option backward.isDefEq.respectTransparency false in
/-- **Meeting loci pull back** along `d : W' ⟶ W`. -/
theorem graphMeet_natural (d : W' ⟶ W) (m m' : W ⟶ T) {v : W'.left}
    (hv : v ∈ graphMeet (d ≫ m) (d ≫ m')) : d.left v ∈ graphMeet m m' := by
  obtain ⟨u, hu⟩ := hv
  refine ⟨d.left u, ?_⟩
  have k1 : pullMap d ((graph (d ≫ m')).left u) = (graph m').left (d.left u) :=
    (Scheme.Hom.comp_apply _ _ u).symm.trans ((congrArg (fun φ => φ u) (graph_natural d m')).trans
      (Scheme.Hom.comp_apply _ _ u))
  have k2 : pullMap d ((graph (d ≫ m)).left v) = (graph m).left (d.left v) :=
    (Scheme.Hom.comp_apply _ _ v).symm.trans ((congrArg (fun φ => φ v) (graph_natural d m)).trans
      (Scheme.Hom.comp_apply _ _ v))
  rw [← k1, ← k2, hu]

end GraphGeo

end RamanujanPetersson.EtPBC.EtMV

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

variable {P : Scheme.{u}} {W T : P.Etale}

/-- **Enough disjoint graphs cover `W ×_P T`.** -/
theorem mem_graph_of_card {ι : Type*} (τ : ι → (W ⟶ T))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (graph (τ i)).left) (Set.range (graph (τ j)).left))
    (hfin : ∀ x : P, Finite ((geomPtAt x).point.fiber.obj T))
    (hcard : ∀ x : P, Nat.card ((geomPtAt x).point.fiber.obj T) ≤ Nat.card ι)
    (e : ((etPull W.hom).obj T).left) : ∃ i, e ∈ Set.range (graph (τ i)).left := by
  obtain ⟨d, hd⟩ := exists_fib_over W (((etPull W.hom).obj T).hom e)
  have := hfin (W.hom (((etPull W.hom).obj T).hom e))
  have hinj : Function.Injective
      (fun i => (geomPtAt (W.hom (((etPull W.hom).obj T).hom e))).point.fiber.map (τ i) d) := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.1 (hdisj i j hne) ⟨_, rfl⟩ ⟨_, graph_left_eq_of_fib _ d (τ j) (τ i) hij.symm⟩
  obtain ⟨σ, hσ⟩ := (hinj.bijective_of_nat_card_le (hcard _)).2.hasRightInverse
  obtain ⟨b, hb⟩ := graph_cover _ d (fun b => τ (σ b)) (fun b => hσ b) e hd.symm
  exact ⟨σ b, hb⟩

end GoodGeo

section Zero

end Zero

section GenZero

universe w' v₁ u₁ v₂ u₂ v₃ u₃

end GenZero

section Good

end Good

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd2 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd2): `H = 1 + t_i e` on every piece at a bad point

REL PLAN v2 (s126), file R2. At a bad point `a_i` (chart `D' = chEt c φ'` with `d : D' ⟶ D_{g₀}`, `φ'(X - C a)` a
unit), the unit `H` of `Y_G` with `H ρ(t)^N = ρ(y)`, `y = liveMod uS t^N`, `uS - t^N ∈ (X - C a_i) S`:
* **`liveMod_eq_add`** (generic): `liveMod uS t^N = t^N + r s` with `s` integral when `uS - t^N ∈ r S`;
* **`exists_bad_genC`** (generic): `exists_bad_genB` (O2Bd1) from the `liveMod` form;
* **`exists_bad_e`**: the `e`, `g`, `he`, `hHq` inputs of `uk_kill_glob` (O2UKd3) at `D'` with `m := mG`, `t := φ'(X - C a_i)`;
* **`exists_S4H'`**: `exists_S4H` (O2Gl2k) also returning the relation `H ρ(t)^N = ρ(y)`.
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

section BadAlg

variable {O Y G' B' : Type} [CommRing O] [CommRing Y] [CommRing G'] [CommRing B'] [Algebra O Y]
  (hY : ∀ (m : Ideal Y) [m.IsMaximal], IsDomain (Localization.AtPrime m)) [IsNoetherianRing Y]

/-- `liveMod uS t^N = t^N + r s` with `s` integral when `uS - t^N ∈ r S`. -/
theorem liveMod_eq_add (uS : integralClosure O Y) {t r : O} {N : ℕ}
    (hu : uS - algebraMap O (integralClosure O Y) t ^ N ∈ Ideal.span {algebraMap O (integralClosure O Y) r}) :
    ∃ s : Y, IsIntegral O s ∧
      liveMod hY (uS : Y) (algebraMap O Y t ^ N) = algebraMap O Y t ^ N + algebraMap O Y r * s := by
  obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton'.1 hu
  refine ⟨(s' : Y) * liveIdem hY (uS : Y),
    (show IsIntegral O (s' : Y) from s'.2).mul (isIntegral_of_isIdempotentElem (isIdempotentElem_liveIdem hY _)), ?_⟩
  have h2 : (uS : Y) - algebraMap O Y t ^ N = (s' : Y) * algebraMap O Y r := by
    have e := congrArg (fun x : integralClosure O Y => (x : Y)) hs'
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] at e
    exact e.symm
  unfold liveMod
  rw [h2]
  ring

end BadAlg

section BadChart

end BadChart

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

include hGf in
/-- **`hDr₁`** for `D' = D_{G_b}`. -/
theorem badCh_r₁ (v : (chEt c (locF (B := CommRingCat.of k[X]) Gb)).left) :
    (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom v ∈ opnDg c G ∨
      (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom v = c (A1pt k b) :=
  bad_pt c hGf (gb_not_mem c v)

variable {Uo : P.Opens} (hle : opnDg c G ≤ Uo) (hb : c (A1pt k b) ∉ Uo)

include hGf hle in
/-- **`hDr`** for `D' = D_{G_b}`. -/
theorem badCh_r (v : (chEt c (locF (B := CommRingCat.of k[X]) Gb)).left) :
    (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom v ∈ Uo ∨
      (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom v = c (A1pt k b) :=
  (badCh_r₁ c hGf v).imp_left fun h => hle h

include hGf hb in
/-- **`hD'`**: `D_{G_b} ×_P U₀` lies over `c(D(G))`. -/
theorem badCh_D' (v : (prd (chEt c (locF (B := CommRingCat.of k[X]) Gb)) (opEt Uo)).left) :
    (prd (chEt c (locF (B := CommRingCat.of k[X]) Gb)) (opEt Uo)).hom v ∈ opnDg c G := by
  let w := pullback.fst (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom (opEt Uo).hom v
  have e1 : (prd (chEt c (locF (B := CommRingCat.of k[X]) Gb)) (opEt Uo)).hom v =
      (opEt Uo).hom (pullback.snd (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom (opEt Uo).hom v) := rfl
  have e2 : (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom w =
      (opEt Uo).hom (pullback.snd (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom (opEt Uo).hom v) :=
    congrArg (fun F => F v) (pullback.condition (f := (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom) (g := (opEt Uo).hom))
  have hU : (prd (chEt c (locF (B := CommRingCat.of k[X]) Gb)) (opEt Uo)).hom v ∈ Uo := by
    rw [e1]
    show (Uo.ι ≫ 𝟙 P) _ ∈ Uo
    rw [Category.comp_id]
    exact opnι_mem (etId P) Uo _
  have hx : (prd (chEt c (locF (B := CommRingCat.of k[X]) Gb)) (opEt Uo)).hom v =
      (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom w := e1.trans e2.symm
  rcases badCh_r₁ c hGf w with h1 | h1
  · rw [hx]; exact h1
  · exact absurd (h1 ▸ hx ▸ hU) hb

include hGf hle hb in
/-- The `hUo` of `isAffine_prdUo` for `D_{G_b}` (`t := X - C b`). -/
theorem badCh_hUo (u : Spec (CommRingCat.of (Localization.Away Gb))) :
    (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom u ∈ Uo ↔
      (locF (B := CommRingCat.of k[X]) Gb).hom (X - C b) ∉ u.asIdeal := by
  have hcu : (chEt c (locF (B := CommRingCat.of k[X]) Gb)).hom u = c (Spec.map (locF (B := CommRingCat.of k[X]) Gb) u) := rfl
  constructor
  · intro hU ht
    have h1 : Spec.map (locF (B := CommRingCat.of k[X]) Gb) u = A1pt k b := eq_A1pt_of_mem (Ideal.mem_comap.2 ht)
    exact hb (h1 ▸ hcu ▸ hU)
  · intro ht
    rcases badCh_r₁ c hGf u with h1 | h1
    · exact hle h1
    · exfalso
      have h2 : Spec.map (locF (B := CommRingCat.of k[X]) Gb) u = A1pt k b := c.isOpenEmbedding.injective (hcu.symm.trans h1)
      have h3 : X - C b ∈ (Spec.map (locF (B := CommRingCat.of k[X]) Gb) u).asIdeal := by
        rw [h2]; exact Ideal.mem_span_singleton_self _
      exact ht (Ideal.mem_comap.1 h3)

end BadCh

section BadCh2

end BadCh2

section JAlg

end JAlg

end RamanujanPetersson.EtPBC.EtKum

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

end TB2

section TB2o

/-! Op-form section calculus: restriction maps are op-morphisms `a : op T ⟶ op Z` that are passed through
unchanged, so consecutive steps meet in syntactically equal terms (this keeps kernel checks cheap). -/

variable {Λ : Type u} [CommRing Λ]

theorem pullCompHom_pbSecO {A B C : Scheme.{u}} (g : A ⟶ B) (h : B ⟶ C) {F : EtSh Λ C} {V : C.Etale}
    {Z : A.Etale} (a : op ((etPull (g ≫ h)).obj V) ⟶ op Z) (x : F.obj.obj (op V)) :
    ((pullCompHom Λ g h F).hom.app (op Z)).hom ((((pull (g ≫ h) Λ).obj F).obj.map a).hom (pbSec (g ≫ h) x)) =
      ((((pull g Λ).obj ((pull h Λ).obj F)).obj.map (((etPullCompIso g h).hom.app V).op ≫ a)).hom
        (pbSec g (pbSec h x))) :=
  (congrArg (fun ψ => ψ.hom (pbSec (g ≫ h) x)) (((pullCompIso Λ g h).hom.app F).hom.naturality a)).trans
    ((congrArg (fun z => (((pull g Λ).obj ((pull h Λ).obj F)).obj.map a).hom z) (pbSec_comp g h x)).trans
      (mapO_comp_apply _ _ _ _).symm)

end TB2o

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

variable {i g} (hig : i ≫ g = 𝟙 S)

variable [IsClosedImmersion i]

/-- The open `D̃ ⊆ Es`: off the bad set and over `Q`. -/
def Og (Q : P.Opens) : (Es i g W).left.Opens :=
  ⟨(Bz W hig)ᶜ ∩ (Es i g W).hom ⁻¹' (Q : Set P),
    (isClosed_Bz W hig).isOpen_compl.inter (Q.isOpen.preimage (Es i g W).hom.continuous)⟩

/-- `D̃`. -/
abbrev Dg (Q : P.Opens) : P.Etale := opn (Es i g W) (Og W hig Q)

/-- `D̃ ⟶ Zs`. -/
def wg (Q : P.Opens) : Dg W hig Q ⟶ Zs i g W := opnι (Es i g W) (Og W hig Q) ≫ prT W (Zs i g W)

theorem fpt_opnι_notMem (Q : P.Opens) (x : P) (b : (geomPtAt x).point.fiber.obj (Dg W hig Q)) :
    fpt x ((geomPtAt x).point.fiber.map (opnι (Es i g W) (Og W hig Q)) b) ∉ Bz W hig := by
  rw [fib_left_map]
  exact (opnι_mem _ _ (fpt x b)).1

/-- **Uniqueness**: `wg` is injective on fibres over `x̄ = (x̄ ≫ g) ≫ i`. -/
theorem graph_unique (Q : P.Opens) (x : P) (hx : (geomPtAt x).pt = ((geomPtAt x).pt ≫ g) ≫ i)
    (a a' : (geomPtAt x).point.fiber.obj (Dg W hig Q))
    (h : (geomPtAt x).point.fiber.map (wg W hig Q) a = (geomPtAt x).point.fiber.map (wg W hig Q) a') :
    a = a' := by
  apply fib_opn_injective _ _ x
  apply fiber_ext
  change fl x _ = fl x _
  rw [fl_graph W hig x hx _ (fpt_opnι_notMem W hig Q x a), fl_graph W hig x hx _ (fpt_opnι_notMem W hig Q x a')]
  simp only [wg, Functor.map_comp, types_comp_apply] at h
  rw [h]

/-- **Existence**: over `x̄ = (x̄ ≫ g) ≫ i` with `x ∈ Q`, every point of `Zs` comes from `D̃`. -/
theorem graph_exists (Q : P.Opens) (x : P) (hx : (geomPtAt x).pt = ((geomPtAt x).pt ≫ g) ≫ i) (hxQ : x ∈ Q)
    (c : (geomPtAt x).point.fiber.obj (Zs i g W)) :
    ∃ a, (geomPtAt x).point.fiber.map (wg W hig Q) a = c := by
  have hc : fl x c ≫ pullback.snd (Vs i W).hom g = (geomPtAt x).pt := Over.w ((geomPtAt x).liftOf c)
  have hφ : ((fl x c ≫ pullback.fst (Vs i W).hom g) ≫ τz W hig) ≫ (Es i g W).hom = (geomPtAt x).pt :=
    (Category.assoc _ _ _).trans ((whisker_eq _ ((τz_hom W hig).trans (jz_snd W hig).symm)).trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker (fl_Zs W hig x hx c) _).trans hc)))
  let d₀ : (geomPtAt x).point.fiber.obj (Es i g W) :=
    (Over.homMk ((fl x c ≫ pullback.fst (Vs i W).hom g) ≫ τz W hig) hφ :
      CategoryTheory.Over.mk (geomPtAt x).pt ⟶ (Scheme.Etale.forget P).obj (Es i g W))
  have hd₀ : (geomPtAt x).point.fiber.map (prT W (Zs i g W)) d₀ = c := by
    apply fiber_ext
    change ((fl x c ≫ pullback.fst (Vs i W).hom g) ≫ τz W hig) ≫ pullback.snd W.hom (Zs i g W).hom = fl x c
    exact (Category.assoc _ _ _).trans ((whisker_eq _ (τz_snd W hig)).trans (fl_Zs W hig x hx c))
  have hmem : fpt x d₀ ∈ ((Bz W hig)ᶜ ∩ (Es i g W).hom ⁻¹' (Q : Set P)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, hyeq⟩
      apply hy
      refine ⟨(fl x c ≫ pullback.fst (Vs i W).hom g) default, ?_⟩
      apply (pullback.fst (Es i g W).hom i).isClosedEmbedding.injective
      exact ((Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg
        (fun f : (Vs i W).left ⟶ (Es i g W).left => f ((fl x c ≫ pullback.fst (Vs i W).hom g) default))
        (δz_fst W hig)).trans
        (Scheme.Hom.comp_apply _ _ _).symm)).trans hyeq.symm
    · have hE : (Es i g W).hom (fpt x d₀) = x := (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun f => f default) hφ).trans (center_geomPtAt x))
      exact (congrArg (· ∈ (Q : Set P)) hE).mpr hxQ
  obtain ⟨b, hb, -⟩ := exists_lift_fib (opnι (Es i g W) (Og W hig Q)) x d₀
    (⟨fpt x d₀, hmem⟩ : Og W hig Q) (Scheme.Opens.ι_apply _ _)
  refine ⟨b, ?_⟩
  simp only [wg, Functor.map_comp, types_comp_apply]
  rw [hb, hd₀]

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
/-- `(𝟙 X)_* ≅ 𝟭`. -/
def pushId (X : Scheme.{u}) : push (𝟙 X) Λ ≅ 𝟭 (EtSh Λ X) :=
  Functor.sheafPushforwardContinuousId' (etPullId X) (ModuleCat.{u} Λ) X.smallEtaleTopology

end L7a

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

theorem δ₀_hom [IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0) (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) :
    δ₀ c a φ ht hP ≫ (chEt c φ).hom = ptz K (zc c a) (chart_hclA c a) := by
  have e : (δ₀ c a φ ht hP ≫ (chEt c φ).hom) ≫ P1.toSpecK K = 𝟙 _ :=
    (Category.assoc _ _ _).trans (pointOfClosedPoint_comp _ _ _)
  refine (pt_factor (P1.toSpecK K) (zc c a) (chart_hclA c a) _ ?_).trans
    ((eq_whisker e _).trans (Category.id_comp _))
  exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (chEt c φ).hom (δ₀_apply c a φ ht hP _)).trans
    (d₀_hom c a φ hP))

theorem fibD_sub [IsDedekindDomain B] (ht : φ.hom (X - C a) ≠ 0)
    (hP : (Ideal.span {φ.hom (X - C a)}).IsPrime) :
    Subsingleton ((geomPtAt (zc c a)).point.fiber.obj (chEt c φ)) := by
  have := chart_hGal c a
  exact ⟨fun n n' => fiber_eq_of_pt (zc c a) n n'
    ((fpt_eq_d₀ c a φ ht hP n).trans (fpt_eq_d₀ c a φ ht hP n').symm)⟩

end Pt

section Fib

end Fib

end RamanujanPetersson.EtPBC.EtMV

end

end


