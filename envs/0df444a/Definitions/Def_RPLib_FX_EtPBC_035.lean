-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_035
-- name    : RPLib_FX_EtPBC_035
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:00:11.277405+00:00
-- url     : https://prove2.me/theorems/dbb5f833-a1cd-5b96-9ef5-f478c73acbe9
-- title:
--   Proper base change for the projective line, library file 035
-- statement:
--   File 035 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
--   * `S4.Def_RP_EtPBC_A_CovPr13`: S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)
--   * `S4.Def_RP_EtPBC_A_CovG1`: S4-EtPBC-A, R4-T2 (A2a): sections of `O(d)` of a two-chart cover and their lifting along transitions
--   * `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
--   * `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
--   * `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
--   * `S4.Def_RP_EtPBC_A_CovLim2`: S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level
--   * `S4.Def_RP_EtPBC_A_CovAsN2`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables
--   * `S4.Def_RP_EtPBC_A_CovAsN3`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN3): the adic completion of a noetherian ring is noetherian
--   * `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
--   * `S4.Def_RP_EtPBC_A_Z2H1`: S4-EtPBC-A, (Z2a-c): `H¹` over the two charts, Artin-Rees, lifting mod `I^n`
--   * `S4.Def_RP_EtPBC_A_Z2Pi0`: S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood
--   * `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
--   * `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_Inj0b`: S4-EtPBC-A, G1b: base change in degree `0` on sections
--   * `S4.Def_RP_EtPBC_A_LocRep`: S4-EtPBC-A, M2 F6a: local representation of a section of `ι^* π_* C`
--   * `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
--   * `S4.Def_RP_EtPBC_A_FinGenA`: S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes
--   * `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
--   * `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
--   * `S4.Def_RP_EtPBC_A_FBCb`: S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective
--   * `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
--   * `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
--   * `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
--   * `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
--   * `S4.Def_RP_EtPBC_A_FGS`: S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre
--   * `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
--   * `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
--   * `S4.Def_RP_EtPBC_A_CovNbA`: S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed
--   * `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
--   * `S4.Def_RP_EtPBC_A_O2E1`: S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain
--   * `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
--   * `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
--   * `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
--   * `S4.Def_RP_EtPBC_A_O2Pb`: S4-EtPBC-A, O2 GLOB (O2Pb): the pullback square of `wm (prdMap d X)` and what it gives on global sections
--   * `S4.Def_RP_EtPBC_A_O2Gl1c`: S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2
--   * `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
--   * `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
--   * `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
--   * `S4.Def_RP_EtPBC_A_CovFix`: S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_028
import Definitions.Def_RPLib_FX_EtPBC_031

/-!
# Proper base change for the projective line, library file 035

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
* `S4.Def_RP_EtPBC_A_CovPr13`: S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)
* `S4.Def_RP_EtPBC_A_CovG1`: S4-EtPBC-A, R4-T2 (A2a): sections of `O(d)` of a two-chart cover and their lifting along transitions
* `S4.Def_RP_EtPBC_A_CovG2`: S4-EtPBC-A, R4-T2 (A2b): Serre vanishing modulo an ideal, uniformly along transitions
* `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
* `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
* `S4.Def_RP_EtPBC_A_CovLim2`: S4-EtPBC-A, R4-T2 (A2c-2b): `R`-combinations of compatible families at each level
* `S4.Def_RP_EtPBC_A_CovAsN2`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables
* `S4.Def_RP_EtPBC_A_CovAsN3`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN3): the adic completion of a noetherian ring is noetherian
* `S4.Def_RP_EtPBC_A_CovPr14`: S4-EtPBC-A, R4-T2 (A3n): the residue of a descended presentation on tensor charts
* `S4.Def_RP_EtPBC_A_Z2H1`: S4-EtPBC-A, (Z2a-c): `H¹` over the two charts, Artin-Rees, lifting mod `I^n`
* `S4.Def_RP_EtPBC_A_Z2Pi0`: S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood
* `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
* `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
* `S4.Def_RP_EtPBC_A_Inj0b`: S4-EtPBC-A, G1b: base change in degree `0` on sections
* `S4.Def_RP_EtPBC_A_LocRep`: S4-EtPBC-A, M2 F6a: local representation of a section of `ι^* π_* C`
* `S4.Def_RP_EtPBC_A_NbExt1`: S4-EtPBC-A, M2 F8a: comparison maps between `Y_s`, the fibre `Y_x` of Z4 and neighbourhoods
* `S4.Def_RP_EtPBC_A_FinGenA`: S4-EtPBC-A, M4(A): finitely many generating sections over AFFINE etale `P`-schemes
* `S4.Def_RP_EtPBC_A_FBCv`: S4-EtPBC-A, R4 (FBC-c, part 1): sections of a constant sheaf with prescribed values on a finite fibre
* `S4.Def_RP_EtPBC_A_FBCa`: S4-EtPBC-A, R4 (FBC-c, part 2): the restriction map `Φ_* M_{U₂} ⟶ (h ≫ Φ)_* M_{U₁}` and its values
* `S4.Def_RP_EtPBC_A_FBCb`: S4-EtPBC-A, R4 (FBC-c, part 3): the stalk of `rU` along a closed immersion is bijective
* `S4.Def_RP_EtPBC_A_FBCc`: S4-EtPBC-A, R4 (FBC-c, part 4): finite base change for constant sheaves along a closed immersion
* `S4.Def_RP_EtPBC_A_T3dB`: S4-EtPBC-A, R4-T3d (part B): closed points, sections by values, and the restriction mono `m`
* `S4.Def_RP_EtPBC_A_DescG5`: S4-EtPBC-A, R4-T1d (part 2): the sheets cover `U₀`, the descended section `σ`
* `S4.Def_RP_EtPBC_A_T3dC`: S4-EtPBC-A, R4-T3d (part C): compatibility of the base change maps, and the degree-one assembly
* `S4.Def_RP_EtPBC_A_FGS`: S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre
* `S4.Def_RP_EtPBC_A_DescK2`: S4-EtPBC-A, R4-T1 (assembly): the torsor of an extension of `Λ` by `π_{s*} N`
* `S4.Def_RP_EtPBC_A_EGeoB`: S4-EtPBC-A, M4(E), EGeoB: a splitting neighbourhood of a geometric point and its sections
* `S4.Def_RP_EtPBC_A_CovNbA`: S4-EtPBC-A, R4-T2 (G2a): `kapV` is an isomorphism; the fibre inclusion of a neighbourhood is closed
* `S4.Def_RP_EtPBC_A_O2Fs`: S4-EtPBC-A, O2 (MV route), Fs: stalks of free sheaves
* `S4.Def_RP_EtPBC_A_O2E1`: S4-EtPBC-A, O2 C-plan S4a: rings of finite type and unramified over a Dedekind domain
* `S4.Def_RP_EtPBC_A_O2P1`: S4-EtPBC-A, O2 M5 P1: purity for Kummer roots on a Dedekind domain (field theory)
* `S4.Def_RP_EtPBC_A_O2Gl2a`: S4-EtPBC-A, O2 GLOB (O2Gl2a): the algebra of stage S3
* `S4.Def_RP_EtPBC_A_O2E4`: S4-EtPBC-A, O2 C-plan S4c2: the punctured neighbourhood `D ×_P Uo` is `Spec B_t`
* `S4.Def_RP_EtPBC_A_O2Pb`: S4-EtPBC-A, O2 GLOB (O2Pb): the pullback square of `wm (prdMap d X)` and what it gives on global sections
* `S4.Def_RP_EtPBC_A_O2Gl1c`: S4-EtPBC-A, O2 GLOB (O2Gl1c): the geometric inputs of stages S1-S2
* `S4.Def_RP_EtPBC_A_O2Gl2h`: S4-EtPBC-A, O2 GLOB (O2Gl2h): stage S4 on the charts, the data `e`, `g`, `hHp`, `hHq` of `uk_diff`
* `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
* `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
* `S4.Def_RP_EtPBC_A_CovFix`: S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`
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

/-- The section of `ι^* Λ[g⁻¹ V]` over `ι⁻¹(g⁻¹ V)` given by the unit of `ι^* ⊣ ι_*`. -/
def unitSec (j : Nbhd s) :
    (fibFree Λ g s j).obj.obj (op ((etPull (fibι g s)).obj ((etPull g).obj j.1))) :=
  freeEquiv Λ ((etPull g).obj j.1) ((push (fibι g s) Λ).obj (fibFree Λ g s j))
    ((pullAdj (fibι g s) Λ).unit.app ((nbhdSys Λ g s).obj j))

/-- The global section `x_v` of `ι^* Λ[g⁻¹ V]`. -/
def fibSec (j : Nbhd s) : (fibFree Λ g s j).obj.obj (op (etId (fib g s))) :=
  ((fibFree Λ g s j).obj.map (nbhdSec g s j).op).hom (unitSec Λ g s j)

/-- `u_v : Λ_{P_s} ⟶ ι^* Λ[g⁻¹ V]`. -/
def bcUnit (j : Nbhd s) : unitSh Λ (fib g s) ⟶ (pull (fibι g s) Λ).obj ((nbhdSys Λ g s).obj j) :=
  ofSec (fibSec Λ g s j)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr13 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)

Over `A` with `χ : A →+* K`: `Ah` (the completion, residue `res`), `R'` (residue `χ'`, a section `s : K →+* R'`), a
chart `B`, a target `Q` with `ν : K →+* Q`, `βQ : B →+* Q` (`βQ ∘ algebraMap = ν ∘ χ`).
* `Jt B χ' = (ker χ') (R' ⊗ B)`; `tmul_mem_Jt`;
* **`kap`** `: R' ⊗[A] B →+* Q`, `r ⊗ b ↦ ν (χ' r) * βQ b` (`kap_tmul`), `Jt_le_ker_kap`;
* **`lamQ`** `: Ah ⊗[A] B →+* (R' ⊗[A] B) ⧸ Jt`, `â ⊗ b ↦ s (res â) ⊗ b` (`lamQ_tmul`), `lamQ_map`, `I_le_ker_lamQ`;
* `kap_map` (the two residues agree on `C ⊗ B`), **`exists_sec`** (the section for `resid_ker_pm`).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Tens

end Tens

section Lam

variable {K A R' B Ah : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Ah] [Algebra A Ah] (χ : A →+* K) (χ' : R' →+* K) (res : Ah →+* K) (s : K →+* R')
  (hres : ∀ a, res (algebraMap A Ah a) = χ a) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a) (hs : ∀ k, χ' (s k) = k)

theorem lamQ_tmul (x : Ah) (b : B) :
    lamQ χ χ' res s hres hχ' hs (x ⊗ₜ b) = Ideal.Quotient.mk (Jt B χ') (s (res x) ⊗ₜ b) := by
  change Ideal.Quotient.mk (Jt B χ') (s (res x) ⊗ₜ[A] (1 : B)) *
    Ideal.Quotient.mk (Jt B χ') ((1 : R') ⊗ₜ[A] b) = _
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Lam

end RamanujanPetersson.EtPBC.Cov

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

/-- **A transition maps sections of `O(d)` to sections of `O(d)`.** -/
def TwoCovHom.secMap (hτ₀ : π₀ t₀ = τ₀) (d : ℕ) : C'.sec d →+ C.sec d where
  toFun x := ⟨(H.ρ₀ x.1.1, H.ρ₁ x.1.2), by
    have e₀ : H.ρ (C'.ψ₀ x.1.1) = C.ψ₀ (H.ρ₀ x.1.1) := RingHom.congr_fun H.d₀ _
    have e₁ : H.ρ (C'.ψ₁ x.1.2) = C.ψ₁ (H.ρ₁ x.1.2) := RingHom.congr_fun H.d₁ _
    rw [TwoCov.mem_sec]
    rw [← e₀, ← e₁, ← H.u_map hτ₀, ← map_pow, ← map_mul, (C'.mem_sec d x.1).1 x.2]⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' := by
    intro x y
    apply Subtype.ext
    simp

end Hom

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

/-- **All of `E₀` satisfies `PI`** for `d ≥ max eᵢ`. -/
theorem TwoCov.PI_all (hv : C.u * C.ψ₁ (C.a₁ τ₁) = 1) {r : ℕ} {m : Fin r → C.E₀} {y : Fin r → C.E₁}
    {e : Fin r → ℕ} (hG : C.Good ι₀ I m y e) (hd : ∀ i, e i ≤ d) (x : C.E₀) : C.PI I d x := by
  obtain ⟨c, hc⟩ := hG.1 x
  refine TwoCov.PI_congr hc (TwoCov.PI_sum _ fun i => ?_)
  exact TwoCov.PI_eval ι₀ ι₁ hι hv (TwoCov.PI_gen hv (hG.2 i) (hd i)) (c i)

end Good

section Zero

end Zero

section Lift

variable {B₀ B₁ N b₀ b₁ n : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing b₀] [CommRing b₁]
  [CommRing n] {φ₀ : B₀ →+* N} {φ₁ : B₁ →+* N} {t₀ : B₀} {t₁ : B₁} {φb₀ : b₀ →+* n} {φb₁ : b₁ →+* n} {τ₀ : b₀}
  {τ₁ : b₁} {π₀ : B₀ →+* b₀} {π₁ : B₁ →+* b₁} {π : N →+* n} {C' : TwoCov φ₀ φ₁ t₀ t₁}
  {C : TwoCov φb₀ φb₁ τ₀ τ₁} (H : TwoCovHom π₀ π₁ π C' C) {R : Type u} [CommRing R]

/-- **Generators lift along a transition, with the same exponents.** -/
theorem TwoCovHom.good_lift (hτ₀ : π₀ t₀ = τ₀) (ι₀ : R →+* C.E₀) (ι₀' : R →+* C'.E₀)
    (hρι : H.ρ₀.comp ι₀' = ι₀) (I : Ideal C.E) (I' : Ideal C'.E) (hI : I.comap H.ρ ≤ I') {r : ℕ}
    {m : Fin r → C.E₀} {y : Fin r → C.E₁} {e : Fin r → ℕ} (hG : C.Good ι₀ I m y e) :
    ∃ (m' : Fin r → C'.E₀) (y' : Fin r → C'.E₁), C'.Good ι₀' I' m' y' e := by
  choose m' hm' using fun i => H.s₀ (m i)
  choose y' hy' using fun i => H.s₁ (y i)
  have ht : H.ρ₀ (C'.a₀ t₀) = C.a₀ τ₀ := (RingHom.congr_fun H.c₀ t₀).trans (congrArg C.a₀ hτ₀)
  have e₀ : ∀ z, H.ρ (C'.ψ₀ z) = C.ψ₀ (H.ρ₀ z) := fun z => RingHom.congr_fun H.d₀ z
  have e₁ : ∀ z, H.ρ (C'.ψ₁ z) = C.ψ₁ (H.ρ₁ z) := fun z => RingHom.congr_fun H.d₁ z
  have hu : H.ρ C'.u = C.u := H.u_map hτ₀
  refine ⟨m', y', fun x => ?_, fun i => ?_⟩
  · obtain ⟨c, hc⟩ := hG.1 (H.ρ₀ x)
    refine ⟨c, hI ?_⟩
    have hs : ∑ i, H.ρ₀ (eval₂ ι₀' (C'.a₀ t₀) (c i) * m' i) = ∑ i, eval₂ ι₀ (C.a₀ τ₀) (c i) * m i :=
      Finset.sum_congr rfl fun i _ => by rw [map_mul, hm', Polynomial.hom_eval₂, hρι, ht]
    rw [Ideal.mem_comap, e₀, map_sub, map_sum, hs]
    exact hc
  · apply hI
    rw [Ideal.mem_comap, map_sub, map_mul, map_pow, hu, e₀, e₁, hm', hy']
    exact hG.2 i

end Lift

section Ker

end Ker

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

theorem lq₁ (hJ₁ : J₁ = p.map ιB₁) : ∀ α ∈ p ^ (k + 1), H.ρ₁ (lι₁ ιB₁ C' α) = 0 := by
  intro α hα
  have hm : ιB₁ α ∈ J₁ ^ (k + 1) := by
    rw [hJ₁, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hα
  have h0 : Ideal.Quotient.mk (J₁ ^ (k + 1)) (ιB₁ α) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  rw [← RingHom.comp_apply, lρι₁ ιB₁ H]
  simp only [lι₁, RingHom.comp_apply]
  rw [h0, map_zero]

end Lv

section Tower

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] (φ₀ : B₀ →+* N)
  (φ₁ : B₁ →+* N) (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN)
  (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀) (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀))
  (hu₁ : IsUnit (φ₁ t₁)) (C₀ : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)
  (p : Ideal R)

theorem good_zero_tower (hts : φ₀ t₀ * φ₁ t₁ = 1) (hB : (eval₂RingHom ιB₀ t₀).Finite) :
    ∃ (r : ℕ) (m : Fin r → C₀.E₀) (y : Fin r → C₀.E₁) (e : Fin r → ℕ),
      C₀.Good (lι₀ ιB₀ C₀) (lI ιB₀ p C₀) m y e := by
  refine C₀.good_zero (lι₀ ιB₀ C₀) (lI ιB₀ p C₀) (lhv hts C₀) ?_
  have e : eval₂RingHom (lι₀ ιB₀ C₀) (C₀.a₀ (Ideal.Quotient.mk (J₀ ^ (0 + 1)) t₀)) =
      (C₀.a₀.comp (Ideal.Quotient.mk (J₀ ^ (0 + 1)))).comp (eval₂RingHom ιB₀ t₀) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [lι₀]
    · simp
  rw [e]
  exact (C₀.fin₀.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)).comp hB

include hφ₀ hφ₁ hu₀ hu₁

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers

* `dep_choice`, `seq_choice`: sequences by choice along `ℕ`;
* `ker_ρ₀`, `ker_ρ₁`: the kernels of a transition are `p^(k+1)` on the charts; `mem_of_ρ₀`, `mem_of_ρ₁`: an element whose
  image has entries in `p^n` (`n ≤ k+1`) has entries in `p^n`;
* **`Gam C H d`**: compatible families of sections of `O(d)` along a tower `C`, `H`; **`exists_gam`**: every level-`0`
  section lifts when all transitions are surjective on sections.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Ker

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R) {k : ℕ}
  {C' : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ (k + 1)} {C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k}
  (H : TwoCovHom (down J₀ k) (down J₁ k) (down JN k) C' C)

theorem mem_of_ρ₀ (hJ₀ : J₀ = p.map ιB₀) {n : ℕ} (hn : n ≤ k + 1) {z : C'.E₀}
    (hz : H.ρ₀ z ∈ (p ^ n).map (lι₀ ιB₀ C)) : z ∈ (p ^ n).map (lι₀ ιB₀ C') := by
  rw [← lρι₀ ιB₀ H, ← Ideal.map_map] at hz
  obtain ⟨z', hz', he⟩ := (Ideal.mem_map_iff_of_surjective _ H.s₀).1 hz
  have hk : z - z' ∈ RingHom.ker H.ρ₀ := by
    rw [RingHom.mem_ker, map_sub, he, sub_self]
  rw [ker_ρ₀ ιB₀ p H hJ₀] at hk
  have h := Ideal.add_mem _ hz' (Ideal.map_mono (Ideal.pow_le_pow_right hn) hk)
  rwa [add_sub_cancel] at h

theorem mem_of_ρ₁ (hJ₁ : J₁ = p.map ιB₁) {n : ℕ} (hn : n ≤ k + 1) {z : C'.E₁}
    (hz : H.ρ₁ z ∈ (p ^ n).map (lι₁ ιB₁ C)) : z ∈ (p ^ n).map (lι₁ ιB₁ C') := by
  rw [← lρι₁ ιB₁ H, ← Ideal.map_map] at hz
  obtain ⟨z', hz', he⟩ := (Ideal.mem_map_iff_of_surjective _ H.s₁).1 hz
  have hk : z - z' ∈ RingHom.ker H.ρ₁ := by
    rw [RingHom.mem_ker, map_sub, he, sub_self]
  rw [ker_ρ₁ ιB₁ p H hJ₁] at hk
  have h := Ideal.add_mem _ hz' (Ideal.map_mono (Ideal.pow_le_pow_right hn) hk)
  rwa [add_sub_cancel] at h

end Ker

section Fam

end Fam

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

/-- Coefficients congruent modulo `p^(m+1)` give the same level-`m` combination. -/
theorem lev_congr (hJ₀ : J₀ = p.map ιB₀) (hJ₁ : J₁ = p.map ιB₁) (m : ℕ) {c c' : Fin r → R}
    (hc : ∀ i, c i - c' i ∈ p ^ (m + 1)) : lev C ιB₀ ιB₁ σ m c = lev C ιB₀ ιB₁ σ m c' := by
  rw [← sub_eq_zero, ← lev_sub]
  refine Prod.ext ?_ ?_
  · rw [lev_fst, Prod.fst_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h := Ideal.mem_map_of_mem (lι₀ ιB₀ (C m)) (hc i)
    rw [lpow_bot₀ _ _ _ _ _ _ _ _ _ ιB₀ p hJ₀ (C m) le_rfl] at h
    rw [Pi.sub_apply, (Submodule.mem_bot _).1 h, zero_mul]
  · rw [lev_snd, Prod.snd_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h := Ideal.mem_map_of_mem (lι₁ ιB₁ (C m)) (hc i)
    rw [lpow_bot₁ _ _ _ _ _ _ _ _ _ ιB₁ p hJ₁ (C m) le_rfl] at h
    rw [Pi.sub_apply, (Submodule.mem_bot _).1 h, zero_mul]

end Lev

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

instance isPrecomplete_Xid [Fintype σ] : IsPrecomplete (Xid σ A) (MvPowerSeries σ A) := by
  refine ⟨fun f hf => ?_⟩
  have hmem : ∀ {m n : ℕ}, m ≤ n → f m - f n ∈ (Xid σ A) ^ m := fun hmn => (smod_Xid_iff _ _).mp (hf hmn)
  obtain ⟨L, hL⟩ : ∃ L : MvPowerSeries σ A, ∀ x, coeff x L = coeff x (f (x.degree + 1)) :=
    ⟨fun x => coeff x (f (x.degree + 1)), fun _ => rfl⟩
  refine ⟨L, fun n => (smod_Xid_iff _ _).mpr ?_⟩
  refine mem_Xid_pow_of_coeff n _ fun x hx => ?_
  have h1 := coeff_zero_of_mem_Xid_pow (hmem (show x.degree + 1 ≤ n by omega)) x (Nat.lt_succ_self _)
  rw [map_sub, sub_eq_zero] at h1
  rw [map_sub, hL, sub_eq_zero]
  exact h1.symm

end HatN2

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

theorem hatPhi_surjective (hp : (Ideal.span (Set.range a)).FG) : Function.Surjective (hatPhi a) := by
  haveI := AdicCompletion.isAdicComplete_self (Ideal.span (Set.range a)) hp
  haveI : IsHausdorff ((Xid σ A).map (hatPhi a)) (AdicCompletion (Ideal.span (Set.range a)) A) := by
    rw [map_Xid_hatPhi]
    infer_instance
  refine surjective_of_mk_map_comp_surjective (I := Xid σ A) (hatPhi a) fun z => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ (Ideal.span (Set.range a)) y)
  refine ⟨C c, ?_⟩
  rw [RingHom.comp_apply, hatPhi_C, Ideal.Quotient.eq, map_Xid_hatPhi,
    ← AdicCompletion.ker_evalOneₐ_eq_map _ hp, RingHom.mem_ker, map_sub, sub_eq_zero]
  change AdicCompletion.evalOneₐ _ (algebraMap A _ c) = AdicCompletion.evalOneₐ _ y
  rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, hc]

end HatN3

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

/-- The comparison map `Ah ⊗ B → Pres (gmap (mk Jt) (gmap f' gC))` for `resid_ker_pm`. -/
def lamT (s : K →+* R') (hs : ∀ k, χ' (s k) = k) :
    Ah ⊗[A] B →+* Pres (gmap (Ideal.Quotient.mk (Jt B χ')) (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC)) :=
  (algebraMap ((R' ⊗[A] B) ⧸ Jt B χ')
    (Pres (gmap (Ideal.Quotient.mk (Jt B χ')) (gmap (Algebra.TensorProduct.map σ (AlgHom.id A B)).toRingHom gC)))).comp
    (lamQ χ χ' res s hres hχ' hs)

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z2H1 =====
section

/-!
# S4-EtPBC-A, (Z2a-c): `H¹` over the two charts, Artin-Rees, lifting mod `I^n`

Two-chart data as in `Z1.twoChart_fg`: `φ₀ : M₀ →ₗ[A[X]] N`, `φ₁ : M₁ →ₗ[A] N` with `X • φ₁ (X • m) = φ₁ m`.
`W := φ₀(M₀) + φ₁(M₁)` (`chartIm`), so that `H¹ = N / W`.

* **`h1_span`**: if `M₁` is finite over `A[X]`, every `y ∈ N` is `X^k • φ₁ b` and every `φ₁ m` is moved into the
  image of `φ₀` by a power of `X`, then `N = U + W` with `U` finite over `A` (`H¹` is finite over `A`).
* **`artinRees_sup`**: `N = U + W` with `U` finite, `A` noetherian: `∃ c, ∀ n, I^(n+c) N ∩ W ≤ I^n W`.
* **`lift_twoChart`**: `∃ c, ∀ n a b, φ₀ a - φ₁ b ∈ I^(n+c) N → ∃ a' b', φ₀ a' = φ₁ b'` with `a' ≡ a`, `b' ≡ b`
  mod `I^n`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

open RamanujanPetersson.EtPBC.Z1

universe u v w w'

variable {A : Type u} [CommRing A]

section Span

variable {M₀ : Type v} {M₁ : Type w} {N : Type w'}
  [AddCommGroup M₀] [Module A[X] M₀] [Module A M₀] [IsScalarTower A A[X] M₀]
  [AddCommGroup M₁] [Module A[X] M₁] [Module A M₁] [IsScalarTower A A[X] M₁]
  [AddCommGroup N] [Module A[X] N] [Module A N] [IsScalarTower A A[X] N]

/-- **`H¹` over the two charts is finite over `A`**: `N = U + W` with `U` finite over `A`. -/
theorem h1_span [Module.Finite A[X] M₁] (φ₀ : M₀ →ₗ[A[X]] N) (φ₁ : M₁ →ₗ[A] N)
    (h₁ : ∀ m, (X : A[X]) • φ₁ ((X : A[X]) • m) = φ₁ m)
    (hgen : ∀ m : M₁, ∃ (d : ℕ) (a : M₀), φ₀ a = (X ^ d : A[X]) • φ₁ m)
    (hloc : ∀ y : N, ∃ (k : ℕ) (b : M₁), y = (X ^ k : A[X]) • φ₁ b) :
    ∃ U : Submodule A N, U.FG ∧ U ⊔ chartIm φ₀ φ₁ = ⊤ := by
  classical
  obtain ⟨m, w, hw⟩ := Module.Finite.exists_fin (R := A[X]) (M := M₁)
  choose d a ha using fun j => hgen (w j)
  set D : ℕ := ∑ j, d j with hD
  let S : Finset N := (Finset.univ : Finset (Fin m × Fin D)).image
    fun p => (X ^ (p.2 : ℕ) : A[X]) • φ₁ (w p.1)
  refine ⟨Submodule.span A (S : Set N), ⟨S, rfl⟩, ?_⟩
  set V := Submodule.span A (S : Set N) ⊔ chartIm φ₀ φ₁ with hV
  have hC₁ : ∀ (c : A) (y : M₁), (C c : A[X]) • y = c • y := fun c y => by
    rw [← algebraMap_eq, algebraMap_smul]
  have step1 : ∀ (j : Fin m) (l : ℕ), (X ^ l : A[X]) • φ₁ (w j) ∈ V := by
    intro j l
    by_cases hl : l < D
    · exact Submodule.mem_sup_left (Submodule.subset_span (Finset.mem_coe.2
        (Finset.mem_image.2 ⟨(j, ⟨l, hl⟩), Finset.mem_univ _, rfl⟩)))
    · have hdj : d j ≤ l := le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le (d i))
        (Finset.mem_univ j)) (not_lt.1 hl)
      rw [← Nat.sub_add_cancel hdj, pow_add, mul_smul, ← ha j, ← map_smul]
      exact Submodule.mem_sup_right (mem_chartIm₀ φ₀ φ₁ _)
  have step2 : ∀ (j : Fin m) (k i : ℕ), (X ^ k : A[X]) • φ₁ ((X ^ i : A[X]) • w j) ∈ V := by
    intro j k i
    by_cases hik : i ≤ k
    · rw [← Nat.sub_add_cancel hik, pow_add, mul_smul, pow_smul_iter φ₁ h₁ i (w j)]
      exact step1 j (k - i)
    · have hki : k ≤ i := le_of_lt (not_le.1 hik)
      rw [← Nat.sub_add_cancel hki, pow_add, mul_comm, mul_smul, pow_smul_iter φ₁ h₁ k]
      exact Submodule.mem_sup_right (mem_chartIm₁ φ₀ φ₁ _)
  have step3 : ∀ (j : Fin m) (k : ℕ) (c : A[X]), (X ^ k : A[X]) • φ₁ (c • w j) ∈ V := by
    intro j k c
    induction c using Polynomial.induction_on' with
    | add p q hp hq => rw [add_smul, map_add, smul_add]; exact V.add_mem hp hq
    | monomial i c =>
      rw [← C_mul_X_pow_eq_monomial, mul_smul, hC₁, map_smul, smul_comm]
      exact V.smul_mem c (step2 j k i)
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨k, b, rfl⟩ := hloc y
  have hb : b ∈ Submodule.span A[X] (Set.range w) := hw ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A[X]).1 hb
  rw [map_sum, Finset.smul_sum]
  exact V.sum_mem fun j _ => step3 j k (c j)

end Span

section ArtinRees

end ArtinRees

section Lift

end Lift
end RamanujanPetersson.EtPBC.Z2
end

end

-- ===== S4.Def_RP_EtPBC_A_Z2Pi0 =====
section

/-!
# S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood

Algebraic form of the `π₀` lemma: `A` noetherian, `p` prime, chart algebras `B₀` (over `A[t]`), `B₁` (over `A[s]`),
both finite over `A[X]`, overlap algebra `N`, `φ₀ : B₀ →ₐ[A[X]] N`, `φ₁ : B₁ →ₐ[A] N`.

* `secAlg φ₀ φ₁`: the global sections `{(a, b) | φ₀ a = φ₁ b}` as an `A`-subalgebra of `B₀ × B₁`;
  `secAlg_finite`: it is finite over `A` (Z1, `twoChart_fg`).
* `fibreMap p φ₀ φ₁ : secAlg →ₐ[A] κ(p) ⊗ B₀ × κ(p) ⊗ B₁` and `fibreUnit p B₀ B₁`.
* `includeRight_eq_of_sub_mem`: `x ≡ y mod p B` gives `1 ⊗ x = 1 ⊗ y` in `κ(p) ⊗ B`.
* **`exists_etale_idem_twoChart`**: chart elements `ε₀`, `ε₁` idempotent mod `p` and agreeing mod `p` on the overlap
  come, after an etale `A → A'` with a prime `P` over `p` and `κ(p) ≅ κ(P)`, from an idempotent of `A' ⊗ secAlg`.
-/

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

open RamanujanPetersson.EtPBC.Z1

universe u v w w'

variable {A : Type u} [CommRing A]

section Fib

end Fib

section TwoChart

variable {B₀ : Type v} {B₁ : Type w} {N : Type w'}
  [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
  [CommRing B₁] [Algebra A[X] B₁] [Algebra A B₁] [IsScalarTower A A[X] B₁]
  [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N]

omit [Algebra A[X] B₁] [IsScalarTower A A[X] B₁] in
theorem secAlg_toSubmodule (φ₀ : B₀ →ₐ[A[X]] N) (φ₁ : B₁ →ₐ[A] N) :
    Subalgebra.toSubmodule (secAlg φ₀ φ₁) = twoChart φ₀.toLinearMap φ₁.toLinearMap := by
  ext x
  rw [Subalgebra.mem_toSubmodule, mem_secAlg, mem_twoChart]
  rfl

end TwoChart

end RamanujanPetersson.EtPBC.Z2

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

theorem res_struct (i : Fin 2) (h : Yc K gV π 0 ⊓ Yc K gV π 1 ≤ Yc K gV π i) (a : Γ(V, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom ((π.app (Qc K gV i)).hom ((ac K gV i).hom a)) = (strN K gV π).hom a :=
  congrArg (fun φ => φ.hom a) (res_struct_hom K gV π i h)

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN

theorem towN : IsScalarTower Γ(V, ⊤) (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    change (strN K gV π).hom a = (resY0 K gV π).hom
      ((π.app (Qc K gV 0)).hom (Polynomial.eval₂ (ac K gV 0).hom (tc K gV 0 1) (Polynomial.C a)))
    rw [Polynomial.eval₂_C]
    exact (res_struct K gV π 0 inf_le_left a).symm

attribute [local instance] tow0 tow1 towN

/-- The restriction `Γ(Y₁) → Γ(Y₀₁)` as a `Γ(V)`-algebra map. -/
def φY1 : Γ(Y, Yc K gV π 1) →ₐ[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) where
  __ := (resY1 K gV π).hom
  commutes' a := res_struct K gV π 1 inf_le_right a

theorem algXN_X : algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) Polynomial.X =
    resY0 K gV π (π.app (Qc K gV 0) (tc K gV 0 1)) :=
  congrArg (resY0 K gV π) (algX0_X K gV π)

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

/-- **`Γ(Y, U) → Γ(Y_x, fx⁻¹ U)` is surjective** (`U` affine). -/
theorem fx_app_surj [IsAffine V] (hx : x ≫ gV = 𝟙 _) (hU : IsAffineOpen U) :
    Function.Surjective ((fx K gV π x).app U).hom := by
  have hinj := appLE_injective_of_eq (jT K gV π x U) (image_jT K gV π x U) (top_le_jT K gV π x U)
  have hs := pushout_inl_surj (isPushout_T K gV π x U hU) (appTop_surj K gV x hx)
  have hρ := ConcreteCategory.bijective_of_isIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge)
  intro y
  obtain ⟨c, hc⟩ := hs (((jT K gV π x U).appLE (fx K gV π x ⁻¹ᵁ U) ⊤ (top_le_jT K gV π x U)).hom y)
  obtain ⟨b, rfl⟩ := hρ.2 c
  refine ⟨b, hinj ?_⟩
  have h := congrArg (fun φ => φ.hom b) (jT_fx K gV π x U)
  exact h.trans hc

end Fib

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCv =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`

`directed_of_range`: directedness of an open cover from its ranges. **`covV`**: the open cover of `Y_{V'} = Y ×_V Spec R'`
by the charts `Spec (R' ⊗ Γ(Y₀₁))`, `Spec (R' ⊗ Γ(Y₀))`, `Spec (R' ⊗ Γ(Y₁))`, indexed by `WalkingSpan`
(`zero ↦ Y₀₁`), with transition maps the `span` of the chart restrictions `a0`, `a1`; instance `LocallyDirected`.
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
  (π : Y ⟶ PV K gV) [IsAffine V] [IsAffineHom π] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

omit [IsAffine V] [IsAffineHom π] in
theorem hA01 : CommRingCat.ofHom (algebraMap Γ(V, ⊤) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) =
    strU K gV π (Yc K gV π 0 ⊓ Yc K gV π 1) := rfl

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0b =====
section

/-!
# S4-EtPBC-A, G1b: base change in degree `0` on sections

For `g : P ⟶ S`, a geometric point `s`, an etale neighbourhood `j = (V, v)` and a class
`α ∈ Ext^0(Λ[g⁻¹ V], G)`, let `sec0 α ∈ G(g⁻¹ V)` be the corresponding section.
* `bc_zero_eq`: `bc_j α = mk₀ (u_v ≫ ι^* α)`;
* **`sec_of_bc_zero`**: if `bc_j α = 0` then the section `σ_v^* η_G(sec0 α)` of `ι^* G` over `P_s` vanishes
  (`η` the unit of `ι^* ⊣ ι_*`, `σ_v = nbhdSec` the section of `ι⁻¹(g⁻¹ V) ⟶ P_s` given by `v`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.PtSec
  RamanujanPetersson.EtCompact.Supp

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- The section of `G` over `g⁻¹ V` of a degree-`0` class. -/
def sec0 (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0) :
    G.obj.obj (op ((etPull g).obj j.1)) :=
  freeEquiv Λ ((etPull g).obj j.1) G (Ext.addEquiv₀ α)

theorem bc_zero_eq (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0) :
    Delta.bc (pull (fibι g s) Λ) (nbhdSys Λ g s) (unitSh Λ (fib g s)) (bcUnit Λ g s) j G 0 α =
      Ext.mk₀ (bcUnit Λ g s j ≫ (pull (fibι g s) Λ).map (Ext.addEquiv₀ α)) := by
  conv_lhs => rw [← Ext.mk₀_addEquiv₀_apply α]
  rw [Delta.bc_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_LocRep =====
section

/-!
# S4-EtPBC-A, M2 F6a: local representation of a section of `ι^* π_* C`

For `ι : X ⟶ P`, `π : Y ⟶ P`, `G = π_* C` (`C = constSh Λ Y M`) and `b : Λ_X ⟶ ι^* G`:
* `germ_elem`: germs along an arrow of the category of elements;
* **`exists_pullRep`**: near any geometric point `y` of `X` there are `W`, an etale `U ⟶ ι⁻¹ W` through `y` and
  `z ∈ C(π⁻¹ W)` with `b(1)|_U = η(z)|_U`;
* **`xi_of_pullRep`**: for such a representation, `ξ_{y'}(b)` at every geometric point `y'` through `U` is the germ
  of `z` at the corresponding point.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp RamanujanPetersson.EtCompact.PtSec

universe u

variable {Λ : Type u} [CommRing Λ] {X P Y : Scheme.{u}} (ι : X ⟶ P) (π : Y ⟶ P) {M : ModuleCat.{u} Λ}

/-- **Local representation of a section of `ι^* π_* C`.** -/
theorem exists_pullRep (y : GeomPt X) (b : unitSh Λ X ⟶ (pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))) :
    ∃ (W : P.Etale) (U : X.Etale) (h : U ⟶ (etPull ι).obj W) (_ : y.point.fiber.obj U)
      (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj W))),
      sc b U = (((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj.map h.op).hom
        ((((pullAdj ι Λ).unit.app ((push π Λ).obj (constSh Λ Y M))).hom.app (op W)).hom z) := by
  obtain ⟨j, z, hz⟩ := exists_rep π (y.map ι) (xi ι y ((push π Λ).obj (constSh Λ Y M)) b)
  have e2 := (pullStalkIso_germ ι y ((push π Λ).obj (constSh Λ Y M)) j.1 ((fiberMapIso ι y).hom.app j.1 j.2) z).trans
    ((congrArg (fun w => ((y.map ι).point.toPresheafFiber j.1 w
      ((push π Λ).obj (constSh Λ Y M)).obj).hom z) (fiberMapIso_inv_hom ι y j.1 j.2)).trans hz)
  have e3 := pullStalkIso_inj ι y ((push π Λ).obj (constSh Λ Y M)) e2
  obtain ⟨U, f₁, f₀, u, hs⟩ := exists_common_rep y.point ((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj
    (j₁ := ⟨(etPull ι).obj j.1, (fiberMapIso ι y).hom.app j.1 j.2⟩) (j₀ := ⟨etId X, y.top⟩) _ _ e3
  exact ⟨j.1, U, f₁, u, z, (sc_map b f₀).symm.trans hs.symm⟩

/-- **`ξ` along a local representation.** -/
theorem xi_of_pullRep (b : unitSh Λ X ⟶ (pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M)))
    {W : P.Etale} {U : X.Etale} (h : U ⟶ (etPull ι).obj W) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj W)))
    (hb : sc b U = (((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj.map h.op).hom
        ((((pullAdj ι Λ).unit.app ((push π Λ).obj (constSh Λ Y M))).hom.app (op W)).hom z))
    (y : GeomPt X) (u : y.point.fiber.obj U) :
    xi ι y ((push π Λ).obj (constSh Λ Y M)) b =
      ((y.map ι).point.toPresheafFiber W ((fiberMapIso ι y).inv.app W (y.point.fiber.map h u))
        ((push π Λ).obj (constSh Λ Y M)).obj).hom z := by
  have e0 := ConcreteCategory.congr_hom (y.point.toPresheafFiber_w ((etId_isTerminal X).from U) u
    ((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj) (sc b (etId X))
  have ht : y.point.fiber.map ((etId_isTerminal X).from U) u = y.top := y.eq_top _
  have e1 := ConcreteCategory.congr_hom (y.point.toPresheafFiber_w h u
    ((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj)
    ((((pullAdj ι Λ).unit.app ((push π Λ).obj (constSh Λ Y M))).hom.app (op W)).hom z)
  have e2 : (y.point.toPresheafFiber (etId X) y.top
      ((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj).hom (sc b (etId X)) =
      (y.point.toPresheafFiber ((etPull ι).obj W) (y.point.fiber.map h u)
        ((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj).hom
        ((((pullAdj ι Λ).unit.app ((push π Λ).obj (constSh Λ Y M))).hom.app (op W)).hom z) := by
    refine (congrArg (fun w => (y.point.toPresheafFiber (etId X) w
      ((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj).hom (sc b (etId X))) ht.symm).trans ?_
    refine e0.symm.trans ?_
    refine (congrArg (y.point.toPresheafFiber U u
      ((pull ι Λ).obj ((push π Λ).obj (constSh Λ Y M))).obj).hom
      ((sc_map b ((etId_isTerminal X).from U)).trans hb)).trans ?_
    exact e1
  exact (congrArg ((pullStalkIso ι Λ y).hom.app ((push π Λ).obj (constSh Λ Y M))).hom e2).trans
    (pullStalkIso_germ ι y ((push π Λ).obj (constSh Λ Y M)) W (y.point.fiber.map h u) z)

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

/-- **`Y_s` is a retract of `Y_x`.** -/
theorem eYV_eY'V (hv : v ≫ hj = s.pt) : eYV K gK s π hj v hv ≫ eY'V K gK s π hj v hv = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [eYV, eY'V, ysV, Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_fst_assoc,
      pullback.lift_snd]
  · simp only [Category.assoc, Category.id_comp, eY'V, pullback.lift_snd]
    apply pullback.hom_ext
    · simp only [eYV, fibW, ysV, fibV, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.lift_snd]
    · simp only [eYV, fibW, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, sg_inv, Category.comp_id]

section Ext

end Ext

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

section Gen

variable {Λ : Type u} [CommRing Λ] {X P : Scheme.{u}} (ι : X ⟶ P)

/-- **Local representation by a section over an affine `W`.** -/
theorem exists_pullRepG_aff (G : EtSh Λ P) (y : GeomPt X) (b : unitSh Λ X ⟶ (pull ι Λ).obj G) :
    ∃ (W : P.Etale) (U : X.Etale) (h : U ⟶ (etPull ι).obj W) (_ : y.point.fiber.obj U) (z : G.obj.obj (op W)),
      IsAffine W.left ∧ sc b U = (((pull ι Λ).obj G).obj.map h.op).hom ((((pullAdj ι Λ).unit.app G).hom.app (op W)).hom z) := by
  obtain ⟨j, z, hj, hz⟩ := exists_repG_aff (y.map ι) G (xi ι y G b)
  have e2 := (pullStalkIso_germ ι y G j.1 ((fiberMapIso ι y).hom.app j.1 j.2) z).trans
    ((congrArg (fun w => ((y.map ι).point.toPresheafFiber j.1 w G.obj).hom z) (fiberMapIso_inv_hom ι y j.1 j.2)).trans hz)
  have e3 := pullStalkIso_inj ι y G e2
  obtain ⟨U, f₁, f₀, u, hs⟩ := exists_common_rep y.point ((pull ι Λ).obj G).obj
    (j₁ := ⟨(etPull ι).obj j.1, (fiberMapIso ι y).hom.app j.1 j.2⟩) (j₀ := ⟨etId X, y.top⟩) _ _ e3
  exact ⟨j.1, U, f₁, u, z, hj, (sc_map b f₀).symm.trans hs.symm⟩

end Gen

section Red

end Red

end RamanujanPetersson.EtPBC

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

/-- **`R' ⊗_{Γ(W)} Γ(U) → Γ(U', ⊤)`.** -/
def PhiU (hg : algebraMap Γ(W, ⊤) Γ(U, ⊤) = g.appTop.hom)
    (h' : algebraMap Γ(W, ⊤) Γ(U', ⊤) = (f₁ ≫ hV W R').appTop.hom) (hf : f₂ ≫ g = f₁ ≫ hV W R') :
    R' ⊗[Γ(W, ⊤)] Γ(U, ⊤) →ₐ[Γ(W, ⊤)] Γ(U', ⊤) :=
  Algebra.TensorProduct.lift (fRU R' f₁ h') (gEU g R' f₁ f₂ hg h' hf) (fun _ _ => Commute.all _ _)

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

theorem rU_app (V : P.Etale) (z : (constSh Λ U₂ M).obj.obj (op ((etPull Φ).obj V))) :
    ((rU M h Φ).hom.app (op V)).hom z =
      ((constSh Λ U₁ M).obj.map (kapU h Φ V).op).hom (((uC h M).hom.app (op ((etPull Φ).obj V))).hom z) := rfl

/-- **Values of `rU`.** -/
theorem cval_rU (V : P.Etale) (z : (constSh Λ U₂ M).obj.obj (op ((etPull Φ).obj V)))
    (w : ((etPull (h ≫ Φ)).obj V).left) :
    cval (((rU M h Φ).hom.app (op V)).hom z) w = cval z (muU h Φ V w) :=
  (cval_map (kapU h Φ V) _ w).trans ((cval_uC h z _).trans
    (congrArg (cval z) (congrArg (fun φ => φ.base w) (kapL_fst h Φ V))))

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

theorem rStk_germ (t : GeomPt P) (j : Nbhd t) (z : (constSh Λ U M).obj.obj (op ((etPull Φ).obj j.1))) :
    ((t.point.presheafFiber (A := ModuleCat.{u} Λ)).map (rU M (pullback.fst Φ ι) Φ).hom).hom
        ((t.point.toPresheafFiber j.1 j.2 ((push Φ Λ).obj (constSh Λ U M)).obj).hom z) =
      (t.point.toPresheafFiber j.1 j.2 ((push (pullback.fst Φ ι ≫ Φ) Λ).obj (constSh Λ (pullback Φ ι) M)).obj).hom
        (((rU M (pullback.fst Φ ι) Φ).hom.app (op j.1)).hom z) :=
  congrArg (fun φ => φ.hom z) (t.point.toPresheafFiber_naturality (rU M (pullback.fst Φ ι) Φ).hom j.1 j.2)

end Stalk

end RamanujanPetersson.EtPBC.FBC

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

variable (M) in
/-- Restriction of sections to `U_s = U ×_P Ps`, landing in `ι_* φs_* M`. -/
def rC : (push Φ Λ).obj (constSh Λ U M) ⟶
    (push ι Λ).obj ((push (pullback.snd Φ ι) Λ).obj (constSh Λ (pullback Φ ι) M)) :=
  rU M (pullback.fst Φ ι) Φ ≫ eqToHom (push_obj_eq_of_eq pullback.condition _) ≫
    (pushCompIso Λ (pullback.snd Φ ι) ι).inv.app _

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

variable {U₁ U₂ P : Scheme.{u}} (h : U₁ ⟶ U₂) (Φ₂ : U₂ ⟶ P) (Φ₁ : U₁ ⟶ P) (hh : h ≫ Φ₂ = Φ₁)

variable (M) in
/-- Restriction along a commutative triangle `h ≫ Φ₂ = Φ₁`. -/
def rUq : (push Φ₂ Λ).obj (constSh Λ U₂ M) ⟶ (push Φ₁ Λ).obj (constSh Λ U₁ M) :=
  rU M h Φ₂ ≫ eqToHom (push_obj_eq_of_eq hh _)

theorem cval_rUq (V : P.Etale) (z : (constSh Λ U₂ M).obj.obj (op ((etPull Φ₂).obj V)))
    (w : ((etPull Φ₁).obj V).left) :
    cval (((rUq M h Φ₂ Φ₁ hh).hom.app (op V)).hom z) w = cval z (muq h Φ₂ Φ₁ hh V w) := by
  subst hh
  simp only [rUq, eqToHom_refl, Category.comp_id]
  exact cval_rU h Φ₂ V z w

end RUq

section M

variable {P P' Y U : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (Φ : U ⟶ P') (h : U ⟶ Y) (hh : h ≫ π = Φ ≫ f)

variable (M) in
/-- `π_* M_Y ⟶ f_* Φ_* M_U`: restriction of sections along `h`. -/
def mS : (push π Λ).obj (constSh Λ Y M) ⟶ (push f Λ).obj ((push Φ Λ).obj (constSh Λ U M)) :=
  rUq M h π (Φ ≫ f) hh ≫ (pushCompIso Λ Φ f).inv.app _

variable (M) in
/-- **The restriction map** `f^* π_* M_Y ⟶ Φ_* M_U` (adjoint of `mS`). -/
def mP : (pull f Λ).obj ((push π Λ).obj (constSh Λ Y M)) ⟶ (push Φ Λ).obj (constSh Λ U M) :=
  ((pullAdj f Λ).homEquiv _ _).symm (mS M π f Φ h hh)

variable [Etale f]

variable (M) in
/-- The same map through `f^* ≅ res f`. -/
def mR : (res f Λ).obj ((push π Λ).obj (constSh Λ Y M)) ⟶ (push Φ Λ).obj (constSh Λ U M) :=
  ((resAdj f Λ).homEquiv _ _).symm (mS M π f Φ h hh)

theorem mP_eq : mP M π f Φ h hh = (pullIsoRes f Λ).hom.app _ ≫ mR M π f Φ h hh := by
  rw [mP, mR, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, ← Category.assoc,
    ← (pullIsoRes f Λ).hom.naturality, Category.assoc, pullIsoRes, Adjunction.leftAdjointUniq_hom_app_counit]

theorem mR_app (W : P'.Etale) (z : (constSh Λ Y M).obj.obj (op ((etPull π).obj ((etComp f).obj W)))) :
    ((mR M π f Φ h hh).hom.app (op W)).hom z =
      ((constSh Λ U M).obj.map ((etPull Φ).map ((etCompAdj f).unit.app W)).op).hom
        (((mS M π f Φ h hh).hom.app (op ((etComp f).obj W))).hom z) := by
  rw [mR]
  exact (resAdj_symm_app f (mS M π f Φ h hh) W z).trans
    (congrArg (fun m => ModuleCat.Hom.hom m (((mS M π f Φ h hh).hom.app (op ((etComp f).obj W))).hom z))
      (push_obj_map_hom Φ (constSh Λ U M) ((etCompAdj f).unit.app W)))

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

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom] (U : X.AffineZariskiSite)

theorem kL_w {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ V.left) (h : g₁ ≫ vh V = g₂ ≫ vh V)
    (hg₁ : ∀ z, vh V (g₁ z) ∈ U.1) (hg₂ : ∀ z, vh V (g₂ z) ∈ U.1) :
    kL V U g₁ g₂ h hg₁ hg₂ ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (CU V U ⊗[Γ(X, U.1)] CU V U))) ≫ U.2.fromSpec =
      g₁ ≫ vh V := by
  have hA : CommRingCat.ofHom (algebraMap Γ(X, U.1) (CU V U)) ≫
      CommRingCat.ofHom (j1 Γ(X, U.1) (CU V U)).toRingHom =
      CommRingCat.ofHom (algebraMap Γ(X, U.1) (CU V U ⊗[Γ(X, U.1)] CU V U)) :=
    CommRingCat.hom_ext (RingHom.ext fun r => (j1 Γ(X, U.1) (CU V U)).commutes r)
  rw [← hA, Spec.map_comp, Category.assoc, kL_j1_assoc, liftU_alg]

end Pt

section Cover

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

theorem rC_eq {U P Ps : Scheme.{u}} (Φ : U ⟶ P) (ι : Ps ⟶ P) :
    rC M Φ ι = rUq M (pullback.fst Φ ι) Φ (pullback.snd Φ ι ≫ ι) pullback.condition ≫
      (pushCompIso Λ (pullback.snd Φ ι) ι).inv.app _ := by
  simp only [rC, rUq, Category.assoc]

section C1

variable {P P' Y U Ps : Scheme.{u}} (π : Y ⟶ P) (f : P' ⟶ P) (Φ : U ⟶ P') (h : U ⟶ Y)
  (hh : h ≫ π = Φ ≫ f) (ι' : Ps ⟶ P')

variable (M) in
/-- **Restriction on the fibre** `π_{s*} M_{Y_s} ⟶ φs_* M_{U_s}` along `hsU`. -/
def rUs (ι : Ps ⟶ P) (hι : ι' ≫ f = ι) :
    (push (pullback.snd π ι) Λ).obj (constSh Λ (pullback π ι) M) ⟶
      (push (pullback.snd Φ ι') Λ).obj (constSh Λ (pullback Φ ι') M) :=
  rUq M (hsU π f Φ h hh ι' ι hι) (pullback.snd π ι) (pullback.snd Φ ι') (hsU_snd π f Φ h hh ι' ι hι)

theorem cval_rUs (ι : Ps ⟶ P) (hι : ι' ≫ f = ι) (V : Ps.Etale)
    (z : (constSh Λ (pullback π ι) M).obj.obj (op ((etPull (pullback.snd π ι)).obj V)))
    (w : ((etPull (pullback.snd Φ ι')).obj V).left) :
    cval (((rUs M π f Φ h hh ι' ι hι).hom.app (op V)).hom z) w =
      cval z (muq (hsU π f Φ h hh ι' ι hι) (pullback.snd π ι) (pullback.snd Φ ι') (hsU_snd π f Φ h hh ι' ι hι)
        V w) :=
  cval_rUq _ _ _ _ V z w

end C1

section B3

variable {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

variable (Λ) in
/-- **The input of T1 + T2** (fibre form): every extension `0 → π_{s*} M_{Y_s} → E' → Λ → 0` on the fibre
is split, after an etale neighbourhood `f` with a closed lift `ι'` of the fibre and a finite `Φ : U ⟶ P'`
covering `P' ×_P Y`, by an extension `κ₀` of the fibre restriction `rUs`. -/
def HypT {Y : Scheme.{u}} (π : Y ⟶ P) (N : ModuleCat.{u} Λ) : Prop :=
  ∀ (E' : EtSh Λ (fib g s))
    (a' : (push (pullback.snd π (fibι g s)) Λ).obj (constSh Λ (pullback π (fibι g s)) N) ⟶ E')
    (b' : E' ⟶ unitSh Λ (fib g s)) (w' : a' ≫ b' = 0), (ShortComplex.mk a' b' w').ShortExact →
    ∃ (P' U : Scheme.{u}) (f : P' ⟶ P) (_ : Etale f) (ι' : fib g s ⟶ P') (hι : ι' ≫ f = fibι g s)
      (_ : IsClosedImmersion ι') (Φ : U ⟶ P') (_ : IsFinite Φ) (h : U ⟶ Y) (hh : h ≫ π = Φ ≫ f)
      (_ : Function.Surjective ⇑(pullback.lift Φ h hh.symm : U ⟶ pullback f π))
      (κ₀ : E' ⟶ (push (pullback.snd Φ ι') Λ).obj (constSh Λ (pullback Φ ι') N)),
      a' ≫ κ₀ = rUs N π f Φ h hh ι' (fibι g s) hι

end B3

end RamanujanPetersson.EtPBC.T3d

end

end

-- ===== S4.Def_RP_EtPBC_A_FGS =====
section

/-!
# S4-EtPBC-A, R2(a,b): sections over compact etale objects, and local lifts on the whole fibre

* `exists_affine_refine'`: finite affine refinement of a covering sieve of a COMPACT etale object;
* `exists_cover_lift`: for an epimorphism `S.g` and a global section `q` of `S.X₃` on a compact `Y`, an affine etale
  surjection `V ⟶ Y` and a section of `S.X₂` over `V` lifting `q`;
* `isAffine_nv1`: `V ×_Y V` is affine when `V` is affine and `V ⟶ Y` is an affine morphism;
* `exists_common_rep'`, `exists_fib_at`, `exists_pullRepS`: local representation of a section of `ι^* G` over `U`;
* **`exists_fg_sec`**: a section `d` of `ι^* G` over a compact `U` is killed by every `p : G ⟶ Q` that kills
  finitely many sections `z x ∈ G(W x)` over affines.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite GrothendieckTopology Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtCompact.Supp

universe u

section Refine

end Refine

section Gen

variable {Λ : Type u} [CommRing Λ] {X P : Scheme.{u}} (ι : X ⟶ P)

/-- **Local representation of a section of `ι^* G` over `U`** near a fibre element `w`. -/
theorem exists_pullRepS (G : EtSh Λ P) (y : GeomPt X) (U : X.Etale) (w : y.point.fiber.obj U)
    (d : ((pull ι Λ).obj G).obj.obj (op U)) :
    ∃ (W : P.Etale) (U' : X.Etale) (h : U' ⟶ (etPull ι).obj W) (f₀ : U' ⟶ U) (u : y.point.fiber.obj U')
      (z : G.obj.obj (op W)), IsAffine W.left ∧ y.point.fiber.map f₀ u = w ∧
      (((pull ι Λ).obj G).obj.map f₀.op).hom d =
        (((pull ι Λ).obj G).obj.map h.op).hom ((((pullAdj ι Λ).unit.app G).hom.app (op W)).hom z) := by
  obtain ⟨j, z, hj, hz⟩ := exists_repG_aff (y.map ι) G
    (((pullStalkIso ι Λ y).hom.app G).hom ((y.point.toPresheafFiber U w ((pull ι Λ).obj G).obj).hom d))
  have e2 := (pullStalkIso_germ ι y G j.1 ((fiberMapIso ι y).hom.app j.1 j.2) z).trans
    ((congrArg (fun w => ((y.map ι).point.toPresheafFiber j.1 w G.obj).hom z)
      (fiberMapIso_inv_hom ι y j.1 j.2)).trans hz)
  have e3 := pullStalkIso_inj ι y G e2
  obtain ⟨U', f₁, f₀, u, hu, hs⟩ := exists_common_rep' y.point ((pull ι Λ).obj G).obj
    (j₁ := ⟨(etPull ι).obj j.1, (fiberMapIso ι y).hom.app j.1 j.2⟩) (j₀ := ⟨U, w⟩) _ _ e3
  exact ⟨j.1, U', f₁, f₀, u, z, hj, hu, hs.symm⟩

end Gen

end RamanujanPetersson.EtPBC

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

/-- **`Φ_*(uC h) = rU h Φ`** (after `pushCompIso`). -/
theorem push_uC_comp : (push Φ Λ).map (uC h M) ≫ (pushCompIso Λ h Φ).hom.app (constSh Λ U₁ M) = rU M h Φ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V => by
    change (uC h M).hom.app (op ((etPull Φ).obj V.unop)) ≫
        ((pushCompIso Λ h Φ).hom.app (constSh Λ U₁ M)).hom.app V =
      (uC h M).hom.app (op ((etPull Φ).obj V.unop)) ≫ (constSh Λ U₁ M).obj.map (kapU h Φ V.unop).op
    rw [pushCompIso_hom_app, kapU_eq]; rfl))

theorem rU_congr {h₁ h₂ : U₁ ⟶ U₂} (e : h₁ = h₂) {Φ₁ : U₁ ⟶ P} (p₁ : h₁ ≫ Φ = Φ₁)
    (p₂ : h₂ ≫ Φ = Φ₁) :
    rU M h₁ Φ ≫ eqToHom (push_obj_eq_of_eq p₁ _) = rU M h₂ Φ ≫ eqToHom (push_obj_eq_of_eq p₂ _) := by
  subst e
  rfl

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

/-- **A neighbourhood through which all points of the `W j` over `x̄` factor.** -/
theorem exists_split (x : P) {J : Type u} [Finite J] (W : J → P.Etale) [∀ j, QuasiCompact (W j).hom] :
    ∃ (T : P.Etale) (t : (geomPtAt x).point.fiber.obj T) (τ : ∀ p : FibPts x W, T ⟶ W p.1),
      IsAffine T.left ∧ ∀ p, (geomPtAt x).point.fiber.map (τ p) t = p.2 := by
  have := finite_fibPts x W
  obtain ⟨j', a, hj'⟩ := exists_common_nbhd (geomPtAt x)
    (fun p : FibPts x W => (⟨W p.1, p.2⟩ : Nbhd (geomPtAt x)))
  exact ⟨j'.1, j'.2, fun p => (a p).1, hj', fun p => (a p).2⟩

section Prd

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

instance isIso_kapV : IsIso (kapV K gK π hj R') :=
  ⟨⟨kapInv K gK π hj R', kapV_kapInv K gK π hj R', kapInv_kapV K gK π hj R'⟩⟩

end Kap

section Fib

end Fib

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

theorem stalkFree_germ (W : P.Etale) (x : P) (a : (geomPtAt x).point.fiber.obj W) :
    (stalkFree Λ W x).hom (germ (freeSh Λ W) x a (taut Λ W)) = Finsupp.single a 1 := by
  have := isIso_fib (Λ := Λ) W x
  have e3 := congrArg (fun ψ => ψ.hom (ModuleCat.freeMk (R := Λ) (𝟙 W)))
    (GrothendieckTopology.Point.toPresheafFiber_naturality (Φ := (geomPtAt x).point)
      (toSheafify P.smallEtaleTopology (freePre Λ W)) W a)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e3
  have hg : germ (freeSh Λ W) x a (taut Λ W) =
      (((geomPtAt x).point.presheafFiber (A := ModuleCat.{u} Λ)).map
        (toSheafify P.smallEtaleTopology (freePre Λ W))).hom
        (((geomPtAt x).point.toPresheafFiber W a (freePre Λ W)).hom (ModuleCat.freeMk (𝟙 W))) := by
    rw [germ, taut_eq]
    exact e3.symm
  have h := congrArg (fun ψ => ψ.hom (((geomPtAt x).point.toPresheafFiber W a (freePre Λ W)).hom
    (ModuleCat.freeMk (𝟙 W)))) (IsIso.hom_inv_id_assoc (((geomPtAt x).point.presheafFiber
      (A := ModuleCat.{u} Λ)).map (toSheafify P.smallEtaleTopology (freePre Λ W))) (fibDesc Λ W x))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hg, stalkFree, ModuleCat.hom_comp]
  refine (LinearMap.comp_apply _ _ _).trans (h.trans ?_)
  refine (toPresheafFiber_fibDesc W x a (ModuleCat.freeMk (𝟙 W))).trans ?_
  change Finsupp.mapDomain _ (Finsupp.single (𝟙 W) 1) = _
  rw [Finsupp.mapDomain_single, FunctorToTypes.map_id_apply]

end RamanujanPetersson.EtPBC.FreeStk

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

end Dom

section Loc

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B]
  [Algebra.FormallyUnramified A B] [Module.Flat A B] [IsNoetherianRing B]

/-- **`B_q` is a domain** when `B` is flat and unramified over `A` and `q` lies over a maximal `(π)`, `π ≠ 0`. -/
theorem isDomain_atPrime (q : Ideal B) [q.IsPrime] (π : A) (hπ : q.under A = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hp : (q.under A).IsMaximal) : IsDomain (Localization.AtPrime q) := by
  have ht := maximalIdeal_eq_span A B q π hπ hp
  have hfl : Module.Flat A (Localization.AtPrime q) := Module.Flat.trans A B (Localization.AtPrime q)
  have hreg : IsSMulRegular (Localization.AtPrime q) π :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
  have hreg' : IsRegular (algebraMap B (Localization.AtPrime q) (algebraMap A B π)) := by
    rw [← IsScalarTower.algebraMap_apply]
    have hl : IsLeftRegular (algebraMap A (Localization.AtPrime q) π) := fun x y hxy => hreg (by
      show π • x = π • y
      rw [Algebra.smul_def, Algebra.smul_def]
      exact hxy)
    exact isLeftRegular_iff_isRegular.1 hl
  exact isDomain_of_span_regular _ ht hreg'

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

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  (S : Submonoid B) [IsLocalization S Bt] (hS : S ≤ nonZeroDivisors B)
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]

include hS in
/-- **Roots unramified over a localization have divisible valuations** at the primes of `B` it keeps. -/
theorem dvd_log_of_mem_maxUnram {d : ℕ} {α : AlgebraicClosure K} (hα : α ∈ maxUnram Bt K) {u : K}
    (hu : α ^ d = algebraMap K (AlgebraicClosure K) u) (p : HeightOneSpectrum B)
    (hp : Disjoint (S : Set B) p.asIdeal) : (d : ℤ) ∣ WithZero.log (p.valuation K u) := by
  obtain ⟨L, hL, hle⟩ := exists_unramSet_of_finite (A := Bt) (K := K) {α}
    (fun x hx => by rw [Finset.mem_singleton] at hx; exact hx ▸ hα)
  have hαL : α ∈ L :=
    hle (IntermediateField.subset_adjoin K _ (Finset.mem_coe.2 (Finset.mem_singleton_self _)))
  haveI : FiniteDimensional K L := hL.1
  haveI : IsGalois K L := hL.2.1
  have hI : InertiaTrivial Bt K L := fun Q hQ => inertia_eq_bot_of_unramSet hL Q hQ
  have hαN : (⟨α, hαL⟩ : L) ^ d = algebraMap K L u := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact hu
  have h := dvd_log_valuation_of_inertia Bt K L hI hαN (locPt S hS p hp)
  rwa [valuation_locPt] at h

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

theorem liveMod_notMem (x v : Y) (hv : ∀ Q : minimalPrimes Y, v ∉ (Q : Ideal Y)) (Q : minimalPrimes Y) :
    liveMod h x v ∉ (Q : Ideal Y) := by
  classical
  rw [← Ideal.Quotient.eq_zero_iff_mem, mk_liveMod]
  split_ifs with hx
  · rw [Ideal.Quotient.eq_zero_iff_mem]; exact hv Q
  · rw [Ideal.Quotient.eq_zero_iff_mem]; exact hx

end Live

section Glob'

end Glob'

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

/-- **`W₁ ≅ D ×_P Uo`** in `P.Etale`. -/
def isoT : W1 c φ a ≅ prd (chEt c φ) (opEt Uo) :=
  MorphismProperty.Over.isoMk (isoTl c φ hUo) (by
    show (isoTl c φ hUo).hom ≫ pullback.snd (chEt c φ).hom (opEt Uo).hom ≫ (opEt Uo).hom =
      Spec.map (φ ≫ locT φ a) ≫ c
    rw [← pullback.condition, ← Category.assoc, isoTl_fst, spec_locT_comp]
    rfl)

section Cls

end Cls

end T

end RamanujanPetersson.EtPBC.EtMV

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

/-- **Zar**: over `D₁ = Spec B_f`, `Γ(W) → Γ(W₁)` is the localization away from `bW f`. -/
theorem isLocalization_away_wm {B : CommRingCat.{u}} (hB : Spec B ⟶ P) [Etale hB] (f : B)
    (hB' : Spec (CommRingCat.of (Localization.Away f)) ⟶ P) [Etale hB']
    (d : Scheme.Etale.mk hB' ⟶ Scheme.Etale.mk hB)
    (hd : d.left = Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f)))) (X : P.Etale)
    [IsAffine ((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left] :
    letI := (wm (R := R) (prdMap d X)).appTop.hom.toAlgebra
    IsLocalization.Away (bW hB X R f) Γ(((etPull (prd (Scheme.Etale.mk hB') X).hom).obj R).left, ⊤) := by
  have h := (isPushout_bW R hB hB' _ d hd X).flip
  letI : Algebra B Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤) := (bW hB X R).hom.toAlgebra
  letI : Algebra (Localization.Away f) Γ(((etPull (prd (Scheme.Etale.mk hB') X).hom).obj R).left, ⊤) :=
    (bW hB' X R).hom.toAlgebra
  letI : Algebra Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤)
      Γ(((etPull (prd (Scheme.Etale.mk hB') X).hom).obj R).left, ⊤) :=
    (wm (R := R) (prdMap d X)).appTop.hom.toAlgebra
  letI : Algebra B Γ(((etPull (prd (Scheme.Etale.mk hB') X).hom).obj R).left, ⊤) :=
    ((wm (R := R) (prdMap d X)).appTop.hom.comp (bW hB X R).hom).toAlgebra
  have : IsScalarTower B Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤)
      Γ(((etPull (prd (Scheme.Etale.mk hB') X).hom).obj R).left, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B (Localization.Away f)
      Γ(((etPull (prd (Scheme.Etale.mk hB') X).hom).obj R).left, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w).symm
  have hP : Algebra.IsPushout B (Localization.Away f) Γ(((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left, ⊤)
      Γ(((etPull (prd (Scheme.Etale.mk hB') X).hom).obj R).left, ⊤) :=
    (CommRingCat.isPushout_iff_isPushout (R := B) (R' := Localization.Away f)).1 h
  have hL := (Algebra.isLocalization_iff_isPushout (Submonoid.powers f) (Localization.Away f)).2
    ((Algebra.IsPushout.comm _ _ _ _).1 hP)
  rw [Algebra.algebraMapSubmonoid_powers] at hL
  exact hL

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

end Gam

section Gen

variable {P : Scheme.{u}} (R : P.Etale)

/-- (Gen) **`Γ(W₁) = B'[Γ(W)]`** along a chart map `d` with `d.left = Spec.map ι`. -/
theorem mem_adjoin_wm {B B' : CommRingCat.{u}} (hB : Spec B ⟶ P) [Etale hB] (hB' : Spec B' ⟶ P) [Etale hB']
    (ι : B ⟶ B') (d : Scheme.Etale.mk hB' ⟶ Scheme.Etale.mk hB) (hd : d.left = Spec.map ι) (X : P.Etale)
    [IsAffine ((etPull (prd (Scheme.Etale.mk hB) X).hom).obj R).left] :
    letI := (bW hB' X R).hom.toAlgebra
    ∀ x : Γ(((etPull (prd (Scheme.Etale.mk hB') X).hom).obj R).left, ⊤),
      x ∈ Algebra.adjoin B' (Set.range (wm (R := R) (prdMap d X)).appTop.hom) := by
  let _ : Algebra B' Γ(((etPull (prd (Scheme.Etale.mk hB') X).hom).obj R).left, ⊤) := (bW hB' X R).hom.toAlgebra
  exact fun x => mem_adjoin_of_isPushout (isPushout_bW R hB hB' ι d hd X) rfl x

end Gen

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

/-- The ring square `B₁ → Γ(W₁) → Γ(W₂)` = `B₁ → B₂ → Γ(W₂)`. -/
theorem wm_bW₂ (ι : B₁ ⟶ B₂) (hd : d₂₁.left = Spec.map ι) (b : B₁) :
    (wm (R := R) (prdMap d₂₁ (opEt Uo))).appTop ((bW (Spec.map φ₁ ≫ c) (opEt Uo) R).hom b) =
      (bW (Spec.map φ₂ ≫ c) (opEt Uo) R).hom (ι.hom b) :=
  congrArg (fun f => f.hom b) (isPushout_bW R (Spec.map φ₁ ≫ c) (Spec.map φ₂ ≫ c) ι d₂₁ hd (opEt Uo)).w

end S4

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

variable [IsClosedImmersion i]

/-- MVG1-shaped summary for `wg`. -/
theorem graph_good (Q : P.Opens) (x : P) (hx : (geomPtAt x).pt = ((geomPtAt x).pt ≫ g) ≫ i) (hxQ : x ∈ Q)
    (c : (geomPtAt x).point.fiber.obj (Zs i g W)) :
    (∀ a a', (geomPtAt x).point.fiber.map (wg W hig Q) a = c → (geomPtAt x).point.fiber.map (wg W hig Q) a' = c →
      a = a') ∧ ∃ a, (geomPtAt x).point.fiber.map (wg W hig Q) a = c :=
  ⟨fun a a' ha ha' => graph_unique W hig Q x hx a a' (ha.trans ha'.symm), graph_exists W hig Q x hx hxQ c⟩

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
/-- `e_*` is an equivalence for an isomorphism `e`. -/
def pushEquiv {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] : EtSh Λ X ≌ EtSh Λ Y :=
  CategoryTheory.Equivalence.mk (push e Λ) (push (inv e) Λ)
    ((pushId Λ X).symm ≪≫ pushCongr Λ (IsIso.hom_inv_id e).symm ≪≫ (pushCompIso Λ e (inv e)).symm)
    (pushCompIso Λ (inv e) e ≪≫ pushCongr Λ (IsIso.inv_hom_id e) ≪≫ pushId Λ Y)

instance push_isEquivalence {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] : (push e Λ).IsEquivalence :=
  (pushEquiv Λ e).isEquivalence_functor

end L7a

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFix =====
section

/-!
# S4-EtPBC-A, R4-T2 (G'): the geometric half of T2 from the corrected statement `CoverLiftAt₂`

* `ker_χV`, `ker_beta`: the fibre charts `Γ(Y, U) ↠ Γ(Y_x, fx⁻¹ U)` have kernel `(ker χ) Γ(Y, U)` (`Z3.ker_fx_app`);
* **`nonempty_liftD₂`**: `CoverLiftAt₂` at `x` gives the lift data `LiftD` (as `nonempty_liftD` from `CoverLiftAt`);
* **`liftT_core₂`**, **`liftT_of_coverLiftAt₂`**: `CoverLiftAt₂` at `xV` gives `T2.LiftT (qV K gK) s π`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

section Ker

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V)

/-- **The fibre chart kernel**: `ker (Γ(Y, U) ↠ Γ(Y_x, fx⁻¹ U)) = (ker χ) Γ(Y, U)` for any presentation `f` of the
structure map. -/
theorem ker_beta [IsAffine V] (hx : x ≫ gV = 𝟙 _) (U : Y.Opens) (hU : IsAffineOpen U) (f : Γ(V, ⊤) →+* Γ(Y, U))
    (hf : f = (strU K gV π U).hom) :
    letI := algKV K gV; RingHom.ker ((fx K gV π x).app U).hom = (RingHom.ker (χV K gV x hx)).map f := by
  letI := algKV K gV
  subst hf
  rw [ker_fx_app K gV π x U hx hU, ker_χV K gV x hx]

end Ker

section Cover

attribute [local instance] algKY

attribute [local instance] algT

end Cover

end RamanujanPetersson.EtPBC.Cov

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.Cov

universe u

section Main

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.eR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁ CoverLift.f₀ CoverLift.f₁ CoverLift.et₀ CoverLift.et₁

end Main

end RamanujanPetersson.EtPBC

end

end


