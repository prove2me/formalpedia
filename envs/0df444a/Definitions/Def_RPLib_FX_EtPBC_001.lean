-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_001
-- name    : RPLib_FX_EtPBC_001
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:29:51.477225+00:00
-- url     : https://prove2.me/theorems/b373b427-07c7-51fd-83eb-58cd934ef82e
-- title:
--   Proper base change for the projective line, library file 001
-- statement:
--   File 001 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_P1`: S4-EtCompact, part 11: the projective line `P^1_K = Proj K[X₀, X₁]` (O6, explicit compactifications)
--   * `S4.Def_RP_EtSheaves_Const`: S4-EtSheaves, part 3: constant, locally constant and lisse etale sheaves
--   * `S4.Def_RP_EtSheaves_PullComp`: S4-EtSheaves, part 4: pullback along a composite; pullback preserves (locally) constant sheaves
--   * `S4.Def_RP_EtSheaves_Lsh`: S4-EtSheaves, part 12: extension by zero `j_!`
--   * `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
--   * `S4.Def_RP_EtSheaves_StalkRes`: S4-EtSheaves, part 38: stalks of a restriction, on germs
--   * `S4.Def_RP_EtCompact_LerayG`: S4-EtCompact, part 40: a two-row Leray argument for `g_*` (CC4, formal part)
--   * `S4.Def_RP_EtSheaves_PullTens`: S4-EtSheaves, part 27: pullback is monoidal along every morphism
--   * `S4.Def_RP_Kummer_Lev`: S4-Kummer, part K5b: Kummer roots at a constant level `F_m = F ⊗ 𝔽_{q^m}`
--   * `S4.Def_RP_ThetaCube_Cst`: S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
--   * `S4.Def_RP_EtCompact_GalTr`: S4-EtCompact (b3a): Galois actions on stalks along etale maps and isomorphisms of geometric points
--   * `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
--   * `S4.Def_RP_EtCompact_GGerm`: S4-EtCompact, (c) T1 SpOne part 1: germs of global sections
--   * `S4.Def_RP_EtCompact_PushStk`: S4-EtCompact, (c) T3: stalks of `j_*` at points of `U`, and boundary points of `P¹`
--   * `S4.Def_RP_EtCompact_ParSuf`: S4-EtCompact, (c) T5a: `j_*` keeps an extension of `Λ_U` short exact when it is unramified at the boundary
--   * `S4.Def_RP_EtCompact_PtSec`: S4-EtCompact, E7 (O9c-2): global sections of sheaves supported on finitely many closed points
--   * `S4.Def_RP_EtPBC_A_FreeSh`: S4-EtPBC-A, L1a: free sheaves on objects of the small etale site
--   * `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
--   * `S4.Def_RP_EtPBC_A_ConstVal`: S4-EtPBC-A, M2a: values of sections of a constant sheaf
--   * `S4.Def_RP_EtPBC_A_NilLift`: S4-EtPBC-A, R4-F1a/b: etale algebras lift uniquely along nilpotent thickenings
--   * `S4.Def_RP_EtPBC_A_CovL1`: S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map
--   * `S4.Def_RP_EtPBC_A_CovAR`: S4-EtPBC-A, R4-T2 (A2c-1b): uniform relations of `p` on the base charts (Artin-Rees)
--   * `S4.Def_RP_EtPBC_A_CovAs1`: S4-EtPBC-A, R4-T2 (A3 assembly, As1): base change of the chart data along a flat algebra
--   * `S4.Def_RP_EtPBC_A_CovAs1b`: S4-EtPBC-A, R4-T2 (A3 assembly, As1b): finiteness and noetherianity of base-changed charts
--   * `S4.Def_RP_EtPBC_A_CovL3`: S4-EtPBC-A, R4-T2 (A1c): the tower of nilpotent lifts of a two-chart etale cover
--   * `S4.Def_RP_EtPBC_A_CovPr11`: S4-EtPBC-A, R4-T2 (A3k): the residue map of an approximated presentation
--   * `S4.Def_RP_EtPBC_A_CovPr12`: S4-EtPBC-A, R4-T2 (A3l): the kernel of reduction mod `J` on a presentation, and `resid_ker` with that target
--   * `S4.Def_RP_EtPBC_A_CovPr13`: S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)
--   * `S4.Def_RP_EtPBC_A_CovAs2`: S4-EtPBC-A, R4-T2 (A3 assembly, As2): the level-0 cover over generic charts, and the fibre kernel
--   * `S4.Def_RP_EtPBC_A_CovFl`: S4-EtPBC-A, R4-T2 (A2c-1c): relations on a flat level-`m` chart come from the base (equational criterion)
--   * `S4.Def_RP_EtPBC_A_CovFil1`: S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations
--   * `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
--   * `S4.Def_RP_EtPBC_A_CovLim4`: S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring
--   * `S4.Def_RP_EtPBC_A_Z1Core`: S4-EtPBC-A, (Z1) algebraic core: a degree bound on the two charts of `P¹_A`
--   * `S4.Def_RP_EtPBC_A_Z1Two`: S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module
--   * `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
--   * `S4.Def_RP_EtPBC_A_CovFq`: S4-EtPBC-A, R4-T2 (A2c-5, E3c1): generic inputs of the etale-on-a-basic-open step
--   * `S4.Def_RP_EtPBC_A_CovFe`: S4-EtPBC-A, R4-T2 (A2c-5, E3c2): etale on a basic open
--   * `S4.Def_RP_EtPBC_A_LocFlat`: S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)
--   * `S4.Def_RP_EtPBC_A_LocFree`: S4-EtPBC-A, R4-T2 (A2c-5, E3b2): the primes over `J` lie in the free locus
--   * `S4.Def_RP_EtPBC_A_CovUnr`: S4-EtPBC-A, R4-T2 (A2c-5c): unramified at the primes over `J` (Nakayama on `Ω`)
--   * `S4.Def_RP_EtPBC_A_CovSp`: S4-EtPBC-A, R4-T2 (A2, properness input): `1` is not an `m`-polynomial in both `x` and `x⁻¹`
--   * `S4.Def_RP_EtPBC_A_CovGlob`: S4-EtPBC-A, R4-T2 (A2c-5a): closed loci on `P¹` that miss the closed fibre are empty
--   * `S4.Def_RP_EtPBC_A_CovLoc`: S4-EtPBC-A, R4-T2 (A2c-5b): being etale at a prime transports along a localization square
--   * `S4.Def_RP_EtPBC_A_CovEtL`: S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)
--   * `S4.Def_RP_EtPBC_A_CovAs3c`: S4-EtPBC-A, R4-T2 (A3 assembly, As3c): finite generating families of extended ideals
--   * `S4.Def_RP_EtPBC_A_CovAs3e`: S4-EtPBC-A, R4-T2 (A3 assembly, As3e): residue and base-change facts for the instantiation over `Â`
--   * `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
--   * `S4.Def_RP_EtPBC_A_CovAsN2`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables
--   * `S4.Def_RP_EtPBC_A_CovAs3f`: S4-EtPBC-A, R4-T2 (A3 assembly, As3f): the completed cover over `Â` from the `CoverLiftAt₂` data
--   * `S4.Def_RP_EtPBC_A_CovAs4a`: S4-EtPBC-A, R4-T2 (A3 assembly, As4a): a map between two localizations away from `t` is bijective
--   * `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
--   * `S4.Def_RP_EtPBC_A_CovPr7`: S4-EtPBC-A, R4-T2 (A3g): flat descent of vanishing tensors to finitely generated subalgebras
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_ArtinApprox_02
import Definitions.Def_RPLib_FX_EtP1_45

/-!
# Proper base change for the projective line, library file 001

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_P1`: S4-EtCompact, part 11: the projective line `P^1_K = Proj K[X₀, X₁]` (O6, explicit compactifications)
* `S4.Def_RP_EtSheaves_Const`: S4-EtSheaves, part 3: constant, locally constant and lisse etale sheaves
* `S4.Def_RP_EtSheaves_PullComp`: S4-EtSheaves, part 4: pullback along a composite; pullback preserves (locally) constant sheaves
* `S4.Def_RP_EtSheaves_Lsh`: S4-EtSheaves, part 12: extension by zero `j_!`
* `S4.Def_RP_EtSheaves_CutSet`: S4-EtSheaves, part 21: `F_S` for a subset `S`
* `S4.Def_RP_EtSheaves_StalkRes`: S4-EtSheaves, part 38: stalks of a restriction, on germs
* `S4.Def_RP_EtCompact_LerayG`: S4-EtCompact, part 40: a two-row Leray argument for `g_*` (CC4, formal part)
* `S4.Def_RP_EtSheaves_PullTens`: S4-EtSheaves, part 27: pullback is monoidal along every morphism
* `S4.Def_RP_Kummer_Lev`: S4-Kummer, part K5b: Kummer roots at a constant level `F_m = F ⊗ 𝔽_{q^m}`
* `S4.Def_RP_ThetaCube_Cst`: S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
* `S4.Def_RP_EtCompact_GalTr`: S4-EtCompact (b3a): Galois actions on stalks along etale maps and isomorphisms of geometric points
* `S4.Def_RP_EtCompact_PushBC`: S4-EtCompact (b2'): pushforward commutes with restriction to an etale chart
* `S4.Def_RP_EtCompact_GGerm`: S4-EtCompact, (c) T1 SpOne part 1: germs of global sections
* `S4.Def_RP_EtCompact_PushStk`: S4-EtCompact, (c) T3: stalks of `j_*` at points of `U`, and boundary points of `P¹`
* `S4.Def_RP_EtCompact_ParSuf`: S4-EtCompact, (c) T5a: `j_*` keeps an extension of `Λ_U` short exact when it is unramified at the boundary
* `S4.Def_RP_EtCompact_PtSec`: S4-EtCompact, E7 (O9c-2): global sections of sheaves supported on finitely many closed points
* `S4.Def_RP_EtPBC_A_FreeSh`: S4-EtPBC-A, L1a: free sheaves on objects of the small etale site
* `S4.Def_RP_EtPBC_A_BCMap`: S4-EtPBC-A, L1d: the data of the base change map at a geometric point
* `S4.Def_RP_EtPBC_A_ConstVal`: S4-EtPBC-A, M2a: values of sections of a constant sheaf
* `S4.Def_RP_EtPBC_A_NilLift`: S4-EtPBC-A, R4-F1a/b: etale algebras lift uniquely along nilpotent thickenings
* `S4.Def_RP_EtPBC_A_CovL1`: S4-EtPBC-A, R4-T2 (A1a): away maps, localized base change and the reduction map
* `S4.Def_RP_EtPBC_A_CovAR`: S4-EtPBC-A, R4-T2 (A2c-1b): uniform relations of `p` on the base charts (Artin-Rees)
* `S4.Def_RP_EtPBC_A_CovAs1`: S4-EtPBC-A, R4-T2 (A3 assembly, As1): base change of the chart data along a flat algebra
* `S4.Def_RP_EtPBC_A_CovAs1b`: S4-EtPBC-A, R4-T2 (A3 assembly, As1b): finiteness and noetherianity of base-changed charts
* `S4.Def_RP_EtPBC_A_CovL3`: S4-EtPBC-A, R4-T2 (A1c): the tower of nilpotent lifts of a two-chart etale cover
* `S4.Def_RP_EtPBC_A_CovPr11`: S4-EtPBC-A, R4-T2 (A3k): the residue map of an approximated presentation
* `S4.Def_RP_EtPBC_A_CovPr12`: S4-EtPBC-A, R4-T2 (A3l): the kernel of reduction mod `J` on a presentation, and `resid_ker` with that target
* `S4.Def_RP_EtPBC_A_CovPr13`: S4-EtPBC-A, R4-T2 (A3m): the residue data on tensor charts (no presentations)
* `S4.Def_RP_EtPBC_A_CovAs2`: S4-EtPBC-A, R4-T2 (A3 assembly, As2): the level-0 cover over generic charts, and the fibre kernel
* `S4.Def_RP_EtPBC_A_CovFl`: S4-EtPBC-A, R4-T2 (A2c-1c): relations on a flat level-`m` chart come from the base (equational criterion)
* `S4.Def_RP_EtPBC_A_CovFil1`: S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations
* `S4.Def_RP_EtPBC_A_CovLim1`: S4-EtPBC-A, R4-T2 (A2c-2a): compatible families of sections along a tower of level covers
* `S4.Def_RP_EtPBC_A_CovLim4`: S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring
* `S4.Def_RP_EtPBC_A_Z1Core`: S4-EtPBC-A, (Z1) algebraic core: a degree bound on the two charts of `P¹_A`
* `S4.Def_RP_EtPBC_A_Z1Two`: S4-EtPBC-A, (Z1): sections over the two charts of `P¹_A` form a finite `A`-module
* `S4.Def_RP_EtPBC_A_CovHat8`: S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`
* `S4.Def_RP_EtPBC_A_CovFq`: S4-EtPBC-A, R4-T2 (A2c-5, E3c1): generic inputs of the etale-on-a-basic-open step
* `S4.Def_RP_EtPBC_A_CovFe`: S4-EtPBC-A, R4-T2 (A2c-5, E3c2): etale on a basic open
* `S4.Def_RP_EtPBC_A_LocFlat`: S4-EtPBC-A, R4-T2 (A2c-5, E3b1): the local criterion for flatness (finite modules over a local ring)
* `S4.Def_RP_EtPBC_A_LocFree`: S4-EtPBC-A, R4-T2 (A2c-5, E3b2): the primes over `J` lie in the free locus
* `S4.Def_RP_EtPBC_A_CovUnr`: S4-EtPBC-A, R4-T2 (A2c-5c): unramified at the primes over `J` (Nakayama on `Ω`)
* `S4.Def_RP_EtPBC_A_CovSp`: S4-EtPBC-A, R4-T2 (A2, properness input): `1` is not an `m`-polynomial in both `x` and `x⁻¹`
* `S4.Def_RP_EtPBC_A_CovGlob`: S4-EtPBC-A, R4-T2 (A2c-5a): closed loci on `P¹` that miss the closed fibre are empty
* `S4.Def_RP_EtPBC_A_CovLoc`: S4-EtPBC-A, R4-T2 (A2c-5b): being etale at a prime transports along a localization square
* `S4.Def_RP_EtPBC_A_CovEtL`: S4-EtPBC-A, R4-T2 (A2c-5, E4b1): etale on `P¹` from etale near the closed fibre (generic)
* `S4.Def_RP_EtPBC_A_CovAs3c`: S4-EtPBC-A, R4-T2 (A3 assembly, As3c): finite generating families of extended ideals
* `S4.Def_RP_EtPBC_A_CovAs3e`: S4-EtPBC-A, R4-T2 (A3 assembly, As3e): residue and base-change facts for the instantiation over `Â`
* `S4.Def_RP_EtPBC_A_CovAsN1`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN1): power series map onto the adic completion
* `S4.Def_RP_EtPBC_A_CovAsN2`: S4-EtPBC-A, R4-T2 (A3 assembly, AsN2): `A⟦X_σ⟧` is precomplete for the ideal of the variables
* `S4.Def_RP_EtPBC_A_CovAs3f`: S4-EtPBC-A, R4-T2 (A3 assembly, As3f): the completed cover over `Â` from the `CoverLiftAt₂` data
* `S4.Def_RP_EtPBC_A_CovAs4a`: S4-EtPBC-A, R4-T2 (A3 assembly, As4a): a map between two localizations away from `t` is bijective
* `S4.Def_RP_EtPBC_A_CovAs4b`: S4-EtPBC-A, R4-T2 (A3 assembly, As4b): presentations of the two charts and of their overlap
* `S4.Def_RP_EtPBC_A_CovPr7`: S4-EtPBC-A, R4-T2 (A3g): flat descent of vanishing tensors to finitely generated subalgebras
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_P1 =====
section

/-!
# S4-EtCompact, part 11: the projective line `P^1_K = Proj K[X₀, X₁]` (O6, explicit compactifications)

`P1 K := Proj (homogeneousSubmodule (Fin 2) K)` with the standard grading of `MvPolynomial (Fin 2) K`.
The degree-0 part is `K` (`bij0`), the structure map `P1 K ⟶ Spec K` is proper (`P1.toSpecK`), and the
standard chart `D₊(X₀) = Spec (K[X₀, X₁]_(X₀)) ⟶ P1 K` is an open immersion (`P1.chart0`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

universe u

variable (K : Type u) [Field K]

/-- The degree-0 part of `K[X₀, X₁]` is `K`. -/
theorem P1.bij0 : Function.Bijective (algebraMap K (homogeneousSubmodule (Fin 2) K 0)) := by
  constructor
  · intro a b h
    have h' := congrArg Subtype.val h
    exact (algebraMap K (MvPolynomial (Fin 2) K)).injective h'
  · rintro ⟨y, hy⟩
    rw [homogeneousSubmodule_zero, Submodule.mem_one] at hy
    obtain ⟨r, rfl⟩ := hy
    exact ⟨r, rfl⟩

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_Const =====
section

/-!
# S4-EtSheaves, part 3: constant, locally constant and lisse etale sheaves

`constSh Λ X M` is the constant sheaf with value `M` (Mathlib's `constantSheaf`: sheafification of the
constant presheaf), `unitSh Λ X = Λ_X`. Its stalk at every geometric point is `M` (`constStalkIso`), and
`f^*` of a constant sheaf is constant (`pullConstIso`: both are left adjoint to global sections).
`F` is locally constant (`IsLocConst`) if every point of `X` is in the image of an etale `U → X` with
`F|_U` constant; lisse (`IsLisse`, = locally constant constructible) if moreover the values are finite
`Λ`-modules. A lisse sheaf has finite stalks, and conversely a locally constant sheaf with finite stalks
is lisse (`isLisse_iff`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

section PullConst

end PullConst

variable {X : Scheme.{u}}

variable {Λ}

theorem IsLisse.of_iso {F G : EtSh Λ X} (e : F ≅ G) (hF : IsLisse Λ F) : IsLisse Λ G :=
  fun x => by
    obtain ⟨U, v, hv, M, hM, ⟨e'⟩⟩ := hF x
    exact ⟨U, v, hv, M, hM, ⟨(pull U.hom Λ).mapIso e.symm ≪≫ e'⟩⟩

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_PullComp =====
section

/-!
# S4-EtSheaves, part 4: pullback along a composite; pullback preserves (locally) constant sheaves

`pullCompIso g f : (g ≫ f)^* ≅ f^* ⋙ g^*` (from base change along a composite and uniqueness of left
adjoints), `pullCongr` (equal maps give isomorphic pullbacks). Consequently `f^*` preserves locally
constant and lisse sheaves (`IsLocConst.pull`, `IsLisse.pull`): if `F|_U` is constant then
`(f^*F)|_(U ×_Y X)` is constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ]

section Comp

end Comp

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Λ}

/-- **`f^*` preserves lisse sheaves.** -/
theorem IsLisse.pull {F : EtSh Λ Y} (hF : IsLisse Λ F) :
    IsLisse Λ ((EtSheaves.pull f Λ).obj F) := by
  intro x
  obtain ⟨U, v, hv, M, hM, ⟨e⟩⟩ := hF (f x)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback v x hv
  exact ⟨(etPull f).obj U, z, hz, M, hM, ⟨pullLocalIso f U M e⟩⟩

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_Lsh =====
section

/-!
# S4-EtSheaves, part 12: extension by zero `j_!`

For an etale `j : U ⟶ X`, `lsh j Λ = j_!` is the left adjoint of restriction `res j ≅ j^*`
(`Functor.sheafPullback` along `etComp j`, with the universe trick used for `push`).
Stalks: `(j_! G)_(t ≫ j) ≅ G_t` when `j` is a monomorphism (an open immersion), and
`(j_! G)_s = 0` when the centre of `s` is not in the image of `j`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

section Lsh

variable (Λ : Type u) [CommRing Λ]

/-- `j_! ⊣ j^*`. -/
def lshPullAdj : lsh j Λ ⊣ pull j Λ := (lshAdj j Λ).ofNatIsoRight (pullIsoRes j Λ).symm

end Lsh

section Stalks

end Stalks

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_CutSet =====
section

/-!
# S4-EtSheaves, part 21: `F_S` for a subset `S`

For an open `W`: `openCut W F = j_! j^* F` with `openCutι : F_W ⟶ F`. For the closed complement of an open `V`:
`quotCut V F = coker (F_V ⟶ F)` (`= i_* i^* F`, part 19). For any `S`: `cut S F = (F_{closure S})_O` with
`O = interior (coborder S)` (`= coborder S`, open, when `S` is locally closed). For `S` locally closed the stalk of
`cut S F` is `F_s` over `S` (`cutStalkIso`) and zero elsewhere (`isZero_stalk_cut`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Topology

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}}

variable {Λ}

theorem isIso_stalk_quotCutπ (V : X.Opens) (F : EtSh Λ X) (s : GeomPt X) (hs : s.center ∉ V) :
    IsIso ((s.stalkF Λ).map (quotCutπ Λ V F)) := by
  have h0 : (s.stalkF Λ).map (openCutι Λ V F) = 0 := (isZero_stalk_openCut V F s hs).eq_of_src _ _
  have := cokernel.π_of_zero h0
  have : IsIso ((s.stalkF Λ).map (quotCutπ Λ V F) ≫
      (PreservesCokernel.iso (s.stalkF Λ) (openCutι Λ V F)).hom) := by
    rw [PreservesCokernel.π_iso_hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso (s.stalkF Λ) (openCutι Λ V F)).hom

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtSheaves_StalkRes =====
section

/-!
# S4-EtSheaves, part 38: stalks of a restriction, on germs

For an etale `g : U ⟶ X` and a geometric point `t` of `U`, `resFib g t Λ F : (res g F)_t ⟶ F_(t ≫ g)` sends the germ of
`z ∈ F(W → U → X)` at a lift `b : Spec Ω ⟶ W` (over `U`) to the germ of `z` at `b` viewed as a lift over `X`
(`liftX`). It is bijective (`resFib_surjective`: every neighbourhood of `t ≫ g` is refined by one of the form
`W ×_X U`; `resFib_injective`: a neighbourhood over `X` of a lift over `U` is again etale over `U`, `etLift`), so it is
an isomorphism `resFibIso` with an explicit germ formula (`resFib_germ`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

variable {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] (t : GeomPt U)

variable (Λ : Type u) [CommRing Λ]

/-- `resFib` is natural in the sheaf. -/
@[reassoc]
theorem resFib_natural {F G : EtSh Λ X} (φ : F ⟶ G) :
    (t.stalkF Λ).map ((res g Λ).map φ) ≫ resFib g t Λ G = resFib g t Λ F ≫ ((t.map g).stalkF Λ).map φ := by
  refine GrothendieckTopology.Point.presheafFiber_hom_ext _ (fun W b => ?_)
  change t.point.toPresheafFiber W b _ ≫ t.point.presheafFiber.map ((res g Λ).map φ).hom ≫ resFib g t Λ G =
    t.point.toPresheafFiber W b _ ≫ resFib g t Λ F ≫ (t.map g).point.presheafFiber.map φ.hom
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality_assoc, germ_resFib, germ_resFib_assoc,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  rfl

end RamanujanPetersson.EtSheaves

end

end

-- ===== S4.Def_RP_EtCompact_LerayG =====
section

/-!
# S4-EtCompact, part 40: a two-row Leray argument for `g_*` (CC4, formal part)

Generic part (`LerayG`): `adj : L ⊣ R` between abelian categories, `L` preserving monomorphisms, `eAB : L A ≅ B`.
For `N : D` with injective presentation `N ↪ I ↠ Qt N`:
* `R1 R N := coker(R I → R (Qt N))` (`= R¹R N`), short exact `presA : 0 → R N → R I → C → 0` and
  `presB : 0 → C → R (Qt N) → R1 → 0`;
* `lift_push`: lifting `A`-sections along `R φ` from lifting `B`-sections along `φ`.
Under `hη : Ext²(B, -) = 0` and `hR : R1 R (Qt M) = 0` for all `M` (`R²R = 0`):
* **`H_push_Qt_eq_zero`**: `Ext^(m+1)(A, R (Qt M)) = 0`;
* **`H_push_eq_zero_of_R1`**: `Ext^(n+3)(A, R N) = 0` if `Ext^(n+1)(A, R1 R N) = 0`;
* **`H_push_two_eq_zero`**: `Ext²(A, R N) = 0` if every `A`-section of `R1 R N` lifts to `R (Qt N)`.
Specialised to `pull g ⊣ push g`, `A = Λ_X`, `B = Λ_Y` (étale cohomology `H Λ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

namespace LerayG

open Abelian

universe w v₁ v₂ u₁ u₂

end LerayG

open RamanujanPetersson.EtSheaves

universe u

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (Λ : Type u) [CommRing Λ]

variable {g Λ}

/-- **`H^(m+1)(X, g_*(I/M)) = 0`** under `H²(Y, -) = 0` and `R²g_* = 0`. -/
theorem H_push_Qt_eq_zero (hη : ∀ (M : EtSh Λ Y) (e : H Λ M 2), e = 0)
    (hR : ∀ M : EtSh Λ Y, IsZero (R1 g Λ (Qt Λ M))) (m : ℕ) (M : EtSh Λ Y)
    (e : H Λ ((push g Λ).obj (Qt Λ M)) (m + 1)) : e = 0 := by
  have := LerayG.pzm (pullAdj g Λ)
  exact LerayG.H_push_Qt_eq_zero (pullAdj g Λ) (pullConst Λ g (ModuleCat.of Λ Λ)) hη hR m M e

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtSheaves_PullTens =====
section

/-!
# S4-EtSheaves, part 27: pullback is monoidal along every morphism

For any `f : X ⟶ Y` and etale sheaves `F G` on `Y`: `f^*(F ⊗ G) ≅ f^*F ⊗ f^*G` (`pullTensIsoGen`),
and the `Core` form `IsEt.pullTensAny`.

Route: the comparison map `δ : f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G` (`pullTensMap`) is the adjoint transpose of
`γ : F ⊗ G ⟶ f_*(f^*F ⊗ f^*G)` (`tensUnit`: sheafified `η_F ⊗ η_G`). It is an isomorphism on stalks:
the base-change map `ρ_A : (f_*A)_{s ≫ f} ⟶ A_s` (`pushFib`, on germs `A(V ×_Y X)` at `b`) satisfies
`β_F = ψ(η_F) ≫ ρ_{f^*F}` for Mathlib's stalk isomorphism `β = sheafFiberComapIso` (`comapIso_hom_app`),
and `ψ(γ) ≫ ρ` is computed on germs of `z₁ ⊗ z₂` (`fib_tensUnitPre`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory GrothendieckTopology

noncomputable section

namespace RamanujanPetersson.EtSheaves

universe u

section Gen

variable (Λ : Type u) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (s : GeomPt X)

@[reassoc]
theorem germ_unit_pushFib (F : EtSh Λ Y) (V : Y.Etale) (b : (comapPt f s).fiber.obj V) :
    (comapPt f s).toPresheafFiber V b F.obj ≫
        (comapPt f s).sheafFiber.map ((pullAdj f Λ).unit.app F) ≫ pushFib Λ f s ((pull f Λ).obj F) =
      ((pullAdj f Λ).unit.app F).hom.app (op V) ≫
        s.point.toPresheafFiber ((etPull f).obj V) b ((pull f Λ).obj F).obj := by
  change (comapPt f s).toPresheafFiber V b F.obj ≫
      (comapPt f s).presheafFiber.map ((pullAdj f Λ).unit.app F).hom ≫ _ = _
  erw [Point.toPresheafFiber_naturality_assoc, germ_pushFib]

end Gen

namespace IsEt

end IsEt

end RamanujanPetersson.EtSheaves

end

end

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

theorem intValuation_comap (e : B1 ≃+* B2) (w : HeightOneSpectrum B2) (b : B1) :
    (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).intValuation b = w.intValuation (e b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have heb : e b ≠ 0 := fun h => hb (e.injective (h.trans (map_zero e).symm))
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hb,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ heb]
  congr 3
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  have hpow : (HeightOneSpectrum.comap (e : B1 →+* B2) e.surjective w).asIdeal ^ n =
      (w.asIdeal ^ n).comap (e : B1 →+* B2) := by
    change (w.asIdeal.comap e) ^ n = (w.asIdeal ^ n).comap e
    rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff,
    Set.singleton_subset_iff, hpow]
  exact Iff.rfl

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

-- ===== S4.Def_RP_ThetaCube_Cst =====
section

/-!
# S4-ThetaCube, file Cst (D-C1, part 3): constants and values of `phiX f` at `K`-points
* `gff_eq_toStalk`, `gff_surjective` (on `Spec` of a field), `gff_sum`;
* `PsiX_stalkMap_val`, `PsiX_fpull_kff`: `PsiX` of the constant `c` pulled back to `X1` is `algebraMap K F c`;
* `fpull_phiX_val`: `phiX f` is regular at a `K`-point `q` with `0 ≤ ord f`, with value `kff c`, `cval q (phiX f) = c`;
* **`fpull_phiX_incB`**: at `q` with `kPl q = inl (ptP φ)`, `fpull q (phiX (incB r)) = kff (φ r)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Gff

variable {R : Type u} [CommRing R] [IsDomain R]

instance isDomain_ofCR : IsDomain (CommRingCat.of R) := inferInstanceAs (IsDomain R)

end Gff

section Cst

end Cst

end RamanujanPetersson.ThetaCube


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

omit [Etale g] in
theorem map_aut {τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω)} (hτ : τ ≫ t.pt = t.pt) :
    τ ≫ (t.map g).pt = (t.map g).pt :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) hτ)

variable (Λ : Type u) [CommRing Λ]

/-- Germs under `stalkAut`. -/
theorem germ_stalkAut {Y : Scheme.{u}} (s : GeomPt Y) {τ : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)}
    (hτ : τ ≫ s.pt = s.pt) (F : EtSh Λ Y) (W : Y.Etale) (a : s.point.fiber.obj W) :
    s.point.toPresheafFiber W a F.obj ≫ (s.stalkAut Λ τ hτ).app F =
      s.point.toPresheafFiber W ((s.autHom τ hτ).hom.app W a) F.obj :=
  ModuleCat.hom_ext (LinearMap.ext fun z => GeomPt.stalkAut_toPresheafFiber (s := s) (Λ := Λ) τ hτ F W a z)

end Res

section Pt

variable {X : Scheme.{u}}

/-- **Conjugation across an isomorphism of geometric points.** -/
theorem autHom_ptIso {s t : GeomPt X} (e : CategoryTheory.Over.mk s.pt ≅ CategoryTheory.Over.mk t.pt)
    (τ : Spec (CommRingCat.of t.Ω) ⟶ Spec (CommRingCat.of t.Ω)) (hτ : τ ≫ t.pt = t.pt)
    (hτs : (e.hom.left ≫ τ ≫ e.inv.left) ≫ s.pt = s.pt) :
    s.autHom (e.hom.left ≫ τ ≫ e.inv.left) hτs ≫ (GPtIso.ptIso e).hom = (GPtIso.ptIso e).hom ≫ t.autHom τ hτ := by
  have h : (Over.homMk (e.hom.left ≫ τ ≫ e.inv.left) hτs :
      CategoryTheory.Over.mk s.pt ⟶ CategoryTheory.Over.mk s.pt) ≫ e.hom =
        e.hom ≫ (Over.homMk τ hτ : CategoryTheory.Over.mk t.pt ⟶ CategoryTheory.Over.mk t.pt) := by
    apply CategoryTheory.Over.OverMorphism.ext
    change (e.hom.left ≫ τ ≫ e.inv.left) ≫ e.hom.left = e.hom.left ≫ τ
    rw [Category.assoc, Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left]
    exact congrArg (e.hom.left ≫ ·) (Category.comp_id τ)
  apply GrothendieckTopology.Point.hom_ext
  ext U a
  have h' : ∀ a' : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget X).obj U,
      (Over.homMk (e.hom.left ≫ τ ≫ e.inv.left) hτs :
        CategoryTheory.Over.mk s.pt ⟶ CategoryTheory.Over.mk s.pt) ≫ e.hom ≫ a' =
      e.hom ≫ (Over.homMk τ hτ : CategoryTheory.Over.mk t.pt ⟶ CategoryTheory.Over.mk t.pt) ≫ a' := fun a' => by
    rw [← Category.assoc, h, Category.assoc]
  exact h' a

end Pt

section Open

variable {U X : Scheme.{u}} (g : U ⟶ X) [IsOpenImmersion g] (y : U)

variable (Λ : Type u) [CommRing Λ]

theorem stalkAut_congr {Y : Scheme.{u}} (s : GeomPt Y)
    {τ τ' : Spec (CommRingCat.of s.Ω) ⟶ Spec (CommRingCat.of s.Ω)}
    (hτ : τ ≫ s.pt = s.pt) (hτ' : τ' ≫ s.pt = s.pt) (h : τ = τ') : s.stalkAut Λ τ hτ = s.stalkAut Λ τ' hτ' := by
  subst h
  rfl

end Open

end RamanujanPetersson.EtCompact.GalTr

end

end

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

variable {V X U : Scheme.{u}} (c : V ⟶ X) [Etale c] (j : U ⟶ X)

instance etale_snd : Etale (pullback.snd c j) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) (IsPullback.of_hasPullback c j) ‹Etale c›

end Gen

section Chart

end Chart

section P1

variable (k : Type) [Field k]

/-- A chart `A¹ ⟶ P¹` whose image contains `s`. -/
def p1Chart (s : P1 k) : A1 k ⟶ P1 k := by
  classical exact if s ∈ (chartA1 k).opensRange then chartA1 k else chartA1' k

end P1

end RamanujanPetersson.EtCompact.PushBC

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

/-- The germ at `t` of a global section `z` of `F`. -/
def gg (t : GeomPt Y) (F : EtSh Λ Y) (z : F.obj.obj (op (etId Y))) : (t.stalkF Λ).obj F :=
  (t.point.toPresheafFiber (etId Y) t.top F.obj).hom z

end Gen

section Res

end Res

section Tr

end Tr

end RamanujanPetersson.EtCompact.GGerm

end

end

-- ===== S4.Def_RP_EtCompact_PushStk =====
section

/-!
# S4-EtCompact, (c) T3: stalks of `j_*` at points of `U`, and boundary points of `P¹`

* **`pushStkIso j u F : (j_* F)_{j u} ≅ F_u`** for an open immersion `j` (`resTrIso⁻¹` and the counit iso),
  `pushStkIso_hom`, **`pushStkIso_natural`**;
* `isClosed_of_not_mem_range`: for a nonempty open `j : Spec A ⟶ P¹`, every point off the image is closed.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

universe u

namespace RamanujanPetersson.EtCompact.PushStk

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.GalTr

section Gen

end Gen

section P1

variable {k : Type} [Field k] {A : Type} [CommRing A] [IsDomain A]

/-- Points of `P¹` off a nonempty open `Spec A` are closed. -/
theorem isClosed_of_not_mem_range (j : Spec (CommRingCat.of A) ⟶ P1 k) [IsOpenImmersion j] (s : P1 k)
    (hs : s ∉ Set.range j) : IsClosed ({s} : Set (P1 k)) := by
  refine CurveHn.P1.isClosed_of_ne_genPt k s ?_
  rintro rfl
  apply hs
  exact ((P1.isGenericPoint_genPt k).mem_open_set_iff j.isOpenEmbedding.isOpen_range).2
    ⟨j (GenBr.genPt A), trivial, GenBr.genPt A, rfl⟩

end P1

end RamanujanPetersson.EtCompact.PushStk

end

end

-- ===== S4.Def_RP_EtCompact_ParSuf =====
section

/-!
# S4-EtCompact, (c) T5a: `j_*` keeps an extension of `Λ_U` short exact when it is unramified at the boundary

* `map_shortExact_of_epi` (generic): a right adjoint keeps a short exact sequence short exact once the last map
  stays epi;
* `epi_push_stalk_range`: over `j u`, `j_* φ` is epi on stalks when `φ` is epi at `u` (`pushStkIso_natural`);
* `epi_push_stalk_bdry`: at a boundary point `s`, `(j_* g)_s̄` is epi once an `I_s`-fixed vector maps to `1`
  (`stalkEquivInert'`, `spHom'_natural`, every element of `(Λ_U)_η̄` is a multiple of `1`);
* **`epi_push`**: `j_* g` is epi when `g` is epi and every boundary point has an inertia-fixed lift of `1`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

universe u

namespace RamanujanPetersson.EtCompact.ParSuf

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

section Adj

/-- A right adjoint keeps a short exact sequence short exact once it keeps the last map epi. -/
theorem map_shortExact_of_epi {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) [R.PreservesZeroMorphisms] {S : ShortComplex D} (hS : S.ShortExact)
    (hg : Epi (R.map S.g)) : (S.map R).ShortExact := by
  have : PreservesLimitsOfSize.{0, 0} R := adj.rightAdjoint_preservesLimits
  have := hS.mono_f
  exact ShortComplex.ShortExact.mk' (hS.exact.map_of_mono_of_preservesKernel R hS.mono_f inferInstance)
    (R.map_mono S.f) hg

end Adj

section Range

end Range

section Bdry

end Bdry

end RamanujanPetersson.EtCompact.ParSuf

end

end

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

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}}

/-- The identity `Y → Y` is terminal among étale `Y`-schemes. -/
def etId_isTerminal (Y : Scheme.{u}) : IsTerminal (etId Y) :=
  IsTerminal.ofUniqueHom
    (fun V => MorphismProperty.Over.homMk V.hom (Category.comp_id _))
    (fun V m => MorphismProperty.Over.Hom.ext ((Category.comp_id m.left).symm.trans (MorphismProperty.Over.w m)))

/-- `c(1)` over the terminal object is the adjunct of `c`. -/
theorem sc_homEquiv {F : EtSh Λ Y} (c : unitSh Λ Y ⟶ F) :
    sc c (etId Y) =
      (((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u} Λ) (etId_isTerminal Y)).homEquiv _ _ c).hom 1 :) :=
  rfl

/-- The map `Λ_Y ⟶ F` attached to a global section `q`. -/
def ofSec {F : EtSh Λ Y} (q : F.obj.obj (op (etId Y))) : unitSh Λ Y ⟶ F :=
  ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u} Λ) (etId_isTerminal Y)).homEquiv _ _).symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _ q))

theorem sc_ofSec {F : EtSh Λ Y} (q : F.obj.obj (op (etId Y))) : sc (ofSec q) (etId Y) = q := by
  rw [sc_homEquiv, ofSec, Equiv.apply_symm_apply]
  exact one_smul Λ q

end RamanujanPetersson.EtCompact.PtSec

namespace RamanujanPetersson.EtCompact.CurveHn

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact

end RamanujanPetersson.EtCompact.CurveHn

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

/-- The presheaf `V ↦ Λ[Hom(V, W)]`. -/
abbrev freePre (W : X.Etale) : (X.Etale)ᵒᵖ ⥤ ModuleCat.{u} Λ :=
  yoneda.obj W ⋙ ModuleCat.free Λ

end RamanujanPetersson.EtPBC

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

variable (Λ : Type u) [CommRing Λ] (X : Scheme.{u})

/-- The functor `W ↦ Λ[W]`. -/
def freeFun : X.Etale ⥤ EtSh Λ X :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free Λ) ⋙
    presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)

end Free

section OfSec

variable {Λ : Type u} [CommRing Λ] {Y : Scheme.{u}}

theorem ofSec_comp {F G : EtSh Λ Y} (q : F.obj.obj (op (etId Y))) (φ : F ⟶ G) :
    ofSec q ≫ φ = ofSec ((φ.hom.app (op (etId Y))).hom q) := by
  rw [ofSec, ofSec, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  ext
  simp

end OfSec

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- The geometric fibre `P_s = P ×_S Spec Ω`. -/
abbrev fib : Scheme.{u} := pullback g s.pt

/-- The etale neighbourhoods `(V, v)` of `s`. -/
abbrev Nbhd := s.point.fiber.Elements

section EtPull

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

@[reassoc]
theorem etPull_map_left_fst {V' V : Y.Etale} (m : V' ⟶ V) :
    ((etPull f).map m).left ≫ pullback.fst V.hom f = pullback.fst V'.hom f ≫ m.left :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem etPull_map_left_snd {V' V : Y.Etale} (m : V' ⟶ V) :
    ((etPull f).map m).left ≫ pullback.snd V.hom f = pullback.snd V'.hom f :=
  pullback.lift_snd _ _ _

end EtPull

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

/-- Lifting a fibre point of any geometric point along an etale arrow through a given point. -/
theorem exists_lift_fib' (t : GeomPt Y) {V T : Y.Etale} (f : V ⟶ T) (a : t.point.fiber.obj T) (v : V.left)
    (hv : f.left v = (t.liftOf a).left (default : Spec (CommRingCat.of t.Ω))) :
    ∃ b : t.point.fiber.obj V, t.point.fiber.map f b = a ∧ (t.liftOf b).left (default : Spec (CommRingCat.of t.Ω)) = v := by
  obtain ⟨l, hl, hl'⟩ := Scheme.exists_fac_of_etale_of_isSepClosed (Ω := t.Ω) f.left (t.liftOf a).left v hv
  have hw : l ≫ V.hom = t.pt := by
    rw [← MorphismProperty.Over.w f, ← Category.assoc, hl]
    exact Over.w (t.liftOf a)
  let b : t.point.fiber.obj V :=
    (Over.homMk l hw : CategoryTheory.Over.mk t.pt ⟶ (Scheme.Etale.forget Y).obj V)
  exact ⟨b, fiber_ext _ hl, hl'⟩

/-- Local constant representations of a section of a constant sheaf. -/
theorem exists_locRep {T : Y.Etale} (c : (constSh Λ Y M).obj.obj (op T)) (w : T.left) :
    ∃ n : M, ∃ (V : Y.Etale) (f : V ⟶ T) (v : V.left), f.left v = w ∧
      ((constSh Λ Y M).obj.map f.op).hom c = (constUnit M V).hom n := by
  obtain ⟨V, f, v, ⟨n, hn⟩, hv⟩ := (mem_smallEtale_iff T _).1
    (Presheaf.imageSieve_mem Y.smallEtaleTopology (toSheafify Y.smallEtaleTopology (constPre M)) c) w
  exact ⟨n, V, f, v, hv, hn.symm⟩

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_NilLift =====
section

/-!
# S4-EtPBC-A, R4-F1a/b: etale algebras lift uniquely along nilpotent thickenings

`φ : R →+* R₀` surjective with nilpotent kernel `J`.

* `isUnit_of_map`: units lift along a surjection with nilpotent kernel.
* **`exists_etale_lift`**: every etale `R₀`-algebra `B₀` is `B ⧸ J B` for an etale `R`-algebra `B`
  (`f : B →+* B₀` surjective, `ker f = J B`, compatible with `φ`), and `B` is finite over `R` when `B₀` is finite
  over `R₀`. Proof: a global submersive presentation of relative dimension `0` of `B₀`
  (`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`), lift its relations, the Jacobian stays a unit.
* **`exists_hom_lift`**, `hom_lift_unique`: ring maps from an etale `R`-algebra lift uniquely along a surjection
  with nilpotent kernel (compatible with `R`).
* **`exists_iso_lift`**: two etale lifts of the same `B₀` are isomorphic over `B₀`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.NilLift

universe u

open MvPolynomial

/-- Units lift along a surjection with nilpotent kernel. -/
theorem isUnit_of_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) (hf : Function.Surjective f)
    (hk : IsNilpotent (RingHom.ker f)) {x : S} (hx : IsUnit (f x)) : IsUnit x := by
  refine (IsNilpotent.isUnit_quotient_mk_iff hk).mp ?_
  have h : Ideal.Quotient.mk (RingHom.ker f) x = (RingHom.quotientKerEquivOfSurjective hf).symm (f x) := by
    apply (RingHom.quotientKerEquivOfSurjective hf).injective
    simp
  rw [h]
  exact hx.map _

/-- The image of a nilpotent ideal is nilpotent. -/
theorem isNilpotent_map {S T : Type*} [CommRing S] [CommRing T] (g : S →+* T) {J : Ideal S}
    (hJ : IsNilpotent J) : IsNilpotent (J.map g) := by
  obtain ⟨n, hn⟩ := hJ
  exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, ← Ideal.zero_eq_bot]⟩

variable {R R₀ : Type u} [CommRing R] [CommRing R₀]

/-- **Maps from an etale algebra lift along nilpotent thickenings.** -/
theorem exists_hom_lift (B : Type u) [CommRing B] [Algebra R B] [Algebra.FormallySmooth R B]
    {C C₀ : Type u} [CommRing C] [CommRing C₀] [Algebra R C] (g : C →+* C₀) (hg : Function.Surjective g)
    (hgk : IsNilpotent (RingHom.ker g)) (h₀ : B →+* C₀)
    (hc : h₀.comp (algebraMap R B) = g.comp (algebraMap R C)) :
    ∃ h : B →ₐ[R] C, g.comp h.toRingHom = h₀ := by
  letI : Algebra R C₀ := (g.comp (algebraMap R C)).toAlgebra
  let gA : C →ₐ[R] C₀ := { g with commutes' := fun _ => rfl }
  let hA : B →ₐ[R] C₀ := { h₀ with commutes' := fun r => congrArg (fun k : R →+* C₀ => k r) hc }
  refine ⟨Algebra.FormallySmooth.liftOfSurjective hA gA hg hgk, ?_⟩
  ext b
  exact Algebra.FormallySmooth.liftOfSurjective_apply hA gA hg hgk b

/-- Lifts of maps from a formally unramified algebra along nilpotent thickenings are unique. -/
theorem hom_lift_unique (B : Type u) [CommRing B] [Algebra R B] [Algebra.FormallyUnramified R B]
    {C C₀ : Type u} [CommRing C] [CommRing C₀] [Algebra R C] (g : C →+* C₀)
    (hgk : IsNilpotent (RingHom.ker g)) (h₁ h₂ : B →ₐ[R] C)
    (he : g.comp h₁.toRingHom = g.comp h₂.toRingHom) : h₁ = h₂ :=
  Algebra.FormallyUnramified.ext' g hgk h₁ h₂ (fun x => congrArg (fun k : B →+* C₀ => k x) he)

end RamanujanPetersson.EtPBC.NilLift

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

variable {R S : Type u} [CommRing R] [CommRing S]

/-- An away map at an element with unit image is a localization. -/
theorem isLocalization_of_isAwayMap (ψ : R →+* S) (t : R) (h : IsAwayMap ψ t) (hu : IsUnit (ψ t)) :
    @IsLocalization.Away R _ t S _ ψ.toAlgebra := by
  letI := ψ.toAlgebra
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, fun y => ?_, fun {x y} hxy => ?_⟩
  · rintro ⟨_, k, rfl⟩
    change IsUnit (ψ (t ^ k))
    rw [map_pow]
    exact hu.pow k
  · obtain ⟨k, a, hk⟩ := h.1 y
    refine ⟨⟨a, ⟨t ^ k, k, rfl⟩⟩, ?_⟩
    change y * ψ (t ^ k) = ψ a
    rw [map_pow, mul_comm]
    exact hk
  · obtain ⟨k, hk⟩ := h.2 (x - y) (by rw [map_sub, sub_eq_zero]; exact hxy)
    refine ⟨⟨t ^ k, k, rfl⟩, ?_⟩
    change t ^ k * x = t ^ k * y
    rw [← sub_eq_zero, ← mul_sub]
    exact hk

/-- A localization map is an away map. -/
theorem isAwayMap_of_isLocalization [Algebra R S] (t : R) [IsLocalization.Away t S] :
    IsAwayMap (algebraMap R S) t := by
  refine ⟨fun y => ?_, fun a ha => ?_⟩
  · obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers t) y
    obtain ⟨k, hk⟩ := s.2
    have hk' : t ^ k = ↑s := hk
    refine ⟨k, a, ?_⟩
    have hs' : y * algebraMap R S (t ^ k) = algebraMap R S a := by rw [hk']; exact hs
    rw [← map_pow, mul_comm]
    exact hs'
  · obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers t) S a).mp ha
    exact ⟨k, hk⟩

/-- Away maps compose with ring isomorphisms. -/
theorem isAwayMap_comp_equiv {S' : Type u} [CommRing S'] (ψ : R →+* S) (t : R) (h : IsAwayMap ψ t)
    (e : S ≃+* S') : IsAwayMap (e.toRingHom.comp ψ) t := by
  refine ⟨fun y => ?_, fun a ha => ?_⟩
  · obtain ⟨k, a, hk⟩ := h.1 (e.symm y)
    refine ⟨k, a, ?_⟩
    have := congrArg e hk
    rw [map_mul, map_pow, RingEquiv.apply_symm_apply] at this
    exact this
  · refine h.2 a ?_
    have ha' : e (ψ a) = 0 := ha
    rw [← map_zero e] at ha'
    exact e.injective ha'

end Away

section Red

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B₀ : Type u} (N : Type u) {E₀ e₀ e : Type u} [CommRing B₀] [CommRing N] [CommRing E₀] [CommRing e₀] [CommRing e]
  [Algebra B₀ N] [Algebra B₀ E₀] (t₀ : B₀) [IsLocalization.Away t₀ N]
  (f₀ : E₀ →+* e₀) (g : e₀ →+* e) (τ : e₀) (hτ : f₀ (algebraMap B₀ E₀ t₀) = τ) (hu : IsUnit (g τ))

instance isLoc_tens : IsLocalization.Away (algebraMap B₀ E₀ t₀) (N ⊗[B₀] E₀) := inferInstance

include hτ hu in
theorem red_units : ∀ y : Submonoid.powers (algebraMap B₀ E₀ t₀), IsUnit ((g.comp f₀) y) := by
  rintro ⟨_, k, rfl⟩
  change IsUnit (g (f₀ (algebraMap B₀ E₀ t₀ ^ k)))
  rw [map_pow, map_pow, hτ]
  exact hu.pow k

end Red

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAR =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1b): uniform relations of `p` on the base charts (Artin-Rees)

For `α : Fin g → R` and `ιB : R → B`:
* **`RelV p α ιB n`**: vectors `w` with entries in `p^n B` and `∑ αᵢ wᵢ = 0`; `muB`, `mem_smul_top_pi`, `mem_relV_iff`;
* **`relV_transport`**: a chart-0 relation is `t₀^f` times a chart-1 relation on the overlap `N`;
* **`relV_uniform`** (Artin-Rees, `B₀` noetherian): one bound `F` such that for every `n` the relations `RelV n` are
  `p^(n-n')`-combinations of finitely many relations in `RelV n'` (`n' ≤ n`) whose transition exponents are `≤ F`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section RelV

variable {R : Type u} [CommRing R] (p : Ideal R) {g : ℕ} (α : Fin g → R)

/-- Relation vectors of `α` with entries in `p^n B`. -/
def RelV {B : Type u} [CommRing B] (ιB : R →+* B) (n : ℕ) : Set (Fin g → B) :=
  {w | (∀ i, w i ∈ (p ^ n).map ιB) ∧ ∑ i, ιB (α i) * w i = 0}

/-- The map `w ↦ ∑ αᵢ wᵢ`. -/
def muB {B : Type u} [CommRing B] (ιB : R →+* B) : (Fin g → B) →ₗ[B] B where
  toFun w := ∑ i, ιB (α i) * w i
  map_add' w w' := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem mem_smul_top_pi {B : Type u} [CommRing B] (𝔟 : Ideal B) (w : Fin g → B) :
    w ∈ 𝔟 • (⊤ : Submodule B (Fin g → B)) ↔ ∀ i, w i ∈ 𝔟 := by
  constructor
  · intro hw
    refine Submodule.smul_induction_on hw (fun r hr m _ i => ?_) (fun x y hx hy i => ?_)
    · rw [Pi.smul_apply, smul_eq_mul]
      exact 𝔟.mul_mem_right _ hr
    · rw [Pi.add_apply]
      exact 𝔟.add_mem (hx i) (hy i)
  · intro hw
    classical
    rw [pi_eq_sum_univ w]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hw i) Submodule.mem_top

end RelV

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As1): base change of the chart data along a flat algebra

* `tmap_id_left`: `map id φ` on `S ⊗[A] B` is `φ.lTensor S`.
* **`away_bc`**: for `S` flat over `A`, `IsAwayMap φ t` gives `IsAwayMap (map id φ) (1 ⊗ t)`.
* `tmul_one_mul_one`: `x * y = 1` gives `(1 ⊗ x) * (1 ⊗ y) = 1`.
* `hat_complete`, `hat_jac`: the completion `Â` is `p Â`-adically complete and `p Â ≤ jacobson ⊥` (`p` f.g.).
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section BC

variable {A S B N : Type u} [CommRing A] [CommRing S] [Algebra A S] [CommRing B] [Algebra A B] [CommRing N]
  [Algebra A N]

theorem tmap_id_left (φ : B →ₐ[A] N) (x : S ⊗[A] B) :
    Algebra.TensorProduct.map (AlgHom.id A S) φ x = φ.toLinearMap.lTensor S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s b =>
    simp only [Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul, AlgHom.id_apply,
      AlgHom.toLinearMap_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem tmul_one_mul_one {x y : B} (h : x * y = 1) : ((1 : S) ⊗ₜ[A] x) * ((1 : S) ⊗ₜ[A] y) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, h, ← Algebra.TensorProduct.one_def]

/-- The torsion part of `away_bc`: elements of `S ⊗ ker φ` are killed by a power of `1 ⊗ t`. -/
theorem away_bc_ker (φ : B →ₐ[A] N) (t : B) (h : IsAwayMap (φ : B →+* N) t)
    (w : S ⊗[A] (LinearMap.ker φ.toLinearMap)) :
    ∃ k : ℕ, ((1 : S) ⊗ₜ[A] t) ^ k * (LinearMap.ker φ.toLinearMap).subtype.lTensor S w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp only [map_zero, mul_zero]⟩
  | tmul s m =>
    have h0 : (φ : B →+* N) (m : B) = 0 := by
      have h1 : φ.toLinearMap (m : B) = 0 := LinearMap.mem_ker.mp m.2
      rw [AlgHom.toLinearMap_apply] at h1
      simpa only [RingHom.coe_coe] using h1
    obtain ⟨k, hk⟩ := h.2 (m : B) h0
    refine ⟨k, ?_⟩
    simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, hk, TensorProduct.tmul_zero]
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨k₁, e₁⟩ := h₁
    obtain ⟨k₂, e₂⟩ := h₂
    refine ⟨k₁ + k₂, ?_⟩
    rw [map_add]
    linear_combination ((1 : S) ⊗ₜ[A] t) ^ k₂ * e₁ + ((1 : S) ⊗ₜ[A] t) ^ k₁ * e₂

end BC

section Hat

variable (A : Type u) [CommRing A] (p : Ideal A)

theorem hat_complete (hp : p.FG) :
    IsAdicComplete (p.map (algebraMap A (AdicCompletion p A))) (AdicCompletion p A) :=
  AdicCompletion.isAdicComplete_self _ hp

end Hat

end RamanujanPetersson.EtPBC.Cov

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

theorem eval_map_bc (c : A[X]) :
    eval₂RingHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] B)
      ((1 : S) ⊗ₜ[A] algebraMap A[X] B X) (c.map (algebraMap A S)) = (1 : S) ⊗ₜ[A] algebraMap A[X] B c := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, hp, hq, map_add, TensorProduct.tmul_add]
  | monomial n a =>
    have e1 : algebraMap A[X] B (Polynomial.monomial n a) = algebraMap A B a * (algebraMap A[X] B X) ^ n := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
    rw [e1, Polynomial.map_monomial, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Algebra.algebraMap_eq_smul_one (A := S) a,
      Algebra.algebraMap_eq_smul_one (A := B) a, smul_mul_assoc, one_mul, TensorProduct.smul_tmul]

/-- Finiteness from generators `1 ⊗ bⱼ`, for any `f : S[X] →+* S ⊗[A] B` with the two evaluation rules. -/
theorem fin_bc_aux [Module.Finite A[X] B] (f : S[X] →+* S ⊗[A] B)
    (hf : ∀ c : A[X], f (c.map (algebraMap A S)) = (1 : S) ⊗ₜ[A] algebraMap A[X] B c)
    (hC : ∀ s₀ : S, f (Polynomial.C s₀) = s₀ ⊗ₜ[A] (1 : B)) : f.Finite := by
  classical
  letI := f.toAlgebra
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A[X]) (M := B)
  have hspan : Submodule.span S[X] (↑(s.image fun b => (1 : S) ⊗ₜ[A] b) : Set (S ⊗[A] B)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul s₀ b =>
      have hb : b ∈ Submodule.span A[X] (s : Set B) := by
        rw [hs]
        exact Submodule.mem_top
      induction hb using Submodule.span_induction with
      | mem b hb' =>
        have e : s₀ ⊗ₜ[A] b = (Polynomial.C s₀) • ((1 : S) ⊗ₜ[A] b) := by
          rw [Algebra.smul_def (Polynomial.C s₀) ((1 : S) ⊗ₜ[A] b), RingHom.algebraMap_toAlgebra, hC,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [e]
        exact Submodule.smul_mem _ _
          (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hb'))))
      | zero =>
        rw [TensorProduct.tmul_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        rw [TensorProduct.tmul_add]
        exact add_mem hx hy
      | smul c x _ hx =>
        have e : s₀ ⊗ₜ[A] (c • x) = (c.map (algebraMap A S)) • (s₀ ⊗ₜ[A] x) := by
          rw [Algebra.smul_def c x]
          rw [Algebra.smul_def (c.map (algebraMap A S)) (s₀ ⊗ₜ[A] x)]
          rw [RingHom.algebraMap_toAlgebra, hf, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [e]
        exact Submodule.smul_mem _ _ hx
    | add x y hx hy => exact add_mem hx hy
  have hfin : Module.Finite S[X] (S ⊗[A] B) := ⟨⟨s.image fun b => (1 : S) ⊗ₜ[A] b, hspan⟩⟩
  exact hfin

end BCFin

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovL3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A1c): the tower of nilpotent lifts of a two-chart etale cover

* **`TwoCov φb₀ φb₁ τ₀ τ₁`**: a two-chart finite etale cover (bundled rings, `RingHom.Etale`/`Finite` properties);
  **`TwoCovHom π₀ π₁ π C' C`**: a transition `C' → C` over reductions `πᵢ`, `π` (surjective, kernels, squares);
* **`exists_lift`**: `lift_step` in this language;
* levels `B ⧸ J^(k+1)`: `down` (square-zero kernel), `qmap` (with `isAwayMap_qmap`, `isUnit_qmap`, `qmap_down`);
* **`tower`**, **`towerHom`**: the lifts of a level-0 cover to all levels `k`, with transitions.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Cov

variable {b₀ b₁ n : Type u} [CommRing b₀] [CommRing b₁] [CommRing n]

/-- **A two-chart finite etale cover** over charts `b₀`, `b₁` glued along `n` (localizations at `τ₀`, `τ₁`). -/
structure TwoCov (φb₀ : b₀ →+* n) (φb₁ : b₁ →+* n) (τ₀ : b₀) (τ₁ : b₁) where
  E₀ : CommRingCat.{u}
  E₁ : CommRingCat.{u}
  E : CommRingCat.{u}
  a₀ : b₀ →+* E₀
  a₁ : b₁ →+* E₁
  a : n →+* E
  et₀ : a₀.Etale
  et₁ : a₁.Etale
  fin₀ : a₀.Finite
  fin₁ : a₁.Finite
  ψ₀ : E₀ →+* E
  ψ₁ : E₁ →+* E
  hψ₀ : ψ₀.comp a₀ = a.comp φb₀
  hψ₁ : ψ₁.comp a₁ = a.comp φb₁
  aw₀ : IsAwayMap ψ₀ (a₀ τ₀)
  aw₁ : IsAwayMap ψ₁ (a₁ τ₁)

end Cov

section Hom

end Hom

section Lift

end Lift

section Lvl

variable {B : Type u} [CommRing B] (J : Ideal B)

/-- The transition `B ⧸ J^(k+2) → B ⧸ J^(k+1)`. -/
abbrev down (k : ℕ) : B ⧸ J ^ (k + 2) →+* B ⧸ J ^ (k + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega))

theorem down_surj (k : ℕ) : Function.Surjective (down J k) :=
  Ideal.Quotient.factor_surjective _

/-- The kernel of `down` is square-zero. -/
theorem isNilpotent_ker_down (k : ℕ) : IsNilpotent (RingHom.ker (down J k)) := by
  refine ⟨2, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul, Ideal.zero_eq_bot, eq_bot_iff]
  calc Ideal.map (Ideal.Quotient.mk (J ^ (k + 2))) (J ^ ((k + 1) * 2))
      ≤ Ideal.map (Ideal.Quotient.mk (J ^ (k + 2))) (J ^ (k + 2)) :=
        Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
    _ = ⊥ := Ideal.map_quotient_self _

variable {N : Type u} [CommRing N] (φ : B →+* N) (JN : Ideal N)

theorem pow_le_comap (h : J.map φ = JN) (k : ℕ) : J ^ (k + 1) ≤ (JN ^ (k + 1)).comap φ :=
  Ideal.map_le_iff_le_comap.1 (by rw [Ideal.map_pow, h])

/-- The chart map at level `k`. -/
abbrev qmap (h : J.map φ = JN) (k : ℕ) : B ⧸ J ^ (k + 1) →+* N ⧸ JN ^ (k + 1) :=
  Ideal.quotientMap (JN ^ (k + 1)) φ (pow_le_comap J φ JN h k)

theorem qmap_down (h : J.map φ = JN) (k : ℕ) :
    (qmap J φ JN h k).comp (down J k) = (down JN k).comp (qmap J φ JN h (k + 1)) := by
  apply Ideal.Quotient.ringHom_ext
  exact RingHom.ext fun _ => rfl

theorem isUnit_qmap (h : J.map φ = JN) (t : B) (hu : IsUnit (φ t)) (k : ℕ) :
    IsUnit (qmap J φ JN h k (Ideal.Quotient.mk _ t)) := by
  rw [Ideal.quotientMap_mk]
  exact hu.map _

end Lvl

section Tower

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] (φ₀ : B₀ →+* N) (φ₁ : B₁ →+* N)
  (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN) (t₀ : B₀) (t₁ : B₁)

/-- The level-`k` two-chart covers. -/
abbrev LCov (k : ℕ) : Type (u + 1) :=
  TwoCov (qmap J₀ φ₀ JN h₀ k) (qmap J₁ φ₁ JN h₁ k) (Ideal.Quotient.mk (J₀ ^ (k + 1)) t₀)
    (Ideal.Quotient.mk (J₁ ^ (k + 1)) t₁)

end Tower

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

variable {P : Type u} [CommRing P] {r : ℕ} {Q : Type u} [CommRing Q]

theorem pres_eval_self {g : Fin r → MvPolynomial (Fin r) P} (θ : Pres g →+* Q) (x : MvPolynomial (Fin r) P) :
    MvPolynomial.eval₂ (θ.comp (algebraMap P (Pres g))) (fun j => θ (Ideal.Quotient.mk _ (MvPolynomial.X j))) x =
      θ (Ideal.Quotient.mk _ x) := by
  have h : MvPolynomial.eval₂Hom (θ.comp (algebraMap P (Pres g)))
      (fun j => θ (Ideal.Quotient.mk _ (MvPolynomial.X j))) = θ.comp (Ideal.Quotient.mk _) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      first
        | exact MvPolynomial.eval₂_C _ _ a
        | (simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]; rfl)
    · intro j
      first
        | exact MvPolynomial.eval₂_X _ _ j
        | simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.comp_apply]
  exact RingHom.congr_fun h x

end Gen

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovPr12 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3l): the kernel of reduction mod `J` on a presentation, and `resid_ker` with that target

* `presMap_mk_ker_le`: `ker (presMap (mk J) g) ≤ J · Pres g`.
* **`resid_ker_pm`**: `resid_ker` with `T := Pres (gmap (mk J) g')`, `q := presMap (mk J) g'` (s68 probe: the
  quotient `Pres g' ⧸ J · Pres` as `T` times out at `whnf`; this target elaborates in 26 s).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Gen

variable {P : Type u} [CommRing P] {r : ℕ}

theorem presMap_mk_ker_le (J : Ideal P) (g : Fin r → MvPolynomial (Fin r) P) :
    RingHom.ker (presMap (Ideal.Quotient.mk J) g) ≤ J.map (algebraMap P (Pres g)) := by
  intro y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, presMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
  have hspan : Ideal.span (Set.range (gmap (Ideal.Quotient.mk J) g)) =
      (Ideal.span (Set.range g)).map (MvPolynomial.map (Ideal.Quotient.mk J)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan, Ideal.mem_map_iff_of_surjective _
    (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)] at hy
  obtain ⟨z, hz, hzx⟩ := hy
  have hxz : x - z ∈ J.map (MvPolynomial.C : P →+* MvPolynomial (Fin r) P) := by
    rw [← Ideal.mk_ker (I := J), ← MvPolynomial.ker_map, RingHom.mem_ker, map_sub, hzx, sub_self]
  have h1 : Ideal.Quotient.mk (Ideal.span (Set.range g)) x = Ideal.Quotient.mk _ (x - z) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hz, sub_zero]
  rw [h1]
  have h2 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span (Set.range g))) hxz
  rw [Ideal.map_map] at h2
  first
  | (rw [Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]; exact h2)
  | exact h2
  | (convert h2 using 2)

end Gen

end RamanujanPetersson.EtPBC.Cov

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

/-- `(ker χ') · (R' ⊗[A] B)`. -/
abbrev Jt {K A R' : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] (B : Type u) [CommRing B]
    [Algebra A B] (χ' : R' →+* K) : Ideal (R' ⊗[A] B) :=
  (RingHom.ker χ').map (Algebra.TensorProduct.includeLeftRingHom : R' →+* R' ⊗[A] B)

section Tens

variable {K A R' B : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]

theorem tmul_mem_Jt (χ' : R' →+* K) (x : R') (hx : χ' x = 0) (b : B) : x ⊗ₜ[A] b ∈ Jt B χ' := by
  have h : x ⊗ₜ[A] b = (Algebra.TensorProduct.includeLeftRingHom x) * ((1 : R') ⊗ₜ[A] b) := by
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [h]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (RingHom.mem_ker.mpr hx))

variable {Q : Type u} [CommRing Q] (χ : A →+* K) (ν : K →+* Q) (βQ : B →+* Q)
  (hβ : ∀ a, βQ (algebraMap A B a) = ν (χ a))

/-- The residue `r ⊗ b ↦ ν (χ' r) * βQ b` on `R' ⊗[A] B`. -/
def kap (χ' : R' →+* K) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a) : R' ⊗[A] B →+* Q :=
  letI : Algebra A Q := (ν.comp χ).toAlgebra
  (Algebra.TensorProduct.productMap
    ({ toRingHom := ν.comp χ', commutes' := fun a => congrArg ν (hχ' a) } : R' →ₐ[A] Q)
    ({ toRingHom := βQ, commutes' := fun a => hβ a } : B →ₐ[A] Q)).toRingHom

theorem kap_tmul (χ' : R' →+* K) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a) (r : R') (b : B) :
    kap χ ν βQ hβ χ' hχ' (r ⊗ₜ b) = ν (χ' r) * βQ b :=
  rfl

theorem Jt_le_ker_kap (χ' : R' →+* K) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a) :
    ∀ a ∈ Jt B χ', kap χ ν βQ hβ χ' hχ' a = 0 := by
  have h : Jt B χ' ≤ RingHom.ker (kap χ ν βQ hβ χ' hχ') := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, Algebra.TensorProduct.includeLeftRingHom_apply, kap_tmul,
      RingHom.mem_ker.mp hx, map_zero, zero_mul]
  exact fun a ha => RingHom.mem_ker.mp (h ha)

variable {C : Type u} [CommRing C] [Algebra A C] {Ah : Type u} [CommRing Ah] [Algebra A Ah]

/-- The two residues agree on `C ⊗ B` when `χ' ∘ σ = res ∘ σh`. -/
theorem kap_map (χ' : R' →+* K) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a) (res : Ah →+* K)
    (hres : ∀ a, res (algebraMap A Ah a) = χ a) (σh : C →ₐ[A] Ah) (σ : C →ₐ[A] R')
    (hσ : ∀ c, χ' (σ c) = res (σh c)) (x : C ⊗[A] B) :
    kap χ ν βQ hβ χ' hχ' (Algebra.TensorProduct.map σ (AlgHom.id A B) x) =
      kap χ ν βQ hβ res hres (Algebra.TensorProduct.map σh (AlgHom.id A B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c b => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, kap_tmul, kap_tmul, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

end Tens

section Lam

end Lam

end RamanujanPetersson.EtPBC.Cov

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

/-- The fibre chart `B ⧸ J ≃ F` (level `0`, generic ideal). -/
def eqvG {B F : Type u} [CommRing B] [CommRing F] (J : Ideal B) (β : B →+* F) (hs : Function.Surjective β)
    (hk : RingHom.ker β = J) : B ⧸ J ^ (0 + 1) ≃+* F :=
  (Ideal.quotEquivOfEq (by rw [zero_add, pow_one, hk])).trans (RingHom.quotientKerEquivOfSurjective hs)

end EqvG

section BaseG

end BaseG

section KerKap

variable {K A R' B Q : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing Q] (χ : A →+* K) (ν : K →+* Q) (βQ : B →+* Q) (hβ : ∀ a, βQ (algebraMap A B a) = ν (χ a))
  (χ' : R' →+* K) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a)

theorem one_tmul_algebraMap_mul (a : A) (b : B) :
    (1 : R') ⊗ₜ[A] (algebraMap A B a * b) = algebraMap A R' a ⊗ₜ[A] b := by
  rw [Algebra.algebraMap_eq_smul_one (A := B) a, smul_mul_assoc, one_mul, ← TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one]

end KerKap

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFl =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1c): relations on a flat level-`m` chart come from the base (equational criterion)

* `mem_span_mul_fun`: `x ∈ span (range f) * 𝔟` is `∑ fᵢ eᵢ` with `eᵢ ∈ 𝔟`;
* **`flat_rel`**: for `q : B₀ ↠ b` with kernel `(p B₀)^(m+1)` and `E` a flat `b`-algebra, a relation vector `w` of `α` on
  `E` with entries in `p^n E` (`n ≤ m`) is `∑ yκ · rκ + v` with `rκ ∈ RelV p α ιB₀ n` (relations on `B₀` itself)
  and `v` with entries in `p^m E`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

theorem mem_span_mul_fun {B : Type u} [CommRing B] {h : ℕ} (f : Fin h → B) (𝔟 : Ideal B) (x : B)
    (hx : x ∈ Ideal.span (Set.range f) * 𝔟) : ∃ e : Fin h → B, (∀ i, e i ∈ 𝔟) ∧ x = ∑ i, f i * e i := by
  have hx' : x ∈ 𝔟 • Submodule.span B (Set.range f) := by
    rw [Ideal.smul_eq_mul, mul_comm]
    exact hx
  obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum 𝔟 f x).1 hx'
  refine ⟨fun i => a i, ha, ?_⟩
  rw [← hsum, Finsupp.sum_fintype a (fun i c => c • f i) (fun i => zero_smul _ _)]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]

section Fl

end Fl

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFil1 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-1d): overlap relations with entries in `p^j` split into chart relations

For a level-`k` cover `C` (charts `Bᵢ ⧸ Jᵢ^(k+1)`, `Jᵢ = p Bᵢ`):
* `decomp_succ`: an element of `p^(j+1) B` is `∑ αᵢ yᵢ` with `yᵢ ∈ p^j B`;
* `lψθ₀`, `lψθ₁`, `mem_lι₀`, `mem_lι₁`: bookkeeping for the level-`k` charts;
* `chart0_decomp`: a chart-0 relation with entries in `p^j` is `∑ cₗ ρ0ₗ + v` (base relations, flatness);
* `split_rel`: such a decomposition splits on the two charts (uniform `H¹` vanishing);
* **`lift_rel`**: an overlap relation `w` with entries in `p^j` is `ψ₀ a - u^d ψ₁ b` with `a`, `b` chart relations
  with entries in `p^j`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

theorem decomp_succ {R B : Type u} [CommRing R] [CommRing B] (p : Ideal R) {g : ℕ} (α : Fin g → R)
    (hα : p = Ideal.span (Set.range α)) (ι : R →+* B) (j : ℕ) {x : B} (hx : x ∈ (p ^ (j + 1)).map ι) :
    ∃ y : Fin g → B, (∀ i, y i ∈ (p ^ j).map ι) ∧ x = ∑ i, ι (α i) * y i := by
  have hp : p.map ι = Ideal.span (Set.range (ι ∘ α)) := by
    rw [hα, Ideal.map_span, Set.range_comp]
  rw [pow_succ', Ideal.map_mul, hp] at hx
  exact mem_span_mul_fun (ι ∘ α) _ x hx

section Lv

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁) (p : Ideal R)

theorem lψθ₀ {k : ℕ} (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) (b : B₀) :
    C.ψ₀ (C.a₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) b)) = C.a (Ideal.Quotient.mk (JN ^ (k + 1)) (φ₀ b)) := by
  have e := RingHom.congr_fun C.hψ₀ (Ideal.Quotient.mk (J₀ ^ (k + 1)) b)
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk] at e
  exact e

end Lv

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

/-- **Dependent choice** along `ℕ`. -/
theorem dep_choice {X : ℕ → Type*} (Rl : ∀ k, X (k + 1) → X k → Prop) (x0 : X 0)
    (h : ∀ k (x : X k), ∃ x' : X (k + 1), Rl k x' x) :
    ∃ f : ∀ k, X k, f 0 = x0 ∧ ∀ k, Rl k (f (k + 1)) (f k) := by
  choose g hg using h
  exact ⟨fun k => Nat.rec (motive := X) x0 (fun k xk => g k xk) k, rfl, fun k => hg k _⟩

/-- **Sequences by choice** with a step relation. -/
theorem seq_choice {α : Type*} (P : ℕ → α → Prop) (Q : ℕ → α → α → Prop) (h0 : ∃ a, P 0 a)
    (h : ∀ k a, P k a → ∃ a', P (k + 1) a' ∧ Q k a a') :
    ∃ f : ℕ → α, ∀ k, P k (f k) ∧ Q k (f k) (f (k + 1)) := by
  obtain ⟨a0, ha0⟩ := h0
  choose g hg hq using h
  obtain ⟨f, -, hf⟩ := dep_choice (X := fun k => {a // P k a}) (fun k a' a => a'.1 = g k a.1 a.2) ⟨a0, ha0⟩
    (fun k a => ⟨⟨g k a.1 a.2, hg k a.1 a.2⟩, rfl⟩)
  refine ⟨fun k => (f k).1, fun k => ⟨(f k).2, ?_⟩⟩
  show Q k (f k).1 (f (k + 1)).1
  rw [hf k]
  exact hq k _ _

section Ker

end Ker

section Fam

end Fam

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLim4 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-2d): compatible families are combinations with coefficients in a `p`-precomplete ring

For compatible families `σ : Fin r → Gam C H d` generating level `0`, over `R` with `IsPrecomplete p R`:
* `gam_agree`: two compatible families that agree at level `k` agree at every level `m ≤ k`;
* `gam_seq`: a level-`k₀` combination extends to a combination at all levels with congruent coefficients;
* **`gam_gen`**: every compatible family is `∑ aᵢ σᵢ` at all levels;
* **`gam_ker`**: a compatible family vanishing at level `k` is `∑ aᵢ σᵢ` with all `aᵢ ∈ p^(k+1)`;
* `gen_all`: every level-`m` section is a combination of the `σᵢ`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

theorem ideal_pow_smul_top {R : Type u} [CommRing R] (p : Ideal R) (m : ℕ) :
    (p ^ m • ⊤ : Submodule R R) = p ^ m := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

section Agree

end Agree

section Lim

end Lim

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

/-- **Degree bound on the two charts.** -/
theorem exists_deg_bound {ι : Type v} [Fintype ι] (K : Submodule A[X] (ι → A[X])) (hK : K.FG) :
    ∃ e : ℕ, ∀ (D : ℕ) (p q : ι → A[X]), (∀ i, (q i).natDegree ≤ D) →
      (X ^ D : A[X]) • p - q ∈ K → ∃ p' : ι → A[X], (∀ i, (p' i).degree < e) ∧ p - p' ∈ K := by
  classical
  obtain ⟨G, hG⟩ := hK
  refine ⟨G.sup (fun g => Finset.univ.sup fun i => (g i).natDegree) + 1, ?_⟩
  intro D p q hq hpq
  rcases subsingleton_or_nontrivial A with hA | hA
  · refine ⟨p, fun i => ?_, by simp⟩
    rw [Subsingleton.elim (p i) 0, degree_zero]
    exact WithBot.bot_lt_coe _
  have hpq' : (X ^ (D + 1) : A[X]) • p - (X : A[X]) • q ∈ K := by
    have h := K.smul_mem (X : A[X]) hpq
    rwa [smul_sub, smul_smul, ← pow_succ'] at h
  rw [← hG, Submodule.mem_span_finset] at hpq'
  obtain ⟨c, -, hc⟩ := hpq'
  have hYm : (X ^ (D + 1) : A[X]).Monic := monic_X_pow _
  have hY1 : (X ^ (D + 1) : A[X]) ≠ 1 := by
    intro h
    have h' := congrArg natDegree h
    rw [natDegree_X_pow, natDegree_one] at h'
    exact Nat.succ_ne_zero D h'
  refine ⟨p - ∑ g ∈ G, (c g /ₘ X ^ (D + 1)) • g, fun i => ?_, ?_⟩
  · have hci := congrFun hc i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hci ⊢
    have hsplit : ∑ g ∈ G, c g * g i = ∑ g ∈ G, (c g %ₘ X ^ (D + 1)) * g i +
        X ^ (D + 1) * ∑ g ∈ G, (c g /ₘ X ^ (D + 1)) * g i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      conv_lhs => rw [← modByMonic_add_div (c g) (X ^ (D + 1))]
      ring
    have hcomp : X ^ (D + 1) * (p i - ∑ g ∈ G, (c g /ₘ X ^ (D + 1)) * g i) =
        X * q i + ∑ g ∈ G, (c g %ₘ X ^ (D + 1)) * g i := by
      linear_combination hsplit - hci
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    rw [← coeff_X_pow_mul _ (D + 1) m, hcomp, coeff_add, finsetSum_coeff]
    have hq' : (X * q i).natDegree < m + (D + 1) :=
      (natDegree_mul_le.trans (add_le_add natDegree_X_le (hq i))).trans_lt (by omega)
    rw [coeff_eq_zero_of_natDegree_lt hq', zero_add]
    refine Finset.sum_eq_zero fun g hg => coeff_eq_zero_of_natDegree_lt ?_
    have h1 : (c g %ₘ X ^ (D + 1)).natDegree < D + 1 := by
      have := natDegree_modByMonic_lt (c g) hYm hY1
      rwa [natDegree_X_pow] at this
    have h2 : (g i).natDegree ≤ G.sup (fun g => Finset.univ.sup fun i => (g i).natDegree) :=
      (Finset.le_sup (f := fun i => (g i).natDegree) (Finset.mem_univ i)).trans
        (Finset.le_sup (f := fun g => Finset.univ.sup fun i => (g i).natDegree) hg)
    exact natDegree_mul_le.trans_lt (by omega)
  · rw [sub_sub_cancel]
    exact Submodule.sum_mem _ fun g hg => Submodule.smul_mem _ _ (hG ▸ Submodule.subset_span hg)

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

/-- The `X`-power torsion of an `A[X]`-module. -/
def xTors (M : Type v) [AddCommGroup M] [Module A[X] M] : Submodule A[X] M where
  carrier := {m | ∃ k : ℕ, (X ^ k : A[X]) • m = 0}
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    rw [smul_add, pow_add, mul_smul, smul_comm ((X : A[X]) ^ k) ((X : A[X]) ^ l) a, hk, smul_zero, mul_smul, hl,
      smul_zero, add_zero]
  zero_mem' := ⟨0, smul_zero _⟩
  smul_mem' := by
    rintro c m ⟨k, hk⟩
    exact ⟨k, by rw [smul_comm, hk, smul_zero]⟩

section TwoChart

variable {M₁ : Type w} {N : Type w'} [AddCommGroup M₁] [Module A[X] M₁] [Module A M₁] [IsScalarTower A A[X] M₁]
  [AddCommGroup N] [Module A[X] N] [Module A N] [IsScalarTower A A[X] N]

omit [IsScalarTower A A[X] M₁] [IsScalarTower A A[X] N] in
theorem pow_smul_iter (φ₁ : M₁ →ₗ[A] N) (h₁ : ∀ m, (X : A[X]) • φ₁ ((X : A[X]) • m) = φ₁ m) :
    ∀ (k : ℕ) (m : M₁), (X ^ k : A[X]) • φ₁ ((X ^ k : A[X]) • m) = φ₁ m
  | 0, m => by simp
  | k + 1, m => by
    rw [pow_succ, mul_smul, mul_smul, smul_comm ((X : A[X]) ^ k) (X : A[X]) m, h₁, pow_smul_iter φ₁ h₁ k m]

/-- The sections over the two charts: `{(a, b) | φ₀ a = φ₁ b}`. -/
def twoChart {M₀ : Type v} [AddCommGroup M₀] [Module A[X] M₀] [Module A M₀] [IsScalarTower A A[X] M₀]
    (φ₀ : M₀ →ₗ[A[X]] N) (φ₁ : M₁ →ₗ[A] N) : Submodule A (M₀ × M₁) :=
  LinearMap.eqLocus ((φ₀.restrictScalars A) ∘ₗ LinearMap.fst A M₀ M₁) (φ₁ ∘ₗ LinearMap.snd A M₀ M₁)

end TwoChart

end RamanujanPetersson.EtPBC.Z1

end

end

-- ===== S4.Def_RP_EtPBC_A_CovHat8 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-4a): shifts of fractions by `T₀`, `T₁`

* `frac₀_mT₀` (`T₀ y / T₀^(d+1) = y / T₀ᵈ`), `frac₀_mT₁` (`T₁ y / T₀^(d+1) = t₀ · y / T₀ᵈ`), and the chart-1
  versions `frac₁_mT₁`, `frac₁_mT₀`;
* `frac₀_dec`, `frac₁_dec`: fractions of `T₀ y + T₁ y'`; `sum_comb₀`, `sum_comb₁` (coefficient bookkeeping).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Comb

/-- Coefficient bookkeeping for chart `0`. -/
theorem sum_comb₀ {S T : Type u} [CommRing S] [CommRing T] (β : S →+* T) (t : S) {r : ℕ} (b b' : Fin r → S)
    (w : Fin r → T) : ∑ i, β (b i) * w i + β t * ∑ i, β (b' i) * w i = ∑ i, β (b i + t * b' i) * w i := by
  simp only [map_add, map_mul, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- Coefficient bookkeeping for chart `1`. -/
theorem sum_comb₁ {S T : Type u} [CommRing S] [CommRing T] (β : S →+* T) (t : S) {r : ℕ} (b b' : Fin r → S)
    (w : Fin r → T) : β t * ∑ i, β (b i) * w i + ∑ i, β (b' i) * w i = ∑ i, β (t * b i + b' i) * w i := by
  simp only [map_add, map_mul, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

end Comb

section MT

end MT

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFq =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E3c1): generic inputs of the etale-on-a-basic-open step

* **`fq_flat`**: if `θ : M →ₐ[B] E` is surjective with kernel `I M` and `E` is flat over `B ⧸ I`, then `M ⧸ I M` is
  flat over `B ⧸ I` (the hypothesis `hfl` of `lf_mem_freeLocus`, level by level);
* **`fq_basicOpen`**: an open subset of `Spec A` containing `V(J)` contains a basic open `D(g)` with `g - 1 ∈ J`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

/-- **Flatness of `M ⧸ I M` from a surjection onto a flat `B ⧸ I`-algebra with kernel `I M`.** -/
theorem fq_flat {B M E : Type u} [CommRing B] [CommRing M] [CommRing E] [Algebra B M] (I : Ideal B)
    [Algebra (B ⧸ I) E] [Algebra B E] [IsScalarTower B (B ⧸ I) E] (θ : M →ₐ[B] E)
    (hθ : Function.Surjective θ) (hker : RingHom.ker θ = I.map (algebraMap B M)) [Module.Flat (B ⧸ I) E] :
    Module.Flat (B ⧸ I) (M ⧸ (I • ⊤ : Submodule B M)) := by
  have hsub : (I • ⊤ : Submodule B M) = (RingHom.ker θ).restrictScalars B := by
    rw [hker, Ideal.smul_top_eq_map]
  haveI : IsScalarTower B (B ⧸ I) (M ⧸ (I • ⊤ : Submodule B M)) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
  have hs : Function.Surjective (algebraMap B (B ⧸ I)) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨y, rfl⟩
  let e₁ : (M ⧸ (I • ⊤ : Submodule B M)) ≃ₗ[B] M ⧸ ((RingHom.ker θ).restrictScalars B) :=
    Submodule.quotEquivOfEq (h := hsub)
  let e₂ : (M ⧸ ((RingHom.ker θ).restrictScalars B)) ≃ₗ[B] M ⧸ RingHom.ker θ :=
    Submodule.Quotient.restrictScalarsEquiv (S := B) (RingHom.ker θ)
  let e₃ : (M ⧸ RingHom.ker θ) ≃ₐ[B] E := Ideal.quotientKerAlgEquivOfSurjective hθ
  let e : (M ⧸ (I • ⊤ : Submodule B M)) ≃ₗ[B] E := (e₁.trans e₂).trans e₃.toLinearEquiv
  exact Module.Flat.of_linearEquiv (LinearEquiv.extendScalarsOfSurjective hs e)

/-- **An open set containing `V(J)` contains some `D(g)` with `g ≡ 1 mod J`.** -/
theorem fq_basicOpen {A : Type u} [CommRing A] (J : Ideal A) (U : Set (PrimeSpectrum A)) (hU : IsOpen U)
    (hJU : PrimeSpectrum.zeroLocus (J : Set A) ⊆ U) :
    ∃ g : A, g - 1 ∈ J ∧ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) ⊆ U := by
  obtain ⟨K, hK⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Uᶜ).1 hU.isClosed_compl
  have htop : J ⊔ K = ⊤ := by
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_sup]
    ext q
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hq hqK
    have hc : q ∈ Uᶜ := by rw [hK]; exact hqK
    exact hc (hJU hq)
  have h1 : (1 : A) ∈ J ⊔ K := by rw [htop]; exact Submodule.mem_top
  obtain ⟨j, hj, g, hg, hjg⟩ := Submodule.mem_sup.1 h1
  refine ⟨g, ?_, ?_⟩
  · have hgj : g - 1 = -j := by rw [← hjg]; ring
    rw [hgj]
    exact J.neg_mem hj
  · intro q hq
    by_contra hqU
    have hq' : q ∈ PrimeSpectrum.zeroLocus (K : Set A) := by
      rw [← hK]
      exact hqU
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hq (hq' hg)

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFe =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E3c2): etale on a basic open

* **`fq_etale`**: for `B` noetherian and `M` a finite `B`-algebra, if `D(g) ⊆ freeLocus B M` and `r` kills
  `Ω[M⁄B]`, then `M[(g r)⁻¹]` is etale over `B`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

/-- **Etale on `D(g r)`** from freeness over `D(g)` and `r` killing the differentials. -/
theorem fq_etale {B M : Type u} [CommRing B] [CommRing M] [Algebra B M] [IsNoetherianRing B]
    [Module.Finite B M] (g : B) (hg : ↑(PrimeSpectrum.basicOpen g) ⊆ Module.freeLocus B M) (r : M)
    (hr : ∀ ω : Ω[M⁄B], r • ω = 0) :
    Algebra.Etale B (Localization.Away (algebraMap B M g * r)) := by
  set S := Localization.Away (algebraMap B M g * r)
  set T := Localization.Away (algebraMap B M g)
  -- flatness of `T = M[g⁻¹]` over `B`
  haveI : Module.FinitePresentation B M := Module.finitePresentation_of_finite (R := B) (M := M)
  have hproj : Module.Projective (Localization.Away g) (LocalizedModule.Away g M) :=
    (Module.basicOpen_subset_freeLocus_iff (R := B) (M := M)).mp hg
  haveI : Module.Flat B (LocalizedModule.Away g M) :=
    Module.Flat.trans B (Localization.Away g) (LocalizedModule.Away g M)
  haveI hloc : IsLocalizedModule (Submonoid.powers g) (IsScalarTower.toAlgHom B M T).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization]
    convert (inferInstance : IsLocalization (Submonoid.powers (algebraMap B M g)) T) using 1
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  haveI : Module.Flat B T := Module.Flat.of_linearEquiv
    (IsLocalizedModule.iso (Submonoid.powers g) (IsScalarTower.toAlgHom B M T).toLinearMap).symm
  -- `S' = T[r⁻¹]` is flat over `B` and is `M[(g r)⁻¹]`
  let S' := Localization.Away (algebraMap M T r)
  haveI : Module.Flat B S' := inferInstance
  haveI : IsScalarTower B M S' := IsScalarTower.of_algebraMap_eq (R := B) (S := M) (A := S') (fun x => by
    have h1 : (algebraMap B S' x : S') = algebraMap T S' (algebraMap B T x) :=
      IsScalarTower.algebraMap_apply B T S' x
    have h2 : (algebraMap M S' (algebraMap B M x) : S') =
        algebraMap T S' (algebraMap M T (algebraMap B M x)) :=
      IsScalarTower.algebraMap_apply M T S' _
    rw [h1, h2, ← IsScalarTower.algebraMap_apply B M T])
  let e : S ≃ₐ[M] S' := IsLocalization.algEquiv (Submonoid.powers (algebraMap B M g * r)) S S'
  haveI : Module.Flat B S := Module.Flat.of_linearEquiv (e.restrictScalars B).toLinearEquiv
  -- finite presentation
  haveI : Algebra.FinitePresentation B M := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.FinitePresentation M S :=
    IsLocalization.Away.finitePresentation (algebraMap B M g * r)
  haveI : Algebra.FinitePresentation B S := .trans _ M _
  -- unramified
  haveI : Algebra.FormallyUnramified B S := by
    refine (Algebra.basicOpen_subset_unramifiedLocus_iff (R := B)).mp ?_
    intro P hP
    have hrP : r ∉ P.asIdeal := fun h => hP (P.asIdeal.mul_mem_left _ h)
    change P ∈ Algebra.unramifiedLocus B M
    rw [Algebra.unramifiedLocus_eq_compl_support]
    exact fun hs => hrP (Module.annihilator_le_of_mem_support hs (Module.mem_annihilator.2 hr))
  exact Algebra.Etale.of_formallyUnramified_of_flat

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

theorem lf_res_sum {R N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup N] [Module R N] {ι : Type*}
    (v : ι → N) (s : Finset ι) (c : ι → R) :
    ∑ j ∈ s, residue R (c j) • TensorProduct.mk R (ResidueField R) N 1 (v j)
      = TensorProduct.mk R (ResidueField R) N 1 (∑ j ∈ s, c j • v j) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  exact algebraMap_smul (ResidueField R) (c j) _

set_option backward.isDefEq.respectTransparency.types false in
theorem lf_mk_eq_zero_iff {R N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup N] [Module R N] (x : N) :
    TensorProduct.mk R (ResidueField R) N 1 x = 0 ↔ x ∈ (maximalIdeal R) • (⊤ : Submodule R N) := by
  rw [← LinearMap.ker_tensorProductMk (Q := N) (I := maximalIdeal R)]
  exact LinearMap.mem_ker.symm

end LocFlat

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_LocFree =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5, E3b2): the primes over `J` lie in the free locus

For a noetherian ring `A`, an ideal `J` and a finite `A`-module `M` with `M ⧸ J^(k+1) M` flat over `A ⧸ J^(k+1)` for
all `k`:
* `lf_flat_quot_iff`: flatness of `M ⧸ I M` over `A ⧸ I` is flatness of `(A ⧸ I) ⊗ M`;
* `lf_flat_loc`: it passes to any `A`-algebra `Rₚ` (`Rₚ ⊗ M` modulo `I Rₚ`);
* **`lf_mem_freeLocus`**: every prime `𝔮 ⊇ J` lies in `Module.freeLocus A M`.
-/

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace RamanujanPetersson.EtPBC.Cov

universe u

section LocFree

theorem lf_flat_quot_iff {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N] (I : Ideal R) :
    Module.Flat (R ⧸ I) (N ⧸ (I • ⊤ : Submodule R N)) ↔ Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] N) := by
  let e : ((R ⧸ I) ⊗[R] N) ≃ₗ[R ⧸ I] N ⧸ (I • ⊤ : Submodule R N) :=
    LinearEquiv.extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap R (R ⧸ I)))
      (TensorProduct.quotTensorEquivQuotSMul N I)
  exact ⟨fun _ => Module.Flat.of_linearEquiv e, fun _ => Module.Flat.of_linearEquiv e.symm⟩

end LocFree

end RamanujanPetersson.EtPBC.Cov

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

/-- `1 ⊗ dx = 0` in `(E ⧸ JE) ⊗ Ω[E⁄B]` for `x ∈ JE`. -/
theorem tmul_D_eq_zero (x : E) (hx : x ∈ J.map (algebraMap B E)) :
    (1 : E ⧸ J.map (algebraMap B E)) ⊗ₜ[E] KaehlerDifferential.D B E x = 0 := by
  have hx' : x ∈ Submodule.span E (⇑(algebraMap B E) '' (J : Set B)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x h =>
    obtain ⟨b, -, rfl⟩ := h
    rw [Derivation.map_algebraMap, tmul_zero]
  | zero => rw [map_zero, tmul_zero]
  | add x y _ _ h₁ h₂ => rw [map_add, tmul_add, h₁, h₂, add_zero]
  | smul a x hx h =>
    have h0 : x • (1 : E ⧸ J.map (algebraMap B E)) = 0 := by
      rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hx
    rw [smul_eq_mul, Derivation.leibniz, tmul_add, tmul_smul, h, smul_zero, zero_add, tmul_smul, smul_tmul', h0,
      zero_tmul]

end Unr

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovSp =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2, properness input): `1` is not an `m`-polynomial in both `x` and `x⁻¹`

**`not_top_and_top`** (the lemma in Atiyah-Macdonald 5.21): for an ideal `m ≤ jacobson ⊥` of `R`, a ring map
`ι : R → S` to a nontrivial ring and `x y = 1` in `S`, the element `1` is not both `P(x)` and `Q(y)` with `P`, `Q`
having coefficients in `m`. Geometrically: every point of `P¹` over a base with `m ≤ jacobson ⊥` specializes into
the closed fibre `V(m)` of one of the two charts (used for flatness and unramifiedness away from the closed fibre).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (ι : R →+* S) (m : Ideal R)

theorem pow_mul_eval₂_inv (x y : S) (hxy : x * y = 1) (Q : R[X]) :
    x ^ (Q.natDegree + 1) * Q.eval₂ ι y =
      ∑ j ∈ Finset.range (Q.natDegree + 1), ι (Q.coeff j) * x ^ (Q.natDegree + 1 - j) := by
  rw [eval₂_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ Q.natDegree + 1 := by
    have := Finset.mem_range.1 hj
    omega
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hj'
  rw [hl, Nat.add_sub_cancel_left]
  have hp : (x * y) ^ j = 1 := by rw [hxy, one_pow]
  linear_combination (ι (Q.coeff j) * x ^ l) * hp

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovGlob =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5a): closed loci on `P¹` that miss the closed fibre are empty

* `nak_poly`: if `B` is finite over `R[X]` (via `X ↦ t`) and `K + m B = ⊤`, then every ring map `g : B → S` killing
  `K` sends some polynomial `P(t)` with coefficients in `m` to `1` (Nakayama over `R[X]`);
* **`glob`**: for two charts `B₀`, `B₁` finite over `R[X]` (via `t₀`, `t₁`) glued along `N = B₀[1/t₀]`,
  `t₀ t₁ = 1` in `N`, `m ≤ jacobson ⊥`, and ideals `K₀`, `K₁` with `Kᵢ + m Bᵢ = ⊤` whose zero loci are compatible on the
  overlap, `K₀ = ⊤` (Atiyah-Macdonald 5.21 via `not_top_and_top`).
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Glob

variable {R : Type u} [CommRing R]

/-- **Nakayama over `R[X]`.** -/
theorem nak_poly {B S : Type u} [CommRing B] [CommRing S] (ιB : R →+* B) (t : B)
    (hB : (eval₂RingHom ιB t).Finite) (m : Ideal R) (K : Ideal B) (hK : K ⊔ m.map ιB = ⊤) (g : B →+* S)
    (hg : K ≤ RingHom.ker g) : ∃ P : R[X], (∀ i, P.coeff i ∈ m) ∧ P.eval₂ (g.comp ιB) (g t) = 1 := by
  letI := (eval₂RingHom ιB t).toAlgebra
  haveI : Module.Finite R[X] B := hB
  haveI : Module.Finite R[X] (B ⧸ K) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R[X] K).toLinearMap Ideal.Quotient.mk_surjective
  have main : ∀ y ∈ m.map ιB, ∀ b : B,
      Ideal.Quotient.mk K (b * y) ∈ (m.map (C : R →+* R[X])) • (⊤ : Submodule R[X] (B ⧸ K)) := by
    intro y hy
    have hy' : y ∈ Submodule.span B (ιB '' (m : Set R)) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      intro b
      have e : Ideal.Quotient.mk K (b * ιB c) = (C c : R[X]) • Ideal.Quotient.mk K b := by
        rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul]
        congr 1
        show b * ιB c = eval₂ ιB t (C c) * b
        rw [eval₂_C, mul_comm]
      rw [e]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hc) Submodule.mem_top
    | zero =>
      intro b
      rw [mul_zero, map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro b
      rw [mul_add, map_add]
      exact add_mem (hx b) (hy b)
    | smul a x _ hx =>
      intro b
      rw [smul_eq_mul, ← mul_assoc]
      exact hx (b * a)
  have key : (⊤ : Submodule R[X] (B ⧸ K)) ≤ (m.map (C : R →+* R[X])) • ⊤ := by
    intro z _
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h1 : (1 : B) ∈ K ⊔ m.map ιB := hK ▸ Submodule.mem_top
    obtain ⟨k, hk, y, hy, hky⟩ := Submodule.mem_sup.1 h1
    have hb : Ideal.Quotient.mk K b = Ideal.Quotient.mk K (b * y) := by
      rw [Ideal.Quotient.eq]
      have e : b - b * y = b * k := by linear_combination (-b) * hky
      rw [e]
      exact K.mul_mem_left b hk
    rw [hb]
    exact main y hy b
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul (m.map (C : R →+* R[X])) ⊤
      Module.Finite.fg_top key
  have h1 : r • (1 : B ⧸ K) = 0 := hr 1 Submodule.mem_top
  rw [Algebra.smul_def, mul_one, ← Ideal.Quotient.mk_algebraMap] at h1
  have h2 : g (eval₂ ιB t r) = 0 := RingHom.mem_ker.1 (hg (Ideal.Quotient.eq_zero_iff_mem.1 h1))
  have h3 : 1 - r ∈ m.map (C : R →+* R[X]) := by
    have := neg_mem hr1
    rwa [neg_sub] at this
  refine ⟨1 - r, fun i => Ideal.mem_map_C_iff.1 h3 i, ?_⟩
  rw [eval₂_sub, eval₂_one, ← Polynomial.hom_eval₂, h2, sub_zero]

end Glob

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovLoc =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-5b): being etale at a prime transports along a localization square

* **`loc_etaleAt`**: for `B → A`, `N = B[1/t]`, `A' = A[1/t]` (compatible algebras) and a prime `Q` of `A'`,
  `A` is etale over `B` at `Q ∩ A` iff `A'` is etale over `N` at `Q`
  (`A_{Q ∩ A} ≃ₐ[A] A'_Q`, and `B → N` is formally etale).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section LocEt

variable {B A N A' : Type u} [CommRing B] [CommRing A] [CommRing N] [CommRing A']
  [Algebra B A] [Algebra B N] [Algebra N A'] [Algebra A A'] [Algebra B A']
  [IsScalarTower B N A'] [IsScalarTower B A A']

/-- **Etale-at along a localization square.** -/
theorem loc_etaleAt (t : B) [IsLocalization.Away t N] [IsLocalization.Away (algebraMap B A t) A']
    (Q : Ideal A') [Q.IsPrime] :
    Algebra.IsEtaleAt B (Q.comap (algebraMap A A')) ↔ Algebra.IsEtaleAt N Q := by
  haveI : Algebra.FormallyEtale B N :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := N) (Submonoid.powers t)
  haveI : IsLocalization.AtPrime (Localization.AtPrime Q) (Q.comap (algebraMap A A')) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers (algebraMap B A t)) (Localization.AtPrime Q) Q
  haveI : IsScalarTower B A (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B A' (Localization.AtPrime Q), IsScalarTower.algebraMap_apply B A A',
      ← IsScalarTower.algebraMap_apply A A' (Localization.AtPrime Q)]
  haveI : IsScalarTower B N (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply B A' (Localization.AtPrime Q), IsScalarTower.algebraMap_apply B N A',
      ← IsScalarTower.algebraMap_apply N A' (Localization.AtPrime Q)]
  let e : Localization.AtPrime (Q.comap (algebraMap A A')) ≃ₐ[A] Localization.AtPrime Q :=
    IsLocalization.algEquiv (Q.comap (algebraMap A A')).primeCompl _ _
  have h1 : Algebra.FormallyEtale B (Localization.AtPrime (Q.comap (algebraMap A A'))) ↔
      Algebra.FormallyEtale B (Localization.AtPrime Q) :=
    ⟨fun _ => .of_equiv (e.restrictScalars B), fun _ => .of_equiv (e.symm.restrictScalars B)⟩
  exact h1.trans Algebra.FormallyEtale.iff_restrictScalars

end LocEt

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

/-- The ideal of the non-etale locus. -/
def etK : Ideal M := PrimeSpectrum.vanishingIdeal (Algebra.etaleLocus B M)ᶜ

variable {B M} [Algebra.FinitePresentation B M]

theorem etK_of_away (s : M) (hs : Algebra.Etale B (Localization.Away s)) : s ∈ etK B M := by
  rw [etK, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  by_contra hsq
  exact hq ((Algebra.basicOpen_subset_etaleLocus_iff_etale.2 hs) ((PrimeSpectrum.mem_basicOpen s q).2 hsq))

end EtK

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3c =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3c): finite generating families of extended ideals

* **`map_fin_gens`**: if `p` is f.g., then `p.map f = span (range α)` for some `α : Fin g → B`, with `α i ∈ p.map f`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u v

theorem map_fin_gens {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) (p : Ideal A)
    (hp : p.FG) : ∃ (g : ℕ) (α : Fin g → B), p.map f = Ideal.span (Set.range α) ∧ ∀ i, α i ∈ p.map f := by
  obtain ⟨g, α, hα⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hp
  have h : p.map f = Ideal.span (Set.range (f ∘ α)) := by
    rw [← hα, Ideal.submodule_span_eq, Ideal.map_span, Set.range_comp]
  refine ⟨g, f ∘ α, h, fun i => ?_⟩
  rw [h]
  exact Ideal.subset_span ⟨i, rfl⟩

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3e =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3e): residue and base-change facts for the instantiation over `Â`

* **`ker_resHat`**: `ker (resHat χ) = (ker χ) Â` (`A` noetherian); `chi_surj`.
* `kap_surj`: `kap` is surjective when the fibre chart is; **`kap_comm`**: `kap` commutes with the gluing maps.
* `bc_tmul`, **`bc_inc`**: `map id φ` on pure tensors, and it fixes the image of `R'`.
-/

set_option autoImplicit false

open TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section ResHat

variable (K : Type u) [Field K] (A : Type u) [CommRing A] [Algebra K A]

theorem resHat_eq (χ : A →ₐ[K] K) (x : AdicCompletion (RingHom.ker χ) A) :
    resHat K A χ x = Ideal.Quotient.lift (RingHom.ker χ) (χ : A →+* K) (fun _ h => RingHom.mem_ker.mp h)
      ((AdicCompletion.evalOneₐ (RingHom.ker χ)).toRingHom x) := rfl

theorem chi_surj (χ : A →ₐ[K] K) : Function.Surjective (χ : A →+* K) := fun k =>
  ⟨algebraMap K A k, by simp⟩

end ResHat

section KapA

variable {K A R' B N : Type u} [Field K] [CommRing A] [CommRing R'] [Algebra A R'] [CommRing B] [Algebra A B]
  [CommRing N] [Algebra A N] (χ : A →+* K) (χ' : R' →+* K) (hχ' : ∀ a, χ' (algebraMap A R' a) = χ a)

theorem kap_surj {Q : Type u} [CommRing Q] (ν : K →+* Q) (βQ : B →+* Q) (hβ : ∀ a, βQ (algebraMap A B a) = ν (χ a))
    (hs : Function.Surjective βQ) : Function.Surjective (kap χ ν βQ hβ χ' hχ') := fun q => by
  obtain ⟨b, rfl⟩ := hs q
  exact ⟨(1 : R') ⊗ₜ[A] b, by rw [kap_tmul, map_one, map_one, one_mul]⟩

theorem bc_tmul (φ : B →ₐ[A] N) (r : R') (b : B) :
    (Algebra.TensorProduct.map (AlgHom.id A R') φ : R' ⊗[A] B →+* R' ⊗[A] N) (r ⊗ₜ b) = r ⊗ₜ φ b :=
  rfl

end KapA

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

theorem aeval_monomial_mem_pow (x : σ →₀ ℕ) (c : A) :
    MvPolynomial.aeval a (MvPolynomial.monomial x c) ∈ (Ideal.span (Set.range a)) ^ x.degree := by
  rw [MvPolynomial.aeval_monomial]
  refine Ideal.mul_mem_left _ _ ?_
  rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self (f := a) i)) _

end HatN1

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

/-- The ideal generated by the variables. -/
abbrev Xid (σ : Type v) (A : Type u) [CommRing A] : Ideal (MvPowerSeries σ A) :=
  Ideal.span (Set.range (X : σ → MvPowerSeries σ A))

end HatN2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs3f =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As3f): the completed cover over `Â` from the `CoverLiftAt₂` data

**`hat_lift`**: under the hypotheses of `CoverLiftAt₂` (and `A` noetherian), there are rings `Ê₀, Ê₁, Ê` with
finite etale `Â ⊗ B₀ → Ê₀`, `Â ⊗ B₁ → Ê₁`, glued by away maps over `Â ⊗ N → Ê`, and surjections `θ̂ᵢ : Êᵢ ↠ Eᵢ`
with kernel `(ker χ) Êᵢ`, compatible with `ψᵢ` and with `r ⊗ b ↦ resHat r * βᵢ b`. (`hat_cov` over `R = Â`,
charts `Â ⊗ Bᵢ`, level-0 cover `baseG` with fibre charts `kap`.)
-/

set_option autoImplicit false

open Polynomial TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section AwayA

variable {A B₀ N : Type u} [CommRing A] [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
  [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N] (φ₀ : B₀ →ₐ[A[X]] N)

theorem away_A₀ (hs₀ : ∀ y : N, ∃ (k : ℕ) (a : B₀), algebraMap A[X] N X ^ k * y = φ₀ a)
    (hk₀ : ∀ a, φ₀ a = 0 → ∃ k : ℕ, algebraMap A[X] B₀ X ^ k * a = 0) :
    IsAwayMap ((φ₀.restrictScalars A : B₀ →ₐ[A] N) : B₀ →+* N) (algebraMap A[X] B₀ X) := by
  refine ⟨fun y => ?_, fun a ha => hk₀ a ha⟩
  obtain ⟨k, a, h⟩ := hs₀ y
  refine ⟨k, a, ?_⟩
  have e : φ₀ (algebraMap A[X] B₀ X) ^ k * y = φ₀ a := by
    rw [AlgHom.commutes]
    exact h
  exact e

end AwayA

section HatLift

end HatLift

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovAs4a =====
section

/-!
# S4-EtPBC-A, R4-T2 (A3 assembly, As4a): a map between two localizations away from `t` is bijective

**`away_bij`**: if `ψa : E → E₁` and `ψb : E → E₂` are both away maps at `t` (`IsAwayMap`), `ψa t` is a unit and
`m ∘ ψa = ψb`, then `m` is bijective; `awayEquiv` is the resulting ring isomorphism.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section AwayBij

variable {E E₁ E₂ : Type u} [CommRing E] [CommRing E₁] [CommRing E₂] (ψa : E →+* E₁) (ψb : E →+* E₂) (t : E)

/-- **A map between two localizations away from `t` is bijective.** -/
theorem away_bij (ha : IsAwayMap ψa t) (hb : IsAwayMap ψb t) (hua : IsUnit (ψa t)) (m : E₁ →+* E₂)
    (hm : ∀ x, m (ψa x) = ψb x) : Function.Bijective m := by
  obtain ⟨v, hv⟩ := hua.exists_right_inv
  refine ⟨(injective_iff_map_eq_zero m).mpr fun y hy => ?_, fun z => ?_⟩
  · obtain ⟨k, a, hka⟩ := ha.1 y
    have h0 : ψb a = 0 := by rw [← hm, ← hka, map_mul, hy, mul_zero]
    obtain ⟨j, hj⟩ := hb.2 a h0
    have e : ψa t ^ j * (ψa t ^ k * y) = 0 := by rw [hka, ← map_pow, ← map_mul, hj, map_zero]
    have hu : IsUnit (ψa t ^ j * ψa t ^ k) := (hua.pow j).mul (hua.pow k)
    rw [← mul_assoc] at e
    exact hu.mul_right_eq_zero.mp e
  · obtain ⟨k, a, hka⟩ := hb.1 z
    refine ⟨ψa a * v ^ k, ?_⟩
    have hmv : ψb t * m v = 1 := by rw [← hm, ← map_mul, hv, map_one]
    rw [map_mul, map_pow, hm, ← hka]
    calc ψb t ^ k * z * m v ^ k = z * (ψb t * m v) ^ k := by ring
      _ = z := by rw [hmv, one_pow, mul_one]

end AwayBij

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

theorem presRel_zero {P : Type u} [CommRing P] {r : ℕ} (g : Fin r → MvPolynomial (Fin r) P) (j : Fin r) :
    Ideal.Quotient.mk (Ideal.span (Set.range g)) (g j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

section PresN

variable {P P' E' : Type u} [CommRing P] [CommRing P'] [CommRing E'] {r : ℕ}
  (f : P →+* P') (g : Fin r → MvPolynomial (Fin r) P) (bN : P' →+* E') (θ : Pres g →+* E')

theorem awayMap_of_equiv {E E₁ : Type u} [CommRing E] [CommRing E₁] (q : E →+* E₁) (b : P →+* E) (t : P)
    (hq : IsAwayMap q (b t)) (e : Pres g ≃+* E) (he : ∀ a, e (algebraMap P (Pres g) a) = b a) :
    IsAwayMap (q.comp (e : Pres g →+* E)) (algebraMap P (Pres g) t) := by
  have h := isAwayMap_comp_equiv_pr q (b t) hq e
  have h' : e.symm (b t) = algebraMap P (Pres g) t := by rw [← he, RingEquiv.symm_apply_apply]
  rwa [h'] at h

end PresN

section Subst

variable {P : Type u} [CommRing P] {r r' : ℕ} (g : Fin r → MvPolynomial (Fin r) P)
  (g' : Fin r' → MvPolynomial (Fin r') P)

theorem mk_bind₁_eq (m : Pres g →+* Pres g')
    (hm : ∀ a, m (algebraMap P (Pres g) a) = algebraMap P (Pres g') a) (v : Fin r → MvPolynomial (Fin r') P)
    (hv : ∀ i, Ideal.Quotient.mk (Ideal.span (Set.range g')) (v i) =
      m (Ideal.Quotient.mk (Ideal.span (Set.range g)) (MvPolynomial.X i)))
    (x : MvPolynomial (Fin r) P) :
    Ideal.Quotient.mk (Ideal.span (Set.range g')) (MvPolynomial.bind₁ v x) =
      m (Ideal.Quotient.mk (Ideal.span (Set.range g)) x) := by
  have h : (Ideal.Quotient.mk (Ideal.span (Set.range g'))).comp
      (MvPolynomial.bind₁ v : MvPolynomial (Fin r) P →+* MvPolynomial (Fin r') P) =
      m.comp (Ideal.Quotient.mk (Ideal.span (Set.range g))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      show Ideal.Quotient.mk _ (MvPolynomial.bind₁ v (MvPolynomial.C a)) =
        m (Ideal.Quotient.mk _ (MvPolynomial.C a))
      rw [MvPolynomial.bind₁_C_right]
      first
        | exact (hm a).symm
        | (have h1 := hm a
           simp only [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply, MvPolynomial.algebraMap_eq] at h1
           exact h1.symm)
    · intro i
      show Ideal.Quotient.mk _ (MvPolynomial.bind₁ v (MvPolynomial.X i)) =
        m (Ideal.Quotient.mk _ (MvPolynomial.X i))
      rw [MvPolynomial.bind₁_X_right]
      exact hv i
  exact DFunLike.congr_fun h x

end Subst

/-- A finite etale ring map is presented by a square system with etale and finite witnesses. -/
theorem chart_pres {P E : Type u} [CommRing P] [CommRing E] (b : P →+* E) (het : b.Etale) (hfi : b.Finite) :
    ∃ (r : ℕ) (g : Fin r → MvPolynomial (Fin r) P) (e : Pres g ≃+* E),
      (∃ w, jdet g * w - 1 ∈ Ideal.span (Set.range g)) ∧
      (∀ j, ∃ q : Polynomial P, q.Monic ∧ Polynomial.aeval (MvPolynomial.X j) q ∈ Ideal.span (Set.range g)) ∧
      ∀ a, e (algebraMap P (Pres g) a) = b a := by
  letI := b.toAlgebra
  haveI : Algebra.Etale P E := het
  haveI : Module.Finite P E := hfi
  obtain ⟨ι, σ, _, _, Q, r, ee, eσ, hJ, hF⟩ := exists_reRel_hJ_hF (P := P) (E := E)
  exact ⟨r, reRel Q.toPresentation ee eσ, (presEquiv Q.toPresentation ee eσ).toRingEquiv, hJ, hF,
    fun a => presEquiv_algebraMap Q.toPresentation ee eσ a⟩

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

theorem exists_fg_lift {ι : Type*} [Finite ι] (z : ι → S ⊗[A] B) :
    ∃ C₀ : Subalgebra A S, C₀.FG ∧ ∀ k, ∃ x : C₀ ⊗[A] B, C₀.val.toLinearMap.rTensor B x = z k := by
  classical
  have := Fintype.ofFinite ι
  choose T hT using fun k => TensorProduct.exists_finset (z k)
  obtain ⟨F, hF⟩ : ∃ F : Finset S, ∀ k, ∀ i ∈ T k, i.1 ∈ F :=
    ⟨Finset.univ.biUnion fun k => (T k).image Prod.fst, fun k i hi =>
      Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ hi⟩⟩
  refine ⟨Algebra.adjoin A (F : Set S), Subalgebra.fg_adjoin_finset F, fun k => ?_⟩
  have hmem : ∀ i ∈ T k, i.1 ∈ Algebra.adjoin A (F : Set S) := fun i hi =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (hF k i hi))
  have hr : z k ∈ LinearMap.range ((Algebra.adjoin A (F : Set S)).val.toLinearMap.rTensor B) := by
    rw [hT k]
    refine Submodule.sum_mem _ fun i hi =>
      ⟨(⟨i.1, hmem i hi⟩ : Algebra.adjoin A (F : Set S)) ⊗ₜ[A] i.2, ?_⟩
    first
      | rfl
      | simp [LinearMap.rTensor_tmul]
  exact LinearMap.mem_range.mp hr

theorem desc_one [Module.Flat A S] (C₀ : Subalgebra A S) (x : C₀ ⊗[A] B)
    (hx : C₀.val.toLinearMap.rTensor B x = 0) :
    ∃ T : Finset S, ∀ (C : Subalgebra A S) (h : C₀ ≤ C), (↑T : Set S) ⊆ ↑C →
      (Subalgebra.inclusion h).toLinearMap.rTensor B x = 0 := by
  classical
  obtain ⟨s, rfl⟩ := TensorProduct.exists_finset x
  have hmn : ∑ i : s, i.1.2 ⊗ₜ[A] ((i.1.1 : C₀) : S) = (0 : B ⊗[A] S) := by
    have h1 := congrArg (TensorProduct.comm A S B) hx
    simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.comm_tmul, map_zero,
      AlgHom.toLinearMap_apply, Subalgebra.coe_val] at h1
    first
      | (rw [← h1]; exact Finset.sum_coe_sort s (fun i => i.2 ⊗ₜ[A] (i.1 : S)))
      | simpa [Finset.sum_coe_sort] using h1
  have hinj : Function.Injective
      ((Submodule.span A (Set.range fun i : s => i.1.2)).subtype.rTensor S) := by
    first
      | exact Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
      | exact Module.Flat.rTensor_preserves_injective_linearMap _ Submodule.injective_subtype
      | exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  obtain ⟨k, a, y, h₁, h₂⟩ := TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective
    (R := A) (m := fun i : s => i.1.2) (n := fun i : s => ((i.1.1 : C₀) : S)) hinj hmn
  refine ⟨Finset.univ.image y, fun C h hT => ?_⟩
  have hy : ∀ j, y j ∈ C := fun j =>
    hT (Finset.mem_coe.mpr (Finset.mem_image_of_mem y (Finset.mem_univ j)))
  have h1' : ∀ i : s, Subalgebra.inclusion h i.1.1 = ∑ j, a i j • (⟨y j, hy j⟩ : C) := by
    intro i
    apply Subtype.val_injective
    rw [Subalgebra.coe_inclusion]
    refine (h₁ i).trans ?_
    first
      | simp
      | (symm
         show C.val (∑ j, a i j • (⟨y j, hy j⟩ : C)) = _
         rw [map_sum]
         exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; rfl)
  have hz := TensorProduct.sum_tmul_eq_zero_of_vanishesTrivially (R := A)
    (m := fun i : s => i.1.2) (n := fun i : s => Subalgebra.inclusion h i.1.1)
    ⟨k, a, fun j => ⟨y j, hy j⟩, h1', h₂⟩
  have h3 := congrArg (TensorProduct.comm A B C) hz
  simp only [map_sum, TensorProduct.comm_tmul, map_zero] at h3
  rw [map_sum, ← Finset.sum_coe_sort s]
  simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply] using h3

end Mod

section Alg

end Alg

end RamanujanPetersson.EtPBC.Cov

end

end


