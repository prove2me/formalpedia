-- Prove2me | Definitions.Def_RPLib_FX_LisseDual_03
-- name    : RPLib_FX_LisseDual_03
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T04:18:44.642621+00:00
-- url     : https://prove2.me/theorems/0c6f7478-3f15-4aec-99f2-1ce3fc88d97f
-- title:
--   Lisse Poincaré duality on an affine curve over a finite field, library file 03 of 7
-- statement:
--   File 03 of 7 of the lisse duality library for affine curves over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_Lefschetz_ConstExt`: S4-Lefschetz L4a: a function field over its full constant field
--   * `S4.Def_RP_Lefschetz_UnrTower`: S4-Lefschetz L4c (part 1): `K_U` depends only on the integral closure
--   * `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
--   * `S4.Def_RP_PerfectCx_CxAlg`: S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module
--   * `S4.Def_RP_PerfectCx_Alg`: S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free
--   * `S4.Def_RP_LisseDuality_Amb`: S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group
--   * `S4.Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
--   * `S4.Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
--   * `S4.Def_RP_Cone_ResAsm`: S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart
--   * `S4.Def_RP_LisseDuality_VDat`: S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`
--   * `S4.Def_RP_CupDuality_VTr1`: S4-CurveDuality, O9b (Route G at `V`) part 1: local data of `V`'s residue data by transfer
--   * `S4.Def_RP_CupDuality_VTr2`: S4-CurveDuality, O9b (Route G at `V`) part 2: `V`'s residue data by transfer
--   * `S4.Def_RP_CupDuality_VCnt1`: S4-CurveDuality, O9b (Route G at `V`) part 3: the `H²` count at `V` (generic)
--   * `S4.Def_RP_LisseDuality_AmbH2`: S4-CurveDuality O7d-P1d (T3): `H²`-vanishing passes to an open subgroup of finite index
--   * `S4.Def_RP_CupDuality_VFrobA`: S4-CurveDuality, O9b (Route G at `V`) part 5: the Frobenius scalar is a unit, generic form
--   * `S4.Def_RP_CupDuality_VPar`: S4-CurveDuality, O9b (V-free) part 3: the parabolic block from the right kernel and finiteness mod `l`
--   * `S4.Def_RP_LisseDuality_Nat`: S4-CurveDuality O7a: naturality of the cup product in the coefficients
--   * `S4.Def_RP_LisseDuality_Exact`: S4-CurveDuality O7b: exactness of `H¹_c` and `H¹` in the coefficients, and the dévissage chase
--   * `S4.Def_RP_LisseDuality_Dev`: S4-CurveDuality O7c: lisse duality by dévissage from coinduced modules
--   * `S4.Def_RP_LisseDuality_Lam`: S4-CurveDuality O7d-P3b T2+T3: the transfer weights are one unit
--   * `S4.Def_RP_CupDuality_VS3b`: S4-CurveDuality, O9b (Route G at `V`) part 9: the `V`-level inputs in the S3 chart
--   * `S4.Def_RP_CupDuality_VGysF`: S4-CurveDuality, O9b (Route G at `V`) part 4: the right kernel vanishes, generic form
--   * `S4.Def_RP_CupDuality_VPerfG`: S4-CurveDuality, O9b (Route G at `V`) part 7: the parabolic block is perfect, generic form
--
--   **Formalization note.** One file of a library formalizing Poincaré duality for $H^1$ with lisse (finite, twisted) coefficients on an affine curve over a finite field: for a finite $\Lambda$-module $M$ with a continuous action of the geometric fundamental group factoring through a finite unramified quotient, the cochain duality map $\alpha_M : H^1_c(M) \to H^1(M^\vee(1))^\vee$ is bijective. It extends the published flat library for constant coefficients (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); J. S. Milne, Arithmetic Duality Theorems, 2nd ed., BookSurge (2006), Chapter II, §3; P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib
import Definitions.Def_RPLib_F2_027
import Definitions.Def_RPLib_FX_LisseDual_02

/-!
# Poincaré duality with lisse coefficients on an affine curve over a finite field, library file 03 of 7

Declarations of the formalization of Poincaré duality for H¹ with lisse (finite, twisted) coefficients on an
affine curve over a finite field (the cochain duality map `alphaM` is bijective), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_Lefschetz_ConstExt`: S4-Lefschetz L4a: a function field over its full constant field
* `S4.Def_RP_Lefschetz_UnrTower`: S4-Lefschetz L4c (part 1): `K_U` depends only on the integral closure
* `S4.Def_RP_Lefschetz_ShapData`: S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover
* `S4.Def_RP_PerfectCx_CxAlg`: S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module
* `S4.Def_RP_PerfectCx_Alg`: S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free
* `S4.Def_RP_LisseDuality_Amb`: S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group
* `S4.Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
* `S4.Def_RP_PerfectCx_Frob`: S4-PD (5), E3: the Frobenius chain map on the cone complex
* `S4.Def_RP_Cone_ResAsm`: S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart
* `S4.Def_RP_LisseDuality_VDat`: S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`
* `S4.Def_RP_CupDuality_VTr1`: S4-CurveDuality, O9b (Route G at `V`) part 1: local data of `V`'s residue data by transfer
* `S4.Def_RP_CupDuality_VTr2`: S4-CurveDuality, O9b (Route G at `V`) part 2: `V`'s residue data by transfer
* `S4.Def_RP_CupDuality_VCnt1`: S4-CurveDuality, O9b (Route G at `V`) part 3: the `H²` count at `V` (generic)
* `S4.Def_RP_LisseDuality_AmbH2`: S4-CurveDuality O7d-P1d (T3): `H²`-vanishing passes to an open subgroup of finite index
* `S4.Def_RP_CupDuality_VFrobA`: S4-CurveDuality, O9b (Route G at `V`) part 5: the Frobenius scalar is a unit, generic form
* `S4.Def_RP_CupDuality_VPar`: S4-CurveDuality, O9b (V-free) part 3: the parabolic block from the right kernel and finiteness mod `l`
* `S4.Def_RP_LisseDuality_Nat`: S4-CurveDuality O7a: naturality of the cup product in the coefficients
* `S4.Def_RP_LisseDuality_Exact`: S4-CurveDuality O7b: exactness of `H¹_c` and `H¹` in the coefficients, and the dévissage chase
* `S4.Def_RP_LisseDuality_Dev`: S4-CurveDuality O7c: lisse duality by dévissage from coinduced modules
* `S4.Def_RP_LisseDuality_Lam`: S4-CurveDuality O7d-P3b T2+T3: the transfer weights are one unit
* `S4.Def_RP_CupDuality_VS3b`: S4-CurveDuality, O9b (Route G at `V`) part 9: the `V`-level inputs in the S3 chart
* `S4.Def_RP_CupDuality_VGysF`: S4-CurveDuality, O9b (Route G at `V`) part 4: the right kernel vanishes, generic form
* `S4.Def_RP_CupDuality_VPerfG`: S4-CurveDuality, O9b (Route G at `V`) part 7: the parabolic block is perfect, generic form
-/

set_option autoImplicit false

-- ===== S4.Def_RP_Lefschetz_ConstExt =====
section

/-!
# S4-Lefschetz L4a: a function field over its full constant field

Let `E` be a function field over `𝔽_q` in the coordinates of S3-Places (`Algebra 𝔽_q[X] E`, `Algebra 𝔽_q(X) E`,
finite separable over `𝔽_q(X)`), but with an arbitrary constant field. Its full constant field
`k' = constField 𝔽_q E` is finite, `x = X_E` is transcendental over `k'`, and with `k'[X] → E`, `k'(X) → E` given by
`X ↦ X_E` the field `E` is a function field over `k'` (finite separable over `k'(X)`) whose full constant field is `k'`
itself (`constField_eq_bot`). So every covering curve of `U` satisfies the hypotheses of S4-CP4 over its own constant
field (`cp4_constExt`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped nonZeroDivisors

namespace RamanujanPetersson
namespace Lefschetz

open Places CurveCoh GalCover CP4a

noncomputable section

section ConstExt

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

instance finite_Kc : Finite (Kc Fq E) := Module.finite_of_finite Fq

instance fintype_Kc : Fintype (Kc Fq E) := Fintype.ofFinite _

end ConstExt

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_UnrTower =====
section

/-!
# S4-Lefschetz L4c (part 1): `K_U` depends only on the integral closure

`IsUnramifiedSub A K L` asks that the inertia groups of `Gal(L/K)` on the integral closure of `A` in `L` vanish.
If `R → S → K` is a tower with `S` integral over `R`, the integral closures of `R` and `S` in `L` are the same
subring of `L` (as `Gal(L/K)`-rings), so `unramSet S K = unramSet R K` and `maxUnram S K = maxUnram R K`.
Applications: `maxUnram (Rfin 𝔽_q F) F = maxUnram 𝔽_q[X] F`, and for a covering function field `E` with full
constant field `k'` (L4a) `maxUnram (Rfin k' E) E = maxUnram 𝔽_q[X] E` (`k'[X]` is integral over `𝔽_q[X]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover

noncomputable section

/-! ### Inertia transport along an equivariant ring isomorphism -/

section InertiaTransport

variable {G B B' : Type} [Group G] [CommRing B] [CommRing B'] [MulSemiringAction G B]
  [MulSemiringAction G B']

end InertiaTransport

/-! ### Integral towers `R → S → K` give the same `K_U` -/

section Tower

variable (R S K : Type) [CommRing R] [CommRing S] [Field K] [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] [Algebra.IsIntegral R S]

end Tower

/-! ### Applications: `Rfin`, and `k'[X]` over `𝔽_q[X]` -/

section Apps

variable (Fq : Type) [Field Fq] [Fintype Fq]

variable [DecidableEq (RatFunc Fq)]
variable (E : Type) [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

theorem algPolyPoly_apply (p : Fq[X]) :
    @algebraMap Fq[X] (Kc Fq E)[X] _ _ (algPolyPoly Fq E) p = p.map (algebraMap Fq (Kc Fq E)) := rfl

end Apps

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_Lefschetz_ShapData =====
section

/-!
# S4-Lefschetz L4g part 3: Shapiro boundary data for a finite subcover

Generic part (`ShapGen`): two pro-charts with boundary data `D` (of `V`) and `D'` (of `U`), an isomorphism
`f : proChart(V) ≃+* proChart(U)` equivariant along an injective `r : π₁(U) →* π₁(V)` with `r⁻¹(Γ) = Γ_U`, and
"stabiliser in `Γ` ⇒ inertia" on `V`. Then `gπ`, `gxT` (from `D.cover`), `gJ` satisfy the three Shapiro
hypotheses `InertiaLift`, `DCover`, `DDisj` of `CurveCoh_ShapiroCone` for `H = range r`.

Concrete part (`ShapE`): `V = K`, `U = E ⊆ K_U` over `k' = Kc 𝔽_q E`, `f = chartE.symm`, `r = thetaE`:
`thetaE_mem_pi1geo_iff`, `thetaE_injective`, `stab_mem_inertia_K`, the objects `bdPiE`, `bdxE`, `bdJE` and
`shap_inertiaLift`, `shap_dCover`, `shap_dDisj`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped Pointwise

namespace RamanujanPetersson
namespace Lefschetz

open Places GalCover CurveCoh CP4a

noncomputable section

section ShapGen

variable {A K R0 : Type} [CommRing A] [Field K] [Algebra A K] [CommRing R0] [Algebra R0 K]
  [Algebra R0 (maxUnram A K)] [IsScalarTower R0 K (maxUnram A K)]
variable {A' K' R0' : Type} [CommRing A'] [Field K'] [Algebra A' K'] [CommRing R0'] [Algebra R0' K']
  [Algebra R0' (maxUnram A' K')] [IsScalarTower R0' K' (maxUnram A' K')]

variable {q q' : ℕ} {S T : Type} (D : BdryData A K q R0 S) (D' : BdryData A' K' q' R0' T)
  (f : proChart A K R0 ≃+* proChart A' K' R0')
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime A K R0 Q) (hD'B : ∀ Q, D'.B Q ↔ IsBdryPrime A' K' R0' Q)

variable (r : Pi1 A' K' →* Pi1 A K) (hf : ∀ σ x, f (r σ • x) = σ • f x) (hr : Function.Injective r)
  (hgeo : ∀ σ, r σ ∈ pi1geo A K q ↔ σ ∈ pi1geo A' K' q')
  (hstab : ∀ Q, IsBdryPrime A K R0 Q → ∀ σ ∈ pi1geo A K q, σ • Q = Q → σ ∈ Q.inertia (Pi1 A K))

end ShapGen

section ShapE

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (K : Type) [Field K] [Algebra Fq K] [Algebra Fq[X] K] [Algebra (RatFunc Fq) K]
  [IsScalarTower Fq[X] (RatFunc Fq) K] [IsScalarTower Fq Fq[X] K] [FunctionField Fq K]
  [Algebra.IsSeparable (RatFunc Fq) K]
variable (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] [Algebra.IsSeparable K E]
  (hE : E ≤ maxUnram Fq[X] K)

variable {p e : ℕ} [Fact p.Prime] [CharP K p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option synthInstance.maxHeartbeats 400000 in
/-- On `K`: an element of `π₁^geo` stabilising a boundary prime lies in its inertia. -/
theorem stab_mem_inertia_K (Q : Ideal (proChart (Rfin Fq K) K (Rinf Fq K)))
    (hQ : IsBdryPrime (Rfin Fq K) K (Rinf Fq K) Q) (σ : Pi1 (Rfin Fq K) K)
    (hσ : σ ∈ pi1geo (Rfin Fq K) K (Fintype.card Fq)) (hfix : σ • Q = Q) :
    σ ∈ Ideal.inertia (α := proChart (Rfin Fq K) K (Rinf Fq K)) (Pi1 (Rfin Fq K) K) Q := by
  have := hQ.1
  obtain ⟨hfin, hcard⟩ := good_inf hq Q hQ
  have := hfin
  rw [hq] at hσ
  exact Residue.stab_mem_inertia (p := p) he (exists_zeta_level (Fq := Fq) (F := K) he) hcard hσ hfix

end ShapE

end

end Lefschetz
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_CxAlg =====
section

/-!
# S4-PD (5), E3 algebra: products, coinvariants of products, and the right regular module

* `repPi`: the pointwise representation on a dependent product; `isProj_prod`, `isProj_pi`;
* `coinvProd`, `coinvPi`: `((P × Q) ⊗ M)_G ≃ (P ⊗ M)_G × (Q ⊗ M)_G` and the same for finite products;
* `rRep`: `Gf` acting on `k[Gf]` by right multiplication by `h⁻¹`; `isProj_rRep`; balancedness `mk_mul_tmul`;
  `coinvA : (k[Gf] ⊗ M)_{Gf} ≃ M`, `⟦a ⊗ m⟧ ↦ a · m`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open MonoidAlgebra TensorProduct HattoriStallings Representation

noncomputable section

section Gen

variable {k : Type} [CommRing k] {Gf : Type} [Group Gf]

variable {M : Type} [AddCommGroup M] [Module k M] (τ : Representation k Gf M)

section Prod

variable {P Q : Type} [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]
  (ρ : Representation k Gf P) (σ : Representation k Gf Q)

end Prod

section Pi

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (σ : ∀ i, Representation k Gf (V i))

end Pi

end Gen

section Right

variable (k : Type) [CommRing k] (Gf : Type) [Group Gf]

variable {k Gf}

variable {M : Type} [AddCommGroup M] [Module k M] (τ : Representation k Gf M)

theorem coinvA_mk_tmul (a : MonoidAlgebra k Gf) (m : M) :
    coinvA τ (Coinvariants.mk _ (a ⊗ₜ m)) = τ.asAlgebraHom a m := rfl

end Right

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_PerfectCx_Alg =====
section

/-!
# S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free

`π : G →* Gf` (open kernel, `Gf` finite), `A = Λ[Gf]` (`MonoidAlgebra`) with `G` acting by left multiplication
through `π` (`regRep`), `E = Z¹(Γ; A)` (locally constant cocycles, `S4-CurveCoh`), and `Gf` acting on `E` by right
multiplication by `h⁻¹` on values (`eRep`; the convention of the `S4-HattoriStallings` coinvariants
`(E ⊗ M)_{Gf} = Coinvariants (tprod eRep τ)`).

* `lift_of_values`: under `H2All`, a cocycle with values in a subrepresentation `W` lifts along any equivariant `q`
  onto `W`;
* `free_E`: over a local `Λ` with `𝔪 = (ϖ)`, `ϖⁿ = 0`, `ϖᵐ ≠ 0` (`m < n`), `E` is free (if finite), via
  `free_of_torsion` and the lift along `ϖ • : A → ϖA`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra IsLocalRing

noncomputable section

section Regular

variable (Λ : Type) [CommRing Λ] (Gf : Type) [Group Gf]

end Regular

section Lift

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N) (Γ : Subgroup G)

end Lift

section Cocycles

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)

theorem coe_smul_Z1 (r : Λ) (c : Z1 (regRep Λ π) Γ) (g : Γ) :
    ((r • c : Z1 (regRep Λ π) Γ) : Γ → MonoidAlgebra Λ Gf) g = r • (c : Γ → MonoidAlgebra Λ Gf) g := rfl

end Cocycles

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Amb =====
section

/-!
# S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group

For subgroups `Δ₁ ≤ G₁`, `Δ₂ ≤ G₂`, a continuous isomorphism `e : Δ₁ ≃ₜ* Δ₂` intertwining `ρ₁` and `ρ₂`
(`Intw`) and matching the boundary subgroups (`IntwI`), the cocycle and cohomology groups are transported:
`z1Tr : Z¹(Δ₁, ρ₁) ≃ Z¹(Δ₂, ρ₂)`, `h1Tr`, `z1cTr`, `h1cTr` and (with `infTr` on `Δ ⊓ I s`) `h2kTr` on the cone `H²`.
Used for the ambient change `G ⇝ K·Γ` in the disconnected case of lisse duality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Tr

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] {M : Type} [AddCommGroup M] [Module k M]
  {ρ₁ : Representation k G₁ M} {ρ₂ : Representation k G₂ M} {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂}

variable {e : Δ₁ ≃ₜ* Δ₂}

/-! ## The compactly supported part -/

variable {S : Type} {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

/-! ## The boundary groups and the cone `H²` -/

variable [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

theorem piTr_cx1 (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (hρ₁ : IsOpen (ρ₁.ker : Set G₁))
    (hρ₂ : IsOpen (ρ₂.ker : Set G₂)) (p : Z1 ρ₁ Δ₁ × (S → M)) :
    piTr h hI (cx1 ρ₁ Δ₁ I₁ hρ₁ p) = cx1 ρ₂ Δ₂ I₂ hρ₂ (z1Tr h p.1, p.2) :=
  funext fun s => Subtype.ext (funext fun g => by
    show (cx1 ρ₁ Δ₁ I₁ hρ₁ p s : ↥(Δ₁ ⊓ I₁ s) → M) ((infTr hI s).symm g) =
      (cx1 ρ₂ Δ₂ I₂ hρ₂ (z1Tr h p.1, p.2) s : ↥(Δ₂ ⊓ I₂ s) → M) g
    rw [cx1_apply, cx1_apply, (h.inf hI s).symm g]
    rfl)

/-- The cone `H²` transported along `e`. -/
def h2kTr (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (hρ₁ : IsOpen (ρ₁.ker : Set G₁))
    (hρ₂ : IsOpen (ρ₂.ker : Set G₂)) : H2K ρ₁ Δ₁ I₁ hρ₁ ≃ₗ[k] H2K ρ₂ Δ₂ I₂ hρ₂ :=
  Submodule.Quotient.equiv _ _ (piTr h hI) (by
    have hc : (piTr h hI : _ →ₗ[k] _) ∘ₗ cx1 ρ₁ Δ₁ I₁ hρ₁ =
        cx1 ρ₂ Δ₂ I₂ hρ₂ ∘ₗ ((z1Tr h).prodCongr (LinearEquiv.refl k (S → M)) : _ →ₗ[k] _) :=
      LinearMap.ext fun p => piTr_cx1 h hI hρ₁ hρ₂ p
    rw [← LinearMap.range_comp, hc, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)])

theorem h2kTr_mk (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (hρ₁ : IsOpen (ρ₁.ker : Set G₁))
    (hρ₂ : IsOpen (ρ₂.ker : Set G₂)) (x : (s : S) → Z1 ρ₁ (Δ₁ ⊓ I₁ s)) :
    h2kTr h hI hρ₁ hρ₂ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (piTr h hI x) := rfl

end Tr

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_HattoriStallings_SES =====
section

/-!
# Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules

* `avg ρ σ f = ∑_g σ g ∘ f ∘ ρ g⁻¹` is always equivariant; `IsHigman ρ E ↔ avg ρ ρ E = id`.
* `exists_equivariant_lift`: a projective (Higman) representation lifts equivariantly along
  equivariant surjections.
* `exists_equivariant_splitting`: a short exact sequence with projective quotient splits equivariantly.
* `hs_ses`: additivity of the HS trace on short exact sequences (and the sub is projective).
* `isHigman_of_basis`, `isProj_permRep`: permutation modules of free `G`-sets are projective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.HattoriStallings

open LinearMap

section Avg

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {Q : Type*} [AddCommGroup Q] [Module R Q]
variable {T : Type*} [AddCommGroup T] [Module R T]
variable {ρ : Representation R G P} {σ : Representation R G Q} {τ : Representation R G T}

lemma isHigman_iff_avg (E : P →ₗ[R] P) : IsHigman ρ E ↔ avg ρ ρ E = LinearMap.id := Iff.rfl

end Avg

section SES

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P' : Type*} [AddCommGroup P'] [Module R P'] {P : Type*} [AddCommGroup P] [Module R P]
variable {P'' : Type*} [AddCommGroup P''] [Module R P'']
variable {ρ' : Representation R G P'} {ρ : Representation R G P} {ρ'' : Representation R G P''}

variable [Module.Free R P'] [Module.Finite R P'] [Module.Free R P] [Module.Finite R P]
  [Module.Free R P''] [Module.Finite R P'']

end SES

section Perm

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}

end Perm

end RamanujanPetersson.HattoriStallings


end

-- ===== S4.Def_RP_PerfectCx_Frob =====
section

/-!
# S4-PD (5), E3: the Frobenius chain map on the cone complex

For `x ∈ G` with `x⁻¹ Δ x ⊆ Δ'`, `conjMap ρ x : Z¹(Δ'; M) → Z¹(Δ; M)`, `c ↦ (g ↦ ρ x (c (x⁻¹ g x)))`. For a Frobenius
lift `ψ` normalising `Γ`, a permutation datum `t : S → S`, `h : S → Γ` compatible with the boundary
(`CurveCoh.BdryCompat`), the maps `ρ ψ` (degree 0), `frob1` (degree 1, the `twistc` of `CurveCoh_Pair`) and `frob2`
(degree 2, `e ↦ (s ↦ conjMap (ψ h_s) (e (t s)))`) form a chain endomorphism of the cone complex `K(M)` (`cx0_frob`,
`cx1_frob`), natural in the coefficients (`frob1_natural`, `frob2_natural`). At `ρ = regRep Λ π` the three maps are
`Gf`-equivariant (`frob0_equiv`, `frob1_equiv`, `frob2_equiv`). `triMap` assembles endomorphisms of a `Tri` family.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings

noncomputable section

section Conj

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N)

theorem conjSub_val (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ') (g : Δ) :
    (conjSub x hx g : G) = x⁻¹ * g * x := rfl

end Conj

section Frob

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N)
  (Γ : Subgroup G) [hΓ : Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (t : S → S) (h : S → Γ)

variable (hρ : IsOpen (ρ.ker : Set G))

end Frob

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) [Γ.Normal] {S : Type} (I : S → Subgroup G)
  (ψ : G) (t : S → S) (h : S → Γ)

end Model

section TriMap

variable {R : Type} [CommRing R] {G : Type} [Group G] {V0 V1 V2 : Type} [AddCommGroup V0] [AddCommGroup V1]
  [AddCommGroup V2] [Module R V0] [Module R V1] [Module R V2]

end TriMap

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_Cone_ResAsm =====
section

/-!
# S4-PD E4S arithmetic ResA, part 4: cover points and inertia in the S3 chart

S3 setting (`F / 𝔽_q`, chart `(Rfin, F, Rinf)`), boundary primes `P s` (one per `π₁^geo`-orbit), a finite level
`M ≤ K_U` with `π : π₁ → Gf` (`Gf` finite, `ker π = Gal(K_U/M)`), and `N` prime to `p`.

* `conj_mem_inertia_smul`: `x I(Q) x⁻¹ ⊆ I(x • Q)`; `Inert Q := I(Q)`, `Jt π Q := I(Q) ∩ ker π`.
* `cosQA`, `cosB`, `cosQA_base`: the cover points `x_t • P (sh t)` and the base points (trivial cosets), with the
  cover / disjointness / inertia facts proved for a general chart `(A, K, R0)` (elaboration note: statements in the
  concrete S3 chart never mention `Ideal.inertia` or a generic `[MulAction]` term directly; they go through these
  chart-generic abbreviations, which instantiate cheaply).
* `exists_norm_tau_fin` (level data discharged) is in `Def_RP_Cone_ResAsmFin`.
* The assembly `exists_resDat` is in `Def_RP_Cone_ResAsm2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Conj

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

variable (A K R0) in
/-- The pointwise action of `π₁` on ideals of the pro-chart. -/
abbrev instMA : MulAction (Pi1 A K) (Ideal (proChart A K R0)) := inferInstance

end Conj

section Gen

variable {G Gf : Type} [Group G] [Group Gf] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

end Gen

section CosA

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]
  {Gf : Type} [Group Gf] (π : Pi1 A K →* Gf) (Γ : Subgroup (Pi1 A K)) {S : Type} (I : S → Subgroup (Pi1 A K))
  (P : S → Ideal (proChart A K R0))

end CosA

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

end S3

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_VDat =====
section

/-!
# S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`

For residue data `D : ResDat π Γ I N T` (S4-PD) and `K = ker π`, the cover `V` (ambient group `K`, geometric group
`geoU Γ K = Γ ∩ K`) gets:
* `rdJ D K t = {h ∈ K | x_t⁻¹ h x_t ∈ I (sh t)}` (inertia of `V` at `t`), `rdX D t = x_t ∈ Γ`,
  `rdY D K hK t = y_t = x_t σ_s x_t⁻¹` (normalised generator);
* `inertiaLift_rd`, `dCover_rd`, `dDisj_rd`: the double-coset data of `ShapiroCone` (from `hrep`);
* **`rdConstData`**: `ConstData (σ|K) (Γ ∩ K) (rdJ D K) (rdY D K hK)` (`inj`/`surj` from `LocGen`,
  `resSum` from `hR`, `resOnto` from `hE`);
* `h2Van_geoU`, `isOpen_ker_comp`, **`rdCupHyp`**: `V`'s `CupHyp` from `H²(Γ ∩ K, σ) = 0` at the `G` level.
No connectedness is used here (`hrep` is stated through `Γ.map π`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Gen

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : Subgroup G) {Γ : Subgroup G}

/-- `H²(Γ ∩ K, M) = 0` at the `G` level gives it for `geoU Γ K` inside the ambient group `K`. -/
theorem h2Van_geoU {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ G M)
    (hv : H2Van ρ (Γ ⊓ K) ⊤) : H2Van (ρ.comp K.subtype) (geoU Γ K) ⊤ := by
  intro f hf _ hc
  let φ : geoU Γ K → ↥(Γ ⊓ K) := fun h =>
    ⟨((h : K) : G), Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 h.2, (h : K).2⟩⟩
  let ψ : ↥(Γ ⊓ K) → geoU Γ K := fun g =>
    ⟨⟨g, (Subgroup.mem_inf.1 g.2).2⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 g.2).1⟩
  have hψc : Continuous ψ := (continuous_subtype_val.subtype_mk _).subtype_mk _
  have hφc : Continuous φ := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  obtain ⟨b, hb, -, hbf⟩ := hv (fun p => f (ψ p.1, ψ p.2))
    (hf.comp_continuous ((hψc.comp continuous_fst).prodMk (hψc.comp continuous_snd)))
    (fun _ => Submodule.mem_top) (fun g h j => hc (ψ g) (ψ h) (ψ j))
  exact ⟨fun h => b (φ h), hb.comp_continuous hφc, fun _ => Submodule.mem_top, fun g h => hbf (φ g) (φ h)⟩

end Gen

section RD

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Gf : Type} [Group Gf] {π : G →* Gf} {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S]
  {I : S → Subgroup G} {N : ℕ} {T : Type} [Fintype T] [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (D : ResDat π Γ I N T) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)

/-- `x_t` in `Γ`. -/
def rdX (t : T) : Γ := ⟨D.x t, D.hx t⟩

/-- The inertia of `V` at `t`: `{h ∈ K | x_t⁻¹ h x_t ∈ I (sh t)}`. -/
def rdJ (t : T) : Subgroup K :=
  (I (D.sh t)).comap ((MulAut.conj (D.x t)⁻¹).toMonoidHom.comp K.subtype)

theorem mem_rdJ (t : T) (h : K) : h ∈ rdJ D K t ↔ (D.x t)⁻¹ * (h : G) * D.x t ∈ I (D.sh t) := by
  rw [rdJ, Subgroup.mem_comap]
  show (MulAut.conj (D.x t)⁻¹) (h : G) ∈ I (D.sh t) ↔ _
  rw [MulAut.conj_apply, inv_inv]

theorem inertiaLift_rd : InertiaLift Γ K I (rdJ D K) D.sh (rdX D) := fun t h => mem_rdJ D K t (h : K)

include hK in
theorem dCover_rd : DCover Γ K I D.sh (rdX D) := by
  intro s y
  obtain ⟨t, ⟨hts, hmem⟩, -⟩ := D.hrep s (π y) (Subgroup.mem_map.2 ⟨y, y.2, rfl⟩)
  obtain ⟨g, hg, hgπ⟩ := Subgroup.mem_map.1 hmem
  have hgΓ : g ∈ Γ := (Subgroup.mem_inf.1 hg).1
  have hhK : (y : G) * g⁻¹ * (D.x t)⁻¹ ∈ K := (hK _).2 (by
    rw [map_mul, map_mul, map_inv, map_inv, hgπ]
    group)
  refine ⟨t, hts, ⟨⟨_, hhK⟩, Subgroup.mem_subgroupOf.2
    (Γ.mul_mem (Γ.mul_mem y.2 (Γ.inv_mem hgΓ)) (Γ.inv_mem (D.hx t)))⟩, ⟨g, hgΓ⟩,
    (Subgroup.mem_inf.1 hg).2, ?_⟩
  show (y : G) = (y : G) * g⁻¹ * (D.x t)⁻¹ * D.x t * g
  group

include hK in
theorem dDisj_rd : DDisj Γ K I D.sh (rdX D) := by
  intro t t' htt' h g hg hx
  have hp : π (D.x t) ∈ Γ.map π := Subgroup.mem_map.2 ⟨D.x t, D.hx t, rfl⟩
  obtain ⟨t0, -, hu⟩ := D.hrep (D.sh t) (π (D.x t)) hp
  have h1 : t = t0 := hu t ⟨rfl, by rw [inv_mul_cancel]; exact Subgroup.one_mem _⟩
  have hhπ : π ((h : K) : G) = 1 := (hK _).1 (h : K).2
  have hx' : D.x t = ((h : K) : G) * D.x t' * g := hx
  have h2 : t' = t0 := hu t' ⟨htt'.symm, by
    rw [hx', map_mul, map_mul, hhπ, one_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_inf.2 ⟨g.2, hg⟩, rfl⟩⟩
  rw [h1, h2]

include hK in
theorem rdY_mem (t : T) : D.x t * D.σ (D.sh t) * (D.x t)⁻¹ ∈ K ∧
    D.x t * D.σ (D.sh t) * (D.x t)⁻¹ ∈ Γ ∧
    (D.x t)⁻¹ * (D.x t * D.σ (D.sh t) * (D.x t)⁻¹) * D.x t ∈ I (D.sh t) := by
  rw [← D.hy t]
  obtain ⟨hΓ, hπ⟩ := (D.hΓH _).1 (D.y t).2
  refine ⟨(hK _).2 hπ, hΓ, ?_⟩
  rw [D.hy t]
  have e : (D.x t)⁻¹ * (D.x t * D.σ (D.sh t) * (D.x t)⁻¹) * D.x t = D.σ (D.sh t) := by group
  rw [e]
  exact (Subgroup.mem_inf.1 (D.hσ (D.sh t))).2

/-- `y_t = x_t σ_s x_t⁻¹`, the normalised inertia generator of `V` at `t`. -/
def rdY (t : T) : ↥(geoU Γ K ⊓ rdJ D K t) :=
  ⟨⟨D.x t * D.σ (D.sh t) * (D.x t)⁻¹, (rdY_mem D K hK t).1⟩, Subgroup.mem_inf.2
    ⟨Subgroup.mem_subgroupOf.2 (rdY_mem D K hK t).2.1, (mem_rdJ D K t _).2 (rdY_mem D K hK t).2.2⟩⟩

/-! ### Conjugation `J_s ≃ geoU Γ K ⊓ rdJ t` -/

include hK in
theorem rdConj_mem (t : T) (j : D.J (D.sh t)) :
    D.x t * (j : G) * (D.x t)⁻¹ ∈ K ∧ D.x t * (j : G) * (D.x t)⁻¹ ∈ Γ ∧
      (D.x t)⁻¹ * (D.x t * (j : G) * (D.x t)⁻¹) * D.x t ∈ I (D.sh t) := by
  obtain ⟨hjΔ, -⟩ := (D.hJ _ _).1 j.2
  obtain ⟨hΓ, hπ⟩ := (D.hΓH _).1 (D.cmem t (D.sh t) j j.2)
  refine ⟨(hK _).2 hπ, hΓ, ?_⟩
  have e : (D.x t)⁻¹ * (D.x t * (j : G) * (D.x t)⁻¹) * D.x t = j := by group
  rw [e]
  exact (Subgroup.mem_inf.1 hjΔ).2

/-- `j ↦ x_t j x_t⁻¹`. -/
def rdConj (t : T) (j : D.J (D.sh t)) : ↥(geoU Γ K ⊓ rdJ D K t) :=
  ⟨⟨_, (rdConj_mem D K hK t j).1⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 (rdConj_mem D K hK t j).2.1,
    (mem_rdJ D K t _).2 (rdConj_mem D K hK t j).2.2⟩⟩

theorem rdConj_cont (t : T) : Continuous (rdConj D K hK t) :=
  (((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _).subtype_mk _

theorem rdConj_mul (t : T) (a b : D.J (D.sh t)) :
    rdConj D K hK t (a * b) = rdConj D K hK t a * rdConj D K hK t b := by
  apply Subtype.ext
  apply Subtype.ext
  show D.x t * ((a : G) * b) * (D.x t)⁻¹ = (D.x t * a * (D.x t)⁻¹) * (D.x t * b * (D.x t)⁻¹)
  group

theorem rdConj_sigma (t : T) : rdConj D K hK t ⟨D.σ (D.sh t), D.hσJ (D.sh t)⟩ = rdY D K hK t := rfl

include hK in
theorem rdUnc_mem (t : T) (h : ↥(geoU Γ K ⊓ rdJ D K t)) :
    (D.x t)⁻¹ * ((h : K) : G) * D.x t ∈ D.J (D.sh t) := by
  have h1 : ((h : K) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 h.2).1
  have h2 := (mem_rdJ D K t (h : K)).1 (Subgroup.mem_inf.1 h.2).2
  have h3 : π ((h : K) : G) = 1 := (hK _).1 (h : K).2
  refine (D.hJ _ _).2 ⟨Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (D.hx t)) h1) (D.hx t), h2⟩, ?_⟩
  rw [map_mul, map_mul, map_inv, h3]
  group

/-- `h ↦ x_t⁻¹ h x_t`. -/
def rdUnc (t : T) (h : ↥(geoU Γ K ⊓ rdJ D K t)) : D.J (D.sh t) := ⟨_, rdUnc_mem D K hK t h⟩

theorem rdUnc_cont (t : T) : Continuous (rdUnc D K hK t) :=
  ((continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul continuous_const).subtype_mk _

theorem rdUnc_mul (t : T) (a b : ↥(geoU Γ K ⊓ rdJ D K t)) :
    rdUnc D K hK t (a * b) = rdUnc D K hK t a * rdUnc D K hK t b := by
  apply Subtype.ext
  show (D.x t)⁻¹ * (((a : K) : G) * ((b : K) : G)) * D.x t =
    ((D.x t)⁻¹ * ((a : K) : G) * D.x t) * ((D.x t)⁻¹ * ((b : K) : G) * D.x t)
  group

theorem rdUnc_rdY (t : T) : rdUnc D K hK t (rdY D K hK t) = ⟨D.σ (D.sh t), D.hσJ (D.sh t)⟩ := by
  apply Subtype.ext
  show (D.x t)⁻¹ * (D.x t * D.σ (D.sh t) * (D.x t)⁻¹) * D.x t = D.σ (D.sh t)
  group

theorem rdConj_rdUnc (t : T) (h : ↥(geoU Γ K ⊓ rdJ D K t)) : rdConj D K hK t (rdUnc D K hK t h) = h := by
  apply Subtype.ext
  apply Subtype.ext
  show D.x t * ((D.x t)⁻¹ * ((h : K) : G) * D.x t) * (D.x t)⁻¹ = ((h : K) : G)
  group

/-! ### `Γ_H ≃ geoU Γ K` -/

/-- `Γ_H → geoU Γ K`. -/
def rdToV (g : D.ΓH) : geoU Γ K :=
  ⟨⟨(g : G), (hK _).2 ((D.hΓH _).1 g.2).2⟩, Subgroup.mem_subgroupOf.2 ((D.hΓH _).1 g.2).1⟩

theorem rdToV_cont : Continuous (rdToV D K hK) := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem rdToV_mul (a b : D.ΓH) : rdToV D K hK (a * b) = rdToV D K hK a * rdToV D K hK b := rfl

/-- `geoU Γ K → Γ_H`. -/
def rdFromV (h : geoU Γ K) : D.ΓH :=
  ⟨((h : K) : G), (D.hΓH _).2 ⟨Subgroup.mem_subgroupOf.1 h.2, (hK _).1 (h : K).2⟩⟩

theorem rdFromV_cont : Continuous (rdFromV D K hK) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem rdFromV_mul (a b : geoU Γ K) : rdFromV D K hK (a * b) = rdFromV D K hK a * rdFromV D K hK b := rfl

/-! ### The constant data of `V` -/

variable (σ : Representation Λ G Λ) (htriv : ∀ (g : Γ) (x : Λ), σ g x = x)

include htriv in
theorem rd_triv_inf (t : T) (g : ↥(geoU Γ K ⊓ rdJ D K t)) (x : Λ) : (σ.comp K.subtype) (g : K) x = x :=
  htriv ⟨((g : K) : G), Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 g.2).1⟩ x

variable [NeZero N] (hN : (N : Λ) = 0)

include htriv hN in
theorem rd_inj (t : T) (e : Z1 (σ.comp K.subtype) (geoU Γ K ⊓ rdJ D K t))
    (h0 : (e : ↥(geoU Γ K ⊓ rdJ D K t) → Λ) (rdY D K hK t) = 0) : e = 0 := by
  have hlc := ((mem_Z1 _ _ _).1 e.2).1
  have hψ : ∀ j, (e : ↥(geoU Γ K ⊓ rdJ D K t) → Λ) (rdConj D K hK t j) = 0 := fun j =>
    (D.hloc (D.sh t)).eq_zero (rd_hM hN) (fun j => (e : ↥(geoU Γ K ⊓ rdJ D K t) → Λ) (rdConj D K hK t j))
      (hlc.comp_continuous (rdConj_cont D K hK t))
      (fun a b => by
        simp only [rdConj_mul]
        exact z1_add_of_triv _ _ (rd_triv_inf D K σ htriv t) e _ _)
      (by
        show (e : ↥(geoU Γ K ⊓ rdJ D K t) → Λ) (rdConj D K hK t ⟨D.σ (D.sh t), D.hσJ (D.sh t)⟩) = 0
        rw [rdConj_sigma]
        exact h0) j
  refine Subtype.ext (funext fun h => ?_)
  have h1 := hψ (rdUnc D K hK t h)
  rw [rdConj_rdUnc] at h1
  exact h1

include htriv hN in
theorem rd_surj (t : T) (a : Λ) : ∃ e : Z1 (σ.comp K.subtype) (geoU Γ K ⊓ rdJ D K t),
    (e : ↥(geoU Γ K ⊓ rdJ D K t) → Λ) (rdY D K hK t) = a := by
  obtain ⟨θ, hθc, hθ, hθ1, -, -⟩ := D.hloc (D.sh t)
  refine ⟨⟨fun h => zlift Λ N hN (θ (rdUnc D K hK t h)) * a, (mem_Z1 _ _ _).2
    ⟨((hθc.comp_continuous (rdUnc_cont D K hK t)).comp (zlift Λ N hN)).comp (· * a), fun g h => ?_⟩⟩, ?_⟩
  · show zlift Λ N hN (θ (rdUnc D K hK t (g * h))) * a =
      zlift Λ N hN (θ (rdUnc D K hK t g)) * a + (σ.comp K.subtype) (g : K) (zlift Λ N hN (θ (rdUnc D K hK t h)) * a)
    rw [rd_triv_inf D K σ htriv t g, rdUnc_mul, hθ, map_add, add_mul]
  · show zlift Λ N hN (θ (rdUnc D K hK t (rdY D K hK t))) * a = a
    rw [rdUnc_rdY]
    have e1 : θ ⟨D.σ (D.sh t), D.hσJ (D.sh t)⟩ = 1 := hθ1
    rw [e1, zlift_one, one_mul]

end RD

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VTr1 =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 1: local data of `V`'s residue data by transfer

Setting (session 49 design, "V-count"): `RD : ResDat π Γ I N T` is the residue data of the cover `V`
(`K = ker π`, boundary points `t : T` over `RD.sh t` with conjugators `x_t`), and `D2 : ResDat π₂ Γ I N T₂` is residue
data of a finer cover (`ker π₂ ≤ K`). On `V` (ambient group `K`, geometric group `geoU Γ K`, inertia `rdJ RD K`,
boundary `T`) with `π_V = π₂|_K`:
* `trJ t = geoU Γ K ⊓ rdJ RD K t ⊓ ker π_V`, which is `x_t J₂(sh t) x_t⁻¹` (`mem_trJ_iff`);
* `trSig t = x_t σ₂(sh t) x_t⁻¹` and its `LocGen` (`trLoc`), from `locGen_conjK` (transport of `LocGen` along
  conjugation by `x` into a subgroup `K`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh PerfectCx

noncomputable section

section LocConj

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K J I' : Subgroup G}
  {JV IV : Subgroup K} {N : ℕ}

/-- **Transport of `LocGen`** along `j ↦ x j x⁻¹` into `K`. -/
theorem locGen_conjK (x : G) (hJV : ∀ g : K, g ∈ JV ↔ x⁻¹ * (g : G) * x ∈ J)
    (hIV : ∀ g : K, g ∈ IV ↔ x⁻¹ * (g : G) * x ∈ I') (hJK : ∀ j ∈ J, x * j * x⁻¹ ∈ K) {τ : J}
    (h : LocGen J I' N τ) (hτ : (⟨x * τ * x⁻¹, hJK _ τ.2⟩ : K) ∈ JV) :
    LocGen JV IV N ⟨⟨x * τ * x⁻¹, hJK _ τ.2⟩, hτ⟩ := by
  obtain ⟨θ, hθc, hθ, hθ1, hθI, hgen⟩ := h
  let unc : JV → J := fun j => ⟨x⁻¹ * ((j : K) : G) * x, (hJV _).1 j.2⟩
  have hunc : Continuous unc :=
    ((continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)).mul continuous_const).subtype_mk _
  have huncm : ∀ a b, unc (a * b) = unc a * unc b := fun a b => Subtype.ext (by
    show x⁻¹ * (((a : K) : G) * ((b : K) : G)) * x = (x⁻¹ * ((a : K) : G) * x) * (x⁻¹ * ((b : K) : G) * x)
    group)
  have hcnj : ∀ j : J, (⟨x * j * x⁻¹, hJK _ j.2⟩ : K) ∈ JV := fun j => (hJV _).2 (by
    show x⁻¹ * (x * (j : G) * x⁻¹) * x ∈ J
    have e : x⁻¹ * (x * (j : G) * x⁻¹) * x = j := by group
    rw [e]
    exact j.2)
  let cnj : J → JV := fun j => ⟨⟨x * j * x⁻¹, hJK _ j.2⟩, hcnj j⟩
  have hcnjc : Continuous cnj :=
    (((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _).subtype_mk _
  have hcnjm : ∀ a b, cnj (a * b) = cnj a * cnj b := fun a b => Subtype.ext (Subtype.ext (by
    show x * ((a : G) * (b : G)) * x⁻¹ = (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹)
    group))
  have hcu : ∀ j, cnj (unc j) = j := fun j => Subtype.ext (Subtype.ext (by
    show x * (x⁻¹ * ((j : K) : G) * x) * x⁻¹ = ((j : K) : G)
    group))
  refine ⟨fun j => θ (unc j), hθc.comp_continuous hunc, fun a b => by
    show θ (unc (a * b)) = θ (unc a) + θ (unc b)
    rw [huncm, hθ], ?_, ?_, ?_⟩
  · have e : unc ⟨⟨x * τ * x⁻¹, hJK _ τ.2⟩, hτ⟩ = τ := Subtype.ext (by
      show x⁻¹ * (x * (τ : G) * x⁻¹) * x = τ
      group)
    show θ (unc _) = 1
    rw [e, hθ1]
  · intro g hg σ hσ hσ'
    have hg' : x⁻¹ * (g : G) * x ∈ I' := (hIV g).1 hg
    have hs : x⁻¹ * ((σ : K) : G) * x ∈ J := (hJV σ).1 hσ
    have hs' : (x⁻¹ * (g : G) * x)⁻¹ * (x⁻¹ * ((σ : K) : G) * x) * (x⁻¹ * (g : G) * x) ∈ J := by
      have e : (x⁻¹ * (g : G) * x)⁻¹ * (x⁻¹ * ((σ : K) : G) * x) * (x⁻¹ * (g : G) * x) =
          x⁻¹ * ((g⁻¹ * σ * g : K) : G) * x := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact (hJV _).1 hσ'
    have := hθI _ hg' _ hs hs'
    have e1 : unc ⟨g⁻¹ * σ * g, hσ'⟩ = ⟨_, hs'⟩ := Subtype.ext (by
      show x⁻¹ * ((g⁻¹ * σ * g : K) : G) * x =
        (x⁻¹ * (g : G) * x)⁻¹ * (x⁻¹ * ((σ : K) : G) * x) * (x⁻¹ * (g : G) * x)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group)
    have e2 : unc ⟨σ, hσ⟩ = ⟨_, hs⟩ := rfl
    show θ (unc ⟨g⁻¹ * σ * g, hσ'⟩) = θ (unc ⟨σ, hσ⟩)
    rw [e1, e2]
    exact this
  · intro χ hχc hχ σ
    have h1 : χ (cnj (unc σ)) = χ (cnj τ) * θ (unc σ) :=
      hgen (fun j => χ (cnj j)) (hχc.comp_continuous hcnjc) (fun a b => by
        show χ (cnj (a * b)) = χ (cnj a) + χ (cnj b)
        rw [hcnjm, hχ]) (unc σ)
    have e : cnj τ = ⟨⟨x * τ * x⁻¹, hJK _ τ.2⟩, hτ⟩ := rfl
    show χ σ = χ ⟨⟨x * τ * x⁻¹, hJK _ τ.2⟩, hτ⟩ * θ (unc σ)
    rw [← e, ← h1, hcu]

end LocConj

section Tr

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Gf Gf2 : Type} [Group Gf] [Group Gf2] {π : G →* Gf} {π2 : G →* Gf2} {Γ : Subgroup G} [Γ.Normal]
  {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T T2 : Type} [Fintype T] [Fintype T2]
  [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (RD : ResDat π Γ I N T) (D2 : ResDat π2 Γ I N T2) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)
  (hK2 : ∀ g, π2 g = 1 → g ∈ K)

/-- The local group of the finer cover at `t`: `geoU Γ K ⊓ rdJ RD K t ⊓ ker π_V`. -/
def trJ (t : T) : Subgroup K := (geoU Γ K ⊓ rdJ RD K t) ⊓ (piV π2 K).ker

theorem mem_trJ (t : T) (g : K) : g ∈ trJ RD K (π2 := π2) t ↔ g ∈ geoU Γ K ⊓ rdJ RD K t ∧ piV π2 K g = 1 := by
  rw [trJ, Subgroup.mem_inf, MonoidHom.mem_ker]

theorem mem_trJ_iff (t : T) (g : K) :
    g ∈ trJ RD K (π2 := π2) t ↔ (RD.x t)⁻¹ * (g : G) * RD.x t ∈ D2.J (RD.sh t) := by
  rw [mem_trJ, Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_rdJ, piV_apply, D2.hJ, Subgroup.mem_inf]
  have hx := RD.hx t
  constructor
  · rintro ⟨⟨hg, hI⟩, hπ⟩
    refine ⟨⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hx) hg) hx, hI⟩, ?_⟩
    rw [map_mul, map_mul, hπ, mul_one, map_inv, inv_mul_cancel]
  · rintro ⟨⟨hg, hI⟩, hπ⟩
    have e : (g : G) = RD.x t * ((RD.x t)⁻¹ * (g : G) * RD.x t) * (RD.x t)⁻¹ := by group
    refine ⟨⟨?_, hI⟩, ?_⟩
    · rw [e]
      exact Γ.mul_mem (Γ.mul_mem hx hg) (Γ.inv_mem hx)
    · rw [e, map_mul, map_mul, hπ, mul_one, map_inv, mul_inv_cancel]

include hK hK2 in
theorem trSig_mem (t : T) : RD.x t * D2.σ (RD.sh t) * (RD.x t)⁻¹ ∈ K :=
  conj_mem_K K hK hK2 _ (D2.hσπ _)

/-- `x_t σ₂(sh t) x_t⁻¹ ∈ K`. -/
def trSig (t : T) : K := ⟨_, trSig_mem RD D2 K hK hK2 t⟩

theorem trSig_mem_trJ (t : T) : trSig RD D2 K hK hK2 t ∈ trJ RD K (π2 := π2) t := by
  rw [mem_trJ_iff RD D2 K]
  show (RD.x t)⁻¹ * (RD.x t * D2.σ (RD.sh t) * (RD.x t)⁻¹) * RD.x t ∈ D2.J (RD.sh t)
  have e : (RD.x t)⁻¹ * (RD.x t * D2.σ (RD.sh t) * (RD.x t)⁻¹) * RD.x t = D2.σ (RD.sh t) := by group
  rw [e]
  exact (D2.hJ _ _).2 ⟨D2.hσ _, D2.hσπ _⟩

/-- **`LocGen` of the transferred generators.** -/
theorem trLoc (t : T) : LocGen (trJ RD K (π2 := π2) t) (rdJ RD K t) N ⟨trSig RD D2 K hK hK2 t, trSig_mem_trJ RD D2 K hK hK2 t⟩ :=
  locGen_conjK (RD.x t) (mem_trJ_iff RD D2 K t) (mem_rdJ RD K t)
    (fun _j hj => conj_mem_K K hK hK2 _ ((D2.hJ _ _).1 hj).2) (D2.hloc (RD.sh t)) _

end Tr

end

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_CupDuality_VTr2 =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 2: `V`'s residue data by transfer

Setting as in part 1: `RD : ResDat π Γ I N T` (the cover `V`, `K = ker π`), `D2 : ResDat π₂ Γ I N T₂` (a finer cover,
`ker π₂ ≤ K`). For `t₂ : T₂`:
* `shV t₂ : T` is the unique point of `V` over `sh₂ t₂` with `π(x_t)⁻¹ π(x₂ t₂) ∈ π(Γ ⊓ I s)` (`RD.hrep`);
* `iV t₂ ∈ Γ ⊓ I s` with `π(i) = π(x_t)⁻¹ π(x₂)`, and `xV t₂ = x₂ i⁻¹ x_t⁻¹ ∈ K ∩ Γ` (so `x₂ = κ x_t i`, `x2_eq`);
* `yV t₂ = κ · trSig t · κ⁻¹` (it differs from `y₂ t₂` by conjugation with `i ∈ I s` inside `J₂ s`: `chi_up_yV`).
**`trResDat`**: the `ResDat (piV π₂ K) (geoU Γ K) (rdJ RD K) N T₂` of `V` (over `G := K`), with `hrep` (`hrepV`,
double cosets), `hR`/`hE` (`hRV`/`hEV`, from `D2.hR`/`D2.hE` through `Γ_H(V) ≅ D2.ΓH`: `upV`, `downV`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh PerfectCx

noncomputable section

section Tr2

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Gf Gf2 : Type} [Group Gf] [Group Gf2] {π : G →* Gf} {π2 : G →* Gf2} {Γ : Subgroup G} [Γ.Normal]
  {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T T2 : Type} [Fintype T] [Fintype T2]
  [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (RD : ResDat π Γ I N T) (D2 : ResDat π2 Γ I N T2) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)
  (hK2 : ∀ g, π2 g = 1 → g ∈ K)

theorem shV_ex (t2 : T2) : ∃! t, RD.sh t = D2.sh t2 ∧
    (π (RD.x t))⁻¹ * π (D2.x t2) ∈ (Γ ⊓ I (D2.sh t2)).map π :=
  RD.hrep _ _ (Subgroup.mem_map_of_mem π (D2.hx t2))

/-- The point of `V` under `t₂`. -/
def shV (t2 : T2) : T := (shV_ex RD D2 t2).exists.choose

theorem shV_spec (t2 : T2) : RD.sh (shV RD D2 t2) = D2.sh t2 ∧
    (π (RD.x (shV RD D2 t2)))⁻¹ * π (D2.x t2) ∈ (Γ ⊓ I (D2.sh t2)).map π :=
  (shV_ex RD D2 t2).exists.choose_spec

theorem shV_eq (t2 : T2) (t : T) (h : RD.sh t = D2.sh t2 ∧
    (π (RD.x t))⁻¹ * π (D2.x t2) ∈ (Γ ⊓ I (D2.sh t2)).map π) : shV RD D2 t2 = t :=
  (shV_ex RD D2 t2).unique (shV_spec RD D2 t2) h

theorem iV_ex (t2 : T2) : ∃ i, i ∈ Γ ⊓ I (D2.sh t2) ∧ π i = (π (RD.x (shV RD D2 t2)))⁻¹ * π (D2.x t2) :=
  Subgroup.mem_map.1 (shV_spec RD D2 t2).2

/-- `i ∈ Γ ⊓ I s` with `x₂ = κ x_t i`. -/
def iV (t2 : T2) : G := (iV_ex RD D2 t2).choose

theorem iV_mem (t2 : T2) : iV RD D2 t2 ∈ Γ ⊓ I (D2.sh t2) := (iV_ex RD D2 t2).choose_spec.1

theorem iV_pi (t2 : T2) : π (iV RD D2 t2) = (π (RD.x (shV RD D2 t2)))⁻¹ * π (D2.x t2) :=
  (iV_ex RD D2 t2).choose_spec.2

include hK in
theorem xV_mem (t2 : T2) : D2.x t2 * (iV RD D2 t2)⁻¹ * (RD.x (shV RD D2 t2))⁻¹ ∈ K := by
  rw [hK]
  simp only [map_mul, map_inv, iV_pi]
  group

/-- `κ = x₂ i⁻¹ x_t⁻¹ ∈ K`. -/
def xV (t2 : T2) : K := ⟨_, xV_mem RD D2 K hK t2⟩

theorem xV_coe (t2 : T2) :
    (xV RD D2 K hK t2 : G) = D2.x t2 * (iV RD D2 t2)⁻¹ * (RD.x (shV RD D2 t2))⁻¹ := rfl

theorem xV_geo (t2 : T2) : xV RD D2 K hK t2 ∈ geoU Γ K :=
  Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.mul_mem (D2.hx t2)
    (Γ.inv_mem (Subgroup.mem_inf.1 (iV_mem RD D2 t2)).1)) (Γ.inv_mem (RD.hx _)))

theorem x2_eq (t2 : T2) : D2.x t2 = (xV RD D2 K hK t2 : G) * RD.x (shV RD D2 t2) * iV RD D2 t2 := by
  rw [xV_coe]
  group

include hK hK2 in
theorem yV_mem (t2 : T2) : xV RD D2 K hK t2 * trSig RD D2 K hK hK2 (shV RD D2 t2) * (xV RD D2 K hK t2)⁻¹ ∈
    trΓH K (Γ := Γ) (π2 := π2) := by
  have hs := (mem_trJ RD K _ _).1 (trSig_mem_trJ RD D2 K hK hK2 (shV RD D2 t2))
  have hx := xV_geo RD D2 K hK t2
  rw [mem_trΓH]
  refine ⟨(geoU Γ K).mul_mem ((geoU Γ K).mul_mem hx (Subgroup.mem_inf.1 hs.1).1) ((geoU Γ K).inv_mem hx), ?_⟩
  rw [map_mul, map_mul, map_inv, hs.2, mul_one, mul_inv_cancel]

/-- `y_V t₂ = κ · trSig (shV t₂) · κ⁻¹ ∈ Γ_H(V)`. -/
def yV (t2 : T2) : trΓH K (Γ := Γ) (π2 := π2) := ⟨_, yV_mem RD D2 K hK hK2 t2⟩

include hK2 in
/-- **`hrep` of `V`** (double cosets). -/
theorem hrepV (t : T) (p : Gf2) (hp : p ∈ (geoU Γ K).map (piV π2 K)) :
    ∃! t2, shV RD D2 t2 = t ∧
      (piV π2 K (xV RD D2 K hK t2))⁻¹ * p ∈ (geoU Γ K ⊓ rdJ RD K t).map (piV π2 K) := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hp
  have hkΓ : (k : G) ∈ Γ := Subgroup.mem_subgroupOf.1 hk
  have hkπ : π (k : G) = 1 := (hK _).1 k.2
  obtain ⟨t2, ⟨hsh, hmem⟩, hu⟩ := D2.hrep (RD.sh t) _
    (Subgroup.mem_map_of_mem π2 (Γ.mul_mem hkΓ (RD.hx t)))
  obtain ⟨j, hj, hjπ⟩ := Subgroup.mem_map.1 hmem
  have hjπ' : π2 j = (π2 (D2.x t2))⁻¹ * (π2 (k : G) * π2 (RD.x t)) := by rw [hjπ, map_mul]
  have hjπ1 : π j = (π (D2.x t2))⁻¹ * π (RD.x t) := by
    rw [pi_eq_of_pi2 K hK hK2 j ((D2.x t2)⁻¹ * ((k : G) * RD.x t)) (by
      rw [hjπ']
      simp only [map_mul, map_inv])]
    simp only [map_mul, map_inv, hkπ, one_mul]
  have hst : shV RD D2 t2 = t := shV_eq RD D2 t2 t ⟨hsh.symm, Subgroup.mem_map.2 ⟨j⁻¹, by
    rw [hsh]
    exact (Γ ⊓ I (RD.sh t)).inv_mem hj, by rw [map_inv, hjπ1, mul_inv_rev, inv_inv]⟩⟩
  refine ⟨t2, ⟨hst, ?_⟩, ?_⟩
  · subst hst
    have hi : iV RD D2 t2 ∈ Γ ⊓ I (RD.sh (shV RD D2 t2)) := by
      rw [← hsh]
      exact iV_mem RD D2 t2
    have hiΓ := (Subgroup.mem_inf.1 hi).1
    have hiI := (Subgroup.mem_inf.1 hi).2
    have hjΓ := (Subgroup.mem_inf.1 hj).1
    have hjI := (Subgroup.mem_inf.1 hj).2
    have hx := RD.hx (shV RD D2 t2)
    have heK : RD.x (shV RD D2 t2) * iV RD D2 t2 * j * (RD.x (shV RD D2 t2))⁻¹ ∈ K := (hK _).2 (by
      simp only [map_mul, map_inv, iV_pi, hjπ1]
      group)
    refine Subgroup.mem_map.2 ⟨⟨_, heK⟩, Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2
      (Γ.mul_mem (Γ.mul_mem (Γ.mul_mem hx hiΓ) hjΓ) (Γ.inv_mem hx)), (mem_rdJ RD K _ _).2 ?_⟩, ?_⟩
    · show (RD.x (shV RD D2 t2))⁻¹ * (RD.x (shV RD D2 t2) * iV RD D2 t2 * j * (RD.x (shV RD D2 t2))⁻¹) *
        RD.x (shV RD D2 t2) ∈ I (RD.sh (shV RD D2 t2))
      have e : (RD.x (shV RD D2 t2))⁻¹ * (RD.x (shV RD D2 t2) * iV RD D2 t2 * j * (RD.x (shV RD D2 t2))⁻¹) *
          RD.x (shV RD D2 t2) = iV RD D2 t2 * j := by group
      rw [e]
      exact (I _).mul_mem hiI hjI
    · show π2 (RD.x (shV RD D2 t2) * iV RD D2 t2 * j * (RD.x (shV RD D2 t2))⁻¹) =
        (π2 (D2.x t2 * (iV RD D2 t2)⁻¹ * (RD.x (shV RD D2 t2))⁻¹))⁻¹ * π2 (k : G)
      simp only [map_mul, map_inv, hjπ']
      group
  · rintro t2' ⟨h1, h2⟩
    subst h1
    obtain ⟨e', he', he'π⟩ := Subgroup.mem_map.1 h2
    have hsp := (shV_spec RD D2 t2').1
    have hi' : iV RD D2 t2' ∈ Γ ⊓ I (RD.sh (shV RD D2 t2')) := by
      rw [hsp]
      exact iV_mem RD D2 t2'
    have he'Γ : (e' : G) ∈ Γ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 he').1
    have he'I := (mem_rdJ RD K _ _).1 (Subgroup.mem_inf.1 he').2
    have hx := RD.hx (shV RD D2 t2')
    refine hu t2' ⟨hsp.symm, Subgroup.mem_map.2 ⟨(iV RD D2 t2')⁻¹ * ((RD.x (shV RD D2 t2'))⁻¹ * (e' : G) *
      RD.x (shV RD D2 t2')), Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.inv_mem (Subgroup.mem_inf.1 hi').1)
      (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hx) he'Γ) hx),
      (I _).mul_mem ((I _).inv_mem (Subgroup.mem_inf.1 hi').2) he'I⟩, ?_⟩⟩
    have he'π' : π2 (e' : G) =
        (π2 (D2.x t2' * (iV RD D2 t2')⁻¹ * (RD.x (shV RD D2 t2'))⁻¹))⁻¹ * π2 (k : G) := he'π
    simp only [map_mul, map_inv] at he'π' ⊢
    rw [he'π']
    group

/-- A point of `T` (for the field `s0`). -/
def s0V : T := (RD.hrep RD.s0 1 (Subgroup.one_mem _)).exists.choose

/-! ### `Γ_H(V) ≅ D2.ΓH` and the residue conditions -/

theorem upV_mem (g : trΓH K (Γ := Γ) (π2 := π2)) : ((g : K) : G) ∈ D2.ΓH :=
  (D2.hΓH _).2 ⟨Subgroup.mem_subgroupOf.1 ((mem_trΓH K (g : K)).1 g.2).1, ((mem_trΓH K (g : K)).1 g.2).2⟩

/-- `Γ_H(V) → D2.ΓH` (same elements). -/
def upV (g : trΓH K (Γ := Γ) (π2 := π2)) : D2.ΓH := ⟨_, upV_mem D2 K g⟩

theorem upV_cont : Continuous (upV D2 K (Γ := Γ)) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- `D2.ΓH → Γ_H(V)` (same elements). -/
def downV (g : D2.ΓH) : trΓH K (Γ := Γ) (π2 := π2) :=
  ⟨⟨g, hK2 _ ((D2.hΓH _).1 g.2).2⟩, (mem_trΓH K _).2
    ⟨Subgroup.mem_subgroupOf.2 ((D2.hΓH _).1 g.2).1, ((D2.hΓH _).1 g.2).2⟩⟩

theorem downV_cont : Continuous (downV D2 K hK2) :=
  (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem downV_mul (a b : D2.ΓH) : downV D2 K hK2 (a * b) = downV D2 K hK2 a * downV D2 K hK2 b := rfl

/-- **`y_V` and `y₂` agree under every locally constant hom on `D2.ΓH`** (conjugation by `i ∈ I s` inside `J₂ s`). -/
theorem chi_up_yV {M : Type} [AddCommGroup M] [NeZero N] (hM : ∀ m : M, N • m = 0) (χ : D2.ΓH → M)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (t2 : T2) :
    χ (upV D2 K (yV RD D2 K hK hK2 t2)) = χ (D2.y t2) := by
  have hs := (shV_spec RD D2 t2).1
  have hi := iV_mem RD D2 t2
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = (xV RD D2 K hK t2 : G) * RD.x (shV RD D2 t2) := ⟨_, rfl⟩
  have hc : c ∈ Γ := by
    rw [hcdef]
    exact Γ.mul_mem (Subgroup.mem_subgroupOf.1 (xV_geo RD D2 K hK t2)) (RD.hx _)
  have hmem : ∀ j : D2.J (D2.sh t2), c * (j : G) * c⁻¹ ∈ D2.ΓH := fun j => by
    obtain ⟨hjΓ, hjπ⟩ := (D2.hJ _ _).1 j.2
    exact (D2.hΓH _).2 ⟨Γ.mul_mem (Γ.mul_mem hc (Subgroup.mem_inf.1 hjΓ).1) (Γ.inv_mem hc), by
      rw [map_mul, map_mul, map_inv, hjπ, mul_one, mul_inv_cancel]⟩
  let cj : D2.J (D2.sh t2) → D2.ΓH := fun j => ⟨c * (j : G) * c⁻¹, hmem j⟩
  have hcj : Continuous cj := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hψc : IsLocallyConstant (fun j => χ (cj j)) := hχc.comp_continuous hcj
  have hψ : ∀ a b, (fun j => χ (cj j)) (a * b) = (fun j => χ (cj j)) a + (fun j => χ (cj j)) b := fun a b => by
    show χ (cj (a * b)) = χ (cj a) + χ (cj b)
    rw [← hχ]
    congr 1
    exact Subtype.ext (by
      show c * ((a : G) * (b : G)) * c⁻¹ = (c * (a : G) * c⁻¹) * (c * (b : G) * c⁻¹)
      group)
  have hiJ : iV RD D2 t2 * D2.σ (D2.sh t2) * (iV RD D2 t2)⁻¹ ∈ D2.J (D2.sh t2) := by
    have hσ' := D2.hσ (D2.sh t2)
    rw [D2.hJ]
    refine ⟨(Γ ⊓ I _).mul_mem ((Γ ⊓ I _).mul_mem hi hσ') ((Γ ⊓ I _).inv_mem hi), ?_⟩
    rw [map_mul, map_mul, map_inv, D2.hσπ, mul_one, mul_inv_cancel]
  have key := LocGen.conj (D2.hloc (D2.sh t2)) hM (fun j => χ (cj j)) hψc hψ (iV RD D2 t2)
    (Subgroup.mem_inf.1 hi).2 hiJ
  have e1 : D2.y t2 = cj ⟨_, hiJ⟩ := Subtype.ext (by
    rw [D2.hy, x2_eq RD D2 K hK t2]
    show _ = c * (iV RD D2 t2 * D2.σ (D2.sh t2) * (iV RD D2 t2)⁻¹) * c⁻¹
    rw [hcdef]
    group)
  have e2 : upV D2 K (yV RD D2 K hK hK2 t2) = cj ⟨D2.σ (D2.sh t2), (D2.hJ _ _).2 ⟨D2.hσ _, D2.hσπ _⟩⟩ := Subtype.ext (by
    show (xV RD D2 K hK t2 : G) * (RD.x (shV RD D2 t2) * D2.σ (RD.sh (shV RD D2 t2)) *
      (RD.x (shV RD D2 t2))⁻¹) * (xV RD D2 K hK t2 : G)⁻¹ = c * D2.σ (D2.sh t2) * c⁻¹
    rw [hs, hcdef]
    group)
  rw [e1, e2]
  exact key.symm

theorem hRV [NeZero N] (χ : trΓH K (Γ := Γ) (π2 := π2) → ZMod N) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) : ∑ t2, χ (yV RD D2 K hK hK2 t2) = 0 := by
  have hc' : IsLocallyConstant (fun g => χ (downV D2 K hK2 g)) := hχc.comp_continuous (downV_cont D2 K hK2)
  have hh' : ∀ a b, (fun g => χ (downV D2 K hK2 g)) (a * b) =
      (fun g => χ (downV D2 K hK2 g)) a + (fun g => χ (downV D2 K hK2 g)) b := fun a b => by
    show χ (downV D2 K hK2 (a * b)) = _
    rw [downV_mul, hχ]
  rw [← D2.hR _ hc' hh']
  refine Finset.sum_congr rfl fun t2 _ => ?_
  exact chi_up_yV RD D2 K hK hK2 trNsmul _ hc' hh' t2

theorem hEV [NeZero N] (c : T2 → ZMod N) (hc : ∑ t2, c t2 = 0) :
    ∃ χ : trΓH K (Γ := Γ) (π2 := π2) → ZMod N, IsLocallyConstant χ ∧ (∀ a b, χ (a * b) = χ a + χ b) ∧
      ∀ t2, χ (yV RD D2 K hK hK2 t2) = c t2 := by
  obtain ⟨χ, hχc, hχ, hy⟩ := D2.hE c hc
  refine ⟨fun g => χ (upV D2 K g), hχc.comp_continuous (upV_cont D2 K),
    fun a b => hχ (upV D2 K a) (upV D2 K b), fun t2 => ?_⟩
  rw [← hy t2]
  exact chi_up_yV RD D2 K hK hK2 trNsmul χ hχc hχ t2

/-- **`V`'s residue data**, by transfer from `D2` (over `G := K`, `π_V = π₂|_K`, `Γ_V = geoU Γ K`,
`I_V = rdJ RD K`, boundary `T`, cover points `T₂`). -/
def trResDat [NeZero N] [DecidableEq T] : ResDat (piV π2 K) (geoU Γ K) (rdJ RD K) N T2 where
  σ := trSig RD D2 K hK hK2
  hσ t := ((mem_trJ RD K _ _).1 (trSig_mem_trJ RD D2 K hK hK2 t)).1
  hσπ t := ((mem_trJ RD K _ _).1 (trSig_mem_trJ RD D2 K hK hK2 t)).2
  J := trJ RD K (π2 := π2)
  hJ := mem_trJ RD K
  hloc := trLoc RD D2 K hK hK2
  ΓH := trΓH K
  hΓH := mem_trΓH K
  sh := shV RD D2
  x := xV RD D2 K hK
  hx := xV_geo RD D2 K hK
  y := yV RD D2 K hK hK2
  hy _ := rfl
  hrep := hrepV RD D2 K hK hK2
  hR := hRV RD D2 K hK hK2
  hE := hEV RD D2 K hK hK2
  s0 := s0V RD

end Tr2

end

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_CupDuality_VCnt1 =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 3: the `H²` count at `V` (generic)

* `resDatOfInj`: residue data change target along an injective hom `j` with `j ∘ π' = π`.
* `vResDat`: `V`'s residue data (`trResDat`) with the surjective `π_V = (piV π₂ K).rangeRestrict`.
* `exists_factor_rep`: a representation trivial on `ker f` (`f` onto) factors through `f`.
* **`vCount`**: for every finite representation `ρ` of `K` with open kernel containing `K ∩ ker π₂`,
  `H²(K)(ρ, Γ_V, I_V) ≃ H²_c(ρ, Γ_V)` (S4-PD item (4) at `V`), given `H2All` at `V`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh PerfectCx

noncomputable section

section OfInj

variable {Gf Gf' : Type} [Group Gf] [Group Gf'] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {π : G →* Gf} {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ}
  {T : Type} [Fintype T] (D : ResDat π Γ I N T) (π' : G →* Gf') (j : Gf' →* Gf)
  (hj : Function.Injective j) (hjπ : ∀ g, j (π' g) = π g)

/-- **Change of target** of residue data along an injective `j` with `j ∘ π' = π`. -/
def resDatOfInj : ResDat π' Γ I N T where
  σ := D.σ
  hσ := D.hσ
  hσπ s := (ker_iff_inj π' j hj hjπ _).2 (D.hσπ s)
  J := D.J
  hJ s g := (D.hJ s g).trans (and_congr_right' (ker_iff_inj π' j hj hjπ g).symm)
  hloc := D.hloc
  ΓH := D.ΓH
  hΓH g := (D.hΓH g).trans (and_congr_right' (ker_iff_inj π' j hj hjπ g).symm)
  sh := D.sh
  x := D.x
  hx := D.hx
  y := D.y
  hy := D.hy
  hrep s p hp := by
    have h := D.hrep s (j p) ((mem_map_iff_inj π' j hj hjπ Γ p).1 hp)
    refine (existsUnique_congr fun t => ?_).2 h
    rw [mem_map_iff_inj π' j hj hjπ, map_mul, map_inv, hjπ]
  hR := D.hR
  hE := D.hE
  s0 := D.s0

end OfInj

section Factor

end Factor

section Cnt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Gf Gf2 : Type} [Group Gf] [Group Gf2] {π : G →* Gf} {π2 : G →* Gf2} {Γ : Subgroup G} [Γ.Normal]
  {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T T2 : Type} [Fintype T] [Fintype T2]
  [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]
  (RD : ResDat π Γ I N T) (D2 : ResDat π2 Γ I N T2) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)
  (hK2 : ∀ g, π2 g = 1 → g ∈ K)

/-- `V`'s residue data with the surjective `π_V`. -/
def vResDat [NeZero N] [DecidableEq T] : ResDat (piR π2 K) (geoU Γ K) (rdJ RD K) N T2 :=
  resDatOfInj (trResDat RD D2 K hK hK2) (piR π2 K) (piV π2 K).range.subtype (Subgroup.subtype_injective _)
    (fun _ => rfl)

end Cnt

end

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_LisseDuality_AmbH2 =====
section

/-!
# S4-CurveDuality O7d-P1d (T3): `H²`-vanishing passes to an open subgroup of finite index

For `H ≤ G` open of finite index and `Δ ≤ H`: `H2All Λ G Δ l n → H2All Λ H (Δ.subgroupOf H) l n`.
A finite `H`-representation `W` is an `H`-equivariant retract of the restriction of the coinduced `G`-representation
`coind_H^G W` (`coindSubIota`, `coindSubEv`), which is finite (`coindSub_finite`) with open kernel
(`isOpen_coindSub_ker`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Retract

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) {W : Type} [AddCommGroup W] [Module Λ W] (ρ : Representation Λ H W)

open Classical

end Retract

section H2

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Subgroup G} {Δ : Subgroup G}

/-- **`H²`-vanishing on an open subgroup of finite index.** -/
theorem h2All_subgroupOf (hHo : IsOpen (H : Set G)) [Finite (G ⧸ H)] (hΔ : Δ ≤ H) {l n : ℕ}
    (hall : H2All Λ G Δ l n) : H2All Λ H (Δ.subgroupOf H) l n := by
  intro W _ _ ρ _ htor hρ f hf hc
  have := coindSub_finite H ρ
  have htorC : ∀ F : Representation.coindV H.subtype ρ, (l ^ n) • F = 0 := fun F =>
    Subtype.ext (funext fun x => by simp [htor])
  obtain ⟨b, hb, hfb⟩ := hall (Representation.coindV H.subtype ρ) (Representation.coind H.subtype ρ) htorC
    (isOpen_coindSub_ker H ρ hHo hρ) (fun x => coindSubIota H ρ (f (toSubOf hΔ x.1, toSubOf hΔ x.2)))
    (IsLocallyConstant.comp (hf.comp_continuous ((continuous_toSubOf hΔ).prodMap (continuous_toSubOf hΔ))) _)
    (fun a a' a'' => by
      have := congrArg (coindSubIota H ρ) (hc (toSubOf hΔ a) (toSubOf hΔ a') (toSubOf hΔ a''))
      simp only [map_add] at this
      rw [coindSubIota_equiv] at this
      exact this)
  refine ⟨fun x => coindSubEv H ρ (b (ofSubOf x)), (hb.comp_continuous continuous_ofSubOf).comp _,
    fun x y => ?_⟩
  have := congrArg (coindSubEv H ρ) (hfb (ofSubOf x) (ofSubOf y))
  simp only [map_add, map_sub, coindSubEv_iota] at this
  have key := coindSubEv_equiv H ρ (x : H) (b (ofSubOf y))
  beta_reduce
  rw [← key]
  exact this

end H2

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VFrobA =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 5: the Frobenius scalar is a unit, generic form

`H²(K)` of the constant cone is `≅ k` (`h2kEquiv`), so every `k`-linear endomorphism of it is a scalar
(`endo_eq_smul`), and the scalar is a unit when the endomorphism is onto (`isUnit_of_surjective`). Frobenius on
`H²(K)` is onto when `frob2` is, which holds when `τ` is bijective and conjugation by `ψ h_s` maps
`Γ ⊓ I (τ s)` back into `I s` (exact boundary conjugation, `hex`). **`constPair_frob_unit`**: then
`⟨F x, F y⟩ = c ⟨x, y⟩` with `c` a unit, which is all `inR_conj` needs (no twist identity).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M)

/-- `conjMap x` is onto when `x` also conjugates `Δ'` back into `Δ`. -/
theorem conjMap_conjMap_inv (x : G) {Δ Δ' : Subgroup G} (hx : ∀ g ∈ Δ, x⁻¹ * g * x ∈ Δ')
    (hx' : ∀ g ∈ Δ', x⁻¹⁻¹ * g * x⁻¹ ∈ Δ) (d : Z1 ρ Δ) : conjMap ρ x hx (conjMap ρ x⁻¹ hx' d) = d := by
  apply Subtype.ext
  funext g
  rw [conjMap_apply, conjMap_apply]
  have e : conjSub x⁻¹ hx' (conjSub x hx g) = g := Subtype.ext (by
    simp only [conjSub_val]
    group)
  rw [e, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable (Γ : Subgroup G) [hΓ : Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (τ : S → S) (h : S → Γ)

/-- `frob2` is onto for exact boundary conjugation and bijective `τ`. -/
theorem frob2_surjective (hI : BdryCompat Γ I ψ τ h) (hτ : Function.Bijective τ)
    (hex : ∀ s (g : G), g ∈ Γ → g ∈ I (τ s) → (ψ * h s) * g * (ψ * h s)⁻¹ ∈ I s) :
    Function.Surjective (frob2 ρ Γ I ψ τ h hI) := by
  intro f
  have hx' : ∀ s, ∀ g ∈ Γ ⊓ I (τ s), (ψ * (h s : G))⁻¹⁻¹ * g * (ψ * (h s : G))⁻¹ ∈ Γ ⊓ I s := by
    intro s g hg
    rw [inv_inv]
    obtain ⟨hgΓ, hgI⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨hΓ.conj_mem g hgΓ _, hex s g hgΓ hgI⟩
  let gs : (s : S) → Z1 ρ (Γ ⊓ I (τ s)) := fun s => conjMap ρ (ψ * (h s : G))⁻¹ (hx' s) (f s)
  let eτ : S ≃ S := Equiv.ofBijective τ hτ
  let e : (u : S) → Z1 ρ (Γ ⊓ I u) := Equiv.piCongrLeft (fun u => Z1 ρ (Γ ⊓ I u)) eτ gs
  refine ⟨e, funext fun s => ?_⟩
  have he : e (τ s) = gs s := Equiv.piCongrLeft_apply_apply (fun u => Z1 ρ (Γ ⊓ I u)) eτ gs s
  show conjMap ρ (ψ * h s) (bdry_mem Γ I ψ τ h hI s) (e (τ s)) = f s
  rw [he]
  exact conjMap_conjMap_inv ρ _ _ _ (f s)

variable (hρ : IsOpen (ρ.ker : Set G))

/-- Frobenius on `H²(K)` is onto when `frob2` is. -/
theorem frobH2K_surjective (hI : BdryCompat Γ I ψ τ h) (hs : Function.Surjective (frob2 ρ Γ I ψ τ h hI)) :
    Function.Surjective (frobH2K ρ Γ I ψ τ h hρ hI) := by
  intro z
  obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨e', he'⟩ := hs e
  exact ⟨Submodule.Quotient.mk e', by rw [frobH2K_mk, he']⟩

end H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [Nonempty S]
  {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

/-- **VFrobA.** Exact boundary conjugation with bijective `τ`: `⟨F x, F y⟩ = c ⟨x, y⟩` for a unit `c`. -/
theorem constPair_frob_unit (H : CupHyp (Representation.trivial k G k) σ σ (LinearMap.mul k k) Γ)
    (D : ConstData σ Γ I t) {ψ : G} {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I ψ τ h)
    (hτ : Function.Bijective τ)
    (hex : ∀ s (g : G), g ∈ Γ → g ∈ I (τ s) → (ψ * h s) * g * (ψ * h s)⁻¹ ∈ I s) :
    ∃ c : k, IsUnit c ∧ ∀ x y, constPair H D (frobH1c (Representation.trivial k G k) Γ I ψ τ h hI x)
      (frobH1 σ Γ ψ y) = c * constPair H D x y := by
  refine ⟨h2kEquiv D H.openL (frobH2K σ Γ I ψ τ h H.openL hI ((h2kEquiv D H.openL).symm 1)),
    isUnit_of_surjective _ _ (frobH2K_surjective σ Γ I ψ τ h H.openL hI
      (frob2_surjective σ Γ I ψ τ h hI hτ hex)), ?_⟩
  exact constPair_frob H D ψ τ h hI _ (endo_eq_smul (h2kEquiv D H.openL) (frobH2K σ Γ I ψ τ h H.openL hI))

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VPar =====
section

/-!
# S4-CurveDuality, O9b (V-free) part 3: the parabolic block from the right kernel and finiteness mod `l`

Route L (session 50). If the `ℤ/l`-valued parabolic homomorphisms on `Γ` form a finite group (`parMod`), they have a
dual basis (`exists_parBasis_one`); every member lifts to a parabolic `ℤ/lⁿ`-valued one (`exists_lift_hom`,
`exists_parLift`: `H²(Γ, ℤ/lⁿ) = 0` and the residue data), so the `ℤ/lⁿ`-valued ones have a dual basis
(`exists_parBasis_of_lift`). With a zero right kernel over `ℤ/lⁿ` the parabolic block is perfect over `ℤ/lⁿ`
(`parabolic_of_rightKer`) and then over every `Λ ← ℤ/lⁿ` (`parabolic_of_zmod`): **`parabolic_of_finite`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh

noncomputable section

section VPar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G}
  {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

variable {l : ℕ} [Fact l.Prime]

/-- A `ℤ/l`-basis of the parabolic homomorphisms, with dual elements, when there are finitely many. -/
theorem exists_parBasis_one [Finite ↥(parMod Γ I l)] :
    ∃ (r : ℕ) (b : Fin r → Γ → ZMod l) (e : Fin r → Γ), (∀ i, IsParHom (InBdry I) (b i)) ∧
      (∀ i j, b i (e j) = if i = j then 1 else 0) ∧
      ∀ y : Γ → ZMod l, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * b i g := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have : Module.Finite (ZMod l) ↥(parMod Γ I l) := Module.Finite.of_finite
  let B := Module.finBasis (ZMod l) ↥(parMod Γ I l)
  let E : ↥(parMod Γ I l) ≃+ ↥(parMod Γ I l).toAddSubgroup :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let Ψ : (Fin (Module.finrank (ZMod l) ↥(parMod Γ I l)) → ZMod l) ≃+ ↥(parMod Γ I l).toAddSubgroup :=
    B.equivFun.symm.toAddEquiv.trans E
  obtain ⟨e, hδ, hspan⟩ := exists_dualBasis (parMod Γ I l).toAddSubgroup Ψ
    (fun y hy => (show IsParHom (InBdry I) y from hy).2.1)
  exact ⟨_, chiOf _ Ψ, e, fun i => chiOf_mem _ Ψ i, hδ, fun y hy g => hspan y hy g⟩

variable [Γ.Normal] {n : ℕ}

/-- **O9b, Route L.** Finitely many `ℤ/l`-valued parabolic homomorphisms and a zero right kernel of `constPair`
over `ℤ/lⁿ` make the parabolic block perfect over every `Λ ← ℤ/lⁿ`. -/
theorem parabolic_of_finite (hn : n ≠ 0) {Λ : Type} [CommRing Λ] (ιΛ : ZMod (l ^ n) →+* Λ)
    {σ0 : Representation (ZMod (l ^ n)) G (ZMod (l ^ n))} {σΛ : Representation Λ G Λ}
    (H0 : CupHyp (Representation.trivial (ZMod (l ^ n)) G (ZMod (l ^ n))) σ0 σ0
      (LinearMap.mul (ZMod (l ^ n)) (ZMod (l ^ n))) Γ)
    (D0 : ConstData σ0 Γ I t)
    (HΛ : CupHyp (Representation.trivial Λ G Λ) σΛ σΛ (LinearMap.mul Λ Λ) Γ) (DΛ : ConstData σΛ Γ I t)
    [Finite ↥(parMod Γ I l)] (hR : ∀ d : Γ → ZMod (l ^ n), InR H0 D0 d → d = 0) :
    (pairQuotSub (constPair HΛ DΛ) _ _ (constPair_h0 HΛ DΛ)).IsPerfPair := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨r, b, e, hb, hbe, hspan1⟩ := exists_parBasis_one (Γ := Γ) (I := I) (l := l)
  have hlift : ∀ i, ∃ y : Γ → ZMod (l ^ n), IsParHom (InBdry I) y ∧ ∀ g, redL l hn (y g) = b i g := fun i => by
    obtain ⟨χ', h1, h2, h3⟩ := exists_lift_hom hn D0.triv H0.van (hb i).1 (hb i).2.1
    exact exists_parLift hn D0 (hb i) h1 h2 h3
  obtain ⟨χ, hχ, hδ, hspan⟩ := exists_parBasis_of_lift hn hbe hspan1 hlift
  exact parabolic_of_zmod ιΛ H0 D0 HΛ DΛ hχ hδ hspan (parabolic_of_rightKer H0 D0 hχ hδ hspan hR)

end VPar

end

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_LisseDuality_Nat =====
section

/-!
# S4-CurveDuality O7a: naturality of the cup product in the coefficients

* `cupPair_natural`: for equivariant `f : M → M₂`, `g : M₂' → M'` with `β₂ (f m) y = β m (g y)`,
  `cup₂(H¹_c(f) x, y) = cup(x, H¹(g) y)` in `H²(K(L))`.
* The dual coefficients `M^∨(1) := Hom(M, L)` with `(g · φ) = σ g ∘ φ ∘ ρ g⁻¹` (`Representation.linHom ρ σ`) and the
  evaluation pairing `evalB`: `dualHyp` (a `CupHyp` from open kernels of `ρ`, `σ` and `H²(Γ, L) = 0`),
  `transp f` (precomposition, equivariant) and `cupPair_natural_dual`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {M' : Type} [AddCommGroup M'] [Module k M']
  {M₂ : Type} [AddCommGroup M₂] [Module k M₂] {M₂' : Type} [AddCommGroup M₂'] [Module k M₂']
  {L : Type} [AddCommGroup L] [Module k L]
  {ρ : Representation k G M} {ρ' : Representation k G M'} {ρ₂ : Representation k G M₂}
  {ρ₂' : Representation k G M₂'} {σ : Representation k G L}
  {β : M →ₗ[k] M' →ₗ[k] L} {β₂ : M₂ →ₗ[k] M₂' →ₗ[k] L} {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}

/-- **Naturality of the cup product** in the coefficients. -/
theorem cupPair_natural (H : CupHyp ρ ρ' σ β Γ) (H₂ : CupHyp ρ₂ ρ₂' σ β₂ Γ) {f : M →ₗ[k] M₂}
    (hf : IsEquivariant ρ ρ₂ f) {g : M₂' →ₗ[k] M'} (hg : IsEquivariant ρ₂' ρ' g)
    (hβ : ∀ m y, β₂ (f m) y = β m (g y)) (x : H1c ρ Γ I) (y : H1 ρ₂' Γ) :
    cupPair H₂ (mapH1c Γ I hf x) y = cupPair H x (mapH1 Γ hg y) := by
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
  change cupH H₂ ⟨pushc Γ f p, pushc_mem_Z1c Γ I hf p.2⟩ d =
    cupH H p ⟨fun a => g ((d : Γ → M₂') a), push_mem_Z1 Γ hg d.2⟩
  obtain ⟨u, hu⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 (push_mem_Z1 Γ hg d.2)
  rw [cupH_eq H _ _ u hu, cupH_eq H₂ _ _ u (isPrim_push hg hβ hu)]
  congr 1
  funext s
  apply Subtype.ext
  funext a
  show β₂ (f ((p : (Γ → M) × (S → M)).2 s)) ((d : Γ → M₂') ⟨a.1, (Subgroup.mem_inf.1 a.2).1⟩) -
      u ⟨a.1, (Subgroup.mem_inf.1 a.2).1⟩ =
    β ((p : (Γ → M) × (S → M)).2 s) (g ((d : Γ → M₂') ⟨a.1, (Subgroup.mem_inf.1 a.2).1⟩)) -
      u ⟨a.1, (Subgroup.mem_inf.1 a.2).1⟩
  rw [hβ]

/-! ## Dual coefficients `M^∨(1) = Hom(M, L)` -/

/-- The cup-product hypotheses for `M × M^∨(1) → L`. -/
theorem dualHyp (hρ : IsOpen (ρ.ker : Set G)) (hσ : IsOpen (σ.ker : Set G)) (hv : H2Van σ Γ ⊤) :
    CupHyp ρ (ρ.linHom σ) σ (evalB (M := M) (L := L)) Γ where
  equiv g m φ := by
    rw [evalB_apply, evalB_apply, Representation.linHom_apply]
    show σ g (φ (ρ g⁻¹ (ρ g m))) = σ g (φ m)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  open' := isOpen_linHom_ker hρ hσ
  openL := hσ
  van := hv

/-- Naturality for the duality pairing `H¹_c(M) × H¹(M^∨(1)) → H²(K(L))`. -/
theorem cupPair_natural_dual (H : CupHyp ρ (ρ.linHom σ) σ (evalB (M := M) (L := L)) Γ)
    (H₂ : CupHyp ρ₂ (ρ₂.linHom σ) σ (evalB (M := M₂) (L := L)) Γ) {f : M →ₗ[k] M₂}
    (hf : IsEquivariant ρ ρ₂ f) (x : H1c ρ Γ I) (y : H1 (ρ₂.linHom σ) Γ) :
    cupPair H₂ (mapH1c Γ I hf x) y = cupPair H x (mapH1 Γ (transp_equivariant (σ := σ) hf) y) :=
  cupPair_natural H H₂ hf (transp_equivariant hf) (fun _ _ => rfl) x y

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Exact =====
section

/-!
# S4-CurveDuality O7b: exactness of `H¹_c` and `H¹` in the coefficients, and the dévissage chase

* `mapH1c_injective`: `H¹_c(f)` is injective for injective `f` (`S` nonempty: `H⁰` of the cone vanishes);
* `exists_pull_Z1c`, `exact_mapH1c`: for `0 → M → X → Q → 0` exact, `H¹_c(M) → H¹_c(X) → H¹_c(Q)` is exact;
* `mapH1_surjective`: `H¹(q)` is surjective for surjective `q` (cohomological dimension 1, `H2All`);
* `transp_surjective`: `Hom(X, L) → Hom(M, L)` is surjective for injective `f` and `L` injective (`Λ` self-injective);
* `injective_of_chase`, `bijective_of_chase`: the dévissage diagram chase (O7c).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {X : Type} [AddCommGroup X] [Module k X]
  {Q : Type} [AddCommGroup Q] [Module k Q]
  {ρ : Representation k G M} {ρX : Representation k G X} {ρQ : Representation k G Q}
  {Γ : Subgroup G} {S : Type} {I : S → Subgroup G}

/-! ## `H¹_c` is left exact -/

/-- **Exactness of `H¹_c(M) → H¹_c(X) → H¹_c(Q)`** for a short exact sequence `0 → M → X → Q → 0`. -/
theorem exact_mapH1c (hX : IsOpen (ρX.ker : Set G)) {f : M →ₗ[k] X} (hf : IsEquivariant ρ ρX f)
    (hinj : Function.Injective f) {q : X →ₗ[k] Q} (hq : IsEquivariant ρX ρQ q)
    (hsurj : Function.Surjective q) (hex : Function.Exact f q) (y : H1c ρX Γ I)
    (hy : mapH1c Γ I hq y = 0) : ∃ x, mapH1c Γ I hf x = y := by
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ y
  have hy0 : (Submodule.Quotient.mk (⟨pushc Γ q p, pushc_mem_Z1c Γ I hq p.2⟩ : Z1c ρQ Γ I) :
      H1c ρQ Γ I) = 0 := hy
  have hy' := (Submodule.Quotient.mk_eq_zero _).1 hy0
  have hB : pushc Γ q (p : (Γ → X) × (S → X)) ∈ B1c ρQ Γ I := hy'
  obtain ⟨-, y₀, hy₁, hy₂⟩ := (mem_B1c ρQ Γ I _).1 hB
  obtain ⟨x₀, rfl⟩ := hsurj y₀
  set P : Z1c ρX Γ I := p - cx0c ρX Γ I hX x₀ with hP
  have e1 : ∀ g, (P : (Γ → X) × (S → X)).1 g = (p : (Γ → X) × (S → X)).1 g - (ρX g x₀ - x₀) :=
    fun g => rfl
  have e2 : ∀ s, (P : (Γ → X) × (S → X)).2 s = (p : (Γ → X) × (S → X)).2 s - x₀ := fun s => rfl
  have h1 : ∀ g, (P : (Γ → X) × (S → X)).1 g ∈ Set.range f := fun g => (hex _).1 (by
    rw [e1, map_sub, map_sub, hq]
    have h : q ((p : (Γ → X) × (S → X)).1 g) = ρQ g (q x₀) - q x₀ := hy₁ g
    rw [h, sub_self])
  have h2 : ∀ s, (P : (Γ → X) × (S → X)).2 s ∈ Set.range f := fun s => (hex _).1 (by
    rw [e2, map_sub]
    have h : q ((p : (Γ → X) × (S → X)).2 s) = q x₀ := hy₂ s
    rw [h, sub_self])
  obtain ⟨P', hP'⟩ := exists_pull_Z1c hf hinj P h1 h2
  refine ⟨Submodule.mkQ _ P', ?_⟩
  have hc : Submodule.mkQ ((B1c ρX Γ I).comap (Z1c ρX Γ I).subtype) (cx0c ρX Γ I hX x₀) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← range_cx0c ρX Γ I hX]
    exact LinearMap.mem_range_self _ _
  have hpP : p = P + cx0c ρX Γ I hX x₀ := by rw [hP, sub_add_cancel]
  rw [hpP, map_add, hc, add_zero]
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext hP'

/-! ## `H¹` is right exact (cohomological dimension `≤ 1`) -/

theorem mapH1_surjective {l n : ℕ} (hall : H2All k G Γ l n) [Finite X] (hXn : ∀ x : X, (l ^ n) • x = 0)
    (hX : IsOpen (ρX.ker : Set G)) {q : X →ₗ[k] Q} (hq : IsEquivariant ρX ρQ q)
    (hsurj : Function.Surjective q) : Function.Surjective (mapH1 Γ hq) := by
  intro y
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨c, hc⟩ := z1Map_surjective_of_all ρX ρQ Γ hall hXn hX q hq hsurj d
  refine ⟨Submodule.mkQ _ c, ?_⟩
  rw [← hc]
  rfl

/-! ## Duals over a self-injective coefficient ring -/

/-! ## The dévissage chase (O7c) -/

section Chase

variable {R : Type} [CommRing R] {HM HX HQ DM DX DQ : Type} [AddCommGroup HM] [Module R HM]
  [AddCommGroup HX] [Module R HX] [AddCommGroup HQ] [Module R HQ] [AddCommGroup DM] [Module R DM]
  [AddCommGroup DX] [Module R DX] [AddCommGroup DQ] [Module R DQ]

end Chase

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Dev =====
section

/-!
# S4-CurveDuality O7c: lisse duality by dévissage from coinduced modules

Fix `σ : Representation Λ G Λ` (the twist `Λ(1)`), `H²(Γ, Λ(1)) = 0` and a trace `e : H²(K(Λ(1))) → Λ`. For a
representation `ρ` with open kernel the **duality map** is `alphaM : H¹_c(M) → Hom(H¹(M^∨(1)), Λ)`,
`x ↦ (y ↦ e (x ∪ y))` (`alpha_natural`: natural in `M`).

For representations `τ ∘ π` of a quotient `π : G →* Gf` with open kernel (lisse sheaves trivialised by `π`):
* `coindF M₀`: `Gf → M₀` with left translation (the push-forward of the constant sheaf `M₀` from the cover);
  `emb τ : M ↪ (Gf → M)`, `m ↦ (x ↦ τ(x⁻¹) m)`, equivariant; `quotRepF τ` the quotient representation;
* `alpha_injective_of_base`: `alphaM` injective on all coinduced modules ⇒ injective for every finite `τ`;
* `alpha_bijective_of_base`: `alphaM` bijective on all coinduced modules ⇒ bijective for every finite `τ`
  (`Λ` finite, self-injective and killed by `lⁿ`, `S` nonempty, cohomological dimension 1 via `H2All`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {σ : Representation Λ G Λ} {hσ : IsOpen (σ.ker : Set G)}
  {M : Type} [AddCommGroup M] [Module Λ M] {X : Type} [AddCommGroup X] [Module Λ X]

/-- **The duality map** `H¹_c(M) → Hom(H¹(M^∨(1)), Λ)`, `x ↦ (y ↦ e (x ∪ y))`. -/
def alphaM (hv : H2Van σ Γ ⊤) (e : H2K σ Γ I hσ →ₗ[Λ] Λ) (ρ : Representation Λ G M)
    (hρ : IsOpen (ρ.ker : Set G)) : H1c ρ Γ I →ₗ[Λ] Module.Dual Λ (H1 (ρ.linHom σ) Γ) :=
  (cupPair (I := I) (dualHyp hρ hσ hv)).compr₂ e

theorem alphaM_apply (hv : H2Van σ Γ ⊤) (e : H2K σ Γ I hσ →ₗ[Λ] Λ) (ρ : Representation Λ G M)
    (hρ : IsOpen (ρ.ker : Set G)) (x : H1c ρ Γ I) (y : H1 (ρ.linHom σ) Γ) :
    alphaM hv e ρ hρ x y = e (cupPair (dualHyp hρ hσ hv) x y) := rfl

theorem alpha_natural (hv : H2Van σ Γ ⊤) (e : H2K σ Γ I hσ →ₗ[Λ] Λ) {ρ : Representation Λ G M}
    (hρ : IsOpen (ρ.ker : Set G)) {ρX : Representation Λ G X} (hX : IsOpen (ρX.ker : Set G))
    {f : M →ₗ[Λ] X} (hf : IsEquivariant ρ ρX f) (x : H1c ρ Γ I) :
    alphaM hv e ρX hX (mapH1c Γ I hf x) = (mapH1 Γ (transp_equivariant (σ := σ) hf)).dualMap (alphaM hv e ρ hρ x) :=
  LinearMap.ext fun y => congrArg e (cupPair_natural_dual (dualHyp hρ hσ hv) (dualHyp hX hσ hv) hf x y)

/-! ## Coinduced modules and the canonical embedding -/

variable {Gf : Type} [Group Gf]

/-! ## Dévissage -/

variable (hv : H2Van σ Γ ⊤) (e : H2K σ Γ I hσ →ₗ[Λ] Λ) (π : G →* Gf) (hπ : IsOpen (π.ker : Set G))

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Lam =====
section

/-!
# S4-CurveDuality O7d-P3b T2+T3: the transfer weights are one unit

Setting of `Def_RP_LisseDuality_Trans`. For the weights `λ` of `sum_trP_eq_lam`:
* `res_gI_eq`: for `c ∈ Z¹(Γ, f_*σ)`, `c(x_u⁻¹ t'_u x_u)(x_u) = (shapiroZ1 c)(t'_u)`;
* `lam_eq` (T2): all `λ_u` are equal (residue theorem on `G` against its converse on `V`);
* `coindV_ext_sec`, `coindV_finite`, `trP_surjective`;
* **`sum_trP_eq_unit_mul`** (T2 + T3): `Σ_s trP (e_s t_s) = c₀ · Σ_u e_{π u}(x_u⁻¹ t'_u x_u)(x_u)` for every
  `e ∈ Π_s Z¹(Γ ⊓ I s, f_*σ)`, with `c₀` a unit (lift `D.surj`'s cocycles through `trP` by `hallI`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Lam

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)

section Local

variable {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {T : Type} [Fintype T]
  {J : T → Subgroup K} {πT : T → S} {xT : T → Γ} {t' : (u : T) → ↥(geoU Γ K ⊓ J u)}

include hK in
/-- `c|_{Γ ⊓ I (π u)}(x_u⁻¹ t'_u x_u)(x_u) = (shapiroZ1 c)(t'_u)` for `c ∈ Z¹(Γ, f_*σ)`. -/
theorem res_gI_eq (hD : ∀ (g : Γ) (v : Λ), σ g v = v) (hJ : InertiaLift Γ K I J πT xT)
    (c : Z1 (pushRep K (σ.comp K.subtype)) Γ) (u : T) :
    (((PerfectCx.res (pushRep K (σ.comp K.subtype)) Γ (inf_le_left : Γ ⊓ I (πT u) ≤ Γ) c :
        ↥(Γ ⊓ I (πT u)) → Representation.coindV K.subtype (σ.comp K.subtype)) (gI K hJ t' u) :
        Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (xT u) =
      (shapiroZ1 Γ K (σ.comp K.subtype) c : geoU Γ K → Λ) (tG t' u) := by
  have h1 := Z1_conj_apply σ K hD c.2 (normal_of_hK π K hK) (xT u)⁻¹ (geoToΓ Γ K (tG t' u))
    (t' u : K).2 (xT u : G)
  have e1 : ((xT u)⁻¹ * geoToΓ Γ K (tG t' u) * ((xT u)⁻¹)⁻¹ : Γ) =
      ⟨((xT u : Γ) : G)⁻¹ * ((t' u : K) : G) * (xT u : G), (Subgroup.mem_inf.1 (gI K hJ t' u).2).1⟩ :=
    Subtype.ext (by rw [inv_inv]; rfl)
  have e2 : (xT u : G) * (((xT u)⁻¹ : Γ) : G) = 1 := by rw [Subgroup.coe_inv, mul_inv_cancel]
  rw [e1, e2] at h1
  exact h1

include hK in
/-- **T2**: the weights of `sum_trP_eq_lam` are all equal. -/
theorem lam_eq [Fintype S] {t : (s : S) → ↥(Γ ⊓ I s)} (D : ConstData σ Γ I t)
    (hJ : InertiaLift Γ K I J πT xT) (DV : ConstData (σ.comp K.subtype) (geoU Γ K) J t')
    (R : CosetReps Γ K) (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ) (hKo : IsOpen (K : Set G))
    (lam : T → Λ)
    (hlam : ∀ e : (s : S) → Z1 (pushRep K (σ.comp K.subtype)) (Γ ⊓ I s),
      ∑ s, trP σ π K hs ((e s : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype)) (t s)) =
        ∑ u, lam u * (((e (πT u) : ↥(Γ ⊓ I (πT u)) → Representation.coindV K.subtype (σ.comp K.subtype))
          (gI K hJ t' u) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (xT u))
    (u v : T) : lam u = lam v := by
  classical
  have key : ∀ c : Z1 (pushRep K (σ.comp K.subtype)) Γ,
      ∑ w, lam w * (shapiroZ1 Γ K (σ.comp K.subtype) c : geoU Γ K → Λ) (tG t' w) = 0 := fun c => by
    have hL := D.resSum (z1Map (pushRep K (σ.comp K.subtype)) σ Γ (trP σ π K hs) (trP_equiv σ π K hK hs) c)
    have h := hlam fun s => PerfectCx.res (pushRep K (σ.comp K.subtype)) Γ (inf_le_left : Γ ⊓ I s ≤ Γ) c
    refine Eq.trans ?_ (h.symm.trans hL)
    exact Finset.sum_congr rfl fun w _ => congrArg (lam w * ·) (res_gI_eq σ π K hK D.triv hJ c w).symm
  obtain ⟨d, hd⟩ := DV.resOnto (fun w => (if w = u then 1 else 0) - (if w = v then 1 else 0))
    (by simp [Finset.sum_sub_distrib])
  have hz : liftZ1 (σ.comp K.subtype) R hcov (d : geoU Γ K → Λ) ∈ Z1 (pushRep K (σ.comp K.subtype)) Γ :=
    (mem_Z1 _ _ _).mpr ⟨liftZ1_isLocallyConstant _ R hcov hKo d.2, liftZ1_cocycle _ R hcov d.2⟩
  have h0 := key ⟨_, hz⟩
  have h1 : ∀ w, (shapiroZ1 Γ K (σ.comp K.subtype) ⟨_, hz⟩ : geoU Γ K → Λ) (tG t' w) =
      (if w = u then 1 else 0) - (if w = v then 1 else 0) := fun w =>
    (resEv_liftZ1 (σ.comp K.subtype) R hcov (d : geoU Γ K → Λ) (tG t' w)).trans (hd w)
  have h2 : ∑ w, lam w * ((if w = u then 1 else 0) - (if w = v then 1 else 0)) = 0 := by
    refine Eq.trans ?_ h0
    exact Finset.sum_congr rfl fun w _ => by rw [h1 w]
  simp only [mul_sub, mul_boole, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at h2
  exact sub_eq_zero.mp h2

include hK in
/-- **T2 + T3**: `Σ_s trP (e_s t_s) = c₀ · Σ_u e_{π u}(x_u⁻¹ t'_u x_u)(x_u)` with `c₀` a unit. -/
theorem sum_trP_eq_unit_mul [Fintype S] [Nonempty S] [Finite Λ] {l n : ℕ}
    (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l n) (hΛ : ∀ a : Λ, (l ^ n) • a = 0)
    (hπ : IsOpen (π.ker : Set G)) (hσ : IsOpen (σ.ker : Set G))
    {t : (s : S) → ↥(Γ ⊓ I s)} (D : ConstData σ Γ I t) (hJ : InertiaLift Γ K I J πT xT)
    (hDC : DCover Γ K I πT xT) (DV : ConstData (σ.comp K.subtype) (geoU Γ K) J t')
    (R : CosetReps Γ K) (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ) (hKo : IsOpen (K : Set G)) :
    ∃ c₀ : Λ, IsUnit c₀ ∧ ∀ e : (s : S) → Z1 (pushRep K (σ.comp K.subtype)) (Γ ⊓ I s),
      ∑ s, trP σ π K hs ((e s : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype)) (t s)) =
        c₀ * ∑ u, (((e (πT u) : ↥(Γ ⊓ I (πT u)) → Representation.coindV K.subtype (σ.comp K.subtype))
          (gI K hJ t' u) : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) (xT u) := by
  classical
  obtain ⟨lam, hlam⟩ := sum_trP_eq_lam σ π K hK hs D.triv hJ hDC hcov DV t
  have hconst := lam_eq σ π K hK hs D hJ DV R hcov hKo lam hlam
  obtain ⟨s0⟩ := ‹Nonempty S›
  obtain ⟨u0, -⟩ := hDC s0 1
  haveI := coindV_finite σ π K hK hs
  have hlift : ∀ s, ∃ e : Z1 (pushRep K (σ.comp K.subtype)) (Γ ⊓ I s),
      trP σ π K hs ((e : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype)) (t s)) =
        if s = s0 then 1 else 0 := fun s => by
    obtain ⟨ε, hε⟩ := D.surj s (if s = s0 then 1 else 0)
    obtain ⟨e, he⟩ := z1Map_surjective_of_all (pushRep K (σ.comp K.subtype)) σ (Γ ⊓ I s) (hallI s)
      (fun F => Subtype.ext (funext fun x => by simp [hΛ])) (isOpen_pushS σ π K hK hπ hσ) (trP σ π K hs)
      (trP_equiv σ π K hK hs) (trP_surjective σ π K hK hs) ε
    exact ⟨e, (congrArg (fun z : Z1 σ (Γ ⊓ I s) => (z : ↥(Γ ⊓ I s) → Λ) (t s)) he).trans hε⟩
  choose e1 he1 using hlift
  have hL : ∑ s, trP σ π K hs ((e1 s : ↥(Γ ⊓ I s) → Representation.coindV K.subtype (σ.comp K.subtype))
      (t s)) = 1 := by
    simp only [he1, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  refine ⟨lam u0, ?_, fun e => (hlam e).trans (sum_mul_const _ _ (lam u0) fun u => hconst u u0)⟩
  have h1 := (hL.symm.trans (hlam e1)).trans (sum_mul_const _ _ (lam u0) fun u => hconst u u0)
  exact IsUnit.of_mul_eq_one _ h1.symm

end Local

end Lam

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VS3b =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 9: the `V`-level inputs in the S3 chart

For an open subgroup `K` of `π₁(U)` (the cover `V`, `K = ker π`):
* `hbasis_S3`: open normal subgroups form a basis at `1` in `π₁(U)` (Krull topology);
* `hallV_S3`, `hallIV_S3`: `H²(Γ_V, -) = 0` and `H²(Γ_V ∩ I_V(t), -) = 0` at `V` (`h2All_closed` for the closed
  subgroups `Γ ∩ K` and `K ∩ x_t (Γ ∩ I_s) x_t⁻¹`, then `h2All_subgroupOf`);
* **`hcount_S3`**: `H²(K)(ρ) ≃ H²_c(ρ)` at `V` for every finite `ρ` with open kernel: a finer unramified cover `L` with
  `ker(π₁ ↠ Gal(L/F)) ⊆ ker ρ` (`exists_resL_ker_le`), its residue data (`exists_resDat_tw`), then `vCount`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

open CurveCoh Kummer CP4a Residue PerfectCx
open scoped Pointwise Polynomial

attribute [local instance] GalCover.grp GalCover.fG

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

omit [DecidableEq (RatFunc Fq)] in
/-- Open normal subgroups form a basis at `1` in `π₁(U)`. -/
theorem hbasis_S3 : ∀ U : Set (Pi1 (Places.Rfin Fq F) F), IsOpen U → (1 : Pi1 (Places.Rfin Fq F) F) ∈ U →
    ∃ N : Subgroup (Pi1 (Places.Rfin Fq F) F), N.Normal ∧ IsOpen (N : Set (Pi1 (Places.Rfin Fq F) F)) ∧
      (N : Set (Pi1 (Places.Rfin Fq F) F)) ⊆ U := by
  intro U hU h1U
  obtain ⟨E, hfin, hE⟩ := (krullTopology_mem_nhds_one_iff F (maxUnram (Places.Rfin Fq F) F) U).mp
    (hU.mem_nhds h1U)
  have := hfin
  obtain ⟨N, hNn, hNo, hNE⟩ := CdOne.exists_openNormal_le E.fixingSubgroup E.fixingSubgroup_isOpen
  exact ⟨N, hNn, hNo, fun g hg => hE (hNE hg)⟩

end S3

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VGysF =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 4: the right kernel vanishes, generic form

The arguments of GysB (`uniFam_eq_zero`) and GysF (`inR_eq_zero`) with their two S3-chart inputs made hypotheses,
so that they apply at the cover `V` (ambient group `K`):
* `hcount`: `H²(K)(ρ) ≃ H²_c(ρ)` for every finite representation `ρ` on `(ι → Λ)²` with open kernel;
* `hbasis` (open normal subgroups form a basis at `1`) and `hdens` (`G = φ^ℕ · Γ · N` for open `N`).
**`uniFam_eq_zero_of_count`**, **`inR_eq_zero_gen`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

noncomputable section

open CurveCoh PerfectCx

variable {Λ : Type} [CommRing Λ] [Finite Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation Λ G Λ} {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

/-- **GysB, generic.** A parabolic unipotent family in the right kernel of `constPair` vanishes, given the count. -/
theorem uniFam_eq_zero_of_count (H : CupHyp (Representation.trivial Λ G Λ) σ σ (LinearMap.mul Λ Λ) Γ)
    (DD : ConstData σ Γ I t) {ι : Type} [Fintype ι] (ρ : Representation Λ G ((ι → Λ) × (ι → Λ)))
    (hρ : IsOpen (ρ.ker : Set G)) (hcount : Nonempty (H2K ρ Γ I hρ ≃ₗ[Λ] H2c ρ Γ))
    {d : ι → Γ → Λ} (hρΓ : IsUniFam ρ d) (hpar : ∀ i s (g : Γ), (g : G) ∈ I s → d i g = 0)
    (hd : ∀ i, d i ∈ Z1 σ Γ)
    (hR : ∀ i (p : Z1c (Representation.trivial Λ G Λ) Γ I),
      constPair H DD (H1c.mk (Representation.trivial Λ G Λ) Γ I p) (H1.mk σ Γ ⟨d i, hd i⟩) = 0) :
    ∀ i g, d i g = 0 := by
  classical
  by_contra hne
  simp only [not_forall] at hne
  obtain ⟨i, g, hg⟩ := hne
  obtain ⟨E⟩ := hcount
  have : Finite (H2c ρ Γ) := Finite.of_surjective _ (Representation.Coinvariants.mk_surjective _)
  have : Finite (H2K ρ Γ I hρ) := Finite.of_equiv _ E.toEquiv.symm
  have h1 := card_sq_le_h2K H DD hρ hρΓ hpar hd hR
  have h2 := card_coinv_lt hρΓ hg
  rw [Nat.card_congr E.toEquiv] at h1
  rw [Nat.card_prod] at h2
  omega

set_option maxHeartbeats 800000 in
/-- **GysF, generic.** A parabolic hom in the right kernel of `constPair` is zero. -/
theorem inR_eq_zero_gen [CompactSpace G] [Γ.Normal] (htriv : ∀ (g : Γ) (x : Λ), σ g x = x)
    (H : CupHyp (Representation.trivial Λ G Λ) σ σ (LinearMap.mul Λ Λ) Γ) (DD : ConstData σ Γ I t)
    (hcount : ∀ {ι : Type} [Fintype ι] (ρ : Representation Λ G ((ι → Λ) × (ι → Λ)))
      (hρ : IsOpen (ρ.ker : Set G)), Nonempty (H2K ρ Γ I hρ ≃ₗ[Λ] H2c ρ Γ))
    (hbasis : ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧ (N : Set G) ⊆ U)
    {φ : G} (hdens : ∀ N : Subgroup G, IsOpen (N : Set G) → ∀ r : G,
      ∃ j : ℕ, ∃ γ ∈ Γ, ∃ m ∈ N, r = φ ^ j * γ * m)
    {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I φ⁻¹ τ h) {τ2 : S → S} {h2 : S → Γ}
    (hI2 : BdryCompat Γ I φ τ2 h2) {c : Λ} (hc : IsUnit c)
    (hF : ∀ x y, constPair H DD (frobH1c (Representation.trivial Λ G Λ) Γ I φ⁻¹ τ h hI x) (frobH1 σ Γ φ⁻¹ y) =
      c * constPair H DD x y)
    {d : Γ → Λ} (hR : InR H DD d) : d = 0 := by
  classical
  obtain ⟨hd, hpar, hker⟩ := hR
  have hadd := add_of_Z1 htriv hd
  obtain ⟨N, hNn, hNo, hdN⟩ : ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧
      ∀ g : Γ, (g : G) ∈ N → d g = 0 := by
    obtain ⟨U, hU, hUd⟩ := isOpen_induced_iff.mp (hd.1.isOpen_fiber 0)
    have h1U : (1 : G) ∈ U := by
      have : (1 : Γ) ∈ Subtype.val ⁻¹' U := by
        rw [hUd]
        exact d_one hadd
      exact this
    obtain ⟨N, hNn, hNo, hNU⟩ := hbasis U hU h1U
    refine ⟨N, hNn, hNo, fun g hg => ?_⟩
    have hg' : g ∈ Subtype.val ⁻¹' U := hNU hg
    rw [hUd] at hg'
    exact hg'
  have : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  have : Finite (Cos Γ N) := Finite.of_surjective _ QuotientGroup.mk_surjective
  let _ : Fintype (Cos Γ N) := Fintype.ofFinite _
  have hRi : ∀ i : Cos Γ N, InR H DD (fun g : Γ =>
      d ⟨repG Γ N i * g * (repG Γ N i)⁻¹, Subgroup.Normal.conj_mem inferInstance _ g.2 _⟩) := by
    intro i
    obtain ⟨j, γ, hγ, m, hm, hψ⟩ := hdens N hNo (repG Γ N i)⁻¹
    have e : (fun g : Γ => d ⟨repG Γ N i * g * (repG Γ N i)⁻¹, Subgroup.Normal.conj_mem inferInstance _ g.2 _⟩) =
        fun g => d (conjΓ Γ (φ ^ j) g) := by
      funext g
      rw [← d_conj_mul htriv hd N hdN (φ ^ j) hγ hm g]
      congr 1
      apply Subtype.ext
      rw [conjΓ_val, ← hψ, inv_inv]
    rw [e]
    exact inR_conj_pow H DD htriv hI hI2 hc hF j ⟨hd, hpar, hker⟩
  have hall := uniFam_eq_zero_of_count H DD (rhoV Γ N hadd hdN)
    (Subgroup.isOpen_mono (le_ker_rhoV _ N hadd hdN) hNo) (hcount _ _) (isUniFam_rhoV _ N hadd hdN)
    (fun i => (hRi i).2.1) (fun i => (hRi i).1) (fun i _ => (hRi i).2.2 _)
  funext g0
  obtain ⟨i0⟩ : Nonempty (Cos Γ N) := ⟨QuotientGroup.mk 1⟩
  have hmem : (repG Γ N i0)⁻¹ * (g0 : G) * repG Γ N i0 ∈ Γ := by
    have := (inferInstance : Γ.Normal).conj_mem _ g0.2 (repG Γ N i0)⁻¹
    rwa [inv_inv] at this
  have h := hall i0 ⟨_, hmem⟩
  rw [Pi.zero_apply]
  convert h using 2
  apply Subtype.ext
  dsimp only
  group

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VPerfG =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 7: the parabolic block is perfect, generic form

For a compact ambient group `G` (at `V`: `K`), the constant data `H0`, `D0` over `ℤ/lⁿ` (trivial on `Γ`) and any
`HΛ`, `DΛ` with the same generators `t`: if
* `H²(K) ≃ H²_c` for every finite representation with open kernel (`hcount`),
* open normal subgroups form a basis at `1` (`hbasis`) and `G = φ^ℕ · Γ · N` for open `N` (`hdens`),
* `φ⁻¹` has boundary data with EXACT conjugation and bijective `τ` (`hI`, `hτ`, `hex`), `φ` has boundary data `hI2`,
* the `ℤ/l`-valued parabolic homomorphisms are finite,
then the parabolic block of `constPair HΛ DΛ` is perfect (**`parabolic_of_count`**): the Frobenius scalar is a unit
(`constPair_frob_unit`), so the right kernel over `ℤ/lⁿ` vanishes (`inR_eq_zero_gen`), and `parabolic_of_finite`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G} [Γ.Normal]
  {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

/-- **O9b, generic.** The parabolic block over `Λ` is perfect, from the count, density and boundary data. -/
theorem parabolic_of_count [CompactSpace G] {l n : ℕ} [Fact l.Prime] (hn : n ≠ 0) {Λ : Type} [CommRing Λ]
    (ιΛ : ZMod (l ^ n) →+* Λ) {σ0 : Representation (ZMod (l ^ n)) G (ZMod (l ^ n))} {σΛ : Representation Λ G Λ}
    (H0 : CupHyp (Representation.trivial (ZMod (l ^ n)) G (ZMod (l ^ n))) σ0 σ0
      (LinearMap.mul (ZMod (l ^ n)) (ZMod (l ^ n))) Γ)
    (D0 : ConstData σ0 Γ I t)
    (HΛ : CupHyp (Representation.trivial Λ G Λ) σΛ σΛ (LinearMap.mul Λ Λ) Γ) (DΛ : ConstData σΛ Γ I t)
    [Finite ↥(parMod Γ I l)] (htriv : ∀ (g : Γ) (x : ZMod (l ^ n)), σ0 g x = x)
    (hcount : ∀ {ι : Type} [Fintype ι] (ρ : Representation (ZMod (l ^ n)) G ((ι → ZMod (l ^ n)) × (ι → ZMod (l ^ n))))
      (hρ : IsOpen (ρ.ker : Set G)), Nonempty (H2K ρ Γ I hρ ≃ₗ[ZMod (l ^ n)] H2c ρ Γ))
    (hbasis : ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧ (N : Set G) ⊆ U)
    {φ : G} (hdens : ∀ N : Subgroup G, IsOpen (N : Set G) → ∀ r : G,
      ∃ j : ℕ, ∃ γ ∈ Γ, ∃ m ∈ N, r = φ ^ j * γ * m)
    {τ : S → S} {h : S → Γ} (hI : BdryCompat Γ I φ⁻¹ τ h) (hτ : Function.Bijective τ)
    (hex : ∀ s (g : G), g ∈ Γ → g ∈ I (τ s) → (φ⁻¹ * h s) * g * (φ⁻¹ * h s)⁻¹ ∈ I s)
    {τ2 : S → S} {h2 : S → Γ} (hI2 : BdryCompat Γ I φ τ2 h2) :
    (pairQuotSub (constPair HΛ DΛ) _ _ (constPair_h0 HΛ DΛ)).IsPerfPair := by
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨c, hc, hF⟩ := constPair_frob_unit H0 D0 hI hτ hex
  exact parabolic_of_finite hn ιΛ H0 D0 HΛ DΛ (fun d hd =>
    inR_eq_zero_gen htriv H0 D0 hcount hbasis hdens hI hI2 hc hF hd)

end

end RamanujanPetersson.CupDuality


end


