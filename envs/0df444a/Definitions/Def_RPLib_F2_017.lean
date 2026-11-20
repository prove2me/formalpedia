-- Prove2me | Definitions.Def_RPLib_F2_017
-- name    : RPLib_F2_017
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T09:41:33.917355+00:00
-- url     : https://prove2.me/theorems/701b77c4-088d-4b1d-9c5a-85bc90db3400
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 017 of 70
-- statement:
--   File 017 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_PerfectCx_Z1Ex`: S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`
--   * `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
--   * `S4.Def_RP_IntersectC_Pit`: S4-IntersectC, file Pit: Krull's height theorem on a scheme (L36, O8)
--   * `S4.Def_RP_IntersectC_Dense`: S4-IntersectC, file Dense: translates of a separating divisor are dense (L36, O7)
--   * `S4.Def_RP_ThetaSquare_CPullOpen`: S4-ThetaSquare, file CPullOpen: `cpull` along open immersions, and monotonicity (F4)
--   * `S4.Def_RP_ThetaSquare_Plus`: Unit S4-ThetaSquare, file Plus: the plus-curve on coordinate rings
--   * `S4.Def_RP_ThetaSquare_PlusC`: Unit S4-ThetaSquare, file PlusC: the ring `R1 = B_{c0}[1/x'] = Rfin[1/(x - c0)]`
--   * `S4.Def_RP_ThetaSquare_PlusJ`: Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula
--   * `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
--   * `S4.Def_RP_ThetaSquare_Mult1`: Unit S4-ThetaSquare, file Mult1: local algebra for the multiplicity-one count (F6a)
--   * `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
--   * `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
--   * `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
--   * `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
--   * `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
--   * `S4.Def_RP_ThetaSquare_Curve9`: Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)
--   * `S4.Def_RP_IsogDegB_Frob`: S4-IsogDegB, Frobenius-type endomorphisms (lemma L28 of S4_COREB_ROUTE.md §3)
--   * `S4.Def_RP_ThetaCube_Deg`: S4-ThetaCube, T8a: the inputs `hD` and `hproj` of DegPoly for the theta divisor
--   * `S4.Def_RP_ThetaCube_Zero`: S4-ThetaCube, T8z: the input `hzero` of DegPoly for the theta divisor
--   * `S4.Def_RP_ThetaCube_Cube`: S4-ThetaCube, file Cube (T5a): numerical triviality of pulled-back principal multiples
--   * `S4.Def_RP_ThetaCube_Line`: S4-ThetaCube, file Line (D-A, part LT1): the curve test for Weil divisors
--   * `S4.Def_RP_ThetaCube_Lines`: S4-ThetaCube, file Lines (D-A, part LP1): coordinate lines in `X1^n` and the open projection
--   * `S4.Def_RP_ThetaCube_Reach`: S4-ThetaCube, file Reach (D-A, part (R)): reachability by coordinate lines in `X1^n`
--   * `S4.Def_RP_JacSymB_Coord`: S4-JacSymB, file D: a coordinate that is étale at finitely many points
--   * `S4.Def_RP_JacSymB_Ker2`: S4-JacSymB, file E1: functions vanishing to high order along the fibre lie in `M^2`
--   * `S4.Def_RP_JacSymB_Height`: S4-JacSymB, file E2: every maximal ideal of `Sym^g X` has height at least `g`
--   * `S4.Def_RP_JacSymB_Reg`: S4-JacSymB, file E3: `Sym^g` of a smooth affine curve is regular at closed points (L11)
--   * `S4.Def_RP_JacSymB`: S4-JacSymB umbrella: `Sym^g A^1 = A^g`, regularity of `Sym^g` of a smooth curve, `Sym^g X` glued and proper
--   * `S4.Def_RP_ThetaCube_Cover`: S4-ThetaCube, file Cover (D-A, rest): the line test on `X1^n`
--   * `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
--   * `S4.Def_RP_ThetaCube_Surj`: S4-ThetaCube, file Surj (D-C2): a surjection from `X1^n` detects Weil divisors by lines
--   * `S4.Def_RP_ThetaCube_SmPP`: S4-ThetaCube, file SmPP (D-B0, part 2): `X1` and `X1^n` are smooth, so their stalks are factorial
--   * `S4.Def_RP_ThetaCube_FF`: S4-ThetaCube, file FF (D-B1, part 1): the function field of `X1` is `F`
--   * `S4.Def_RP_ThetaCube_Ord`: S4-ThetaCube, file Ord (D-B1, part 2): orders of vanishing on `X1` are the place orders
--   * `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
--   * `S4.Def_RP_ThetaCube_Cof`: S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
--   * `S4.Def_RP_ThetaCube_Eff`: S4-ThetaCube, file Eff (D-B3, part 2): the residual divisor of a slice of `det_k`
--   * `S4.Def_RP_ThetaCube_Rank`: S4-ThetaCube, file Rank (D-B4, part 1): the slices do not vanish
--   * `S4.Def_RP_ThetaCube_NZ`: S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
--   * `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
--   * `S4.Def_RP_ThetaCube_Asm1`: S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
--   * `S4.Def_RP_ThetaCube_Val`: S4-ThetaCube, file Val (D-C1, part 1): values of rational functions at `K`-points
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_016

/-!
# Ramanujan-Petersson curve library (flat edition), file 017 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_PerfectCx_Z1Ex`: S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`
* `S4.Def_RP_ThetaSquare_Pts`: Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`
* `S4.Def_RP_IntersectC_Pit`: S4-IntersectC, file Pit: Krull's height theorem on a scheme (L36, O8)
* `S4.Def_RP_IntersectC_Dense`: S4-IntersectC, file Dense: translates of a separating divisor are dense (L36, O7)
* `S4.Def_RP_ThetaSquare_CPullOpen`: S4-ThetaSquare, file CPullOpen: `cpull` along open immersions, and monotonicity (F4)
* `S4.Def_RP_ThetaSquare_Plus`: Unit S4-ThetaSquare, file Plus: the plus-curve on coordinate rings
* `S4.Def_RP_ThetaSquare_PlusC`: Unit S4-ThetaSquare, file PlusC: the ring `R1 = B_{c0}[1/x'] = Rfin[1/(x - c0)]`
* `S4.Def_RP_ThetaSquare_PlusJ`: Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula
* `S4.Def_RP_ThetaSquare_PlusX`: Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map
* `S4.Def_RP_ThetaSquare_Mult1`: Unit S4-ThetaSquare, file Mult1: local algebra for the multiplicity-one count (F6a)
* `S4.Def_RP_ThetaSquare_Mult2`: Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)
* `S4.Def_RP_ThetaSquare_Curve1`: Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)
* `S4.Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
* `S4.Def_RP_ThetaSquare_Curve4`: Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))
* `S4.Def_RP_ThetaSquare_Curve6`: Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)
* `S4.Def_RP_ThetaSquare_Curve9`: Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)
* `S4.Def_RP_IsogDegB_Frob`: S4-IsogDegB, Frobenius-type endomorphisms (lemma L28 of S4_COREB_ROUTE.md §3)
* `S4.Def_RP_ThetaCube_Deg`: S4-ThetaCube, T8a: the inputs `hD` and `hproj` of DegPoly for the theta divisor
* `S4.Def_RP_ThetaCube_Zero`: S4-ThetaCube, T8z: the input `hzero` of DegPoly for the theta divisor
* `S4.Def_RP_ThetaCube_Cube`: S4-ThetaCube, file Cube (T5a): numerical triviality of pulled-back principal multiples
* `S4.Def_RP_ThetaCube_Line`: S4-ThetaCube, file Line (D-A, part LT1): the curve test for Weil divisors
* `S4.Def_RP_ThetaCube_Lines`: S4-ThetaCube, file Lines (D-A, part LP1): coordinate lines in `X1^n` and the open projection
* `S4.Def_RP_ThetaCube_Reach`: S4-ThetaCube, file Reach (D-A, part (R)): reachability by coordinate lines in `X1^n`
* `S4.Def_RP_JacSymB_Coord`: S4-JacSymB, file D: a coordinate that is étale at finitely many points
* `S4.Def_RP_JacSymB_Ker2`: S4-JacSymB, file E1: functions vanishing to high order along the fibre lie in `M^2`
* `S4.Def_RP_JacSymB_Height`: S4-JacSymB, file E2: every maximal ideal of `Sym^g X` has height at least `g`
* `S4.Def_RP_JacSymB_Reg`: S4-JacSymB, file E3: `Sym^g` of a smooth affine curve is regular at closed points (L11)
* `S4.Def_RP_JacSymB`: S4-JacSymB umbrella: `Sym^g A^1 = A^g`, regularity of `Sym^g` of a smooth curve, `Sym^g X` glued and proper
* `S4.Def_RP_ThetaCube_Cover`: S4-ThetaCube, file Cover (D-A, rest): the line test on `X1^n`
* `S4.Def_RP_ThetaCube_Sym`: S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`
* `S4.Def_RP_ThetaCube_Surj`: S4-ThetaCube, file Surj (D-C2): a surjection from `X1^n` detects Weil divisors by lines
* `S4.Def_RP_ThetaCube_SmPP`: S4-ThetaCube, file SmPP (D-B0, part 2): `X1` and `X1^n` are smooth, so their stalks are factorial
* `S4.Def_RP_ThetaCube_FF`: S4-ThetaCube, file FF (D-B1, part 1): the function field of `X1` is `F`
* `S4.Def_RP_ThetaCube_Ord`: S4-ThetaCube, file Ord (D-B1, part 2): orders of vanishing on `X1` are the place orders
* `S4.Def_RP_ThetaCube_Slice`: S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `S4.Def_RP_ThetaCube_Cof`: S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
* `S4.Def_RP_ThetaCube_Eff`: S4-ThetaCube, file Eff (D-B3, part 2): the residual divisor of a slice of `det_k`
* `S4.Def_RP_ThetaCube_Rank`: S4-ThetaCube, file Rank (D-B4, part 1): the slices do not vanish
* `S4.Def_RP_ThetaCube_NZ`: S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
* `S4.Def_RP_ThetaCube_Good`: S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `S4.Def_RP_ThetaCube_Asm1`: S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
* `S4.Def_RP_ThetaCube_Val`: S4-ThetaCube, file Val (D-C1, part 1): values of rational functions at `K`-points
-/

set_option autoImplicit false

-- ===== S4.Def_RP_PerfectCx_Z1Ex =====
section

/-!
# S4-PD (5), E2.1: locally constant 1-cocycles are exact under `H² = 0`

For a subgroup `Γ` of a topological group `G` and representations `ρ`, `σ` of `G`, an equivariant linear map
`q : M → N` induces `z1Map : Z¹(Γ, M) → Z¹(Γ, N)` (locally constant cocycles, the `S4-CurveCoh` convention).

* `H2Van ρ Γ K`: locally constant 2-cocycles with values in the submodule `K` are coboundaries of locally constant
  `K`-valued cochains (cochains on `Γ`, the `h2_eq_zero` shape);
* `z1Map_surjective`: if `q` is surjective and `H2Van` holds for `ker q`, then `z1Map` is surjective
  (lift a cocycle along a set-theoretic section, its coboundary lies in `ker q`, correct by a `ker q`-valued cochain);
* `H2All k G Γ l n`: `H² = 0` for every finite `lⁿ`-torsion representation with open kernel (the output shape of
  `h2_pi1geo_eq_zero` / `h2_closed_eq_zero`); `h2Van_of_all` passes it to subrepresentations, and
  `z1Map_surjective_of_all` is the exactness statement used for `E_Γ = Z¹(Γ; A)` and `E_s = Z¹(I_s; A)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N) (Γ : Subgroup G)

/-- `H²(Γ, K) = 0` for a submodule `K ≤ M`, phrased on `M`-valued cochains with values in `K`. -/
def H2Van (K : Submodule k M) : Prop :=
  ∀ f : Γ × Γ → M, IsLocallyConstant f → (∀ x, f x ∈ K) →
    (∀ g h j : Γ, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)) →
    ∃ b : Γ → M, IsLocallyConstant b ∧ (∀ g, b g ∈ K) ∧
      ∀ g h : Γ, f (g, h) = ρ g (b h) - b (g * h) + b g

end

end PerfectCx
end RamanujanPetersson


end

-- ===== S4.Def_RP_ThetaSquare_Pts =====
section

/-!
# Unit S4-ThetaSquare, file Pts: chart points of `J` and translates of `W_{g-1}`

Input for `coheight (zTheta P0) ≤ 1` (file `Codim`, Krull on the chart `X0`):
* `kJ yR`: the `K`-point of `J` at the closed point `yR` of `X0`; `pt_kJ` (it is `jX0 (kpt yR)`) and `cls_kJ`
  (its class is `[Zdiv A] - [Θ]`, `A` the `g` points of `yR`); `deg_thetaK : deg [Θ] = g`;
* `exists_cJ`: the `K`-point `c_φ` with class `[φ] + (g-1)[P0] - [Θ]`;
* `mem_W_of_cls`: a class `[Zdiv S] - (g-1)[P0]` with `#S = g-1` lies on `W`;
* `mem_transl_W`: if `φ` is one of the points of `yR`, then `jX0 (kpt yR) - c_φ ∈ W`;
* `finite_zeros`: a nonzero `u ∈ Rfin` has finitely many zeros.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB

universe u

section Pts

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- A nonzero `u ∈ Rfin` has finitely many zeros. -/
theorem finite_zeros {u : Rfin K F} (hu : u ≠ 0) : {φ : Rfin K F →ₐ[K] K | φ u = 0}.Finite := by
  have hI : Ideal.span {u} ≠ (0 : Ideal (Rfin K F)) := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine ((Ideal.finite_factors hI).preimage ptP_injective.injOn).subset fun φ hφ => ?_
  show (ptP φ).asIdeal ∣ Ideal.span {u}
  rw [Ideal.dvd_span_singleton]
  exact mem_ptP.2 hφ

end Pts

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_IntersectC_Pit =====
section

/-!
# S4-IntersectC, file Pit: Krull's height theorem on a scheme (L36, O8)

* `exists_gen_of_span`: if `J` is generated on an affine chart by `i` sections and `y` lies in
  its support with `i < coheight y`, some other point of the support generalizes `y`.
* `exists_span_of_iSup`: a finite sup of locally principal ideal sheaves is generated, near any
  point, by one section per term.
* `locPrin_comap_iso`: pulling back along an isomorphism keeps an ideal sheaf locally principal.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IntersectB

/-- **Krull** on a chart: a support point `y` of codimension `> i` of an ideal sheaf generated by `i`
sections has a proper generalization in the support. -/
theorem exists_gen_of_span {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (W : X.affineOpens) {y : X} (hyW : y ∈ (W : X.Opens)) {i : ℕ} (v : Fin i → Γ(X, W))
    (hv : J.ideal W = Ideal.span (Set.range v)) (hy : y ∈ (J.support : Set X))
    (hi : (i : ℕ∞) < Order.coheight y) :
    ∃ z ∈ (J.support : Set X), z ≠ y ∧ z ⤳ y := by
  classical
  have hW := W.2
  have := hW.isOpenImmersion_fromSpec
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  set m := hW.primeIdealOf ⟨y, hyW⟩ with hm
  have hmy : hW.fromSpec m = y := hW.fromSpec_primeIdealOf ⟨y, hyW⟩
  have hmem : ∀ q, hW.fromSpec q ∈ (W : X.Opens) := fun q => by
    have h := Set.mem_range_self (f := hW.fromSpec) q
    rw [hW.range_fromSpec] at h
    exact h
  have hsupp : ∀ q : PrimeSpectrum Γ(X, W),
      hW.fromSpec q ∈ (J.support : Set X) ↔ J.ideal W ≤ q.asIdeal := by
    intro q
    change hW.fromSpec q ∈ J.support ↔ _
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (hmem q)]
    exact (Set.ext_iff.mp (hW.fromSpec_preimage_zeroLocus (J.ideal W : Set Γ(X, W))) q).trans
      ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)
  have hIm : J.ideal W ≤ m.asIdeal := (hsupp m).1 (hmy ▸ hy)
  obtain ⟨p, hpmin, hpm⟩ := Ideal.exists_minimalPrimes_le hIm
  have hpprime : p.IsPrime := hpmin.1.1
  have hpi : p.height ≤ i := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := Finset.univ.image v)
      (p := p) (by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← hv]; exact hpmin)
    have hc : (Finset.univ.image v).card ≤ i :=
      Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
    exact h1.trans (by exact_mod_cast hc)
  letI := X.presheaf.algebra_section_stalk (⟨y, hyW⟩ : (W : X.Opens))
  have hloc := hW.isLocalization_stalk ⟨y, hyW⟩
  have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal
    (X.presheaf.stalk ((⟨y, hyW⟩ : (W : X.Opens)) : X))
  have h2 := ringKrullDim_stalk_eq_coheight ((⟨y, hyW⟩ : (W : X.Opens)) : X)
  have hmh : m.asIdeal.height = Order.coheight y := WithBot.coe_inj.mp (h1.symm.trans h2)
  have hpm' : p ≠ m.asIdeal := by
    rintro rfl
    rw [hmh] at hpi
    exact absurd hi (not_lt.2 hpi)
  refine ⟨hW.fromSpec ⟨p, hpprime⟩, (hsupp _).2 hpmin.1.2, fun h => ?_, ?_⟩
  · rw [← hmy] at h
    exact hpm' (congrArg PrimeSpectrum.asIdeal (hW.fromSpec.isOpenEmbedding.injective h))
  · rw [← hmy]
    exact ((PrimeSpectrum.le_iff_specializes ⟨p, hpprime⟩ m).1 hpm).map hW.fromSpec.continuous

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_IntersectC_Dense =====
section

/-!
# S4-IntersectC, file Dense: translates of a separating divisor are dense (L36, O7)

* `mem_support_effI_of_pos`: a point with positive coefficient lies in `supp (effI D)`.
* `coheight_iso`: isomorphisms of schemes keep the codimension of points.
* `finite_coheight_one`: a proper closed subset of an irreducible Noetherian scheme has finitely many
  points of codimension one.
* `transl_dense`: if the right translates of `supp D` separate `k`-points, the left translates of
  `supp D` by any infinite set of `k`-points are dense.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB

section Top

variable {X : Scheme.{u}}

/-- Isomorphisms of schemes keep the codimension of points. -/
lemma coheight_iso {Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (x : X) :
    Order.coheight (f x) = Order.coheight x :=
  Topology.IsOpenEmbedding.coheight_eq (x := x) f f.isOpenEmbedding

/-- A codimension-one point of a proper closed subset is maximal in it. -/
lemma eq_of_coheight_one [IrreducibleSpace X] {S : Set X} (hS : IsClosed S) (hne : S ≠ Set.univ)
    {p q : X} (hp : Order.coheight p = 1) (hq : q ∈ S) (hqp : q ⤳ p) : q = p := by
  by_contra hne'
  have hη : genericPoint X ∉ S := fun h => hne (Set.eq_univ_of_forall fun x =>
    (genericPoint_specializes x).mem_closed hS h)
  have h1 : p < q := lt_of_le_not_ge hqp fun h => hne' (Specializes.antisymm (show p ⤳ q from h) hqp).eq.symm
  have h2 : q < genericPoint X := lt_of_le_not_ge (genericPoint_specializes q) fun h =>
    hη ((show q ⤳ genericPoint X from h).mem_closed hS hq)
  have hq1 : 1 ≤ Order.coheight q := le_trans le_add_self (Order.coheight_add_one_le h2)
  have h4 : (1 : ℕ∞) + 1 ≤ Order.coheight q + 1 := by gcongr
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := h4.trans ((Order.coheight_add_one_le h1).trans hp.le)
  exact absurd h3 (by norm_num)

/-- A proper closed subset of an irreducible Noetherian scheme has finitely many codimension-one
points. -/
lemma finite_coheight_one [IrreducibleSpace X] [NoetherianSpace X] {S : Set X} (hS : IsClosed S)
    (hne : S ≠ Set.univ) : {p | p ∈ S ∧ Order.coheight p = 1}.Finite := by
  obtain ⟨T, hT, hST⟩ := NoetherianSpace.exists_finset_irreducible (⟨S, hS⟩ : Closeds X)
  refine (T.finite_toSet.biUnion fun C _ =>
    Set.Subsingleton.finite (s := {p | IsGenericPoint p (C : Set X)})
      fun x hx y hy => IsGenericPoint.eq hx hy).subset ?_
  rintro p ⟨hpS, hp⟩
  have hpT : p ∈ ((T.sup id : Closeds X) : Set X) := by rw [← hST]; exact hpS
  rw [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂] at hpT
  obtain ⟨C, hCT, hpC⟩ := hpT
  have hgen := (hT ⟨C, hCT⟩).isGenericPoint_genericPoint C.isClosed
  have hCS : (C : Set X) ⊆ S := fun x hx => by
    have h : C ≤ T.sup id := Finset.le_sup (f := id) hCT
    rw [← hST] at h
    exact SetLike.coe_subset_coe.mpr h hx
  refine Set.mem_biUnion hCT ?_
  rw [← eq_of_coheight_one hS hne hp (hCS hgen.mem) (hgen.specializes hpC)]
  exact hgen

end Top

section Dense

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

end Dense

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_ThetaSquare_CPullOpen =====
section

/-!
# S4-ThetaSquare, file CPullOpen: `cpull` along open immersions, and monotonicity (F4)

* `ringOrd_ringEquiv`: `Ring.ord` is invariant under ring isomorphisms.
* `ord_algebraMap_stalkMap`, `ord_ffMap_openImm`: an open immersion `ι` keeps orders of vanishing
  (`ord_x (ι^* h) = ord_{ι x} h`).
* `fpull_comp_left`, `avoid_comp_left`, **`cpull_comp_openImm`**: `cpull (ι ≫ f) D x = cpull f D (ι x)`.
* `isDominant_openImm`; `cpull_mono` (`D ≤ E` near `f x`) and `cpull_le_ord` (`D ≤ div g` near `f x`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace RamanujanPetersson.ThetaSquare

open AlgebraicGeometry CategoryTheory Order Topology IsLocalRing RamanujanPetersson.JacDivisors
  RamanujanPetersson.IsogDegA

universe u

/-- **`Ring.ord` is invariant under ring isomorphisms.** -/
lemma ringOrd_ringEquiv {R R' : Type u} [CommRing R] [CommRing R'] (e : R ≃+* R') (b : R) :
    Ring.ord R' (e b) = Ring.ord R b := by
  letI : Algebra R R' := e.toRingHom.toAlgebra
  have h1 : Module.length R (R' ⧸ Ideal.span {e b}) = Module.length R' (R' ⧸ Ideal.span {e b}) :=
    Module.length_eq_of_surjective e.surjective
  let f : R ≃ₐ[R] R' := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  have hJ : Ideal.span {e b} = (Ideal.span {b}).map (f : R →+* R') := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have h2 := (Ideal.quotientEquivAlg (Ideal.span {b}) (Ideal.span {e b}) f hJ).toLinearEquiv.length_eq
  exact h1.symm.trans h2.symm

/-- An open dense immersion: a nonempty open immersion into an irreducible scheme is dominant. -/
theorem isDominant_openImm {U C : Scheme.{u}} (ι : U ⟶ C) [IsOpenImmersion ι] [Nonempty U]
    [IrreducibleSpace C] : IsDominant ι :=
  ⟨ι.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

section
variable {U C : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsIntegral C] [IsLocallyNoetherian C]
  (ι : U ⟶ C) [IsOpenImmersion ι]

variable [IsDominant ι]

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (f : C ⟶ Y)

variable [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

end

section
variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

end

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Plus =====
section

/-!
# Unit S4-ThetaSquare, file Plus: the plus-curve on coordinate rings

For a `g`-tuple `a` of `k`-points of `B` and a slot `i0`, `plusMap a i0 : Sym^g B → R` sends a symmetric tensor to its
value at `(a_1, .., P, .., a_g)` with the generic point `P` of `B` in slot `i0`, where `ι : B →ₐ R` is any map
(the inclusion of the curve's coordinate ring in a larger chart ring). On `R`-points it is
`y ∘ plusMap = symPt (update a i0 (y ∘ ι))` (`comp_plusMap`), and on norms
`plusMap (Nm w) = ι w * ∏_{i ≠ i0} a_i(w)` (`plusMap_normS`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.JacSym

section PlusRing

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {R : Type*} [CommRing R] [Algebra k R]
  {R' : Type*} [CommRing R'] [Algebra k R'] {g : ℕ}

/-- The multilinear map `(b_i) ↦ ∏ a_i (b_i)` with values in a `k`-algebra `R`. -/
noncomputable def ptMLR (a : Fin g → (B →ₐ[k] R)) : MultilinearMap k (fun _ : Fin g => B) R :=
  (MultilinearMap.mkPiAlgebra k (Fin g) R).compLinearMap (fun i => (a i).toLinearMap)

theorem ptMLR_apply (a : Fin g → (B →ₐ[k] R)) (b : Fin g → B) : ptMLR a b = ∏ i, a i (b i) := by
  simp [ptMLR, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- `b_1 ⊗ ... ⊗ b_g ↦ ∏ a_i (b_i)` as an algebra map `X^g → R`. -/
noncomputable def ptOfR (a : Fin g → (B →ₐ[k] R)) : XPow k B g →ₐ[k] R :=
  PiTensorProduct.liftAlgHom (ptMLR a) (by rw [ptMLR_apply]; simp)
    (fun x y => by rw [ptMLR_apply, ptMLR_apply, ptMLR_apply, ← Finset.prod_mul_distrib]; simp)

@[simp] theorem ptOfR_tprod (a : Fin g → (B →ₐ[k] R)) (b : Fin g → B) :
    ptOfR a (PiTensorProduct.tprod k b) = ∏ i, a i (b i) := by
  rw [ptOfR, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod, ptMLR_apply]

theorem ptOfR_comp_inc (a : Fin g → (B →ₐ[k] R)) (i : Fin g) : (ptOfR a).comp (inc i) = a i := by
  ext b
  simp only [inc, AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply, ptOfR_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem ptOfR_inc (a : Fin g → (B →ₐ[k] R)) (i : Fin g) (b : B) : ptOfR a (inc i b) = a i b :=
  AlgHom.congr_fun (ptOfR_comp_inc a i) b

theorem comp_ptOfR (φ : R →ₐ[k] R') (a : Fin g → (B →ₐ[k] R)) :
    φ.comp (ptOfR a) = ptOfR (fun i => φ.comp (a i)) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change φ.comp ((ptOfR a).comp (inc i)) = (ptOfR _).comp (inc i)
  rw [ptOfR_comp_inc, ptOfR_comp_inc]

theorem ptOfR_eq_ptOf (a : Fin g → (B →ₐ[k] k)) : ptOfR a = ptOf a := by
  apply PiTensorProduct.algHom_ext
  intro i
  change (ptOfR a).comp (inc i) = (ptOf a).comp (inc i)
  rw [ptOfR_comp_inc, ptOf_inc]

/-- The tuple `a` with slot `i0` replaced by `ι : B →ₐ R` (the other slots are the constants `a i`). -/
noncomputable def plusTuple (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) : Fin g → (B →ₐ[k] R) :=
  Function.update (fun i => (Algebra.ofId k R).comp (a i)) i0 ι

theorem plusTuple_apply (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 l : Fin g) (w : B) :
    plusTuple ι a i0 l w = if l = i0 then ι w else algebraMap k R (a l w) := by
  by_cases h : l = i0
  · subst h; simp [plusTuple]
  · simp [plusTuple, h]

/-- **The plus-curve on coordinate rings**: `Sym^g B → R`, `x ↦ x(a_1, .., P, .., a_g)` (`P` in slot `i0`). -/
noncomputable def plusMap (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) : SymRing k B g →ₐ[k] R :=
  (ptOfR (plusTuple ι a i0)).comp (SymRing k B g).val

theorem plusMap_apply (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) (x : SymRing k B g) :
    plusMap ι a i0 x = ptOfR (plusTuple ι a i0) (x : XPow k B g) := rfl

/-- `R`-points of the plus-curve: `y ∘ plusMap = symPt (update a i0 (y ∘ ι))`. -/
theorem comp_plusMap (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) (y : R →ₐ[k] k) :
    y.comp (plusMap ι a i0) = symPt (Function.update a i0 (y.comp ι)) := by
  have h : y.comp (ptOfR (plusTuple ι a i0)) = ptOf (Function.update a i0 (y.comp ι)) := by
    rw [comp_ptOfR, ← ptOfR_eq_ptOf]
    congr 1
    funext i
    by_cases hi : i = i0
    · subst hi; simp [plusTuple]
    · rw [Function.update_of_ne hi]
      simp only [plusTuple, Function.update_of_ne hi]
      ext b
      simp only [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply]
  ext x
  change y (ptOfR (plusTuple ι a i0) (x : XPow k B g)) = ptOf _ (x : XPow k B g)
  rw [← h]
  rfl

theorem plusMap_normS (ι : B →ₐ[k] R) (a : Fin g → (B →ₐ[k] k)) (i0 : Fin g) (w : B) :
    plusMap ι a i0 (normS k w) = ι w * ∏ i ∈ Finset.univ.erase i0, algebraMap k R (a i w) := by
  rw [plusMap_apply, normS_coe, map_prod]
  simp only [ptOfR_inc]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i0), plusTuple_apply, if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [plusTuple_apply, if_neg (Finset.ne_of_mem_erase hl)]

end PlusRing

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_PlusC =====
section

/-!
# Unit S4-ThetaSquare, file PlusC: the ring `R1 = B_{c0}[1/x'] = Rfin[1/(x - c0)]`

The plus-curve is placed on `R1 c0 := B_{c0} ⊔ Rfin ⊆ F`, which is both the localization of the chart ring
`B_{c0}` at `x' = 1/(x - c0)` (`isLocalization_bc_R1`) and the localization of `Rfin` at `x - c0`
(`isLocalization_rfin_R1`); both inclusions are open immersions on spectra. Also `Sym¹ B ≃ B` (`sym1Equiv`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial AlgebraicGeometry

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete

universe u

section Sym1

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-- `Sym¹ B → B`, the inverse of `diag1`. -/
noncomputable def undiag1 : SymRing k B 1 →ₐ[k] B :=
  (ptOfR (fun _ : Fin 1 => AlgHom.id k B)).comp (SymRing k B 1).val

theorem undiag1_diag1 (b : B) : undiag1 (diag1 (k := k) b) = b := by
  change ptOfR _ (diag1 (k := k) b : XPow k B 1) = b
  rw [diag1_coe, ptOfR_inc]
  rfl

theorem inc_comp_ptOfR_id :
    (inc (k := k) (B := B) (g := 1) 0).comp (ptOfR (fun _ : Fin 1 => AlgHom.id k B)) =
      AlgHom.id k (XPow k B 1) := by
  apply PiTensorProduct.algHom_ext
  intro i
  rw [Subsingleton.elim i 0]
  change ((inc 0).comp (ptOfR (fun _ : Fin 1 => AlgHom.id k B))).comp (inc 0) = (AlgHom.id k _).comp (inc 0)
  rw [AlgHom.comp_assoc, ptOfR_comp_inc, AlgHom.comp_id, AlgHom.id_comp]

theorem diag1_undiag1 (x : SymRing k B 1) : diag1 (undiag1 x) = x := by
  apply Subtype.ext
  rw [diag1_coe]
  change ((inc 0).comp (ptOfR (fun _ : Fin 1 => AlgHom.id k B))) (x : XPow k B 1) = _
  rw [inc_comp_ptOfR_id]
  rfl

/-- **`Sym¹ B ≃ B`.** -/
noncomputable def sym1Equiv : SymRing k B 1 ≃ₐ[k] B :=
  AlgEquiv.ofAlgHom undiag1 diag1 (AlgHom.ext undiag1_diag1) (AlgHom.ext diag1_undiag1)

@[simp] theorem sym1Equiv_apply (x : SymRing k B 1) : sym1Equiv x = undiag1 x := rfl

@[simp] theorem sym1Equiv_symm_apply (b : B) : sym1Equiv.symm b = diag1 (k := k) b := rfl

end Sym1

section PlusC

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

variable (F) in
/-- The chart ring `B_{c0}` of the curve. -/
noncomputable abbrev Bc : Subalgebra K F := chartRing (algebraMap K[X] F X) {c0}

variable (F) in
/-- **`R1 = B_{c0}[1/x'] = Rfin[1/(x - c0)]`** inside `F`. -/
noncomputable def R1 : Subalgebra K F := Bc F c0 ⊔ (FunctionField.ringOfIntegers K F).restrictScalars K

theorem bc_le_R1 : Bc F c0 ≤ R1 F c0 := le_sup_left

theorem rfin_mem_R1 (w : Rfin K F) : (w : F) ∈ R1 F c0 :=
  (le_sup_right : (FunctionField.ringOfIntegers K F).restrictScalars K ≤ R1 F c0) w.2

/-- `B_{c0} → R1`. -/
noncomputable def inclB : Bc F c0 →ₐ[K] R1 F c0 := Subalgebra.inclusion (bc_le_R1 c0)

/-- `Rfin → R1`. -/
noncomputable def inclR : Rfin K F →ₐ[K] R1 F c0 :=
  (IsScalarTower.toAlgHom K (Rfin K F) F).codRestrict (R1 F c0) (rfin_mem_R1 c0)

@[simp] theorem coe_inclB (b : Bc F c0) : ((inclB c0 b : R1 F c0) : F) = b := rfl

@[simp] theorem coe_inclR (w : Rfin K F) : ((inclR c0 w : R1 F c0) : F) = w := rfl

noncomputable instance algBR1 : Algebra (Bc F c0) (R1 F c0) := (inclB c0).toRingHom.toAlgebra

noncomputable instance algRR1 : Algebra (Rfin K F) (R1 F c0) := (inclR c0).toRingHom.toAlgebra

@[simp] theorem algebraMap_bc_R1 (b : Bc F c0) : algebraMap (Bc F c0) (R1 F c0) b = inclB c0 b := rfl

@[simp] theorem algebraMap_rfin_R1 (w : Rfin K F) : algebraMap (Rfin K F) (R1 F c0) w = inclR c0 w := rfl

variable (F) in
/-- `x' = 1/(x - c0)` in `B_{c0}`. -/
noncomputable def uc0 : Bc F c0 :=
  ⟨uc (algebraMap K[X] F X) c0, polyA_le_chartRing _ _ (uc_mem_polyA _ (Finset.mem_singleton_self c0))⟩

@[simp] theorem coe_uc0 : ((uc0 F c0 : Bc F c0) : F) = uc (algebraMap K[X] F X) c0 := rfl

variable (F) in
/-- `x - c0` in `Rfin`. -/
noncomputable def xcR : Rfin K F := algebraMap K[X] (Rfin K F) (X - C c0)

theorem coe_xcR : ((xcR F c0 : Rfin K F) : F) = algebraMap K[X] F X - algebraMap K F c0 := by
  change algebraMap K[X] F (X - C c0) = _
  rw [map_sub, IsScalarTower.algebraMap_apply K K[X] F c0, Polynomial.algebraMap_eq]

theorem uc_mem_bc : uc (algebraMap K[X] F X) c0 ∈ Bc F c0 := (uc0 F c0).2

/-- `R1 ⊆ B_{c0}[1/x']`. -/
theorem exists_uc_pow_mul_bc {z : F} (hz : z ∈ R1 F c0) :
    ∃ n : ℕ, uc (algebraMap K[X] F X) c0 ^ n * z ∈ Bc F c0 := by
  have hu := uc_mem_bc (F := F) c0
  rw [R1, Algebra.sup_def] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact ⟨0, by simpa using hz⟩
    · exact exists_uc_pow_mul_chartRing c0 ⟨z, hz⟩
  | algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem (Bc F c0) r⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have e : uc (algebraMap K[X] F X) c0 ^ (m + n) * (a + b) =
        uc (algebraMap K[X] F X) c0 ^ n * (uc (algebraMap K[X] F X) c0 ^ m * a) +
          uc (algebraMap K[X] F X) c0 ^ m * (uc (algebraMap K[X] F X) c0 ^ n * b) := by ring
    rw [e]
    exact add_mem (mul_mem (pow_mem hu n) hm) (mul_mem (pow_mem hu m) hn)
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    rw [pow_add, mul_mul_mul_comm]
    exact mul_mem hm hn

/-- `R1 ⊆ Rfin[1/(x - c0)]`. -/
theorem exists_sub_pow_mul_rfin_R1 {z : F} (hz : z ∈ R1 F c0) :
    ∃ n : ℕ, ∃ w : Rfin K F, (w : F) = (algebraMap K[X] F X - algebraMap K F c0) ^ n * z := by
  rw [R1, Algebra.sup_def] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact exists_sub_pow_mul_rfin c0 hz
    · exact ⟨0, ⟨z, hz⟩, by rw [pow_zero, one_mul]⟩
  | algebraMap r =>
    refine ⟨0, algebraMap K[X] (Rfin K F) (C r), ?_⟩
    rw [pow_zero, one_mul]
    change algebraMap K[X] F (C r) = _
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  | add a b _ _ ha hb =>
    obtain ⟨m, w1, hw1⟩ := ha
    obtain ⟨n, w2, hw2⟩ := hb
    refine ⟨m + n, xcR F c0 ^ n * w1 + xcR F c0 ^ m * w2, ?_⟩
    push_cast
    rw [coe_xcR, hw1, hw2]
    ring
  | mul a b _ _ ha hb =>
    obtain ⟨m, w1, hw1⟩ := ha
    obtain ⟨n, w2, hw2⟩ := hb
    refine ⟨m + n, w1 * w2, ?_⟩
    push_cast
    rw [hw1, hw2]
    ring

theorem uc_mul_xcR : (inclB c0 (uc0 F c0)) * inclR c0 (xcR F c0) = 1 := by
  apply Subtype.ext
  change uc (algebraMap K[X] F X) c0 * ((xcR F c0 : Rfin K F) : F) = 1
  rw [coe_xcR, uc_mul_sub]

/-- **`R1 = B_{c0}[1/x']`.** -/
instance isLocalization_bc_R1 : IsLocalization.Away (uc0 F c0) (R1 F c0) := by
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · exact IsUnit.of_mul_eq_one _ (uc_mul_xcR c0)
  · intro s
    obtain ⟨n, hn⟩ := exists_uc_pow_mul_bc c0 s.2
    refine ⟨n, ⟨_, hn⟩, Subtype.ext ?_⟩
    rw [algebraMap_bc_R1, algebraMap_bc_R1]
    push_cast
    rw [coe_inclB, coe_inclB, coe_uc0]
    ring
  · intro a b h
    refine ⟨0, ?_⟩
    have e0 := congrArg Subtype.val h
    have e : (a : F) = b := e0
    rw [Subtype.ext e]

/-- **`R1 = Rfin[1/(x - c0)]`.** -/
instance isLocalization_rfin_R1 : IsLocalization.Away (xcR F c0) (R1 F c0) := by
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans (uc_mul_xcR c0))
  · intro s
    obtain ⟨n, w, hw⟩ := exists_sub_pow_mul_rfin_R1 c0 s.2
    refine ⟨n, w, Subtype.ext ?_⟩
    rw [algebraMap_rfin_R1, algebraMap_rfin_R1]
    push_cast
    rw [coe_inclR, coe_inclR, hw, coe_xcR]
    ring
  · intro a b h
    refine ⟨0, ?_⟩
    have e0 := congrArg Subtype.val h
    have e : (a : F) = b := e0
    rw [Subtype.ext e]

theorem isOpenImmersion_bc_R1 :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (Bc F c0) (R1 F c0)))) :=
  IsOpenImmersion.of_isLocalization (uc0 F c0)

end PlusC

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_PlusJ =====
section

/-!
# Unit S4-ThetaSquare, file PlusJ: the plus-curve `Spec R2 → X0` and its class formula

For `g` points `a_i` of `Rfin` and a slot `i0`, `plusR = plusMap inclR a i0 : Sym^g Rfin → R1`; with `h = plusR(u0)`
and `R2 = R1[1/h]` it induces **`lawMapPlus : LawRing → R2`**, whose `K`-points have class
`[P] + [E] - [Θ]` (`psiJ_lawMapPlus`), `P` the point of `Rfin` under `x`, `E = Σ_{i ≠ i0} a_i` (`plusE`).
Also: the center of a `K`-point `y` of `R1` restricted to `B_{c0}` is the finite place of `y|Rfin` (`isCenter_R1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial AlgebraicGeometry

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete RamanujanPetersson.RR

universe u

section PlusJ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

variable [IsAlgClosed K]

theorem placeVal_inl_coe (P : HeightOneSpectrum (Rfin K F)) (w : Rfin K F) :
    placeVal (Sum.inl P : Place K F) (w : F) = P.valuation F (algebraMap (Rfin K F) F w) := rfl

theorem inclR_xcR_ne (y : R1 F c0 →ₐ[K] K) : y (inclR c0 (xcR F c0)) ≠ 0 := by
  intro h
  have e := congrArg y (uc_mul_xcR c0)
  rw [map_mul, h, mul_zero, map_one] at e
  exact zero_ne_one e

/-- **Centers on `R1`**: the center of `y|B_{c0}` is the finite place of `y|Rfin`. -/
theorem isCenter_R1 (y : R1 F c0 →ₐ[K] K) :
    IsCenter (Sum.inl (ptP (y.comp (inclR c0))) : Place K F) (y.comp (inclB c0)) := by
  have hxc : (ptP (y.comp (inclR c0))).valuation F (algebraMap (Rfin K F) F (xcR F c0)) = 1 := by
    refine le_antisymm (HeightOneSpectrum.valuation_le_one (K := F) (ptP (y.comp (inclR c0))) _) (not_lt.1 fun hlt => ?_)
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), mem_ptP] at hlt
    exact inclR_xcR_ne c0 y hlt
  have key : ∀ b : Bc F c0, ∃ n : ℕ, ∃ w : Rfin K F, placeVal (Sum.inl (ptP (y.comp (inclR c0))) : Place K F) (b : F) =
      (ptP (y.comp (inclR c0))).valuation F (algebraMap (Rfin K F) F w) ∧ (y.comp (inclR c0) w = 0 ↔ y.comp (inclB c0) b = 0) := by
    intro b
    obtain ⟨n, w, hw⟩ := exists_sub_pow_mul_rfin c0 b.2
    refine ⟨n, w, ?_, ?_⟩
    · rw [placeVal_inl]
      change _ = (ptP (y.comp (inclR c0))).valuation F (w : F)
      rw [hw, map_mul, map_pow, ← coe_xcR]
      change _ = (ptP (y.comp (inclR c0))).valuation F (algebraMap (Rfin K F) F (xcR F c0)) ^ n * _
      rw [hxc, one_pow, one_mul]
    · have e : inclR c0 w = inclR c0 (xcR F c0) ^ n * inclB c0 b := by
        apply Subtype.ext
        push_cast
        rw [coe_inclR, coe_inclR, coe_inclB, hw, coe_xcR]
      rw [AlgHom.comp_apply, AlgHom.comp_apply, e, map_mul, map_pow, mul_eq_zero,
        or_iff_right (pow_ne_zero n (inclR_xcR_ne c0 y))]
  refine ⟨fun b => ?_, fun b => ?_⟩
  · obtain ⟨n, w, h1, -⟩ := key b
    rw [h1]
    exact HeightOneSpectrum.valuation_le_one (K := F) (ptP (y.comp (inclR c0))) _
  · obtain ⟨n, w, h1, h2⟩ := key b
    rw [h1, HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), mem_ptP, h2]

/-- The chart index `{c0}`. -/
noncomputable abbrev idx0 : ChartIdx K := ⟨{c0}, Finset.singleton_nonempty c0⟩

theorem plA_R1 (y : R1 F c0 →ₐ[K] K) :
    plA (idx0 c0) (y.comp (inclB c0)) = (Sum.inl (ptP (y.comp (inclR c0))) : Place K F) :=
  plA_eq_of_isCenter (idx0 c0) (isCenter_R1 c0 y)

variable (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

/-- The plus-curve on `R1`. -/
noncomputable abbrev plusR : SymRing K (Rfin K F) (genusFK K F) →ₐ[K] R1 F c0 := plusMap (inclR c0) a i0

/-- `E = Σ_{i ≠ i0} [a_i]`. -/
noncomputable def plusE : Places.Divisor K F :=
  ∑ i ∈ Finset.univ.erase i0, Finsupp.single (Sum.inl (ptP (a i))) 1

end PlusJ

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_PlusX =====
section

/-!
# Unit S4-ThetaSquare, file PlusX: the plus-curve is a translate of the Abel-Jacobi map

`plusX c0 a i0 : Spec R2 ⟶ X1` (through the chart `{c0}`) and the constant `cE a i0 P0` (class `[E] + [P0] - [Θ]`)
satisfy **`plus_eq`**: `(const cE) * (plusX ≫ AJ_{P0}) = jMap lawMapPlus` (`Spec R2 → X0 → J`).
Also `exists_eq_kptO` (every `K`-point of `Spec R` is `kptO x`) and `finiteType_R1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.JacComplete RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

universe u

section KptO

variable {K : Type u} [Field K]

/-- **Every `K`-point of `Spec R` is `kptO x`.** -/
theorem exists_eq_kptO {R : Type u} [CommRing R] [Algebra K R] (p : 𝟙_ (Over (Spec (.of K))) ⟶ specO K R) :
    ∃ x : R →ₐ[K] K, p = kptO x := by
  have hw : p.left ≫ sR K R = 𝟙 (Spec (.of K)) := Over.w p
  obtain ⟨f, hf⟩ : ∃ f : CommRingCat.of R ⟶ CommRingCat.of K, Spec.map f = p.left :=
    ⟨Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of K) p.left, Spec.map_preimage _⟩
  have hc : CommRingCat.ofHom (algebraMap K R) ≫ f = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hf, Spec.map_id]
    exact hw
  refine ⟨{ f.hom with commutes' := fun k => congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of K => φ.hom k) hc },
    ?_⟩
  apply Over.OverMorphism.ext
  refine hf.symm.trans ?_
  rfl

end KptO

section PlusX

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

variable (c0 : K)

instance finiteType_R1 : Algebra.FiniteType K (R1 F c0) := by
  have : IsScalarTower K (Rfin K F) (R1 F c0) :=
    IsScalarTower.of_algebraMap_eq fun k => ((inclR c0).commutes k).symm
  exact Algebra.FiniteType.trans (S := Rfin K F) inferInstance
    (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (xcR F c0)) (R1 F c0))

variable [IsAlgClosed K]

variable (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F)) (P0 : Place K F)

theorem deg_plusE : (plusE a i0).deg = (genusFK K F : ℤ) - 1 := by
  have h : ∀ s : Finset (Fin (genusFK K F)),
      Places.Divisor.deg (∑ i ∈ s, Finsupp.single (Sum.inl (ptP (a i)) : Place K F) (1 : ℤ)) = s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Places.Divisor.deg]
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, PlacesK.Divisor.deg_add, ih, deg_single_one, Finset.card_insert_of_notMem hj]
      push_cast; ring
  rw [plusE, h, Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub (i0.pos : 1 ≤ genusFK K F), Nat.cast_one]

end PlusX

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Mult1 =====
section

/-!
# Unit S4-ThetaSquare, file Mult1: local algebra for the multiplicity-one count (F6a)

* `ufd_X0T`: the stalks of the chart `X0` are factorial (they are stalks of `J`);
* `span_eq_maximalIdeal_of_dedekind`: in `A_P` (`A` Dedekind), any `t ∈ P \ P²` generates the maximal ideal;
* `eq_of_zero_imp`, `exists_unif`: a uniformizer `t` at a point `φ` of `Rfin` with no zero on a finite set `S ∌ φ`;
* on the plus-curve `Spec R2`: `plusH_ne_zero`, `isDomain_R2`, `isNoetherianRing_R2`, `isLocalization_rfin_R2`
  (`R2` is a localization of `Rfin`), `dvr_stalk_R2` (the stalk at a `K`-point is `Rfin` localized at `ptP`),
  **`coheight_kpt_R2`** (`K`-points have codimension one) and **`ord_kpt_R2`** (a uniformizer has order one).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section Alg

open IsLocalRing

/-- In the localization of a Dedekind domain at a prime `P`, any `t ∈ P \ P²` generates the maximal ideal. -/
theorem span_eq_maximalIdeal_of_dedekind {A O : Type*} [CommRing A] [IsDedekindDomain A] [CommRing O] [IsDomain O] [IsLocalRing O]
    [Algebra A O] {P : Ideal A} [hPp : P.IsPrime] [IsLocalization.AtPrime O P] {t : A} (ht : t ∈ P)
    (ht2 : t ∉ P ^ 2) : Ideal.span {algebraMap A O t} = maximalIdeal O := by
  have hP : P ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at ht
    exact ht2 (ht ▸ Ideal.zero_mem _)
  haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP O
  have hτm : algebraMap A O t ∈ maximalIdeal O := (IsLocalization.AtPrime.to_map_mem_maximal_iff O P t).2 ht
  have hτ2 : algebraMap A O t ∉ maximalIdeal O ^ 2 := by
    intro h
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P O, ← Ideal.map_pow] at h
    have hprim : (P ^ 2).IsPrimary := by
      refine Ideal.isPrimary_of_isMaximal_radical ?_
      rw [Ideal.radical_pow P two_ne_zero, hPp.radical]
      exact hPp.isMaximal hP
    have hdis : Disjoint (P.primeCompl : Set A) (↑(P ^ 2)) := by
      rw [Set.disjoint_left]
      intro b hb hb2
      exact hb (Ideal.pow_le_self two_ne_zero hb2)
    apply ht2
    rw [← IsLocalization.under_map_of_isPrimary_disjoint P.primeCompl O hprim hdis]
    exact h
  have hτ0 : algebraMap A O t ≠ 0 := by
    intro h0
    apply hτ2
    rw [h0]
    exact Ideal.zero_mem _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖm : ϖ ∈ maximalIdeal O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit)
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hτ0 hϖ
  rcases n with _ | _ | n
  · exfalso
    apply (mem_maximalIdeal _).1 hτm
    rw [hv, pow_zero, mul_one]
    exact v.isUnit
  · rw [hv, zero_add, pow_one, Ideal.span_singleton_mul_left_unit v.isUnit,
      ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  · exfalso
    apply hτ2
    have e : (v : O) * ϖ ^ (n + 1 + 1) = ((v : O) * ϖ ^ n * ϖ) * ϖ := by ring
    rw [hv, e, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hϖm) hϖm

/-- Two `K`-points with `φ b = 0 → ψ b = 0` agree. -/
theorem eq_of_zero_imp {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra K R] {φ ψ : R →ₐ[K] K}
    (h : ∀ b, φ b = 0 → ψ b = 0) : φ = ψ := by
  ext b
  have h2 : ψ (b - algebraMap K R (φ b)) = 0 := by
    refine h _ ?_
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h2
  exact h2.symm

end Alg

section Chart

open CategoryTheory AlgebraicGeometry

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- **A uniformizer avoiding finitely many points**: for `φ ∉ S` there is `t ∈ m_φ \ m_φ²` with no zero on `S`. -/
theorem exists_unif (φ : Rfin K F →ₐ[K] K) (S : Finset (Rfin K F →ₐ[K] K)) (hφ : φ ∉ S) :
    ∃ t : Rfin K F, φ t = 0 ∧ t ∉ (ptP φ).asIdeal ^ 2 ∧ ∀ ψ ∈ S, ψ t ≠ 0 := by
  classical
  by_contra hne
  push Not at hne
  let f : (Rfin K F →ₐ[K] K) → Ideal (Rfin K F) := fun ψ =>
    if ψ = φ then (ptP φ).asIdeal ^ 2 else (ptP ψ).asIdeal
  have hsub : ((ptP φ).asIdeal : Set (Rfin K F)) ⊆
      ⋃ ψ ∈ (↑(insert φ S) : Set (Rfin K F →ₐ[K] K)), (f ψ : Set (Rfin K F)) := by
    intro s hs
    by_cases h2 : s ∈ (ptP φ).asIdeal ^ 2
    · refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_self φ S)) ?_
      show s ∈ f φ
      simp only [f, if_pos rfl]
      exact h2
    · obtain ⟨ψ, hψ, h0⟩ := hne s (mem_ptP.1 hs) h2
      have hne' : ψ ≠ φ := fun h => hφ (h ▸ hψ)
      refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_insert_of_mem hψ)) ?_
      show s ∈ f ψ
      simp only [f, if_neg hne']
      exact mem_ptP.2 h0
  obtain ⟨ψ, -, hle⟩ := (Ideal.subset_union_prime φ φ (fun ψ _ h1 _ => by
    simp only [f, if_neg h1]
    exact (ptP ψ).isPrime)).1 hsub
  by_cases hψ : ψ = φ
  · simp only [f, if_pos hψ] at hle
    haveI := (ptP φ).isPrime
    exact (Ideal.pow_succ_lt_pow (ptP φ).ne_bot 1).not_ge (by rw [pow_one]; exact hle)
  · simp only [f, if_neg hψ] at hle
    exact hψ (eq_of_zero_imp (fun b hb => mem_ptP.1 (hle (mem_ptP.2 hb)))).symm

end Chart

section R2

open CategoryTheory AlgebraicGeometry IsLocalRing Order

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

end R2

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Mult2 =====
section

/-!
# Unit S4-ThetaSquare, file Mult2: multiplicity one of `Θ` along the plus-curve (F6b)

* `avoid_Theta`: a map to `J` with one point off `W` avoids `Θ`;
* `kappa`: the plus-curve chart map `κ = Spec (lawMapPlus) : Spec R2 → X0`, `jMap_transl`, `kappa_kpt`;
* `lawMapPlus_normS`: `κ^* (Nm t) = t · ∏_{i ≠ i0} a_i(t)`;
* `fpull_kappa`, `ord_fpull_kappa`: `κ^* (Nm t)` has order one at a `K`-point `x` when `t` is a uniformizer at
  `ptR2 x` with no zero at the other points `a_i`;
* **`cpull_kappa_eq_one`**: `(τ ∘ κ)^* Θ` has multiplicity exactly one at every `K`-point `x` of the plus-curve
  (`τ = τ_{c_φ⁻¹}`, `φ = ptR2 x`): lower bound by `exists_eta` + `cpull_pos`, upper bound by `cpull_le_ord` with the
  norm `Nm t` (`normS_mem_eta`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section Mult2

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

theorem injective_ΓSpecIso_inv (R : CommRingCat.{u}) : Function.Injective (Scheme.ΓSpecIso R).inv.hom :=
  (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.injective

variable (hg : 0 < genusFK K F)

end Mult2

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve1 =====
section

/-!
# Unit S4-ThetaSquare, file Curve1: the curve cycle `D_e = f_e^* Θ` on `X1` (T4c, part 1)

* `fe P0 e = AJ ≫ transl e : X1 → J` (`p ↦ AJ(p) · e`), `feX` its underlying scheme map, `comp_fe`, `mem_W_fe`;
* **`Dc P0 e := cpull (feX P0 e) Θ`**, a cycle on the curve `X1`; `Dc_nonneg`, `Dc_eq_zero` (support in `f_e⁻¹ W`);
* `plusX` is an open immersion (`ι2`), and `plusX ≫ f_{cE · d} = τ_d ∘ κ` (`plusX_fe`);
* **`Dc_plusX_eq_one`**: `D_e` has multiplicity exactly one at the point `plusX (kpt x)` when `e = cE · c_φ⁻¹`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete
open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB RamanujanPetersson.JacDivisors

universe u

section Curve1

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance isLocallyNoetherian_X1 : IsLocallyNoetherian (X1 K F) := by
  haveI : LocallyOfFiniteType (toSpecK K (algebraMap K[X] F X) 1) := inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (toSpecK K (algebraMap K[X] F X) 1)

variable (P0 : Place K F)

variable (hg : 0 < genusFK K F)

variable (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F))

end Curve1

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve3 =====
section

/-!
# Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)

* `div_pow_of_div`, `le_ell_single`: if `div f = [Q'] - [Q]` with `Q ≠ Q'` then `ℓ(n[Q]) ≥ n + 1` for all `n`;
* **`eq_of_clsK_single`** (Abel for one point, `g ≥ 1`): `[Q] ~ [Q'] ⇒ Q = Q'`; `ajK_injective`;
* `kPl_kptO_plusX`: the place of the plus-curve point at `x` is `ptR2 x`; `kPl_chart`: the place of a chart point;
* **`exists_chart0`**: every `K`-point `q` of `X1` lies in a chart `{c0}`, at a point centered at `kPl q`;
  `xcR_ne_of_isCenter`: then `x - c0` does not vanish at that place;
* **`eq_iota2`**: if `ptR2 x` is the place of `q` (chart `{c0}` from `exists_chart0`), then `q = ι2 (kpt x)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Abel

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end Abel

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- In the chart `{c0}` through a place `P`, `x - c0` does not vanish at `P`. -/
theorem xcR_ne_of_isCenter (c0 : K) {φ : Rfin K F →ₐ[K] K} {θ : Bc F c0 →ₐ[K] K}
    (h : IsCenter (Sum.inl (ptP φ) : Place K F) θ) : φ (xcR F c0) ≠ 0 := by
  intro h0
  have h1 := h.1 (uc0 F c0)
  rw [placeVal_inl] at h1
  have h2 : (ptP φ).valuation F (algebraMap (Rfin K F) F (xcR F c0)) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), mem_ptP]
    exact h0
  have e : ((uc0 F c0 : Bc F c0) : F) * algebraMap (Rfin K F) F (xcR F c0) = 1 := by
    change (algebraMap K[X] F X - algebraMap K F c0)⁻¹ * ((xcR F c0 : Rfin K F) : F) = 1
    rw [coe_xcR]
    exact inv_mul_cancel₀ (sub_ne_zero_of_tr (transcendental_xF K F) c0)
  have h3 := congrArg ((ptP φ).valuation F) e
  rw [map_mul, map_one] at h3
  have h4 : (ptP φ).valuation F ((uc0 F c0 : Bc F c0) : F) *
      (ptP φ).valuation F (algebraMap (Rfin K F) F (xcR F c0)) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left' h1) h2
  rw [h3] at h4
  exact lt_irrefl _ h4

end Geom

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve4 =====
section

/-!
# Unit S4-ThetaSquare, file Curve4: multiplicity one of `D_e` at the points of `G` (T4c, step (B))

* `exists_of_Zdiv_pos`: a place in the support of `Zdiv S` is a point of `S`;
* `exists_mem_X0`: if `ℓ(W0 - G + 2[v]) = 1` and that class contains the reduced divisor `Zdiv S`, then `v ∈ S`;
* `exists_R2pt`: a point `φ` of an `X0` point with `φ(x - c0) ≠ 0` is `ptR2 x` for a `K`-point `x` of a plus chart;
* `Zdiv_image_eq`, `eq_cE`: class bookkeeping (`e = cE · c_φ⁻¹`);
* **`Dc_eq_one`**: for `e` of class `[W0 - G] - (g-2)[P0]` and `q` with `1 ≤ G (kPl q)`, `D_e` is `1` at `q`
  (hypotheses: `ℓ(W0 - G + 2[kPl q]) = 1`, an `X0` point in that class, `f_e` avoids `Θ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve4

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

open Classical

theorem exists_of_Zdiv_pos {S : Finset (Rfin K F →ₐ[K] K)} {v : Place K F} (h : 1 ≤ Zdiv S v) :
    ∃ φ ∈ S, v = Sum.inl (ptP φ) := by
  rcases v with P | P
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Zdiv_inl_ptP] at h
    by_cases hφ : φ ∈ S
    · exact ⟨φ, hφ, rfl⟩
    · rw [if_neg hφ] at h
      omega
  · rw [Zdiv_inr] at h
    omega

theorem Zdiv_image_eq (t : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (ht : Function.Injective t)
    (i0 : Fin (genusFK K F)) :
    Zdiv (Finset.univ.image t) = Finsupp.single (Sum.inl (ptP (t i0))) 1 + plusE t i0 := by
  rw [Zdiv, Finset.sum_image (fun i _ j _ h => ht h), ← Finset.add_sum_erase _ _ (Finset.mem_univ i0), plusE]

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

end Geom

end Curve4

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve6 =====
section

/-!
# Unit S4-ThetaSquare, file Curve6: when a `K`-point `e` of `J` is good (T4c (D), `K`-point reduction)

* `ell_two_eq_one`: for `G ≥ 0` reduced of degree `g` with `ℓ(G) = 1`, `ℓ(W0 - G + 2[v]) = 1` for every place `v`;
* `exists_cK`, `exists_c2`: the constant `K`-points of classes `[W0] - (g-2)[P0] - [Θ]` and `g[P0] - [Θ]`;
* `exists_kJ`: a `K`-point of `J` whose closed point lies in `jX0 (X0)` is `kJ yR`;
* `avoid_of_not_mem`: `e ∉ W` makes `f_e` avoid `Θ`;
* **`isGoodFor_of`**: if `e ∉ W`, `c_K e⁻¹ ∈ jX0 (X0)`, and `AJ(q)² e c_2 ∈ jX0 (X0)` whenever `f_e (q) ∈ W`, then
  `e` is good for some `G` (`IsGoodFor P0 W0 e G`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve6

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem Zdiv_le_one (S : Finset (Rfin K F →ₐ[K] K)) (v : Place K F) : Zdiv S v ≤ 1 := by
  rcases v with P | P
  · obtain ⟨φ, rfl⟩ := exists_ptP P
    rw [Zdiv_inl_ptP]
    split_ifs <;> omega
  · rw [Zdiv_inr]
    omega

end Curve6

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Curve9 =====
section

/-!
# Unit S4-ThetaSquare, file Curve9: the good open set is nonempty and dense (T4c (D), nonemptiness, part 2)

On `X1^g` (irreducible) the three open conditions on `p`, with `e := e_M(p) = c_3 Φ_g(p)⁻¹`:
* `Ua`: `c_K e⁻¹ ∈ jX0 (X0)`; `Ub`: `e ∉ W`; `Uj j`: `AJ(p_j)² e c_2 ∈ jX0 (X0)` (each nonempty);
* `mem_Ogood_of_U`: a `K`-point `p` in all of them gives `e ∈ Ogood` (`f_e (q) ∈ W` forces `q = p_j` for some `j`);
* **`exists_kpt_Ogood`**, **`nonempty_Ogood`**, **`dense_Ogood`**: `Ogood P0 cK c2` has a `K`-point and is dense in `J`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

/-- In an irreducible space, finitely many nonempty opens meet. -/
theorem nonempty_iInter_of_open {X : Type*} [TopologicalSpace X] [IrreducibleSpace X] {ι : Type*} [Fintype ι]
    (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hn : ∀ i, (U i).Nonempty) : (⋂ i, U i).Nonempty := by
  have h := (isIrreducible_iff_sInter.1 (IrreducibleSpace.isIrreducible_univ X)) (Finset.univ.image U)
    (by simpa using ho) (by simpa using hn)
  simpa [Set.sInter_image] using h

section Curve9

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end Curve9

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_IsogDegB_Frob =====
section

/-!
# S4-IsogDegB, Frobenius-type endomorphisms (lemma L28 of S4_COREB_ROUTE.md §3)

* If `π♯ : 𝒪_{A,e} → 𝒪_{A,e}` lands in the subring generated by `k` and the `p`-th powers
  (`CharP k p`), then `dπ = 1` (`dφ_eq_one_of_frob`): tangent vectors are pointed derivations, and
  these kill constants and `p`-th powers.
* For a commutative `A`, `polyEnd π F = F(π) = ∏ (π^∘n)^{F_n}` in the Hom-group; it is a
  homomorphism, `F ↦ F(π)` is additive, and `t ≫ π = 1` gives `t ≫ F(π) = t ^ F(0)`.
* Hence `dπ = 1` gives `d F(π) = F(0)`, and for `p ∤ F(0)` the map `F(π)` is a dominant separable
  isogeny with `deg F(π) = #Ker F(π)(k)` (`polyEnd_separable`).
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA Polynomial

universe u

section Kill

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

/-- `π^∘n`. -/
noncomputable def piter (π : A ⟶ A) : ℕ → (A ⟶ A)
  | 0 => 𝟙 A
  | n + 1 => π ≫ piter π n

theorem isMonHom_piter (π : A ⟶ A) [IsMonHom π] (n : ℕ) : IsMonHom (piter π n) := by
  induction n with
  | zero => show IsMonHom (𝟙 A); infer_instance
  | succ n ih => show IsMonHom (π ≫ piter π n); infer_instance

instance (π : A ⟶ A) [IsMonHom π] (n : ℕ) : IsMonHom (piter π n) := isMonHom_piter π n

theorem comp_piter {X : Over (Spec (.of k))} (π : A ⟶ A) [IsMonHom π] (t : X ⟶ A)
    (ht : t ≫ π = 1) (n : ℕ) : t ≫ piter π (n + 1) = 1 := by
  show t ≫ π ≫ piter π n = 1
  rw [← Category.assoc, ht, MonObj.one_comp]

end Kill

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

theorem isMonHom_one : IsMonHom (1 : A ⟶ A) := by
  rw [Hom.one_def]; infer_instance

instance isMonHom_mul (φ ψ : A ⟶ A) [IsMonHom φ] [IsMonHom ψ] : IsMonHom (φ * ψ) := by
  rw [Hom.mul_def]; infer_instance

theorem isMonHom_zpow (φ : A ⟶ A) [IsMonHom φ] (n : ℤ) : IsMonHom (φ ^ n) := by
  have hpow : ∀ m : ℕ, IsMonHom (φ ^ m) := by
    intro m
    induction m with
    | zero => rw [pow_zero]; exact isMonHom_one
    | succ m ih => rw [pow_succ]; infer_instance
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hpow m
  | negSucc m => rw [zpow_negSucc]; have := hpow (m + 1); infer_instance

/-- `F(π) = ∏ₙ (π^∘n)^{Fₙ}` in the commutative Hom-group (`+` on `End A` is `*` here). -/
noncomputable def polyEnd (π : A ⟶ A) (F : ℤ[X]) : A ⟶ A :=
  F.toFinsupp.coeff.prod fun n c ↦ piter π n ^ c

theorem isMonHom_polyEnd (π : A ⟶ A) [IsMonHom π] (F : ℤ[X]) : IsMonHom (polyEnd π F) := by
  unfold polyEnd Finsupp.prod
  refine Finset.prod_induction _ (fun f ↦ IsMonHom f) (fun a b ha hb ↦ ?_) isMonHom_one
    (fun n _ ↦ isMonHom_zpow _ _)
  have := ha; have := hb; infer_instance

instance (π : A ⟶ A) [IsMonHom π] (F : ℤ[X]) : IsMonHom (polyEnd π F) := isMonHom_polyEnd π F

theorem polyEnd_add (π : A ⟶ A) (F G : ℤ[X]) :
    polyEnd π (F + G) = polyEnd π F * polyEnd π G := by
  unfold polyEnd
  rw [Polynomial.toFinsupp_add, AddMonoidAlgebra.coeff_add]
  exact Finsupp.prod_add_index' (fun n ↦ zpow_zero _) (fun n a b ↦ zpow_add _ a b)

theorem polyEnd_monomial (π : A ⟶ A) (n : ℕ) (c : ℤ) :
    polyEnd π (monomial n c) = piter π n ^ c := by
  unfold polyEnd
  rw [Polynomial.toFinsupp_monomial, AddMonoidAlgebra.coeff_single]
  exact Finsupp.prod_single_index (zpow_zero _)

/-- `t ≫ π = 1` gives `t ≫ F(π) = t ^ F(0)`. -/
theorem comp_polyEnd {X : Over (Spec (.of k))} (π : A ⟶ A) [IsMonHom π] (t : X ⟶ A)
    (ht : t ≫ π = 1) (F : ℤ[X]) : t ≫ polyEnd π F = t ^ F.coeff 0 := by
  let P : (A ⟶ A) →* (X ⟶ A) := MonoidHom.mk' (fun g ↦ t ≫ g) (MonObj.comp_mul t)
  have e : t ≫ polyEnd π F = P (polyEnd π F) := rfl
  rw [e]
  unfold polyEnd Finsupp.prod
  rw [map_prod, Finset.prod_eq_single 0]
  · show t ≫ piter π 0 ^ F.toFinsupp.coeff 0 = _
    rw [GrpObj.comp_zpow, Polynomial.toFinsupp_apply]
    rfl
  · intro n _ hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    show t ≫ piter π (m + 1) ^ F.toFinsupp.coeff (m + 1) = 1
    rw [GrpObj.comp_zpow, comp_piter π t ht, one_zpow]
  · intro h0
    rw [Finsupp.notMem_support_iff.1 h0]
    exact (congrArg P (zpow_zero (piter π 0))).trans (map_one P)

end Poly

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_ThetaCube_Deg =====
section

/-!
# S4-ThetaCube, T8a: the inputs `hD` and `hproj` of DegPoly for the theta divisor

* `polyEnd_one`: `1(π) = 𝟙`.
* `exists_avoid`, `cTh P0 hg φ := (φ ≫ τ_b)^* Θ` for a translate `b` whose image avoids `Θ`.
* `iform_cTh`: `(cTh φ)^g = deg φ · (Θ^g)`.
* `formTh g hdim`: the intersection form as a multilinear map (`DegPoly.formOfAdd` of `iform`).
* `hD_Th`, `hproj_Th`: the hypotheses `hD` and `hproj` of `DegPoly.degreeDataOfQuad` for
  `c G := cTh (polyEnd π G)` and `deg G := degree (polyEnd π G).left`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

theorem polyEnd_one (π : A ⟶ A) : IsogDegB.polyEnd π 1 = 𝟙 A := by
  rw [← Polynomial.monomial_zero_one, IsogDegB.polyEnd_monomial, zpow_one]
  rfl

end Poly

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Zero =====
section

/-!
# S4-ThetaCube, T8z: the input `hzero` of DegPoly for the theta divisor

* `polyEnd_zero`: `0(π) = 1` (the constant map to the origin).
* `cpull_eq_zero_of_eq_one`: the Cartier pull-back along a constant map `1 ≫ τ_b` is `0`.
* `hzero_Th`: `cTh (polyEnd π 0) ∈ numKer (formTh ..)` (it is the zero cycle).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Poly

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

theorem polyEnd_zero (π : A ⟶ A) : IsogDegB.polyEnd π 0 = 1 := by
  have h := IsogDegB.polyEnd_add π 0 0
  rw [add_zero] at h
  simpa using h.symm

end Poly

section Const

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsIntegral A.left]
  [IsLocallyNoetherian A.left] [∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x)]

end Const

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cube =====
section

/-!
# S4-ThetaCube, file Cube (T5a): numerical triviality of pulled-back principal multiples

* general `cpull` facts: `avoid_zero`, `cpull_zero`, `avoid_neg`, `cpull_neg`, `avoid_sub`, `cpull_sub`,
  `avoid_nsmul`, `cpull_nsmul`;
* `div_mem_numKer`: principal divisors of `J` lie in `numKer` of the intersection form;
* **`mem_numKer_of_cpull_div`**: if `n • Z = div h` on any `P` and `L : J ⟶ P` avoids `Z`, then `L^* Z ∈ numKer`
  (the interface for the J^3 cube: `P = J^3`, `L = (α, β, γ)`);
* `cubeC c p q r`: the seven-term cube combination (hom-group law `*`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

end General

/-- The seven-term cube combination of `c` along `p q r` (group law written `*`). -/
def cubeC {X : Type*} [Mul X] {M : Type*} [AddCommGroup M] (c : X → M) (p q r : X) : M :=
  c (p * q * r) - c (p * q) - c (p * r) - c (q * r) + c p + c q + c r

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Line =====
section

/-!
# S4-ThetaCube, file Line (D-A, part LT1): the curve test for Weil divisors

Let `X` be integral, locally Noetherian, locally factorial and Jacobson, `E` a Weil divisor on `X`, `y` a point of
coheight one and `O` an open set containing `y`. Suppose that through every closed point `p ∈ O` there is a
curve `ℓ : C ⟶ X` (`ℓ x = p`, `x` of coheight one in `C`) avoiding `E` with `ℓ^* E = 0` at `x`. Then `E y = 0`.
Proof: pick a closed point `p` of `closure {y} ∩ O` off the other components of `supp E` near `y`
(Jacobson); `cpull_pos` at `x` gives `ℓ^* E x > 0` (or `< 0`).
* `not_specializes_of_coheight`: distinct points of coheight one are incomparable;
* **`eq_zero_of_test`** (one point), **`eq_zero_of_tests`** (every point of coheight one has such an `O`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry Order Topology RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare

universe u

section LineTest

variable {C X : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral X] [IsLocallyNoetherian X]
  [∀ y : X, UniqueFactorizationMonoid (X.presheaf.stalk y)]

/-- Two distinct points of coheight one are incomparable. -/
lemma not_specializes_of_coheight {y z : X} (hy : coheight y = 1) (hz : coheight z = 1) (hne : z ≠ y) :
    ¬ z ⤳ y := by
  intro h
  have hlt : y < z := lt_of_le_not_ge h fun h' => hne (Specializes.antisymm h h').eq
  have := coheight_strictAnti hlt (by rw [hz]; exact ENat.one_lt_top)
  rw [hy, hz] at this
  exact lt_irrefl _ this

variable [JacobsonSpace X]

lemma false_of_test_pos {E : AlgebraicCycle X ℤ} (hE : E ∈ weilDivisors X) {y : X} (hy : coheight y = 1)
    (hpos : 0 < E y) {O : Set X} (hO : IsOpen O) (hyO : y ∈ O)
    (htest : ∀ p ∈ O, IsClosed {p} → ∃ (ℓ : C ⟶ X) (x : C), ℓ x = p ∧ coheight x = 1 ∧ Avoid ℓ E ∧
      cpull ℓ E x = 0) : False := by
  obtain ⟨t, ht, hfin⟩ := E.supportLocallyFiniteWithinDomain' y (Set.mem_univ y)
  obtain ⟨t', ht't, ht'o, hyt'⟩ := mem_nhds_iff.mp ht
  set S : Set X := (t ∩ Function.support E) \ {y} with hS
  have hSfin : S.Finite := hfin.sdiff
  set Z : Set X := ⋃ z ∈ S, closure {z} with hZdef
  have hZ : IsClosed Z := hSfin.isClosed_biUnion fun z _ => isClosed_closure
  have hyZ : y ∉ Z := by
    rw [hZdef, Set.mem_iUnion₂]
    rintro ⟨z, ⟨⟨_, hz⟩, hzy⟩, hyz⟩
    exact not_specializes_of_coheight hy (hE z hz) hzy (specializes_iff_mem_closure.mpr hyz)
  set U : Set X := (O ∩ t') ∩ Zᶜ with hU
  have hUo : IsOpen U := (hO.inter ht'o).inter hZ.isOpen_compl
  have hyU : y ∈ U := ⟨⟨hyO, hyt'⟩, hyZ⟩
  obtain ⟨p, ⟨hpU, hpy⟩, hpc⟩ := nonempty_inter_closedPoints (Z := U ∩ closure {y})
    ⟨y, hyU, subset_closure rfl⟩ (hUo.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  obtain ⟨ℓ, x, hxp, hx1, hA, h0⟩ := htest p hpU.1.1 hpc
  have hyp : y ⤳ ℓ x := by
    rw [hxp]
    exact specializes_iff_mem_closure.mpr hpy
  have hnn : ∀ z : X, z ⤳ ℓ x → coheight z = 1 → 0 ≤ E z := by
    intro z hz _
    by_contra hneg
    replace hneg := not_le.mp hneg
    by_cases hzy : z = y
    · rw [hzy] at hneg
      omega
    · have hzt : z ∈ t := ht't (hz.mem_open ht'o (hxp ▸ hpU.1.2))
      apply hpU.2
      rw [hZdef, Set.mem_iUnion₂]
      exact ⟨z, ⟨⟨hzt, hneg.ne⟩, hzy⟩, specializes_iff_mem_closure.mp (hxp ▸ hz)⟩
  have key := cpull_pos ℓ hE hA hx1 hnn hyp hpos
  rw [h0] at key
  exact lt_irrefl _ key

end LineTest

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Lines =====
section

/-!
# S4-ThetaCube, file Lines (D-A, part LP1): coordinate lines in `X1^n` and the open projection

For objects `W`, `C` over `Spec K` (`K` a field):
* `isOpenMap_fst`: the projection `W ⊗ C ⟶ W` is open (Mathlib: every morphism to `Spec K` is universally open);
* `cline W C w : C ⟶ W ⊗ C`, `c ↦ (w, c)` for a `K`-point `w` of `W`; `isPullback_cline`: it is the fibre of the
  projection over `w`; **`mem_range_cline`**: every point of `W ⊗ C` over `w` lies on it.
For `PP n = X1^n` (unit JacComplete):
* `line n i p : X1 ⟶ X1^n`, the `i`-th coordinate line through the `K`-point `p`; `line_val`: it passes through `p`;
  `line_castSucc_fst`: projecting a line of `X1^(n+1)` in a direction `< n` gives a line of `X1^n`;
  `mem_range_line_last`: the fibre of `X1^(n+1) ⟶ X1^n` through `p` is the last line through `p`;
* `exists_kpt_of_closed`: every closed point of `X1^n` is the value of a `K`-point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacComplete
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

universe u

section CLine

variable {K : Type u} [Field K]

/-- **The projection `W ⊗ C ⟶ W` over a field is open.** -/
lemma isOpenMap_fst (W C : Over (Spec (.of K))) : IsOpenMap (fst W C).left := by
  haveI : Subsingleton (Spec (.of K)) := inferInstance
  haveI : UniversallyOpen C.hom := inferInstance
  exact Scheme.Hom.isOpenMap (pullback.fst W.hom C.hom)

/-- The line `c ↦ (w, c)` of `W ⊗ C` through the `K`-point `w` of `W`. -/
noncomputable def cline (W C : Over (Spec (.of K))) (w : 𝟙_ (Over (Spec (.of K))) ⟶ W) : C ⟶ W ⊗ C :=
  lift (toUnit C ≫ w) (𝟙 C)

lemma cline_fst (W C : Over (Spec (.of K))) (w : 𝟙_ (Over (Spec (.of K))) ⟶ W) :
    cline W C w ≫ fst W C = toUnit C ≫ w := lift_fst _ _

lemma cline_snd (W C : Over (Spec (.of K))) (w : 𝟙_ (Over (Spec (.of K))) ⟶ W) :
    cline W C w ≫ snd W C = 𝟙 C := lift_snd _ _

/-- The line through `w` is the fibre of `W ⊗ C ⟶ W` over `w`. -/
lemma isPullback_cline (W C : Over (Spec (.of K))) (w : 𝟙_ (Over (Spec (.of K))) ⟶ W) :
    IsPullback (cline W C w).left C.hom (pullback.fst W.hom C.hom) w.left := by
  have h1 : (cline W C w).left ≫ pullback.snd W.hom C.hom = 𝟙 C.left :=
    congrArg CommaMorphism.left (cline_snd W C w)
  have h2 : w.left ≫ W.hom = 𝟙 (Spec (.of K)) := Over.w w
  have h3 : (cline W C w).left ≫ pullback.fst W.hom C.hom = C.hom ≫ w.left :=
    congrArg CommaMorphism.left (cline_fst W C w)
  refine IsPullback.of_right (h₁₂ := pullback.snd W.hom C.hom) (h₂₂ := W.hom) (v₁₃ := C.hom) ?_ h3
    (IsPullback.of_hasPullback W.hom C.hom).flip
  rw [h1, h2]
  exact IsPullback.id_horiz C.hom

/-- **Every point of `W ⊗ C` over the `K`-point `w` lies on the line through `w`.** -/
lemma mem_range_cline (W C : Over (Spec (.of K))) (w : 𝟙_ (Over (Spec (.of K))) ⟶ W) {z : (W ⊗ C).left}
    (s : Spec (.of K)) (hz : (fst W C).left z = w.left s) : z ∈ Set.range (cline W C w).left := by
  obtain ⟨c, hc, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_cline W C w) z s hz
  exact ⟨c, hc⟩

end CLine

section Lines

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The `i`-th coordinate line `X1 ⟶ X1^n` through the `K`-point `p`. -/
noncomputable def line : (n : ℕ) → Fin n → (𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) → (X1O K F ⟶ PP K F n)
  | 0, i, _ => i.elim0
  | n + 1, i, p => Fin.lastCases (cline (PP K F n) (X1O K F) (p ≫ fst (PP K F n) (X1O K F)))
      (fun j => lift (line n j (p ≫ fst (PP K F n) (X1O K F))) (toUnit _ ≫ p ≫ snd (PP K F n) (X1O K F))) i

lemma line_last (n : ℕ) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (n + 1)) :
    line K F (n + 1) (Fin.last n) p = cline (PP K F n) (X1O K F) (p ≫ fst (PP K F n) (X1O K F)) := by
  rw [line]; exact Fin.lastCases_last

lemma line_castSucc (n : ℕ) (j : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (n + 1)) :
    line K F (n + 1) j.castSucc p =
      lift (line K F n j (p ≫ fst (PP K F n) (X1O K F))) (toUnit _ ≫ p ≫ snd (PP K F n) (X1O K F)) := by
  rw [line]; exact Fin.lastCases_castSucc j

/-- Projecting a line of `X1^(n+1)` in a direction `j < n` to `X1^n` gives the `j`-th line there. -/
lemma line_castSucc_fst (n : ℕ) (j : Fin n) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (n + 1)) :
    line K F (n + 1) j.castSucc p ≫ fst (PP K F n) (X1O K F) = line K F n j (p ≫ fst (PP K F n) (X1O K F)) := by
  rw [line_castSucc]; exact lift_fst _ _

lemma line_val_last (n : ℕ) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n ⊗ X1O K F) :
    (p ≫ snd _ _) ≫ cline (PP K F n) (X1O K F) (p ≫ fst _ _) = p := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, cline_fst, ← Category.assoc, toUnit_unique ((p ≫ snd _ _) ≫ toUnit _) (𝟙 _),
      Category.id_comp]
  · rw [Category.assoc, cline_snd, Category.comp_id]

/-- **(P3)** The fibre of `X1^(n+1) ⟶ X1^n` through the `K`-point `p` is the last line through `p`. -/
theorem mem_range_line_last (n : ℕ) (p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F (n + 1)) {z : (PP K F (n + 1)).left}
    (s : Spec (.of K)) (hz : (fst (PP K F n) (X1O K F)).left z = (fst (PP K F n) (X1O K F)).left (p.left s)) :
    z ∈ Set.range (line K F (n + 1) (Fin.last n) p).left := by
  rw [line_last]
  exact mem_range_cline (PP K F n) (X1O K F) _ (z := z) s hz

/-- **Every closed point of `X1^n` is the value of a `K`-point.** -/
theorem exists_kpt_of_closed (n : ℕ) {z : (PP K F n).left} (hz : IsClosed {z}) :
    ∃ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n, p.left (IsLocalRing.closedPoint K) = z :=
  ⟨Over.homMk (pointOfClosedPoint (PP K F n).hom z hz) (pointOfClosedPoint_comp _ _ _),
    pointOfClosedPoint_apply (PP K F n).hom z hz _⟩

end Lines

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Reach =====
section

/-!
# S4-ThetaCube, file Reach (D-A, part (R)): reachability by coordinate lines in `X1^n`

**`reach`**: let `Z ⊆ X1^n` be closed and irreducible and `U` open with `Z ∩ U ≠ ∅`. If for every `K`-point `p`
with `p ∈ Z ∩ U` every coordinate line through `p` lies in `Z`, then `Z = X1^n`.
Proof by induction, `X1^(n+1) = X1^n ⊗ X1` with the open projection `π`: the fibre of `π` through a closed point
of `Z ∩ U` is the last line through it (`mem_range_line_last`), so `Z = π⁻¹(closure (π (Z ∩ U ∩ closed)))` (open
map + Jacobson); the image satisfies the hypothesis on `X1^n` (the other lines project to lines).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

universe u

section Reach

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The hypothesis of `reach` on `X1^n`. -/
def LinesIn (n : ℕ) (Z U : Set (PP K F n).left) : Prop :=
  ∀ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n, p.left (IsLocalRing.closedPoint K) ∈ Z ∩ U →
    ∀ i, Set.range (line K F n i p).left ⊆ Z

variable (K F) in
/-- The conclusion of `reach` on `X1^n`. -/
def Reach (n : ℕ) : Prop :=
  ∀ Z U : Set (PP K F n).left, IsClosed Z → IsIrreducible Z → IsOpen U → (Z ∩ U).Nonempty →
    LinesIn K F n Z U → Z = Set.univ

lemma reach_zero : Reach K F 0 := by
  unfold Reach
  intro Z U _ _ _ hZU _
  have : Subsingleton (PP K F 0).left := (inferInstance : Subsingleton (Spec (.of K)))
  obtain ⟨z, hz, -⟩ := hZU
  exact Set.eq_univ_of_forall fun x => Subsingleton.elim z x ▸ hz

lemma isClosed_kpt (n : ℕ) (q : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n) :
    IsClosed ({q.left (IsLocalRing.closedPoint K)} : Set (PP K F n).left) :=
  (pointEquivClosedPoint (PP K F n).hom ⟨q.left, Over.w q⟩).2

lemma reach_step (n : ℕ) (ih : Reach K F n) (Z U : Set (PP K F n ⊗ X1O K F).left) (hZ : IsClosed Z)
    (hZi : IsIrreducible Z) (hU : IsOpen U) (hZU : (Z ∩ U).Nonempty) (hline : LinesIn K F (n + 1) Z U) :
    Z = Set.univ := by
  set π := (fst (PP K F n) (X1O K F)).left with hπ
  have hπo : IsOpenMap π := isOpenMap_fst _ _
  have hπc : Continuous π := π.continuous
  haveI : IsProper (PP K F n ⊗ X1O K F).hom := isProper_PP (n + 1)
  haveI : JacobsonSpace (PP K F n ⊗ X1O K F).left := LocallyOfFiniteType.jacobsonSpace (PP K F n ⊗ X1O K F).hom
  haveI : JacobsonSpace (PP K F n).left := LocallyOfFiniteType.jacobsonSpace (PP K F n).hom
  set S := Z ∩ U ∩ closedPoints (PP K F n ⊗ X1O K F).left with hS
  have hZUl : IsLocallyClosed (Z ∩ U) := hZ.isLocallyClosed.inter hU.isLocallyClosed
  have hclS : closure S = Z := by
    rw [hS, JacobsonSpace.closure_inter_closedPoints_eq_closure hZUl]
    exact (closure_mono Set.inter_subset_left).trans_eq hZ.closure_eq |>.antisymm
      (subset_closure_inter_of_isPreirreducible_of_isOpen hZi.isPreirreducible hU hZU)
  obtain ⟨s0, hs0⟩ : S.Nonempty := nonempty_inter_closedPoints hZU hZUl
  -- step 1: the fibres of `π` through `S` lie in `Z`
  have hfib : π ⁻¹' (π '' S) ⊆ Z := by
    rintro z ⟨s, ⟨⟨hsZ, hsU⟩, hsc⟩, hsz⟩
    obtain ⟨p, hp⟩ := exists_kpt_of_closed (K := K) (F := F) (n + 1) hsc
    have hz : (fst (PP K F n) (X1O K F)).left z =
        (fst (PP K F n) (X1O K F)).left (p.left (IsLocalRing.closedPoint K)) := by
      rw [hp]; exact hsz.symm
    exact hline p (by rw [hp]; exact ⟨hsZ, hsU⟩) (Fin.last n) (mem_range_line_last n p _ hz)
  set ZW := closure (π '' S) with hZWdef
  have hZW : Z = π ⁻¹' ZW := by
    refine subset_antisymm ?_ ?_
    · rw [← hclS]
      exact closure_minimal (fun s hs => subset_closure ⟨s, hs, rfl⟩) (isClosed_closure.preimage hπc)
    · rw [hZWdef, hπo.preimage_closure_eq_closure_preimage hπc]
      exact closure_minimal hfib hZ
  have himZ : π '' Z ⊆ ZW := by
    rw [← hclS]; exact image_closure_subset_closure_image hπc
  have hZWi : IsIrreducible ZW := by
    have h1 : ZW = closure (π '' Z) :=
      subset_antisymm (closure_mono (Set.image_mono (Set.inter_subset_left.trans Set.inter_subset_left)))
        (closure_minimal himZ isClosed_closure)
    rw [h1]
    exact isIrreducible_iff_closure.mpr (hZi.image π hπc.continuousOn)
  -- step 2: `ZW` satisfies the hypothesis on `X1^n` with `U_W = π(U)`
  have hlW : LinesIn K F n ZW (π '' U) := by
    unfold LinesIn
    rintro q ⟨hqZ, u, hu, hqu⟩ j
    have hT : IsLocallyClosed (π ⁻¹' {q.left (IsLocalRing.closedPoint K)} ∩ U) :=
      ((isClosed_kpt n q).preimage hπc).isLocallyClosed.inter hU.isLocallyClosed
    obtain ⟨t, ⟨htq, htU⟩, htc⟩ := nonempty_inter_closedPoints
      (Z := π ⁻¹' {q.left (IsLocalRing.closedPoint K)} ∩ U) ⟨u, hqu, hu⟩ hT
    have htZ : t ∈ Z := by
      rw [hZW]
      show π t ∈ ZW
      rw [Set.mem_singleton_iff.mp htq]
      exact hqZ
    obtain ⟨p, hp⟩ := exists_kpt_of_closed (K := K) (F := F) (n + 1) htc
    have hpq : p ≫ fst (PP K F n) (X1O K F) = q := by
      apply Over.OverMorphism.ext
      refine ext_of_apply_closedPoint_eq (PP K F n).hom (Over.w _) (Over.w _) ?_
      show (fst (PP K F n) (X1O K F)).left (p.left (IsLocalRing.closedPoint K)) = _
      rw [hp]
      exact Set.mem_singleton_iff.mp htq
    rintro _ ⟨x, rfl⟩
    have hx : (line K F n j q).left x = π ((line K F (n + 1) j.castSucc p).left x) := by
      rw [← hpq, ← line_castSucc_fst]; rfl
    rw [hx]
    exact himZ ⟨_, hline p (by rw [hp]; exact ⟨htZ, htU⟩) j.castSucc ⟨x, rfl⟩, rfl⟩
  have := ih ZW (π '' U) isClosed_closure hZWi (hπo U hU)
    ⟨π s0, subset_closure ⟨s0, hs0, rfl⟩, s0, hs0.1.2, rfl⟩ hlW
  rw [hZW, this, Set.preimage_univ]

/-- **(R) Reachability by coordinate lines in `X1^n`.** -/
theorem reach : (n : ℕ) → Reach K F n
  | 0 => reach_zero
  | n + 1 => fun Z U hZ hZi hU hZU hl => reach_step n (reach n) Z U hZ hZi hU hZU hl

end Reach

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_JacSymB_Coord =====
section

/-!
# S4-JacSymB, file D: a coordinate that is étale at finitely many points

For a Dedekind domain `B` over an infinite field `k` and finitely many `k`-points `T`, there is `x ∈ B` with
`k[x] + ⋂_{φ ∈ T} (ker φ)^n = B` for every `n` (`x - φ(x)` is a uniformiser at each point, the `φ(x)` distinct).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacSym

section Coord

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra k B]

omit [IsDedekindDomain B] in
theorem sub_algebraMap_mem_ker (φ : B →ₐ[k] k) (r : B) : r - algebraMap k B (φ r) ∈ RingHom.ker φ := by
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

omit [Algebra k B] in
/-- At a uniformiser `y ∈ P \ P^2` of a maximal ideal of a Dedekind domain: `P = (y) + P^2`. -/
theorem eq_span_sup_sq {P : Ideal B} [hPm : P.IsMaximal] {y : B} (hy : y ∈ P) (hx : y ∉ P ^ 2) :
    P = Ideal.span {y} ⊔ P ^ 2 := by
  have hP : P ≠ ⊥ := by
    rintro rfl
    exact hx (by rw [Ideal.mem_bot.1 hy]; exact zero_mem _)
  have hpr : Prime P := Ideal.prime_of_isPrime hP hPm.isPrime
  have hIP : Ideal.span {y} ⊔ P ^ 2 ≤ P :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hy) (Ideal.pow_le_self (by norm_num))
  have hdvd : Ideal.span {y} ⊔ P ^ 2 ∣ P ^ 2 := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨i, hi, hassoc⟩ := (dvd_prime_pow hpr 2).1 hdvd
  rw [associated_iff_eq] at hassoc
  interval_cases i
  · rw [hassoc, pow_zero, Ideal.one_eq_top, top_le_iff] at hIP
    exact absurd hIP hPm.ne_top
  · rw [pow_one] at hassoc; exact hassoc.symm
  · exact absurd (hassoc ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self y)) hx

omit [IsDedekindDomain B] [Algebra k B] in
theorem pow_le_span_sup {P : Ideal B} {y : B} (hy : y ∈ P) (hPy : P = Ideal.span {y} ⊔ P ^ 2) (m : ℕ) :
    P ^ m ≤ Ideal.span {y ^ m} ⊔ P ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hym : Ideal.span {y ^ m} ≤ P ^ m := (Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hy m)
    have hy1 : Ideal.span {y} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 hy
    calc P ^ (m + 1) = P ^ m * P := pow_succ P m
      _ ≤ (Ideal.span {y ^ m} ⊔ P ^ (m + 1)) * (Ideal.span {y} ⊔ P ^ 2) := Ideal.mul_mono ih hPy.le
      _ ≤ Ideal.span {y ^ (m + 1)} ⊔ P ^ (m + 1 + 1) := by
        rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
        refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
        · rw [Ideal.span_singleton_mul_span_singleton, ← pow_succ]; exact le_sup_left
        · refine le_sup_of_le_right ?_
          calc Ideal.span {y ^ m} * P ^ 2 ≤ P ^ m * P ^ 2 := Ideal.mul_mono_left hym
            _ = P ^ (m + 1 + 1) := by rw [← pow_add]
        · refine le_sup_of_le_right ?_
          calc P ^ (m + 1) * Ideal.span {y} ≤ P ^ (m + 1) * P := Ideal.mul_mono_right hy1
            _ = P ^ (m + 1 + 1) := (pow_succ P (m + 1)).symm
        · refine le_sup_of_le_right ?_
          rw [← pow_add]
          exact Ideal.pow_le_pow_right (by omega)

/-- One point: `k[x] + P^m = B` when `x - φ x` is a uniformiser at `P = ker φ`. -/
theorem exists_poly_single (φ : B →ₐ[k] k) (x : B) (hx : x - algebraMap k B (φ x) ∉ RingHom.ker φ ^ 2)
    (m : ℕ) (b : B) : ∃ p : k[X], b - aeval x p ∈ RingHom.ker φ ^ m := by
  have : (RingHom.ker φ).IsMaximal := ker_isMaximal φ
  have hy := sub_algebraMap_mem_ker φ x
  have hPy := eq_span_sup_sq hy hx
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (pow_le_span_sup hy hPy m hp)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hu
    refine ⟨p + C (φ r) * (X - C (φ x)) ^ m, ?_⟩
    have he : b - aeval x (p + C (φ r) * (X - C (φ x)) ^ m) =
        (r - algebraMap k B (φ r)) * (x - algebraMap k B (φ x)) ^ m + v := by
      simp only [map_add, map_mul, aeval_C, map_pow, map_sub, aeval_X]
      linear_combination (-1 : B) * huv
    rw [he]
    refine add_mem ?_ hv
    rw [pow_succ']
    exact Ideal.mul_mem_mul (sub_algebraMap_mem_ker φ r) (Ideal.pow_mem_pow hy m)

/-- Finitely many points: one `x` with `k[x] + P^n = B` at every point of `T`, for every `n`. -/
theorem exists_coord [Infinite k] (hB : ¬ IsField B) (T : Finset (B →ₐ[k] k)) :
    ∃ x : B, ∀ n : ℕ, ∀ b : B, ∃ p : k[X], ∀ φ ∈ T, b - aeval x p ∈ RingHom.ker φ ^ n := by
  classical
  let c : (B →ₐ[k] k) → k := fun φ =>
    if h : φ ∈ T then Infinite.natEmbedding k (T.equivFin ⟨φ, h⟩ : ℕ) else 0
  have hc : ∀ φ ∈ T, ∀ ψ ∈ T, c φ = c ψ → φ = ψ := by
    intro φ hφ ψ hψ h
    simp only [c, dif_pos hφ, dif_pos hψ] at h
    have h1 := T.equivFin.injective (Fin.ext ((Infinite.natEmbedding k).injective h))
    exact congrArg Subtype.val h1
  have hπ : ∀ φ : B →ₐ[k] k, ∃ π ∈ RingHom.ker φ, π ∉ RingHom.ker φ ^ 2 := by
    intro φ
    have hm := ker_isMaximal φ
    have hP : RingHom.ker φ ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm hB
    have hlt : RingHom.ker φ ^ 2 < RingHom.ker φ ^ 1 :=
      Ideal.pow_right_strictAnti _ hP hm.ne_top (by norm_num)
    rw [pow_one] at hlt
    obtain ⟨π, h1, h2⟩ := SetLike.exists_of_lt hlt
    exact ⟨π, h1, h2⟩
  choose π hπP hπ2 using hπ
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun φ => RingHom.ker φ) (fun _ => 2)
    (fun φ _ => Ideal.prime_of_isPrime (Ring.ne_bot_of_isMaximal_of_not_isField (ker_isMaximal φ) hB)
      (ker_isMaximal φ).isPrime)
    (fun φ _ ψ _ hne h => hne (algHom_eq_of_ker_eq h))
    (fun φ => algebraMap k B (c φ.1) + π φ.1)
  have hx' : ∀ φ ∈ T, x - (algebraMap k B (c φ) + π φ) ∈ RingHom.ker φ ^ 2 := fun φ hφ => hx φ hφ
  have hxφ : ∀ φ ∈ T, φ x = c φ := by
    intro φ hφ
    have h' : x - (algebraMap k B (c φ) + π φ) ∈ RingHom.ker φ := Ideal.pow_le_self (by norm_num) (hx' φ hφ)
    rw [RingHom.mem_ker, map_sub, map_add, AlgHom.commutes, (RingHom.mem_ker).1 (hπP φ)] at h'
    simpa [sub_eq_zero] using h'
  have hunif : ∀ φ ∈ T, x - algebraMap k B (φ x) ∉ RingHom.ker φ ^ 2 := by
    intro φ hφ hmem
    apply hπ2 φ
    have h1 := sub_mem hmem (hx' φ hφ)
    rw [hxφ φ hφ] at h1
    convert h1 using 1
    ring
  refine ⟨x, fun n b => ?_⟩
  choose p hp using fun φ : T => exists_poly_single φ.1 x (hunif φ.1 φ.2) n b
  have hcop : Pairwise (Function.onFun IsCoprime fun φ : T => Ideal.span {((X : k[X]) - C (c φ.1)) ^ n}) := by
    intro φ ψ hne
    rw [Function.onFun, Ideal.isCoprime_span_singleton_iff]
    apply IsCoprime.pow
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero, sub_ne_zero]
    intro h
    exact hne (Subtype.ext (hc _ φ.2 _ ψ.2 h))
  obtain ⟨q, hq⟩ := Ideal.exists_forall_sub_mem_ideal hcop p
  refine ⟨q, fun φ hφ => ?_⟩
  have h1 := hp ⟨φ, hφ⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hq ⟨φ, hφ⟩)
  have h2 : aeval x q - aeval x (p ⟨φ, hφ⟩) ∈ RingHom.ker φ ^ n := by
    rw [← map_sub, ← hr, map_mul, map_pow, map_sub, aeval_X, aeval_C, ← hxφ φ hφ]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (sub_algebraMap_mem_ker φ x) n)
  have h3 := sub_mem h1 h2
  convert h3 using 1
  ring

omit [IsDedekindDomain B] in
/-- `⋂ P^n ≤ (⋂ P)^n` for finitely many distinct `k`-points. -/
theorem iInf_pow_le_pow_iInf (T : Finset (B →ₐ[k] k)) (n : ℕ) :
    (⨅ φ ∈ T, RingHom.ker φ ^ n) ≤ (⨅ φ ∈ T, RingHom.ker φ) ^ n := by
  classical
  have hcop : (T : Set (B →ₐ[k] k)).Pairwise (Function.onFun IsCoprime fun φ => RingHom.ker φ ^ n) := by
    intro φ _ ψ _ hne
    have := ker_isMaximal φ
    have := ker_isMaximal ψ
    exact (Ideal.isCoprime_of_isMaximal (fun h => hne (algHom_eq_of_ker_eq h))).pow
  rw [← Ideal.prod_eq_iInf_of_pairwise_isCoprime hcop, Finset.prod_pow, ← Finset.inf_eq_iInf]
  exact Ideal.pow_right_mono Ideal.prod_le_inf n

end Coord

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_Ker2 =====
section

/-!
# S4-JacSymB, file E1: functions vanishing to high order along the fibre lie in `M^2`

For a `k`-point `symPt a` of `Sym^g X` with maximal ideal `M`, and `K_n = ⋂_{ψ ∈ a} (ker ψ)^n`, the kernel of
`Sym^g B → Sym^g (B / K_n)` lies in `M^2` for `n` large (radical + Artin-Rees for the finite module `X^g`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Ker2

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B] {g : ℕ}

omit [IsDomain B] in
open scoped Classical in
/-- The coordinate copies of the ideal of the support lie in the radical of `M · X^g`. -/
theorem span_inc_le_radical (a : Fin g → (B →ₐ[k] k)) :
    Ideal.span (⋃ l : Fin g, inc l '' ((⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ : Ideal B) : Set B)) ≤
      (Ideal.map (algebraMap (SymRing k B g) (XPow k B g)) (RingHom.ker (symPt a))).radical := by
  classical
  rw [Ideal.radical_eq_sInf, le_sInf_iff]
  rintro Q ⟨hQ, hQp⟩
  have hc : Q.comap (algebraMap (SymRing k B g) (XPow k B g)) = RingHom.ker (symPt a) :=
    ((ker_isMaximal (symPt a)).eq_of_le (Ideal.comap_ne_top _ hQp.ne_top)
      (Ideal.map_le_iff_le_comap.1 hQ)).symm
  have hQm : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap Q (hc ▸ ker_isMaximal _)
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq (k := k) Q
  let b : Fin g → (B →ₐ[k] k) := fun l => ψ.comp (inc l)
  have hψb : ψ = ptOf b := algHom_ext_inc (fun l => (ptOf_inc b l).symm)
  have hsym : symPt b = symPt a := by
    apply algHom_eq_of_ker_eq
    rw [← hc]
    ext s
    rw [RingHom.mem_ker, Ideal.mem_comap, ← hψ, RingHom.mem_ker, hψb]
    rfl
  have hm := mset_eq_of_symPt_eq b a hsym
  rw [Ideal.span_le]
  intro t ht
  rw [Set.mem_iUnion] at ht
  obtain ⟨l, j, hj, rfl⟩ := ht
  have hbl : b l ∈ Finset.univ.image a := by
    have hmem : b l ∈ (mset b : Multiset (B →ₐ[k] k)) := by simp [mset_coe]
    rw [hm, mset_coe] at hmem
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hmem
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hj' : j ∈ RingHom.ker (b l) := Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 hj (b l)) hbl
  rw [SetLike.mem_coe, ← hψ, RingHom.mem_ker]
  exact (RingHom.mem_ker).1 hj'

omit [IsAlgClosed k] [IsDomain B] in
/-- Artin-Rees for the finite `Sym^g`-module `X^g`: `Sym^g ∩ M^(c+2) X^g ⊆ M^2`. -/
theorem exists_artinRees (M : Ideal (SymRing k B g)) :
    ∃ c : ℕ, ∀ s : SymRing k B g,
      (s : XPow k B g) ∈ Ideal.map (algebraMap (SymRing k B g) (XPow k B g)) (M ^ (c + 2)) → s ∈ M ^ 2 := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul M
    (LinearMap.range (Algebra.linearMap (SymRing k B g) (XPow k B g)))
  refine ⟨c, fun s hs => ?_⟩
  have h1 : (s : XPow k B g) ∈ M ^ (c + 2) • (⊤ : Submodule (SymRing k B g) (XPow k B g)) ⊓
      LinearMap.range (Algebra.linearMap (SymRing k B g) (XPow k B g)) := by
    refine ⟨?_, ⟨s, rfl⟩⟩
    rw [Ideal.smul_top_eq_map]
    exact hs
  rw [hc (c + 2) (by omega), show c + 2 - c = 2 by omega] at h1
  have key : ∀ t ∈ M ^ 2 • (M ^ c • (⊤ : Submodule (SymRing k B g) (XPow k B g)) ⊓
      LinearMap.range (Algebra.linearMap (SymRing k B g) (XPow k B g))),
      ∃ s' ∈ M ^ 2, (s' : XPow k B g) = t := by
    intro t ht
    refine Submodule.smul_induction_on (p := fun t => ∃ s' ∈ M ^ 2, (s' : XPow k B g) = t) ht ?_ ?_
    · intro r hr n hn
      obtain ⟨s0, rfl⟩ := hn.2
      exact ⟨r * s0, Ideal.mul_mem_right _ _ hr, by simp [Algebra.smul_def]⟩
    · rintro x y ⟨s1, h1, rfl⟩ ⟨s2, h2, rfl⟩
      exact ⟨s1 + s2, add_mem h1 h2, by simp⟩
  obtain ⟨s', hs', he⟩ := key _ h1
  rwa [Subtype.val_injective he] at hs'

omit [IsDomain B] in
open scoped Classical in
/-- **Step (i).** Functions on `Sym^g X` vanishing on the `n`-th fibre neighbourhood lie in `M^2`, `n` large. -/
theorem exists_ker_symMap_le_sq (a : Fin g → (B →ₐ[k] k)) :
    ∃ n : ℕ, RingHom.ker (symMap (g := g)
      (Ideal.Quotient.mkₐ k (⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ ^ n))) ≤ RingHom.ker (symPt a) ^ 2 := by
  classical
  obtain ⟨r, hr⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (span_inc_le_radical a)
    (IsNoetherian.noetherian _)
  obtain ⟨c, hc⟩ := exists_artinRees (RingHom.ker (symPt a))
  refine ⟨r * (c + 2), fun s hs => hc s ?_⟩
  set K : Ideal B := ⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ ^ (r * (c + 2))
  have h1 : (s : XPow k B g) ∈ RingHom.ker (xMap (g := g) (Ideal.Quotient.mkₐ k K)) := by
    rw [RingHom.mem_ker] at hs ⊢
    exact congrArg Subtype.val hs
  have h2 := ker_xMap_le _ (Ideal.Quotient.mkₐ_surjective k K) h1
  have hK : RingHom.ker (Ideal.Quotient.mkₐ k K) = K := by
    ext x
    rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  rw [hK] at h2
  refine (?_ : Ideal.span (⋃ l : Fin g, inc l '' (K : Set B)) ≤ _) h2
  rw [Ideal.span_le]
  intro t ht
  rw [Set.mem_iUnion] at ht
  obtain ⟨l, j, hj, rfl⟩ := ht
  have hjJ := iInf_pow_le_pow_iInf (k := k) (Finset.univ.image a) (r * (c + 2)) hj
  have hmap : Ideal.map (inc (k := k) l) ((⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ) ^ (r * (c + 2))) ≤
      Ideal.span (⋃ l : Fin g, inc l '' ((⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ : Ideal B) : Set B)) ^
        (r * (c + 2)) := by
    rw [Ideal.map_pow]
    apply Ideal.pow_right_mono
    rw [Ideal.map_le_iff_le_comap]
    intro j' hj'
    exact Ideal.subset_span (Set.mem_iUnion.2 ⟨l, j', hj', rfl⟩)
  have h3 := hmap (Ideal.mem_map_of_mem _ hjJ)
  rw [pow_mul] at h3
  rw [SetLike.mem_coe, Ideal.map_pow]
  exact Ideal.pow_right_mono hr _ h3

end Ker2

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_Height =====
section

/-!
# S4-JacSymB, file E2: every maximal ideal of `Sym^g X` has height at least `g`

Specialising the first `j` coordinates at a `k`-point gives a strictly increasing chain of `g + 1` primes of `X^g`
below the point; integrality (incomparability) keeps it strict on `Sym^g X`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Height

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B] {g : ℕ}

/-- Specialise the coordinates `l < j` at `a l`. -/
noncomputable def specHom (a : Fin g → (B →ₐ[k] k)) (j : ℕ) : XPow k B g →ₐ[k] XPow k B g :=
  liftFam (fun l => if (l : ℕ) < j then (Algebra.ofId k (XPow k B g)).comp (a l) else inc l)

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] in
theorem specHom_inc (a : Fin g → (B →ₐ[k] k)) (j : ℕ) (l : Fin g) :
    (specHom a j).comp (inc l) = if (l : ℕ) < j then (Algebra.ofId k (XPow k B g)).comp (a l) else inc l :=
  liftFam_inc _ l

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] in
theorem specHom_succ (a : Fin g → (B →ₐ[k] k)) (j : ℕ) :
    specHom a (j + 1) = (liftFam (fun l : Fin g =>
      if (l : ℕ) = j then (Algebra.ofId k (XPow k B g)).comp (a l) else inc l)).comp (specHom a j) := by
  apply PiTensorProduct.algHom_ext
  intro l
  change (specHom a (j + 1)).comp (inc l) = ((liftFam _).comp (specHom a j)).comp (inc l)
  rw [AlgHom.comp_assoc, specHom_inc, specHom_inc]
  by_cases h1 : (l : ℕ) < j
  · rw [if_pos (by omega : (l : ℕ) < j + 1), if_pos h1]
    ext b
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes]
  · rw [if_neg h1, liftFam_inc]
    by_cases h2 : (l : ℕ) = j
    · rw [if_pos (by omega : (l : ℕ) < j + 1), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] in
theorem ker_specHom_le_succ (a : Fin g → (B →ₐ[k] k)) (j : ℕ) :
    RingHom.ker (specHom a j) ≤ RingHom.ker (specHom a (j + 1)) := by
  intro t ht
  rw [RingHom.mem_ker] at ht ⊢
  rw [specHom_succ, AlgHom.comp_apply, ht, map_zero]

theorem exists_mem_ker_specHom_succ (hB : ¬ IsField B) (a : Fin g → (B →ₐ[k] k)) (j : ℕ) (hj : j < g) :
    ∃ t, t ∈ RingHom.ker (specHom a (j + 1)) ∧ t ∉ RingHom.ker (specHom a j) := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ring.ne_bot_of_isMaximal_of_not_isField (ker_isMaximal (a ⟨j, hj⟩)) hB)
  refine ⟨inc ⟨j, hj⟩ π, ?_, ?_⟩
  · rw [RingHom.mem_ker, ← AlgHom.comp_apply, specHom_inc, if_pos (by simp), AlgHom.comp_apply,
      (RingHom.mem_ker).1 hπ, map_zero]
  · rw [RingHom.mem_ker, ← AlgHom.comp_apply, specHom_inc, if_neg (by simp)]
    intro h0
    apply hπ0
    apply eq_zero_of_forall_pt (k := k)
    intro x0
    have h1 := congrArg (ptOf (fun _ : Fin g => x0)) h0
    rw [← AlgHom.comp_apply, ptOf_inc, map_zero] at h1
    exact h1

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] in
theorem specHom_top (a : Fin g → (B →ₐ[k] k)) :
    specHom a g = (Algebra.ofId k (XPow k B g)).comp (ptOf a) := by
  apply PiTensorProduct.algHom_ext
  intro l
  change (specHom a g).comp (inc l) = ((Algebra.ofId k (XPow k B g)).comp (ptOf a)).comp (inc l)
  rw [specHom_inc, if_pos l.2, AlgHom.comp_assoc, ptOf_inc]

/-- Height of a `k`-point of `Sym^g X` is at least `g`. -/
theorem le_height_ker (hB : ¬ IsField B) (a : Fin g → (B →ₐ[k] k)) :
    (g : ℕ∞) ≤ (RingHom.ker (symPt a)).height := by
  have : IsDomain (XPow k B g) := isDomain_xPow k B g
  have hpr : ∀ j, (RingHom.ker (specHom a j)).IsPrime := fun j => RingHom.ker_isPrime _
  have key : ∀ j ≤ g, (j : ℕ∞) ≤
      ((RingHom.ker (specHom a j)).comap (algebraMap (SymRing k B g) (XPow k B g))).height := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨t, ht1, ht2⟩ := exists_mem_ker_specHom_succ hB a j (by omega)
      have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := SymRing k B g) (ker_specHom_le_succ a j)
        ⟨ht1, ht2⟩ (Algebra.IsIntegral.isIntegral t)
      calc ((j + 1 : ℕ) : ℕ∞) = (j : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ ((RingHom.ker (specHom a j)).comap (algebraMap (SymRing k B g) (XPow k B g))).height + 1 := by
          gcongr
          exact ih (by omega)
        _ ≤ _ := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  refine (key g le_rfl).trans (Ideal.height_mono ?_)
  intro s hs
  rw [Ideal.mem_comap, RingHom.mem_ker, specHom_top, AlgHom.comp_apply, Algebra.ofId_apply] at hs
  rw [RingHom.mem_ker]
  exact (algebraMap k (XPow k B g)).injective (by rw [map_zero]; exact hs)

/-- The local ring of `Sym^g X` at a closed point has dimension at least `g`. -/
theorem le_ringKrullDim_localization (hB : ¬ IsField B) (M : Ideal (SymRing k B g)) [M.IsMaximal] :
    (g : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime M) := by
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) M
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M)
  refine le_of_le_of_eq ?_ h.symm
  rw [← hφ, ← symPt_liftTuple φ]
  exact_mod_cast le_height_ker hB (liftTuple φ)

end Height

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB_Reg =====
section

/-!
# S4-JacSymB, file E3: `Sym^g` of a smooth affine curve is regular at closed points (L11)

For a Dedekind domain `B` of finite type over an algebraically closed field `k` (not a field), the local ring of
`Sym^g B` at every maximal ideal is a regular local ring of dimension `g`. The maximal ideal is generated modulo `M^2`
by the `g` elementary symmetric functions of the étale coordinate (files Coord, Ker2, Poly), Nakayama gives `g`
generators, and the height chain (file Height) gives dimension `≥ g`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Reg

open Polynomial

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra k B]
  [Algebra.FiniteType k B] {g : ℕ}

omit [Algebra.FiniteType k B] in
open scoped Classical in
/-- The étale coordinate gives a surjection `k[X] → B / K_n`. -/
theorem exists_surj_coord (hB : ¬ IsField B) (a : Fin g → (B →ₐ[k] k)) (n : ℕ) :
    ∃ x : B, Function.Surjective ((Ideal.Quotient.mkₐ k (⨅ ψ ∈ Finset.univ.image a, RingHom.ker ψ ^ n)).comp
      (aeval x : k[X] →ₐ[k] B)) := by
  obtain ⟨x, hx⟩ := exists_coord hB (Finset.univ.image a)
  refine ⟨x, fun y => ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ y
  obtain ⟨p, hp⟩ := hx n b
  refine ⟨p, ?_⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq]
  simp only [Submodule.mem_iInf]
  intro ψ hψ
  rw [← neg_sub]
  exact neg_mem (hp ψ hψ)

/-- The maximal ideal of a closed point of `Sym^g` is generated by `g` elements modulo `M^2`. -/
theorem le_span_sup_sq (hB : ¬ IsField B) (M : Ideal (SymRing k B g)) [M.IsMaximal] :
    ∃ y : Fin g → SymRing k B g, (∀ j, y j ∈ M) ∧ M ≤ Ideal.span (Set.range y) ⊔ M ^ 2 := by
  classical
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) M
  have ha : symPt (liftTuple φ) = φ := symPt_liftTuple φ
  obtain ⟨n, hn⟩ := exists_ker_symMap_le_sq (liftTuple φ)
  obtain ⟨x, hx⟩ := exists_surj_coord hB (liftTuple φ) n
  rw [ha, hφ] at hn
  have hsurj := symMap_surjective (g := g) _ hx
  rw [symMap_comp] at hsurj
  let e := symPolyEquiv k g
  let ψ0 : SymRing k k[X] g →ₐ[k] k := φ.comp (symMap (g := g) (aeval x : k[X] →ₐ[k] B))
  let z : Fin g → SymRing k k[X] g := fun j =>
    e.symm (MvPolynomial.X j) - algebraMap k _ (ψ0 (e.symm (MvPolynomial.X j)))
  have hz : RingHom.ker ψ0 = Ideal.span (Set.range z) := ker_eq_span_of_equiv e ψ0
  refine ⟨fun j => symMap (aeval x : k[X] →ₐ[k] B) (z j), fun j => ?_, fun m hm => ?_⟩
  · have hzj : z j ∈ RingHom.ker ψ0 := hz ▸ Ideal.subset_span ⟨j, rfl⟩
    rw [← hφ, RingHom.mem_ker]
    exact hzj
  · obtain ⟨p, hp⟩ := hsurj (symMap (Ideal.Quotient.mkₐ k _) m)
    have h1 : symMap (Ideal.Quotient.mkₐ k _) (symMap (aeval x : k[X] →ₐ[k] B) p) =
        symMap (Ideal.Quotient.mkₐ k _) m := hp
    have hd : m - symMap (aeval x : k[X] →ₐ[k] B) p ∈ M ^ 2 :=
      hn (by rw [RingHom.mem_ker, map_sub, h1, sub_self])
    have hM2 : M ^ 2 ≤ M := Ideal.pow_le_self two_ne_zero
    have h2 : symMap (aeval x : k[X] →ₐ[k] B) p ∈ M := by
      have h3 := M.sub_mem hm (hM2 hd)
      rwa [sub_sub_cancel] at h3
    have hp0 : p ∈ RingHom.ker ψ0 := by
      rw [← hφ, RingHom.mem_ker] at h2
      exact h2
    have hmap : symMap (aeval x : k[X] →ₐ[k] B) p ∈
        Ideal.span (Set.range fun j => symMap (aeval x : k[X] →ₐ[k] B) (z j)) := by
      have h4 := Ideal.mem_map_of_mem (symMap (g := g) (aeval x : k[X] →ₐ[k] B)) hp0
      rw [hz, Ideal.map_span, ← Set.range_comp] at h4
      exact h4
    rw [← add_sub_cancel (symMap (aeval x : k[X] →ₐ[k] B) p) m]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hmap) (Ideal.mem_sup_right hd)

omit [IsAlgClosed k] [Algebra k B] [Algebra.FiniteType k B] [IsDedekindDomain B] in
/-- A Noetherian local ring whose maximal ideal is generated by `g` elements modulo its square, and whose dimension is
at least `g`, is regular of dimension `g` (Nakayama). -/
theorem isRegular_of_le_span_sup_sq {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (y : Fin g → R) (hy : ∀ j, y j ∈ IsLocalRing.maximalIdeal R)
    (h : IsLocalRing.maximalIdeal R ≤ Ideal.span (Set.range y) ⊔ IsLocalRing.maximalIdeal R ^ 2)
    (hdim : (g : WithBot ℕ∞) ≤ ringKrullDim R) : IsRegularLocalRing R ∧ ringKrullDim R = g := by
  have hle : IsLocalRing.maximalIdeal R ≤ Ideal.span (Set.range y) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
    rwa [Ideal.smul_eq_mul, ← pow_two]
  have hN : IsLocalRing.maximalIdeal R = Ideal.span (Set.range y) :=
    le_antisymm hle (Ideal.span_le.2 (Set.range_subset_iff.2 hy))
  have hrank : (IsLocalRing.maximalIdeal R).spanFinrank ≤ g := by
    rw [hN]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
  have hrank' : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ g := by
    exact_mod_cast hrank
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hrank'.trans hdim), le_antisymm ?_ hdim⟩
  exact (ringKrullDim_le_spanFinrank_maximalIdeal _).trans hrank'

/-- **L11.** The local ring of `Sym^g X` at every closed point is a regular local ring of dimension `g`. -/
theorem isRegularLocalRing_symRing (hB : ¬ IsField B) (M : Ideal (SymRing k B g)) [M.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime M) ∧ ringKrullDim (Localization.AtPrime M) = g := by
  obtain ⟨y, hyM, hle⟩ := le_span_sup_sq hB M
  refine isRegular_of_le_span_sup_sq (algebraMap (SymRing k B g) (Localization.AtPrime M) ∘ y) (fun j => ?_) ?_
    (le_ringKrullDim_localization hB M)
  · rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hyM j)
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    refine (Ideal.map_mono hle).trans ?_
    rw [Ideal.map_sup, Ideal.map_span, ← Set.range_comp]

end Reg

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_JacSymB =====
section

/-!
# S4-JacSymB umbrella: `Sym^g A^1 = A^g`, regularity of `Sym^g` of a smooth curve, `Sym^g X` glued and proper

* **L10** `symPolyEquiv k g : SymRing k k[X] g ≃ₐ[k] MvPolynomial (Fin g) k` (`Def_RP_JacSymB_Poly`).
* **L11** `isRegularLocalRing_symRing`: for a Dedekind `k`-algebra `B` of finite type (`k` algebraically closed, `B` not a
  field) every local ring of `Sym^g B` at a maximal ideal is regular of dimension `g` (`Def_RP_JacSymB_Reg`).
* **L12** `SymX k x g := colimit (symDiagram k x g)` glued from the charts `Spec Sym^g B_A`
  (`Def_RP_JacSymB_Glue`), with `toSpecK k x g : SymX k x g ⟶ Spec k` locally of finite type and quasi-compact
  (`_Cover`), separated (`_Sep`), universally closed and proper (`_Exist`); the singleton charts cover `SymX`
  (`exists_mem_range_ι_single`) and their local rings at closed points are regular of dimension `g`
  (`isRegularLocalRing_chart` below).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Umbrella

variable {k : Type*} [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F] {x : F} {g : ℕ}
  [FiniteDimensional (IntermediateField.adjoin k {x}) F] [Algebra.IsSeparable (IntermediateField.adjoin k {x}) F]

/-- **L11 on the charts of `Sym^g X`**: the local ring of `Sym^g B_{c}` at a maximal ideal is regular of dimension `g`. -/
theorem isRegularLocalRing_chart (hx : Transcendental k x) (c : k) (M : Ideal (SymRing k (chartRing x {c}) g))
    [M.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime M) ∧ ringKrullDim (Localization.AtPrime M) = g := by
  have := isDedekindDomain_chartRing_single hx c
  have := finiteType_chartRing hx (Finset.singleton_nonempty c)
  exact isRegularLocalRing_symRing (not_isField_chartRing_single hx c) M

end Umbrella

end RamanujanPetersson.JacSym


end

-- ===== S4.Def_RP_ThetaCube_Cover =====
section

/-!
# S4-ThetaCube, file Cover (D-A, rest): the line test on `X1^n`

* `coheight_kpt_X1`: `K`-points of `X1` have codimension one (singleton chart, `Sym¹` regular of dimension one);
* **`eq_zero_of_lines`**: let `E` be a Weil divisor on `X1^n` (factorial stalks) and, for each direction `i`, `B i`
  a proper closed subset, saturated for the `i`-th lines, such that for every `K`-point `p ∉ B i` the `i`-th line
  through `p` avoids `E` and pulls `E` back to `0` at the parameter of `p`. Then `E = 0`.
  Proof: a point `y` of codimension one off some `B i` is handled by the curve test (`eq_zero_of_tests`) with the
  `i`-th lines through the closed points of `(B i)ᶜ`. If `y ∈ ⋂ B i`, then `Y = closure {y}` is a component of every
  `B i`; off the other components every line through a point of `Y` stays in `Y`, so `Y = X1^n` by `reach`, and `y`
  would be the generic point.
* `eq_zero_of_lines'`: the same with `ℓ^* E = 0` as a cycle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Cover

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance locallyOfFiniteType_X1O : LocallyOfFiniteType (X1O K F).hom :=
  (inferInstance : LocallyOfFiniteType (toSpecK K (algebraMap K[X] F X) 1))

instance isLocallyNoetherian_X1O : IsLocallyNoetherian (X1O K F).left :=
  LocallyOfFiniteType.isLocallyNoetherian (X1O K F).hom

instance isLocallyNoetherian_PPl (n : ℕ) : IsLocallyNoetherian (PP K F n).left :=
  LocallyOfFiniteType.isLocallyNoetherian (PP K F n).hom

set_option synthInstance.maxHeartbeats 400000 in
/-- Closed points of the singleton chart `Spec Sym¹ B_c` have codimension one. -/
theorem coheight_chartPt (c : K) (p : Spec (.of (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1)))
    (hpc : IsClosed ({p} : Set (Spec (.of (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1))))) :
    Order.coheight p = 1 := by
  let M : Ideal (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1) := p.asIdeal
  haveI : M.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hpc
  have h2 := IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M)
  have h3 := (JacSym.isRegularLocalRing_chart (k := K) (F := F) (x := algebraMap K[X] F X) (g := 1)
    (transcendental_xF K F) c M).2
  rw [h3] at h2
  have h : M.height = Order.coheight p := idealHeight_eq_coheight _ p
  rw [← h]
  exact_mod_cast h2.symm

/-- Closed points of `X1` have codimension one. -/
theorem coheight_closed_X1 {t : X1 K F} (ht : IsClosed ({t} : Set (X1 K F))) : Order.coheight t = 1 := by
  obtain ⟨c, -, p, rfl⟩ := JacSym.exists_mem_range_ι_single K (algebraMap K[X] F X) 1 ({0, 1} : Finset K)
    (by rw [Finset.card_pair zero_ne_one]; norm_num) t
  let A : (ChartIdx K)ᵒᵖ := op ⟨{c}, Finset.singleton_nonempty c⟩
  haveI := isOpenImmersion_ιX1 (K := K) (F := F) A
  have hemb := (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A).isOpenEmbedding
  have hpc : IsClosed ({p} : Set (cht K F A)) := by
    have e2 : (⇑(colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A)) ⁻¹'
        {(colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A) p} = {p} := by
      rw [← Set.image_singleton, hemb.injective.preimage_image]
    exact (congrArg IsClosed e2).mp (ht.preimage hemb.continuous)
  exact (Topology.IsOpenEmbedding.coheight_eq (x := p) _ hemb).trans (coheight_chartPt c p hpc)

/-- **`K`-points of `X1` have codimension one.** -/
theorem coheight_kpt_X1 (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    Order.coheight (q.left (IsLocalRing.closedPoint K)) = 1 :=
  coheight_closed_X1 (pointEquivClosedPoint (X1O K F).hom ⟨q.left, Over.w q⟩).2

variable {n : ℕ} [∀ y : (PP K F n).left, UniqueFactorizationMonoid ((PP K F n).left.presheaf.stalk y)]

end Cover

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Sym =====
section

/-!
# S4-ThetaCube, file Sym (T8b): the symmetric divisor `D' = Θ_{x0} + [-1]^* Θ_{x0}`

* `algebraMap_generic`, **`cpull_eq_pullback`**: for a dominant map, `cpull` is `JacDivisors.pullback`;
* `negJ = (𝟙 J)⁻¹` (the inverse map), `comp_negJ : φ ≫ negJ = φ⁻¹`;
* `DTh P0 x0 := τ_{x0}^* Θ + (negJ ≫ τ_{x0})^* Θ`: Weil (`DTh_mem`), effective (`DTh_nonneg`);
* `avoid_DTh`: every homomorphism avoids `DTh P0 x0` when `x0 ∉ W`;
* **`cpull_DTh`**: `φ^* D' = (φ ≫ τ_{x0})^* Θ + (φ⁻¹ ≫ τ_{x0})^* Θ`;
* **`cpull_inv_DTh`**: `(φ⁻¹)^* D' = φ^* D'` (exact symmetry).
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section General

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (φ : C ⟶ Y) [IsDominant φ]

/-- For a dominant map, the Cartier pull-back is the pull-back of `JacDivisors`. -/
lemma cpull_eq_pullback {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hA : Avoid φ D) :
    cpull φ D = JacDivisors.pullback φ D := by
  ext x
  obtain ⟨hg, V, hV, hxV, hDV⟩ := isLocEq_locEq hD (φ x)
  have hloc : IsLocEq D (φ x) (locEq D (φ x)) := ⟨hg, V, hV, hxV, hDV⟩
  obtain ⟨ug, -, hg'⟩ := exists_unit_of_isLocEq φ hA hloc
  rw [cpull_eq_of φ hD hA hloc, pullback_eq_div_of φ hD hg hV hDV hxV, div_apply, ← hg', fpull_algebraMap,
    ffMap_algebraMap φ (genericPoint C) ug, algebraMap_generic]

end General

section Theta

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

end Theta

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Surj =====
section

/-!
# S4-ThetaCube, file Surj (D-C2): a surjection from `X1^n` detects Weil divisors by lines

Let `Φ : X1^n ⟶ Y` be surjective (`Y` integral, locally Noetherian, factorial stalks) and `E` a Weil divisor on `Y`
such that for every `K`-point `p` of `X1^n` and every direction `i`, the composite `line i p ≫ Φ`, whenever it avoids
`E`, pulls `E` back to `0` at the parameter of `p`. Then `E = 0`.
Proof: if `E y > 0` (`y` of codimension one), `exists_open_test` gives an open `U ∋ y` on which (a) every avoiding
test curve through `closure {y} ∩ U` has positive pull-back and (b) every curve through `U` whose generic point
leaves `closure {y}` avoids `E`. Take a component `T'` of `Φ⁻¹ (closure {y})` maximal among those meeting the fibre
over `y`; its generic point lies over `y`. Off the other components, every line through a point of `T' ∩ Φ⁻¹ U`
stays in `T'` (else (b) and (a) contradict the hypothesis), so `T' = X1^n` by `reach`, and `y` would be generic.
* `exists_open_test` (general curves and schemes);
* **`eq_zero_of_surj`** (line hypothesis), **`eq_zero_of_cpull_surj`** (`Φ` dominant, `cpull Φ E = 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Test

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

/-- Near a point `y` of codimension one with `E y > 0`: (a) avoiding test curves through `closure {y}` have positive
pull-back, (b) curves whose generic point leaves `closure {y}` avoid `E`. -/
lemma exists_open_test {E : AlgebraicCycle Y ℤ} (hE : E ∈ weilDivisors Y) {y : Y} (hy : Order.coheight y = 1)
    (hpos : 0 < E y) : ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
      (∀ (ℓ : C ⟶ Y) (x : C), ℓ x ∈ U → ℓ x ∈ closure {y} → Order.coheight x = 1 → Avoid ℓ E →
        0 < cpull ℓ E x) ∧
      (∀ (ℓ : C ⟶ Y) (x : C), ℓ x ∈ U → ℓ (genericPoint C) ∉ closure {y} → Avoid ℓ E) := by
  obtain ⟨t, ht, hfin⟩ := E.supportLocallyFiniteWithinDomain' y (Set.mem_univ y)
  obtain ⟨t', ht't, ht'o, hyt'⟩ := mem_nhds_iff.mp ht
  set S : Set Y := (t ∩ Function.support E) \ {y} with hS
  have hSfin : S.Finite := hfin.sdiff
  set Z : Set Y := ⋃ z ∈ S, closure {z} with hZdef
  have hZ : IsClosed Z := hSfin.isClosed_biUnion fun z _ => isClosed_closure
  have hyZ : y ∉ Z := by
    rw [hZdef, Set.mem_iUnion₂]
    rintro ⟨z, ⟨⟨_, hz⟩, hzy⟩, hyz⟩
    exact not_specializes_of_coheight hy (hE z hz) hzy (specializes_iff_mem_closure.mpr hyz)
  refine ⟨t' ∩ Zᶜ, ht'o.inter hZ.isOpen_compl, ⟨hyt', hyZ⟩, fun ℓ x hxU hxy hx1 hA => ?_,
    fun ℓ x hxU hη => ?_⟩
  · have hnn : ∀ z : Y, z ⤳ ℓ x → Order.coheight z = 1 → 0 ≤ E z := by
      intro z hz _
      by_contra hneg
      replace hneg := not_le.mp hneg
      by_cases hzy : z = y
      · rw [hzy] at hneg
        omega
      · have hzt : z ∈ t := ht't (hz.mem_open ht'o hxU.1)
        apply hxU.2
        rw [hZdef, Set.mem_iUnion₂]
        exact ⟨z, ⟨⟨hzt, hneg.ne⟩, hzy⟩, specializes_iff_mem_closure.mp hz⟩
    exact cpull_pos ℓ hE hA hx1 hnn (specializes_iff_mem_closure.mpr hxy) hpos
  · have hsp := xi_specializes ℓ x
    refine ⟨t' ∩ (Z ∪ closure {y})ᶜ, ht'o.inter (hZ.union isClosed_closure).isOpen_compl,
      ⟨hsp.mem_open ht'o hxU.1, fun h => h.elim (fun hZ' => hxU.2 (hsp.mem_closed hZ hZ')) hη⟩,
      fun w hw => ?_⟩
    by_contra hw0
    apply hw.2
    left
    rw [hZdef, Set.mem_iUnion₂]
    refine ⟨w, ⟨⟨ht't hw.1, hw0⟩, fun hwy => hw.2 (Or.inr ?_)⟩, subset_closure rfl⟩
    rw [Set.mem_singleton_iff.mp hwy]
    exact subset_closure rfl

end Test

section Surj

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]
variable {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]

end Surj

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_SmPP =====
section

/-!
# S4-ThetaCube, file SmPP (D-B0, part 2): `X1` and `X1^n` are smooth, so their stalks are factorial

* `smooth_chart`: the singleton charts `Sym¹ B_c ≅ B_c` of `X1` are smooth over `K` (file SmDed);
* `smooth_X1O`: `X1 → Spec K` is smooth (smoothness is local on the source; singleton charts cover `X1`);
* `smooth_PP`: `X1^n → Spec K` is smooth (base change and composition);
* `ufd_PP`: the stalks of `X1^n` are factorial (`JacDivisors.uniqueFactorizationMonoid_stalk_of_smooth`), so the
  line test `eq_zero_of_lines` and `eq_zero_of_cpull_surj` hold with no extra hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section SmPP

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K F) in
/-- The singleton charts `Sym¹ B_c` of `X1` are smooth over `K`. -/
theorem smooth_chart (c : K) : Algebra.Smooth K (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1) := by
  have := isDedekindDomain_chartRing_single (transcendental_xF K F) c
  have := finiteType_chartRing (transcendental_xF K F) (Finset.singleton_nonempty c)
  have := smooth_of_dedekind (K := K) (not_isField_chartRing_single (transcendental_xF K F) c)
  exact Algebra.Smooth.of_equiv sym1Equiv.symm

/-- Instance search does not find this here (it fails even for `Flat`); state it once. -/
instance isZariskiLocalAtSource_smooth : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
  (HasRingHomProperty.instIsZariskiLocalAtSource : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u})

open Classical in
/-- **`X1` is smooth over `K`.** -/
instance smooth_X1O : Smooth (X1O K F).hom := by
  let 𝒰 : (X1 K F).OpenCover := Scheme.Cover.mkOfCovers K
    (fun c : K => cht K F (op ⟨{c}, Finset.singleton_nonempty c⟩))
    (fun c : K => colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (op ⟨{c}, Finset.singleton_nonempty c⟩))
    (fun t => by
      obtain ⟨c, -, p, hp⟩ := JacSym.exists_mem_range_ι_single K (algebraMap K[X] F X) 1 ({0, 1} : Finset K)
        (by rw [Finset.card_pair zero_ne_one]; norm_num) t
      exact ⟨c, p, hp⟩)
    (fun c : K => isOpenImmersion_ιX1 (K := K) (F := F) _)
  refine IsZariskiLocalAtSource.of_openCover 𝒰 fun c => ?_
  show Smooth (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (op ⟨{c}, Finset.singleton_nonempty c⟩) ≫
    toSpecK K (algebraMap K[X] F X) 1)
  rw [ι_toSpecK]
  have := smooth_chart K F c
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr this)

/-- **`X1^n` is smooth over `K`.** -/
instance smooth_PP (n : ℕ) : Smooth (PP K F n).hom := by
  induction n with
  | zero =>
    show Smooth (𝟙 (Spec (.of K)))
    infer_instance
  | succ n ih =>
    haveI : Smooth (toSpecK K (algebraMap K[X] F X) 1) := smooth_X1O (K := K) (F := F)
    show Smooth (pullback.fst (PP K F n).hom (toSpecK K (algebraMap K[X] F X) 1) ≫ (PP K F n).hom)
    infer_instance

end SmPP

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_FF =====
section

/-!
# S4-ThetaCube, file FF (D-B1, part 1): the function field of `X1` is `F`

* `ffMap_Spec_algebraMap`: `Spec f` acts on fractions through `f`; `isIso_ffMap_openImm`.
* `rhoA A : Sym¹ B_A → F`, `psiA A : K(cht A) → F` (fractions), `PsiA A := psiA A ∘ ι_A^*`;
* `PsiA_eq`: chart independence; `PsiX := PsiA {0}`, `PsiA_eq_PsiX`; `PsiX_surjective`;
* `phiX : F ≃+* K(X1)` (inverse of `PsiX`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section FFSpec

theorem ffMap_Spec_algebraMap {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S] (f : R ⟶ S)
    [IsDominant (Spec.map f)] (r : R) :
    (ffMap (Spec.map f)).hom (algebraMap R (Spec R).functionField r) =
      algebraMap S (Spec S).functionField (f r) := by
  have h2 := stalkMap_toStalk_apply f (genericPoint (Spec S)) r
  have h1 := StructureSheaf.toStalk_stalkSpecializes_apply (R := R)
    (specializes_of_eq (map_genericPoint (Spec.map f))) r
  simp only [ffMap, CommRingCat.comp_apply]
  erw [h1]
  exact h2

theorem isIso_ffMap_openImm {U C : Scheme.{u}} (ι : U ⟶ C) [IsOpenImmersion ι] [IrreducibleSpace U]
    [IrreducibleSpace C] [IsDominant ι] : IsIso (ffMap ι) := by
  have h : ∀ {a b : C} (e : a = b), IsIso (C.presheaf.stalkSpecializes (specializes_of_eq e)) := by
    rintro a b rfl
    have e1 : C.presheaf.stalkSpecializes (specializes_of_eq (rfl : a = a)) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    rw [e1]
    infer_instance
  haveI := h (map_genericPoint ι)
  unfold ffMap
  infer_instance

theorem surjective_ffMap_openImm {U C : Scheme.{u}} (ι : U ⟶ C) [IsOpenImmersion ι] [IrreducibleSpace U]
    [IrreducibleSpace C] [IsDominant ι] : Function.Surjective (ffMap ι).hom := by
  haveI := isIso_ffMap_openImm ι
  intro y
  refine ⟨(inv (ffMap ι)).hom y, ?_⟩
  rw [← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply]

end FFSpec

section FFX1

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance fact_trX : Fact (Transcendental K (algebraMap K[X] F X)) := ⟨transcendental_xF K F⟩

variable (K F) in
/-- The chart ring `Sym¹ B_A` as a commutative ring. -/
noncomputable abbrev RA (A : (ChartIdx K)ᵒᵖ) : CommRingCat.{u} :=
  CommRingCat.of (SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1)

variable (K F) in
/-- `Sym¹ B_A → F`. -/
noncomputable def rhoA (A : (ChartIdx K)ᵒᵖ) : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1 →+* F :=
  (chartRing (algebraMap K[X] F X) A.unop.1).val.toRingHom.comp (sym1Equiv (k := K)).toAlgHom.toRingHom

instance isDomain_RA (A : (ChartIdx K)ᵒᵖ) : IsDomain (RA K F A) :=
  Function.Injective.isDomain (rhoA K F A) (Subtype.val_injective.comp (sym1Equiv (k := K)).injective)

theorem rhoA_apply (A : (ChartIdx K)ᵒᵖ) (r : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) :
    rhoA K F A r = ((undiag1 (k := K) r : chartRing (algebraMap K[X] F X) A.unop.1) : F) := rfl

theorem rhoA_injective (A : (ChartIdx K)ᵒᵖ) : Function.Injective (rhoA K F A) :=
  Subtype.val_injective.comp (sym1Equiv (k := K)).injective

theorem rhoA_diag1 (A : (ChartIdx K)ᵒᵖ) (y : chartRing (algebraMap K[X] F X) A.unop.1) :
    rhoA K F A (diag1 (k := K) y) = (y : F) := by
  rw [rhoA_apply, undiag1_diag1]

theorem rhoA_chartMap {A A' : (ChartIdx K)ᵒᵖ} (h : A ⟶ A')
    (r : SymRing K (chartRing (algebraMap K[X] F X) A'.unop.1) 1) :
    rhoA K F A (chartMap (algebraMap K[X] F X) 1 (leOfHom h.unop) r) = rhoA K F A' r := by
  obtain ⟨b, rfl⟩ := (sym1Equiv (k := K) (B := chartRing (algebraMap K[X] F X) A'.unop.1)).symm.surjective r
  rw [sym1Equiv_symm_apply, chartMap, ← AlgHom.comp_apply, symMap_diag1, AlgHom.comp_apply, rhoA_diag1,
    rhoA_diag1, Subalgebra.coe_inclusion]

theorem ffMap_congr {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] {f g : X ⟶ Y} (e : f = g)
    [IsDominant f] [IsDominant g] : ffMap f = ffMap g := by
  subst e
  rfl

variable (K) in
/-- The chart `{0}`. -/
noncomputable abbrev A0 : (ChartIdx K)ᵒᵖ := op ⟨{0}, Finset.singleton_nonempty 0⟩

theorem isFractionRing_chartRing_single (c : K) : IsFractionRing (chartRing (algebraMap K[X] F X) {c}) F := by
  have hx := transcendental_xF K F
  have hK : K⟮uc (algebraMap K[X] F X) c⟯ = K⟮algebraMap K[X] F X⟯ := adjoin_uc_eq hx c
  have : FiniteDimensional K⟮uc (algebraMap K[X] F X) c⟯ F := hK ▸ inferInstance
  have key : ∀ P : Subalgebra K F, P = Algebra.adjoin K {uc (algebraMap K[X] F X) c} →
      IsFractionRing ((integralClosure P F).restrictScalars K) F := by
    intro P hP
    subst hP
    exact integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin K {uc (algebraMap K[X] F X) c})
      K⟮uc (algebraMap K[X] F X) c⟯ F
  exact key _ (polyA_singleton _ c)

end FFX1

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Ord =====
section

/-!
# S4-ThetaCube, file Ord (D-B1, part 2): orders of vanishing on `X1` are the place orders

* `val_chart_algebraMap`: on a singleton chart, the stalk valuation at `kpt ψ0` is `≤ 1` on the chart ring
  and `< 1` exactly on `ker ψ0`;
* `ord_chart_kpt`: `ord_{kpt ψ0} h = P.ord (psiA h)` for the center `P` of `ψ0`;
* **`ord_kpt`**: `ord_{q} g = (kPl q).ord (PsiX g)`; `ord_phiX_kpt`; `ord_genericPoint_X1 = 0`;
* `isClosed_of_coheight_X1`; **`eq_of_kpt_X1`**: Weil divisors on `X1` agree if they agree at `K`-points.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial
open scoped WithZero

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.JacLaw RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Ord

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (K) in
/-- The singleton chart `{c}`. -/
noncomputable abbrev Ac (c : K) : (ChartIdx K)ᵒᵖ := op ⟨{c}, Finset.singleton_nonempty c⟩

instance isNoetherianRing_single (c : K) :
    IsNoetherianRing (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1) := by
  haveI : Algebra.FiniteType K (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1) :=
    Algebra.FiniteType.equiv (finiteType_chartRing (transcendental_xF K F) (Finset.singleton_nonempty c))
      sym1Equiv.symm
  exact Algebra.FiniteType.isNoetherianRing K _

instance isLocallyNoetherian_cht_single (c : K) : IsLocallyNoetherian (cht K F (Ac K c)) :=
  (inferInstance : IsLocallyNoetherian (Spec (.of (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1))))

theorem rhoA_algebraMap (c : K) (a : K) :
    rhoA K F (Ac K c) (algebraMap K (SymRing K (chartRing (algebraMap K[X] F X) {c}) 1) a) =
      algebraMap K F a := by
  rw [rhoA_apply, AlgHom.commutes]
  rfl

end Ord

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Slice =====
section

/-!
# S4-ThetaCube, file Slice (D-B2, part 2): `det_k` on `X1^n` and its slices along lines
* `line_prj_self`, `line_prj_ne`: a line against the projections;
* `cval q g` (the constant `g(q)` as an element of `F`), **`cval_mem`**: it lies in `K`;
* `exists_stalk_of_ord`: nonnegative place order at `q` ⇒ regular at the point `q`;
* `zPP`, `detPP` (the determinant `det_k`), `sliceRow`;
* **`slice_detPP`**: `PsiX (fpull line (detPP ..)) = det (sliceRow ..)`; **`avoid_detPP`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Slice

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

lemma toUnit_comp_apply {T : Over (Spec (.of K))} (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (x : T.left) :
    (toUnit T ≫ q).left x = q.left (IsLocalRing.closedPoint K) :=
  congrArg (fun y => q.left y) (Subsingleton.elim (α := Spec (.of K)) _ _)

end Slice

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Cof =====
section

/-!
# S4-ThetaCube, file Cof (D-B3, part 1): the slice of `det_k` along a line
* `det_mem_range`: a matrix with entries in `K` has its determinant in `K`;
* **`slice_mem_LFK`** (Laplace along the variable row): the slice lies in `L(D)` when every `h l` does;
* `ptRow` (the point of each row, `q` in the variable rows), `comp_line_zPP`;
* **`ord_slice_pos`**: the slice vanishes at `q` when two rows sit at `q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Cof

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- A matrix over `F` with entries in `K` has its determinant in `K`. -/
theorem det_mem_range {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F)
    (hA : ∀ i j, A i j ∈ Set.range (algebraMap K F)) : A.det ∈ Set.range (algebraMap K F) := by
  have hA' : ∀ i j, ∃ y : K, algebraMap K F y = A i j := hA
  choose B hB using hA'
  refine ⟨(Matrix.of B).det, ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact hB i j

end Cof

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Eff =====
section

/-!
# S4-ThetaCube, file Eff (D-B3, part 2): the residual divisor of a slice of `det_k`
* `ptC`, `Zsl` (the points of the constant rows and their divisor), `ptRow_of_ne`;
* `ord_nonneg_of_mem_LFK`, `deg_finsetSum_single`, `deg_Zsl`;
* **`slice_mem_LFK_sub`**: the slice lies in `L(H - Zsl)`;
* **`slice_eff`**: `G := div f + H - Zsl` is effective of degree `deg H - (N + r - 1)`;
* **`eq_of_ell_one`**: effective, linearly equivalent, `ℓ(G) = 1` ⇒ equal.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Eff

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- Regularity at a place outside the support of `H`. -/
theorem ord_nonneg_of_mem_LFK {H : Places.Divisor K F} {f : F} (hf : f ∈ LFK K F H) {P : Place K F}
    (hP : H P = 0) : 0 ≤ P.ord f := by
  by_cases h0 : f = 0
  · subst h0
    rcases P with P | P
    · show (0 : ℤ) ≤ -WithZero.log (P.valuation F (0 : F))
      simp
    · show (0 : ℤ) ≤ -WithZero.log (P.valuation F (0 : F))
      simp
  · have h1 := Finsupp.le_def.mp ((mem_LFK h0).mp hf) P
    rw [Finsupp.zero_apply, Finsupp.add_apply, PlacesK.div_apply, hP, add_zero] at h1
    exact h1

theorem deg_finsetSum_single {ι : Type*} (s : Finset ι) (t : ι → Place K F) :
    (∑ a ∈ s, Finsupp.single (t a) (1 : ℤ) : Places.Divisor K F).deg = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Places.Divisor.deg]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, PlacesK.Divisor.deg_add, ih, PlacesK.Divisor.deg_single, placeDeg_one,
      Finset.card_insert_of_notMem ha]
    push_cast
    ring

/-- **Uniqueness**: effective, linearly equivalent and `ℓ(G) = 1` ⇒ equal. -/
theorem eq_of_ell_one {G G' : Places.Divisor K F} (hG : 0 ≤ G) (hG' : 0 ≤ G') (hell : ellFK K F G = 1)
    (hcls : clsK K F G = clsK K F G') : G = G' := by
  obtain ⟨φ, hφ0, hφ⟩ := (mem_PrincK K F).mp ((clsK_eq_iff K F).mp hcls)
  have hd1 : (PlacesK.div (1 : F) : Places.Divisor K F) = 0 :=
    (PlacesK.div_eq_zero_iff (K := K) (F := F) one_ne_zero).mpr (one_mem _)
  have h1 : (1 : F) ∈ LFK K F G := by
    rw [mem_LFK one_ne_zero, hd1, zero_add]
    exact hG
  have hφL : φ ∈ LFK K F G := by
    rw [mem_LFK hφ0, hφ, show -G + G' + G = G' by abel]
    exact hG'
  have hfr : Module.finrank K (LFK K F G) = 1 := hell
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨1, h1⟩ : LFK K F G)
    (fun e => one_ne_zero (congrArg Subtype.val e : (1 : F) = 0))).mp hfr ⟨φ, hφL⟩
  have e : c • (1 : F) = φ := congrArg Subtype.val hc
  rw [Algebra.smul_def, mul_one] at e
  have hd : (PlacesK.div φ : Places.Divisor K F) = 0 :=
    (PlacesK.div_eq_zero_iff (K := K) (F := F) hφ0).mpr (e ▸ IntermediateField.algebraMap_mem _ c)
  rw [hd] at hφ
  exact neg_add_eq_zero.mp hφ.symm

end Eff

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Rank =====
section

/-!
# S4-ThetaCube, file Rank (D-B4, part 1): the slices do not vanish
* `ord_sub_cval_pos`: `f - f(q)` vanishes at `q` (the 2 x 2 case of `ord_slice_pos`);
* `ord_pos_sum`: sums of functions vanishing at a place vanish there;
* `comb_mem_LFK`: a `K`-combination of the `h l` whose values vanish at the points lies in `L(H - Σ pts)`;
* **`det_ne_zero_of_ker`**, `det_ne_zero_of_ker0`: the linear algebra (rank-nullity).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section Rank

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- Functions vanishing at `P` are closed under finite sums. -/
theorem ord_pos_sum {ι : Type*} (P : Place K F) (s : Finset ι) (t : ι → F)
    (ht : ∀ l ∈ s, t l = 0 ∨ 0 < P.ord (t l)) : (∑ l ∈ s, t l) = 0 ∨ 0 < P.ord (∑ l ∈ s, t l) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (Finset.sum_empty)
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    by_cases h0 : t a = 0
    · rw [h0, zero_add]
      exact ih fun l hl => ht l (Finset.mem_insert_of_mem hl)
    have hpos := (ht a (Finset.mem_insert_self a s)).resolve_left h0
    by_cases hs0 : ∑ l ∈ s, t l = 0
    · rw [hs0, add_zero]
      exact Or.inr hpos
    have hs := (ih fun l hl => ht l (Finset.mem_insert_of_mem hl)).resolve_left hs0
    by_cases hsum : t a + ∑ l ∈ s, t l = 0
    · exact Or.inl hsum
    exact Or.inr (lt_of_lt_of_le (lt_min hpos hs) (PlacesK.Place.ord_add (K := K) (F := F) (P := P) h0 hs0 hsum))

/-- **Rank lemma**: a variable row `A a0` (independent over `K`) above constant rows `V` whose kernel is at most a line. -/
theorem det_ne_zero_of_ker {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (a0 : ι)
    (V : Matrix {a // a ≠ a0} ι K) (hV : ∀ (a : {a // a ≠ a0}) l, A a l = algebraMap K F (V a l))
    (hh : LinearIndependent K (A a0)) (hker : Module.finrank K (LinearMap.ker V.mulVecLin) ≤ 1) :
    A.det ≠ 0 := by
  intro hd
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  have key : ∀ c : ι → K, x a0 * ∑ l, A a0 l * algebraMap K F (c l) +
      ∑ a : {a // a ≠ a0}, x a * algebraMap K F ((V.mulVec c) a) = 0 := by
    intro c
    have h0 : ∑ l, Matrix.vecMul x A l * algebraMap K F (c l) = 0 := by simp [hx]
    have h1 : ∑ l, Matrix.vecMul x A l * algebraMap K F (c l) =
        ∑ a, x a * ∑ l, A a l * algebraMap K F (c l) := by
      simp only [Matrix.vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    rw [h1, Fintype.sum_eq_add_sum_subtype_ne _ a0] at h0
    refine Eq.trans ?_ h0
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hV]
  have hrn := LinearMap.finrank_range_add_finrank_ker V.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hlt : Fintype.card {a // a ≠ a0} < Fintype.card ι :=
    Fintype.card_subtype_lt (p := fun a => a ≠ a0) (x := a0) (fun h' => h' rfl)
  have hrle : Module.finrank K (LinearMap.range V.mulVecLin) ≤ Fintype.card {a // a ≠ a0} :=
    (Submodule.finrank_le _).trans (by simp)
  obtain ⟨⟨c0, hc0⟩, hc0ne⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0 < Module.finrank K
    (LinearMap.ker V.mulVecLin) by omega)
  have hc0' : V.mulVec c0 = 0 := hc0
  have hc0ne' : c0 ≠ 0 := fun e => hc0ne (Subtype.ext e)
  have htop : LinearMap.range V.mulVecLin = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [Module.finrank_fintype_fun_eq_card]; omega)
  by_cases hxa : x a0 = 0
  · apply hx0
    funext a
    by_cases ha : a = a0
    · rw [ha, hxa]; rfl
    obtain ⟨c, hc⟩ := LinearMap.range_eq_top.mp htop (Pi.single ⟨a, ha⟩ 1)
    have hk := key c
    rw [hxa, zero_mul, zero_add] at hk
    have hc' : V.mulVec c = Pi.single ⟨a, ha⟩ 1 := hc
    rw [hc', Finset.sum_eq_single ⟨a, ha⟩ (fun b _ hb => by rw [Pi.single_eq_of_ne hb, map_zero, mul_zero])
      (fun h' => absurd (Finset.mem_univ _) h'), Pi.single_eq_same, map_one, mul_one] at hk
    exact hk
  · apply hc0ne'
    have hk := key c0
    rw [hc0'] at hk
    simp only [Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, add_zero] at hk
    have hs : ∑ l, c0 l • A a0 l = 0 := by
      rcases mul_eq_zero.mp hk with h' | h'
      · exact absurd h' hxa
      · rw [← h']; exact Finset.sum_congr rfl fun l _ => by rw [Algebra.smul_def, mul_comm]
    funext l
    exact Fintype.linearIndependent_iff.mp hh c0 hs l

/-- An all-constant matrix with trivial kernel. -/
theorem det_ne_zero_of_ker0 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (V : Matrix ι ι K)
    (hV : ∀ a l, A a l = algebraMap K F (V a l)) (hker : ∀ c : ι → K, V.mulVec c = 0 → c = 0) : A.det ≠ 0 := by
  have e : A = (algebraMap K F).mapMatrix V := by ext a l; exact hV a l
  rw [e, ← RingHom.map_det, _root_.map_ne_zero]
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  exact hv0 (hker v hv)

end Rank

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_NZ =====
section

/-!
# S4-ThetaCube, file NZ (D-B4, part 2): the slices are nonzero
* `ellFK_add_div`, `ellFK_of_clsK_eq`: `ℓ` only depends on the divisor class;
* `sliceRow_of_ne`: the constant rows of a slice are the values at `ptC`;
* **`slice_ne_zero`**: the slice with one variable row is nonzero when `ℓ(H - Zsl) ≤ 1`;
* **`slice_ne_zero_const`**: the all-constant slice is nonzero when `ℓ(H - Zall) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
set_option linter.style.haveILetI false

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaCube

open RamanujanPetersson.JacComplete RamanujanPetersson.JacDivisors RamanujanPetersson.ThetaSquare RamanujanPetersson.JacSym
  RamanujanPetersson.IsogDegA RamanujanPetersson.RR
open RamanujanPetersson.Places (Place)
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Opposite TopologicalSpace

universe u

section NZ

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `ℓ(D + div z) = ℓ(D)`. -/
theorem ellFK_add_div {z : F} (hz : z ≠ 0) (D : Places.Divisor K F) :
    ellFK K F (D + PlacesK.div z) = ellFK K F D := by
  have h := (ffDataK K F).ell_add_div hz D
  rwa [ffDataK_div] at h

/-- **`ℓ` is a class invariant.** -/
theorem ellFK_of_clsK_eq {D E : Places.Divisor K F} (h : clsK K F D = clsK K F E) :
    ellFK K F D = ellFK K F E := by
  obtain ⟨φ, hφ0, hφ⟩ := (mem_PrincK K F).mp ((clsK_eq_iff K F).mp h)
  have e : E = D + PlacesK.div φ := by rw [hφ]; abel
  rw [e, ellFK_add_div hφ0]

end NZ

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Good =====
section

/-!
# S4-ThetaCube, file Good (D-B4, part 5): the bad closed sets `B i` of the line test
* `IsSat n i B`: `B` contains the `i`-th line through each of its `K`-points; `isSat_iUnion`, `isSat_empty`;
* `ConstAlong n i φ`: `φ` is constant along the `i`-th lines; `isSat_preimage`, closure under `≫`, `*`, `⁻¹`,
  constants, `psiE`, `epsS := psiE · x0`;
* `ne_univ_of_compl`: finitely many closed sets with nonempty complements do not cover an irreducible space;
* `exists_ne_place`: every place has a different one;
* **`bad P0 n β i x0 cK c2 A`** `= ⋃ badC`: `e_S(p) ∉ Ogood` (all `S`), `p_k = A l` (`k ≠ i`), `p_k = p_k'`
  (`k ≠ k'`, both `≠ i`), in Abel-Jacobi coordinates; **`isClosed_bad`**, **`isSat_bad`**, **`bad_ne_univ`** (when
  `x0 ∈ Ogood`), **`of_not_mem_bad`** (the three conditions at a good `K`-point).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Good

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- `B` contains the `i`-th line through each of its `K`-points. -/
def IsSat (n : ℕ) (i : Fin n) (B : Set (PP K F n).left) : Prop :=
  ∀ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n, p.left (IsLocalRing.closedPoint K) ∈ B →
    Set.range (line K F n i p).left ⊆ B

theorem isSat_iUnion {n : ℕ} {i : Fin n} {I : Type*} (B : I → Set (PP K F n).left) (h : ∀ c, IsSat n i (B c)) :
    IsSat n i (⋃ c, B c) := by
  intro p hp
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hp
  exact (h c p hc).trans (Set.subset_iUnion B c)

theorem isSat_empty (n : ℕ) (i : Fin n) : IsSat n i (∅ : Set (PP K F n).left) := fun _ h => by simp at h

/-- `φ` is constant along the `i`-th lines. -/
def ConstAlong (n : ℕ) (i : Fin n) {Y : Over (Spec (.of K))} (φ : PP K F n ⟶ Y) : Prop :=
  ∀ p : 𝟙_ (Over (Spec (.of K))) ⟶ PP K F n, line K F n i p ≫ φ = toUnit (X1O K F) ≫ p ≫ φ

variable (n : ℕ) (β : Fin n → Fin 3) (i : Fin n) {s : ℕ} (A : Fin s → (𝟙_ (Over (Spec (.of K))) ⟶ X1O K F))

end Good

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Asm1 =====
section

/-!
# S4-ThetaCube, file Asm1 (D-B4, part 6b): the per-`S` line test with its correction, and the cancellation
* `tauS`, `j0S`: the enumeration of the block `{k | β k ∈ S}`;
* `HS`, `YS`, `Vp`, `VS`: the correction divisors; **`cancel_VS`**: their signed cube sum is `0`;
* **`test_S`**: off `bad i0`, both sides avoid and `cpull det_S = cpull Θ_S + VS_S (p_{i0})`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Order Polynomial
  RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectB
  RamanujanPetersson.ThetaSquare
open RamanujanPetersson.Places (Place)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Asm1

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

/-- The enumeration of the block `{k | β k ∈ S}`. -/
noncomputable def tauS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) :
    Fin (Finset.univ.filter (fun k => β k ∈ S)).card → Fin n :=
  fun j => ((Finset.univ.filter (fun k => β k ∈ S)).equivFin.symm j : Fin n)

theorem tauS_inj (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) : Function.Injective (tauS n β S) :=
  fun _ _ h => (Finset.univ.filter (fun k => β k ∈ S)).equivFin.symm.injective (Subtype.ext h)

theorem tauS_mem (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3))
    (j : Fin (Finset.univ.filter (fun k => β k ∈ S)).card) : β (tauS n β S j) ∈ S :=
  (Finset.mem_filter.mp ((Finset.univ.filter (fun k => β k ∈ S)).equivFin.symm j).2).2

theorem tauS_iff (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (k : Fin n) :
    β k ∈ S ↔ ∃ j, tauS n β S j = k := by
  refine ⟨fun hk => ⟨(Finset.univ.filter (fun k => β k ∈ S)).equivFin
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩, by simp [tauS]⟩, ?_⟩
  rintro ⟨j, rfl⟩
  exact tauS_mem n β S j

/-- The index of `i0` in the block. -/
noncomputable def j0S (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n) (hi : β i0 ∈ S) :
    Fin (Finset.univ.filter (fun k => β k ∈ S)).card :=
  (Finset.univ.filter (fun k => β k ∈ S)).equivFin ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

theorem tauS_j0S (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (i0 : Fin n) (hi : β i0 ∈ S) :
    tauS n β S (j0S n β S i0 hi) = i0 := by
  simp [tauS, j0S]

/-- `H_S := (g + r + |block S| - 1) [P0]`. -/
noncomputable def HS (n : ℕ) (β : Fin n → Fin 3) (S : Finset (Fin 3)) (r : ℕ) : Places.Divisor K F :=
  ((genusFK K F : ℤ) + r + (Finset.univ.filter (fun k => β k ∈ S)).card - 1) • Finsupp.single P0 (1 : ℤ)

theorem clsK_zsmul_c (c : ℤ) (D : Places.Divisor K F) : clsK K F (c • D) = c • clsK K F D := by
  exact QuotientAddGroup.mk_zsmul _ _ _

end Asm1

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_ThetaCube_Val =====
section

/-!
# S4-ThetaCube, file Val (D-C1, part 1): values of rational functions at `K`-points
* `RegAt x G`: `G` is regular at `x` (a subring condition); `fpull_add_of`, `fpull_sub_of`, `fpull_sum_of`;
* `regAt_fpull`: regular at `(ℓ ≫ z) (η_C)` ⇒ `fpull z G` regular at `ℓ (η_C)`, `fpull ℓ (fpull z G) = fpull (ℓ ≫ z) G`;
* **`eq_zero_of_kpt`**, **`eq_of_kpt`**: on an integral scheme locally of finite type over an algebraically closed
  `K`, rational functions regular with equal values at the `K`-points of a nonempty open are equal.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory MonoidalCategory Topology RamanujanPetersson.ThetaSquare

universe u

section Reg

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- `G` is regular at `x`. -/
def RegAt (x : Y) (G : Y.functionField) : Prop :=
  G ∈ (algebraMap (Y.presheaf.stalk x) Y.functionField).range

lemma regAt_iff (x : Y) (G : Y.functionField) :
    RegAt x G ↔ ∃ w : Y.presheaf.stalk x, algebraMap _ Y.functionField w = G :=
  RingHom.mem_range

variable {C : Scheme.{u}} [IsIntegral C] (f : C ⟶ Y)

end Reg

section Comp

variable {C P X : Scheme.{u}} [IsIntegral C] [IsIntegral P] [IsIntegral X]

end Comp

section Agree

variable {K : Type u} [Field K] [IsAlgClosed K]

instance isIntegral_unitO : IsIntegral (𝟙_ (Over (Spec (.of K)))).left :=
  inferInstanceAs (IsIntegral (Spec (.of K)))

end Agree

end RamanujanPetersson.ThetaCube


end


