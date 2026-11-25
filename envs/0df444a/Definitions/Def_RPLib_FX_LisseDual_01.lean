-- Prove2me | Definitions.Def_RPLib_FX_LisseDual_01
-- name    : RPLib_FX_LisseDual_01
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:59:59.639017+00:00
-- url     : https://prove2.me/theorems/c4f73356-da70-506c-9f93-3447fffb3a99
-- title:
--   Lisse Poincaré duality on an affine curve over a finite field, library file 01 of 7
-- statement:
--   File 01 of 7 of the lisse duality library for affine curves over a finite field: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_PicDescent_E4`: S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`
--   * `S4.Def_RP_CurveCoh_Shapiro`: S4-CurveCoh, part 4: Shapiro's lemma for a finite etale pushforward (K0c), degrees 0 and 1
--   * `S4.Def_RP_LisseDuality_Amb`: S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group
--   * `S4.Def_RP_LisseDuality_VDat`: S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`
--   * `S4.Def_RP_CupDuality_VS3a`: S4-CurveDuality, O9b (Route G at `V`) part 8: topology and density at `K`, generic form
--   * `S4.Def_RP_CupDuality_VTr1`: S4-CurveDuality, O9b (Route G at `V`) part 1: local data of `V`'s residue data by transfer
--   * `S4.Def_RP_CupDuality_VTr2`: S4-CurveDuality, O9b (Route G at `V`) part 2: `V`'s residue data by transfer
--   * `S4.Def_RP_CupDuality_VCnt1`: S4-CurveDuality, O9b (Route G at `V`) part 3: the `H²` count at `V` (generic)
--   * `S4.Def_RP_LisseDuality_AmbH2`: S4-CurveDuality O7d-P1d (T3): `H²`-vanishing passes to an open subgroup of finite index
--   * `S4.Def_RP_CupDuality_VFrobA`: S4-CurveDuality, O9b (Route G at `V`) part 5: the Frobenius scalar is a unit, generic form
--   * `S4.Def_RP_CupDuality_VFree1`: S4-CurveDuality, O9b (V-free) part 1: a parabolic dual basis mod `lⁿ` from one mod `l` and lifting
--   * `S4.Def_RP_CupDuality_VLift`: S4-CurveDuality, O9b (V-free) part 2: parabolic homomorphisms to `ℤ/l` lift to `ℤ/lⁿ`
--   * `S4.Def_RP_CupDuality_VPar`: S4-CurveDuality, O9b (V-free) part 3: the parabolic block from the right kernel and finiteness mod `l`
--   * `S4.Def_RP_CurveCoh_Lim`: S4-CurveCoh, part 6: functoriality in the coefficients and the `λ`-adic limit
--   * `S4.Def_RP_LisseDuality_Nat`: S4-CurveDuality O7a: naturality of the cup product in the coefficients
--   * `S4.Def_RP_LisseDuality_Exact`: S4-CurveDuality O7b: exactness of `H¹_c` and `H¹` in the coefficients, and the dévissage chase
--   * `S4.Def_RP_LisseDuality_Dev`: S4-CurveDuality O7c: lisse duality by dévissage from coinduced modules
--   * `S4.Def_RP_LisseDuality_Base`: S4-CurveDuality O7c': the dévissage base reduces to the regular coinduced module `coindF Λ`
--   * `S4.Def_RP_LisseDuality_Push`: S4-CurveDuality O7d, steps P0 and P1: from the regular representation to a pushforward
--   * `S4.Def_RP_LisseDuality_Dual`: S4-CurveDuality O7d-P2: the dual of a finite push-forward, and Shapiro on the dual side
--   * `S4.Def_RP_LisseDuality_Proj`: S4-CurveDuality O7d-P3a: the trace of a finite push-forward and the duality pairing
--   * `S4.Def_RP_LisseDuality_Trans`: S4-CurveDuality O7d-P3b T1: local traces are weighted `V`-level residues
--   * `S4.Def_RP_LisseDuality_Lam`: S4-CurveDuality O7d-P3b T2+T3: the transfer weights are one unit
--   * `S4.Def_RP_LisseDuality_AmbCup`: S4-CurveDuality O7d-P1d (T2): the cup product, `ConstData` and the duality maps under a change of ambient group
--   * `S4.Def_RP_LisseDuality_AmbRes`: S4-CurveDuality O7d-P1d (T4): restricting the cover data to a subgroup `H ⊇ Γ, K`
--   * `S4.Def_RP_LisseDuality_AmbAsm`: S4-CurveDuality O7d-P1d (T5): lisse duality without connectedness
--
--   **Formalization note.** One file of a library formalizing Poincaré duality for $H^1$ with lisse (finite, twisted) coefficients on an affine curve over a finite field: for a finite $\Lambda$-module $M$ with a continuous action of the geometric fundamental group factoring through a finite unramified quotient, the cochain duality map $\alpha_M : H^1_c(M) \to H^1(M^\vee(1))^\vee$ is bijective. It extends the published flat library for constant coefficients (`RPLib_F2_*`), which it imports. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); J. S. Milne, Arithmetic Duality Theorems, 2nd ed., BookSurge (2006), Chapter II, §3; P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »

import Mathlib
import Definitions.Def_RPLib_F2_005
import Definitions.Def_RPLib_F2_008
import Definitions.Def_RPLib_F2_010

/-!
# Poincaré duality with lisse coefficients on an affine curve over a finite field, library file 01 of 7

Declarations of the formalization of Poincaré duality for H¹ with lisse (finite, twisted) coefficients on an
affine curve over a finite field (the cochain duality map `alphaM` is bijective), re-hosted declaration by
declaration from the library modules below. Each module contributes the declarations assigned to this file,
copied verbatim with the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_PicDescent_E4`: S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`
* `S4.Def_RP_CurveCoh_Shapiro`: S4-CurveCoh, part 4: Shapiro's lemma for a finite etale pushforward (K0c), degrees 0 and 1
* `S4.Def_RP_LisseDuality_Amb`: S4-CurveDuality O7d-P1d (T1): transport of the cohomology of a pair along a change of ambient group
* `S4.Def_RP_LisseDuality_VDat`: S4-CurveDuality O7d-P4: the cover's constant data from `ResDat`
* `S4.Def_RP_CupDuality_VS3a`: S4-CurveDuality, O9b (Route G at `V`) part 8: topology and density at `K`, generic form
* `S4.Def_RP_CupDuality_VTr1`: S4-CurveDuality, O9b (Route G at `V`) part 1: local data of `V`'s residue data by transfer
* `S4.Def_RP_CupDuality_VTr2`: S4-CurveDuality, O9b (Route G at `V`) part 2: `V`'s residue data by transfer
* `S4.Def_RP_CupDuality_VCnt1`: S4-CurveDuality, O9b (Route G at `V`) part 3: the `H²` count at `V` (generic)
* `S4.Def_RP_LisseDuality_AmbH2`: S4-CurveDuality O7d-P1d (T3): `H²`-vanishing passes to an open subgroup of finite index
* `S4.Def_RP_CupDuality_VFrobA`: S4-CurveDuality, O9b (Route G at `V`) part 5: the Frobenius scalar is a unit, generic form
* `S4.Def_RP_CupDuality_VFree1`: S4-CurveDuality, O9b (V-free) part 1: a parabolic dual basis mod `lⁿ` from one mod `l` and lifting
* `S4.Def_RP_CupDuality_VLift`: S4-CurveDuality, O9b (V-free) part 2: parabolic homomorphisms to `ℤ/l` lift to `ℤ/lⁿ`
* `S4.Def_RP_CupDuality_VPar`: S4-CurveDuality, O9b (V-free) part 3: the parabolic block from the right kernel and finiteness mod `l`
* `S4.Def_RP_CurveCoh_Lim`: S4-CurveCoh, part 6: functoriality in the coefficients and the `λ`-adic limit
* `S4.Def_RP_LisseDuality_Nat`: S4-CurveDuality O7a: naturality of the cup product in the coefficients
* `S4.Def_RP_LisseDuality_Exact`: S4-CurveDuality O7b: exactness of `H¹_c` and `H¹` in the coefficients, and the dévissage chase
* `S4.Def_RP_LisseDuality_Dev`: S4-CurveDuality O7c: lisse duality by dévissage from coinduced modules
* `S4.Def_RP_LisseDuality_Base`: S4-CurveDuality O7c': the dévissage base reduces to the regular coinduced module `coindF Λ`
* `S4.Def_RP_LisseDuality_Push`: S4-CurveDuality O7d, steps P0 and P1: from the regular representation to a pushforward
* `S4.Def_RP_LisseDuality_Dual`: S4-CurveDuality O7d-P2: the dual of a finite push-forward, and Shapiro on the dual side
* `S4.Def_RP_LisseDuality_Proj`: S4-CurveDuality O7d-P3a: the trace of a finite push-forward and the duality pairing
* `S4.Def_RP_LisseDuality_Trans`: S4-CurveDuality O7d-P3b T1: local traces are weighted `V`-level residues
* `S4.Def_RP_LisseDuality_Lam`: S4-CurveDuality O7d-P3b T2+T3: the transfer weights are one unit
* `S4.Def_RP_LisseDuality_AmbCup`: S4-CurveDuality O7d-P1d (T2): the cup product, `ConstData` and the duality maps under a change of ambient group
* `S4.Def_RP_LisseDuality_AmbRes`: S4-CurveDuality O7d-P1d (T4): restricting the cover data to a subgroup `H ⊇ Γ, K`
* `S4.Def_RP_LisseDuality_AmbAsm`: S4-CurveDuality O7d-P1d (T5): lisse duality without connectedness
-/

set_option autoImplicit false

-- ===== S4.Def_RP_PicDescent_E4 =====
section

/-!
# S4-PicDescent, part E4 (review R6): function fields whose full constant field is `F_(q^d)`

For a function field `F / Fq` with full constant field `K = constField Fq F` (`#K = q ^ d`, `d = [K : Fq]`,
`card_constField`), `F` is rebased as a function field over `K` with the same separating element `x`:
* instances `Algebra K[X] F` (`x ↦ xF Fq F`), `Algebra (RatFunc K) F`, the towers, `FunctionField K F`,
  `Algebra.IsSeparable (RatFunc K) F`; `xF_constField : xF K F = xF Fq F`;
* `constField_K : constField K F = ⊥` (`F / K` is geometrically connected),
  `exists_deg_one_K` (F. K. Schmidt over `K`), `finite_Pic0_K`;
so parts A–E apply over `K` with `q ^ d` in place of `q`; the `K`-Frobenius is `π ^ d` (`mem_Lc_K`).
Restated over `K`: `picBarEquivK`, `pic0BarEquivK`, `picBaseEquivK`, `pic0BaseEquivK`, `classNumber_barK`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial
open IsDedekindDomain Polynomial

namespace RamanujanPetersson.PicDescent

open Places ZetaSB

section Rebase

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

noncomputable instance fintype_constField : Fintype (constField Fq F) :=
  @Fintype.ofFinite _ (Module.finite_of_finite Fq)

section Descent

-- `Algebra K Ω` and `IsScalarTower K F Ω` are Mathlib's intermediate-field instances (through `F`).
variable {Ω : Type*} [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]

end Descent

end Rebase

end RamanujanPetersson.PicDescent


end

-- ===== S4.Def_RP_CurveCoh_Shapiro =====
section

/-!
# S4-CurveCoh, part 4: Shapiro's lemma for a finite etale pushforward (K0c), degrees 0 and 1

A finite etale cover `f : U → V` corresponds to an open subgroup `H = π₁(U)` of finite index in `G = π₁(V)`.
For a representation `σ` of `H` on `M` (a lisse sheaf on `U`), `f_* M` is the coinduced representation
`pushRep Γ H σ` of `G` on `coindV H.subtype σ`: `H`-equivariant functions `F : G → M`, `(g • F) x = F (x * g)`.
The geometric fundamental group of `U` is `Γ ∩ H` (`geoU Γ H`), and `U` is geometrically connected over the
constant field of `V` exactly when `G = H Γ` (hypothesis `hcov`).

Results (over any commutative ring `k`):
* `shapiroH0Equiv : H⁰(Γ, f_* M) ≃ₗ H⁰(Γ ∩ H, M)` (`F ↦ F 1`);
* `shapiroH1 : H¹(Γ, f_* M) →ₗ H¹(Γ ∩ H, M)` (restrict to `Γ ∩ H`, evaluate at `1`): injective (`hcov`), surjective
  (`hcov`, `H` open, representatives of `(Γ ∩ H) \ Γ`, which exist for finite index: `exists_cosetReps`), hence
  `shapiroH1Equiv`;
* `shapiroH1_frobH1`: Shapiro commutes with the operators `T_ψ`, `ψ ∈ H`; in particular with the GEOMETRIC Frobenius
  `F = T_{φ⁻¹}` for a Frobenius lift `φ ∈ π₁(U)` (which is also one for `V`), so purity is preserved.
Part 5 (`Def_RP_CurveCoh_ShapiroCone`) treats the cone `H¹_c`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

open Representation

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module k M] (Γ H : Subgroup G) (σ : Representation k H M)

/-! ## Extension from `Γ` to `G = H Γ` -/

section Ext

variable (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)

end Ext

/-! ## Degree 0 -/

theorem H0_coind_apply {F : coindV H.subtype σ} (hF : F ∈ H0 (pushRep H σ) Γ) (y : Γ) :
    (F : G → M) y = (F : G → M) 1 := by
  have h1 : (F : G → M) (1 * (y : G)) = (F : G → M) 1 :=
    congrArg (fun F' : coindV H.subtype σ => (F' : G → M) 1) ((mem_H0 _ _ F).mp hF y)
  rwa [one_mul] at h1

/-- Shapiro in degree 0: `F ↦ F 1`. -/
def shapiroH0 : H0 (pushRep H σ) Γ →ₗ[k] H0 σ (geoU Γ H) where
  toFun F := ⟨((F : coindV H.subtype σ) : G → M) 1, (mem_H0 _ _ _).mpr fun h => by
    rw [← coind_apply_of_mem]; exact H0_coind_apply Γ H σ F.2 (geoToΓ Γ H h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shapiroH0_injective (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ) :
    Function.Injective (shapiroH0 Γ H σ) := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  have h0 : ((F : coindV H.subtype σ) : G → M) 1 = 0 := congrArg Subtype.val hF
  refine Subtype.ext (coind_ext_Γ Γ H σ hcov fun y => ?_)
  rw [H0_coind_apply Γ H σ F.2 y, h0]; rfl

theorem shapiroH0_surjective (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ) :
    Function.Surjective (shapiroH0 Γ H σ) := by
  intro m
  have hφ : EquivOnΓ Γ H σ (fun _ => (m : M)) := by
    intro h y y' hy
    have hhΓ : (h : G) ∈ Γ := by
      have : (h : G) = y' * (y : G)⁻¹ := by rw [hy]; group
      rw [this]; exact Γ.mul_mem y'.2 (Γ.inv_mem y.2)
    exact ((mem_H0 _ _ _).mp m.2 ⟨h, Subgroup.mem_subgroupOf.mpr hhΓ⟩).symm
  refine ⟨⟨coindOf Γ H σ hcov _ hφ, (mem_H0 _ _ _).mpr fun g => coind_ext_Γ Γ H σ hcov fun y => ?_⟩, ?_⟩
  · show ((coindOf Γ H σ hcov _ hφ : coindV H.subtype σ) : G → M) ((y : G) * g) =
      ((coindOf Γ H σ hcov _ hφ : coindV H.subtype σ) : G → M) y
    rw [show (y : G) * g = ((y * g : Γ) : G) from rfl]
    simp only [coindOf_apply]
  · exact Subtype.ext (coindExt_apply Γ H σ hcov _ hφ 1)

/-- **Shapiro, degree 0** (`U` geometrically connected): `H⁰(Γ, f_* M) ≃ H⁰(Γ ∩ H, M)`. -/
def shapiroH0Equiv (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ) :
    H0 (pushRep H σ) Γ ≃ₗ[k] H0 σ (geoU Γ H) :=
  LinearEquiv.ofBijective _ ⟨shapiroH0_injective Γ H σ hcov, shapiroH0_surjective Γ H σ hcov⟩

/-! ## Degree 1: the map -/

theorem resEv_mem_B1 {c : Γ → coindV H.subtype σ} (hc : c ∈ B1 (pushRep H σ) Γ) :
    resEv Γ H σ c ∈ B1 σ (geoU Γ H) := by
  obtain ⟨hz, F, hF⟩ := (mem_B1 _ _ c).mp hc
  refine (mem_B1 _ _ _).mpr ⟨resEv_mem_Z1 Γ H σ hz, (F : G → M) 1, fun h => ?_⟩
  rw [resEv_apply, hF]
  change (F : G → M) (1 * ((h : H) : G)) - (F : G → M) 1 = σ h ((F : G → M) 1) - (F : G → M) 1
  rw [one_mul, coind_apply_of_mem]

/-- Shapiro on cocycles. -/
def shapiroZ1 : Z1 (pushRep H σ) Γ →ₗ[k] Z1 σ (geoU Γ H) :=
  (resEv Γ H σ).restrict fun _ hc => resEv_mem_Z1 Γ H σ hc

/-- **Shapiro, degree 1**: `H¹(Γ, f_* M) → H¹(Γ ∩ H, M)`. -/
def shapiroH1 : H1 (pushRep H σ) Γ →ₗ[k] H1 σ (geoU Γ H) :=
  Submodule.mapQ _ _ (shapiroZ1 Γ H σ) fun _ hc => resEv_mem_B1 Γ H σ hc

theorem shapiroH1_mk (c : Z1 (pushRep H σ) Γ) :
    shapiroH1 Γ H σ (H1.mk (pushRep H σ) Γ c) = H1.mk σ (geoU Γ H) (shapiroZ1 Γ H σ c) := rfl

/-! ## Degree 1: surjectivity (the Shapiro lift) -/

variable {Γ H} (R : CosetReps Γ H)

variable (hcov : ∀ x : G, ∃ h : H, ∃ γ : Γ, x = (h : G) * γ)

variable (Γ H)

end

end CurveCoh
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

/-- `e` restricted to `Δ ⊓ I s`. -/
def infTr (hI : IntwI I₁ I₂ e) (s : S) : ↥(Δ₁ ⊓ I₁ s) ≃ₜ* ↥(Δ₂ ⊓ I₂ s) where
  toFun g := ⟨e ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩,
    Subgroup.mem_inf.2 ⟨(e _).2, (hI s _).1 (Subgroup.mem_inf.1 g.2).2⟩⟩
  invFun g := ⟨e.symm ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩,
    Subgroup.mem_inf.2 ⟨(e.symm _).2, (hI.symm s _).1 (Subgroup.mem_inf.1 g.2).2⟩⟩
  left_inv g := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (show ((e ⟨(a : G₁) * b, (Subgroup.mem_inf.1 (a * b).2).1⟩ : Δ₂) : G₂) =
      (e ⟨a, (Subgroup.mem_inf.1 a.2).1⟩ : G₂) * (e ⟨b, (Subgroup.mem_inf.1 b.2).1⟩ : G₂) from
    congrArg Subtype.val
      (map_mul e ⟨(a : G₁), (Subgroup.mem_inf.1 a.2).1⟩ ⟨(b : G₁), (Subgroup.mem_inf.1 b.2).1⟩))
  continuous_toFun :=
    (continuous_subtype_val.comp ((map_continuous e).comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp ((map_continuous e.symm).comp (continuous_subtype_val.subtype_mk _))).subtype_mk _

theorem infTr_coe (hI : IntwI I₁ I₂ e) (s : S) (g : ↥(Δ₁ ⊓ I₁ s)) :
    ((infTr hI s g : ↥(Δ₂ ⊓ I₂ s)) : G₂) = (e ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ : G₂) := rfl

theorem infTr_symm_coe (hI : IntwI I₁ I₂ e) (s : S) (g : ↥(Δ₂ ⊓ I₂ s)) :
    (((infTr hI s).symm g : ↥(Δ₁ ⊓ I₁ s)) : G₁) = (e.symm ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ : G₁) := rfl

theorem Intw.inf (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) (s : S) : Intw ρ₁ ρ₂ (infTr hI s) :=
  fun g => h ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩

/-- The `Π_s Z¹(Δ ⊓ I s)` transport. -/
def piTr (h : Intw ρ₁ ρ₂ e) (hI : IntwI I₁ I₂ e) :
    ((s : S) → Z1 ρ₁ (Δ₁ ⊓ I₁ s)) ≃ₗ[k] ((s : S) → Z1 ρ₂ (Δ₂ ⊓ I₂ s)) :=
  LinearEquiv.piCongrRight fun s => z1Tr (h.inf hI s)

variable [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

end Tr

end

end CupDuality
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

/-- A cocycle for an action that is trivial on `Δ` is additive. -/
theorem z1_add_of_triv {H : Type} [Group H] [TopologicalSpace H] (ρ : Representation Λ H Λ) (Δ : Subgroup H)
    (htr : ∀ (g : Δ) (x : Λ), ρ g x = x) (e : Z1 ρ Δ) (a b : Δ) :
    (e : Δ → Λ) (a * b) = (e : Δ → Λ) a + (e : Δ → Λ) b := by
  rw [((mem_Z1 _ _ _).1 e.2).2 a b, htr]

theorem isOpen_ker_comp {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ G M)
    (hρ : IsOpen (ρ.ker : Set G)) : IsOpen ((ρ.comp K.subtype).ker : Set K) := by
  have e : ((ρ.comp K.subtype).ker : Set K) = Subtype.val ⁻¹' (ρ.ker : Set G) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply,
      Subgroup.coe_subtype]
  rw [e]
  exact hρ.preimage continuous_subtype_val

end Gen

section RD

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Gf : Type} [Group Gf] {π : G →* Gf} {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T : Type} [Fintype T] [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)] (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1)

/-! ### Conjugation `J_s ≃ geoU Γ K ⊓ rdJ t` -/

/-! ### `Γ_H ≃ geoU Γ K` -/

/-! ### The constant data of `V` -/

variable (σ : Representation Λ G Λ) (htriv : ∀ (g : Γ) (x : Λ), σ g x = x)

variable [NeZero N] (hN : (N : Λ) = 0)

include hN in
theorem rd_hM : ∀ m : Λ, N • m = 0 := fun m => by
  rw [← Nat.cast_smul_eq_nsmul Λ, hN, zero_smul]

end RD

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VS3a =====
section

/-!
# S4-CurveDuality, O9b (Route G at `V`) part 8: topology and density at `K`, generic form

For an open subgroup `K` of a compact group `G`:
* `compactSpace_of_isOpen`: `K` is compact;
* `hbasis_subgroup`: if open normal subgroups form a basis at `1` in `G`, they do in `K` (`N ↦ N ∩ K`);
* **`exists_dens_sub`**: if `G = φ^ℕ · Γ · N` for every open `N` (`Γ` normal) and `K = ker π` with `π` onto a finite
  group, then `K = φ_V^ℕ · (Γ ∩ K) · N` for every open `N ≤ K`, where `φ_V = γ₀⁻¹ φ^f ∈ K`, `f` the least `f > 0`
  with `π(φ)^f ∈ π(Γ)` (`π(φ)^j ∈ π(Γ) → f ∣ j`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem compactSpace_of_isOpen [CompactSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) : CompactSpace K :=
  isCompact_iff_compactSpace.mp (K.isClosed_of_isOpen hK).isCompact

/-- Open normal subgroups form a basis at `1` in a subgroup when they do in `G`. -/
theorem hbasis_subgroup (hb : ∀ U : Set G, IsOpen U → (1 : G) ∈ U →
      ∃ N : Subgroup G, N.Normal ∧ IsOpen (N : Set G) ∧ (N : Set G) ⊆ U) (K : Subgroup G) :
    ∀ U : Set K, IsOpen U → (1 : K) ∈ U → ∃ N : Subgroup K, N.Normal ∧ IsOpen (N : Set K) ∧ (N : Set K) ⊆ U := by
  intro U hU h1
  obtain ⟨U', hU', hUU'⟩ := isOpen_induced_iff.mp hU
  have h1' : (1 : G) ∈ U' := by
    have : (1 : K) ∈ Subtype.val ⁻¹' U' := by
      rw [hUU']
      exact h1
    exact this
  obtain ⟨N, hNn, hNo, hNU⟩ := hb U' hU' h1'
  refine ⟨N.subgroupOf K, by have := hNn; infer_instance, hNo.preimage continuous_subtype_val, fun x hx => ?_⟩
  have : x ∈ Subtype.val ⁻¹' U' := hNU (Subgroup.mem_subgroupOf.1 hx)
  rwa [hUU'] at this

/-- Least exponent: `π(φ)^j ∈ P → f ∣ j` for the least `f > 0` with `π(φ)^f ∈ P`. -/
theorem exists_least_pow {H : Type} [Group H] [Finite H] (x : H) (P : Subgroup H) :
    ∃ f : ℕ, 0 < f ∧ x ^ f ∈ P ∧ ∀ j, x ^ j ∈ P → f ∣ j := by
  classical
  have hex : ∃ j, 0 < j ∧ x ^ j ∈ P :=
    ⟨orderOf x, orderOf_pos x, by rw [pow_orderOf_eq_one]; exact P.one_mem⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun j hj => ?_⟩
  set f := Nat.find hex with hf_def
  have hf := Nat.find_spec hex
  have e : x ^ j = (x ^ f) ^ (j / f) * x ^ (j % f) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have hm : x ^ (j % f) ∈ P := by
    have e2 : x ^ (j % f) = ((x ^ f) ^ (j / f))⁻¹ * x ^ j := by rw [e, inv_mul_cancel_left]
    rw [e2]
    exact P.mul_mem (P.inv_mem (P.pow_mem hf.2 _)) hj
  by_contra hnd
  have hpos : 0 < j % f := Nat.pos_of_ne_zero fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  exact Nat.find_min hex (Nat.mod_lt j hf.1) ⟨hpos, hm⟩

end

end RamanujanPetersson.CupDuality


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

end LocConj

section Tr

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Gf Gf2 : Type} [Group Gf] [Group Gf2] {π : G →* Gf} {π2 : G →* Gf2} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T T2 : Type} [Fintype T] [Fintype T2] [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)] (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hK2 : ∀ g, π2 g = 1 → g ∈ K)

variable (π2) in
/-- `π_V = π₂|_K`. -/
def piV : K →* Gf2 := π2.comp K.subtype

theorem piV_apply (g : K) : piV π2 K g = π2 g := rfl

include hK hK2 in
theorem conj_mem_K (x : G) {j : G} (hj : π2 j = 1) : x * j * x⁻¹ ∈ K := by
  rw [hK, map_mul, map_mul, map_inv, (hK _).1 (hK2 _ hj), mul_one, mul_inv_cancel]

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

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Gf Gf2 : Type} [Group Gf] [Group Gf2] {π : G →* Gf} {π2 : G →* Gf2} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T T2 : Type} [Fintype T] [Fintype T2] [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)] (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hK2 : ∀ g, π2 g = 1 → g ∈ K)

include hK hK2 in
theorem pi_eq_of_pi2 (a b : G) (h : π2 a = π2 b) : π a = π b := by
  have h1 : π (a⁻¹ * b) = 1 := (hK _).1 (hK2 _ (by rw [map_mul, map_inv, h, inv_mul_cancel]))
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

/-! ### `Γ_H(V) ≅ D2.ΓH` and the residue conditions -/

theorem trNsmul (m : ZMod N) : N • m = 0 := by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

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

variable {Gf Gf' : Type} [Group Gf] [Group Gf'] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {π : G →* Gf} {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T : Type} [Fintype T] (π' : G →* Gf') (j : Gf' →* Gf) (hj : Function.Injective j) (hjπ : ∀ g, j (π' g) = π g)

include hj hjπ in
theorem ker_iff_inj (g : G) : π' g = 1 ↔ π g = 1 :=
  ⟨fun h => by rw [← hjπ, h, map_one], fun h => hj (by rw [hjπ, h, map_one])⟩

include hj hjπ in
theorem mem_map_iff_inj (H : Subgroup G) (a : Gf') : a ∈ H.map π' ↔ j a ∈ H.map π := by
  constructor
  · intro h
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 h
    exact Subgroup.mem_map.2 ⟨g, hg, (hjπ g).symm⟩
  · intro h
    obtain ⟨g, hg, he⟩ := Subgroup.mem_map.1 h
    exact Subgroup.mem_map.2 ⟨g, hg, hj (by rw [hjπ, he])⟩

end OfInj

section Factor

/-- A representation trivial on `ker f` (`f` surjective) factors through `f`. -/
theorem exists_factor_rep {H Q : Type} [Group H] [Group Q] {Λ M : Type} [CommRing Λ] [AddCommGroup M]
    [Module Λ M] (f : H →* Q) (hf : Function.Surjective f) (ρ : Representation Λ H M) (hle : f.ker ≤ ρ.ker) :
    ∃ τ : Representation Λ Q M, τ.comp f = ρ := by
  refine ⟨(QuotientGroup.lift f.ker ρ hle).comp
    (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom, MonoidHom.ext fun g => ?_⟩
  have e : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f g) = (g : H ⧸ f.ker) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  show QuotientGroup.lift f.ker ρ hle ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f g)) = ρ g
  rw [e]
  rfl

end Factor

section Cnt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Gf Gf2 : Type} [Group Gf] [Group Gf2] {π : G →* Gf} {π2 : G →* Gf2} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [DecidableEq S] {I : S → Subgroup G} {N : ℕ} {T T2 : Type} [Fintype T] [Fintype T2] [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)] (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hK2 : ∀ g, π2 g = 1 → g ∈ K)

variable (π2) in
/-- `π_V` onto its image. -/
abbrev piR : K →* (piV π2 K).range := (piV π2 K).rangeRestrict

theorem piR_eq_one_iff (g : K) : piR π2 K g = 1 ↔ π2 (g : G) = 1 := by
  rw [Subtype.ext_iff]
  exact Iff.rfl

theorem piR_ker_open (hπ2 : IsOpen (π2.ker : Set G)) : IsOpen ((piR π2 K).ker : Set K) := by
  have e : ((piR π2 K).ker : Set K) = Subtype.val ⁻¹' (π2.ker : Set G) := by
    ext g
    exact piR_eq_one_iff K g
  rw [e]
  exact hπ2.preimage continuous_subtype_val

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

theorem coindSub_mul (F : Representation.coindV H.subtype ρ) (h : H) (y : G) :
    (F : G → W) ((h : G) * y) = ρ h ((F : G → W) y) := F.2 h y

/-- `ι w = (x ↦ x · w on H, 0 off H)`. -/
def coindSubIota : W →ₗ[Λ] Representation.coindV H.subtype ρ where
  toFun w := ⟨fun x => if hx : x ∈ H then ρ ⟨x, hx⟩ w else 0, fun h x => by
    by_cases hx : x ∈ H
    · have hhx : H.subtype h * x ∈ H := H.mul_mem h.2 hx
      simp only [dif_pos hx, dif_pos hhx]
      rw [show (⟨H.subtype h * x, hhx⟩ : H) = h * ⟨x, hx⟩ from rfl, map_mul, Module.End.mul_apply]
    · have hhx : H.subtype h * x ∉ H := fun hm => hx ((H.mul_mem_cancel_left h.2).1 hm)
      simp only [dif_neg hx, dif_neg hhx, map_zero]⟩
  map_add' w w' := Subtype.ext (funext fun x => by
    by_cases hx : x ∈ H <;> simp [hx])
  map_smul' a w := Subtype.ext (funext fun x => by
    by_cases hx : x ∈ H <;> simp [hx])

theorem coindSubIota_equiv (h : H) (w : W) :
    coindSubIota H ρ (ρ h w) = Representation.coind H.subtype ρ (h : G) (coindSubIota H ρ w) :=
  Subtype.ext (funext fun x => by
    show (if hx : x ∈ H then ρ ⟨x, hx⟩ (ρ h w) else 0) = (if hx : x * h ∈ H then ρ ⟨x * h, hx⟩ w else 0)
    by_cases hx : x ∈ H
    · have hxh : x * (h : G) ∈ H := H.mul_mem hx h.2
      rw [dif_pos hx, dif_pos hxh, show (⟨x * h, hxh⟩ : H) = ⟨x, hx⟩ * h from rfl, map_mul,
        Module.End.mul_apply]
    · have hxh : x * (h : G) ∉ H := fun hm => hx ((H.mul_mem_cancel_right h.2).1 hm)
      rw [dif_neg hx, dif_neg hxh])

/-- Evaluation at `1`. -/
def coindSubEv : Representation.coindV H.subtype ρ →ₗ[Λ] W where
  toFun F := (F : G → W) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coindSubEv_equiv (h : H) (F : Representation.coindV H.subtype ρ) :
    coindSubEv H ρ (Representation.coind H.subtype ρ (h : G) F) = ρ h (coindSubEv H ρ F) := by
  show (F : G → W) (1 * h) = ρ h ((F : G → W) 1)
  rw [← coindSub_mul, one_mul, mul_one]

theorem coindSubEv_iota (w : W) : coindSubEv H ρ (coindSubIota H ρ w) = w := by
  show (if hx : (1 : G) ∈ H then ρ ⟨1, hx⟩ w else 0) = w
  rw [dif_pos H.one_mem]
  show ρ 1 w = w
  rw [map_one, Module.End.one_apply]

theorem coindSub_finite [Finite (G ⧸ H)] [Finite W] : Finite (Representation.coindV H.subtype ρ) :=
  Finite.of_injective (fun F : Representation.coindV H.subtype ρ => fun q : G ⧸ H => (F : G → W) (q.out)⁻¹)
    fun F F' hFF => Subtype.ext (funext fun y => by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H y⁻¹
      have hy : y = (h : G) * ((QuotientGroup.mk y⁻¹ : G ⧸ H).out)⁻¹ := by
        rw [hh, mul_inv_rev, inv_inv, mul_inv_cancel_left]
      rw [hy, coindSub_mul, coindSub_mul]
      exact congrArg (ρ h) (congrFun hFF (QuotientGroup.mk y⁻¹)))

theorem isOpen_coindSub_ker (hHo : IsOpen (H : Set G)) [Finite (G ⧸ H)] (hρ : IsOpen (ρ.ker : Set H)) :
    IsOpen ((Representation.coind H.subtype ρ).ker : Set G) := by
  have hNo : IsOpen (Subtype.val '' (ρ.ker : Set H) : Set G) := hHo.isOpenMap_subtype_val _ hρ
  have hUo : IsOpen (⋂ q : G ⧸ H, (fun g => (q.out)⁻¹ * g * q.out) ⁻¹' (Subtype.val '' (ρ.ker : Set H))) :=
    isOpen_iInter_of_finite fun q => hNo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hU1 : (1 : G) ∈ ⋂ q : G ⧸ H, (fun g => (q.out)⁻¹ * g * q.out) ⁻¹' (Subtype.val '' (ρ.ker : Set H)) :=
    Set.mem_iInter.2 fun q => Set.mem_preimage.2 ((Set.mem_image _ _ _).2 ⟨1, ρ.ker.one_mem, by simp⟩)
  refine Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hUo.mem_nhds hU1) fun g hg => ?_)
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  refine LinearMap.ext fun F => Subtype.ext (funext fun x => ?_)
  show (F : G → W) (x * g) = (F : G → W) x
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H x⁻¹
  obtain ⟨n, hn, hng⟩ :=
    (Set.mem_image _ _ _).1 (Set.mem_preimage.1 (Set.mem_iInter.1 hg (QuotientGroup.mk x⁻¹)))
  rw [hh] at hng
  have e1 : x * g = ((h * n : H) : G) * (x⁻¹ * (h : G))⁻¹ := by
    rw [Subgroup.coe_mul, hng]
    group
  have e2 : x = (h : G) * (x⁻¹ * (h : G))⁻¹ := by group
  rw [e1, coindSub_mul, map_mul, Module.End.mul_apply, MonoidHom.mem_ker.1 hn, Module.End.one_apply,
    ← coindSub_mul, ← e2]

end Retract

section H2

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Subgroup G} {Δ : Subgroup G}

/-- `Δ → Δ.subgroupOf H` for `Δ ≤ H`. -/
def toSubOf (hΔ : Δ ≤ H) (a : Δ) : Δ.subgroupOf H := ⟨⟨a.1, hΔ a.2⟩, a.2⟩

/-- `Δ.subgroupOf H → Δ`. -/
def ofSubOf (a : Δ.subgroupOf H) : Δ := ⟨a.1.1, a.2⟩

theorem continuous_toSubOf (hΔ : Δ ≤ H) : Continuous (toSubOf hΔ) :=
  Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val (fun a => hΔ a.2)) (fun a => a.2)

theorem continuous_ofSubOf : Continuous (ofSubOf (H := H) (Δ := Δ)) :=
  Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun a => a.2)

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

/-- A linear endomorphism of a module isomorphic to `k` is a scalar. -/
theorem endo_eq_smul {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A] (E : A ≃ₗ[k] k)
    (F : A →ₗ[k] A) (z : A) : F z = E (F (E.symm 1)) • z := by
  apply E.injective
  have hz : E z • E.symm 1 = z := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  calc E (F z) = E (F (E z • E.symm 1)) := by rw [hz]
    _ = E (E (F (E.symm 1)) • z) := by
      simp only [map_smul, smul_eq_mul]
      ring

/-- The scalar of an onto endomorphism of a module isomorphic to `k` is a unit. -/
theorem isUnit_of_surjective {k : Type} [CommRing k] {A : Type} [AddCommGroup A] [Module k A] (E : A ≃ₗ[k] k)
    (F : A →ₗ[k] A) (hF : Function.Surjective F) : IsUnit (E (F (E.symm 1))) := by
  obtain ⟨z, hz⟩ := hF (E.symm 1)
  have h := endo_eq_smul E F z
  rw [hz] at h
  have h2 := congrArg E h
  rw [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul] at h2
  exact IsUnit.of_mul_eq_one (E z) h2.symm

section H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M)

variable (Γ : Subgroup G) [hΓ : Γ.Normal] {S : Type} (I : S → Subgroup G) (ψ : G) (τ : S → S) (h : S → Γ)

variable (hρ : IsOpen (ρ.ker : Set G))

end H

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {σ : Representation k G k} {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [Nonempty S]
  {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_VFree1 =====
section

/-!
# S4-CurveDuality, O9b (V-free) part 1: a parabolic dual basis mod `lⁿ` from one mod `l` and lifting

`Γ` a topological group, `P` a predicate ("inertia"). If the `ℤ/l`-valued parabolic homomorphisms have a dual basis
`b_i`, `e_j` (`b_i(e_j) = δ_ij`, spanning) and every `b_i` lifts to a `ℤ/lⁿ`-valued parabolic homomorphism, then the
`ℤ/lⁿ`-valued ones have a dual basis `χ_i` with the same `e_j` (**`exists_parBasis_of_lift`**): evaluation at the `e_j`
is injective mod `lⁿ` (`eval_inj`, `l`-adic descent) and onto (`exists_eval`, Nakayama).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

section VFree

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {P : Γ → Prop}

theorem isParHom_zeroV {A : Type*} [AddCommGroup A] : IsParHom P (fun _ : Γ => (0 : A)) :=
  ⟨IsLocallyConstant.const 0, fun _ _ => (add_zero 0).symm, fun _ _ => rfl⟩

theorem IsParHom.addV {A : Type*} [AddCommGroup A] {x y : Γ → A} (hx : IsParHom P x) (hy : IsParHom P y) :
    IsParHom P (fun g => x g + y g) :=
  ⟨hx.1.comp₂ hy.1 (· + ·), fun a b => by
    show x (a * b) + y (a * b) = (x a + y a) + (x b + y b)
    rw [hx.2.1, hy.2.1]; abel,
   fun g hg => by show x g + y g = 0; rw [hx.2.2 g hg, hy.2.2 g hg, add_zero]⟩

theorem IsParHom.subV {A : Type*} [AddCommGroup A] {x y : Γ → A} (hx : IsParHom P x) (hy : IsParHom P y) :
    IsParHom P (fun g => x g - y g) :=
  ⟨hx.1.comp₂ hy.1 (· - ·), fun a b => by
    show x (a * b) - y (a * b) = (x a - y a) + (x b - y b)
    rw [hx.2.1, hy.2.1]; abel,
   fun g hg => by show x g - y g = 0; rw [hx.2.2 g hg, hy.2.2 g hg, sub_zero]⟩

theorem IsParHom.cmulV {R : Type*} [CommRing R] (c : R) {x : Γ → R} (hx : IsParHom P x) :
    IsParHom P (fun g => c * x g) :=
  ⟨hx.1.comp (fun a => c * a), fun a b => by
    show c * x (a * b) = c * x a + c * x b
    rw [hx.2.1, mul_add],
   fun g hg => by show c * x g = 0; rw [hx.2.2 g hg, mul_zero]⟩

theorem IsParHom.sumV {A : Type*} [AddCommGroup A] {ι : Type*} (s : Finset ι) {f : ι → Γ → A}
    (hf : ∀ i, IsParHom P (f i)) : IsParHom P (fun g => ∑ i ∈ s, f i g) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact isParHom_zeroV
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    exact (hf a).addV ih

/-- Reduction `ℤ/lⁿ → ℤ/l`. -/
def redL (l : ℕ) {n : ℕ} (hn : n ≠ 0) : ZMod (l ^ n) →+* ZMod l := ZMod.castHom (dvd_pow_self l hn) (ZMod l)

variable {l n : ℕ} [Fact l.Prime]

theorem redL_eq_zero_of_mul (hn : n ≠ 0) {m : ℕ} (hmn : m < n) {x : ZMod (l ^ n)}
    (h : (l : ZMod (l ^ n)) ^ m * x = 0) : redL l hn x = 0 := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  show (ZMod.cast x : ZMod l) = 0
  rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  have h2 : ((l ^ m * x.val : ℕ) : ZMod (l ^ n)) = 0 := by
    rw [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val, h]
  rw [ZMod.natCast_eq_zero_iff] at h2
  have h3 : l ^ m * l ^ (n - m) ∣ l ^ m * x.val := by
    rw [← pow_add, Nat.add_sub_cancel' hmn.le]; exact h2
  exact (dvd_pow_self l (by omega)).trans (Nat.dvd_of_mul_dvd_mul_left (pow_pos hl.pos m) h3)

theorem exists_mul_of_redL_eq_zero (hn : n ≠ 0) {x : ZMod (l ^ n)} (h : redL l hn x = 0) :
    ∃ y : ZMod (l ^ n), x = l * y := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have h' : (x.val : ZMod l) = 0 := by
    rw [← ZMod.cast_eq_val]
    exact h
  obtain ⟨q, hq⟩ := (ZMod.natCast_eq_zero_iff _ _).1 h'
  exact ⟨q, by rw [← ZMod.natCast_zmod_val x, hq, Nat.cast_mul]⟩

theorem lpow_eq_zero : (l : ZMod (l ^ n)) ^ n = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

variable {r : ℕ} {b : Fin r → Γ → ZMod l} {e : Fin r → Γ}

theorem eq_zero_of_eval1 (hspan1 : ∀ y : Γ → ZMod l, IsParHom P y → ∀ g, y g = ∑ i, y (e i) * b i g)
    {v : Γ → ZMod l} (hv : IsParHom P v) (he : ∀ j, v (e j) = 0) (g : Γ) : v g = 0 := by
  rw [hspan1 v hv g]
  exact Finset.sum_eq_zero fun i _ => by rw [he i, zero_mul]

/-- Mod `lⁿ`, a parabolic homomorphism vanishing at all `e_j` is zero (`l`-adic descent). -/
theorem eval_inj (hn : n ≠ 0) (hspan1 : ∀ y : Γ → ZMod l, IsParHom P y → ∀ g, y g = ∑ i, y (e i) * b i g)
    {w : Γ → ZMod (l ^ n)} (hw : IsParHom P w) (he : ∀ j, w (e j) = 0) (g : Γ) : w g = 0 := by
  classical
  suffices key : ∀ m ≤ n, ∀ g, ∃ u : ZMod (l ^ n), w g = (l : ZMod (l ^ n)) ^ m * u by
    obtain ⟨u, hu⟩ := key n le_rfl g
    rw [hu, lpow_eq_zero, zero_mul]
  intro m
  induction m with
  | zero => exact fun _ g => ⟨w g, by rw [pow_zero, one_mul]⟩
  | succ m ih =>
    intro hm g
    have IH := ih (by omega)
    have hmn : m < n := by omega
    let F : ZMod (l ^ n) → ZMod l := fun x =>
      if h : ∃ u : ZMod (l ^ n), x = (l : ZMod (l ^ n)) ^ m * u then redL l hn (Classical.choose h) else 0
    have hF : ∀ g, w g = (l : ZMod (l ^ n)) ^ m * Classical.choose (IH g) := fun g => Classical.choose_spec (IH g)
    have hFv : ∀ g, F (w g) = redL l hn (Classical.choose (IH g)) := fun g => dif_pos (IH g)
    have hv : IsParHom P (fun g => F (w g)) := by
      refine ⟨hw.1.comp F, fun a c => ?_, fun g hg => ?_⟩
      · show F (w (a * c)) = F (w a) + F (w c)
        rw [hFv, hFv, hFv, ← sub_eq_zero, ← map_add, ← map_sub]
        refine redL_eq_zero_of_mul hn hmn ?_
        rw [mul_sub, mul_add, ← hF, ← hF, ← hF, hw.2.1, sub_self]
      · show F (w g) = 0
        rw [hFv]
        refine redL_eq_zero_of_mul hn hmn ?_
        rw [← hF, hw.2.2 g hg]
    have h0 : F (w g) = 0 := eq_zero_of_eval1 hspan1 hv (fun j => by
      show F (w (e j)) = 0
      rw [hFv]
      exact redL_eq_zero_of_mul hn hmn (by rw [← hF, he j])) g
    rw [hFv g] at h0
    obtain ⟨y, hy⟩ := exists_mul_of_redL_eq_zero hn h0
    exact ⟨y, by rw [hF g, hy, ← mul_assoc, ← pow_succ]⟩

/-- Lifts `χ'_i` of the `b_i` make evaluation at the `e_j` onto mod `lⁿ` (Nakayama). -/
theorem exists_eval (hn : n ≠ 0) (hbe : ∀ i j, b i (e j) = if i = j then 1 else 0)
    {χ' : Fin r → Γ → ZMod (l ^ n)} (hχ' : ∀ i, IsParHom P (χ' i)) (hred : ∀ i g, redL l hn (χ' i g) = b i g)
    (v : Fin r → ZMod (l ^ n)) : ∃ y : Γ → ZMod (l ^ n), IsParHom P y ∧ ∀ j, y (e j) = v j := by
  classical
  suffices key : ∀ k, ∃ y : Γ → ZMod (l ^ n), IsParHom P y ∧ ∃ u : Fin r → ZMod (l ^ n),
      ∀ j, v j = y (e j) + (l : ZMod (l ^ n)) ^ k * u j by
    obtain ⟨y, hy, u, hu⟩ := key n
    exact ⟨y, hy, fun j => by rw [hu j, lpow_eq_zero, zero_mul, add_zero]⟩
  intro k
  induction k with
  | zero => exact ⟨fun _ => 0, isParHom_zeroV, v, fun j => by rw [pow_zero, one_mul, zero_add]⟩
  | succ k ih =>
    obtain ⟨y, hy, u, hu⟩ := ih
    have hd : ∀ j, ∃ u' : ZMod (l ^ n), u j - ∑ i, u i * χ' i (e j) = l * u' := fun j => by
      refine exists_mul_of_redL_eq_zero hn ?_
      simp only [map_sub, map_sum, map_mul, hred, hbe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, sub_self]
    choose u' hu' using hd
    refine ⟨fun g => y g + (l : ZMod (l ^ n)) ^ k * ∑ i, u i * χ' i g,
      hy.addV ((IsParHom.sumV Finset.univ fun i => (hχ' i).cmulV (u i)).cmulV _), u', fun j => ?_⟩
    show v j = y (e j) + (l : ZMod (l ^ n)) ^ k * ∑ i, u i * χ' i (e j) + (l : ZMod (l ^ n)) ^ (k + 1) * u' j
    rw [hu j, pow_succ, mul_assoc, ← hu' j]
    ring

/-- **A parabolic dual basis mod `lⁿ`** from one mod `l` whose members lift (O9b, V-free). -/
theorem exists_parBasis_of_lift (hn : n ≠ 0) (hbe : ∀ i j, b i (e j) = if i = j then 1 else 0)
    (hspan1 : ∀ y : Γ → ZMod l, IsParHom P y → ∀ g, y g = ∑ i, y (e i) * b i g)
    (hlift : ∀ i, ∃ y : Γ → ZMod (l ^ n), IsParHom P y ∧ ∀ g, redL l hn (y g) = b i g) :
    ∃ χ : Fin r → Γ → ZMod (l ^ n), (∀ i, IsParHom P (χ i)) ∧ (∀ i j, χ i (e j) = if i = j then 1 else 0) ∧
      ∀ y : Γ → ZMod (l ^ n), IsParHom P y → ∀ g, y g = ∑ i, y (e i) * χ i g := by
  classical
  choose χ' hχ' hred using hlift
  choose χ hχ hχe using fun i => exists_eval hn hbe hχ' hred (fun j => if i = j then 1 else 0)
  refine ⟨χ, hχ, hχe, fun y hy g => ?_⟩
  have hw := hy.subV (IsParHom.sumV Finset.univ fun i => (hχ i).cmulV (y (e i)))
  have h0 := eval_inj hn hspan1 hw (fun j => by
    show y (e j) - ∑ i, y (e i) * χ i (e j) = 0
    simp only [hχe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      sub_self]) g
  exact sub_eq_zero.1 h0

end VFree

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_CupDuality_VLift =====
section

/-!
# S4-CurveDuality, O9b (V-free) part 2: parabolic homomorphisms to `ℤ/l` lift to `ℤ/lⁿ`

Route L (session 50; replaces the counting steps V-perf/V-lev of the session-49 design). `σ` trivial on `Γ`.
* `exists_lift_hom`: if `H²(Γ, ℤ/lⁿ) = 0` (`H2Van`), every locally constant homomorphism `χ : Γ → ℤ/l` lifts to one
  `Γ → ℤ/lⁿ`: the integer carry `c(g, h) = (χ̃ g + χ̃ h - χ̃(gh)) / l` is a 2-cocycle, `c = δb`, `χ' = χ̃ - l b`.
* `exists_parLift`: with the residue data `ConstData` at level `lⁿ`, a lift of a parabolic `χ` can be made parabolic:
  its residues `χ'(t_s) = l y_s` are corrected by `l d` with `d(t_s) = y'_s`, `Σ y'_s = 0` (`resOnto`), and a
  cocycle on `Γ ⊓ I s` vanishing at `t_s` is zero (`inj`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.CupDuality

open CurveCoh PerfectCx

section VLift

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G} {l n : ℕ}
  [Fact l.Prime]

/-- The carry of `χ g + χ h`. -/
def carry (χ : Γ → ZMod l) (x : Γ × Γ) : ℕ := ((χ x.1).val + (χ x.2).val) / l

theorem carry_spec {χ : Γ → ZMod l} (hχ : ∀ a b, χ (a * b) = χ a + χ b) (g h : Γ) :
    l * carry χ (g, h) + (χ (g * h)).val = (χ g).val + (χ h).val := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  show l * (((χ g).val + (χ h).val) / l) + (χ (g * h)).val = _
  rw [hχ, ZMod.val_add]
  exact Nat.div_add_mod _ _

theorem carry_cocycle {χ : Γ → ZMod l} (hχ : ∀ a b, χ (a * b) = χ a + χ b) (g h j : Γ) :
    carry χ (g * h, j) + carry χ (g, h) = carry χ (h, j) + carry χ (g, h * j) := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have e1 := carry_spec hχ (g * h) j
  have e2 := carry_spec hχ g h
  have e3 := carry_spec hχ h j
  have e4 := carry_spec hχ g (h * j)
  rw [mul_assoc] at e1
  refine Nat.eq_of_mul_eq_mul_left hl ?_
  zify at e1 e2 e3 e4 ⊢
  linear_combination e1 + e2 - e3 - e4

variable {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G} {t : (s : S) → ↥(Γ ⊓ I s)}

/-- **Parabolic lifts.** A lift of a parabolic `χ : Γ → ℤ/l` can be corrected to a parabolic lift. -/
theorem exists_parLift (hn : n ≠ 0) {σ : Representation (ZMod (l ^ n)) G (ZMod (l ^ n))}
    (D : ConstData σ Γ I t) {χ : Γ → ZMod l} (hχ : IsParHom (InBdry I) χ) {χ' : Γ → ZMod (l ^ n)}
    (hlc' : IsLocallyConstant χ') (hχ' : ∀ a b, χ' (a * b) = χ' a + χ' b) (hred : ∀ g, redL l hn (χ' g) = χ g) :
    ∃ ψ : Γ → ZMod (l ^ n), IsParHom (InBdry I) ψ ∧ ∀ g, redL l hn (ψ g) = χ g := by
  classical
  have hz : χ' ∈ Z1 σ Γ := (mem_Z1 σ Γ χ').2 ⟨hlc', fun a b => by rw [D.triv]; exact hχ' a b⟩
  have hr : ∀ s, ∃ y : ZMod (l ^ n), χ' (tG t s) = l * y := fun s =>
    exists_mul_of_redL_eq_zero hn (by rw [hred]; exact hχ.2.2 _ ⟨s, (Subgroup.mem_inf.1 (t s).2).2⟩)
  choose y hy using hr
  obtain ⟨s0⟩ := (inferInstance : Nonempty S)
  have hc : (l : ZMod (l ^ n)) * ∑ s, y s = 0 := by
    have hsum : ∑ s, χ' (tG t s) = 0 := D.resSum ⟨χ', hz⟩
    simp only [hy] at hsum
    rw [Finset.mul_sum]
    exact hsum
  have hy' : ∑ s, (y s - if s = s0 then ∑ s, y s else 0) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  obtain ⟨d, hd⟩ := D.resOnto _ hy'
  have hdZ := (mem_Z1 σ Γ _).1 d.2
  have hdadd : ∀ a b, (d : Γ → ZMod (l ^ n)) (a * b) = (d : Γ → ZMod (l ^ n)) a + (d : Γ → ZMod (l ^ n)) b :=
    fun a b => by rw [hdZ.2, D.triv]
  let ψ : Γ → ZMod (l ^ n) := fun g => χ' g - (l : ZMod (l ^ n)) * (d : Γ → ZMod (l ^ n)) g
  have hψt : ∀ s, ψ (tG t s) = 0 := by
    intro s
    show χ' (tG t s) - (l : ZMod (l ^ n)) * (d : Γ → ZMod (l ^ n)) (tG t s) = 0
    rw [hd s, hy s, mul_sub]
    by_cases h : s = s0
    · rw [if_pos h, hc, sub_zero, sub_self]
    · rw [if_neg h, mul_zero, sub_zero, sub_self]
  have hψlc : IsLocallyConstant ψ := hlc'.comp₂ hdZ.1 (fun u v => u - (l : ZMod (l ^ n)) * v)
  have hψadd : ∀ a b, ψ (a * b) = ψ a + ψ b := fun a b => by
    show χ' (a * b) - (l : ZMod (l ^ n)) * (d : Γ → ZMod (l ^ n)) (a * b) =
      (χ' a - (l : ZMod (l ^ n)) * (d : Γ → ZMod (l ^ n)) a) + (χ' b - (l : ZMod (l ^ n)) * (d : Γ → ZMod (l ^ n)) b)
    rw [hχ', hdadd]
    ring
  refine ⟨ψ, ⟨hψlc, hψadd, fun g ⟨s, hg⟩ => ?_⟩, fun g => ?_⟩
  · have htI : ∀ (x : ↥(Γ ⊓ I s)) (v : ZMod (l ^ n)), σ (x : G) v = v := fun x v =>
      D.triv ⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩ v
    let e : Z1 σ (Γ ⊓ I s) := ⟨fun x => ψ ⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, (mem_Z1 σ _ _).2
      ⟨hψlc.comp_continuous (continuous_subtype_val.subtype_mk fun x => (Subgroup.mem_inf.1 x.2).1),
        fun a b => by
          rw [htI]
          exact hψadd ⟨a.1, (Subgroup.mem_inf.1 a.2).1⟩ ⟨b.1, (Subgroup.mem_inf.1 b.2).1⟩⟩⟩
    have he : e = 0 := D.inj s e (hψt s)
    exact congrFun (congrArg Subtype.val he) ⟨g.1, Subgroup.mem_inf.2 ⟨g.2, hg⟩⟩
  · show redL l hn (χ' g - (l : ZMod (l ^ n)) * (d : Γ → ZMod (l ^ n)) g) = χ g
    rw [map_sub, map_mul, map_natCast, ZMod.natCast_self, zero_mul, sub_zero, hred]

end VLift

end RamanujanPetersson.CupDuality


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

variable (N : ℕ) (Γ I) in
/-- The `ℤ/N`-module of `ℤ/N`-valued parabolic homomorphisms on `Γ`. -/
def parMod : Submodule (ZMod N) (Γ → ZMod N) where
  carrier := {y | IsParHom (InBdry I) y}
  add_mem' hx hy := hx.addV hy
  zero_mem' := isParHom_zeroV
  smul_mem' c _ hy := hy.cmulV c

theorem mem_parMod (N : ℕ) (y : Γ → ZMod N) : y ∈ parMod Γ I N ↔ IsParHom (InBdry I) y := Iff.rfl

variable {l : ℕ} [Fact l.Prime]

variable [Γ.Normal] {n : ℕ}

end VPar

end

end RamanujanPetersson.CupDuality


end

-- ===== S4.Def_RP_CurveCoh_Lim =====
section

/-!
# S4-CurveCoh, part 6: functoriality in the coefficients and the `λ`-adic limit

Review END-2 / decision R19: the cohomology of parts 1-5 is stated over ANY commutative ring `k`, so it applies to
each level `O_λ ⧸ λⁿ` of an S4-Coeffs `CoeffTower` (`O_λ` the ring of integers of a finite `E_λ/ℚ_l`). For the
`λ`-adic limit we work over the one ring `k = O_λ`: an inverse system of `k`-representations `M n` of `G` (each
killed by `λⁿ`, i.e. an `O ⧸ λⁿ`-module viewed over `O`) with equivariant transition maps `f n : M (n+1) → M n`.

* `IsEquivariant`, `mapH0`, `mapH1`, `mapH1c`: functoriality of `H⁰`, `H¹`, `H¹_c` in the coefficients;
  `mapH1c_frobH1c`: it commutes with the operators `T_ψ` (so with the geometric Frobenius `F = T_{φ⁻¹}`);
  `mapH1c_bdryToH1c`, `h1cToH1_mapH1c`: it commutes with the maps of the exact sequence.
* `H0Lim`, `H1Lim`, `H1cLim`: the inverse limits `lim_n Hⁱ(M n)` (submodules of `Π n, Hⁱ(M n)`), and
  `frobH1cLim`: the geometric Frobenius on `lim_n H¹_c(M n)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G]
  {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {ρ : Representation k G M} {ρ' : Representation k G N} (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

/-- `f : M → N` is a morphism of representations. -/
def IsEquivariant (ρ : Representation k G M) (ρ' : Representation k G N) (f : M →ₗ[k] N) : Prop :=
  ∀ (g : G) (m : M), f (ρ g m) = ρ' g (f m)

/-! ## Functoriality -/

theorem push_mem_Z1 {f : M →ₗ[k] N} (hf : IsEquivariant ρ ρ' f) {c : Γ → M} (hc : c ∈ Z1 ρ Γ) :
    f.compLeft Γ c ∈ Z1 ρ' Γ :=
  ⟨hc.1.comp f, fun g h => by
    show f (c (g * h)) = f (c g) + ρ' g (f (c h))
    rw [hc.2 g h, map_add, hf]⟩

theorem push_mem_B1 {f : M →ₗ[k] N} (hf : IsEquivariant ρ ρ' f) {c : Γ → M} (hc : c ∈ B1 ρ Γ) :
    f.compLeft Γ c ∈ B1 ρ' Γ := by
  obtain ⟨hz, m, hm⟩ := hc
  refine ⟨push_mem_Z1 Γ hf hz, f m, fun g => ?_⟩
  show f (c g) = ρ' g (f m) - f m
  rw [hm, map_sub, hf]

/-- `H¹(f)`. -/
def mapH1 {f : M →ₗ[k] N} (hf : IsEquivariant ρ ρ' f) : H1 ρ Γ →ₗ[k] H1 ρ' Γ :=
  Submodule.mapQ _ _ ((f.compLeft Γ).restrict (fun c hc => push_mem_Z1 Γ hf hc))
    (fun c hc => push_mem_B1 Γ hf hc)

/-- Pushing cone cochains along `f`. -/
def pushc (f : M →ₗ[k] N) : ((Γ → M) × (S → M)) →ₗ[k] ((Γ → N) × (S → N)) :=
  LinearMap.prodMap (f.compLeft Γ) (f.compLeft S)

theorem pushc_apply (f : M →ₗ[k] N) (p : (Γ → M) × (S → M)) :
    pushc Γ f p = (fun g => f (p.1 g), fun s => f (p.2 s)) := rfl

theorem pushc_mem_Z1c {f : M →ₗ[k] N} (hf : IsEquivariant ρ ρ' f) {p : (Γ → M) × (S → M)}
    (hp : p ∈ Z1c ρ Γ I) : pushc Γ f p ∈ Z1c ρ' Γ I :=
  ⟨push_mem_Z1 Γ hf hp.1, fun s g hg => by
    show f (p.1 g) = ρ' g (f (p.2 s)) - f (p.2 s)
    rw [hp.2 s g hg, map_sub, hf]⟩

theorem pushc_mem_B1c {f : M →ₗ[k] N} (hf : IsEquivariant ρ ρ' f) {p : (Γ → M) × (S → M)}
    (hp : p ∈ B1c ρ Γ I) : pushc Γ f p ∈ B1c ρ' Γ I := by
  obtain ⟨hz, m, hm, hm'⟩ := hp
  refine ⟨pushc_mem_Z1c Γ I hf hz, f m, fun g => ?_, fun s => ?_⟩
  · show f (p.1 g) = ρ' g (f m) - f m
    rw [hm, map_sub, hf]
  · show f (p.2 s) = f m
    rw [hm']

/-- `H¹_c(f)`. -/
def mapH1c {f : M →ₗ[k] N} (hf : IsEquivariant ρ ρ' f) : H1c ρ Γ I →ₗ[k] H1c ρ' Γ I :=
  Submodule.mapQ _ _ ((pushc Γ f).restrict (fun p hp => pushc_mem_Z1c Γ I hf hp))
    (fun p hp => pushc_mem_B1c Γ I hf hp)

theorem mapH1c_mk {f : M →ₗ[k] N} (hf : IsEquivariant ρ ρ' f) (p : Z1c ρ Γ I) :
    mapH1c Γ I hf (H1c.mk ρ Γ I p) = H1c.mk ρ' Γ I ⟨pushc Γ f p, pushc_mem_Z1c Γ I hf p.2⟩ := rfl

section Frob

variable [IsTopologicalGroup G] [Γ.Normal]

end Frob

/-! ## The `λ`-adic limit -/

section Lim

variable {Mn : ℕ → Type} [∀ n, AddCommGroup (Mn n)] [∀ n, Module k (Mn n)]
  (ρn : ∀ n, Representation k G (Mn n)) (f : ∀ n, Mn (n + 1) →ₗ[k] Mn n)
  (hf : ∀ n, IsEquivariant (ρn (n + 1)) (ρn n) (f n))

section Frob

variable [IsTopologicalGroup G] [Γ.Normal]

end Frob

end Lim

end

end CurveCoh
end RamanujanPetersson


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

theorem isPrim_push {f : M →ₗ[k] M₂} {g : M₂' →ₗ[k] M'} (hg : IsEquivariant ρ₂' ρ' g)
    (hβ : ∀ m y, β₂ (f m) y = β m (g y)) {c : Γ → M} {d : Γ → M₂'} {u : Γ → L}
    (hu : IsPrim ρ' σ β Γ c (g.compLeft Γ d) u) : IsPrim ρ₂' σ β₂ Γ (f.compLeft Γ c) d u := by
  refine ⟨hu.1, fun a b => ?_⟩
  have h := hu.2 a b
  show β₂ (f (c a)) (ρ₂' a (d b)) = σ a (u b) - u (a * b) + u a
  rw [hβ, hg]
  exact h

/-! ## Dual coefficients `M^∨(1) = Hom(M, L)` -/

/-- The evaluation pairing `M × Hom(M, L) → L`. -/
def evalB : M →ₗ[k] (M →ₗ[k] L) →ₗ[k] L := LinearMap.applyₗ

theorem evalB_apply (m : M) (φ : M →ₗ[k] L) : evalB m φ = φ m := rfl

theorem ker_le_linHom (ρ : Representation k G M) (σ : Representation k G L) :
    ρ.ker ⊓ σ.ker ≤ (ρ.linHom σ).ker := by
  intro g hg
  have h1 : ρ g = 1 := (Subgroup.mem_inf.1 hg).1
  have h2 : σ g = 1 := (Subgroup.mem_inf.1 hg).2
  have h3 : ρ g⁻¹ = 1 := by
    have e := map_mul ρ g⁻¹ g
    rw [inv_mul_cancel, map_one, h1, mul_one] at e
    exact e.symm
  rw [MonoidHom.mem_ker]
  ext φ m
  rw [Representation.linHom_apply, h2, h3]
  rfl

theorem isOpen_linHom_ker (hρ : IsOpen (ρ.ker : Set G)) (hσ : IsOpen (σ.ker : Set G)) :
    IsOpen ((ρ.linHom σ).ker : Set G) :=
  Subgroup.isOpen_mono (ker_le_linHom ρ σ) (by
    show IsOpen ((ρ.ker : Set G) ∩ (σ.ker : Set G))
    exact hρ.inter hσ)

/-- Precomposition with `f : M → M₂`: the transpose `Hom(M₂, L) → Hom(M, L)`. -/
def transp (f : M →ₗ[k] M₂) : (M₂ →ₗ[k] L) →ₗ[k] (M →ₗ[k] L) where
  toFun φ := φ ∘ₗ f
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_smul' _ _ := LinearMap.ext fun _ => rfl

theorem transp_apply (f : M →ₗ[k] M₂) (φ : M₂ →ₗ[k] L) (m : M) : transp f φ m = φ (f m) := rfl

theorem transp_equivariant {f : M →ₗ[k] M₂} (hf : IsEquivariant ρ ρ₂ f) :
    IsEquivariant (ρ₂.linHom σ) (ρ.linHom σ) (transp (L := L) f) := by
  intro g φ
  apply LinearMap.ext
  intro m
  rw [transp_apply, Representation.linHom_apply, Representation.linHom_apply]
  show σ g (φ (ρ₂ g⁻¹ (f m))) = σ g (φ (f (ρ g⁻¹ m)))
  rw [hf]

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

theorem mapH1c_injective [Nonempty S] {f : M →ₗ[k] X} (hf : IsEquivariant ρ ρX f)
    (hinj : Function.Injective f) : Function.Injective (mapH1c Γ I hf) := by
  refine (injective_iff_map_eq_zero (mapH1c Γ I hf)).2 fun x hx => ?_
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ x
  have hx0 : (Submodule.Quotient.mk (⟨pushc Γ f p, pushc_mem_Z1c Γ I hf p.2⟩ : Z1c ρX Γ I) :
      H1c ρX Γ I) = 0 := hx
  have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx0
  have hB : pushc Γ f (p : (Γ → M) × (S → M)) ∈ B1c ρX Γ I := hx'
  obtain ⟨-, x₂, hx₁, hx₂⟩ := (mem_B1c ρX Γ I _).1 hB
  have e0 : f ((p : (Γ → M) × (S → M)).2 (Classical.arbitrary S)) = x₂ := hx₂ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  show (p : (Γ → M) × (S → M)) ∈ B1c ρ Γ I
  refine (mem_B1c ρ Γ I _).2 ⟨p.2, (p : (Γ → M) × (S → M)).2 (Classical.arbitrary S), fun g => hinj ?_,
    fun s => hinj ?_⟩
  · have h := hx₁ g
    rw [map_sub, hf, e0]
    exact h
  · have h := hx₂ s
    rw [e0]
    exact h

/-- Cocycles with values in the image of an injective `f` come from `M`. -/
theorem exists_pull_Z1c {f : M →ₗ[k] X} (hf : IsEquivariant ρ ρX f) (hinj : Function.Injective f)
    (P : Z1c ρX Γ I) (h1 : ∀ g, (P : (Γ → X) × (S → X)).1 g ∈ Set.range f)
    (h2 : ∀ s, (P : (Γ → X) × (S → X)).2 s ∈ Set.range f) :
    ∃ P' : Z1c ρ Γ I, pushc Γ f (P' : (Γ → M) × (S → M)) = P := by
  obtain ⟨⟨hlc, hcoc⟩, hbd⟩ := (mem_Z1c ρX Γ I _).1 P.2
  set a : Γ → M := fun g => Function.invFun f ((P : (Γ → X) × (S → X)).1 g) with ha
  set b : S → M := fun s => Function.invFun f ((P : (Γ → X) × (S → X)).2 s) with hb
  have fa : ∀ g, f (a g) = (P : (Γ → X) × (S → X)).1 g := fun g => Function.invFun_eq (h1 g)
  have fb : ∀ s, f (b s) = (P : (Γ → X) × (S → X)).2 s := fun s => Function.invFun_eq (h2 s)
  have hmem : (a, b) ∈ Z1c ρ Γ I := by
    refine (mem_Z1c ρ Γ I _).2 ⟨(mem_Z1 ρ Γ _).2 ⟨hlc.comp (Function.invFun f), fun g h => hinj ?_⟩, fun s g hg => hinj ?_⟩
    · show f (a (g * h)) = f (a g + ρ g (a h))
      rw [map_add, hf, fa, fa, fa]
      exact hcoc g h
    · show f (a g) = f (ρ g (b s) - b s)
      rw [map_sub, hf, fa, fb]
      exact hbd s g hg
  refine ⟨⟨(a, b), hmem⟩, ?_⟩
  rw [pushc_apply]
  exact Prod.ext (funext fa) (funext fb)

/-! ## `H¹` is right exact (cohomological dimension `≤ 1`) -/

/-! ## Duals over a self-injective coefficient ring -/

theorem transp_surjective {L : Type} [AddCommGroup L] [Module k L] [Module.Injective k L] {f : M →ₗ[k] X}
    (hinj : Function.Injective f) : Function.Surjective (transp (L := L) f) := by
  intro φ
  obtain ⟨h, hh⟩ := Module.Injective.out f hinj φ
  exact ⟨h, LinearMap.ext hh⟩

/-! ## The dévissage chase (O7c) -/

section Chase

variable {R : Type} [CommRing R] {HM HX HQ DM DX DQ : Type} [AddCommGroup HM] [Module R HM]
  [AddCommGroup HX] [Module R HX] [AddCommGroup HQ] [Module R HQ] [AddCommGroup DM] [Module R DM]
  [AddCommGroup DX] [Module R DX] [AddCommGroup DQ] [Module R DQ]

theorem injective_of_chase (i : HM →ₗ[R] HX) (i' : DM →ₗ[R] DX) (aM : HM →ₗ[R] DM) (aX : HX →ₗ[R] DX)
    (hi : Function.Injective i) (c1 : ∀ x, aX (i x) = i' (aM x)) (hX : Function.Injective aX) :
    Function.Injective aM := fun x x' h => hi (hX (by rw [c1, c1, h]))

theorem bijective_of_chase (i : HM →ₗ[R] HX) (j : HX →ₗ[R] HQ) (i' : DM →ₗ[R] DX) (j' : DX →ₗ[R] DQ)
    (aM : HM →ₗ[R] DM) (aX : HX →ₗ[R] DX) (aQ : HQ →ₗ[R] DQ) (hi : Function.Injective i)
    (hij : ∀ y, j y = 0 → ∃ x, i x = y) (hi' : Function.Injective i') (hj'i' : ∀ x, j' (i' x) = 0)
    (c1 : ∀ x, aX (i x) = i' (aM x)) (c2 : ∀ y, aQ (j y) = j' (aX y)) (hX : Function.Bijective aX)
    (hQ : Function.Injective aQ) : Function.Bijective aM := by
  refine ⟨injective_of_chase i i' aM aX hi c1 hX.1, fun φ => ?_⟩
  obtain ⟨y, hy⟩ := hX.2 (i' φ)
  have hj : j y = 0 := hQ (by rw [c2, hy, hj'i', map_zero])
  obtain ⟨x, rfl⟩ := hij y hj
  exact ⟨x, hi' (by rw [← c1, hy])⟩

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

theorem mapH1_transp_comp {ρ : Representation Λ G M} {ρX : Representation Λ G X} {Q : Type} [AddCommGroup Q]
    [Module Λ Q] {ρQ : Representation Λ G Q} {f : M →ₗ[Λ] X} (hf : IsEquivariant ρ ρX f) {q : X →ₗ[Λ] Q}
    (hq : IsEquivariant ρX ρQ q) (hqf : ∀ m, q (f m) = 0) (y : H1 (ρQ.linHom σ) Γ) :
    mapH1 Γ (transp_equivariant (σ := σ) hf) (mapH1 Γ (transp_equivariant (σ := σ) hq) y) = 0 := by
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
  have e2 : (⟨fun a => transp f (transp q ((d : Γ → (Q →ₗ[Λ] Λ)) a)),
      push_mem_Z1 Γ (transp_equivariant hf) (push_mem_Z1 Γ (transp_equivariant hq) d.2)⟩ :
        Z1 (ρ.linHom σ) Γ) = 0 :=
    Subtype.ext (funext fun a => LinearMap.ext fun m => by
      rw [transp_apply, transp_apply, hqf, map_zero]
      rfl)
  have e1 : mapH1 Γ (transp_equivariant (σ := σ) hf) (mapH1 Γ (transp_equivariant (σ := σ) hq)
      (Submodule.mkQ _ d)) = Submodule.mkQ _ (⟨fun a => transp f (transp q ((d : Γ → (Q →ₗ[Λ] Λ)) a)),
      push_mem_Z1 Γ (transp_equivariant hf) (push_mem_Z1 Γ (transp_equivariant hq) d.2)⟩ :
        Z1 (ρ.linHom σ) Γ) := rfl
  rw [e1, e2, map_zero]

/-! ## Coinduced modules and the canonical embedding -/

variable {Gf : Type} [Group Gf]

/-- `Gf → M₀` with left translation `(h · F)(x) = F(h⁻¹ x)`. -/
def coindF (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] : Representation Λ Gf (Gf → M₀) where
  toFun h := LinearMap.funLeft Λ M₀ (fun x => h⁻¹ * x)
  map_one' := LinearMap.ext fun F => funext fun x => by
    simp only [LinearMap.funLeft_apply, inv_one, one_mul, Module.End.one_apply]
  map_mul' h h' := LinearMap.ext fun F => funext fun x => by
    simp only [LinearMap.funLeft_apply, mul_inv_rev, mul_assoc, Module.End.mul_apply]

theorem coindF_apply (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] (h : Gf) (F : Gf → M₀) (x : Gf) :
    coindF (Λ := Λ) M₀ h F x = F (h⁻¹ * x) := rfl

/-- `m ↦ (x ↦ τ(x⁻¹) m)`. -/
def emb (τ : Representation Λ Gf M) : M →ₗ[Λ] (Gf → M) := LinearMap.pi fun x => τ x⁻¹

theorem emb_apply (τ : Representation Λ Gf M) (m : M) (x : Gf) : emb τ m x = τ x⁻¹ m := rfl

theorem emb_equiv (τ : Representation Λ Gf M) (h : Gf) (m : M) : emb τ (τ h m) = coindF (Λ := Λ) M h (emb τ m) :=
  funext fun x => by
    rw [emb_apply, coindF_apply, emb_apply, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

theorem emb_injective (τ : Representation Λ Gf M) : Function.Injective (emb τ) := fun m m' h => by
  have := congrFun h 1
  rw [emb_apply, emb_apply, inv_one, map_one] at this
  exact this

/-- The quotient representation on `(Gf → M) / emb(M)`. -/
def quotRepF (τ : Representation Λ Gf M) : Representation Λ Gf ((Gf → M) ⧸ LinearMap.range (emb τ)) where
  toFun h := (LinearMap.range (emb τ)).mapQ _ (coindF (Λ := Λ) M h) (fun F hF => by
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.1 hF
    exact LinearMap.mem_range.2 ⟨τ h m, emb_equiv τ h m⟩)
  map_one' := by
    apply Submodule.linearMap_qext
    refine LinearMap.ext fun F => ?_
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_one, Module.End.one_apply]
  map_mul' h h' := by
    apply Submodule.linearMap_qext
    refine LinearMap.ext fun F => ?_
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, map_mul, Module.End.mul_apply]

theorem quotRepF_mk (τ : Representation Λ Gf M) (h : Gf) (F : Gf → M) :
    quotRepF τ h (Submodule.Quotient.mk F) = Submodule.Quotient.mk (coindF (Λ := Λ) M h F) := rfl

theorem isOpen_comp (π : G →* Gf) (hπ : IsOpen (π.ker : Set G)) (τ : Representation Λ Gf M) :
    IsOpen ((τ.comp π).ker : Set G) :=
  Subgroup.isOpen_mono (fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]) hπ

/-! ## Dévissage -/

variable (π : G →* Gf) (hπ : IsOpen (π.ker : Set G))

theorem finite_dual [Finite X] [Finite Λ] : Finite (X →ₗ[Λ] Λ) :=
  Finite.of_injective (fun φ : X →ₗ[Λ] Λ => (φ : X → Λ)) DFunLike.coe_injective

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Base =====
section

/-!
# S4-CurveDuality O7c': the dévissage base reduces to the regular coinduced module `coindF Λ`

* `sum_mapH1c_retract`, `sum_mapH1_retract`: `H¹_c` and `H¹` respect finite retract decompositions
  `Σᵢ injᵢ ∘ projᵢ = id`;
* `alpha_bijective_of_retract`: the duality map `alphaM` is bijective on `X` once it is bijective on a module `Y`
  of which `X` is a finite retract sum (covers equivariant isomorphisms, `ι = Unit`);
* `alpha_injective_of_emb`, `alpha_bijective_of_ses`: the two dévissage steps for an arbitrary short exact sequence;
* `SepDual Λ`: the `Λ`-dual separates points of finite modules (true for finite local self-injective `Λ`);
* `alpha_free_bijective`: bijective on `coindF Λ` ⇒ bijective on every `coindF (ι → Λ)`;
* `base_injective`, `base_bijective`: ⇒ bijective on every `coindF M₀`, `M₀` finite (via `M₀ ↪ (Dual M₀ → Λ)`);
* `alpha_bijective_of_regular`: lisse duality for every finite `τ ∘ π` from the single base case `coindF Λ`.
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
  {Y : Type} [AddCommGroup Y] [Module Λ Y] {Q : Type} [AddCommGroup Q] [Module Λ Q]
  {ρ : Representation Λ G M} {ρX : Representation Λ G X} {ρY : Representation Λ G Y}
  {ρQ : Representation Λ G Q}

/-! ## Retracts -/

section Retract

variable {ι : Type} [Fintype ι]

theorem sum_mapH1c_retract {inj : ι → (Y →ₗ[Λ] X)} {proj : ι → (X →ₗ[Λ] Y)}
    (hinj : ∀ i, IsEquivariant ρY ρX (inj i)) (hproj : ∀ i, IsEquivariant ρX ρY (proj i))
    (hsum : ∀ x, ∑ i, inj i (proj i x) = x) (z : H1c ρX Γ I) :
    ∑ i, mapH1c Γ I (hinj i) (mapH1c Γ I (hproj i) z) = z := by
  obtain ⟨p, rfl⟩ := Submodule.mkQ_surjective _ z
  let q : ι → Z1c ρX Γ I := fun i => ⟨pushc Γ (inj i) (pushc Γ (proj i) p),
    pushc_mem_Z1c Γ I (hinj i) (pushc_mem_Z1c Γ I (hproj i) p.2)⟩
  have e1 : ∀ i, mapH1c Γ I (hinj i) (mapH1c Γ I (hproj i) (Submodule.mkQ _ p)) = Submodule.mkQ _ (q i) :=
    fun i => rfl
  have e2 : ∑ i, q i = p := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    refine Prod.ext (funext fun g => ?_) (funext fun s => ?_)
    · rw [Prod.fst_sum, Finset.sum_apply]
      exact hsum _
    · rw [Prod.snd_sum, Finset.sum_apply]
      exact hsum _
  simp only [e1]
  rw [← map_sum, e2]

theorem sum_mapH1_retract {a : ι → (Y →ₗ[Λ] X)} {b : ι → (X →ₗ[Λ] Y)}
    (ha : ∀ i, IsEquivariant ρY ρX (a i)) (hb : ∀ i, IsEquivariant ρX ρY (b i))
    (hsum : ∀ x, ∑ i, a i (b i x) = x) (y : H1 ρX Γ) :
    ∑ i, mapH1 Γ (ha i) (mapH1 Γ (hb i) y) = y := by
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y
  let q : ι → Z1 ρX Γ := fun i => ⟨fun g => a i (b i ((d : Γ → X) g)),
    push_mem_Z1 Γ (ha i) (push_mem_Z1 Γ (hb i) d.2)⟩
  have e1 : ∀ i, mapH1 Γ (ha i) (mapH1 Γ (hb i) (Submodule.mkQ _ d)) = Submodule.mkQ _ (q i) :=
    fun i => rfl
  have e2 : ∑ i, q i = d := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    refine funext fun g => ?_
    rw [Finset.sum_apply]
    exact hsum _
  simp only [e1]
  rw [← map_sum, e2]

end Retract

/-! ## The two dévissage steps for a short exact sequence -/

/-! ## Coinduced maps and the reduction to `coindF Λ` -/

variable {Gf : Type} [Group Gf] (π : G →* Gf) (hπ : IsOpen (π.ker : Set G))

/-- `coindF` on maps: pointwise composition. -/
def coindMap {M₀ N₀ : Type} [AddCommGroup M₀] [Module Λ M₀] [AddCommGroup N₀] [Module Λ N₀]
    (f : M₀ →ₗ[Λ] N₀) : (Gf → M₀) →ₗ[Λ] (Gf → N₀) := f.compLeft Gf

section CoindMap

variable {M₀ N₀ : Type} [AddCommGroup M₀] [Module Λ M₀] [AddCommGroup N₀] [Module Λ N₀]

theorem coindMap_apply (f : M₀ →ₗ[Λ] N₀) (F : Gf → M₀) (x : Gf) : coindMap f F x = f (F x) := rfl

theorem coindMap_equiv (f : M₀ →ₗ[Λ] N₀) :
    IsEquivariant ((coindF (Λ := Λ) M₀).comp π) ((coindF (Λ := Λ) N₀).comp π) (coindMap (Gf := Gf) f) :=
  fun _ _ => funext fun _ => rfl

theorem coindMap_injective {f : M₀ →ₗ[Λ] N₀} (hf : Function.Injective f) :
    Function.Injective (coindMap (Gf := Gf) f) := fun _ _ h => funext fun x => hf (congrFun h x)

theorem coindMap_surjective {f : M₀ →ₗ[Λ] N₀} (hf : Function.Surjective f) :
    Function.Surjective (coindMap (Gf := Gf) f) := fun F =>
  ⟨fun x => (hf (F x)).choose, funext fun x => (hf (F x)).choose_spec⟩

theorem coindMap_exact {P₀ : Type} [AddCommGroup P₀] [Module Λ P₀] {f : M₀ →ₗ[Λ] N₀} {g : N₀ →ₗ[Λ] P₀}
    (hex : Function.Exact f g) : Function.Exact (coindMap (Gf := Gf) f) (coindMap (Gf := Gf) g) := fun F =>
  ⟨fun h => ⟨fun x => ((hex (F x)).1 (congrFun h x)).choose,
      funext fun x => ((hex (F x)).1 (congrFun h x)).choose_spec⟩,
    fun ⟨F', hF'⟩ => by
      rw [← hF']
      exact funext fun x => (hex (f (F' x))).2 ⟨F' x, rfl⟩⟩

end CoindMap

/-- The `Λ`-dual separates points of every finite `Λ`-module. -/
def SepDual (Λ : Type) [CommRing Λ] : Prop :=
  ∀ (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] [Finite M₀] (m : M₀), m ≠ 0 → ∃ φ : M₀ →ₗ[Λ] Λ, φ m ≠ 0

/-- `m ↦ (φ ↦ φ m)`. -/
def dualEmb (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] : M₀ →ₗ[Λ] (Module.Dual Λ M₀ → Λ) :=
  LinearMap.pi fun φ => φ

theorem dualEmb_injective (hsep : SepDual Λ) (M₀ : Type) [AddCommGroup M₀] [Module Λ M₀] [Finite M₀] :
    Function.Injective (dualEmb (Λ := Λ) M₀) := by
  refine (injective_iff_map_eq_zero _).2 fun m hm => ?_
  by_contra hne
  obtain ⟨φ, hφ⟩ := hsep M₀ m hne
  exact hφ (congrFun hm φ)

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Push =====
section

/-!
# S4-CurveDuality O7d, steps P0 and P1: from the regular representation to a pushforward

* P0 (`alpha_bijective_of_regular_range`): the input `hone` of `alpha_bijective_of_regular` is only needed for a
  SURJECTIVE `π` (replace `π` by `π.rangeRestrict` and `τ` by `τ ∘ subtype`).
* P1 (`alpha_coindF_of_push`): for `π : G →* Gf` surjective with kernel `K`, `Fun(Gf, Λ) ∘ π ≅ f_* Λ = pushRep K Λ`
  (`F ↦ (x ↦ F (π x)⁻¹)`), so `hone` follows from duality for the pushforward of the constant sheaf along the
  cover with group `K` (no connectedness needed here; it enters only through Shapiro).
* `alpha_bijective_of_push`: lisse duality for every finite `τ ∘ π` from duality for `pushRep (ker π) Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {σ : Representation Λ G Λ} {hσ : IsOpen (σ.ker : Set G)} {Gf : Type} [Group Gf]

/-! ## P0 -/

/-! ## P1: `Fun(Gf, Λ) ∘ π ≅ pushRep (ker π) Λ` -/

section Push

variable (π : G →* Gf) (K : Subgroup G)

/-- `F ↦ (x ↦ F (π x)⁻¹)`. -/
def projP (hK : ∀ g, g ∈ K ↔ π g = 1) :
    (Gf → Λ) →ₗ[Λ] Representation.coindV K.subtype (Representation.trivial Λ K Λ) :=
  LinearMap.codRestrict _ (LinearMap.funLeft Λ Λ (fun x : G => (π x)⁻¹)) fun F h x => by
    have h1 : π (h : G) = 1 := (hK h).1 h.2
    show F (π ((h : G) * x))⁻¹ = F (π x)⁻¹
    rw [map_mul, h1, one_mul]

theorem projP_apply (hK : ∀ g, g ∈ K ↔ π g = 1) (F : Gf → Λ) (x : G) :
    ((projP π K hK F : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) : G → Λ) x =
      F (π x)⁻¹ := rfl

/-- `F' ↦ (y ↦ F' (s y⁻¹))` for a set-theoretic section `s` of `π`. -/
def injP (hs : Function.Surjective π) :
    Representation.coindV K.subtype (Representation.trivial Λ K Λ) →ₗ[Λ] (Gf → Λ) :=
  LinearMap.funLeft Λ Λ (fun y : Gf => Function.surjInv hs y⁻¹) ∘ₗ
    (Representation.coindV K.subtype (Representation.trivial Λ K Λ)).subtype

theorem injP_apply (hs : Function.Surjective π)
    (F' : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) (y : Gf) :
    injP π K hs F' y = (F' : G → Λ) (Function.surjInv hs y⁻¹) := rfl

theorem injP_projP (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π) (F : Gf → Λ) :
    injP π K hs (projP π K hK F) = F := funext fun y => by
  rw [injP_apply, projP_apply, Function.surjInv_eq hs, inv_inv]

theorem coindV_triv_eq (hK : ∀ g, g ∈ K ↔ π g = 1)
    (F' : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) {a b : G} (hab : π a = π b) :
    (F' : G → Λ) a = (F' : G → Λ) b := by
  have hm : a * b⁻¹ ∈ K := (hK _).2 (by rw [map_mul, map_inv, hab, mul_inv_cancel])
  have h := F'.2 ⟨a * b⁻¹, hm⟩ b
  rw [show K.subtype ⟨a * b⁻¹, hm⟩ * b = a by simp, Representation.trivial_apply] at h
  exact h

end Push

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Dual =====
section

/-!
# S4-CurveDuality O7d-P2: the dual of a finite push-forward, and Shapiro on the dual side

Let `π : G →* Gf` be surjective onto a finite group with kernel `K` (the cover `f : V → U` with group `Gf`), and
`σ : Representation Λ G Λ` the twist `Λ(1)`. Then `(f_* Λ)^∨(1) ≅ f_* (σ|K)` as representations of `G`:
* `psiP : (coindV K Λ →ₗ Λ) → coindV K (σ|K)`, `φ ↦ (x ↦ σ x (φ δ_x))`, `δ_x` the indicator of the coset `K x`
  (`deltaP`); equivariant (`psiP_equiv`);
* `phiP` its inverse, `F' ↦ (F ↦ Σ_{y : Gf} F (s y) * σ (s y)⁻¹ (F' (s y)))` for a section `s` of `π`;
* `dualPushEquiv`: the equivariant isomorphism; `mapH1Equiv`: `H¹` of an equivariant linear isomorphism;
* `shapiroDual : H¹(Γ, (f_* Λ)^∨(1)) ≃ H¹(Γ ∩ K, σ|K)` (`hcov`, `K` open), `shapiroDual_mk`: on cocycles
  `d ↦ (h ↦ d h δ_K)`;
* `bijective_of_equiv_pair`: a duality map is bijective once it agrees, through isomorphisms on both sides, with a
  bijective one (used to move `alphaM` to the cover).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

/-! ## `H¹` of an equivariant linear isomorphism -/

section Gen

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G)
  {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  {ρ : Representation k G M} {ρ' : Representation k G N}

theorem isEquivariant_symm (f : M ≃ₗ[k] N) (hf : IsEquivariant ρ ρ' f.toLinearMap) :
    IsEquivariant ρ' ρ f.symm.toLinearMap := fun g n => by
  apply f.injective
  have h := hf g (f.symm n)
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
  exact h.symm

theorem mapH1_leftInv {f : M →ₗ[k] N} (hf : IsEquivariant ρ ρ' f) {g : N →ₗ[k] M}
    (hg : IsEquivariant ρ' ρ g) (hgf : ∀ m, g (f m) = m) (x : H1 ρ Γ) :
    mapH1 Γ hg (mapH1 Γ hf x) = x := by
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ x
  have e : (⟨fun a => g (f ((c : Γ → M) a)), push_mem_Z1 Γ hg (push_mem_Z1 Γ hf c.2)⟩ : Z1 ρ Γ) = c :=
    Subtype.ext (funext fun a => hgf _)
  have e1 : mapH1 Γ hg (mapH1 Γ hf (Submodule.mkQ _ c)) = Submodule.mkQ _
      (⟨fun a => g (f ((c : Γ → M) a)), push_mem_Z1 Γ hg (push_mem_Z1 Γ hf c.2)⟩ : Z1 ρ Γ) := rfl
  rw [e1, e]

/-- `H¹` of an equivariant linear isomorphism. -/
def mapH1Equiv (f : M ≃ₗ[k] N) (hf : IsEquivariant ρ ρ' f.toLinearMap) : H1 ρ Γ ≃ₗ[k] H1 ρ' Γ :=
  LinearEquiv.ofLinear (mapH1 Γ hf) (mapH1 Γ (isEquivariant_symm f hf))
    (LinearMap.ext fun x => mapH1_leftInv Γ (isEquivariant_symm f hf) hf (fun n => by simp) x)
    (LinearMap.ext fun x => mapH1_leftInv Γ hf (isEquivariant_symm f hf) (fun m => by simp) x)

theorem mapH1Equiv_apply (f : M ≃ₗ[k] N) (hf : IsEquivariant ρ ρ' f.toLinearMap) (x : H1 ρ Γ) :
    mapH1Equiv Γ f hf x = mapH1 Γ hf x := rfl

end Gen

/-- A duality map that agrees, through isomorphisms on both sides, with a bijective one is bijective. -/
theorem bijective_of_equiv_pair {Λ : Type} [CommRing Λ] {A B A' B' : Type} [AddCommGroup A] [Module Λ A]
    [AddCommGroup B] [Module Λ B] [AddCommGroup A'] [Module Λ A'] [AddCommGroup B'] [Module Λ B']
    (α : A →ₗ[Λ] Module.Dual Λ B) (α' : A' →ₗ[Λ] Module.Dual Λ B') (a : A ≃ₗ[Λ] A') (b : B ≃ₗ[Λ] B')
    (h : ∀ x y, α x y = α' (a x) (b y)) (h' : Function.Bijective α') : Function.Bijective α := by
  have e : (α : A → Module.Dual Λ B) = (b.dualMap : Module.Dual Λ B' → Module.Dual Λ B) ∘ α' ∘ a :=
    funext fun x => LinearMap.ext fun y => by rw [h]; rfl
  rw [e]
  exact b.dualMap.bijective.comp (h'.comp a.bijective)

/-! ## `(f_* Λ)^∨(1) ≅ f_* (σ|K)` -/

section Dual

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)

include hK in
theorem pi_mem_mul (h : K) (z : G) : π ((h : G) * z) = π z := by
  rw [map_mul, (hK h).1 h.2, one_mul]

/-- The indicator of the coset `K x`. -/
def deltaP (x : G) : Representation.coindV K.subtype (Representation.trivial Λ K Λ) :=
  ⟨fun z => if π z = π x then 1 else 0, fun h z => by
    show (if π (K.subtype h * z) = π x then (1 : Λ) else 0) =
      Representation.trivial Λ K Λ h (if π z = π x then 1 else 0)
    rw [Representation.trivial_apply, Subgroup.coe_subtype, pi_mem_mul π K hK]⟩

theorem deltaP_apply (x z : G) :
    ((deltaP (Λ := Λ) π K hK x : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) : G → Λ) z =
      if π z = π x then 1 else 0 := rfl

theorem deltaP_eq {a b : G} (hab : π a = π b) : deltaP (Λ := Λ) π K hK a = deltaP π K hK b :=
  Subtype.ext (funext fun z => by rw [deltaP_apply, deltaP_apply, hab])

/-- `φ ↦ (x ↦ σ x (φ δ_x))`. -/
def psiP : (Representation.coindV K.subtype (Representation.trivial Λ K Λ) →ₗ[Λ] Λ) →ₗ[Λ]
    Representation.coindV K.subtype (σ.comp K.subtype) where
  toFun φ := ⟨fun x => σ x (φ (deltaP π K hK x)), fun h z => by
    show σ (K.subtype h * z) (φ (deltaP π K hK (K.subtype h * z))) =
      (σ.comp K.subtype) h (σ z (φ (deltaP π K hK z)))
    have hd : deltaP (Λ := Λ) π K hK (K.subtype h * z) = deltaP π K hK z :=
      deltaP_eq π K hK (by rw [Subgroup.coe_subtype, pi_mem_mul π K hK])
    rw [hd, map_mul, Module.End.mul_apply, MonoidHom.comp_apply]⟩
  map_add' φ ψ := Subtype.ext (funext fun x => by
    show σ x ((φ + ψ) (deltaP π K hK x)) = σ x (φ (deltaP π K hK x)) + σ x (ψ (deltaP π K hK x))
    rw [LinearMap.add_apply, map_add])
  map_smul' c φ := Subtype.ext (funext fun x => by
    show σ x ((c • φ) (deltaP π K hK x)) = c • σ x (φ (deltaP π K hK x))
    rw [LinearMap.smul_apply, map_smul])

theorem psiP_apply (φ : Representation.coindV K.subtype (Representation.trivial Λ K Λ) →ₗ[Λ] Λ) (x : G) :
    ((psiP σ π K hK φ : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) x =
      σ x (φ (deltaP π K hK x)) := rfl

/-- `F' ↦ (F ↦ Σ_y F (s y) * σ (s y)⁻¹ (F' (s y)))`. -/
def phiP : Representation.coindV K.subtype (σ.comp K.subtype) →ₗ[Λ]
    (Representation.coindV K.subtype (Representation.trivial Λ K Λ) →ₗ[Λ] Λ) :=
  LinearMap.mk₂ Λ (fun F' F => ∑ y : Gf, (F : G → Λ) (Function.surjInv hs y) *
      σ (Function.surjInv hs y)⁻¹ ((F' : G → Λ) (Function.surjInv hs y)))
    (fun a b F => by
      simp only [Submodule.coe_add, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (fun c a F => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
      ring)
    (fun F a b => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c F a => by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring)

theorem phiP_apply (F' : Representation.coindV K.subtype (σ.comp K.subtype))
    (F : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) :
    phiP σ π K hs F' F = ∑ y : Gf, (F : G → Λ) (Function.surjInv hs y) *
      σ (Function.surjInv hs y)⁻¹ ((F' : G → Λ) (Function.surjInv hs y)) := rfl

theorem sig_inv_sig (g : G) (v : Λ) : σ g⁻¹ (σ g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

include hK in
theorem coind_sig_inv (F' : Representation.coindV K.subtype (σ.comp K.subtype)) {x z : G} (hzx : π z = π x) :
    σ x (σ z⁻¹ ((F' : G → Λ) z)) = (F' : G → Λ) x := by
  have hk : z * x⁻¹ ∈ K := (hK _).2 (by rw [map_mul, map_inv, hzx, mul_inv_cancel])
  have h1 := F'.2 ⟨z * x⁻¹, hk⟩ x
  have hz : K.subtype ⟨z * x⁻¹, hk⟩ * x = z := by simp
  rw [hz] at h1
  have e : σ x (σ z⁻¹ (σ (K.subtype ⟨z * x⁻¹, hk⟩) ((F' : G → Λ) x))) =
      σ (x * z⁻¹ * K.subtype ⟨z * x⁻¹, hk⟩) ((F' : G → Λ) x) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h2 : x * z⁻¹ * K.subtype ⟨z * x⁻¹, hk⟩ = 1 := by simp [mul_assoc]
  rw [h1, MonoidHom.comp_apply, e, h2, map_one, Module.End.one_apply]

theorem psiP_phiP (F' : Representation.coindV K.subtype (σ.comp K.subtype)) :
    psiP σ π K hK (phiP σ π K hs F') = F' := Subtype.ext (funext fun x => by
  rw [psiP_apply, phiP_apply]
  simp only [deltaP_apply, Function.surjInv_eq hs, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  exact coind_sig_inv σ π K hK F' (Function.surjInv_eq hs _))

theorem sum_deltaP (F : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) :
    ∑ y : Gf, (F : G → Λ) (Function.surjInv hs y) • deltaP π K hK (Function.surjInv hs y) = F :=
  Subtype.ext (funext fun z => by
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      deltaP_apply, Function.surjInv_eq hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]
    exact coindV_triv_eq π K hK F (Function.surjInv_eq hs _))

theorem phiP_psiP (φ : Representation.coindV K.subtype (Representation.trivial Λ K Λ) →ₗ[Λ] Λ) :
    phiP σ π K hs (psiP σ π K hK φ) = φ := LinearMap.ext fun F => by
  rw [phiP_apply]
  simp only [psiP_apply, sig_inv_sig]
  conv_rhs => rw [← sum_deltaP π K hK hs F]
  rw [map_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [map_smul, smul_eq_mul]

/-- **`(f_* Λ)^∨(1) ≅ f_* (σ|K)`**, equivariantly (`psiP_equiv`). -/
def dualPushEquiv : (Representation.coindV K.subtype (Representation.trivial Λ K Λ) →ₗ[Λ] Λ) ≃ₗ[Λ]
    Representation.coindV K.subtype (σ.comp K.subtype) :=
  LinearEquiv.ofLinear (psiP σ π K hK) (phiP σ π K hs) (LinearMap.ext fun F' => psiP_phiP σ π K hK hs F')
    (LinearMap.ext fun φ => phiP_psiP σ π K hK hs φ)

theorem dualPushEquiv_apply (φ : Representation.coindV K.subtype (Representation.trivial Λ K Λ) →ₗ[Λ] Λ) :
    dualPushEquiv σ π K hK hs φ = psiP σ π K hK φ := rfl

/-! ## Shapiro on the dual side -/

variable (Γ : Subgroup G) (R : CosetReps Γ K)
  (hcov : ∀ x : G, ∃ h : K, ∃ γ : Γ, x = (h : G) * γ) (hKo : IsOpen (K : Set G))

end Dual

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Proj =====
section

/-!
# S4-CurveDuality O7d-P3a: the trace of a finite push-forward and the duality pairing

`π : G →* Gf` surjective onto a finite group, `K = ker π` (the cover `f : V → U`), `σ : Representation Λ G Λ`.
* `trP : f_*(σ|K) → σ`, `F ↦ Σ_y σ(s y)⁻¹ F(s y)` (`s` a section of `π`); equivariant (`trP_equiv`);
* `mulP : f_*Λ × f_*(σ|K) → f_*(σ|K)`, the pointwise product, equivariant (`mulP_equiv`);
  `phiP_eq_trP : phiP F' F = trP (F · F')`;
* `isOpen_pushS`, `mulHyp`: the cup-product hypotheses for `mulP`;
* `alphaM_eq_sum_trP`: for a primitive `U` of the `mulP`-cup product of `(c, psiP ∘ d)`, the duality pairing of
  `[(c, m)]` and `[d]` is `Σ_s trP (m_s · psiP (d t_s) - U t_s)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Proj

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)

include hK in
theorem hP_eq (F : Representation.coindV K.subtype (σ.comp K.subtype)) {a b : G} (hab : π a = π b) :
    σ a⁻¹ ((F : G → Λ) a) = σ b⁻¹ ((F : G → Λ) b) := by
  rw [← coind_sig_inv σ π K hK F hab, sig_inv_sig]

/-- The trace `f_*(σ|K) → σ`, `F ↦ Σ_y σ(s y)⁻¹ F(s y)`. -/
def trP : Representation.coindV K.subtype (σ.comp K.subtype) →ₗ[Λ] Λ where
  toFun F := ∑ y : Gf, σ (Function.surjInv hs y)⁻¹ ((F : G → Λ) (Function.surjInv hs y))
  map_add' F F' := by
    simp only [Submodule.coe_add, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

theorem trP_apply (F : Representation.coindV K.subtype (σ.comp K.subtype)) :
    trP σ π K hs F = ∑ y : Gf, σ (Function.surjInv hs y)⁻¹ ((F : G → Λ) (Function.surjInv hs y)) := rfl

/-- The pointwise product `f_*Λ × f_*(σ|K) → f_*(σ|K)`. -/
def mulP : Representation.coindV K.subtype (Representation.trivial Λ K Λ) →ₗ[Λ]
    Representation.coindV K.subtype (σ.comp K.subtype) →ₗ[Λ]
      Representation.coindV K.subtype (σ.comp K.subtype) :=
  LinearMap.mk₂ Λ (fun F F' => ⟨fun x => (F : G → Λ) x * (F' : G → Λ) x, fun h z => by
      show (F : G → Λ) (K.subtype h * z) * (F' : G → Λ) (K.subtype h * z) =
        (σ.comp K.subtype) h ((F : G → Λ) z * (F' : G → Λ) z)
      rw [F.2 h z, F'.2 h z, Representation.trivial_apply]
      exact (map_smul ((σ.comp K.subtype) h) ((F : G → Λ) z) ((F' : G → Λ) z)).symm⟩)
    (fun a b F' => Subtype.ext (funext fun x => by
      show ((a : G → Λ) x + (b : G → Λ) x) * (F' : G → Λ) x =
        (a : G → Λ) x * (F' : G → Λ) x + (b : G → Λ) x * (F' : G → Λ) x
      ring))
    (fun c a F' => Subtype.ext (funext fun x => by
      show (c * (a : G → Λ) x) * (F' : G → Λ) x = c * ((a : G → Λ) x * (F' : G → Λ) x)
      ring))
    (fun F a b => Subtype.ext (funext fun x => by
      show (F : G → Λ) x * ((a : G → Λ) x + (b : G → Λ) x) =
        (F : G → Λ) x * (a : G → Λ) x + (F : G → Λ) x * (b : G → Λ) x
      ring))
    (fun c F a => Subtype.ext (funext fun x => by
      show (F : G → Λ) x * (c * (a : G → Λ) x) = c * ((F : G → Λ) x * (a : G → Λ) x)
      ring))

theorem mulP_apply (F : Representation.coindV K.subtype (Representation.trivial Λ K Λ))
    (F' : Representation.coindV K.subtype (σ.comp K.subtype)) (x : G) :
    ((mulP σ K F F' : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) x =
      (F : G → Λ) x * (F' : G → Λ) x := rfl

theorem phiP_eq_trP (F' : Representation.coindV K.subtype (σ.comp K.subtype))
    (F : Representation.coindV K.subtype (Representation.trivial Λ K Λ)) :
    phiP σ π K hs F' F = trP σ π K hs (mulP σ K F F') := by
  rw [phiP_apply, trP_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact (map_smul (σ (Function.surjInv hs y)⁻¹) ((F : G → Λ) (Function.surjInv hs y))
    ((F' : G → Λ) (Function.surjInv hs y))).symm

end Proj

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_Trans =====
section

/-!
# S4-CurveDuality O7d-P3b T1: local traces are weighted `V`-level residues

`π : G →* Gf` finite quotient, `K = ker π`, `σ` a character of `G` trivial on `Γ`. For
`e ∈ Z¹(Γ ⊓ I s, f_*(σ|K))` put `E(g)(y) = σ(r)⁻¹ e(g)(r)` (`π r = y`, `EP`), so `trP (e g) = Σ_y E(g)(y)`.
* `sum_eq_sum_quot_zpowers`: `Σ_y f y = Σ_{q ∈ Gf ⧸ ⟨a⟩} Σ_{j < ord a} f (q.out a^j)`;
* `EP_mul`, `EP_pow`, `trP_eq_sum_quot`: `trP (e t) = Σ_q E(t^m)(q.out)`, `m = ord (π t)`;
* `Z1_conj_apply`: `e(g k g⁻¹)(x) = e(k)(x g)` for `k ∈ K`;
* `locZ`, `locZ_mem`: `Z'(h) = e(x⁻¹ h x)(x)` is a cocycle on `B ≤ K`;
* `eq_mul_of_constData`: under `V`'s `ConstData` every such cocycle is `Z'(t'_u) · ε_u`;
* **`trP_local`**, **`sum_trP_eq_lam`** (T1): weights `λ : T → Λ`, independent of `e`, with
  `Σ_s trP (e_s t_s) = Σ_u λ_u · e_{π u}(x_u⁻¹ t'_u x_u)(x_u)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Orbit

variable {Gf : Type} [Group Gf] [Fintype Gf] {M : Type} [AddCommMonoid M]

theorem sum_eq_sum_quot_zpowers (a : Gf) (f : Gf → M) :
    ∑ y, f y = ∑ q : Gf ⧸ Subgroup.zpowers a, ∑ j ∈ Finset.range (orderOf a), f (q.out * a ^ j) := by
  have hx : IsOfFinOrder a := isOfFinOrder_of_finite a
  have hbij : Function.Bijective
      (fun p : (Gf ⧸ Subgroup.zpowers a) × Subgroup.zpowers a => p.1.out * (p.2 : Gf)) := by
    constructor
    · rintro ⟨q, h⟩ ⟨q', h'⟩ e
      have e' : q.out * (h : Gf) = q'.out * (h' : Gf) := e
      have hq : q = q' := by
        have := congrArg (QuotientGroup.mk (s := Subgroup.zpowers a)) e'
        rwa [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.mk_mul_of_mem _ h'.2,
          QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      subst hq
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel e'))
    · intro y
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.zpowers a) y
      refine ⟨((y : Gf ⧸ Subgroup.zpowers a), h⁻¹), ?_⟩
      show (QuotientGroup.mk y : Gf ⧸ Subgroup.zpowers a).out * ((h⁻¹ : Subgroup.zpowers a) : Gf) = y
      rw [hh, Subgroup.coe_inv, mul_inv_cancel_right]
  refine (Fintype.sum_bijective _ hbij (fun p => f (p.1.out * (p.2 : Gf))) f (fun _ => rfl)).symm.trans ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  refine (Fintype.sum_equiv (finEquivZPowers hx) (fun j => f (q.out * a ^ (j : ℕ)))
    (fun h => f (q.out * (h : Gf))) (fun j => rfl)).symm.trans ?_
  exact Fin.sum_univ_eq_sum_range (fun j => f (q.out * a ^ j)) (orderOf a)

end Orbit

section Trans

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf]
  (π : G →* Gf) (K : Subgroup G) (hK : ∀ g, g ∈ K ↔ π g = 1) (hs : Function.Surjective π)

/-- `E_F(y) = σ(r)⁻¹ F(r)` at the chosen preimage `r` of `y`. -/
def EP (F : Representation.coindV K.subtype (σ.comp K.subtype)) (y : Gf) : Λ :=
  σ (Function.surjInv hs y)⁻¹ ((F : G → Λ) (Function.surjInv hs y))

theorem trP_eq_sum_EP (F : Representation.coindV K.subtype (σ.comp K.subtype)) :
    trP σ π K hs F = ∑ y, EP σ π K hs F y := rfl

include hK in
theorem EP_eq (F : Representation.coindV K.subtype (σ.comp K.subtype)) {r : G} {y : Gf} (hr : π r = y) :
    EP σ π K hs F y = σ r⁻¹ ((F : G → Λ) r) :=
  hP_eq σ π K hK F ((Function.surjInv_eq hs y).trans hr.symm)

theorem EP_zero (y : Gf) : EP σ π K hs 0 y = 0 := by
  simp [EP]

open Classical in
/-- `f` extended by zero from `A` to `G`. -/
def extZ {A : Subgroup G} (f : A → Representation.coindV K.subtype (σ.comp K.subtype)) (x : G) :
    Representation.coindV K.subtype (σ.comp K.subtype) :=
  if h : x ∈ A then f ⟨x, h⟩ else 0

theorem extZ_of_mem {A : Subgroup G} (f : A → Representation.coindV K.subtype (σ.comp K.subtype)) {x : G}
    (hx : x ∈ A) : extZ σ K f x = f ⟨x, hx⟩ := dif_pos hx

open Classical in
/-- `f` extended by zero from `B` to `K`. -/
def extL {B : Subgroup K} (f : B → Λ) (k : K) : Λ := if h : k ∈ B then f ⟨k, h⟩ else 0

theorem extL_of_mem {B : Subgroup K} (f : B → Λ) {k : K} (hk : k ∈ B) : extL K f k = f ⟨k, hk⟩ :=
  dif_pos hk

/-- `Z'(h) = f(x⁻¹ h x)(x)` on `B ≤ K` with `x⁻¹ B x ⊆ A`. -/
def locZ {A : Subgroup G} (x : G) (B : Subgroup K) (hB : ∀ h : B, x⁻¹ * ((h : K) : G) * x ∈ A)
    (f : A → Representation.coindV K.subtype (σ.comp K.subtype)) (h : B) : Λ :=
  ((f ⟨x⁻¹ * ((h : K) : G) * x, hB h⟩ : Representation.coindV K.subtype (σ.comp K.subtype)) : G → Λ) x

section Coc

variable {A : Subgroup G} (hA : ∀ (g : A) (v : Λ), σ g v = v)
  {e : A → Representation.coindV K.subtype (σ.comp K.subtype)} (he : e ∈ Z1 (pushRep K (σ.comp K.subtype)) A)

end Coc

section Local

variable {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {T : Type} [Fintype T]
  {J : T → Subgroup K} {πT : T → S} {xT : T → Γ}

variable {t' : (u : T) → ↥(geoU Γ K ⊓ J u)}

end Local

end Trans

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

include hK in
theorem normal_of_hK : K.Normal := ⟨fun n hn g => (hK _).2 (by
  rw [map_mul, map_mul, map_inv, (hK n).1 hn, mul_one, mul_inv_cancel])⟩

include hK in
/-- An element of `f_*(σ|K)` is determined by its values on the section `surjInv hs`. -/
theorem coindV_ext_sec {F F' : Representation.coindV K.subtype (σ.comp K.subtype)}
    (h : ∀ y, (F : G → Λ) (Function.surjInv hs y) = (F' : G → Λ) (Function.surjInv hs y)) : F = F' := by
  refine Subtype.ext (funext fun x => ?_)
  have hx : π (Function.surjInv hs (π x)) = π x := Function.surjInv_eq hs (π x)
  rw [← coind_sig_inv σ π K hK F hx, ← coind_sig_inv σ π K hK F' hx, h]

include hK hs in
theorem coindV_finite [Finite Λ] : Finite (Representation.coindV K.subtype (σ.comp K.subtype)) :=
  Finite.of_injective (fun F : Representation.coindV K.subtype (σ.comp K.subtype) =>
    fun y : Gf => (F : G → Λ) (Function.surjInv hs y))
    fun _ _ h => coindV_ext_sec σ π K hK hs fun y => congrFun h y

include hK in
/-- `trP` is onto: `F(x) = σ(x) v` on `K` and `0` off `K` has trace `v`. -/
theorem trP_surjective : Function.Surjective (trP σ π K hs) := by
  intro v
  refine ⟨⟨fun x => σ x (if π x = 1 then v else 0), fun h z => ?_⟩, ?_⟩
  · have h1 : π (K.subtype h) = 1 := (hK _).1 h.2
    have hz : π (K.subtype h * z) = π z := by rw [map_mul, h1, one_mul]
    show σ (K.subtype h * z) (if π (K.subtype h * z) = 1 then v else 0) =
      (σ.comp K.subtype) h (σ z (if π z = 1 then v else 0))
    rw [hz, map_mul, Module.End.mul_apply, MonoidHom.comp_apply]
  · show ∑ y : Gf, σ (Function.surjInv hs y)⁻¹
        (σ (Function.surjInv hs y) (if π (Function.surjInv hs y) = 1 then v else 0)) = v
    simp only [sig_inv_sig, Function.surjInv_eq hs]
    simp

/-- `Σ_u λ_u X_u = c Σ_u X_u` when all `λ_u = c`. -/
theorem sum_mul_const {T : Type} [Fintype T] (lam X : T → Λ) (c : Λ) (h : ∀ u, lam u = c) :
    ∑ u, lam u * X u = c * ∑ u, X u := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [h u]

section Local

variable {Γ : Subgroup G} {S : Type} {I : S → Subgroup G} {T : Type} [Fintype T]
  {J : T → Subgroup K} {πT : T → S} {xT : T → Γ} {t' : (u : T) → ↥(geoU Γ K ⊓ J u)}

end Local

end Lam

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_AmbCup =====
section

/-!
# S4-CurveDuality O7d-P1d (T2): the cup product, `ConstData` and the duality maps under a change of ambient group

For `e : Δ₁ ≃ₜ* Δ₂` intertwining the representations (`Intw`) and the boundary subgroups (`IntwI`):
* `h2van_comp`: `H²(Δ₂, σ₂) = 0 → H²(Δ₁, σ₁) = 0`; `Intw.linHom`: `e` intertwines the internal Homs;
* `cupPair_tr`: `h2kTr (x ∪ y) = h1cTr x ∪ h1Tr y`, hence `pair_tr` for any functional on the cone `H²`;
* `constData_tr`, `h2kEquiv_tr`, `constPair_tr`, `constPair_bijective_tr`;
* `alphaM_tr`, `alphaM_bijective_tr`: the duality map `α` is bijective at `Δ₂` ⇒ at `Δ₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section AmbCup

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} {e : Δ₁ ≃ₜ* Δ₂}

theorem Intw.linHom {M L : Type} [AddCommGroup M] [Module k M] [AddCommGroup L] [Module k L]
    {ρ₁ : Representation k G₁ M} {ρ₂ : Representation k G₂ M} {σ₁ : Representation k G₁ L}
    {σ₂ : Representation k G₂ L} (h : Intw ρ₁ ρ₂ e) (hσ : Intw σ₁ σ₂ e) :
    Intw (ρ₁.linHom σ₁) (ρ₂.linHom σ₂) e := fun g => by
  have hi : ρ₁ (g : G₁)⁻¹ = ρ₂ ((e g : Δ₂) : G₂)⁻¹ := by
    rw [← Subgroup.coe_inv, h g⁻¹, map_inv, Subgroup.coe_inv]
  ext φ m
  simp only [Representation.linHom_apply, LinearMap.comp_apply]
  rw [hi, hσ g]

variable {M M' L : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] [AddCommGroup L]
  [Module k L] {ρ₁ : Representation k G₁ M} {ρ₂ : Representation k G₂ M}
  {ρ₁' : Representation k G₁ M'} {ρ₂' : Representation k G₂ M'}
  {σ₁ : Representation k G₁ L} {σ₂ : Representation k G₂ L} {β : M →ₗ[k] M' →ₗ[k] L}

variable {S : Type} {I₁ : S → Subgroup G₁} {I₂ : S → Subgroup G₂}

end AmbCup

/-! ## The duality map `α` -/

section Alpha

variable {Λ : Type} [CommRing Λ] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} {e : Δ₁ ≃ₜ* Δ₂} {S : Type} {I₁ : S → Subgroup G₁}
  {I₂ : S → Subgroup G₂} {σ₁ : Representation Λ G₁ Λ} {σ₂ : Representation Λ G₂ Λ}
  {hσ₁ : IsOpen (σ₁.ker : Set G₁)} {hσ₂ : IsOpen (σ₂.ker : Set G₂)}
  {M : Type} [AddCommGroup M] [Module Λ M]

end Alpha

/-! ## Constant coefficients -/

section Const

variable {k : Type} [CommRing k] {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁]
  [TopologicalSpace G₂] [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
  {Δ₁ : Subgroup G₁} {Δ₂ : Subgroup G₂} {e : Δ₁ ≃ₜ* Δ₂} {S : Type} {I₁ : S → Subgroup G₁}
  {I₂ : S → Subgroup G₂} {σ₁ : Representation k G₁ k} {σ₂ : Representation k G₂ k}

theorem intw_trivial : Intw (Representation.trivial k G₁ k) (Representation.trivial k G₂ k) e :=
  fun _ => rfl

theorem infTr_symm_eq (hI : IntwI I₁ I₂ e) (s : S) (g : ↥(Δ₂ ⊓ I₂ s)) :
    infTr hI.symm s g = (infTr hI s).symm g := rfl

variable [Fintype S]

variable [Nonempty S]

end Const

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_AmbRes =====
section

/-!
# S4-CurveDuality O7d-P1d (T4): restricting the cover data to a subgroup `H ⊇ Γ, K`

For `Γ, K ≤ H ≤ G` the groups `Γ₁ = Γ.subgroupOf H`, `K₁ = K.subgroupOf H` and `I₁ s = (I s).subgroupOf H` carry
the same data as `Γ, K, I`:
* `eSub : Γ.subgroupOf H ≃ₜ* Γ` and `eGeo : geoU Γ₁ K₁ ≃ₜ* geoU Γ K`, intertwining the restricted representations
  (`intw_sub`, `intw_geo`) and boundary subgroups (`intwI_sub`, `intwI_geo` with `J₁ t = (J t).comap (kMap K)`);
* `inertiaLift_sub`, `dCover_sub`, `dDisj_sub`: the Shapiro data transported to `H`;
* `inf_subgroupOf'`: `(A ⊓ B).subgroupOf H = A.subgroupOf H ⊓ B.subgroupOf H`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Res

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}

theorem inf_subgroupOf' (A B : Subgroup G) : (A ⊓ B).subgroupOf H = A.subgroupOf H ⊓ B.subgroupOf H :=
  Subgroup.ext fun _ => Iff.rfl

/-- `Γ.subgroupOf H ≃ₜ* Γ` for `Γ ≤ H`. -/
def eSub {Γ : Subgroup G} (hΓ : Γ ≤ H) : Γ.subgroupOf H ≃ₜ* Γ where
  toFun := ofSubOf
  invFun := toSubOf hΓ
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_ofSubOf
  continuous_invFun := continuous_toSubOf hΓ

theorem eSub_apply {Γ : Subgroup G} (hΓ : Γ ≤ H) (a : Γ.subgroupOf H) : eSub hΓ a = ofSubOf a := rfl

theorem eSub_symm_apply {Γ : Subgroup G} (hΓ : Γ ≤ H) (a : Γ) : (eSub hΓ).symm a = toSubOf hΓ a := rfl

/-- `K.subgroupOf H → K`. -/
def kMap (K : Subgroup G) : K.subgroupOf H →* K where
  toFun x := ⟨((x : H) : G), x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]

theorem intw_sub (σ : Representation k G M) {Γ : Subgroup G} (hΓ : Γ ≤ H) :
    Intw (σ.comp H.subtype) σ (eSub hΓ) := fun _ => rfl

theorem intwI_sub {S : Type} (I : S → Subgroup G) {Γ : Subgroup G} (hΓ : Γ ≤ H) :
    IntwI (fun s => (I s).subgroupOf H) I (eSub hΓ) := fun _ _ => Iff.rfl

variable {S T : Type} {Γ K : Subgroup G} {I : S → Subgroup G} {J : T → Subgroup K} {πT : T → S} {xT : T → Γ}

end Res

end

end CupDuality
end RamanujanPetersson


end

-- ===== S4.Def_RP_LisseDuality_AmbAsm =====
section

/-!
# S4-CurveDuality O7d-P1d (T5): lisse duality without connectedness

For `π : G →* Gf` onto a finite group with open kernel and residue data `RD : ResDat π Γ I N T`, the cover `V`
need not be connected over `Ū`: replace the ambient group `G` by `H₁ = π⁻¹(π Γ) = ker π · Γ` (`hOne`), which is
open of finite index, and `π` by `π₁ : H₁ ↠ π Γ` (`piOne`). Over `H₁` the cover is connected (`cov_hOne`), so the
connected chain (`alpha_bijective_of_regular` ← `alpha_coindF_of_push` ← `alphaM_push_bijective`) applies to the
data restricted to `H₁` (`h2All_subgroupOf`, `constData_tr'`, `inertiaLift_sub`, ...), and `alphaM_bijective_tr`
carries bijectivity back to `G`. The parabolic hypothesis `hB` is the same as in `lisse_bijective_connected`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

section Hone

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Gf : Type} [Group Gf]
  (π : G →* Gf) (Γ : Subgroup G)

/-- `H₁ = π⁻¹(π Γ) = ker π · Γ`. -/
def hOne : Subgroup G := (Γ.map π).comap π

theorem le_hOne : Γ ≤ hOne π Γ := fun _ hg => Subgroup.mem_map_of_mem π hg

theorem ker_le_hOne : π.ker ≤ hOne π Γ := fun g hg => by
  show π g ∈ Γ.map π
  rw [MonoidHom.mem_ker.1 hg]
  exact Subgroup.one_mem _

/-- `π₁ : H₁ → π Γ`. -/
def piOne : hOne π Γ →* Γ.map π := (π.comp (hOne π Γ).subtype).codRestrict (Γ.map π) fun x => x.2

theorem piOne_coe (x : hOne π Γ) : (piOne π Γ x : Gf) = π x := rfl

theorem piOne_surjective : Function.Surjective (piOne π Γ) := by
  rintro ⟨p, hp⟩
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hp
  exact ⟨⟨γ, le_hOne π Γ hγ⟩, rfl⟩

theorem mem_kOne_iff (g : hOne π Γ) : g ∈ π.ker.subgroupOf (hOne π Γ) ↔ piOne π Γ g = 1 :=
  Subgroup.mem_subgroupOf.trans
    (MonoidHom.mem_ker.trans ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)

theorem isOpen_hOne (hπ : IsOpen (π.ker : Set G)) : IsOpen (hOne π Γ : Set G) :=
  Subgroup.isOpen_mono (ker_le_hOne π Γ) hπ

theorem isOpen_kOne (hπ : IsOpen (π.ker : Set G)) :
    IsOpen ((π.ker.subgroupOf (hOne π Γ) : Subgroup (hOne π Γ)) : Set (hOne π Γ)) :=
  hπ.preimage continuous_subtype_val

theorem isOpen_ker_piOne (hπ : IsOpen (π.ker : Set G)) :
    IsOpen ((piOne π Γ).ker : Set (hOne π Γ)) := by
  have e : ((piOne π Γ).ker : Set (hOne π Γ)) = ((π.ker.subgroupOf (hOne π Γ) : Subgroup (hOne π Γ)) :
      Set (hOne π Γ)) :=
    Set.ext fun g => (mem_kOne_iff π Γ g).symm
  rw [e]
  exact isOpen_kOne π Γ hπ

theorem finite_quot_hOne [Finite Gf] : Finite (G ⧸ hOne π Γ) := by
  have : (hOne π Γ).FiniteIndex := Subgroup.finiteIndex_of_le (ker_le_hOne π Γ)
  infer_instance

/-- Over `H₁` the cover is connected: `H₁ = K₁ · Γ₁`. -/
theorem cov_hOne (x : hOne π Γ) :
    ∃ h : π.ker.subgroupOf (hOne π Γ), ∃ γ : Γ.subgroupOf (hOne π Γ), x = (h : hOne π Γ) * γ := by
  have hx : π x ∈ Γ.map π := x.2
  obtain ⟨γ, hγ, hπγ⟩ := Subgroup.mem_map.1 hx
  refine ⟨⟨x * ⟨γ, le_hOne π Γ hγ⟩⁻¹, ?_⟩, ⟨⟨γ, le_hOne π Γ hγ⟩, hγ⟩, (inv_mul_cancel_right x _).symm⟩
  show π ((x : G) * γ⁻¹) = 1
  rw [map_mul, map_inv, hπγ, mul_inv_cancel]

end Hone

section Lisse

variable {Λ : Type} [CommRing Λ] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (σ : Representation Λ G Λ) {Gf : Type} [Group Gf] [Fintype Gf] [DecidableEq Gf] (π : G →* Gf)
  {Γ : Subgroup G} {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)} {N : ℕ} {T : Type} [Fintype T]
  [Fintype (Γ.map π)] [∀ s, Fintype ((Γ ⊓ I s).map π)]

end Lisse

end

end CupDuality
end RamanujanPetersson


end


