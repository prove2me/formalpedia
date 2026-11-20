-- Prove2me | Definitions.Def_RPLib_F2_040
-- name    : RPLib_F2_040
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T17:35:28.475171+00:00
-- url     : https://prove2.me/theorems/08a27798-ed69-47ea-b3ec-af2a5e4bd3f9
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 040 of 70
-- statement:
--   File 040 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_InstR`: S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l`
--   * `S4.Def_RP_JacLaw_InstA`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`
--   * `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
--   * `S4.Def_RP_JacLaw`: Weil's birational group law on `Sym^g X` (unit S4-JacLaw), umbrella
--   * `S4.Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
--   * `S4.Def_RP_CoreB_Zeta`: Core B, O4: the zeta link
--   * `S4.Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_038

/-!
# Ramanujan-Petersson curve library (flat edition), file 040 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_InstR`: S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l`
* `S4.Def_RP_JacLaw_InstA`: S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`
* `S4.Def_RP_JacLaw_GenWit`: S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data
* `S4.Def_RP_JacLaw`: Weil's birational group law on `Sym^g X` (unit S4-JacLaw), umbrella
* `S4.Def_RP_JacComplete_PicLw`: The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)
* `S4.Def_RP_CoreB_Zeta`: Core B, O4: the zeta link
* `S4.Def_RP_Cone_ResAsm2`: S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstR =====
section

/-!
# S4-JacLaw, file O10e (part R): the `PreChunk` relations `rel_r_m rel_m_r rel_l_m rel_m_l`

For points of `D(ωm)`, `D(ωr)`, `D(ωl)` (through `law_*` at `x ∘ nestK`).
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Inst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace LawData

variable (L : LawData K F)

section Rel

variable (x : Localization.Away L.ωm →ₐ[K] K) (xr : Localization.Away L.ωr →ₐ[K] K)
  (xl : Localization.Away L.ωl →ₐ[K] K)

theorem rel_m_l (hR : pR x = pR xl) (hL : pL x = xl.comp L.lal) : x.comp L.μm = pL xl :=
  (L.m_nest x).trans <| (L.law_m_l (x.comp (nestK (K := K) L.mU)) (xl.comp (nestK (K := K) L.lU))
    ((L.mB_L x).trans (hL.trans (L.l_nest xl))) ((L.mB_R x).trans (hR.trans (L.lB_R xl).symm))).trans (L.lB_L xl)

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_InstA =====
section

/-!
# S4-JacLaw, file O10e (part A): associativity at points of `D(ωm)`

`b_LL b_LR b_RR b_Lmu b_Rmu` (base identities through the nest) and `rel_assoc`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Inst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace LawData

variable (L : LawData K F)

section Rel

variable (x : Localization.Away L.ωm →ₐ[K] K) (xr : Localization.Away L.ωr →ₐ[K] K)
  (xl : Localization.Away L.ωl →ₐ[K] K)

set_option maxHeartbeats 400000 in
theorem rel_assoc (x₁ x₂ x₃ x₄ : Localization.Away L.ωm →ₐ[K] K) (e₁ : pR x₁ = pL x₂)
    (e₂ : pL x₃ = x₁.comp L.μm) (e₃ : pR x₃ = pR x₂) (e₄ : pL x₄ = pL x₁) (e₅ : pR x₄ = x₂.comp L.μm) :
    x₃.comp L.μm = x₄.comp L.μm :=
  (L.m_nest x₃).trans <| (L.law_assoc (x₁.comp (nestK (K := K) L.mU)) (x₂.comp (nestK (K := K) L.mU))
    (x₃.comp (nestK (K := K) L.mU)) (x₄.comp (nestK (K := K) L.mU)) (L.b_LL e₄) (L.b_LR e₁.symm)
    (L.b_RR e₃) (L.b_Lmu e₂) (L.b_Rmu e₅)).trans (L.m_nest x₄).symm

end Rel

end LawData

end Inst

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw_GenWit =====
section

/-!
# S4-JacLaw, file O9h (G5 GenWit): a witness point for the law data

* `wit_mu_gen`: the point set of `m(a,b)` at a point of the `mOut` target, from the two `m`-roles (any `T`).
* `pair_iL`, `pair_iR`; `wit_m`, `wit_mu`, `wit_r`, `wit_l`: the four steps at `T0 = S_g ⊗ S_g`.
* **`exists_lawData_wit`**: `∃ L : LawData K F, ∃ x, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0`
  (the hypothesis `hw` of `LawData.toPre` / `LawData.chunk`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section GenWit

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

section Gen

variable {T : Type u} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]

end Gen

variable (L : LawData K F) {a b E c : Finset (Places.Rfin K F →ₐ[K] K)}

/-- **The witness at a configuration.** -/
theorem wit_all {ta tb : Fin (genusFK K F) → (Places.Rfin K F →ₐ[K] K)}
    (ea : ptSet (symPt ta) = a) (eb : ptSet (symPt tb) = b)
    (hm3 : RoleOn L.Dm3 (a ∪ b ∪ Finset.univ.image L.c0) E) (hm2 : RoleOn L.Dm2 (E ∪ Finset.univ.image L.c1) c)
    (hr2 : RoleOn L.Dr2 (c ∪ Finset.univ.image L.c1) E) (hl2 : RoleOn L.Dl2 (c ∪ Finset.univ.image L.c1) E)
    (hr3 : RoleOn L.Dr3 (a ∪ E ∪ Finset.univ.image L.c0) b) (hl3 : RoleOn L.Dl3 (b ∪ E ∪ Finset.univ.image L.c0) a) :
    L.HasWit := by
  obtain ⟨x, hx0, hxL, hxR⟩ := exists_over_pair (wit_m L ea eb hm3 hm2)
  have hw := wit_mu L ea eb hm3 hm2 x hxL hxR
  have p1 : x (phiS L.μm L.ωr) ≠ 0 := by
    have e : x (phiS L.μm L.ωr) = (x.comp (phiS L.μm)) L.ωr := rfl
    rw [e, phiS_pt, hxL]
    exact wit_r L ea hr2 hr3 _ hw
  have p2 : x (psiS L.μm L.ωl) ≠ 0 := by
    have e : x (psiS L.μm L.ωl) = (x.comp (psiS L.μm)) L.ωl := rfl
    rw [e, psiS_pt, hxR]
    exact wit_l L eb hl2 hl3 _ hw
  exact Exists.intro x ⟨p1, p2⟩

/-- **The witness**: law data and a point of `D(ωm)` where `Φ` and `Ψ` land in `D(ωr)`, `D(ωl)`
(`(exists_lawData_wit).choose_spec.out` is the `hw` of `LawData.chunk`). -/
theorem exists_lawData_wit : ∃ L : LawData K F, L.HasWit := by
  obtain ⟨L, ta, tb, a, b, E, c, ea, eb, hm3, hm2, hr2, hl2, hr3, hl3⟩ := exists_cfg (K := K) (F := F)
  exact ⟨L, wit_all L ea eb hm3 hm2 hr2 hl2 hr3 hl3⟩

end GenWit

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacLaw =====
section

/-!
# Weil's birational group law on `Sym^g X` (unit S4-JacLaw), umbrella

Milne III.7.1-7.2 (lemmas L15-L16 of `S4_COREB_ROUTE.md`). `S = S_g = SymRing K (Rfin K F) g` is the coordinate
ring of (an affine open of) `Sym^g X`.
* L15: `exists_lawData_wit` (files `Gen*`) produces law data `lawData K F`: the rule `(D, D') ↦ E` with
  `D + D' - g P0 ~ E` as a rational map `m` (`μm` on `D(ωm) ⊆ Sym^g × Sym^g`), and `r` (`ρr`) for the inverse,
  each well defined and unique on a dense open (files `Nu`, `Uniq`, `Step`, `Law`).
* L16: `lawPre K F : PreChunk K S` packages `m`, `r`, `l` with associativity and the inverse relations
  (`InstL*`, `InstR`, `InstA`, `Assoc`); `lawChunk K F` is the resulting strict group chunk on the dense open
  `D(u0) = Spec S[1/u0]` (`Shrink*`, `Sch`), stated in the form `StrictChunk (X ↘ Spec k)` used by S4-JacChunkB.
* The instances S4-JacChunkB needs on `X = Spec S[1/u0]`: reduced, irreducible, separated, locally of finite type,
  geometrically reduced; `dense_basicOpen_u0`: `D(u0)` is dense in `Spec S`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk

universe u

section Umb

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The law data of Weil's birational group law (L15), chosen by the genericity argument. -/
noncomputable def lawData : LawData K F := (exists_lawData_wit (K := K) (F := F)).choose

theorem lawData_hasWit : (lawData K F).HasWit := (exists_lawData_wit (K := K) (F := F)).choose_spec

end Umb

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacComplete_PicLw =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicLw` (L20: Weil's law in `Pic`)

* `cls_mOut`: `[m(a,b)] = [a] + [b] - [Θ]` (`Θ = ThetaD = Hn3 - Hn2 - c0 + c1`), from `div_sec3`, `div_sec2`;
  `card_mBase_L`: inputs of the law are reduced of degree `g`.
* `psiL L y = [supp y] - [Θ]`: additive for the law (`lawData_add`) and (`lawData_rigid` is in `PicLr`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory Limits AlgebraicGeometry
open RamanujanPetersson.JacChunk RamanujanPetersson.JacLaw

universe u

section Pt

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {T : Type*} [CommRing T] [Algebra K T] [IsReduced T] [Algebra.FiniteType K T]
  {r3 r2 : ℕ} (D3 : NuData K F (genusFK K F + genusFK K F + r3)) (D2 : NuData K F (genusFK K F + r2))
  (c0 : Fin r3 → (Places.Rfin K F →ₐ[K] K)) (c1 : Fin r2 → (Places.Rfin K F →ₐ[K] K))

end Pt

section Law

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (L : LawData K F)

set_option maxHeartbeats 1000000 in
theorem lawData_add (x : Localization.Away L.ωm →ₐ[K] K) :
    psiL L (x.comp L.μm) = psiL L (pL x) + psiL L (pR x) := by
  have h : clsK K F (Zdiv (ptSet ((x.comp (nestK (K := K) L.mU)).comp L.mOutL))) =
      clsK K F (Zdiv (ptSet ((L.mB (x.comp (nestK (K := K) L.mU))).comp (iL K F))) +
        Zdiv (ptSet ((L.mB (x.comp (nestK (K := K) L.mU))).comp (iR K F))) - ThetaD L.Dm3 L.Dm2 L.c0 L.c1) :=
    cls_mOut (T := T0 K F) L.Dm3 L.Dm2 L.c0 L.c1 (iL K F) (iR K F) (x.comp (nestK (K := K) L.mU))
  rw [L.mB_L x, L.mB_R x, ← L.m_nest x] at h
  rw [psiL, psiL, psiL, h, clsK_sub, clsK_add]
  abel

end Law

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_CoreB_Zeta =====
section

/-!
# Core B, O4: the zeta link

* `multiset_eq_of_powerSum_le`: `#c ≤ #ω`, `0 ∉ ω` and equal power sums force `c = ω`.
* `coe_piBar0_pow`, `card_ker_one_sub_X_pow_piBar0`: `ker (1 - π^m) = Pic⁰(X̄)^(π^m)`.
* `piBar0_injective`: the Frobenius is injective on `Pic⁰(X̄)`.
* `zeta_link D`: for degree data `D` on `ℤ[π]`, `gD = g` and `χ_D = P0` with `P0 ∈ ℤ[X]` the zeta polynomial
  `Π (X - ω_i)` (for any `c` with `#c ≤ 2g` and the point-count formula).
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.CoreB

open RamanujanPetersson.JacAlg RamanujanPetersson.JacComplete RamanujanPetersson.JacFrob RamanujanPetersson.RR
open RamanujanPetersson.PicDescent RamanujanPetersson.Places

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω]
variable (hk : constField Fq F = ⊥)

/-- **O4.** Degree data on `ℤ[π]` has genus `g` and characteristic polynomial the integral zeta polynomial. -/
theorem zeta_link {gD : ℕ} (D : DegreeData (piBar0 Fq F Ω hk) gD (ringChar Fq)) :
    gD = genusF Fq F ∧ ∀ c : Multiset ℂ, Multiset.card c ≤ 2 * genusF Fq F →
      (∀ m : ℕ, 1 ≤ m → (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) →
      ∃ P0 : ℤ[X], P0.map (Int.castRingHom ℂ) = (c.map fun r => X - C r).prod ∧
        D.charPoly = P0.map (Int.castRingHom ℚ) := by
  obtain ⟨ω, hcard, hnorm, -, hN, h0, -, -, P0, -, hP0⟩ := CP4a.zeta_RH_FE hk
  have hU : ∀ c : Multiset ℂ, Multiset.card c ≤ 2 * genusF Fq F →
      (∀ m : ℕ, 1 ≤ m → (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) →
      c = ω := fun c hc hcN => multiset_eq_of_powerSum_le (hcard ▸ hc) h0 fun m hm =>
    sub_right_injective ((hcN m hm).symm.trans (hN m hm))
  obtain ⟨c', hc', -, hc'N, hc'h⟩ := classNumber_bar (Ω := Ω) hk
  have hcω := hU c' hc' hc'N
  have hp : ringChar Fq ≠ 1 := CharP.ringChar_ne_one
  have hdeg : ∀ m : ℕ, 1 ≤ m → (D.deg (1 - X ^ m) : ℂ) = (ω.map fun w => 1 - w ^ m).prod := fun m hm => by
    have : NeZero m := ⟨by omega⟩
    obtain ⟨-, h1, h2⟩ := hc'h m
    rw [D.card_ker_one_sub_X_pow hp m hm, card_ker_one_sub_X_pow_piBar0, h1, h2, hcω]
  have hq : (1 : ℝ) < Fintype.card Fq := by exact_mod_cast Fintype.one_lt_card
  have hprod := D.charPoly_map_eq_prod (piBar0_injective Fq F Ω hk) hq ω hnorm hdeg
  have hmap : D.charPoly = P0.map (Int.castRingHom ℚ) := by
    refine Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective ?_
    rw [hprod, Polynomial.map_map, ← hP0]
    congr 1
  refine ⟨?_, fun c hc hcN => ⟨P0, by rw [hU c hc hcN]; exact hP0, hmap⟩⟩
  have h2 := congrArg Polynomial.natDegree hprod
  rw [Polynomial.natDegree_map, D.charPoly_natDegree, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card,
    hcard] at h2
  omega

end RamanujanPetersson.CoreB


end

-- ===== S4.Def_RP_Cone_ResAsm2 =====
section

/-!
# S4-PD E4S arithmetic ResA, part 5: assembly of `ResDat` in the S3 chart

Continues `Def_RP_Cone_ResAsm` (split for build time). With `τ t` the normalised generators of
`exists_norm_tau_fin` at the cover points `cosQA t`:

* `locGen_base`, `normAll_base`: the base-point data `σ s := τ (cosB s)`.
* `yconj_chi`: `χ (x_t σ x_t⁻¹) = χ (τ t)`; `yconj_exist`: existence at the conjugates.
* **`exists_resDat`**: under `PicDivX`, a `ResDat π π₁^geo I N (CosT π π₁^geo I)` (the input of `ResDat.toResHyp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

section Tau

variable {Gf : Type} [Group Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf) {S : Type}
  (P : S → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
  (hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (P s))
  (I : S → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hI : ∀ s, I s = Inert (P s))
  (τ : ∀ t : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I,
    Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))

include hq he hP hI in
set_option maxHeartbeats 800000 in
/-- The conjugate `y t = x_t σ x_t⁻¹` and `τ t` have the same `χ`-value. -/
theorem yconj_chi {N : ℕ} [NeZero N] {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup) {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hn : ∀ t, NormAll p e hζN M (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) (τ t) k₀)
    (χ : ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) → ZMod N) (hχc : IsLocallyConstant χ)
    (hχ : ∀ a b, χ (a * b) = χ a + χ b) (t : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I) :
    χ ⟨_, yconj_mem π _ I P τ hI (ile_S3 hq he P hP I hI) t⟩ =
      χ ⟨τ t, jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP t (τ t).2⟩ := by
  have h1 := normAll_conj hq he hζN hM hMU (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I t.1))
    (ile_S3 hq he P hP I hI t.1 (tau_base_I π _ I P τ hI t.1)) ((hπM _).1 (tau_base_ker π _ I P τ t.1))
    (hζNg _ (cosX_mem t)) (yconj_memJ π _ I P τ hI t) (normAll_base π P I τ hζN hn t.1)
  exact chi_eq_of_norm hq he hζN hM hMU _ (fun σ hσ => hζNg σ (Subgroup.mem_inf.1 hσ).1) (memΓH_S3 hMU hπM)
    (cosQA_bdry π _ I P hP t) (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))
    (jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP t) ⟨_, yconj_memJ π _ I P τ hI t⟩ (τ t)
    hk₀ hk₀ h1 (hn t) χ hχc hχ

include hq he hP hI in
set_option maxHeartbeats 800000 in
/-- Existence at the conjugates `y t` (from `exists_kchar_of_sum_zero`). -/
theorem yconj_exist {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0)
    (hPic : PicDivX (Places.Rfin Fq F) F (Places.Rinf Fq F) p N)
    {ζN : maxUnram (Places.Rfin Fq F) F} (hζN : IsPrimitiveRoot ζN N)
    (hζNg : ∀ σ ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), σ ζN = ζN)
    {M : IntermediateField F (AlgebraicClosure F)} (hM : M ∈ unramSet (Places.Rfin Fq F) F)
    (hMU : M ≤ maxUnram (Places.Rfin Fq F) F)
    (hπM : ∀ σ, π σ = 1 ↔ σ ∈ (IntermediateField.restrict hMU).fixingSubgroup)
    (hcov : ∀ Q, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q →
      ∃ s, ∃ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), Q = g • P s)
    (hdis : ∀ s s', ∀ g ∈ pi1geo (Places.Rfin Fq F) F (Fintype.card Fq), P s' = g • P s → s = s')
    [Fintype (CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I)] {k₀ : ℕ} (hk₀ : 0 < k₀)
    (hn : ∀ t, NormAll p e hζN M (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)
      (Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t)) (τ t) k₀)
    (c : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I → ZMod N) (hc : ∑ t, c t = 0) :
    ∃ χ : ↥(pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) → ZMod N, IsLocallyConstant χ ∧
      (∀ a b, χ (a * b) = χ a + χ b) ∧ ∀ t, χ ⟨_, yconj_mem π _ I P τ hI (ile_S3 hq he P hP I hI) t⟩ = c t := by
  obtain ⟨χ, hχc, hχ, hχt⟩ := exists_kchar_of_sum_zero hq he (CP4a.exists_zeta_level he)
    (CP4a.isUnit_cast_Rfin hNF) hPic hζN hζNg hM hMU (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P)
    (cosQA_bdry π _ I P hP) (cosQA_cover π _ I P hπM hcov hI) (cosQA_disj_S3 hq he hMU π hπM P hP hdis I hI)
    (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq) ⊓ π.ker) (memΓH_S3 hMU hπM)
    (fun t => Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))
    (jt_le π _ I P (fun _ hQ => inertia_le_geo_S3 hq he hQ) hP) τ hk₀
    (by
      intro k hk hdvd hLU hD hF t v hv α b hαb
      exact @hn t k hk hdvd hLU hD hF v hv α b hαb) c hc
  exact ⟨χ, hχc, hχ, fun t =>
    (yconj_chi hq he π P hP I hI τ hζN hζNg hM hMU hπM hk₀ hn χ hχc hχ t).trans (hχt t)⟩

end Tau

end S3

end

end Residue
end RamanujanPetersson


end


