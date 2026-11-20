-- Prove2me | Definitions.Def_RPLib_F2_028
-- name    : RPLib_F2_028
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T13:35:48.328316+00:00
-- url     : https://prove2.me/theorems/9f2e2610-cb02-4584-a690-fdb52b8d4d90
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 028 of 70
-- statement:
--   File 028 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacLaw_InstBase`: S4-JacLaw, file O10e (part Base): points below points of `D(numA _)`
--   * `S4.Def_RP_JacComplete_AJLoc`: The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point
--   * `S4.Def_RP_Cone_TwS3`: S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data
--   * `S4.Def_RP_CupDuality_GysD`: S4-CurveDuality O4G-4: `π₁(U) = φ^ℕ · π₁^geo · N` for every open `N`
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_026
import Definitions.Def_RPLib_F2_087

/-!
# Ramanujan-Petersson curve library (flat edition), file 028 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacLaw_InstBase`: S4-JacLaw, file O10e (part Base): points below points of `D(numA _)`
* `S4.Def_RP_JacComplete_AJLoc`: The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point
* `S4.Def_RP_Cone_TwS3`: S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data
* `S4.Def_RP_CupDuality_GysD`: S4-CurveDuality O4G-4: `π₁(U) = φ^ℕ · π₁^geo · N` for every open `N`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstBase =====
section

/-!
# S4-JacLaw, file O10e (part Base): points below points of `D(numA _)`

`mB_L mB_R rB_L rB_R lB_L lB_R` (`nestK_base` at `T0`, `iL`, `iR`: the base of `x ∘ nestK` is `pL x`, `pR x`)
and `m_nest r_nest l_nest` (`x ∘ μm = (x ∘ nestK) ∘ mOutL`, etc.).
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

section Base

variable (x : Localization.Away L.ωm →ₐ[K] K) (xr : Localization.Away L.ωr →ₐ[K] K)
  (xl : Localization.Away L.ωl →ₐ[K] K)

theorem mB_L : (L.mB (x.comp (nestK (K := K) L.mU))).comp (iL K F) = pL x := nestK_base L.mU x (iL K F)
theorem mB_R : (L.mB (x.comp (nestK (K := K) L.mU))).comp (iR K F) = pR x := nestK_base L.mU x (iR K F)

end Base

end LawData

end Inst

end RamanujanPetersson.JacLaw


end

-- ===== S4.Def_RP_JacComplete_AJLoc =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJLoc`: the local `ν`-piece through a closed point

* `exists_secE`: through a closed point `φ0` and any finite `E` avoiding the roots of some `b ≠ 0` (in `x`),
  a section `s` with exact poles, only simple zeros, and zero set `Z ⊇ E ∪ {φ0}` of any size.
* `exists_nuE`: `ν`-data `D` with `ν(Z \ E) = E` (`exists_role`), `Z \ E = {φ0} ∪ c`.
* `pieceF D c` (`good` at `Q + c`), `PieceR D c = B[1/pieceF]`, **`pieceMap D c : Sym^g B → B[1/pieceF]`**
  (points `Q ↦ ν(Q + c)`, `ptSet_pieceMap`); `clsK_nuF`: `[ν(A)] = [Hn] - [A]`.
* **`exists_piece`**: the package for a closed point.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR

universe u

section AJLoc

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {r : ℕ} (D : NuData K F (1 + r)) (c : Fin r → (Rfin K F →ₐ[K] K))

/-- **The `ν`-piece** `Q ↦ ν(Q + c)` on `D(f)`. -/
noncomputable def pieceMap : SymRing K (Rfin K F) (genusFK K F) →ₐ[K] PieceR D c :=
  (pieceLift D c).comp D.nuMap

theorem ptSet_pieceMap (x : PieceR D c →ₐ[K] K) :
    ptSet (x.comp (pieceMap D c)) = D.nuF (padPt phi1 c rfl (x.comp (pieceι D c))) := by
  rw [pieceMap, ← AlgHom.comp_assoc, NuData.comp_nuMap, NuData.ptSet_nuPt, NuData.nuSet_eq_nuF,
    yOf_pieceLift]

end AJLoc

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_Cone_TwS3 =====
section

/-!
# S4-PD (4), arithmetic twist part C: the twist clause of the S3 residue data

* `twist_jt` (chart-generic): the local twist `χ (φ σ φ⁻¹) = q • χ σ` on `J = I(Q) ∩ ker π` for `φ • Q = Q`.
* `twist_loc_S3`: the same in the S3 chart for a Frobenius lift `φ` (`q = |𝔽_q|`), level data discharged.
* `tw_core`: for the normalised generators `τ` of `exists_norm_tau_fin`, `g⁻¹` a Frobenius lift with
  `P u = g⁻¹ • P s`: `χ (g⁻¹ τ_s g) = q • χ τ_u` (local twist if `u = s`, global normalisation otherwise).
* **`exists_resDat_tw`**: `exists_resDat` together with this twist clause.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace RamanujanPetersson
namespace Residue

noncomputable section

open CurveCoh GalCover Kummer CP4a TameInertia IsDedekindDomain Polynomial
open scoped Pointwise

section Gen

variable {A K : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  {R0 : Type} [CommRing R0] [IsDedekindDomain R0] [Algebra R0 K] [IsFractionRing R0 K]

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)

include hq he in
set_option maxHeartbeats 1600000 in
/-- **Local twist in the S3 chart**: a Frobenius lift `φ` stabilising the boundary prime `Q` acts on every locally
constant homomorphism `χ : I(Q) ∩ ker π → M` (`N M = 0`) by `χ (φ σ φ⁻¹) = q • χ σ`. -/
theorem twist_loc_S3 {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0) {Gf : Type} [Group Gf] [Finite Gf]
    (π : Pi1 (Places.Rfin Fq F) F →* Gf) {Q : Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))}
    (hQ : IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) Q) (φ : Pi1 (Places.Rfin Fq F) F)
    (hφF : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) φ) (hφQ : φ • Q = Q)
    {Mo : Type*} [AddCommGroup Mo] (hMo : ∀ m : Mo, N • m = 0) (χ : Jt π Q → Mo)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b) (σ : Pi1 (Places.Rfin Fq F) F)
    (hσ : σ ∈ Jt π Q) (hσ' : φ * σ * φ⁻¹ ∈ Jt π Q) :
    χ ⟨φ * σ * φ⁻¹, hσ'⟩ = Fintype.card Fq • χ ⟨σ, hσ⟩ := by
  have hp : p.Prime := Fact.out
  have hc0 : Nat.card Gf ≠ 0 := Nat.card_pos.ne'
  obtain ⟨d, hd_def⟩ : ∃ d, d = Nat.card Gf / p ^ Nat.factorization (Nat.card Gf) p := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    rw [hd_def]
    exact Nat.ordCompl_pos p hc0
  have hdF : (d : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p, hd_def]
    exact Nat.not_dvd_ordCompl hp hc0
  have hpd : p ^ Nat.factorization (Nat.card Gf) p * d = Nat.card Gf := by
    rw [hd_def]
    exact Nat.ordProj_mul_ordCompl_eq_self (Nat.card Gf) p
  have hNd : ((N * d : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_mul]
    exact mul_ne_zero hNF hdF
  have : NeZero (N * d) := ⟨Nat.mul_ne_zero (NeZero.ne N) hd0.ne'⟩
  have : NeZero d := ⟨hd0.ne'⟩
  obtain ⟨ζd, hζd, hζc⟩ := Kummer.exists_zeta (Places.Rfin Fq F) F p he (N * d) hNd
  have hne : Q.comap (algebraMap (Places.Rinf Fq F)
      (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) ≠ ⊥ := by
    have := hQ.1
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ.2
    exact Ideal.comap_ne_bot_of_integral_mem hz0 hz (Algebra.IsIntegral.isIntegral z)
  obtain ⟨x, hx⟩ : ∃ x : HeightOneSpectrum (Places.Rinf Fq F), x.asIdeal =
      Q.comap (algebraMap (Places.Rinf Fq F) (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F))) :=
    ⟨⟨_, Ideal.IsPrime.comap _ (hK := hQ.1), hne⟩, rfl⟩
  have := hasFiniteQuotients_of_finiteQuot (S := Places.Rinf Fq F)
  exact twist_jt π hQ (p := p) (CP4a.isUnit_cast_Rfin hNd) (CP4a.isUnit_cast_Rinf hNd) hζd
    (fun σ' hσ'' => Kummer.zeta_fixed hζc σ' (by
      have h := Kummer.inertia_le_pi1geo he hq (hP := hQ.1) hσ''
      rwa [hq] at h)) x hx
    (⟨algebraMap Fq[X] F X, isIntegral_algebraMap⟩ : Places.Rfin Fq F)
    (by have h := JacComplete.one_lt_placeVal_inr_x (K := Fq) (F := F) x; exact h)
    _ hpd φ hφQ _ (hφF ζd (by rw [hq]; exact hζc)) hMo χ hχc hχ σ hσ hσ'

section Tau

variable {Gf : Type} [Group Gf] (π : Pi1 (Places.Rfin Fq F) F →* Gf) {S : Type}
  (P : S → Ideal (proChart (Places.Rfin Fq F) F (Places.Rinf Fq F)))
  (hP : ∀ s, IsBdryPrime (Places.Rfin Fq F) F (Places.Rinf Fq F) (P s))
  (I : S → Subgroup (Pi1 (Places.Rfin Fq F) F)) (hI : ∀ s, I s = Inert (P s))
  (τ : ∀ t : CosT π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I,
    Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P t))

include hq he hP in
set_option maxHeartbeats 800000 in
/-- Case `u = s` of `tw_core`: `g⁻¹` stabilises `P u` (local twist). -/
theorem tw_same [Finite Gf] {N : ℕ} [NeZero N] (hNF : (N : F) ≠ 0) {u : S} (g : Pi1 (Places.Rfin Fq F) F)
    (hgF : IsFrobLift (Places.Rfin Fq F) F (Fintype.card Fq) g⁻¹) (hu : P u = g⁻¹ • P u)
    {Mo : Type*} [AddCommGroup Mo] (hMo : ∀ m : Mo, N • m = 0)
    (χ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) → Mo)
    (hχc : IsLocallyConstant χ) (hχ : ∀ a b, χ (a * b) = χ a + χ b)
    (hc : g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) : Pi1 (Places.Rfin Fq F) F) * g ∈
      Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))) :
    χ ⟨_, hc⟩ = Fintype.card Fq • χ (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) := by
  have hφQ : g⁻¹ • cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) =
      cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) := by
    have key : ∀ X, X = P u → g⁻¹ • X = X := by
      rintro X rfl
      exact hu.symm
    exact key _ (cosQA_base π _ I P u)
  have hc' : g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) : Pi1 (Places.Rfin Fq F) F) *
      g⁻¹⁻¹ ∈ Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
        (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u)) := by
    rw [inv_inv]
    exact hc
  have h := twist_loc_S3 hq he hNF π (cosQA_bdry π _ I P hP _) g⁻¹ hgF hφQ hMo χ hχc hχ _ (τ _).2 hc'
  have e1 : (⟨_, hc'⟩ : Jt π (cosQA π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I P
      (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u))) = ⟨_, hc⟩ := by
    apply Subtype.ext
    show g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) : Pi1 (Places.Rfin Fq F) F) *
      g⁻¹⁻¹ = g⁻¹ * (τ (cosB π (pi1geo (Places.Rfin Fq F) F (Fintype.card Fq)) I u) : Pi1 (Places.Rfin Fq F) F) * g
    rw [inv_inv]
  exact (congrArg χ e1).symm.trans h

end Tau

end S3

end

end Residue
end RamanujanPetersson


end

-- ===== S4.Def_RP_CupDuality_GysD =====
section

/-!
# S4-CurveDuality O4G-4: `π₁(U) = φ^ℕ · π₁^geo · N` for every open `N`

Route G (session 44). `Γ_L` (`fixLev`) fixes the constants of level `L`; these sets are closed, directed, and
`⋂ Γ_L = π₁^geo`, so by compactness some `Γ_L` lies in the open set `π₁^geo · N` (`exists_fixLev_sub`). Any `ψ`
acts on `𝔽_{q^L} ⊆ K_U` as a power `x ↦ x^{q^j}` (`exists_pow_lev`, CP4a's `exists_frob_pow_of_finite`), as does `φ^j`
for a Frobenius lift `φ`; hence `(φ^j)⁻¹ ψ ∈ Γ_L` and `ψ = φ^j γ n` (`exists_frobPow_mul`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open Places PicDescent CurveCoh Kummer GalCover CP4a
open scoped Pointwise Polynomial

noncomputable section

section Gen

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem fixLev_mono (q a b : ℕ) : fixLev (A := A) (K := K) q (a * b) ⊆ fixLev q a := by
  intro σ hσ x hx
  exact hσ x (by rw [pow_mul]; exact pow_pow_iter hx b)

/-- A Frobenius lift acts as `x ↦ x^{q^j}` through `φ^j` on the constants of level `L`. -/
theorem frob_pow_apply {q : ℕ} {φ : Pi1 A K} (hφ : IsFrobLift A K q φ) {L : ℕ} (hL : 0 < L) (j : ℕ) :
    ∀ x : maxUnram A K, x ^ q ^ L = x → (φ ^ j) x = x ^ q ^ j := by
  induction j with
  | zero => intro x _; simp
  | succ j ih =>
    intro x hx
    have hxq : (x ^ q) ^ q ^ L = x ^ q := by rw [← pow_mul, mul_comm, pow_mul, hx]
    rw [pow_succ φ j, AlgEquiv.mul_apply, hφ x ⟨L, hL, hx⟩, ih _ hxq, ← pow_mul, pow_succ' q j]

/-- Compactness: some `Γ_L` lies in a given open neighbourhood of `π₁^geo`. -/
theorem exists_fixLev_sub (q : ℕ) {U : Set (Pi1 A K)} (hU : IsOpen U)
    (hsub : (pi1geo A K q : Set (Pi1 A K)) ⊆ U) : ∃ L, 0 < L ∧ fixLev (A := A) (K := K) q L ⊆ U := by
  let T : ℕ → Set (Pi1 A K) := fun m => fixLev q (m + 1) ∩ Uᶜ
  have hdir : Directed (· ⊇ ·) T := by
    intro i j
    have hpos : 1 ≤ (i + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
    · show T _ ⊆ T _
      simp only [T, Nat.sub_add_cancel hpos]
      exact Set.inter_subset_inter_left _ (fixLev_mono _ _ _)
    · show T _ ⊆ T _
      simp only [T, Nat.sub_add_cancel hpos]
      rw [mul_comm]
      exact Set.inter_subset_inter_left _ (fixLev_mono _ _ _)
  have hclosed : ∀ m, IsClosed (T m) := fun m => (isClosed_fixLev _ _).inter hU.isClosed_compl
  have hempty : (Set.univ ∩ ⋂ m, T m) = ∅ := by
    refine Set.subset_empty_iff.1 fun σ hσ => ?_
    have hT : ∀ m, σ ∈ T m := Set.mem_iInter.1 hσ.2
    have hgeo : σ ∈ pi1geo A K q := (mem_pi1geo A K q σ).2 fun x hx => by
      obtain ⟨n, hn, hxn⟩ := hx
      exact (hT (n - 1)).1 x (by rw [Nat.sub_add_cancel hn]; exact hxn)
    exact (hT 0).2 (hsub hgeo)
  obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_family_closed T hclosed hempty hdir
  refine ⟨m + 1, Nat.succ_pos m, fun σ hσ => ?_⟩
  by_contra hσU
  have h : σ ∈ Set.univ ∩ T m := ⟨trivial, hσ, hσU⟩
  rw [hm] at h
  exact h

end Gen

section S3

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- Every `ψ ∈ π₁(U)` acts on the constants of level `L` as a power of the `q`-Frobenius. -/
theorem exists_pow_lev (ψ : Pi1 (Rfin Fq F) F) (L : ℕ) [NeZero L] :
    ∃ j : ℕ, ∀ x : maxUnram (Rfin Fq F) F, x ^ Fintype.card Fq ^ L = x →
      ψ x = x ^ Fintype.card Fq ^ j := by
  let f : Lc Fq (maxUnram (Rfin Fq F) F) L →+* maxUnram (Rfin Fq F) F :=
    (Lc Fq (maxUnram (Rfin Fq F) F) L).val.toRingHom
  let g : Lc Fq (maxUnram (Rfin Fq F) F) L →+* maxUnram (Rfin Fq F) F := ψ.toAlgHom.toRingHom.comp f
  have hfg : ∀ a : Fq, f (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a) =
      g (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a) := by
    intro a
    have h1 : f (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a) =
        algebraMap Fq (maxUnram (Rfin Fq F) F) a := (Lc Fq (maxUnram (Rfin Fq F) F) L).val.commutes a
    rw [show g (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a) =
      ψ (f (algebraMap Fq (Lc Fq (maxUnram (Rfin Fq F) F) L) a)) from rfl, h1,
      IsScalarTower.algebraMap_apply Fq F (maxUnram (Rfin Fq F) F) a, AlgEquiv.commutes]
  obtain ⟨j, hj⟩ := exists_frob_pow_of_finite f g hfg
  refine ⟨j, fun x hx => ?_⟩
  exact hj ⟨x, mem_Lc.2 hx⟩

/-- **O4G-4.** `ψ = φ^j γ n` with `γ ∈ π₁^geo`, `n ∈ N`, for a Frobenius lift `φ` and an open `N`. -/
theorem exists_frobPow_mul {φ : Pi1 (Rfin Fq F) F} (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    (N : Subgroup (Pi1 (Rfin Fq F) F)) (hN : IsOpen (N : Set (Pi1 (Rfin Fq F) F))) (ψ : Pi1 (Rfin Fq F) F) :
    ∃ j : ℕ, ∃ γ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), ∃ n ∈ N, ψ = φ ^ j * γ * n := by
  obtain ⟨L, hL, hsub⟩ := exists_fixLev_sub (A := Rfin Fq F) (K := F) (Fintype.card Fq)
    (U := (pi1geo (Rfin Fq F) F (Fintype.card Fq) : Set (Pi1 (Rfin Fq F) F)) * (N : Set (Pi1 (Rfin Fq F) F)))
    hN.mul_left (fun σ hσ => Set.mem_mul.2 ⟨σ, hσ, 1, N.one_mem, mul_one σ⟩)
  have : NeZero L := ⟨hL.ne'⟩
  obtain ⟨j, hj⟩ := exists_pow_lev ψ L
  have hmem : (φ ^ j)⁻¹ * ψ ∈ fixLev (A := Rfin Fq F) (K := F) (Fintype.card Fq) L := by
    simp only [fixLev, Set.mem_ofPred_eq]
    intro x hx
    show (φ ^ j).symm (ψ x) = x
    rw [hj x hx, ← frob_pow_apply hφ hL j x hx]
    exact (φ ^ j).symm_apply_apply x
  obtain ⟨γ, hγ, n, hn, hγn⟩ := Set.mem_mul.1 (hsub hmem)
  exact ⟨j, γ, hγ, n, hn, by rw [mul_assoc, hγn, mul_inv_cancel_left]⟩

end S3

end

end CupDuality
end RamanujanPetersson


end


