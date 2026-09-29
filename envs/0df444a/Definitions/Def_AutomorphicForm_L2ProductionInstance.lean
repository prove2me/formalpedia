-- Prove2me | Definitions.Def_AutomorphicForm_L2ProductionInstance
-- name    : AutomorphicForm_L2ProductionInstance
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/c8fa68fd-0013-53b2-b410-fdf5e23b3e5f
-- title:
--   The L2 space on a Γ0​(N) fundamental set
-- statement:
--   For a natural number $N$ with $N \neq 0$, `Gamma0L2 N` is an abbreviation for the complex $L^2$ space $L^2(\mathbb{C}, 2, \mathrm{vol}|_{F_N})$, where $\mathrm{vol}$ is the hyperbolic volume on the upper half plane $\mathbb{H}$ and $F_N =$ `gammaFundamentalSet (Gamma0 N)` is the union $\bigcup_{q \in SL_2(\mathbb{Z})/\Gamma_0(N)} (\mathrm{out}\,q)^{-1} \cdot \mathcal{D}$ of translates of Mathlib's standard fundamental domain $\mathcal{D}$ for $SL_2(\mathbb{Z})$ by the inverses of chosen coset representatives (a covering set, with no disjointness asserted). The supporting declarations record that each translate $\gamma \cdot \mathcal{D}$ is closed, hence measurable; that $SL_2(\mathbb{Z})$ and all its coset spaces are countable, so that $F_N$, being a countable union of such translates, is measurable; and that the restriction of $\mathrm{vol}$ to $F_N$ is a finite measure, since $\mathrm{vol}(F_N) < \infty$. Consequently `Gamma0L2 N` carries the usual normed group, complex inner product space and completeness structures.
--
--   The map `boundedToGamma0L2` sends a continuous $f : \mathbb{H} \to \mathbb{C}$ together with a real bound $C$ satisfying $\|f(z)\| \leq C$ for all $z \in F_N$ to the corresponding class in `Gamma0L2 N`, and `boundedToGamma0L2_coeFn` states that this class is represented by $f$ almost everywhere for $\mathrm{vol}|_{F_N}$. Applying this to the constant function $1$ gives `gamma0L2Const N`, which is nonzero because $\mathrm{vol}(F_N) > 0$; hence `Gamma0L2 N` is nontrivial. Two further statements delimit the construction: the constant function $1$ does not lie in $L^2(\mathbb{H}, \mathrm{vol})$ for the unrestricted measure, since $\mathrm{vol}(\mathbb{H}) = \infty$; and at level one $\mathrm{vol}(F_1) \leq \mathrm{vol}(\mathcal{D})$, the index-one coset space being a single class.
--
--   **Relation to Mathlib.** Mathlib supplies the upper half plane with its hyperbolic volume, the fundamental domain $\mathcal{D}$ for $SL_2(\mathbb{Z})$, the congruence subgroups $\Gamma_0(N)$ and the $L^p$ spaces; the fundamental set for a subgroup of $SL_2(\mathbb{Z})$ and the resulting $L^2$ automorphic carrier are the project's own.
--
--   **Where it is used.** These declarations provide the Hilbert space of square-integrable functions on a fundamental set for $\Gamma_0(N)$, the analytic carrier on which a spectral decomposition of automorphic forms of level $N$ is to be set up.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_L2ProductionInstance.lean

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Definitions.Def_AutomorphicForm_L2AutomorphicCarrier
import Definitions.Def_AutomorphicForm_TruncatedDomainPartition

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open MeasureTheory
open scoped Modular MatrixGroups Pointwise ENNReal

noncomputable section

namespace FLT.L2ProductionInstance

open FLT.Gamma0FundamentalSet FLT.L2Carrier

theorem isClosed_smul_fd (γ : SL(2, ℤ)) : IsClosed (γ • 𝒟) :=
  ModularGroup.isClosed_fd.smul γ

theorem measurableSet_smul_fd (γ : SL(2, ℤ)) : MeasurableSet (γ • 𝒟) :=
  (isClosed_smul_fd γ).measurableSet

instance countable_SL2Z : Countable SL(2, ℤ) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  inferInstanceAs (Countable { A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1 })

instance countable_quotient (Γ : Subgroup SL(2, ℤ)) : Countable (SL(2, ℤ) ⧸ Γ) :=
  Quotient.countable

theorem measurableSet_gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) :
    MeasurableSet (gammaFundamentalSet Γ) :=
  MeasurableSet.iUnion fun q => measurableSet_smul_fd (Quotient.out q)⁻¹

theorem measurableSet_gamma0 (N : ℕ) : MeasurableSet (gammaFundamentalSet (Gamma0 N)) :=
  measurableSet_gammaFundamentalSet (Gamma0 N)

abbrev Gamma0L2 (N : ℕ) : Type :=
  AutomorphicL2 (gammaFundamentalSet (Gamma0 N))

instance isFiniteMeasure_gamma0 (N : ℕ) [NeZero N] :
    IsFiniteMeasure ((volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))) :=
  isFiniteMeasure_restrict_of_lt_top (volume_gamma0_lt_top N)

example (N : ℕ) : NormedAddCommGroup (Gamma0L2 N) := inferInstance

example (N : ℕ) : InnerProductSpace ℂ (Gamma0L2 N) := inferInstance

example (N : ℕ) : CompleteSpace (Gamma0L2 N) := inferInstance

noncomputable def boundedToGamma0L2 (N : ℕ) [NeZero N] (f : ℍ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ z ∈ gammaFundamentalSet (Gamma0 N), ‖f z‖ ≤ C) : Gamma0L2 N :=
  boundedToL2 (volume_gamma0_lt_top N) (measurableSet_gamma0 N) f hf C hC

theorem boundedToGamma0L2_coeFn (N : ℕ) [NeZero N] (f : ℍ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ z ∈ gammaFundamentalSet (Gamma0 N), ‖f z‖ ≤ C) :
    (boundedToGamma0L2 N f hf C hC : ℍ → ℂ)
      =ᵐ[(volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))] f :=
  boundedToL2_coeFn _ _ f hf C hC

noncomputable def gamma0L2Const (N : ℕ) [NeZero N] : Gamma0L2 N :=
  boundedToGamma0L2 N (fun _ => (1 : ℂ)) continuous_const 1 (fun _ _ => by simp)

theorem gamma0L2Const_ne_zero (N : ℕ) [NeZero N] : gamma0L2Const N ≠ 0 := by
  intro h

  have h1 : (gamma0L2Const N : ℍ → ℂ)
      =ᵐ[(volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp h
  have h2 : (fun _ : ℍ => (1 : ℂ))
      =ᵐ[(volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))] 0 :=
    (boundedToGamma0L2_coeFn N (fun _ => (1 : ℂ)) continuous_const 1
      (fun _ _ => by simp)).symm.trans h1

  have hnull : (volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))
      Set.univ = 0 := by
    have h3 : ∀ᵐ z ∂((volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))),
        (1 : ℂ) = 0 := h2
    simpa [ae_iff] using h3
  rw [Measure.restrict_apply_univ] at hnull
  exact absurd hnull (volume_gammaFundamentalSet_pos (Gamma0 N)).ne'

instance nontrivial_gamma0L2 (N : ℕ) [NeZero N] : Nontrivial (Gamma0L2 N) :=
  ⟨gamma0L2Const N, 0, gamma0L2Const_ne_zero N⟩

theorem gate_const_not_memLp_unrestricted :
    ¬ MemLp (fun _ : ℍ => (1 : ℂ)) 2 (volume : Measure ℍ) :=
  gate_const_not_memLp_of_infinite FLT.HyperbolicMeasure.volume_univ_eq_top

example : volume (gammaFundamentalSet (Gamma0 11)) < ⊤ := volume_gamma0_lt_top 11

theorem gate_level_one_volume :
    volume (gammaFundamentalSet (Gamma0 1)) ≤ volume 𝒟 := by

  have hsub : ∀ q : SL(2, ℤ) ⧸ Gamma0 1,
      q = QuotientGroup.mk (1 : SL(2, ℤ)) := fun q => by
    induction q using QuotientGroup.induction_on with
    | _ a => exact (QuotientGroup.eq).mpr (Gamma0_mem.mpr (Subsingleton.elim _ _))
  have hcover : gammaFundamentalSet (Gamma0 1) ⊆
      (Quotient.out (QuotientGroup.mk (1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma0 1))⁻¹ • 𝒟 := by
    refine Set.iUnion_subset fun q => ?_
    rw [hsub q]
  calc volume (gammaFundamentalSet (Gamma0 1))
      ≤ volume ((Quotient.out (QuotientGroup.mk (1 : SL(2, ℤ)) :
          SL(2, ℤ) ⧸ Gamma0 1))⁻¹ • 𝒟) := measure_mono hcover
    _ = volume 𝒟 := FLT.HyperbolicMeasure.volume_smul_sl2z _ _

end FLT.L2ProductionInstance

end


