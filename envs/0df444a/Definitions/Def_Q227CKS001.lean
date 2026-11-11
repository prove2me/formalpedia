-- Prove2me | Definitions.Def_Q227CKS001
-- name    : Q227CKS001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:37:08.508823+00:00
-- url     : https://prove2.me/theorems/2ca68d5c-781a-4174-aba7-d8910b52ac48
-- title:
--   Definitions bundle Q227CKS001 of the split of OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CKSMain.schwarzschild_equality_examples`, carved from OpenAI's openai/math development (OpenAI, *Area-controlled end replacement and the Bondi Penrose inequality in the CKS class*, OpenAI Math Release, September 27, 2026, result family 260, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 33 definitions, 3 inductive types or structures, 8 instances and 14 theorems. The definitions and types are `OAI.CKSMixedGeometry.chartDerivative`, `OAI.CKSMixedGeometry.coordinateIter`, `OAI.CKSRealizedRound.lapse`, `OAI.CKSRealizedRound.radial`, `OAI.CKSRealizedRound.radicand`, `OAI.CKSReplacementCompleteness.metricEDist`, `OAI.CKSReplacementCompleteness.tangentNorm`, `OAI.CKSRound.LapseJet`, `OAI.CKSRound.LapseJet.first`, `OAI.CKSRound.LapseJet.roundDInv`, `OAI.CKSRound.LapseJet.roundGamma`, `OAI.CKSRound.LapseJet.roundMetric`, `OAI.CKSRound.LapseJet.second`, `OAI.CKSRound.MassJet`, `OAI.CKSRound.MassJet.gradientSq`, `OAI.CKSRound.MassJet.laplace`, `OAI.CKSRound.MassJet.lapse`, `OAI.CKSRound.RoundTensor`, `OAI.CKSRound.RoundTensor.jet`, `OAI.CKSSphericalHarmonics.SphereL2`, `OAI.CKSSphericalHarmonics.sphereArea`, `OAI.CKSSphericalHarmonics.sphereHome`, `OAI.CKSSphericalHarmonics.sphereIntegral`, `OAI.CKSSphericalHarmonics.toL2`, `OAI.CKSSurfaceVolume.chartPreimage`, `OAI.CKSSurfaceVolume.chartTransition`, `OAI.CKSSurfaceVolume.instNormedAddCommGroupContinuousLinearMapRealIdE`, `OAI.CKSSurfaceVolume.instNormedSpaceRealContinuousLinearMapIdE`, `OAI.CKSSurfaceVolume.mapChart`, `OAI.CKSSurfaceVolume.mapChartDeriv`, `OAI.CKSSurfaceVolume.mapPullbackInner`, `OAI.CKSSurfaceVolume.pullbackInner`, `OAI.CKSSurfaceVolume.stdBasis`, `OAI.CKSSurfaceVolume.transitionDeriv`, `OAI.circleMeasurableSpace`, `OAI.starSubalgebraCommCStarAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`Relativity_CKS_BondiBalance`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/BondiBalance.lean), [`Relativity_CKS_HeatBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/HeatBase.lean), [`Relativity_CKS_LogRadiusJets`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/LogRadiusJets.lean), [`Relativity_CKS_ScaledPullback`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/ScaledPullback.lean), [`Relativity_CKS_SchwarzschildCKSAlgebra`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SchwarzschildCKSAlgebra.lean), [`Relativity_CKS_SchwarzschildCKSDecay`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SchwarzschildCKSDecay.lean), [`Relativity_CKS_SchwarzschildProfile`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SchwarzschildProfile.lean), [`Relativity_CKS_SmoothOuterDEC`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SmoothOuterDEC.lean), [`Relativity_CKS_SurfaceMapDerivative`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SurfaceMapDerivative.lean), [`Relativity_CKS_SurfaceScaling`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SurfaceScaling.lean), [`Relativity_CKS_SurfaceVolume`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/SurfaceVolume.lean), [`Relativity_CKS_TailEnergy`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/Relativity/CKS/TailEnergy.lean).
--
--   **Imports.** It imports the published bundle `Def_CKSBondiPenrose`.
--
--   **Imported by** (directly, in this split): the bundles `Q227CKS002` and `Q227CKS003`; the proofs of `OAI_CKSAngularGeometry_local_coordinate_DEC_pushforward` and `OAI_CKSSurfaceVolume_volume_le_of_surjective_nonexpanding`.
-- source:
--   OpenAI, Area-controlled end replacement and the Bondi Penrose inequality in the CKS class, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 260; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Area-controlled-end-replacement-and-the-Bondi-Penrose-inequality-in-the-CKS-class-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_CKSBondiPenrose

section
-- module Solutions.Q227_CKS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SmoothOuterDEC
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSRound
noncomputable section

structure LapseJet where
  u : ℝ
  ur : ℝ
  ut : ℝ
  up : ℝ
  urr : ℝ
  urt : ℝ
  urp : ℝ
  utt : ℝ
  utp : ℝ
  upp : ℝ

namespace LapseJet

def first (j : LapseJet) : Idx → ℝ := ![j.ur, j.ut, j.up]
def second (j : LapseJet) : Mat :=
  !![j.urr, j.urt, j.urp; j.urt, j.utt, j.utp; j.urp, j.utp, j.upp]

def roundMetric (j : LapseJet) (r s c : ℝ) : MetricJet where
  inv := !![j.u ^ 2, 0, 0; 0, 1 / r ^ 2, 0; 0, 0, 1 / (r ^ 2 * s ^ 2)]
  d := fun a => !![-2 * j.first a / j.u ^ 3, 0, 0;
    0, (![2 * r, 0, 0] : Idx → ℝ) a, 0;
    0, 0, (![2 * r * s ^ 2, 2 * r ^ 2 * s * c, 0] : Idx → ℝ) a]
  dd := fun a b => !![6 * j.first a * j.first b / j.u ^ 4 -
      2 * j.second a b / j.u ^ 3, 0, 0;
    0, (!![2, 0, 0; 0, 0, 0; 0, 0, 0] : Mat) a b, 0;
    0, 0, (!![2 * s ^ 2, 4 * r * s * c, 0;
      4 * r * s * c, 2 * r ^ 2 * (c ^ 2 - s ^ 2), 0;
      0, 0, 0] : Mat) a b]

def roundGamma (j : LapseJet) (r s c : ℝ) : Idx → Mat := ![
  !![-j.ur / j.u, -j.ut / j.u, -j.up / j.u;
    -j.ut / j.u, -r * j.u ^ 2, 0;
    -j.up / j.u, 0, -r * j.u ^ 2 * s ^ 2],
  !![j.ut / (r ^ 2 * j.u ^ 3), 1 / r, 0;
    1 / r, 0, 0;
    0, 0, -s * c],
  !![j.up / (r ^ 2 * s ^ 2 * j.u ^ 3), 0, 1 / r;
    0, 0, c / s;
    1 / r, c / s, 0]]

def roundDInv (j : LapseJet) (r s c : ℝ) : Idx → Mat := fun a =>
  !![2 * j.u * j.first a, 0, 0;
    0, (![-2 / r ^ 3, 0, 0] : Idx → ℝ) a, 0;
    0, 0, (![-2 / (r ^ 3 * s ^ 2), -2 * c / (r ^ 2 * s ^ 3), 0] : Idx → ℝ) a]

end LapseJet

structure RoundTensor where
  v : ℝ
  vp : ℝ
  L : ℝ
  Lr : ℝ
  Lt : ℝ
  Lp : ℝ
  a : ℝ
  ar : ℝ
  aθ : ℝ
  ap : ℝ
  b : ℝ
  br : ℝ
  bt : ℝ
  bp : ℝ

namespace RoundTensor

def jet (k : RoundTensor) (j : LapseJet) (r s c : ℝ) : TensorJet where
  val := !![k.L / j.u ^ 2, 0, 0;
    0, k.v * r + k.a, k.b;
    0, k.b, (k.v * r - k.a) * s ^ 2]
  d := fun i => !![
    (![k.Lr, k.Lt, k.Lp] : Idx → ℝ) i / j.u ^ 2 -
      2 * k.L * j.first i / j.u ^ 3, 0, 0;
    0, (![k.vp * r + k.v + k.ar, k.aθ, k.ap] : Idx → ℝ) i,
      (![k.br, k.bt, k.bp] : Idx → ℝ) i;
    0, (![k.br, k.bt, k.bp] : Idx → ℝ) i,
      (![(k.vp * r + k.v - k.ar) * s ^ 2,
        -k.aθ * s ^ 2 + 2 * (k.v * r - k.a) * s * c,
        -k.ap * s ^ 2] : Idx → ℝ) i]

end RoundTensor

structure MassJet where
  F : ℝ
  Fr : ℝ
  Ft : ℝ
  Fp : ℝ
  Frr : ℝ
  Frt : ℝ
  Frp : ℝ
  Ftt : ℝ
  Ftp : ℝ
  Fpp : ℝ

namespace MassJet

def laplace (f : MassJet) (s c : ℝ) : ℝ := f.Ftt + c / s * f.Ft + f.Fpp / s ^ 2

def gradientSq (f : MassJet) (s : ℝ) : ℝ := f.Ft ^ 2 + f.Fp ^ 2 / s ^ 2

def lapse (f : MassJet) (r u v vp vpp : ℝ) : LapseJet where
  u := u
  ur := (v * vp - f.Fr / r + f.F / r ^ 2) / u
  ut := -f.Ft / (r * u)
  up := -f.Fp / (r * u)
  urr := (vp ^ 2 + v * vpp - f.Frr / r + 2 * f.Fr / r ^ 2 -
      2 * f.F / r ^ 3) / u - (v * vp - f.Fr / r + f.F / r ^ 2) ^ 2 / u ^ 3
  urt := (-f.Frt / r + f.Ft / r ^ 2) / u +
    (v * vp - f.Fr / r + f.F / r ^ 2) * f.Ft / (r * u ^ 3)
  urp := (-f.Frp / r + f.Fp / r ^ 2) / u +
    (v * vp - f.Fr / r + f.F / r ^ 2) * f.Fp / (r * u ^ 3)
  utt := -f.Ftt / (r * u) - f.Ft ^ 2 / (r ^ 2 * u ^ 3)
  utp := -f.Ftp / (r * u) - f.Ft * f.Fp / (r ^ 2 * u ^ 3)
  upp := -f.Fpp / (r * u) - f.Fp ^ 2 / (r ^ 2 * u ^ 3)

end MassJet

end
end CKSRound

end

noncomputable section
namespace CKSRealizedRound
noncomputable section
open CKSCalculus CKSRound Filter
open scoped Topology ContDiff

def radial (v : ℝ → ℝ) (x : Point) : ℝ := v (x 0)

def radicand (F : Point → ℝ) (v : ℝ → ℝ) (x : Point) : ℝ :=
  1 + radial v x ^ 2 - 2 * F x / x 0

def lapse (F : Point → ℝ) (v : ℝ → ℝ) (x : Point) : ℝ :=
  Real.sqrt (radicand F v x)

end
end CKSRealizedRound

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_LogRadiusJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma basis_rad_abs (a : I) : |basis a 0| ≤ 1 := by
  simp only [basis,Pi.single_apply]
  split_ifs <;> norm_num

end
end CKSMixedGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_ScaledPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal

lemma radialFactor_smooth (a : I) : ContDiff ℝ ∞ (radialFactor a) := by
  unfold radialFactor
  by_cases ha : a = 0 <;> simp only [ha,ite_true, if_true,ite_false, if_false] <;> fun_prop

theorem coordinate_continuousConstSMul : ContinuousConstSMul ℝ ℝ := inferInstance

theorem coordinate_smulCommClass :
    @SMulCommClass ℝ ℝ ℝ Algebra.toSMul
      (@instSMulOfMul ℝ (@Distrib.toMul ℝ
        (@instDistribOfSemiring ℝ (@CommSemiring.toSemiring ℝ Real.instCommSemiring)))) :=
  inferInstance

def chartDerivative (x : Point) : Point →L[ℝ] Point :=
  letI := pointDimension_neZero
  letI := coordinate_smulCommClass
  letI := coordinate_continuousConstSMul
  ContinuousLinearMap.pi (fun i => if i = 0 then Real.exp (x 0) • ContinuousLinearMap.proj 0
    else ContinuousLinearMap.proj i)

def coordinateIter : List I → (Point → ℝ) → Point → ℝ
  | [], f => f
  | a::l,f => D (basis a) (coordinateIter l f)

end
end CKSMixedGeometry

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_HeatBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MvPolynomial

open MeasureTheory

abbrev SphereL2 := Lp ℝ 2 surfaceMeasure

def toL2 : C(Sphere, ℝ) →L[ℝ] SphereL2 := ContinuousMap.toLp 2 surfaceMeasure ℝ

open scoped Pointwise
def sphereHome (u : Ambient ≃ₗᵢ[ℝ] Ambient) : Sphere ≃ₜ Sphere :=
  u.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      u.norm_map])

def sphereIntegral : C(Sphere, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (toL2 1)).comp toL2

def sphereArea : ℝ := sphereIntegral 1

open scoped Manifold ContDiff Topology
open Set

end
end CKSSphericalHarmonics

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_BondiBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSTangentCoefficients
noncomputable section
open Bundle Manifold Set Bornology
open scoped Matrix.Norms.Elementwise Bundle Manifold ContDiff BigOperators
variable {H : Type*}
  [TopologicalSpace H]
  {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace H M]
local instance scalarAtlas : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℝ) :=
  ⟨by rfl⟩
end
end CKSTangentCoefficients

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_TailEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CKSReplacementCompleteness
noncomputable section
open Bundle Manifold
open scoped Bundle Manifold ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
def tangentNorm (g : Metric I (M := M)) (x : M) (v : TangentSpace I x) : ℝ :=
  Real.sqrt (g.inner x v v)
def metricEDist (g : Metric I (M := M)) (x y : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y
end
end CKSReplacementCompleteness

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

abbrev stdBasis : Module.Basis (Fin 2) ℝ E := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def pullbackInner (g : Metric (M := M)) (x : M) (y : E) : LinearMap.BilinForm ℝ E :=
  (g.inner ((extChartAt I x).symm y)).toBilinForm.comp
    (chartFrame x y).toLinearMap (chartFrame x y).toLinearMap

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem real_id_compTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance
attribute [local instance] real_id_compTriple

def chartTransition (x z : M) : E → E := (extChartAt I x) ∘ (extChartAt I z).symm

def transitionDeriv (x z : M) (y : E) : E →L[ℝ] E :=
  (mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp (chartFrame z y)

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable [MeasurableSpace M] [BorelSpace M]

def chartPreimage (x : M) (s : Set M) : Set E :=
  (extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma velocity_far (m r : ℝ) (hr : 2*m+2 ≤ r) : velocity m r = r := by
  rw [velocity,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ r-2*m-1)]
  ring

end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCKSAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle CKSLorentz CKSMixedGeometry
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma velocity_deriv_far (m r : ℝ) (hr : 2*m+2 < r) : deriv (velocity m) r = 1 := by
  have h : velocity m =ᶠ[𝓝 r] id := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact velocity_far m s hs.le
  rw [h.deriv_eq]
  exact deriv_id r
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SchwarzschildCKSDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSMixedGeometry
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma tail_inverse_small {m r : ℝ} (hm : 0 < m) (hr : 4*m+4 ≤ r) :
    r⁻¹ ∈ Icc 0 (1/(4*m+4)) := by
  have hD : 0 < 4*m+4 := by positivity
  exact ⟨inv_nonneg.mpr (hD.le.trans hr),by simpa only [one_div] using (inv_le_inv₀ (hD.trans_le hr) hD).mpr hr⟩
end CKSSchwarzschild

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceMapDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff
namespace CKSSurfaceVolume
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H N] [IsManifold I 1 M] [IsManifold I 1 N]

def mapChart (f : M → N) (x : M) (y : N) : E → E :=
  (extChartAt I y) ∘ f ∘ (extChartAt I x).symm

def mapChartDeriv (f : M → N) (x : M) (y : N) (z : E) : E →L[ℝ] E :=
  (mfderiv I I (extChartAt I y) (f ((extChartAt I x).symm z))).comp
    ((mfderiv I I f ((extChartAt I x).symm z)).comp (chartFrame x z))

def mapPullbackInner (h : Metric (M := N)) (f : M → N) (x : M) (z : E) :
    LinearMap.BilinForm ℝ E :=
  (h.inner (f ((extChartAt I x).symm z))).toBilinForm.comp
    ((mfderiv I I f ((extChartAt I x).symm z)).comp (chartFrame x z)).toLinearMap
    ((mfderiv I I f ((extChartAt I x).symm z)).comp (chartFrame x z)).toLinearMap

end CKSSurfaceVolume

end

end OAI
end

section
-- module Solutions.Q227_CKS.Relativity_CKS_SurfaceScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
local instance instNormedAddCommGroupContinuousLinearMapRealIdE : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance instNormedSpaceRealContinuousLinearMapIdE : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

end CKSSurfaceVolume

end

end OAI
end


