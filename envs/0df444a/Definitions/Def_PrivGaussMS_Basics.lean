-- Prove2me | Definitions.Def_PrivGaussMS_Basics
-- name    : PrivGaussMS_Basics
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:04.555758+00:00
-- url     : https://prove2.me/theorems/cc435b8e-d291-42a3-ae47-8f3d76398e49
-- title:
--   Measurable structures on matrices, partial batches and index sets; $Q_P$, $\mathrm{Lap}(b)$, $\mathrm{clip}_\ell$, $\chi^2_h$ and $(\varepsilon,\delta)$-DP for families of laws
-- statement:
--   This file fixes the measure-theoretic setting of the mission.
--
--   1. Real matrices $\mathbb R^{r\times d}$ carry the product Borel $\sigma$-algebra of their entries and Lebesgue measure on the entries (the reference measure of every matrix density in the paper).
--   2. A **partial batch** has $m$ ordered positions, each holding a vector of $\mathbb R^d$ or a blank $\star$; the all-blank tuple $\star^m$ is the empty partial batch. The blank is a measurable atom. Finite index sets $A\subseteq[n]$ carry the discrete $\sigma$-algebra.
--   3. The target law of one output is
--   $$Q_P=(1-\eta)P+\eta\,\mathcal N(0,I_d),\qquad P=\mathcal N(\mu,\Sigma).$$
--   4. $\mathrm{Lap}(b)$ has density $e^{-|z|/b}/(2b)$ on $\mathbb R$, $\mathrm{clip}_\ell(z)=\max\{-\ell,\min\{z,\ell\}\}$, and $\chi^2_h$ is the law of a sum of $h$ squared independent standard Gaussians. Independent uniform draws on $[0,1]$ implement every Bernoulli choice.
--   5. A mechanism given by its output laws $x\mapsto M(x)$ is $(\varepsilon,\delta)$-differentially private when every $M(x)$ is a probability measure and, for all datasets $x,x'$ of the same size differing in one record and every measurable event $E$, $M(x)(E)\le e^{\varepsilon}M(x')(E)+\delta$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** DP is the published `PrivateUniformGen.Characterization.IsDP` (replacement neighbours); the wrapper only adds that each output law is a probability measure, so that a non-measurable output (pushed to the zero measure) cannot satisfy DP vacuously.
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Appendix A.1 notation, p.23; Definition 1.1, p.3; DP paragraph, p.24; Theorem B.1 eq. (10), p.32; Lemma A.4, p.25; partial batches, p.32

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Privacy

open MeasureTheory ProbabilityTheory

namespace PrivGaussMS

/-!
# Measurable structures, the target law `Q_P`, Laplace noise, clipping and `χ²_h`

R. Z. Moayedi, M. H. Yassaee, J. B. Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027
submission (manuscript sha256 1838c582…), Appendix A.1 notation, p.23; Definition 1.1, p.3; the DP
paragraph, p.24; Theorem B.1, eq. (10), p.32; Lemma A.4, p.25.

**Formalization Note.**
* Real matrices `Matrix m n ℝ` carry the product Borel σ-algebra of their entries and, for finite
  index types, Lebesgue measure on the entries ("Lebesgue density on `ℝ^{r×d}`", p.29). Mathlib
  provides neither instance for `Matrix`.
* `Option α` (a vector or the blank `⋆ = none`, p.32) carries the σ-algebra transported from
  `α ⊕ Unit`, so the blank is a measurable atom. `Finset (Fin n)` (the set `A` drawn by Procedure 5)
  carries the discrete σ-algebra.
* `IsDPM` applies the published `PrivateUniformGen.Characterization.IsDP` to a mechanism given as a
  family of measures: it asserts that every output law is a probability measure and that the
  induced `ProbabilityMeasure`-valued mechanism is `(ε, δ)`-DP. It adds no condition to DP.
-/

/-- Product Borel σ-algebra on the entries of a real matrix. -/
instance instMeasurableSpaceMatrix {m n : Type*} : MeasurableSpace (Matrix m n ℝ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℝ))

/-- The product σ-algebra on matrices is the Borel σ-algebra of the entrywise topology. -/
instance instBorelSpaceMatrix {m n : Type*} [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℝ) :=
  inferInstanceAs (BorelSpace (m → n → ℝ))

/-- Lebesgue measure on the entries of a real matrix (`ℝ^{r×d}` in the paper). -/
noncomputable instance instMeasureSpaceMatrix {m n : Type*} [Fintype m] [Fintype n] :
    MeasureSpace (Matrix m n ℝ) where
  volume := Measure.pi fun _ : m => Measure.pi fun _ : n => (volume : Measure ℝ)

/-- The σ-algebra on `Option α` transported from `α ⊕ PUnit`: `none` (the blank `⋆`) is an atom. -/
instance instMeasurableSpaceOption {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0} α) inferInstance

/-- The discrete σ-algebra on finite sets of indices. -/
instance instMeasurableSpaceFinset {α : Type*} : MeasurableSpace (Finset α) := ⊤

/-- A vector of `ℝ^d` with the Euclidean structure (the type `multivariateGaussian` lives on). -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A partial batch (p.32): `m` ordered positions, each holding a vector (`some v`) or the blank
`⋆` (`none`). The all-blank tuple is the empty partial batch. -/
abbrev PartialBatch (m d : ℕ) := Fin m → Option (Vec d)

/-- The empty partial batch `⋆^m`. -/
def emptyBatch (m d : ℕ) : PartialBatch m d := fun _ => none

/-- The fixed replacement law `R = N(0, I_d)` (p.31). -/
noncomputable def replLaw (d : ℕ) : Measure (Vec d) := multivariateGaussian 0 1

/-- `Q_P = (1 − η) P + η N(0, I_d)` for `P = N(µ, Σ)` (eq. (10), p.32). -/
noncomputable def QP {d : ℕ} (μ : Vec d) (Sig : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :
    Measure (Vec d) :=
  ENNReal.ofReal (1 - η) • multivariateGaussian μ Sig + ENNReal.ofReal η • replLaw d

/-- `Q_P` is a finite measure (needed to form products `Q_P^{⊗m}`). -/
instance instIsFiniteMeasureQP {d : ℕ} (μ : Vec d) (Sig : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :
    IsFiniteMeasure (QP μ Sig η) := by
  constructor
  simp only [QP, replLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

/-- `(ε, δ)`-differential privacy (Definition 1.1, p.3) for a mechanism given by its output laws:
every output law is a probability measure and the induced mechanism satisfies the published
`PrivateUniformGen.Characterization.IsDP` (replacement neighbours, every measurable event). -/
def IsDPM {X Y : Type*} [MeasurableSpace Y] {n : ℕ} (M : (Fin n → X) → Measure Y)
    (ε δ : ℝ) : Prop :=
  ∃ h : ∀ x, IsProbabilityMeasure (M x),
    PrivateUniformGen.Characterization.IsDP (fun x => ⟨M x, h x⟩) ε δ

/-- The Laplace law `Lap(b)` with density `e^{−|z|/b}/(2b)` (Lemma A.4, p.25). -/
noncomputable def laplace (b : ℝ) : Measure ℝ :=
  volume.withDensity fun z => ENNReal.ofReal (Real.exp (-|z| / b) / (2 * b))

/-- `clip_ℓ(z) = max{−ℓ, min{z, ℓ}}` (Lemma A.4, p.25; Algorithm 4, line 3, p.40). -/
noncomputable def clip (ℓ z : ℝ) : ℝ := max (-ℓ) (min z ℓ)

/-- The uniform law on `[0, 1]`; an independent uniform draw implements every Bernoulli choice
(omission with probability `η`, the decision probability (28)). -/
noncomputable def unif01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- `m` independent uniform `[0, 1]` draws. -/
noncomputable def coins (m : ℕ) : Measure (Fin m → ℝ) := Measure.pi fun _ : Fin m => unif01

/-- `χ²_h`: the law of a sum of `h` squared independent standard Gaussians (p.23). -/
noncomputable def chiSq (h : ℕ) : Measure ℝ :=
  (Measure.pi fun _ : Fin h => gaussianReal 0 1).map fun g => ∑ i, g i ^ 2

end PrivGaussMS


