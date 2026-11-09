-- Prove2me | Definitions.Def_PersuasionByParts_Known_Model
-- name    : PersuasionByParts_Known_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:38.724804+00:00
-- url     : https://prove2.me/theorems/bedd9d62-f528-4f2f-b352-2c782aa20a1e
-- title:
--   Product priors, arbitrary-signal experiments and persuasion values
-- statement:
--   Let $n\ge1$. A product prior consists of Borel probability measures $P_i$ on $\mathbb R$, each satisfying $\int |x|\,dP_i(x)<\infty$. Write $P=\bigotimes_iP_i$ and $X(x)=\sum_i x_i$. A decision function $g:\mathbb R\to[0,1]$ is measurable and nondecreasing. A joint experiment is any Markov kernel from $\mathbb R^n$ to an arbitrary measurable signal space. A product experiment consists of coordinate kernels, with independent private randomness. Its signal law is the product of the coordinate signal laws.
--
--   For a joint experiment, $Y_\Pi=\mathbb E[X\mid S]$. For a product experiment, $Y_\Pi=\sum_i\mathbb E[X_i\mid S_i]$. Define
--
--   $$V_\Pi(g)=\mathbb E[g(Y_\Pi)],\qquad V_{\rm joint}(g)=\sup_{\Pi\text{ joint}}V_\Pi(g),\qquad V_{\rm prod}(g)=\sup_{\Pi\text{ product}}V_\Pi(g).$$
--
--   For a real cutoff $t$, use $g(y)=\mathbf1_{y\ge t}$. The experiment classes have concrete full-revelation members. No optimizer, desired inequality or additional state regularity enters admissibility. This model is the operational basis shared by every result in this mission.
--
--   **Formalization Note** Coordinates use `Fin n`, with positivity in the theorem binders. Decision functions are real functions with explicit range bounds. Signal spaces range over arbitrary small measurable types. Mathlib posterior kernels represent conditional means up to signal-null sets. The generic scalar posterior helper is imported from the published mechanism definition; its separate `IsState` predicate is not used. The vector posterior and product aggregation are defined locally.
-- source:
--   Shuyuan Jia, Kangning Wang, Renzhe Xu, Persuasion by Parts, STOC 2027 submission #314 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/314.pdf, printed pp. 1–2 / PDF pp. 2–3, §1.1 and Definition 1.1

import Mathlib
import Definitions.Def_PersuasionNetworks_Mechanism

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

namespace PersuasionByParts.Known

/-- Section 1.1: arbitrary integrable real marginal laws. Positivity of n is a theorem binder. -/
structure Prior (n : ℕ) where
  marginal : Fin n → Measure ℝ
  probability : ∀ i, IsProbabilityMeasure (marginal i)
  finiteMean : ∀ i, Integrable id (marginal i)

attribute [instance] Prior.probability

def priorLaw {n : ℕ} (P : Prior n) : Measure (Fin n → ℝ) :=
  Measure.pi P.marginal

instance {n : ℕ} (P : Prior n) : IsProbabilityMeasure (priorLaw P) := by
  unfold priorLaw
  infer_instance

def total {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i

def sumLaw {n : ℕ} (P : Prior n) : Measure ℝ := (priorLaw P).map total

def others {n : ℕ} (i : Fin n) (x : Fin n → ℝ) : ℝ := ∑ j ∈ Finset.univ.erase i, x j

def othersLaw {n : ℕ} (P : Prior n) (i : Fin n) : Measure ℝ :=
  (priorLaw P).map (others i)

/-- Includes discontinuous nondecreasing functions and both constant functions. -/
structure Decision where
  toFun : ℝ → ℝ
  measurable : Measurable toFun
  monotone : Monotone toFun
  range : ∀ y, toFun y ∈ Icc 0 1

instance : CoeFun Decision (fun _ => ℝ → ℝ) := ⟨Decision.toFun⟩

def cutoff (t : ℝ) (y : ℝ) : ℝ := if t ≤ y then 1 else 0

/-- All small measurable signal spaces, with an actual Markov kernel from the full vector. -/
structure JointExperiment (n : ℕ) where
  Signal : Type
  signalSpace : MeasurableSpace Signal
  kernel : @Kernel (Fin n → ℝ) Signal inferInstance signalSpace
  markov : @IsMarkovKernel (Fin n → ℝ) Signal inferInstance signalSpace kernel

attribute [instance] JointExperiment.signalSpace JointExperiment.markov

/-- Coordinate kernels run independently; the signal law below is their product. -/
structure ProductExperiment (n : ℕ) where
  Signal : Fin n → Type
  signalSpace : ∀ i, MeasurableSpace (Signal i)
  kernel : ∀ i, @Kernel ℝ (Signal i) inferInstance (signalSpace i)
  markov : ∀ i, @IsMarkovKernel ℝ (Signal i) inferInstance (signalSpace i) (kernel i)

attribute [instance] ProductExperiment.signalSpace ProductExperiment.markov

def jointSignalLaw {n : ℕ} (P : Prior n) (E : JointExperiment n) : Measure E.Signal :=
  E.kernel ∘ₘ priorLaw P

/-- Disintegration of the joint state-signal law: E[sum_i X_i | S=s]. -/
def jointPosterior {n : ℕ} (P : Prior n) (E : JointExperiment n) (s : E.Signal) : ℝ :=
  ∫ x, total x ∂(posterior E.kernel (priorLaw P) s)

def productSignalLaw {n : ℕ} (P : Prior n) (E : ProductExperiment n) :
    Measure (∀ i, E.Signal i) :=
  Measure.pi (fun i => E.kernel i ∘ₘ P.marginal i)

/-- The paper's additive posterior, using the published scalar conditional-mean helper. -/
def productPosterior {n : ℕ} (P : Prior n) (E : ProductExperiment n)
    (s : ∀ i, E.Signal i) : ℝ :=
  ∑ i, PersuasionNetworks.posteriorMean (P.marginal i) (E.kernel i) (s i)

def jointPayoff {n : ℕ} (P : Prior n) (E : JointExperiment n) (g : ℝ → ℝ) : ℝ :=
  ∫ s, g (jointPosterior P E s) ∂jointSignalLaw P E

def productPayoff {n : ℕ} (P : Prior n) (E : ProductExperiment n) (g : ℝ → ℝ) : ℝ :=
  ∫ s, g (productPosterior P E s) ∂productSignalLaw P E

/-- These sets contain only actual experiment payoffs; no optimum is supplied. -/
def jointPayoffs {n : ℕ} (P : Prior n) (g : ℝ → ℝ) : Set ℝ :=
  {v | ∃ E : JointExperiment n, v = jointPayoff P E g}

def productPayoffs {n : ℕ} (P : Prior n) (g : ℝ → ℝ) : Set ℝ :=
  {v | ∃ E : ProductExperiment n, v = productPayoff P E g}

def jointValue {n : ℕ} (P : Prior n) (g : ℝ → ℝ) : ℝ := sSup (jointPayoffs P g)

def productValue {n : ℕ} (P : Prior n) (g : ℝ → ℝ) : ℝ := sSup (productPayoffs P g)

def jointCutoff {n : ℕ} (P : Prior n) (t : ℝ) : ℝ := jointValue P (cutoff t)

def productCutoff {n : ℕ} (P : Prior n) (t : ℝ) : ℝ := productValue P (cutoff t)

/-- Concrete witnesses that the admissible experiment classes are nonempty. -/
def jointRevelation (n : ℕ) : JointExperiment n where
  Signal := Fin n → ℝ
  signalSpace := inferInstance
  kernel := Kernel.id
  markov := inferInstance

def productRevelation (n : ℕ) : ProductExperiment n where
  Signal := fun _ => ℝ
  signalSpace := fun _ => inferInstance
  kernel := fun _ => Kernel.id
  markov := fun _ => inferInstance

end PersuasionByParts.Known


