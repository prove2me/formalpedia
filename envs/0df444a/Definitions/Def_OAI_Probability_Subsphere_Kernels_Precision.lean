-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
-- name    : OAI_Probability_Subsphere_Kernels_Precision
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:42:45.353432+00:00
-- url     : https://prove2.me/theorems/13f2173c-7155-40d7-988b-5e8d31393bbd
-- title:
--   Measurable versions of transition kernels, inverse-CDF sampling and the random-tape form of a kernel learner
-- statement:
--   Fix $d,M,T\in\mathbb{N}$, let $Q_M=\{0,\dots,2^M-1\}$ and let $S^{d-1}$ be the unit sphere of $\mathbb{R}^d$. A *kernel learner* $L$ has an initial distribution $\pi_0$ on $\{0,1\}\times Q_M$, transition kernels $P_t(q;x,y)$ (distributions on $\{0,1\}\times Q_M$, for $t\in\mathbb{N}$, $q\in Q_M$ and observations $(x,y)\in\mathbb{R}^d\times\mathbb{R}$) and output probability measures $o_{t,q}$ on $S^{d-1}$. Drawing $(1,q)$ at time $t$ means "stop at time $t$ in state $q$" and drawing $(0,q)$ means "continue in state $q$"; accordingly a run status is either *active in $q$* or *stopped with record $(t,q)$*. The observation at step $n+1$ is $(x_n,\langle x_n,s\rangle)$ for the hidden unit vector $s$. Write $\gamma_d=N(0,I_d)$.
--
--   1. **Measurable version of a finite kernel.** Let $X$ be a measurable space with a measure $\mu$, $A$ a finite nonempty set and $p:X\to\Delta(A)$ a map into probability distributions on $A$ such that each $x\mapsto p(x)(\{a\})$ is $\mu$-a.e. measurable. Fix measurable functions $\bar p_a$ equal $\mu$-a.e. to $x\mapsto p(x)(\{a\})$. The measurable version is $\bar p(x)=(\bar p_a(x))_{a\in A}$ at points where $\sum_a\bar p_a(x)=1$, and the point mass at a fixed element of $A$ elsewhere.
--   2. **Borel version of a kernel learner.** If every $(x,y)\mapsto P_t(q;x,y)(\{a\})$ is a.e. measurable for $\gamma_d\otimes\mathrm{Leb}$, the Borel version of $L$ replaces each kernel $P_t(q;\cdot)$ by its measurable version with respect to $\gamma_d\otimes\mathrm{Leb}$, keeping $\pi_0$ and the outputs.
--   3. **Inverse-CDF sampling.** For a distribution $p$ on $\{0,\dots,n-1\}$ let $F_p(k)=\sum_{j<\min(k,n)}p(j)$ for $k\in\mathbb{N}$. For $n\ge1$ and $r\in\mathbb{R}$, $\mathrm{sample}(p,r)$ is the index $i$ with
--   $$F_p(i)\le r<F_p(i+1)$$
--   if one exists, and $0$ otherwise. The coin law is Lebesgue measure on $[0,1)$, a probability measure. For a finite nonempty set $A$, sampling is transported along a fixed enumeration of $A$.
--   4. **Chains.** For a set $A$, maps $F_n:A\times\mathbb{R}\to A$ and $a\in A$, the deterministic chain driven by $r=(r_0,\dots,r_{n-1})$ is $a_0=a$, $a_{k+1}=F_k(a_k,r_k)$. For kernels $K_n$ from $A$ to distributions on $A$, the law chain is $\mathcal L_0=\delta_a$, $\mathcal L_{n+1}(c)=\sum_b\mathcal L_n(b)\,K_n(b)(\{c\})$.
--   5. **Tape form of a kernel learner.** An output tape is a function $\tau:\mathbb{N}\times Q_M\to S^{d-1}$; a tape is a triple $\omega=(a_0,(r_0,\dots,r_{T-1}),\tau)$ of an initial pair, $T$ coins and an output tape. The tape law is $\pi_0\otimes\mathrm{Unif}[0,1)^{\otimes T}\otimes\bigotimes_{(t,q)}o_{t,q}$, the last factor being the infinite product of the output laws; it is a probability measure. The coin used at time $t$ is $r_{t-1}$ if $t-1<T$ and $0$ otherwise. The tape learner of $L$ is the deterministic seeded learner with seed space the tapes, initial choice $a_0$, transition $(t,\omega,q,(x,y))\mapsto\mathrm{sample}\bigl(P_t(q;x,y),\text{coin at time }t\bigr)$ and output $(t,\omega,q)\mapsto\tau(t,q)$.
--   6. **One-step maps.** For a hidden $s$, samples $x$, time $n$ and status $\alpha$: the one-step law keeps a stopped status, sends an active state $q$ with $n<T$ to $P_{n+1}(q;x_n,\langle x_n,s\rangle)$ (a drawn $(1,q')$ becoming "stopped with record $(n+1,q')$"), and keeps an active status when $n\ge T$; the deterministic step does the same with the draw replaced by $\mathrm{sample}(\cdot,u)$ for a coin $u$. The finishing map sends "active in $q$" to $(T,q)$ and a stopped record $(t,q)$ to itself.
--   7. **Success test and auxiliary facts.** The success test is $\mathbf 1\{\arccos\langle u,s\rangle\le\varepsilon\}$ for $u,s\in S^{d-1}$. Also recorded: a disjoint union of measurable spaces with measurable singletons has measurable singletons; the Gaussian sample law and (for $d\ge1$) the uniform law on $S^{d-1}$ are probability measures; for fixed $s$ and samples $x$, the law of the estimate of a kernel learner is a probability measure; and $(a,(b,c))\mapsto(b,(a,c))$ is a measurable isomorphism $A\times(B\times C)\to B\times(A\times C)$.
--
--   These constructions replace a randomized finite-memory learner whose rules are only almost everywhere measurable by a Borel one, and then by a deterministic seeded learner whose seed is a random tape; inverse-CDF sampling with uniform coins, and the identification of deterministic chains driven by independent coins with Markov chains, are the probabilistic tools behind this derandomization.
--
--   **Formalization Note** Names, in order: `borelPMF`, `KernelLearner.borelVersion`, `finiteCDF`, `finiteSample`, `coinLaw` (with `coinLaw_probability`), `samplePMF` (along `Fintype.equivFin`), `detChain`, `lawChain` (Lean's `PMF.bind`), `KernelLearner.OutputTape`, `KernelLearner.Tape`, `outputTapeLaw` (`Measure.infinitePi`), `tapeLaw`, `tapeCoin`, `asTape` (a `SubsphereRegression.Learner d M T (Tape d M T)`), `stepPMF`, `stepDet`, `finish`, `successTest`, and the instances `sumMeasurableSingletonClass`, `sampleLaw_probability`, `uniformSphere_probability` (under `[NeZero d]`), `estimateLaw_probability`, together with `swapFirstTwo`. In `tapeCoin` the index $t-1$ is truncated subtraction, so $t=0$ also reads $r_0$. The fixed choices in item 1 are Lean's `AEMeasurable.mk` and `Classical.arbitrary`. `detChain` and `lawChain` need no structure on $A$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Kernels/Precision.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Kernels/Precision.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent

section FiniteVersion
variable {X A : Type*} [MeasurableSpace X] [Fintype A] [Nonempty A]
variable {μ : Measure X} (p : X → PMF A)

def borelPMF (hp : ∀ a, AEMeasurable (fun x => p x a) μ) (x : X) : PMF A :=
  if h : ∑ a, (hp a).mk (fun x => p x a) x = 1
  then PMF.ofFintype (fun a => (hp a).mk (fun x => p x a) x) h
  else PMF.pure (Classical.arbitrary A)

end FiniteVersion

namespace KernelLearner

def borelVersion {d M T : ℕ} (L : KernelLearner d M T) (hL : L.CompletedRules) :
    KernelLearner d M T where
  initial := L.initial
  transition t q := borelPMF (L.transition t q) (hL t q)
  output := L.output
  output_probability := L.output_probability

end KernelLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

def finiteCDF {n : ℕ} (p : PMF (Fin n)) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if h : j < n then (p ⟨j,h⟩).toReal else 0

def finiteSample {n : ℕ} [NeZero n] (p : PMF (Fin n)) (r : ℝ) : Fin n :=
  if h : ∃ i : Fin n, finiteCDF p i.val ≤ r ∧ r < finiteCDF p (i.val+1)
  then h.choose else 0

def coinLaw : Measure ℝ := volume.restrict (Ico 0 1)

instance coinLaw_probability : IsProbabilityMeasure coinLaw := by
  constructor
  simp [coinLaw, Real.volume_Ico]

section EquivSampling
variable {A B : Type*}
variable [Fintype A] [Nonempty A]

def samplePMF (p : PMF A) (r : ℝ) : A :=
  letI : NeZero (Fintype.card A) := ⟨Fintype.card_ne_zero⟩
  (Fintype.equivFin A).symm (finiteSample (p.map (Fintype.equivFin A)) r)

end EquivSampling

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

section CountableBind
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]

end CountableBind

section Chain
variable {A : Type*} [MeasurableSpace A] [Countable A] [MeasurableSingletonClass A]

def detChain (F : ℕ → A → ℝ → A) (a : A) : (n : ℕ) → (Fin n → ℝ) → A
  | 0, _ => a
  | n+1, r => F n (detChain F a n (Fin.init r)) (r (Fin.last n))

def lawChain (K : ℕ → A → PMF A) (a : A) : ℕ → PMF A
  | 0 => PMF.pure a
  | n+1 => (lawChain K a n).bind (K n)

end Chain
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section

namespace SubsphereCurrent
instance sumMeasurableSingletonClass {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    MeasurableSingletonClass (A ⊕ B) where
  measurableSet_singleton a := by
    cases a with
    | inl a => simpa only [← Set.image_singleton] using MeasurableSet.inl_image (measurableSet_singleton a)
    | inr b => simpa only [← Set.image_singleton] using MeasurableSet.inr_image (measurableSet_singleton b)

end SubsphereCurrent

namespace SubsphereRegression.Learner
-- [generator] dropped: open SubsphereCurrent (measurable_countable_select)

end SubsphereRegression.Learner

namespace SubsphereCurrent
namespace KernelLearner
abbrev OutputTape (d M : ℕ) := (ℕ × State M) → UnitSphere d
abbrev Tape (d M T : ℕ) := (Bool × State M) × ((Fin T → ℝ) × OutputTape d M)

def outputTapeLaw {d M T : ℕ} (L : KernelLearner d M T) : Measure (OutputTape d M) :=
  Measure.infinitePi (fun a : ℕ × State M => L.output a.1 a.2)

instance outputTapeLaw_probability {d M T : ℕ} (L : KernelLearner d M T) :
    IsProbabilityMeasure L.outputTapeLaw := by
  let : ∀ a : ℕ × State M, IsProbabilityMeasure (L.output a.1 a.2) :=
    fun a => L.output_probability a.1 a.2
  unfold outputTapeLaw
  infer_instance

def tapeLaw {d M T : ℕ} (L : KernelLearner d M T) : Measure (Tape d M T) :=
  L.initial.toMeasure.prod ((Measure.pi (fun _ : Fin T => coinLaw)).prod L.outputTapeLaw)

instance tapeLaw_probability {d M T : ℕ} (L : KernelLearner d M T) :
    IsProbabilityMeasure L.tapeLaw := by unfold tapeLaw; infer_instance

def tapeCoin {d M T : ℕ} (t : ℕ) (ω : Tape d M T) : ℝ :=
  if h : t-1 < T then ω.2.1 ⟨t-1,h⟩ else 0

def asTape {d M T : ℕ} (L : KernelLearner d M T) :
    SubsphereRegression.Learner d M T (Tape d M T) where
  initialChoice := Prod.fst
  transition t ω q obs := samplePMF (L.transition t q obs) (tapeCoin t ω)
  output t ω q := ω.2.2 (t,q)

def stepPMF {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) (n : ℕ) (a : RunStatus M) : PMF (RunStatus M) :=
  match a with
  | .inr done => PMF.pure (.inr done)
  | .inl q => if hn : n < T then
      (L.transition (n+1) q (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)).map (tagged M (n+1))
    else PMF.pure (.inl q)

def stepDet {d M T : ℕ} (L : KernelLearner d M T) (s : UnitSphere d)
    (x : Samples d T) (n : ℕ) (a : RunStatus M) (u : ℝ) : RunStatus M :=
  match a with
  | .inr done => .inr done
  | .inl q => if hn : n < T then
      tagged M (n+1) (samplePMF (L.transition (n+1) q
        (x ⟨n,hn⟩, ⟪x ⟨n,hn⟩,s.val⟫)) u)
    else .inl q

def finish (M T : ℕ) (status : RunStatus M) : ℕ × State M :=
  match status with | .inl q => (T,q) | .inr done => done

end KernelLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u v w
namespace SubsphereCurrent

instance sampleLaw_probability (d T : ℕ) : IsProbabilityMeasure (sampleLaw d T) :=
  SubsphereRegression.sampleLaw_probability d T
instance uniformSphere_probability (d : ℕ) [NeZero d] : IsProbabilityMeasure (uniformSphere d) :=
  SubsphereRegression.uniformSphere_probability d

def swapFirstTwo (A : Type u) (B : Type v) (C : Type w)
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] :
    A × (B × C) ≃ᵐ B × (A × C) :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl C)).trans
      MeasurableEquiv.prodAssoc)

namespace KernelLearner
instance estimateLaw_probability {d M T : ℕ} (L : KernelLearner d M T)
    (s : UnitSphere d) (x : Samples d T) : IsProbabilityMeasure (L.estimateLaw s x) := by
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  exact ae_of_all _ (fun a => L.output_probability a.1 a.2)

def successTest {d : ℕ} (s : UnitSphere d) (ε : ℝ) (u : UnitSphere d) : ℝ≥0∞ :=
  {u | angularError s u ≤ ε}.indicator (fun _ => 1) u

end KernelLearner

namespace SeededLearner
end SeededLearner
end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace SubsphereCurrent

end SubsphereCurrent
end
end

end OAI


