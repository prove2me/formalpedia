-- Prove2me | Definitions.Def_SpatialHalfspace_FullLabels_Learning
-- name    : SpatialHalfspace_FullLabels_Learning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:21:20.063195+00:00
-- url     : https://prove2.me/theorems/df41d99a-6a81-4b2f-b9d4-5e475f3a5ad4
-- title:
--   Definition 2.4 — fixed-marginal environments, risk, input models and $\mathrm{OptBM}_p$
-- statement:
--   Features lie in $\mathbb R^D$ and labels in $\{0,1\}$. The comparison class is $H_D=\{h_w: x\mapsto 1\{\langle w,x\rangle>0\}: w\in\mathbb R^D\}$ (all $w$, including $w=0$).
--
--   For a law $P$ on $\mathbb R^D\times\{0,1\}$ and a classifier $h$, the **risk** is $R_P(h)=\Pr_{(X,Y)\sim P}[h(X)\ne Y]$ and the **optimal halfspace risk** is $R^*_P(H_D)=\inf_{w\in\mathbb R^D}R_P(h_w)$. For a tuple $(P_u)_{u\in U}$ of local laws, the population is the equal mixture $\bar P=\frac1n\sum_u P_u$, $n=|U|$.
--
--   Given feature marginals $\mu=(\mu_u)_{u\in U}$, the **fixed-marginal environment** is
--
--   $$\mathcal E(\mu)=\{(P_u)_{u\in U}: P_u \text{ a probability law with feature marginal } \mu_u\},$$
--
--   with arbitrary conditional label distributions (eq. (5)).
--
--   **Input models.** In the *sample model*, terminal $u$ holds an infinite i.i.d. sequence of examples from $P_u$, independent across terminals. In the *exact-kernel model*, terminal $u$ holds $\eta_{u,x}=P_u(Y=1\mid X=x)$ for every atom $x$ of $\mu_u$.
--
--   **Learners.** A learner is a protocol whose root output is a binary classifier evaluable at the root from its final state; it is *proper* if that classifier lies in $H_D$ on every execution. It achieves $(\varepsilon,1-\delta)$ on a family $\mathcal F\subseteq\mathcal E(\mu)$ if for every $P\in\mathcal F$ it is legal and
--
--   $$\Pr\big[R_{\bar P}(\hat h)\le R^*_{\bar P}(H_D)+\varepsilon\big]\ \ge\ 1-\delta .$$
--
--   **Optimal cost (Definition 2.4).**
--
--   $$\mathrm{OptBM}^{\mathrm{prop}}_p(H_D,\mathcal F,\varepsilon,\delta)=\inf_{G,\Pi}\ \sup_{P\in\mathcal F}\mathrm{BM}_G(\Pi;P),$$
--
--   the infimum over $p$-dimensional substrates $G$ and proper learners $\Pi$ achieving $(\varepsilon,1-\delta)$ on $\mathcal F$; $\mathrm{OptBM}^{\mathrm{imp}}_p$ is the same with arbitrary measurable classifiers allowed as outputs (same benchmark $R^*$). The infimum of the empty set is $+\infty$.
--
--   The sample model requires each invocation of a local send, halt, finalization, or root-output operation to depend on a finite prefix of its terminal's sample stream. This prefix length may depend on the local execution; it imposes no uniform sample bound. Together with almost-sure finite halting, this permits adaptive sampling and excludes infinite-sample oracles. `InputModel` packages the input law and this local access rule; exact kernels are supplied as complete local inputs.
--
--   A learner **uses at most $N$ samples per terminal** if every transmitted symbol and the root's classifier depend on each terminal's sequence only through its first $N$ examples.
--
--   **Formalization Note** $H_D$, $h_w$ and $\mathbb R^D$ are reused from the published `UnderstandingML_Linear` definition (strict inequality, $w=0$ allowed); labels are `Bool`. The i.i.d. sequences use Mathlib's infinite product measure. In the exact-kernel model the input is the function $x\mapsto P_u(Y=1\mid X=x)$ on atoms of the marginal and $0$ elsewhere; since $\mu$ is known, the values off the support carry no information. A learner must have measurable transcripts and a root classifier jointly measurable in (inputs, tapes, feature vector), the standing measurability convention that makes risks, success probabilities and expected costs well defined. `OptBM` is an extended nonnegative real.
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 5, PDF p. 6, §1.1 eq. (1) and risk definitions, PDF p. 2; §2.1 eq. (5), PDF p. 6; Definition 2.4 and the exact-kernel model, eqs. (8)–(9), PDF p. 7

import Definitions.Def_SpatialHalfspace_FullLabels_Protocol
import Definitions.Def_UnderstandingML_Linear

/-!
# Fixed-marginal environments, risk, and the optimal learning cost
(Yang, STOC 2027 submission #119, §1.1, §2.1 eq. (5), Definition 2.4, printed pp. 1, 5–6)

* Features live in `ℝ^D` (`UnderstandingML.Vec D`), labels in `Bool` (`false`/`true` = `0`/`1`).
  `H_D` is `UnderstandingML.homHalfspaces D = {x ↦ 1{⟨w, x⟩ > 0} : w ∈ ℝ^D}` (all `w`, `w = 0`
  included).
* `risk P h = Pr_{(X,Y)∼P}[h(X) ≠ Y]`, `optRisk P = inf_{w ∈ ℝ^D} risk P h_w`.
* `env μ = E(μ)`: all tuples `(P_u)` of probability laws on `ℝ^D × {0,1}` with feature marginals
  `μ_u`; the population is the equal mixture `P̄ = (1/n) ∑_u P_u`.
* Input models: in the **sample model** terminal `u` holds an i.i.d. sequence of examples from
  `P_u` (independent across terminals); in the **exact-kernel model** terminal `u` holds
  `x ↦ P_u(Y = 1 | X = x)` on the atoms of its marginal (and `0` elsewhere).
* `OptBM p D model proper F ε δ = inf_{G, Π} sup_{P ∈ F} BM_G(Π; P)` over `p`-dimensional
  substrates and legal protocols whose root output (a classifier evaluable from the root's final
  state; a halfspace on every execution if `proper`) has excess risk at most `ε` with
  probability at least `1 − δ` for every `P ∈ F`.
-/

namespace SpatialHalfspace.FullLabels

open MeasureTheory UnderstandingML
open scoped ENNReal

/-- A labelled example `(x, y) ∈ ℝ^D × {0, 1}`. -/
abbrev Example (D : ℕ) := Vec D × Bool

variable {D : ℕ}

/-- The classification risk `R_P(h) = Pr_{(X,Y) ∼ P}[h(X) ≠ Y]`. -/
noncomputable def risk (P : Measure (Example D)) (h : Vec D → Bool) : ℝ :=
  (P {z | h z.1 ≠ z.2}).toReal

/-- The optimal halfspace risk `R*_P(H_D) = inf_{w ∈ ℝ^D} R_P(h_w)`. -/
noncomputable def optRisk (P : Measure (Example D)) : ℝ :=
  ⨅ w : Vec D, risk P (halfspace w 0)

/-- `P(Y = 1 | X = x)` for an atom `x` of the feature marginal of `P`. -/
noncomputable def condProbOne (P : Measure (Example D)) (x : Vec D) : ℝ :=
  (P {(x, true)}).toReal / (P ({x} ×ˢ Set.univ)).toReal

/-- The equal mixture `P̄ = (1/n) ∑_u P_u` of a tuple of local laws. -/
noncomputable def mixture {U : Type} [Fintype U] (P : U → Measure (Example D)) :
    Measure (Example D) :=
  ((Fintype.card U : ℝ≥0∞)⁻¹) • ∑ u, P u

/-- Equation (5): the fixed-marginal environment `E(μ)`. -/
def env {U : Type} (μ : U → Measure (Vec D)) : Set (U → Measure (Example D)) :=
  {P | ∀ u, IsProbabilityMeasure (P u) ∧ (P u).map Prod.fst = μ u}

/-- Input of a terminal in the sample model: an infinite sequence of examples. -/
abbrev SampleInp (D : ℕ) := ℕ → Example D

/-- A local operation inspects only finitely many samples on each invocation. The number may
depend on the sample sequence and all other local arguments. No uniform sample bound is imposed. -/
def FiniteSampleFunction {Out : Type} (f : SampleInp D → Out) : Prop :=
  ∀ s, ∃ n : ℕ, ∀ s', (∀ i, i < n → s i = s' i) → f s = f s'

/-- The send, halt, finalization and root-output operations use finite sample prefixes. Together with
almost-sure finite halting this models an adaptive sample-based learner; it does not grant free
access to a statistic of an entire infinite sample stream. -/
def Protocol.FiniteSampleAccess {p : ℕ} {U : Type} {S : Substrate p U} {Out : Type}
    (P : Protocol S (SampleInp D) Out) : Prop :=
  (∀ v w k R hist, FiniteSampleFunction fun s => P.send v w k (some s) R hist) ∧
  (∀ v k R hist, FiniteSampleFunction fun s => P.halt v k (some s) R hist) ∧
  (∀ v R hist, FiniteSampleFunction fun s => P.finish v (some s) R hist) ∧
  (∀ R st, FiniteSampleFunction fun s => P.output (some s, R, st))

/-- An input model supplies the input laws and the operational local-input access rule.
Exact kernels are given as complete local inputs; sampled examples may only be requested in
finite prefixes on each local operation. -/
structure InputModel (D : ℕ) (U Inp : Type) [MeasurableSpace Inp] where
  law : (U → Measure (Example D)) → Measure (U → Inp)
  localAccess : ∀ {p : ℕ} (S : Substrate p U), Protocol S Inp (Vec D → Bool) → Prop

instance {U Inp : Type} [MeasurableSpace Inp] :
    CoeFun (InputModel D U Inp) (fun _ => (U → Measure (Example D)) → Measure (U → Inp)) :=
  ⟨InputModel.law⟩

/-- The law of an i.i.d. sequence of examples from `Q` (Mathlib's infinite product measure;
it is the zero measure if `Q` is not a probability measure, which never occurs in `E(μ)`). -/
noncomputable def iidStream (Q : Measure (Example D)) : Measure (SampleInp D) :=
  Measure.infinitePi fun _ : ℕ => Q

/-- The sample model: independent i.i.d. example sequences at the terminals. -/
noncomputable def sampleModel {U : Type} : InputModel D U (SampleInp D) where
  law P := Measure.infinitePi fun u => iidStream (P u)
  localAccess _ P := P.FiniteSampleAccess

/-- Input of a terminal in the exact-kernel model: its conditional label probabilities. -/
abbrev KernelInp (D : ℕ) := Vec D → ℝ

/-- The exact kernel `x ↦ P_u(Y = 1 | X = x)` on the atoms of the marginal, `0` elsewhere. -/
noncomputable def kernelOf (Q : Measure (Example D)) : KernelInp D := by
  classical
  exact fun x => if Q ({x} ×ˢ Set.univ) = 0 then 0 else condProbOne Q x

/-- The exact-kernel model: terminal `u` is given `kernelOf (P u)` (deterministically). -/
noncomputable def kernelModel {U : Type} : InputModel D U (KernelInp D) where
  law P := Measure.dirac fun u => kernelOf (P u)
  localAccess _ _ := True

namespace Protocol

variable {p : ℕ} {U : Type} [Fintype U] {S : Substrate p U} {Inp : Type} [MeasurableSpace Inp]
  (P : Protocol S Inp (Vec D → Bool))

/-- The learner is well formed: transcripts are measurable, the root classifier is jointly
measurable in (inputs, tapes, feature vector) — so each output is a measurable classifier — and,
if `proper`, the root outputs a homogeneous halfspace on every execution. -/
structure IsLearner (proper : Bool) : Prop where
  measurableTranscripts : P.MeasurableTranscripts
  measurable_output : Measurable fun q : ((U → Inp) × P.Tape) × Vec D => P.rootOutput q.1.1 q.1.2 q.2
  proper_output : proper = true → ∀ x R, P.rootOutput x R ∈ homHalfspaces D

/-- The executions on which the root's classifier has excess risk at most `ε` under `Pt`. -/
def successSet (Pt : U → Measure (Example D)) (ε : ℝ) : Set ((U → Inp) × P.Tape) :=
  {xR | risk (mixture Pt) (P.rootOutput xR.1 xR.2) ≤ optRisk (mixture Pt) + ε}

/-- For every `Pt ∈ F`, the protocol is legal for the input law `model Pt` and its output has
excess risk at most `ε` with probability at least `conf`. -/
structure Achieves (model : InputModel D U Inp)
    (F : Set (U → Measure (Example D))) (ε conf : ℝ) : Prop where
  local_access : model.localAccess S P
  legal : ∀ Pt ∈ F, P.Legal (model Pt)
  success : ∀ Pt ∈ F, ENNReal.ofReal conf ≤ ((model Pt).prod P.tapeLaw) (P.successSet Pt ε)

/-- The worst-case bit-meter cost `sup_{P ∈ F} BM_G(Π; P)`. -/
noncomputable def worstBM (model : (U → Measure (Example D)) → Measure (U → Inp))
    (F : Set (U → Measure (Example D))) : ℝ≥0∞ :=
  ⨆ Pt ∈ F, P.BM (model Pt)

/-- The learner uses at most `n` samples per terminal: every transmitted symbol and the root's
classifier depend on each terminal's sequence only through its first `n` examples. -/
def UsesSamples (P : Protocol S (SampleInp D) (Vec D → Bool)) (n : ℕ) : Prop :=
  ∀ (x x' : U → SampleInp D) (R : P.Tape), (∀ u i, i < n → x u i = x' u i) →
    (∀ w v k, P.sym x R w v k = P.sym x' R w v k) ∧ P.rootOutput x R = P.rootOutput x' R

end Protocol

/-- Definition 2.4: `OptBM_p^prop` (`proper = true`) and `OptBM_p^imp` (`proper = false`) for the
family `F`, in the input model `model` (sample or exact-kernel), with terminal set `U`. -/
noncomputable def OptBM (p : ℕ) {U : Type} [Fintype U] (Inp : Type) [MeasurableSpace Inp]
    (model : InputModel D U Inp) (proper : Bool)
    (F : Set (U → Measure (Example D))) (ε δ : ℝ) : ℝ≥0∞ :=
  ⨅ (S : Substrate p U) (P : Protocol S Inp (Vec D → Bool)) (_ : P.IsLearner proper)
    (_ : P.Achieves model F ε (1 - δ)), P.worstBM model F

end SpatialHalfspace.FullLabels


