-- Prove2me | Definitions.Def_CondGeoVerif_OneMsgVerifier
-- name    : CondGeoVerif_OneMsgVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:28:22.340854+00:00
-- url     : https://prove2.me/theorems/6afa3b87-85b9-4db5-941b-fdcab3f2a2fe
-- title:
--   One-message verifiers, sample-only honest provers, soundness, Massart completeness, properness
-- statement:
--   A **one-message verifier** in dimension $d$ receives one prover message, sent before it draws a private sample of $m_V$ labeled observations; from the message, the sample and its own coins (from an arbitrary probability space) it outputs a predictor or rejects. A **sample-only honest prover** draws $m_P$ labeled observations of its own, independent of the verifier's, and maps them and its coins to a message; it sees the law only through its samples.
--
--   For a class $\mathcal H$, accuracy $\varepsilon$ and confidence $\delta$ (Definition 2.1):
--   1. **Arbitrary-label Gaussian soundness**: for every law with Gaussian feature marginal and any labels, and every message, the probability that the verifier outputs some $h$ with $R_P(h)>\mathrm{OPT}_P(\mathcal H)+\varepsilon$ is at most $\delta$.
--   2. **Full Massart completeness** with noise bound $\eta$: for every such law satisfying (2.1) around some target $h^*\in\mathcal H$, the honest prover's message makes the verifier output some $h$ with $R_P(h)\le\mathrm{OPT}_P(\mathcal H)+\varepsilon$ with probability at least $1-\delta$.
--   3. **Properness** with rule alphabet $F_0$: every output is $x\mapsto f(W^\top x)$ with $f\in F_0$ and an orthonormal $W$.
--
--   A **frame message** carries a frame with at most $N$ columns; a verifier **checks the frame** if it rejects every message whose frame is not orthonormal.
--
--   **Formalization Note** Soundness is required for every fixed message, which covers every prover strategy, including one that knows the law, since a random message is a mixture of fixed ones. For each message the decision is measurable (acceptance in sample and coins, the output predictor jointly in sample, coins and feature), and completeness also requires the honest run to be jointly measurable, so every probability of Definition 2.1 is defined. The prover's sample, the prover's coins, the verifier's sample and the verifier's coins are independent; the honest prover is fixed before the law.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §2, p.3 (PDF p.6), Definition 2.1; §A.1, p.13 (PDF p.16); §A.6, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_CondGeoVerif_risk

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory ProjLikeRetr.Stiefel

/-- A **one-message verifier** in ambient dimension `d` with message type `Msg` (Chen, *The
Conditional Geometry of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…,
§2 "Samples, messages, and computation", p.3; §A.1, p.13): the prover sends one message before
the verifier draws its private sample of `m` labeled observations; the verifier then uses the
message, the sample and its own coins to output a predictor (`some h`) or reject (`none`).

**Formalization Note** `m` is the worst-case private sample count `m_V`; every observation
counts. The coin space is an arbitrary probability space. For each fixed message the decision is
measurable: the acceptance bit is measurable in (sample, coins) and the output predictor (read with
the default `fun _ => false` on rejection) is jointly measurable in (sample, coins, feature), so the
probabilities of Definition 2.1 ("the probabilities include the samples and all protocol
randomness") are defined and every output is a measurable predictor. The message type carries no
measurable structure; soundness is required for every message (see `OMSound`). -/
structure OneMsgVerifier (d : ℕ) (Msg : Type) where
  /-- The private sample count `m_V`. -/
  m : ℕ
  /-- The verifier's coin space. -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- The law of the verifier's coins. -/
  coins : ProbabilityMeasure Ω
  /-- The decision: message, private sample, coins ↦ an output predictor or rejection. -/
  decide : Msg → (Fin m → Vec d × Bool) → Ω → Option (Vec d → Bool)
  /-- For each message, acceptance is measurable in (sample, coins). -/
  accept_meas : ∀ msg : Msg,
    Measurable (fun p : (Fin m → Vec d × Bool) × Ω => (decide msg p.1 p.2).isSome)
  /-- For each message, the output predictor is jointly measurable in (sample, coins, feature). -/
  pred_meas : ∀ msg : Msg,
    Measurable (fun p : ((Fin m → Vec d × Bool) × Ω) × Vec d =>
      (decide msg p.1.1 p.1.2).getD (fun _ => false) p.2)

attribute [instance] OneMsgVerifier.mΩ

/-- A **sample-only honest prover** for messages of type `Msg` (Chen, Oct. 2026, §2, p.3; §A.6.1,
p.19): it draws `m_P` labeled observations of its own, independent of the verifier's, and maps
them and its coins to a message. It sees the law only through its samples. -/
structure HonestProver (d : ℕ) (Msg : Type) where
  /-- The honest prover's sample count `m_P`. -/
  mP : ℕ
  /-- The prover's coin space. -/
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  /-- The law of the prover's coins. -/
  coins : ProbabilityMeasure Ω
  /-- The message as a function of the prover's sample and coins. -/
  send : (Fin mP → Vec d × Bool) → Ω → Msg

attribute [instance] HonestProver.mΩ

/-- **Arbitrary-label Gaussian soundness** of a one-message verifier against a class `H`
(Chen, Oct. 2026, Definition 2.1, p.3; §A.1, p.13): for every law `P` of `(X, Y)` with feature
marginal `N(0, I_d)` and **any** conditional label law, and for every message, the probability
over the private sample and the coins that the verifier outputs some `h` with
`R_P(h) > OPT_P(H) + ε` is at most `δ`.

**Formalization Note** Soundness is required for every fixed message, which covers every prover
strategy, including one that knows the law: the message is sent before the private sample is
drawn, so a random message is a mixture of fixed ones. For a fixed message the decision is
measurable, so the bad set is an event; the bound is stated on its measure. -/
def OMSound {d : ℕ} {Msg : Type} (V : OneMsgVerifier d Msg) (H : Set (Vec d → Bool))
    (ε δ : ℝ) : Prop :=
  ∀ P : ProbabilityMeasure (Vec d × Bool), GaussMarginal (P : Measure (Vec d × Bool)) →
    ∀ msg : Msg,
      ((sampleLaw P V.m).prod (V.coins : Measure V.Ω))
          {sω | ∃ h, V.decide msg sω.1 sω.2 = some h ∧
            risk (P : Measure (Vec d × Bool)) h > opt (P : Measure (Vec d × Bool)) H + ε}
        ≤ ENNReal.ofReal δ

/-- **Full Massart completeness** of a one-message verifier with an honest prover (Chen, Oct. 2026,
Definition 2.1 and (2.1), p.3; §A.1, p.13): for every law `P` with feature marginal `N(0, I_d)`
that satisfies Massart noise with bound `η` around some target `h* ∈ H`, the honest prover's
message, computed from its own sample, makes the verifier output a correct predictor, i.e. some `h`
with `R_P(h) ≤ OPT_P(H) + ε`, with probability at least `1 − δ`.

**Formalization Note** The prover's sample, the prover's coins, the verifier's sample and the
verifier's coins are independent (a fourfold product measure); the honest prover is fixed before
the law. The honest run is measurable: its acceptance bit and its output predictor are jointly
measurable in (prover sample, prover coins, verifier sample, verifier coins), and in the feature for
the predictor, so the completeness probability is defined. The failure set (no output, or an output
with `R_P(h) > OPT_P(H) + ε`) is required to have measure at most `δ`. -/
def OMMassartComplete {d : ℕ} {Msg : Type} (V : OneMsgVerifier d Msg) (Hon : HonestProver d Msg)
    (H : Set (Vec d → Bool)) (η ε δ : ℝ) : Prop :=
  (Measurable (fun x : ((Fin Hon.mP → Vec d × Bool) × Hon.Ω) × ((Fin V.m → Vec d × Bool) × V.Ω) =>
      (V.decide (Hon.send x.1.1 x.1.2) x.2.1 x.2.2).isSome) ∧
    Measurable (fun p : (((Fin Hon.mP → Vec d × Bool) × Hon.Ω) ×
        ((Fin V.m → Vec d × Bool) × V.Ω)) × Vec d =>
      (V.decide (Hon.send p.1.1.1 p.1.1.2) p.1.2.1 p.1.2.2).getD (fun _ => false) p.2)) ∧
  ∀ P : ProbabilityMeasure (Vec d × Bool), GaussMarginal (P : Measure (Vec d × Bool)) →
    ∀ hstar ∈ H, IsMassart (P : Measure (Vec d × Bool)) hstar η →
      (((sampleLaw P Hon.mP).prod (Hon.coins : Measure Hon.Ω)).prod
          ((sampleLaw P V.m).prod (V.coins : Measure V.Ω)))
          {x | ¬ ∃ h, V.decide (Hon.send x.1.1 x.1.2) x.2.1 x.2.2 = some h ∧
            risk (P : Measure (Vec d × Bool)) h ≤ opt (P : Measure (Vec d × Bool)) H + ε}
        ≤ ENNReal.ofReal δ

/-- A one-message verifier is **proper with rule alphabet `F₀`** (Chen, Oct. 2026, Definition 2.1,
p.3; Theorem A.5, p.21: protocols "name a rule from a fixed finite subset of F"): every output, for
every message, sample and coin value, is a projection predictor `x ↦ f(Wᵀx)` with `f ∈ F₀` and an
orthonormal frame `W ∈ ℝ^{d×k}`. -/
def ProperIn {d k : ℕ} {Msg : Type} (V : OneMsgVerifier d Msg) (F₀ : Set (Vec k → Bool)) : Prop :=
  ∀ (msg : Msg) (s : Fin V.m → Vec d × Bool) (ω : V.Ω) (h : Vec d → Bool),
    V.decide msg s ω = some h → ∃ f ∈ F₀, ∃ W ∈ stiefel d k, h = frameRule f W

/-- Messages that carry a frame with at most `N` columns in `ℝᵈ` (Chen, Oct. 2026, §A.6, p.18:
"The prover sends an orthonormal basis P of at most k + K directions"). -/
def FrameMsg (d N : ℕ) : Type := Σ m : Fin (N + 1), Matrix (Fin d) (Fin m) ℝ

/-- The verifier **rejects every message whose frame is not orthonormal** (Chen, Oct. 2026, §A.6,
p.18: "Invalid messages are rejected"): whenever it outputs a predictor, the frame carried by the
message (read through `frame`) has orthonormal columns. Together with the message type `FrameMsg d N`
this says that the message contains at most `N` orthonormal directions. -/
def ChecksFrame {d N : ℕ} {Msg : Type} (V : OneMsgVerifier d Msg) (frame : Msg → FrameMsg d N) :
    Prop :=
  ∀ (msg : Msg) (s : Fin V.m → Vec d × Bool) (ω : V.Ω),
    (V.decide msg s ω).isSome → (frame msg).2 ∈ stiefel d (frame msg).1

end CondGeoVerif


