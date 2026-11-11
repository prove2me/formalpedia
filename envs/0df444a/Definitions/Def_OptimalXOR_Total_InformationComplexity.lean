-- Prove2me | Definitions.Def_OptimalXOR_Total_InformationComplexity
-- name    : OptimalXOR_Total_InformationComplexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:06:31.492232+00:00
-- url     : https://prove2.me/theorems/d8885590-d765-4448-aa9c-07208a7e3d84
-- title:
--   Information cost $\mathrm{IC}(\pi,\mu)$, $\mathrm{IC}(\pi)$, errors, and $\mathrm{IC}_\varepsilon(F,\mu)$, $\mathrm{IC}^D_\varepsilon(F)$, $\mathrm{IC}_\varepsilon(F)$
-- statement:
--   Protocols are two-party randomized protocols with a public random tape $R$ and private tapes for Alice and Bob, independent of each other and of the input: each message depends only on the sender's input, the preceding messages and the sender's public and private randomness, and the output is a function of the public randomness and the transcript $M$ (the sequence of messages). These are the published protocols of `CaiZhuInfo.Matrix.Protocol`.
--
--   For $\mu\in\mathcal P(\mathcal X\times\mathcal Y)$ and $(X,Y)\sim\mu$, the **internal information cost** of $\pi$ is, in bits,
--   $$\mathrm{IC}(\pi,\mu)=I(M;X\mid Y,R)+I(M;Y\mid X,R),$$
--   and for a problem $F$, $\mathrm{IC}(\pi)=\sup_{\mu\in\mathcal P(\operatorname{dom}F)}\mathrm{IC}(\pi,\mu)$. The **distributional error** is $\mathrm{err}_\mu(\pi,F)=\mathbf P[\pi(X,Y)\neq F(X,Y)]$ over the input and the protocol's randomness, and the **worst-case error** is $\mathrm{err}(\pi,F)=\max_{(x,y)\in\operatorname{dom}F}\mathbf P[\pi(x,y)\neq F(x,y)]$ over the protocol's randomness. Then
--   $$\mathrm{IC}_\varepsilon(F,\mu)=\inf_{\pi:\ \mathrm{err}_\mu(\pi,F)\le\varepsilon}\mathrm{IC}(\pi,\mu),\qquad \mathrm{IC}^D_\varepsilon(F)=\sup_{\mu\in\mathcal P(\operatorname{dom}F)}\mathrm{IC}_\varepsilon(F,\mu),\qquad \mathrm{IC}_\varepsilon(F)=\inf_{\pi:\ \mathrm{err}(\pi,F)\le\varepsilon}\mathrm{IC}(\pi).$$
--   The last is the (worst-case) **information complexity** of $F$: its protocol must meet the error bound on every legal input and its information bound under every $\mu\in\mathcal P(\operatorname{dom}F)$.
--
--   **Formalization Note** `infoCost P μ` is the published `Protocol.informationCost` with the discrete σ-algebra on the inputs; `worstInfoCost P F` is the supremum over `Distributions F` of `ENNReal.ofReal (infoCost P μ)`. `pointError`, `worstError` (a real supremum over the nonempty finite `dom F`, values in $[0,1]$) and `distError` are probabilities in `ℝ`; `execProb` is the probability of an event of an execution. `distIC F ε μ`, `distMaxIC F ε` and `IC F ε` take values in `ℝ≥0∞`, range over every protocol satisfying `Protocol.TranscriptDetermined` (the output convention), and are $\infty$ when no protocol qualifies.
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), pp. 13–14 (PDF 15–16) §2.3, (2.5)–(2.9)

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems

open MeasureTheory
open scoped ENNReal

namespace OptimalXOR.Total

open CaiZhuInfo.Matrix

/-! Sherstov, *Optimal XOR Lemmas for Information Complexity*, STOC 2027 submission, §2.3,
printed pp. 13–14 / PDF pp. 15–16, (2.5)–(2.9).

Protocols are the published `CaiZhuInfo.Matrix.Protocol`: a finite binary communication tree with
a fixed speaker at each node, a public tape and two private tapes (arbitrary probability spaces,
independent of each other and of the input), each message bit a measurable function of the
sender's input, the public tape, the sender's own private tape and the preceding messages.
The paper's output convention ("the output is a function of the public randomness and the
transcript") is the published predicate `Protocol.TranscriptDetermined`, imposed on every protocol
in the infima below. Inputs carry the discrete σ-algebra `⊤`. Information is in bits. -/

noncomputable section

variable {X Y Z : Type}

/-- The internal information cost `IC(π, µ) = I(M; X | Y, R) + I(M; Y | X, R)` of (2.5), in bits,
with `(X, Y) ∼ µ`, `R` the public randomness and `M` the transcript; inputs carry the discrete
σ-algebra. -/
def infoCost (P : Protocol X Y Z) (μ : PMF (X × Y)) : ℝ :=
  letI : MeasurableSpace X := ⊤
  letI : MeasurableSpace Y := ⊤
  P.informationCost μ

/-- The probability of an event `E` of an execution of `P` on `(X, Y) ∼ µ`, over the input and
the protocol's public and private randomness. -/
def execProb (P : Protocol X Y Z) (μ : PMF (X × Y)) (E : Set P.Sample) : ℝ :=
  letI : MeasurableSpace X := ⊤
  letI : MeasurableSpace Y := ⊤
  ((P.executionLaw μ) E).toReal

/-- `IC(π) = sup_{µ ∈ P(dom F)} IC(π, µ)` for the communication problem `F` under consideration
(p. 14), with values in `[0, ∞]`. -/
def worstInfoCost {W : Type} (P : Protocol X Y Z) (F : X → Y → Option W) : ℝ≥0∞ :=
  ⨆ (μ : PMF (X × Y)) (_ : μ ∈ Distributions F), ENNReal.ofReal (infoCost P μ)

/-- `P[π(x, y) ≠ F(x, y)]` over the protocol's public and private randomness, on input `(x, y)`. -/
def pointError (P : Protocol X Y Z) (F : X → Y → Option Z) (x : X) (y : Y) : ℝ :=
  (P.coinsLaw {c | some (P.output x y c) ≠ F x y}).toReal

/-- The worst-case error `err(π, F) = max_{(x,y) ∈ dom F} P[π(x, y) ≠ F(x, y)]` (p. 14). -/
def worstError (P : Protocol X Y Z) (F : X → Y → Option Z) : ℝ :=
  ⨆ p : dom F, pointError P F p.1.1 p.1.2

/-- The distributional error `err_µ(π, F) = P[π(X, Y) ≠ F(X, Y)]`, `(X, Y) ∼ µ`, over the input
and the protocol's randomness (p. 14). -/
def distError (P : Protocol X Y Z) (μ : PMF (X × Y)) (F : X → Y → Option Z) : ℝ :=
  execProb P μ {ω | some (P.output ω.1.1 ω.1.2 ω.2) ≠ F ω.1.1 ω.1.2}

/-- `IC_ε(F, µ) = inf { IC(π, µ) : err_µ(π, F) ≤ ε }` (2.7), over all protocols obeying the
output convention; the infimum of the empty set is `∞`. -/
def distIC (F : X → Y → Option Z) (ε : ℝ) (μ : PMF (X × Y)) : ℝ≥0∞ :=
  ⨅ (P : Protocol X Y Z) (_ : P.TranscriptDetermined ∧ distError P μ F ≤ ε),
    ENNReal.ofReal (infoCost P μ)

/-- `IC^D_ε(F) = sup_{µ ∈ P(dom F)} IC_ε(F, µ)` (2.8). -/
def distMaxIC (F : X → Y → Option Z) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ (μ : PMF (X × Y)) (_ : μ ∈ Distributions F), distIC F ε μ

/-- The (worst-case) information complexity `IC_ε(F) = inf { IC(π) : err(π, F) ≤ ε }` (2.9):
the protocol must meet its error bound on every legal input, and its information bound is the
supremum over every `µ ∈ P(dom F)`; the infimum ranges over all protocols obeying the output
convention, and the infimum of the empty set is `∞`. -/
def IC (F : X → Y → Option Z) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ (P : Protocol X Y Z) (_ : P.TranscriptDetermined ∧ worstError P F ≤ ε),
    worstInfoCost P F

end

end OptimalXOR.Total


