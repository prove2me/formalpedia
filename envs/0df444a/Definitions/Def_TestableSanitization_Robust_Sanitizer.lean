-- Prove2me | Definitions.Def_TestableSanitization_Robust_Sanitizer
-- name    : TestableSanitization_Robust_Sanitizer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:53:47.523399+00:00
-- url     : https://prove2.me/theorems/800382b3-a978-4992-927e-68fc11288b1e
-- title:
--   Definition 2 — $(\alpha,\eta,\varepsilon)$-testable sanitization algorithms with success probability $1-\zeta$, and worst-case cost bounds
-- statement:
--   **Testable sanitization (Definition 2).** Fix $\alpha\ge1$, $\eta,\varepsilon>0$, $\zeta\in(0,1)$. A randomized algorithm receives a radius $r>0$, oracle access to a classifier $f$ and sample access to a distribution $D$ on $\mathbb R^d$, and outputs either Reject or (Accept, $g^f$), where $g^f:\mathbb R^d\to\{\pm1\}$ may keep oracle access to $f$. It is an **$(\alpha,\eta,\varepsilon)$-testable sanitization algorithm with success probability $1-\zeta$** if, for every $r>0$, every classifier $f$ and every admissible $D$:
--   - **Soundness:** the probability that it accepts with an output $g^f$ such that $\Pr_{x\sim D}[f(x)\neq g^f(x)]>\varepsilon$ or $D(\partial g^f_r)>\eta$ is at most $\zeta$;
--   - **Completeness:** if $D(\partial f_{\alpha r})\le c\,\eta$, it accepts with probability at least $1-\zeta$,
--
--   where $c\in(0,1)$ is the completeness constant.
--
--   In this mission an algorithm is a pair $(P,E)$ of programs of the oracle real RAM (`Machine`): $P$ runs on the inputs $[d,\alpha,\eta,\zeta,\mu,r]$; if it accepts with final memory $M$, the output classifier is $g^f=$ `outputFn E d f M`, the deterministic evaluation program $E$ run on $M$ with oracle $f$. `BadOutput` is the soundness failure for an accepted memory: $E$ fails to return a value in $\{\pm1\}$ at some point, or $D\{x: f(x)\neq g^f(x)\}>\varepsilon$, or $D(\partial g^f_r)>\eta$. `Sound`: the stream measure of the runs that accept with a bad output is at most $\zeta$. `Complete`: $D(\partial f_{\alpha r})\le c\eta$ implies that the runs that do not accept have measure at most $\zeta$. `IsTestableSanitizer d α η ε ζ c μ P E`: both hold for every $r>0$, every classifier $f$ and every probability measure $D$ with $\mathbb E_{x\sim D}\|x\|\le\mu$.
--
--   **Cost.** `CostBounded d α η ζ μ n_S n_Q n_T P`: for every $r>0$, every classifier $f$, every value of the random streams and every number of steps $t$, the run of $P$ has drawn at most $n_S(r)$ samples, made at most $n_Q(r)$ queries and taken at most $n_T(r)$ steps — worst-case bounds on every run, counted for the construction program only (the cost of later evaluations of $g^f$ is not bounded, as in Theorem 1).
--
--   **Formalization Note.** Failure probabilities are measures of failure sets, bounded by $\zeta$ (outer measures if a set is not measurable, which only strengthens the bound); "accepts with probability at least $1-\zeta$" is written as "the set of runs that do not accept has measure at most $\zeta$". The measures $D\{f\neq g^f\}$ and $D(\partial g^f_r)$ are outer measures: no measurability of $g^f$ is assumed. $\mathbb E_{x\sim D}\|x\|$ is the lower Lebesgue integral $\int^-\|x\|\,dD$ in $[0,\infty]$. A step bound forces $P$ to halt, since a running program is charged at least one step per step when $d\ge1$.
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 8 (PDF 10), Definition 2; p. 9 (PDF 11), Theorem 1 (the class of D with E‖x‖ ≤ µ and the efficiency measures)

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Machine

/-!
# Testable sanitization algorithms (Definition 2)

Cai, Mamali, Sotiraki, Yu, Zampetakis, *Testable Sanitization via Boundary Geometry*, STOC 2027
submission (manuscript sha256 bcf6434f…), Definition 2 p. 8; Theorem 1 p. 9.

"A randomized algorithm A receives a radius r > 0, oracle access to f : R^d → {±1}, and sample
access to a distribution D over R^d. It outputs either "Reject" or ("Accept", g^f), where
g^f : R^d → {±1} may retain oracle access to f. … (Soundness) The probability that A outputs
("Accept", g^f) and either Pr_{x∼D}[f(x) ≠ g^f(x)] > ε or D(∂g^f_r) > η is at most ζ.
(Completeness) If there exists universal constant c ∈ (0, 1) such that D(∂f_{αr}) ≤ cη, then A
outputs ("Accept", g^f) with probability at least 1 − ζ."

Encoding.
* An algorithm is a pair `(P, E)` of programs of the oracle real RAM: `P` is run on the inputs
  `[d, α, η, ζ, μ, r]` with oracle `f` and the random streams; if it accepts with final memory
  `M`, the output classifier `g^f` is the evaluation program `E` run on `M` (`outputFn E d f M`).
* `BadOutput` is the soundness failure for an accepted memory `M`: `E` fails to return a `±1`
  value at some point, or `D{x : f x ≠ g^f x} > ε`, or `D(∂g^f_r) > η` (outer measures).
* Soundness bounds the stream measure of the set of runs that accept with a bad output by `ζ`;
  completeness says that `D(∂f_{αr}) ≤ cη` implies the runs that do not accept have measure at
  most `ζ`. The completeness constant `c` is a parameter here; Theorem 1 quantifies it as one
  universal constant.
* `IsTestableSanitizer d α η ε ζ c μ P E`: soundness and completeness hold for every radius
  `r > 0`, every classifier `f` and every probability measure `D` on `ℝ^d` with
  `E_{x∼D} ‖x‖ ≤ μ` (a lower Lebesgue integral in `[0, ∞]`).
* `CostBounded d α η ζ μ nS nQ nT P`: on every run (every radius `r > 0`, every classifier `f`,
  every value of the streams, hence every `D`, and every number of steps) `P` has drawn at most
  `nS r` samples, made at most `nQ r` queries and taken at most `nT r` steps. Since a running
  program is charged at least one step per step, the step bound also forces `P` to halt.
-/

open MeasureTheory

namespace TestableSanitization.Robust

/-- The soundness failure for an accepted run with final memory `M`. -/
def BadOutput {d : ℕ} (E : Program) (f : Pt d → ℝ) (D : Measure (Pt d)) (r η ε : ℝ)
    (M : ℤ → ℝ) : Prop :=
  ¬ EvalTotal E d f M ∨
    ENNReal.ofReal ε < D {x | f x ≠ outputFn E d f M x} ∨
    ENNReal.ofReal η < boundaryMass D r (outputFn E d f M)

/-- Soundness (Definition 2) at one radius, classifier and distribution. -/
def Sound {d : ℕ} (P E : Program) (inp : List ℝ) (f : Pt d → ℝ) (D : Measure (Pt d))
    [IsProbabilityMeasure D] (r η ε ζ : ℝ) : Prop :=
  streamLaw D {ω | ∃ M, AcceptsWith P d f inp ω M ∧ BadOutput E f D r η ε M} ≤ ENNReal.ofReal ζ

/-- Completeness (Definition 2) at one radius, classifier and distribution, with constant `c`. -/
def Complete {d : ℕ} (P : Program) (inp : List ℝ) (f : Pt d → ℝ) (D : Measure (Pt d))
    [IsProbabilityMeasure D] (r α η ζ c : ℝ) : Prop :=
  boundaryMass D (α * r) f ≤ ENNReal.ofReal (c * η) →
    streamLaw D {ω | ¬ Accepts P d f inp ω} ≤ ENNReal.ofReal ζ

/-- `(P, E)` is an `(α, η, ε)`-testable sanitization algorithm with success probability `1 − ζ`
and completeness constant `c`, for all distributions with `E_{x∼D} ‖x‖ ≤ μ` (Definition 2). -/
def IsTestableSanitizer (d : ℕ) (α η ε ζ c μ : ℝ) (P E : Program) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ f : Pt d → ℝ, IsClassifier f →
    ∀ (D : Measure (Pt d)) [IsProbabilityMeasure D],
      ∫⁻ x, ENNReal.ofReal ‖x‖ ∂D ≤ ENNReal.ofReal μ →
        Sound P E (inputs d α η ζ μ r) f D r η ε ζ ∧
          Complete P (inputs d α η ζ μ r) f D r α η ζ c

/-- Worst-case cost bounds: for every radius `r > 0`, every classifier `f`, every value of the
random streams (hence every distribution `D`) and every number of steps `t`, the run of `P` has
drawn at most `nS r` samples, made at most `nQ r` queries and taken at most `nT r` steps. -/
def CostBounded (d : ℕ) (α η ζ μ : ℝ) (nS nQ nT : ℝ → ℝ) (P : Program) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ f : Pt d → ℝ, IsClassifier f → ∀ (ω : Streams d) (t : ℕ),
    ((run P d f ω (initial d (inputs d α η ζ μ r)) t).samples : ℝ) ≤ nS r ∧
    ((run P d f ω (initial d (inputs d α η ζ μ r)) t).queries : ℝ) ≤ nQ r ∧
    ((run P d f ω (initial d (inputs d α η ζ μ r)) t).work : ℝ) ≤ nT r

end TestableSanitization.Robust


