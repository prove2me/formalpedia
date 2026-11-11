-- Prove2me | Definitions.Def_PrivInfoHier_Main_Model
-- name    : PrivInfoHier_Main_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:13:25.839136+00:00
-- url     : https://prove2.me/theorems/de04da0d-c8ee-4707-80d9-b09b0a672a32
-- title:
--   Mechanisms, data-release processes, request strategies, the interaction law and the privacy loss (§2.1)
-- statement:
--   **Databases and outputs.** Let $\mathcal X$ be the space of databases and $\mathcal Y$ a measurable output space. A **mechanism** is a random function of the database: for every database $x$ a probability law $m(x)$ of the output on $\mathcal Y$. The type of mechanisms carries the discrete σ-algebra, so the identity of a realised mechanism is an observable quantity.
--
--   **Sequential adaptive model.** At each round $i\ge1$ an analyst submits a request $R_i$ from a measurable request space $\mathcal R$, and then an output $Y_i\in\mathcal Y$ is released. Write $R^k=(R_1,\dots,R_k)$, $Y^k=(Y_1,\dots,Y_k)$, $Y^0=\varnothing$. A **data-release process** $(\mathcal M_i)_{i\ge1}$ is a sequence of release rules fixed in advance: $\mathcal M_i$ maps each transcript $(r^i,y^{i-1})$ to a mechanism, and the realised mechanism is $M_i=\mathcal M_i(R^i,Y^{i-1})$. For each database the output law must depend measurably on the transcript (it is a probability kernel), so that the interaction law below exists.
--
--   A **request strategy** $\mathcal A$ is a sequence of probability kernels: $R_i$ is drawn from $\mathcal A_i(\cdot\mid R^{i-1},Y^{i-1})$, conditionally independent of the database given the previous transcript.
--
--   **Interaction law.** For a process, a strategy $\mathcal A$ and a database $x$, the law $P_{x,\mathcal A}$ of the path $(R_1,Y_1,R_2,Y_2,\dots)$ is built by alternating
--   $$R_i\sim\mathcal A_i(\cdot\mid R^{i-1},Y^{i-1}),\qquad Y_i\sim m_i(x),\quad m_i=\mathcal M_i(R^i,Y^{i-1}),$$
--   which defines a unique probability measure on the path space $(\mathcal R\times\mathcal Y)^{\mathbb N}$ by the Ionescu-Tulcea theorem.
--
--   **Privacy loss.** For databases $x,x'$ the privacy loss of round $i$ is
--   $$L_i(x,x')=\log\frac{P_x(Y_i\mid R_i,Y^{i-1})}{P_{x'}(Y_i\mid R_i,Y^{i-1})}\in[-\infty,+\infty],$$
--   the log density ratio of $m_i(x)$ to $m_i(x')$ at the output $Y_i$ ($+\infty$ on the part of $m_i(x)$ singular to $m_i(x')$). The cumulative loss is $L^{(t)}=\sum_{i=1}^tL_i$; it enters the mission only through $e^{-L^{(t)}}=\prod_{i=1}^t e^{-L_i}$.
--
--   **Formalization Note.** `Mechanism 𝒳 𝒴` has a field `law : 𝒳 → Measure 𝒴` with every `law x` a probability measure; no measurability in the database is required. Rounds are 0-based in Lean: `Path ℛ 𝒴 = ℕ → ℛ × 𝒴` holds round $k+1$ at index $k$, `Hist ℛ 𝒴 n = Fin n → ℛ × 𝒴` is a transcript of $n$ rounds, and `Process.rule n (h, r)` is $\mathcal M_{n+1}(r^{n+1},y^n)$ with `measurable_law` the kernel condition. `RequestStrategy.kernel n` is the Markov kernel of $R_{n+1}$ given the first $n$ rounds. `interLaw P A x` is `Kernel.trajMeasure` (Ionescu-Tulcea) with first coordinate drawn from `roundKernel P A x 0` at the empty transcript and step kernels `roundKernel = A.kernel n ⊗ₖ mechKernel P x n`. `realisedMech P k p` is $M_{k+1}$ on the path `p`. `lossRatio P x x' k p` is $e^{-L_{k+1}(x,x')}$, the Radon–Nikodym derivative $\mathrm d m_{k+1}(x')/\mathrm d m_{k+1}(x)$ at the output, in $[0,\infty]$; `privLoss = −log(lossRatio)` in `EReal`; `expNegCumLoss P x x' t p` $=\prod_{k<t}$ `lossRatio` $=e^{-L^{(t)}}$, a product of nonnegative extended reals, so no $\infty-\infty$ arises.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 5 (PDF 7), §2.1 and footnote 1; §2.2, p. 5

import Mathlib

namespace PrivInfoHier.Main

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-- A mechanism (Taylor–Vippathalla–Coon, §2.1, p. 5, footnote 1): "a random function with input
`X` and output `Y_i`", i.e. for every database `x` a probability law `law x` of the output on the
output space `𝒴`. No measurability in the database is required. -/
structure Mechanism (𝒳 𝒴 : Type) [MeasurableSpace 𝒴] where
  /-- the law of the output when the database is `x` -/
  law : 𝒳 → Measure 𝒴
  /-- every output law is a probability measure -/
  isProb : ∀ x, IsProbabilityMeasure (law x)

/-- The type of mechanisms carries the discrete σ-algebra: the identity of a realised mechanism
is observable (used for the mechanism-level information `σ(M^t)`, §2.2). -/
instance instMeasurableSpaceMechanism (𝒳 𝒴 : Type) [MeasurableSpace 𝒴] :
    MeasurableSpace (Mechanism 𝒳 𝒴) := ⊤

/-- A transcript of `n` rounds `((r_1, y_1), …, (r_n, y_n))`; round `j + 1` sits at index `j`. -/
abbrev Hist (ℛ 𝒴 : Type) (n : ℕ) : Type := Fin n → ℛ × 𝒴

/-- An infinite interaction path `(R_1, Y_1), (R_2, Y_2), …`; round `k + 1` sits at index `k`. -/
abbrev Path (ℛ 𝒴 : Type) : Type := ℕ → ℛ × 𝒴

/-- A data-release process `(𝓜_i)_{i ≥ 1}` (§2.1, p. 5). `rule n` is the release rule
`𝓜_{n+1}`: it maps the transcript `(r^{n+1}, y^n)` — the first `n` rounds together with the
current request `r_{n+1}` — to a mechanism. For each database `x` the output law must depend
measurably on the transcript (a kernel), so that the interaction law exists. -/
structure Process (𝒳 ℛ 𝒴 : Type) [MeasurableSpace ℛ] [MeasurableSpace 𝒴] where
  /-- `rule n (h, r) = 𝓜_{n+1}(r^{n+1}, y^n)` -/
  rule : (n : ℕ) → Hist ℛ 𝒴 n × ℛ → Mechanism 𝒳 𝒴
  /-- for every database the output law is measurable in the transcript -/
  measurable_law : ∀ n (x : 𝒳), Measurable (fun h : Hist ℛ 𝒴 n × ℛ => (rule n h).law x)

/-- A request strategy `𝒜` (§2.1, p. 5): at round `n + 1` the request is drawn from the
probability kernel `kernel n` applied to the previous transcript `(r^n, y^n)`. -/
structure RequestStrategy (ℛ 𝒴 : Type) [MeasurableSpace ℛ] [MeasurableSpace 𝒴] where
  /-- `kernel n` is the conditional law of `R_{n+1}` given `(R^n, Y^n)` -/
  kernel : (n : ℕ) → Kernel (Hist ℛ 𝒴 n) ℛ
  /-- each conditional law is a probability measure -/
  isMarkov : ∀ n, IsMarkovKernel (kernel n)

variable {𝒳 ℛ 𝒴 : Type} [MeasurableSpace ℛ] [MeasurableSpace 𝒴]

/-- The output kernel of round `n + 1` for database `x`: `(r^{n+1}, y^n) ↦ m_{n+1}(x)`. -/
noncomputable def mechKernel (P : Process 𝒳 ℛ 𝒴) (x : 𝒳) (n : ℕ) :
    Kernel (Hist ℛ 𝒴 n × ℛ) 𝒴 :=
  ⟨fun h => (P.rule n h).law x, P.measurable_law n x⟩

instance isMarkovKernel_mechKernel (P : Process 𝒳 ℛ 𝒴) (x : 𝒳) (n : ℕ) :
    IsMarkovKernel (mechKernel P x n) :=
  ⟨fun h => (P.rule n h).isProb x⟩

/-- The law of round `n + 1`, `(R_{n+1}, Y_{n+1})`, given the first `n` rounds: the request is
drawn from `𝒜`, then the output from the realised mechanism applied to `x`. -/
noncomputable def roundKernel (P : Process 𝒳 ℛ 𝒴) (A : RequestStrategy ℛ 𝒴) (x : 𝒳) (n : ℕ) :
    Kernel (Hist ℛ 𝒴 n) (ℛ × 𝒴) :=
  (A.kernel n) ⊗ₖ (mechKernel P x n)

instance isMarkovKernel_roundKernel (P : Process 𝒳 ℛ 𝒴) (A : RequestStrategy ℛ 𝒴) (x : 𝒳)
    (n : ℕ) : IsMarkovKernel (roundKernel P A x n) := by
  have := A.isMarkov n
  unfold roundKernel
  infer_instance

/-- Reading the coordinates `0, …, n` of a path prefix as a transcript of `n + 1` rounds. -/
def toHist (n : ℕ) (h : Π _ : Iic n, ℛ × 𝒴) : Hist ℛ 𝒴 (n + 1) :=
  fun j => h ⟨j.1, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 j.2)⟩

lemma measurable_toHist (n : ℕ) : Measurable (toHist (ℛ := ℛ) (𝒴 := 𝒴) n) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- The Ionescu-Tulcea step kernel: coordinates `0, …, n` (rounds `1, …, n + 1`) to
coordinate `n + 1` (round `n + 2`). -/
noncomputable def stepKernel (P : Process 𝒳 ℛ 𝒴) (A : RequestStrategy ℛ 𝒴) (x : 𝒳) (n : ℕ) :
    Kernel (Π _ : Iic n, ℛ × 𝒴) (ℛ × 𝒴) :=
  (roundKernel P A x (n + 1)).comap (toHist n) (measurable_toHist n)

instance isMarkovKernel_stepKernel (P : Process 𝒳 ℛ 𝒴) (A : RequestStrategy ℛ 𝒴) (x : 𝒳)
    (n : ℕ) : IsMarkovKernel (stepKernel P A x n) := by
  unfold stepKernel
  infer_instance

/-- The interaction law `P_{x,𝒜}` (§2.1): the law on the path space of
`(R_1, Y_1, R_2, Y_2, …)` built by alternating the request strategy and the realised mechanisms
(Ionescu-Tulcea). Coordinate `k` is round `k + 1`; round 1 is drawn from the empty transcript. -/
noncomputable def interLaw (P : Process 𝒳 ℛ 𝒴) (A : RequestStrategy ℛ 𝒴) (x : 𝒳) :
    Measure (Path ℛ 𝒴) :=
  Kernel.trajMeasure (X := fun _ => ℛ × 𝒴) (roundKernel P A x 0 isEmptyElim) (stepKernel P A x)

/-- The realised mechanism `M_{k+1} = 𝓜_{k+1}(R^{k+1}, Y^k)` on a path. -/
def realisedMech (P : Process 𝒳 ℛ 𝒴) (k : ℕ) (p : Path ℛ 𝒴) : Mechanism 𝒳 𝒴 :=
  P.rule k (fun j : Fin k => p j, (p k).1)

/-- `e^{−L_{k+1}(x, x′)}` on a path: the density ratio `dm_{k+1}(x′)/dm_{k+1}(x)` of the realised
mechanism's output laws, evaluated at the output `Y_{k+1}`. It is `0` on the part of `m(x)` that is
singular to `m(x′)`, where the privacy loss is `+∞`. -/
noncomputable def lossRatio (P : Process 𝒳 ℛ 𝒴) (x x' : 𝒳) (k : ℕ) (p : Path ℛ 𝒴) : ℝ≥0∞ :=
  ((realisedMech P k p).law x').rnDeriv ((realisedMech P k p).law x) (p k).2

/-- The privacy loss of round `k + 1` (§2.1, p. 5):
`L_{k+1}(x, x′) = log P_x(Y_{k+1} | R_{k+1}, Y^k) / P_{x′}(Y_{k+1} | R_{k+1}, Y^k)`, valued in
`[−∞, +∞]`. -/
noncomputable def privLoss (P : Process 𝒳 ℛ 𝒴) (x x' : 𝒳) (k : ℕ) (p : Path ℛ 𝒴) : EReal :=
  - ENNReal.log (lossRatio P x x' k p)

/-- `e^{−L^{(t)}(x, x′)} = ∏_{i ≤ t} e^{−L_i(x, x′)}`, the exponential of minus the cumulative
privacy loss `L^{(t)} = Σ_{i=1}^t L_i` (§2.1), written as a product of density ratios so that no
`∞ − ∞` arises. -/
noncomputable def expNegCumLoss (P : Process 𝒳 ℛ 𝒴) (x x' : 𝒳) (t : ℕ) (p : Path ℛ 𝒴) : ℝ≥0∞ :=
  ∏ k ∈ range t, lossRatio P x x' k p

end PrivInfoHier.Main


