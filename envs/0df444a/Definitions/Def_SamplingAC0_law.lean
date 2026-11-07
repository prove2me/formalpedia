-- Prove2me | Definitions.Def_SamplingAC0_law
-- name    : SamplingAC0_law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:39.598584+00:00
-- url     : https://prove2.me/theorems/0f378311-731a-47c5-b95c-cd6971c06b76
-- title:
--   Uniform input, output distribution, probability, expectation, conditioning
-- statement:
--   For a finite index set $\iota$, $U$ denotes the **uniform distribution** on $\{0,1\}^\iota$. For a map $F:\{0,1\}^\iota\to B$, the **output distribution** $F(U)$ is the law of $F$ applied to a uniform input.
--
--   For a distribution $P$ on a finite set, $\mathbb P_P[E]$ is the probability of an event $E$ and $\mathbb E_{x\sim P}[g(x)]$ the expectation of a real function $g$. The **conditional distribution** $(P\mid S)$ of $P$ given an event $S$ with $\mathbb P_P[S]>0$ has mass $P(x)/\mathbb P_P[S]$ on $S$ and $0$ off $S$.
--
--   These are the probabilistic primitives of every statement of the mission.
--
--   **Formalization Note** Distributions are probability mass functions on finite types and probabilities are real numbers. When $\mathbb P_P[S]=0$ the conditioning returns $P$ itself; every statement of the mission conditions only on events of positive probability.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Notation, p.2

import Mathlib
set_option autoImplicit false

namespace SamplingAC0

/-- The uniform distribution `U` on `{0,1}^ι` (Riazanov–Viola, STOC 2027 submission, manuscript
sha256 99c33d30…, Notation, p.2: "U for the uniform distribution (over suitable domain)"). -/
noncomputable def unif (ι : Type) [Fintype ι] [DecidableEq ι] : PMF (ι → Bool) :=
  PMF.uniformOfFintype (ι → Bool)

/-- **Output distribution of a sampler; probabilities, expectations, conditioning.**
Riazanov–Viola, *Sampling Tools and the Power of AC0*, STOC 2027 submission (manuscript sha256
99c33d30…), Notation, p.2. `law F` is the distribution `F(U)` of `F` applied to a uniform input
`U ∼ {0,1}^ι`.

**Formalization Note.** All distributions are `PMF`s on finite types; probabilities and
expectations are real numbers (`toReal` of the masses). -/
noncomputable def law {ι β : Type} [Fintype ι] [DecidableEq ι] (F : (ι → Bool) → β) : PMF β :=
  (unif ι).map F

/-- The probability `P[E]` of an event `E` under a distribution `P` on a finite type. -/
noncomputable def pr {β : Type} [Fintype β] (P : PMF β) (E : Set β) : ℝ :=
  open Classical in
  ∑ x, if x ∈ E then (P x).toReal else 0

/-- The expectation `E_{x ∼ P}[g(x)]` of a real function under a distribution on a finite type. -/
noncomputable def expect {β : Type} [Fintype β] (P : PMF β) (g : β → ℝ) : ℝ :=
  ∑ x, (P x).toReal * g x

/-- The distribution `P` conditioned on the event `S`, i.e. `P(x | S) = P(x)/P(S)` on `S` and `0`
off `S`.

**Formalization Note.** When `P(S) = 0` the conditional distribution is undefined; this definition
then returns `P` itself. Every statement of the mission uses it only on events of positive
probability. -/
noncomputable def condOn {β : Type} (P : PMF β) (S : Set β) : PMF β :=
  open Classical in
  if h : ∃ a ∈ S, a ∈ P.support then P.filter S h else P

end SamplingAC0


