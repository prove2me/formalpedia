-- Prove2me | Definitions.Def_Avram2004_Shared_IsSNLevy
-- name    : Avram2004_Shared_IsSNLevy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:03:34.677581+00:00
-- url     : https://prove2.me/theorems/c2e3e945-faa0-421b-8edf-c683406f5e25
-- title:
--   Spectrally negative Lévy process (with respect to a right-continuous filtration): independent stationary increments, càdlàg paths from 0, no positive jumps, not monotone
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $X=\{X_t,\ t\ge 0\}$ a real-valued process indexed by time $t\in[0,\infty)$. We say that $X$ is a **spectrally negative Lévy process** (started at $0$) if
--
--   1. each $X_t$ is a random variable (measurable);
--   2. every path starts at $0$: $X_0(\omega)=0$ for every $\omega$;
--   3. $X$ has independent increments: for $t_1\le\dots\le t_n$ the increments $X_{t_2}-X_{t_1},\dots,X_{t_n}-X_{t_{n-1}}$ are independent;
--   4. $X$ has stationary increments: for all $s,t\ge 0$, $X_{s+t}-X_s$ has the same law as $X_t$;
--   5. every path is càdlàg: right-continuous at every $t\ge0$ and with a left limit $X_{t-}$ at every $t>0$;
--   6. $X$ has no positive jumps: $X_t\le X_{t-}$ for every path and every $t>0$;
--   7. the paths are not monotone: it is not the case that almost every path is nondecreasing, and it is not the case that almost every path is nonincreasing.
--
--   This is the class of processes studied by Avram, Kyprianou and Pistorius: a Lévy process whose jumps are all nonpositive, excluding the case of monotone paths. Every later object of the missions (the Laplace exponent, the scale functions, the reflected process) is built from such an $X$.
--
--   **Formalization Note** Properties 2, 5 and 6 are required for every $\omega$, not just almost surely; every Lévy process has a version with these properties, and the paper works with such a version. The Lévy–Itô representation $X_t=\mu t+\sigma W_t+J_t^{(-)}$ of the paper's (1) is a consequence of the definition and is not imposed.
--
--   **With a filtration.** Let $\mathbf F=\{\mathcal F_t\}_{t\ge0}$ be a filtration on $(\Omega,\mathcal F)$. We say that $X$ is a **spectrally negative Lévy process with respect to $\mathbf F$** if, in addition to 1–7,
--
--   8. $X$ is adapted: each $X_t$ is $\mathcal F_t$-measurable;
--   9. the increments are independent of the past: for all $s,t\ge0$, $X_{s+t}-X_s$ is independent of $\mathcal F_s$;
--   10. $\mathbf F$ is right-continuous: $\mathcal F_t=\bigcap_{u>t}\mathcal F_u$ for every $t\ge0$.
--
--   This is the paper's "Lévy process defined on $(\Omega,\mathcal F,\mathbf F,\mathbb P)$, a filtered probability space which satisfies the usual conditions".
--
--   **Formalization Note (filtration)** "The usual conditions" are read as right-continuity only; completeness of $\mathbf F$ is not imposed. The paper never uses completeness, and the Esscher measure $\mathbb P^1$ of (3), which is part of the Russian problem, is typically singular to $\mathbb P$ on $\mathcal F_\infty$: putting every $\mathbb P$-null set into $\mathcal F_0$ would contradict (3) at $t=0$.
--
--   **Shared definition.** This is the group's single copy of this definition, reviewed once for every chunk that uses it: `02-russian` (Theorem 2: Remarks 3–4 and Lemma 1 p. 218, the Russian problem (27)–(28) pp. 227–228, Corollary 1 p. 228, Lemma 2 and Theorem 2 p. 229, proof of Theorem 2 pp. 230–231); `03-canadized-russian` (Theorem 3: Corollary 1 p. 228, Lemma 2 (i) p. 229, the Canadized problem (32) and Lemma 3 pp. 231–233, Theorem 3 p. 233, Lemma 4 p. 234, proof of Theorem 3 pp. 234–235).
-- source:
--   Avram, Kyprianou, Pistorius, Exit problems for spectrally negative Lévy processes and applications to (Canadized) Russian options, Ann. Appl. Probab. 14(1), 2004, p. 216, Section 2, first paragraph, Eq. (1) and the sentence after it

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Avram2004.Shared

/-- A spectrally negative Lévy process started at `0` (Avram–Kyprianou–Pistorius 2004, §2, p. 216).
Time is `ℝ≥0`, values are real. The fields are:
* each `X t` is measurable;
* every path starts at `0`;
* independent increments (Mathlib's `HasIndepIncrements`);
* stationary increments: `X (s + t) - X s` has the law of `X t`;
* every path is right-continuous at every time and has a left limit at every `t > 0` (càdlàg);
* no positive jumps: for every path and every `t > 0`, `X t ≤ X (t-)`;
* the paths are not almost surely monotone ("We exclude the case that X has monotone paths"):
  neither almost surely nondecreasing nor almost surely nonincreasing. -/
structure IsSNLevy {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop where
  measurable : ∀ t, Measurable (X t)
  start_zero : ∀ ω, X 0 ω = 0
  indep_increments : HasIndepIncrements X P
  stationary_increments :
    ∀ s t : ℝ≥0, IdentDistrib (fun ω => X (s + t) ω - X s ω) (X t) P P
  right_continuous : ∀ ω (t : ℝ≥0), ContinuousWithinAt (fun r => X r ω) (Set.Ici t) t
  left_limits : ∀ ω (t : ℝ≥0), 0 < t →
    ∃ l : ℝ, Filter.Tendsto (fun r => X r ω) (nhdsWithin t (Set.Iio t)) (nhds l)
  no_positive_jumps : ∀ ω (t : ℝ≥0), 0 < t → X t ω ≤ Function.leftLim (fun r => X r ω) t
  not_ae_monotone : ¬ (∀ᵐ ω ∂P, Monotone fun t => X t ω)
  not_ae_antitone : ¬ (∀ᵐ ω ∂P, Antitone fun t => X t ω)

/-- A spectrally negative Lévy process with respect to a filtration `𝓕` (§2, p. 216: "`X` is a Lévy
process defined on `(Ω, 𝓕, F = {𝓕_t}_{t≥0}, ℙ)`, a filtered probability space which satisfies the usual
conditions"). The fields are:
* `X` is a spectrally negative Lévy process under `P` (`IsSNLevy`);
* `X` is adapted to `𝓕`;
* the increments are independent of the past: `X (s + t) - X s` is independent of `𝓕 s`;
* the filtration is right-continuous (`𝓕_t = ⋂_{u > t} 𝓕_u`), which is how "the usual conditions"
  are read here; completeness of the filtration is not imposed. -/
structure IsSNLevyWrt {Ω : Type*} {m : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 m) (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ) : Prop where
  isSNLevy : IsSNLevy P X
  adapted : Adapted 𝓕 X
  indep_past : ∀ s t : ℝ≥0,
    Indep (MeasurableSpace.comap (fun ω => X (s + t) ω - X s ω) (inferInstance : MeasurableSpace ℝ))
      (𝓕 s) P
  right_continuous_filtration : 𝓕.IsRightContinuous

end Avram2004.Shared


