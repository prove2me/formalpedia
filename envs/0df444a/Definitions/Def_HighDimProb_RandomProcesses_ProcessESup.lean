-- Prove2me | Definitions.Def_HighDimProb_RandomProcesses_ProcessESup
-- name    : HighDimProb_RandomProcesses_ProcessESup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:11.532975+00:00
-- url     : https://prove2.me/theorems/39f0b06a-b12c-467f-9a23-12d2ccf4fb0b
-- title:
--   The expected supremum $E \sup_{t\in T} X_t$ of a random process
-- statement:
--   This is the **expected supremum** of a random process, the basic quantity Chapter 7 studies:
--   how large a family of (not necessarily independent) random variables gets on average, uniformly
--   over its index set.
--
--   Fix a probability space $(\Omega, \mathcal F, P)$ and a family $(X_t)_{t\in T}$ of real random
--   variables indexed by an arbitrary set $T$ (not assumed countable). When $T$ is finite this is
--   just $E\max_{t\in T} X_t$. For a general $T$, $\sup_{t\in T} X_t(\omega)$ need not even be a
--   measurable function of $\omega$, so $E\sup_{t\in T}X_t$ is not defined as the expectation of a
--   pointwise supremum. Instead, following Vershynin's own convention for this chapter, it is
--   defined through the process's finite-dimensional marginals:
--
--   $$
--   E \sup_{t\in T} X_t \;:=\; \sup_{T_0 \subseteq T \text{ finite, nonempty}} E \max_{t\in T_0} X_t.
--   $$
--
--   This quantity is the subject of Slepian's, Sudakov-Fernique's, and Sudakov's inequalities, and
--   reappears throughout the book as the Gaussian width of a set (Chapter 7.5 onward).
--
--   **Formalization Note** The value is taken in the extended reals `EReal` rather than `ℝ`: for a
--   process unbounded across its finite marginals (e.g. a non-relatively-compact canonical Gaussian
--   process, Exercise 7.4.2), the book's own convention is that this quantity equals $\infty$. A
--   real-valued supremum would instead silently default to the junk value $0$ in that case, making
--   any inequality stated against it vacuous.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 156, footnote 3 to Section 7.2

import Mathlib

open MeasureTheory

namespace HighDimProb.RandomProcesses

/-- The **expected supremum** `E sup_{t∈T} X_t` of a random process `(X_t)_{t∈T}` on a
probability space `(Ω, P)`. To avoid the measurability issues an arbitrary (possibly
uncountable) index set `T` creates for `sup_t X_t ω` itself, this is understood exactly as
Vershynin's own footnote to Section 7.2 requires, through the process's finite-dimensional
marginals:

`E sup_{t∈T} X_t := sup { E max_{t∈T0} X_t : T0 ⊆ T finite and nonempty }`.

Vershynin, *High-Dimensional Probability* (2018), p. 156 (PDF p. 164), footnote 3 to Section
7.2 ("we interpret `E sup_{t∈T} X_t` more formally as `sup_{T0⊂T} E max_{t∈T0} X_t` where the
supremum is over all finite subsets `T0 ⊆ T`"). Valued in `EReal`, not `ℝ`: a real-valued
`sSup` would silently default to the junk value `0` whenever the underlying set of finite
marginals is unbounded above (e.g. Exercise 7.4.2's non-compact case, where the book itself
records the value as `∞`), which would make comparison theorems stated against it vacuous. -/
noncomputable def processESup {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {T : Type}
    (X : T → Ω → ℝ) : EReal :=
  ⨆ (T0 : {s : Finset T // s.Nonempty}), ((∫ ω, T0.1.sup' T0.2 (fun t => X t ω) ∂P : ℝ) : EReal)

end HighDimProb.RandomProcesses


