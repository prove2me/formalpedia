-- Prove2me | Definitions.Def_NonmonotoneSubmod_SmoothLS_SLSAlgorithm
-- name    : NonmonotoneSubmod_SmoothLS_SLSAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:08:03.102327+00:00
-- url     : https://prove2.me/theorems/5bb12506-6afe-4b30-95c7-4517d0d84e74
-- title:
--   Algorithm SLS — accurate estimates, one iteration, termination
-- statement:
--   Let $f$ be a set function on a finite ground set $X$ with $n = |X|$ elements, let $OPT = \max_{S\subseteq X} f(S)$, and let $\delta$ be the bias of Algorithm SLS (Smooth Local Search).
--
--   1. An estimate $\tilde\omega : X \to \mathbb{R}$ of $\omega_{A,\delta}$ is **accurate** if $|\tilde\omega(x) - \omega_{A,\delta}(x)| \le \frac{1}{n^2} OPT$ for every $x \in X$ (step 2: "within $\pm\frac{1}{n^2}OPT$").
--   2. **One iteration** from the current set $A$ with estimates $\tilde\omega$ to the next set $A'$ is either
--      - step 3: some $x \in X \setminus A$ has $\tilde\omega(x) > \frac{2}{n^2} OPT$, and $A' = A \cup \{x\}$; or
--      - step 4, reached only if step 3 does not apply (every $x \notin A$ has $\tilde\omega(x) \le \frac{2}{n^2}OPT$): some $x \in A$ has $\tilde\omega(x) < -\frac{2}{n^2} OPT$, and $A' = A \setminus \{x\}$.
--
--      Any element meeting the condition may be chosen.
--   3. The algorithm has **terminated** at $A$ with estimates $\tilde\omega$ if no iteration applies; it then proceeds to step 5 and returns a random set $\mathcal{R}(A,\delta')$.
--
--   These are the rules of Algorithm SLS; a run starts from $A = \emptyset$ and recomputes the estimates for the current set before each iteration.
--
--   **Formalization Note** The thresholds and the accuracy use $OPT$ itself, as the proof of Theorem 3.6 does; step 1 of the algorithm says an estimate of $OPT$ is used in practice. The sampling procedure that produces the estimates is not modelled: accuracy is a property of the estimate supplied.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1142, Algorithm SLS, steps 1-5

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The estimate `est` of `ω_{A,δ}` used in step 2 of Algorithm SLS (p. 1142) is accurate
"within `± (1/n²) OPT`", where `n = |X|`: `|est x - ω_{A,δ}(x)| ≤ OPT / n²` for every `x`. -/
def Accurate (f : Finset X → ℝ) (δ : ℝ) (A : Finset X) (est : X → ℝ) : Prop :=
  ∀ x : X, |est x - omegaB f A δ x| ≤ NonmonotoneSubmod.Shared.OPT f / (Fintype.card X : ℝ) ^ 2

/-- One iteration of Algorithm SLS (steps 3 and 4, p. 1142), given the current set `A`, the
current estimates `est` of `ω_{A,δ}`, and the next set `A'`, with `n = |X|`:
* step 3: some `x ∉ A` has `est x > (2/n²) OPT`, and `A' = A ∪ {x}`;
* step 4 (reached only when step 3 does not apply, i.e. `est x ≤ (2/n²) OPT` for every
  `x ∉ A`): some `x ∈ A` has `est x < -(2/n²) OPT`, and `A' = A \ {x}`.
Any such `x` may be chosen. -/
def SLSStep (f : Finset X → ℝ) (est : X → ℝ) (A A' : Finset X) : Prop :=
  (∃ x, x ∉ A ∧ 2 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f < est x ∧ A' = insert x A) ∨
  ((∀ x, x ∉ A → est x ≤ 2 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ∧
    ∃ x, x ∈ A ∧ est x < -(2 / (Fintype.card X : ℝ) ^ 2 * NonmonotoneSubmod.Shared.OPT f) ∧ A' = A.erase x)

/-- Algorithm SLS has terminated at `A` with estimates `est` (it reaches step 5): neither step 3
nor step 4 applies. -/
def SLSTerminated (f : Finset X → ℝ) (est : X → ℝ) (A : Finset X) : Prop :=
  ¬ ∃ A' : Finset X, SLSStep f est A A'

end NonmonotoneSubmod.SmoothLS


