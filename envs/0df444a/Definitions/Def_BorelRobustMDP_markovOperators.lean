-- Prove2me | Definitions.Def_BorelRobustMDP_markovOperators
-- name    : BorelRobustMDP_markovOperators
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:34.463201+00:00
-- url     : https://prove2.me/theorems/e330ccf0-fc07-4a12-b7e9-ff9821a01a2d
-- title:
--   The operators $L_n$, $\mathcal T_{nd\gamma}$, $\mathcal T_{nd}$, $\mathcal T_n$, and minimizers and maximizers
-- statement:
--   For $v$ on $E$, Markov rules $d:E\to A$ and $\gamma:D_n\to\mathcal Q_{n+1}$:
--
--   $$L_nv(x,a,Q)=\int c_n(x,a,T_n(x,a,Z_{n+1}))+v(T_n(x,a,Z_{n+1}))\,dQ,$$
--
--   $$\mathcal T_{nd\gamma}v(x)=L_nv(x,d(x),\gamma(x,d(x))),\quad\mathcal T_{nd}v(x)=\sup_{Q\in\mathcal Q_{n+1}}L_nv(x,d(x),Q),\quad\mathcal T_nv(x)=\inf_{a\in D_n(x)}\sup_{Q\in\mathcal Q_{n+1}}L_nv(x,a,Q).$$
--
--   A Markov decision rule $d$ is a **minimizer** of $v$ at time $n$ if $\sup_QL_nv(x,d(x),Q)=\mathcal T_nv(x)$ for all $x$. A measurable $g:E\times A\to\mathcal Q_{n+1}$ is a **maximizer** if it attains $\sup_QL_nv(x,a,Q)$ at every $(x,a)\in D_n$.
--
--   These operators state the robust Bellman equation.
--
--   **Formalization Note.** The supremum and infimum are real ones over the types $\mathcal Q_{n+1}$ and $D_n(x)$, which are non-empty for $n<N$.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, Definition 3.8, p.9, Theorem 3.10, p.10, and (3.2), p.11

import Mathlib
import Definitions.Def_BorelRobustMDP_RobustModel
import Definitions.Def_BorelRobustMDP_MarkovPolicy

open MeasureTheory

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- `L_n v(x, a, Q) = ∫ c_n(x, a, T_n(x, a, Z_{n+1})) + v(T_n(x, a, Z_{n+1})) dQ` (Bäuerle & Glauner,
arXiv:2007.13103v1, Definition 3.8, p.9). -/
noncomputable def L (R : RobustModel E A Z N) (n : ℕ) (v : E → ℝ) (y : E × A) (Q : Measure Z) : ℝ :=
  ∫ z, R.c n y (R.T n y z) + v (R.T n y z) ∂Q

/-- `sup_{Q∈𝒬_{n+1}} L_n v(x, a, Q)`, the worst case of `L_n v` at `y = (x, a)`.

**Formalization Note.** A real supremum over the non-empty type `𝒬_{n+1}`, bounded by Remark 3.2 (a)
for `v ∈ 𝔹_b`, `y ∈ D_n`. -/
noncomputable def supL (R : RobustModel E A Z N) (n : ℕ) (v : E → ℝ) (y : E × A) : ℝ :=
  ⨆ Q : R.Amb (n + 1), L R n v y Q.measure

/-- `𝒯_{ndγ} v(x) = L_n v(x, d(x), γ(x, d(x)))` (Bäuerle & Glauner, arXiv:2007.13103v1, Definition 3.8,
p.9). -/
noncomputable def Tdg (R : RobustModel E A Z N) (n : ℕ) (v : E → ℝ) (d : E → A)
    (γ : E × A → R.Amb (n + 1)) (x : E) : ℝ :=
  L R n v (x, d x) (γ (x, d x)).measure

/-- `𝒯_{nd} v(x) = sup_{Q∈𝒬_{n+1}} L_n v(x, d(x), Q)` (Bäuerle & Glauner, arXiv:2007.13103v1,
Definition 3.8, p.9). -/
noncomputable def Td (R : RobustModel E A Z N) (n : ℕ) (v : E → ℝ) (d : E → A) (x : E) : ℝ :=
  supL R n v (x, d x)

/-- `𝒯_n v(x) = inf_{a∈D_n(x)} sup_{Q∈𝒬_{n+1}} L_n v(x, a, Q)` (Bäuerle & Glauner,
arXiv:2007.13103v1, Definition 3.8, p.9).

**Formalization Note.** A real infimum over the subtype `D_n(x)`, which is non-empty for `n < N`. -/
noncomputable def Tmin (R : RobustModel E A Z N) (n : ℕ) (v : E → ℝ) (x : E) : ℝ :=
  ⨅ a : R.sec n x, supL R n v (x, a)

/-- `d` is a Markov minimizer of `v` at time `n` (Bäuerle & Glauner, arXiv:2007.13103v1, Theorem 3.10,
p.10, and (3.2), p.11): a Markov decision rule attaining `𝒯_n v` at every state. -/
def IsMinimizer (R : RobustModel E A Z N) (n : ℕ) (v : E → ℝ) (d : E → A) : Prop :=
  IsDecisionRule R.toDecisionModel n d ∧ ∀ x, supL R n v (x, d x) = Tmin R n v x

/-- `g` is a maximizing Markov decision rule of nature for `v` at time `n`: it attains
`sup_{Q∈𝒬_{n+1}} L_n v(x, a, Q)` at every `(x, a) ∈ D_n`. -/
def IsMaximizer (R : RobustModel E A Z N) (n : ℕ) (v : E → ℝ) (g : E × A → R.Amb (n + 1)) : Prop :=
  Measurable g ∧ ∀ y ∈ R.D n, L R n v y (g y).measure = supL R n v y

end BorelRobustMDP


