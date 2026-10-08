-- Prove2me | Definitions.Def_PrivLearn_LocalSim_Simulation
-- name    : PrivLearn_LocalSim_Simulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:17.020388+00:00
-- url     : https://prove2.me/theorems/32139572-9897-43df-a333-48957effe790
-- title:
--   SQ algorithms, valid transcripts, the randomizer R_g, the local algorithm A_g and the simulation of §5.1.1
-- statement:
--   Fix a domain $D$ (a measurable space).
--
--   1. **SQ algorithm with $t$ queries** (Definitions 5.4–5.5). For a fixed string of its coins, the algorithm is given by: for each $k=0,\dots,t-1$, the query $g_k(a_0,\dots,a_{k-1}):D\to\mathbb R$ and the tolerance $\tau_k(a_0,\dots,a_{k-1})$ it asks after receiving the answers $a_0,\dots,a_{k-1}$, and its output $\mathrm{out}(a_0,\dots,a_{t-1})$. It is **nonadaptive** if every query and tolerance is fixed before any answer is received.
--   2. A vector $a=(a_0,\dots,a_{t-1})$ is a **valid transcript** against $SQ_P$ if for every $k$
--   $$\bigl|a_k-\mathbb E_{u\sim P}\bigl[g_k(a_0,\dots,a_{k-1})(u)\bigr]\bigr|\le \tau_k(a_0,\dots,a_{k-1}),$$
--   that is, every answer is a valid SQ answer to the query actually asked at that point.
--   3. **The randomizer** $R_g(u)=g(u)+\eta$ with $\eta\sim\mathrm{Lap}(s)$ (p. 20; the paper takes $s=2b/\varepsilon$), as the law of its output on input $u$.
--   4. **The local algorithm $\mathcal A_g(n,\varepsilon,LR_z)$** (p. 20) applies $R_g$ once to every entry of $z$ and outputs the average of the responses,
--   $$\mathcal A_g(z)=\frac1n\sum_{i=1}^n\bigl(g(z_i)+\eta_i\bigr),\qquad \eta_1,\dots,\eta_n\ \text{i.i.d.}\ \mathrm{Lap}(2b/\varepsilon).$$
--   5. **The simulation** (p. 21). With block size $m$ and a database $z$ of size $n\ge tm$, the $k$-th query is answered by running $\mathcal A_{g_k}(m,\varepsilon,LR_z)$ on the $k$-th block of $m$ entries $z_{km},\dots,z_{km+m-1}$, where $g_k$ is the query the SQ algorithm asks after the earlier simulated answers:
--   $$a_k=\frac1m\sum_{i=0}^{m-1}\Bigl(g_k(a_0,\dots,a_{k-1})(z_{km+i})+\eta_{k,i}\Bigr),$$
--   with all $tm$ noises $\eta_{k,i}$ i.i.d. $\mathrm{Lap}(2b/\varepsilon)$. The simulation outputs $\mathrm{out}(a_0,\dots,a_{t-1})$. Its output law on $z$ is the image of the noise law under this map.
--
--   These objects are the statement of Theorem 5.7: the simulation turns any SQ algorithm into an $\varepsilon$-local, hence $\varepsilon$-differentially private, algorithm.
--
--   **Formalization Note.** A randomized SQ algorithm is a mixture of deterministic strategies over its coins; a guarantee for every fixed coin string gives the guarantee for the mixture, so the deterministic strategy is the unit. "At most $t$ queries" is "exactly $t$" after padding with dummy queries. The blocks are disjoint index ranges: entry $(k,i)$ of the block structure is database index $km+i$ (`finProdFinEquiv`), so every entry enters at most one randomizer, and entries with index $\ge tm$ are unused. The simulated answers are defined by recursion on $k$ as a deterministic function of the database and the noise vector. For $m=0$ or $n=0$ Lean's convention $1/0=0$ makes the average $0$; the theorems never use a zero block where it matters. Running time ("efficient") and the interaction pattern of the simulation are not modelled.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 19 (Definitions 5.4, 5.5), p. 20 (§5.1.1, R_g and the local algorithm A_g), p. 21 (Simulation)

import Mathlib
import Definitions.Def_PrivLearn_LocalSim_Privacy

namespace PrivLearn.LocalSim

open MeasureTheory

/-- An SQ algorithm making `t` queries (Definitions 5.4–5.5, p. 19), for one fixed string of its
coins. The `k`-th query `(g, τ_k)` (`k = 0, …, t − 1`) may depend on the answers to the first `k`
queries (adaptive); the output is a function of all `t` answers. -/
structure SQAlg (Dom Out : Type*) (t : ℕ) where
  /-- the query function `g_k`, as a function of the earlier answers -/
  query : (k : Fin t) → (Fin k → ℝ) → Dom → ℝ
  /-- the tolerance `τ_k`, as a function of the earlier answers -/
  tol : (k : Fin t) → (Fin k → ℝ) → ℝ
  /-- the output, as a function of all answers -/
  output : (Fin t → ℝ) → Out

variable {Dom Out : Type*} {t : ℕ}

/-- Definition 5.5 (p. 19): the SQ algorithm is nonadaptive if every query and tolerance is fixed
before any answer is received. -/
def SQAlg.IsNonadaptive (A : SQAlg Dom Out t) : Prop :=
  ∀ (k : Fin t) (a a' : Fin k → ℝ), A.query k a = A.query k a' ∧ A.tol k a = A.tol k a'

/-- The first `k` entries `a_0, …, a_{k−1}` of an answer vector `a`. -/
def answerPrefix (a : Fin t → ℝ) (k : Fin t) : Fin k → ℝ :=
  fun j => a (Fin.castLE k.2.le j)

/-- `a` is a transcript of `A` against a valid SQ oracle `SQ_P` (Definition 5.4): for every `k`,
the answer `a_k` is within the tolerance `τ_k` of the true mean of the query `g_k` that `A` asks
after receiving `a_0, …, a_{k−1}`. -/
def SQAlg.IsValidTranscript [MeasurableSpace Dom] (A : SQAlg Dom Out t) (P : Measure Dom)
    (a : Fin t → ℝ) : Prop :=
  ∀ k : Fin t, IsSQAnswer P (A.query k (answerPrefix a k)) (A.tol k (answerPrefix a k)) (a k)

/-- The local randomizer `R_g(u) = g(u) + η`, `η ∼ Lap(s)` (p. 20), as the law of its output on the
input `u`. The paper takes `s = 2b/ε`. -/
noncomputable def randomizerLaw (g : Dom → ℝ) (s : ℝ) (u : Dom) : Measure ℝ :=
  (PrivLearn.Generic.laplace s).map fun η => g u + η

/-- The output of the local algorithm `A_g(n, ε, LR_z)` (p. 20) on the database `z` when the
randomizer applied to entry `i` draws the noise `η_i`: the average
`(1/n) ∑_{i} (g(z_i) + η_i)` of the `n` responses `LR_z(i, R_g)`. -/
noncomputable def avgResp {n : ℕ} (g : Dom → ℝ) (z : Fin n → Dom) (η : Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (g (z i) + η i)

/-- The law of the output of `A_g(n, ε, LR_z)` on the database `z`: the noises
`η_1, …, η_n` are i.i.d. `Lap(2b/ε)`. -/
noncomputable def avgRespLaw {n : ℕ} (g : Dom → ℝ) (b ε : ℝ) (z : Fin n → Dom) : Measure ℝ :=
  (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace (2 * b / ε)).map (avgResp g z)

/-- The block of the database used for the `k`-th query (p. 21, "a previously unused portion of
the database z containing n′ entries"): with block size `m` and `t * m ≤ n`, the `i`-th entry of
block `k` is the database entry with index `k * m + i`. Distinct pairs `(k, i)` give distinct
indices, so blocks are disjoint and entries with index `≥ t * m` are never used. -/
def blockIdx {m n : ℕ} (h : t * m ≤ n) (k : Fin t) (i : Fin m) : Fin n :=
  Fin.castLE h (finProdFinEquiv (k, i))

/-- The `k`-th answer of the simulation (p. 21), for `k < t`, on the database `z` and the noise
`η` (`η k i` is the noise drawn by the randomizer applied to the `i`-th entry of block `k`):
`A_g(m, ε, LR_z)` run on block `k` for the query `g = g_k` that `A` asks after the earlier
simulated answers, i.e. `a_k = (1/m) ∑_{i<m} (g_k(z_{k m + i}) + η_{k,i})`. -/
noncomputable def simAnswer (A : SQAlg Dom Out t) {n : ℕ} (m : ℕ) (h : t * m ≤ n)
    (z : Fin n → Dom) (η : Fin t → Fin m → ℝ) : (k : ℕ) → k < t → ℝ
  | k, hk =>
    (1 / (m : ℝ)) * ∑ i : Fin m,
      (A.query ⟨k, hk⟩ (fun j : Fin k => simAnswer A m h z η j.1 (lt_trans j.2 hk))
          (z (blockIdx h ⟨k, hk⟩ i)) + η ⟨k, hk⟩ i)

/-- The transcript `(a_0, …, a_{t−1})` of simulated answers (p. 21), block size `m`. -/
noncomputable def simTranscript (A : SQAlg Dom Out t) {n : ℕ} (m : ℕ) (h : t * m ≤ n)
    (z : Fin n → Dom) (η : Fin t → Fin m → ℝ) : Fin t → ℝ :=
  fun k => simAnswer A m h z η k.1 k.2

/-- The law of all the noises of the simulation: `t * m` i.i.d. `Lap(2b/ε)` variables. -/
noncomputable def noiseLaw (t m : ℕ) (b ε : ℝ) : Measure (Fin t → Fin m → ℝ) :=
  Measure.pi fun _ : Fin t => Measure.pi fun _ : Fin m => PrivLearn.Generic.laplace (2 * b / ε)

/-- The law of the output of the simulation (p. 21) on the database `z`: `A` is run on the
simulated answers. -/
noncomputable def simOutputLaw [MeasurableSpace Out] (A : SQAlg Dom Out t) (b ε : ℝ) {n : ℕ}
    (m : ℕ) (h : t * m ≤ n) (z : Fin n → Dom) : Measure Out :=
  (noiseLaw t m b ε).map fun η => A.output (simTranscript A m h z η)

end PrivLearn.LocalSim


