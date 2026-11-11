-- Prove2me | Definitions.Def_NonMarkovColorings_Main_LabelingChain
-- name    : NonMarkovColorings_Main_LabelingChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:08:50.519196+00:00
-- url     : https://prove2.me/theorems/8a4604cb-64a6-4168-ac5f-c55eb93848cc
-- title:
--   The Metropolis rule on all labelings $\widehat\Omega=[k]^V$, runs along update sequences, the uniform law on update sequences, and $T$-step couplings (§3, pp. 11–12)
-- statement:
--   Colors are $[k]$ (in Lean $\{0,\dots,k-1\}$). A **labeling** is any $X:V\to[k]$; $\widehat\Omega=[k]^V$. Write $X\oplus Y=\{v: X(v)\ne Y(v)\}$, $A(X,u)=[k]\setminus X(N(u))$ and $A_v(X,u)=[k]\setminus X(N(u)\setminus\{v\})$. The **extended Metropolis rule** (p. 11): an update $(u,c)\in V\times[k]$ sends $X$ to $X'$ with $X'(w)=X(w)$ for $w\ne u$ and
--   $$X'(u)=\begin{cases}c & c\notin X(N(u)),\\ X(u) & c\in X(N(u)).\end{cases}$$
--   An **update sequence** of length $T$ is $\vec\sigma=((v_1,c_1),\dots,(v_T,c_T))$; $X_0$ evolved by $\vec\sigma$ gives $X_1,\dots,X_T$. The transition matrix of the rule on $\widehat\Omega$ is $P(X,Y)=\#\{(u,c): X\xrightarrow{(u,c)}Y\}/(nk)$, $n=|V|$. Probabilities and expectations over the discrete-time dynamics are taken with $\vec\sigma$ uniform on $(V\times[k])^T$: counts and sums divided by $(nk)^T$. A **$T$-step coupling** is a probability distribution $\mu$ on pairs $(\vec\sigma,\vec\sigma')$ of update sequences of length $T$ whose two marginals are uniform; the first chain runs on $\vec\sigma$, the second on $\vec\sigma'$.
--
--   **Formalization Note.** `diffSet`, `avail`, `availExcept`, `metStep`, `run G X0 σ t` ($=X_t$; constant after $T$), `labelingChain G k`, `seqProb V k T E`, `seqExp V k T f`, `IsSeqCoupling V k T μ` (the published `MarkovMixing.IsCoupling` of the two uniform laws). The entry `σ i` of `σ : Fin T → V × Fin k` is the paper's update at time $i+1$.
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), pp. 11–12 §3; p. 6 §1.3; p. 33; p. 41

import Mathlib
import Definitions.Def_mm_mixing

/-!
# The Metropolis rule on all labelings, runs along update sequences, and their uniform law

Jain, Mizgerd, Vigoda, *Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling
and Local Uniformity*, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), §1.3 p. 6,
§3 pp. 11–12, §5 p. 33, §6 p. 41, §8 p. 64.

* Colors are `Fin k` (the paper's `[k] = {1, …, k}`, shifted to `0, …, k-1`); a labeling is any
  `X : V → Fin k` (the extended state space `Ω̂ = [k]^V`).
* `diffSet X Y` is `X ⊕ Y = {v : X(v) ≠ Y(v)}`.
* `avail G X u` is `A(X, u) = [k] \ X(N(u))`; `availExcept G X v u` is
  `A_v(X, u) = [k] \ X(N(u) \ {v})`.
* `metStep G X (u, c)` is one step of the extended Metropolis rule (p. 11): `u` takes color `c` if
  `c ∉ X(N(u))`, and nothing else changes.
* An update sequence of length `T` is `σ : Fin T → V × Fin k`; entry `σ ⟨s - 1, _⟩` is the
  paper's `(v_s, c_s)` at time `s ∈ [T]`. `run G X0 σ t` is `X_t`, the labeling after the first
  `t` updates (`X_0 = X0`; times beyond `T` repeat `X_T`).
* `labelingChain G k` is the transition matrix of the extended rule on `Ω̂`:
  `P(X, Y) = #{(u, c) : metStep G X (u, c) = Y} / (n k)`.
* `seqProb T E` and `seqExp T f` are probability and expectation for `σ` uniform on
  `(V × [k])^T`, i.e. counts and sums divided by `(n k)^T`.
* `IsSeqCoupling μ` says `μ` is a joint law of a pair `(σ, σ')` of update sequences of length
  `T` whose two marginals are uniform (a `T`-step coupling of the dynamics: `X` runs on `σ`,
  `Y` on `σ'`).
-/

namespace NonMarkovColorings.Main

noncomputable section

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An update sequence of length `T`: entry `i` is the update `(v_{i+1}, c_{i+1})`. -/
abbrev UpdSeq (V : Type*) (k T : ℕ) := Fin T → V × Fin k

/-- `X ⊕ Y`: the vertices where two labelings differ. -/
def diffSet {k : ℕ} (X Y : V → Fin k) : Finset V :=
  Finset.univ.filter fun v => X v ≠ Y v

/-- `A(X, u) = [k] \ X(N(u))`: colors available at `u`. -/
def avail (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (X : V → Fin k) (u : V) :
    Finset (Fin k) :=
  Finset.univ \ (G.neighborFinset u).image X

/-- `A_v(X, u) = [k] \ X(N(u) \ {v})`: colors available at `u` ignoring the color of `v`. -/
def availExcept (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (X : V → Fin k) (v u : V) :
    Finset (Fin k) :=
  Finset.univ \ ((G.neighborFinset u).erase v).image X

/-- One step of the extended Metropolis rule with update `(u, c)`: `u` is recolored `c` when
`c ∉ X(N(u))`, and otherwise keeps its color; all other vertices keep their colors. -/
def metStep (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (X : V → Fin k) (uc : V × Fin k) :
    V → Fin k :=
  Function.update X uc.1 (if uc.2 ∈ avail G X uc.1 then uc.2 else X uc.1)

/-- `run G X0 σ t = X_t`: the labeling after the first `t` updates of `σ` (constant after `T`). -/
def run (G : SimpleGraph V) [DecidableRel G.Adj] {k T : ℕ} (X0 : V → Fin k) (σ : UpdSeq V k T) :
    ℕ → (V → Fin k)
  | 0 => X0
  | j + 1 => if h : j < T then metStep G (run G X0 σ j) (σ ⟨j, h⟩) else run G X0 σ j

/-- The transition matrix of the extended Metropolis rule on all labelings `Ω̂ = [k]^V`:
`P(X, Y)` is the fraction of the `n k` updates `(u, c)` that take `X` to `Y`. -/
def labelingChain (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    Matrix (V → Fin k) (V → Fin k) ℝ :=
  fun X Y => ((Finset.univ.filter fun uc : V × Fin k => metStep G X uc = Y).card : ℝ) /
    ((Fintype.card V : ℝ) * k)

/-- Probability of an event for `σ` uniform on `(V × [k])^T`. -/
def seqProb (V : Type*) [Fintype V] (k T : ℕ) (E : UpdSeq V k T → Prop) : ℝ :=
  ((Finset.univ.filter E).card : ℝ) / ((Fintype.card V : ℝ) * k) ^ T

/-- Expectation of `f` for `σ` uniform on `(V × [k])^T`. -/
def seqExp (V : Type*) [Fintype V] (k T : ℕ) (f : UpdSeq V k T → ℝ) : ℝ :=
  (∑ σ, f σ) / ((Fintype.card V : ℝ) * k) ^ T

/-- A `T`-step coupling of the dynamics: a joint law of `(σ, σ')` whose marginals are both
uniform on `(V × [k])^T`. -/
def IsSeqCoupling (V : Type*) [Fintype V] [DecidableEq V] (k T : ℕ)
    (μ : UpdSeq V k T × UpdSeq V k T → ℝ) : Prop :=
  MarkovMixing.IsCoupling (MarkovMixing.uniformDist (UpdSeq V k T))
    (MarkovMixing.uniformDist (UpdSeq V k T)) μ

end

end NonMarkovColorings.Main


