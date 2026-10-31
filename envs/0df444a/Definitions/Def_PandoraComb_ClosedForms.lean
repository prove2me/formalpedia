-- Prove2me | Definitions.Def_PandoraComb_ClosedForms
-- name    : PandoraComb_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:59.206442+00:00
-- url     : https://prove2.me/theorems/55c196b1-2f44-4ee1-86da-6be3e871adcd
-- title:
--   Marginal cost $c(x\mid S)$ and the closed forms $q(\pi)$, $p(\pi)$, $p(\pi_P)$, $u_N(\pi_P\mid T)$ of impulsive strategies
-- statement:
--   Fix probabilities $p_i$, weights $v_i$ and a cost $c$. Let $\pi=(i_1,\dots,i_k)$ be an impulsive strategy (distinct boxes), $q_i=1-p_i$, and write $q(i_1,\dots,i_{j-1})=\prod_{l<j}q_{i_l}$.
--
--   1. **Marginal cost:** $c(x\mid S)=c(S\cup\{x\})-c(S)$.
--   2. $q(\pi)=\prod_{j=1}^k(1-p_{i_j})$ and $p(\pi)=1-q(\pi)$, the probability that some box of $\pi$ is non-zero; $p(\emptyset)=0$.
--   3. For $P\subseteq\pi$, the **impulsive strategy with dummies** $\pi_P$ runs like $\pi$, but at a box $i\in\pi\setminus P$ it does not inspect $i$; it halts with probability $p_i$ and otherwise moves on. Its probability of finding a non-zero value is
--   $$p(\pi_P)=\sum_{j:\ i_j\in P}q(i_1,\dots,i_{j-1})\,p_{i_j}.$$
--   4. For a base set $R$ (the paper's $\{r\}$) and a set $T$ of boxes already opened,
--   $$u_N(\pi_P\mid T)=\sum_{j:\ i_j\in P}q(i_1,\dots,i_{j-1})\Big(p_{i_j}v_{i_j}-c\big(i_j\ \big|\ R\cup T\cup\{i_l:\ l<j,\ i_l\in P\}\big)\Big).$$
--   With $P=\pi$ this is Observation 3's formula for $u_N(\pi\mid T)$, and $u_N(\pi)=u_N(\pi\mid\emptyset)$.
--
--   These quantities are the language of Lemmas 3.2–3.4 and Observation 5, the core of the proof that impulsive strategies are optimal on Bernoulli instances.
--
--   **Formalization Note** The quantities are defined by the paper's own closed-form expressions (Observation 2, Observation 3 and the worked example of p.11), not by expectations over runs. Dummy boxes keep their factor $q_i$ in the later terms but are never opened, so they do not enter the conditioning set of the cost.
-- source:
--   Berger, Ezra, Feldman & Fusco, Pandora’s Problem with Combinatorial Cost, arXiv:2303.01078v1, §2, p.8 (marginal contribution c(x | S)); §3.1, p.10 (p(π), q(π), Observation 2, Definition 3.1, Observation 3); p.11 (impulsive strategies with dummies and the worked example)

import Mathlib

noncomputable section

namespace PandoraComb

/-- **Marginal cost** `c(x | S) := c(S ∪ {x}) − c(S)` (arXiv:2303.01078v1, §2, p.8). -/
def marginal {ι : Type*} [DecidableEq ι] (c : Finset ι → ℝ) (x : ι) (S : Finset ι) : ℝ :=
  c (insert x S) - c S

/-- **`q(π)`** for the impulsive strategy `π = l` of a Bernoulli instance with probabilities `p`
(§3.1, p.10, Observation 2): `q(π) = ∏_{j} (1 − p_{i_j})`, the probability that every box of `π`
is zero; `q(∅) = 1`. -/
def qL {ι : Type*} (p : ι → ℝ) (l : List ι) : ℝ :=
  (l.map fun i => 1 - p i).prod

/-- **`p(π) := 1 − q(π)`** (§3.1, p.10): the probability that one of the boxes inspected by the
impulsive strategy `π = l` has a non-zero value; `p(∅) = 0`. -/
def pL {ι : Type*} (p : ι → ℝ) (l : List ι) : ℝ :=
  1 - qL p l

/-- **`p(π_P)`** for the impulsive strategy with dummies `π_P` (§3.1, p.11), `π = l`, `P ⊆ π`:
the probability that one of the boxes inspected by `π_P` has a non-zero value,
`Σ_{j : l_j ∈ P} q(l_1, …, l_{j−1}) · p_{l_j}` ("in the example above this probability equals
q2p1 + q(2,1,4)p7", p.11). A dummy box `i ∈ π ∖ P` is not inspected; it halts with probability
`p_i`, so it still contributes its factor `q_i` to the later terms. -/
def pD {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (l : List ι) (P : Finset ι) : ℝ :=
  ∑ j : Fin l.length, if l.get j ∈ P then qL p (l.take j) * p (l.get j) else 0

/-- **`u_N(π_P | T)`** (Definition 3.1, p.10, with Observation 3, p.10, and the dummies of p.11):
the marginal utility of the impulsive strategy with dummies `π_P` (`π = l`, `P ⊆ π`) given that
`V_r = 0` and that the boxes in `T` were already opened,
`Σ_{j : l_j ∈ P} q(l_1, …, l_{j−1}) · (p_{l_j} v_{l_j} − c(l_j | {r} ∪ T ∪ {l_k : k < j, l_k ∈ P}))`.

**Formalization Note.** The paper's `{r}` is a base set `R` (`R = {r}`). Dummy boxes multiply the
later terms by their factor `q_i` but are never opened, so they do not enter the conditioning set
(the worked example of p.11). With `P = π` this is Observation 3's formula for `u_N(π | T)`;
`u_N(π) = u_N(π | ∅)`. -/
def uND {ι : Type*} [DecidableEq ι] (v p : ι → ℝ) (c : Finset ι → ℝ) (R : Finset ι)
    (l : List ι) (P T : Finset ι) : ℝ :=
  ∑ j : Fin l.length,
    if l.get j ∈ P then
      qL p (l.take j) * (p (l.get j) * v (l.get j) -
        marginal c (l.get j) (R ∪ T ∪ ((l.take j).filter (fun i => i ∈ P)).toFinset))
    else 0

end PandoraComb


