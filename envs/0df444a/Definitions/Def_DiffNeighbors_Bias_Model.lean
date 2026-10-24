-- Prove2me | Definitions.Def_DiffNeighbors_Bias_Model
-- name    : DiffNeighbors_Bias_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:45.943758+00:00
-- url     : https://prove2.me/theorems/fdbc8446-97ef-4bc7-8f41-4246e5629bd7
-- title:
--   §2.1, (1), (3), §3.2, §3.3, pp. 4–10 — network interference model, Assumption 1, ATE, conditional outcomes, second-order differences, ϵ-smoothness, Bernoulli design and the DN estimator
-- statement:
--   The objects of Peng, Ye and Zheng's analysis of the Differences-in-Neighbors (DN) estimator (§2.1, pp. 4–5; §3, pp. 7–10).
--
--   1. **Units, graph and treatments.** There are $N$ units. Interference between them is an undirected graph $G$ without self-loops; $\mathcal N_i$ is the set of neighbours of unit $i$ (so $i \notin \mathcal N_i$) and $d = \max_i |\mathcal N_i|$ is the maximum degree. A treatment assignment is a vector $z \in \{0,1\}^N$.
--   2. **Potential outcomes.** Each unit $i$ has an outcome function $f_i : \{0,1\}^N \to \mathbb R$, and the observed outcome is $Y_i = f_i(z)$.
--   3. **Assumption 1 (Neighborhood Interference)**, p. 5. For all $i$ and all $z, z'$: if $z_j = z'_j$ for every $j \in \{i\} \cup \mathcal N_i$, then $f_i(z) = f_i(z')$.
--   4. **Average treatment effect**, p. 5:
--   $$\mathrm{ATE} = \frac1N \sum_{i=1}^N \bigl(f_i(\vec 1) - f_i(\vec 0)\bigr).$$
--   5. **Conditional outcome functions** (1), p. 5: $f^a_i$, $a \in \{0,1\}$, is the outcome of unit $i$ when its own treatment is $a$, so that $f_i(z) = f^{z_i}_i(z)$.
--   6. **Second-order finite differences and $\epsilon$-smoothness**, p. 9. Writing $z^{(z_j=a,z_k=b)}$ for $z$ with its $j$-th and $k$-th entries replaced by $a$ and $b$,
--   $$\Delta_{jk} h(z) = h(z^{(z_j=1,z_k=1)}) - h(z^{(z_j=0,z_k=1)}) - h(z^{(z_j=1,z_k=0)}) + h(z^{(z_j=0,z_k=0)}),$$
--   and $h$ is $\epsilon$-smooth if $|\Delta_{jk} h(z)| \le \epsilon$ for every $z \in \{0,1\}^N$ and every $j, k \in [N]$.
--   7. **Multilinear extension and the Bernoulli design**, pp. 7, 10. For $w \in \mathbb R^N$,
--   $$F(w) = \sum_{z \in \{0,1\}^N} \Bigl(\prod_{j} \bigl(z_j w_j + (1 - z_j)(1 - w_j)\bigr)\Bigr) h(z),$$
--   which for $w \in [0,1]^N$ is $\mathbb E[h(Z)]$ with independent $Z_j \sim \mathrm{Bernoulli}(w_j)$. The experimental design draws $z_i$ i.i.d. Bernoulli$(p)$, so $\mathbb E[h(Z)] = F(p, \dots, p)$, and $\Pr(Z_i = 1) = p$, $\Pr(Z_i = 0) = 1 - p$.
--   8. **The DN estimator** (3), p. 7:
--   $$\mathrm{ATE}_{\mathrm{DN}} = \frac1N \sum_{i=1}^N \Bigl(\frac{z_i}{p} - \frac{1 - z_i}{1 - p}\Bigr)\Bigl(\sum_{j \in \mathcal N_i} Y_j\, \xi_j + Y_i\Bigr), \qquad \xi_j = \frac{z_j(1-p)}{p} + \frac{(1 - z_j)p}{1 - p}.$$
--
--   These definitions carry every statement of the mission: Theorem 1 bounds $|\mathrm{ATE} - \mathbb E[\mathrm{ATE}_{\mathrm{DN}}]|$, and its proof runs through the multilinear extension $F^a$ of each $f^a_i$.
--
--   **Formalization Note** Units are a finite type `ι` (with $N$ = `Fintype.card ι`), treatments are `ι → Bool`, and `ind` sends `true`/`false` to $1$/$0$. The graph is a Mathlib `SimpleGraph`, so $\mathcal N_i$ is `G.neighborFinset i` and $d$ is `G.maxDegree`. `condOutcome f i a` is $f^a_i$ viewed on the whole vector, $z \mapsto f_i(z \text{ with } z_i := a)$; under Assumption 1 it depends only on $z_{\mathcal N_i}$, which is the paper's $f^a_i(z_{\mathcal N_i})$. $z^{(z_j=a,z_k=b)}$ is `update (update z j a) k b`, so for $j = k$ the later write wins and $\Delta_{jj} h \equiv 0$. The multilinear extension `mlExt` sums over all coordinates; for a function of $z_{\mathcal N_i}$ only it agrees with the paper's $F$ (the other factors sum to one). `bernExp p h` is the expectation under the Bernoulli$(p)$ design, and the conditional expectation $\mathbb E[h(Z) \mid Z_j = b]$ is `bernExp p (fun z => h (update z j b))`. `dnEstimator G p f z` is (3) evaluated at the realised vector $z$.
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, pp. 4–5, §2.1, Assumption 1, ATE, (1); p. 7, §3, Bernoulli design, (3); p. 9, §3.2, second-order differences and ϵ-smoothness; p. 10, §3.3, F¹(w)

import Mathlib

noncomputable section

namespace DiffNeighbors.Bias

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real value of a binary treatment: `ind true = 1`, `ind false = 0`
(Peng–Ye–Zheng, arXiv:2503.02271v1, §2.1, p. 5: treatments `z_i ∈ {0, 1}`). -/
def ind (b : Bool) : ℝ := if b then 1 else 0

/-- **Assumption 1 (Neighborhood Interference)**, p. 5. Units are the elements of the finite type `ι`,
the interference graph is the simple (undirected, loopless) graph `G`, so that `N_i = {j : G.Adj i j}`,
and `f i : (ι → Bool) → ℝ` is the potential outcomes function of unit `i`. The assumption: for every
unit `i` and treatment vectors `z, z'`, if `z_j = z'_j` for all `j ∈ {i} ∪ N_i`, then
`f_i(z) = f_i(z')`. -/
def NeighborhoodInterference (G : SimpleGraph ι) (f : ι → (ι → Bool) → ℝ) : Prop :=
  ∀ i (z z' : ι → Bool), (∀ j, (j = i ∨ G.Adj i j) → z j = z' j) → f i z = f i z'

/-- The average treatment effect, p. 5: `ATE = (1/N) ∑_i (f_i(1⃗) − f_i(0⃗))` with `N = |ι|`. -/
def ate (f : ι → (ι → Bool) → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (f i (fun _ => true) - f i (fun _ => false))

/-- The conditional outcome function `f^a_i` of (1), p. 5, viewed as a function on the whole treatment
vector: `condOutcome f i a z = f_i(z with its i-th entry set to a)`, so that `f_i(z) = f^{z_i}_i(z)`.
Under Assumption 1 it depends only on `z_{N_i}`, which is the paper's `f^a_i(z_{N_i})`. -/
def condOutcome (f : ι → (ι → Bool) → ℝ) (i : ι) (a : Bool) : (ι → Bool) → ℝ :=
  fun z => f i (Function.update z i a)

/-- The second-order finite difference of p. 9, in the printed order of terms:
`Δ_jk h(z) = h(z^(z_j=1,z_k=1)) − h(z^(z_j=0,z_k=1)) − h(z^(z_j=1,z_k=0)) + h(z^(z_j=0,z_k=0))`,
where `z^(z_j=a,z_k=b)` is `update (update z j a) k b` (for `j = k` the later write wins, so
`Δ_jj h ≡ 0`). -/
def secondDiff (h : (ι → Bool) → ℝ) (j k : ι) (z : ι → Bool) : ℝ :=
  h (Function.update (Function.update z j true) k true)
    - h (Function.update (Function.update z j false) k true)
    - h (Function.update (Function.update z j true) k false)
    + h (Function.update (Function.update z j false) k false)

/-- `h` is `ε`-smooth (p. 9): `|Δ_jk h(z)| ≤ ε` for every `z ∈ {0,1}^N` and every `j, k ∈ [N]`. -/
def IsSmooth (ε : ℝ) (h : (ι → Bool) → ℝ) : Prop :=
  ∀ (z : ι → Bool) (j k : ι), |secondDiff h j k z| ≤ ε

/-- The multilinear extension `F(w) = ∑_z (∏_j (z_j w_j + (1 − z_j)(1 − w_j))) h(z)` (§3.3, p. 10),
taken over all coordinates of `ι`. For `w ∈ [0,1]^ι` it is the expectation of `h(Z)` when the `Z_j` are
independent Bernoulli(`w_j`); for an `h` that depends only on the coordinates in `N_i` it equals the
paper's `F(w)`, because the remaining factors sum to one. -/
def mlExt (h : (ι → Bool) → ℝ) (w : ι → ℝ) : ℝ :=
  ∑ z : ι → Bool, (∏ j, if z j then w j else 1 - w j) * h z

/-- `E[h(Z)]` under the Bernoulli design of §3, p. 7: `Z_j` i.i.d. Bernoulli(`p`). It is the
multilinear extension at the constant vector `(p, …, p)`. Since the coordinates are independent, the
conditional expectation `E[h(Z) | Z_j = b]` is `bernExp p (fun z => h (Function.update z j b))`, and
`E[h(Z) | Z_j = b, Z_k = c]` (for `j ≠ k`) is
`bernExp p (fun z => h (Function.update (Function.update z j b) k c))`. -/
def bernExp (p : ℝ) (h : (ι → Bool) → ℝ) : ℝ :=
  mlExt h (fun _ => p)

/-- The probability `Pr(Z_i = a)` of a treatment value under Bernoulli(`p`): `p` for `a = 1`,
`1 − p` for `a = 0`. -/
def bernProb (p : ℝ) (a : Bool) : ℝ := if a then p else 1 - p

/-- The difference-in-means weight `η_i = z_i/p − (1 − z_i)/(1 − p)` of (2)–(3), p. 7. -/
def eta (p : ℝ) (z : ι → Bool) (i : ι) : ℝ :=
  ind (z i) / p - (1 - ind (z i)) / (1 - p)

/-- The propensity score correction `ξ_j = z_j(1 − p)/p + (1 − z_j)p/(1 − p)` of (3), p. 7. -/
def xi (p : ℝ) (z : ι → Bool) (j : ι) : ℝ :=
  ind (z j) * (1 - p) / p + (1 - ind (z j)) * p / (1 - p)

/-- The Differences-in-Neighbors estimator (3), p. 7, evaluated at the realised treatment vector `z`
with observed outcomes `Y_j = f_j(z)`:
`ATE_DN = (1/N) ∑_i (z_i/p − (1 − z_i)/(1 − p)) (∑_{j ∈ N_i} Y_j ξ_j + Y_i)`. -/
def dnEstimator (G : SimpleGraph ι) [DecidableRel G.Adj] (p : ℝ) (f : ι → (ι → Bool) → ℝ)
    (z : ι → Bool) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ i, eta p z i * (∑ j ∈ G.neighborFinset i, f j z * xi p z j + f i z)

end DiffNeighbors.Bias

end


