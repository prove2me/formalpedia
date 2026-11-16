-- Prove2me | Definitions.Def_DecodablePOMDP_Supplement_SlowForgetting
-- name    : DecodablePOMDP_Supplement_SlowForgetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:44:39.797723+00:00
-- url     : https://prove2.me/theorems/9ff69a43-58db-43f4-bc2e-3a6720f7f0ce
-- title:
--   The slow-forgetting family of App. C.1 and the expected filter distance $D_h=\mathbb E_{b_0}\|b_h-\widehat b_h\|_1$
-- statement:
--   Let $n\ge1$ and let $M\in\{0,1\}^{n\times n}$ be the biadjacency matrix of a simple bipartite graph $G=(\mathcal L,\mathcal R,E)$, $\mathcal L=\{L_1,\dots,L_n\}$, $\mathcal R=\{R_1,\dots,R_n\}$, with $M_{ij}=1$ iff $\{L_i,R_j\}\in E$. The family of App. C.1 requires
--
--   1. every row sum and every column sum of $M$ to equal $3$ ($G$ is 3-regular), and
--   2. $\sigma_2(M)\le2\sqrt2$, where $\sigma_2$ is the second largest singular value; equivalently, at most one eigenvalue of $M^\top M$, counted with multiplicity, exceeds $8$.
--
--   The POMDP has the $S=2n$ states $\mathcal L\cup\mathcal R$, one action, the stationary transition kernel $T(L_k\mid L_i)=T(R_k\mid R_j)=1/n$ (no moves between groups) and observations $\mathcal O=E\cup\{g_+,g_-\}$ with
--
--   $$K(e\mid s)=\tfrac16\,\mathbf 1\{s\text{ is an endpoint of }e\},\qquad K(g_\pm\mid L_i)=\tfrac14\pm\tfrac1{8\sqrt n},\qquad K(g_\pm\mid R_j)=\tfrac14\mp\tfrac1{8\sqrt n}.$$
--
--   For an initial law $\beta$ let $X_0\sim\beta$, $X_t\sim T(\cdot\mid X_{t-1})$ and $Y_t\sim K(\cdot\mid X_t)$ for $t\ge1$, and let $b^\beta_h(s;y_{1:h})=\Pr_\beta(X_h=s\mid Y_{1:h}=y_{1:h})$ be the filter. With $b_0=\mathrm{Unif}(\mathcal L)$ and $\widehat b_0=\frac12\mathrm{Unif}(\mathcal L)+\frac12\mathrm{Unif}(\mathcal R)$, write $b_h$, $\widehat b_h$ for the two filters run on the same observations. The **expected filter distance** is
--
--   $$D_h=\mathbb E_{b_0}\|b_h-\widehat b_h\|_1=\sum_{y\in\mathcal O^h}\Pr_{b_0}(Y_{1:h}=y)\,\big\|b_h(\cdot;y)-\widehat b_h(\cdot;y)\big\|_1 .$$
--
--   This is the example on which Theorem 6 shows that filters forget their initialisation only after order $S\log(1/\varepsilon)$ observations.
--
--   **Formalization Note** States are `Fin n ⊕ Fin n` (left = $\mathcal L$), observations are the edges $\{(i,j)\mid M_{ij}=1\}$ plus `Bool` (`true` = $g_+$). Probabilities and filters are finite sums computed by the forward recursion $\alpha_0=\beta$, $\alpha_t(s')=\big(\sum_s\alpha_{t-1}(s)T(s'\mid s)\big)K(y_t\mid s')$. The sum defining $D_h$ runs over all of $\mathcal O^h$; histories of probability $0$ contribute $0$. Because $T$ fixes $\mathrm{Unif}(\mathcal L)$, $\mathrm{Unif}(\mathcal R)$ and their mixtures, starting the laws at $X_1$ instead of $X_0$ gives the same $D_h$; $D_0=1$.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), App. C.1, pp.24–25, (22); App. C.2, pp.25–26, (23)

import Mathlib
import Definitions.Def_DecodablePOMDP_Supplement_Observability

namespace DecodablePOMDP.Supplement

/-- **Biadjacency matrix of a simple 3-regular bipartite graph** `G = (L, R, E)`, `|L| = |R| = n`
(App. C.1, p.24): `M i j = true` iff `{L_i, R_j}` is an edge, and every row sum and every column sum
of `M` equals `3`.

Dobson, Jog, Shiu, *Quasipolynomial-Time Planning for Decodable POMDPs* (preprint, sha256
c1256cbe…3584b), App. C.1, p.24: "Let G = (L, R, E) be a simple 3-regular bipartite graph and
|L| = |R| = n. … their biadjacency matrix (indicating connections from L to R) M ∈ {0, 1}^{n×n} has
every row and column sum equal to 3".

**Formalization Note.** A `{0,1}` matrix is a `Bool` matrix; simplicity (no repeated edges) is built
into the encoding. -/
def IsCubicBiadjacency {n : ℕ} (M : Fin n → Fin n → Bool) : Prop :=
  (∀ i, (Finset.univ.filter (fun j => M i j = true)).card = 3) ∧
  (∀ j, (Finset.univ.filter (fun i => M i j = true)).card = 3)

/-- The real `n × n` matrix with entries `1` where `M` is `true` and `0` elsewhere. -/
def realBiadj {n : ℕ} (M : Fin n → Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if M i j then 1 else 0

/-- **Second singular value at most `b`** (App. C.1, p.24, "σ₂(M) ≤ 2√2"). For `b ≥ 0`,
`σ₂(A) ≤ b` holds iff at most one eigenvalue of `AᵀA`, counted with multiplicity, exceeds `b²`
(the eigenvalues of `AᵀA` are the squared singular values `σ₁² ≥ σ₂² ≥ …`).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. C.1, p.24: "… and satisfies
σ2(M) ≤ 2√2."

**Formalization Note.** Uses Mathlib's `Matrix.IsHermitian.eigenvalues` of the Hermitian matrix
`Aᴴ A` (`= Aᵀ A` for real `A`), an indexed list of its eigenvalues with multiplicity. -/
noncomputable def SecondSingularValueLE {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : ℝ) : Prop :=
  (Finset.univ.filter
    (fun i => b ^ 2 < (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)).card ≤ 1

/-- The edges `E = {(i, j) | M i j = true}` of the bipartite graph; `(i, j)` is the edge
`{L_i, R_j}`. -/
abbrev Edge {n : ℕ} (M : Fin n → Fin n → Bool) : Type :=
  {e : Fin n × Fin n // M e.1 e.2 = true}

/-- States `S = L ⊕ R` (`Sum.inl i = L_i`, `Sum.inr j = R_j`), `S = 2n`. -/
abbrev State (n : ℕ) : Type := Fin n ⊕ Fin n

/-- Observations `O = E ⊕ {g₊, g₋}` (`Sum.inr true = g₊`, `Sum.inr false = g₋`), of size `3n + 2`. -/
abbrev Obs {n : ℕ} (M : Fin n → Fin n → Bool) : Type := Edge M ⊕ Bool

/-- **Transition kernel (22)** (App. C.1, p.24), `transT n s s' = T(s' | s)`: the state is resampled
uniformly within its current group, `T(L_k | L_i) = T(R_k | R_j) = 1/n`, and never moves between
groups. The same kernel at every stage.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. C.1, (22), p.24. -/
noncomputable def transT (n : ℕ) : State n → State n → ℝ
  | Sum.inl _, Sum.inl _ => 1 / (n : ℝ)
  | Sum.inr _, Sum.inr _ => 1 / (n : ℝ)
  | _, _ => 0

/-- **Observation kernel** (App. C.1, pp.24–25), `obsK M s o = K(o | s)`:
`K(e | s) = 1/6 · 1{s is an endpoint of e}`; `K(g₊ | L_i) = 1/4 + 1/(8√n)`,
`K(g₊ | R_j) = 1/4 − 1/(8√n)`, `K(g₋ | L_i) = 1/4 − 1/(8√n)`, `K(g₋ | R_j) = 1/4 + 1/(8√n)`.
The same kernel at every stage.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. C.1, pp.24–25: "for e ∈ E and s ∈ S,
K(e | s) = (1/6) 1{s is an endpoint of e}. … K(g+ | Li) = 1/4 + 1/(8√n), K(g+ | Rj) = 1/4 − 1/(8√n),
K(g− | Li) = 1/4 − 1/(8√n), K(g− | Rj) = 1/4 + 1/(8√n)." -/
noncomputable def obsK {n : ℕ} (M : Fin n → Fin n → Bool) : State n → Obs M → ℝ
  | Sum.inl i, Sum.inl e => if e.1.1 = i then 1 / 6 else 0
  | Sum.inr j, Sum.inl e => if e.1.2 = j then 1 / 6 else 0
  | Sum.inl _, Sum.inr true => 1 / 4 + 1 / (8 * Real.sqrt n)
  | Sum.inl _, Sum.inr false => 1 / 4 - 1 / (8 * Real.sqrt n)
  | Sum.inr _, Sum.inr true => 1 / 4 - 1 / (8 * Real.sqrt n)
  | Sum.inr _, Sum.inr false => 1 / 4 + 1 / (8 * Real.sqrt n)

/-- `b_L = Unif(L)`. -/
noncomputable def bL (n : ℕ) : State n → ℝ
  | Sum.inl _ => 1 / (n : ℝ)
  | Sum.inr _ => 0

/-- `b_R = Unif(R)`. -/
noncomputable def bR (n : ℕ) : State n → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => 1 / (n : ℝ)

/-- The true initial law `b₀ = b_L` (App. C.1, p.25). -/
noncomputable def b0 (n : ℕ) : State n → ℝ := bL n

/-- The second filter's initial law `b̂₀ = ½ b_L + ½ b_R` (App. C.1, p.25). -/
noncomputable def bhat0 (n : ℕ) : State n → ℝ := fun s => bL n s / 2 + bR n s / 2

/-- **Forward (unnormalised filter) vector.** For a stationary hidden Markov model with transition
kernel `T s s' = T(s' | s)`, observation kernel `K s y = K(y | s)`, initial law `β` of `X₀`, and an
observation sequence `ys = [y₁, …, y_h]` (oldest first),
`forward T K β ys s = Pr_β(X_h = s, Y_{1:h} = y_{1:h})`, where `X_t ~ T(· | X_{t−1})` and
`Y_t ~ K(· | X_t)` for `t ≥ 1`. Recursion: `α₀ = β`,
`α_t(s') = (Σ_s α_{t−1}(s) T(s' | s)) K(y_t | s')`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. C.1, p.25 ("Write X_h and Y_h for the
state and observation at stage h"). -/
def forward {S O : Type} [Fintype S] (T : S → S → ℝ) (K : S → O → ℝ) (β : S → ℝ) (ys : List O) :
    S → ℝ :=
  ys.foldl (fun α y => fun s' => (∑ s, α s * T s s') * K s' y) β

/-- `Pr_β(Y_{1:h} = y_{1:h}) = Σ_s forward T K β ys s`. -/
def obsProb {S O : Type} [Fintype S] (T : S → S → ℝ) (K : S → O → ℝ) (β : S → ℝ) (ys : List O) :
    ℝ :=
  ∑ s, forward T K β ys s

/-- **The filter** `b_h^β(s; y_{1:h}) = Pr_β(X_h = s | Y_{1:h} = y_{1:h})`, the forward vector
normalised by `Pr_β(Y_{1:h} = y_{1:h})`.

**Formalization Note.** On a history of probability `0` Lean's division gives the zero vector;
such histories carry weight `0` in `filterDist`. -/
noncomputable def filter {S O : Type} [Fintype S] (T : S → S → ℝ) (K : S → O → ℝ) (β : S → ℝ)
    (ys : List O) : S → ℝ :=
  fun s => forward T K β ys s / obsProb T K β ys

/-- **Expected filter distance** (Theorem 6, p.25; (23), p.26):
`D_h = E_{b₀} ‖b_h − b̂_h‖₁ = Σ_{y ∈ O^h} Pr_{b₀}(Y_{1:h} = y) ‖b_h(·; y) − b̂_h(·; y)‖₁`,
where `b_h` is the filter started at `b₀ = b_L` and `b̂_h` the filter started at
`b̂₀ = ½ b_L + ½ b_R`, both run on the same history with the kernels of the C.1 family, and the
expectation is under the true process started at `b₀`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. C.1–C.2, pp.25–26: "bh(s; y1:h) =
Pr_{b0}(Xh = s | Y1:h = y1:h), b̂h(s; y1:h) = Pr_{b̂0}(Xh = s | Y1:h = y1:h)", "Dh := E_{b0}∥bh − b̂h∥1".

**Formalization Note.** The sum runs over all of `O^h`; a history with `Pr_{b₀} = 0` contributes
`0`, so this equals the sum over histories of positive probability. The initial law is that of
`X₀` and `Y₁` is observed after the first transition; since `T` fixes `b_L`, `b_R` and every mixture
of them, taking the initial law as that of `X₁` instead gives the same `D_h`. `D₀ = ‖b₀ − b̂₀‖₁ = 1`. -/
noncomputable def filterDist {n : ℕ} (M : Fin n → Fin n → Bool) (h : ℕ) : ℝ :=
  ∑ y : Fin h → Obs M,
    obsProb (transT n) (obsK M) (b0 n) (List.ofFn y) *
      l1norm (fun s => filter (transT n) (obsK M) (b0 n) (List.ofFn y) s -
        filter (transT n) (obsK M) (bhat0 n) (List.ofFn y) s)

end DecodablePOMDP.Supplement


