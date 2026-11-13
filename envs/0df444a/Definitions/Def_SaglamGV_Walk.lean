-- Prove2me | Definitions.Def_SaglamGV_Walk
-- name    : SaglamGV_Walk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:47:44.514413+00:00
-- url     : https://prove2.me/theorems/cb974b01-89a8-49bb-af13-f6ec682d1aa3
-- title:
--   The kernel $\mu=1_{B_d}/V$, zero-sum probabilities $p_\ell$ and the Poisson walk $W_t$ on $\mathbb F_2^{n+1}$
-- statement:
--   The **probability kernel** $\mu(x)=1_{x\in B_d}/V$ is the uniform law on $B_d$. For $X_1,X_2,\dots$ independent with law $\mu$,
--
--   $$
--   p_\ell=\Pr[X_1+\cdots+X_\ell=0],
--   $$
--
--   which, since $\mu$ is uniform, is the number of ordered $\ell$-tuples of elements of $B_d$ (repetitions allowed) summing to $0$, divided by $V^\ell$; $p_0=1$. Let $J_t$ be Poisson with mean $t$, independent of the $X_i$. The continuous-time random walk on $\mathbb F_2^{n+1}$ is
--
--   $$
--   W_t=\sum_{i=1}^{J_t}(X_i,1),
--   $$
--
--   started at $0$, and $e_{n+1}=(0,\dots,0,1)$. Its law at time $\tau$ is the Poisson$(\tau)$ mixture of the convolution powers of the step law of $(X_1,1)$:
--
--   $$
--   \Pr[W_\tau=y]=\sum_{\ell\ge0}e^{-\tau}\frac{\tau^\ell}{\ell!}\Pr\Big[\sum_{i=1}^{\ell}(X_i,1)=y\Big].
--   $$
--
--   The paper bounds the expected number of odd circuits by $\Pr[W_\tau=e_{n+1}]$, the probability of an odd number of steps whose first $n$ coordinates cancel.
--
--   **Formalization Note** `mu`, `zeroSumProb` (counting), `stepLaw` (mass $\mu(x)$ at $(x,1)$), `convPow` (iterated convolution, the $0$-th power the point mass at $0$), `walkProb` (the Poisson mixture above, a `tsum`), `eLast`. The walk is encoded by its law; no process is built. `walkProb` is the law of the walk, not the series in $p_\ell$ that the paper derives from it.
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, pp.2–3 (µ, p_ℓ, J_t, W_t, e_{n+1})

import Mathlib
import Definitions.Def_SaglamGV_Code

namespace SaglamGV

/-- The probability kernel `μ(x) = 1_{x ∈ B_d} / V`, the uniform law on `B_d`
(M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript
(held version, sha256 ac6f2bba…), §2, p.2: "Define the probability kernel µ(x) := 1_{x∈B_d}/V").

**Formalization Note** For `d ≤ 1` (`V = 0`) Lean's `1/0 = 0` makes `μ` the zero function. -/
noncomputable def mu (n d : ℕ) (x : Fin n → ZMod 2) : ℝ :=
  if x ∈ ballP n d then 1 / (vol n d : ℝ) else 0

/-- `p_ℓ = Pr[X₁ + ⋯ + X_ℓ = 0]` for `X₁, X₂, …` i.i.d. with law `μ` (Saglam, §2, p.2).

**Formalization Note** Since `μ` is uniform on `B_d`, `p_ℓ` is the number of ordered `ℓ`-tuples of
elements of `B_d` (repetitions allowed) summing to `0`, divided by `V^ℓ`. `p_0 = 1`. -/
noncomputable def zeroSumProb (n d ℓ : ℕ) : ℝ :=
  ((Finset.univ.filter (fun t : Fin ℓ → (Fin n → ZMod 2) =>
      (∀ i, t i ∈ ballP n d) ∧ ∑ i, t i = 0)).card : ℝ) / (vol n d : ℝ) ^ ℓ

/-- The law of one step `(X, 1) ∈ 𝔽₂^{n+1}` of the walk, `X ∼ μ` (Saglam, §2, p.3: the increments
`(X_i, 1)` of `W_t`): mass `μ(x)` at the word whose first `n` coordinates are `x` and whose last
coordinate is `1`. -/
noncomputable def stepLaw (n d : ℕ) (y : Fin (n + 1) → ZMod 2) : ℝ :=
  if y (Fin.last n) = 1 then mu n d (Fin.init y) else 0

/-- The `ℓ`-fold convolution power of `stepLaw`: the law of `∑_{i=1}^ℓ (X_i, 1)` for i.i.d. `X_i ∼ μ`;
the `0`-th power is the point mass at `0`. -/
noncomputable def convPow (n d : ℕ) : ℕ → (Fin (n + 1) → ZMod 2) → ℝ
  | 0, y => if y = 0 then 1 else 0
  | ℓ + 1, y => ∑ z, convPow n d ℓ z * stepLaw n d (y - z)

/-- `Pr[W_τ = y]` for the continuous-time random walk `W_t = ∑_{i=1}^{J_t} (X_i, 1)` on `𝔽₂^{n+1}`,
`J_t` Poisson with mean `t` independent of the `X_i` (Saglam, §2, p.3: "Let J_t be Poisson with mean
t, independently of the X_i, and define the continuous-time random walk on F_2^{n+1} by
W_t := Σ_{i=1}^{J_t} (X_i, 1). The walk starts at zero").

**Formalization Note** The walk is encoded by its law at time `τ`, the Poisson(`τ`) mixture of the
convolution powers of the step law: `Pr[W_τ = y] = ∑_ℓ e^{−τ} τ^ℓ/ℓ! · Pr[∑_{i≤ℓ}(X_i,1) = y]`. Only
`Pr[W_τ = e_{n+1}]` is used by the paper, so no process is constructed. This is the law of the walk,
not the series in `p_ℓ` that the paper derives from it. -/
noncomputable def walkProb (n d : ℕ) (τ : ℝ) (y : Fin (n + 1) → ZMod 2) : ℝ :=
  ∑' ℓ : ℕ, Real.exp (-τ) * τ ^ ℓ / (ℓ.factorial : ℝ) * convPow n d ℓ y

/-- `e_{n+1} = (0, …, 0, 1) ∈ 𝔽₂^{n+1}` (Saglam, §2, p.3). -/
def eLast (n : ℕ) : Fin (n + 1) → ZMod 2 := Pi.single (Fin.last n) 1

end SaglamGV


