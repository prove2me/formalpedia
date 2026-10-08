-- Prove2me | Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems
-- name    : HomogBiLimit_OutputFeedback_ChainSystems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:02.220987+00:00
-- url     : https://prove2.me/theorems/5329e794-fcdb-4713-850a-4fc1a3394bbf
-- title:
--   Weights (3.2), chain of integrators, observer-error and closed-loop fields, GAS, definiteness, backstepping properties
-- statement:
--   This definition file collects the objects of §§3–5 of the paper.
--
--   1. **Admissible degrees.** For $n\ge2$, a degree $\mathfrak d$ is admissible if $\mathfrak d\in\left(-1,\tfrac1{n-1}\right)$.
--   2. **Weights (3.2).** $r_n=1$ and $r_i=r_{i+1}-\mathfrak d=1-\mathfrak d\,(n-i)$; `weights n 𝔡 o m` is the block $(r_{o+1},\dots,r_{o+m})$, so `weights n 𝔡 0 n` is $r$, `weights n 𝔡 0 i` the prefix $(r_1,\dots,r_i)$ and `weights n 𝔡 i (n-i)` the tail $(r_{i+1},\dots,r_n)$.
--   3. **Chain of integrators.** $S_m x=(x_2,\dots,x_m,0)^T$ is the shift matrix and $B_m u=(0,\dots,0,u)^T$. For a scalar $s$, $K(s)$ means $K(s,0,\dots,0)$ (footnote 6).
--   4. **Systems.** The observer-error system $\dot E=S_mE+K(e)$, $e=E_1$ (equations (3.4)–(3.6), (3.12)); the state-feedback system $\dot{\mathfrak X}=S_m\mathfrak X+B_m\phi(\mathfrak X)$ ((4.3), (4.4), (4.9)); and the closed loop of the chain (5.1) with the output feedback (5.2) on $\mathbb R^{2n}$ with state $(x,\hat{\mathfrak X})$:
--   $$\dot x=S_nx+B_nL^n\phi(\hat{\mathfrak X}),\qquad \dot{\hat{\mathfrak X}}=L\bigl(S_n\hat{\mathfrak X}+B_n\phi(\hat{\mathfrak X})+K(x_1-\hat x_1)\bigr).$$
--   5. **GAS.** Global asymptotic stability (GAS) of the origin of $\dot x=f(x)$ is the published notion `ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable` applied to the time-invariant field ($f(0)=0$, from every initial state there is a solution on $[0,\infty)$, Lyapunov stability and uniform global attractivity for *every* solution on $[0,\infty)$; solutions need not be unique, since the fields are only continuous), together with the requirement that no solution escapes to infinity in finite time, so that every solution is defined on $[0,\infty)$. For a continuous autonomous field this is the textbook notion of GAS (Bacciotti–Rosier, *Liapunov Functions and Stability in Control Theory*, §2; uniform attractivity follows from Kurzweil's converse theorem).
--   6. **Definiteness.** $V$ is positive definite if $V(0)=0$ and $V(x)>0$ for $x\ne0$; $g$ is negative definite if $g(0)=0$ and $g(x)<0$ for $x\ne0$; $V$ is proper if $V(x)\to\infty$ as $|x|\to\infty$. The partial derivative $\partial g/\partial x_j$ is the Fréchet derivative applied to the $j$-th basis vector. The signed power is $w^{r}=\operatorname{sign}(w)|w|^{r}$ (1.4).
--   7. **Backstepping properties (Theorem 4.1).** For $1\le k\le n$, a feedback $\phi_k:\mathbb R^k\to\mathbb R$ with exponent $\alpha$ has the properties of Theorem 4.1 if it is homogeneous in the bi-limit with triples $((r_{0,1},\dots,r_{0,k}),\mathfrak d_0+r_{0,k},\phi_{k,0})$ and $((r_{\infty,1},\dots,r_{\infty,k}),\mathfrak d_\infty+r_{\infty,k},\phi_{k,\infty})$; $\psi_k=\phi_k^{\alpha}$ (signed power) is $C^1$ and there are $C^1$ functions $\psi_{k,0},\psi_{k,\infty}$ such that each $\partial\psi_k/\partial x_j$ is homogeneous in the bi-limit with these weights, degrees $\alpha(r_{0,k}+\mathfrak d_0)-r_{0,j}$ and $\alpha(r_{\infty,k}+\mathfrak d_\infty)-r_{\infty,j}$ and approximating functions $\partial\psi_{k,0}/\partial x_j$, $\partial\psi_{k,\infty}/\partial x_j$; and the origin is GAS for $\dot{\mathfrak X}=S_k\mathfrak X+B_k\phi_k(\mathfrak X)$ and for the same system with $\phi_{k,0}$ and with $\phi_{k,\infty}$.
--
--   **Formalization Note** Indices are 0-based in Lean: `weight n 𝔡 k` is the paper's $r_{k+1}$. On $\mathbb R^{2n}$ (`Fin (n + n) → ℝ`) the first $n$ coordinates are $x$ and the last $n$ are $\hat{\mathfrak X}$. The paper's $\psi_{i0},\psi_{i\infty}$ in Theorem 4.1 are left implicit by the paper and are quantified existentially here. The signed power is defined locally (it duplicates `sgnPow` of `ChitourPrescribedTime.FixedTime.Feedback`).
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, p. 2 (1.4); p. 10 (3.1), (3.2); p. 11 (3.4)–(3.6) and footnote 6; p. 16 (4.1)–(4.4) and Theorem 4.1; p. 20 (5.1), (5.2)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_FixedTime_Stability
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity

noncomputable section

namespace HomogBiLimit.OutputFeedback

/-- The admissible range of degrees of §3–§5 (p. 10): `𝔡 ∈ (−1, 1/(n−1))`. It is only used
together with `2 ≤ n`. -/
def AdmissibleDegree (n : ℕ) (𝔡 : ℝ) : Prop :=
  -1 < 𝔡 ∧ 𝔡 < 1 / ((n : ℝ) - 1)

/-- The weights (3.2), p. 10, indexed from 0: for the chain of length `n` and degree `𝔡`,
`weight n 𝔡 k = r_{k+1} = 1 − 𝔡 (n − (k + 1))`, so `r_n = 1` and `r_i = r_{i+1} − 𝔡`. -/
def weight (n : ℕ) (𝔡 : ℝ) (k : ℕ) : ℝ :=
  1 - 𝔡 * ((n : ℝ) - 1 - (k : ℝ))

/-- The block `(r_{o+1}, …, r_{o+m})` of `m` consecutive weights (3.2) starting after offset
`o`, as a weight vector on `ℝ^m`. `weights n 𝔡 0 n` is the full weight vector `r` of (3.2);
`weights n 𝔡 0 i` is the prefix `(r_1, …, r_i)`; `weights n 𝔡 i (n - i)` is the tail
`(r_{i+1}, …, r_n)`. -/
def weights (n : ℕ) (𝔡 : ℝ) (o m : ℕ) : Fin m → ℝ :=
  fun j => weight n 𝔡 (o + j.val)

/-- The shift matrix of order `m` (p. 10): `S_m x = (x₂, …, x_m, 0)ᵀ`. -/
def shift (m : ℕ) (x : Fin m → ℝ) : Fin m → ℝ :=
  fun j => if h : j.val + 1 < m then x ⟨j.val + 1, h⟩ else 0

/-- `B_m u = (0, …, 0, u)ᵀ ∈ ℝ^m` (p. 10). -/
def lastInput (m : ℕ) (u : ℝ) : Fin m → ℝ :=
  fun j => if j.val + 1 = m then u else 0

/-- The first coordinate `x₁` of `x ∈ ℝ^m` (`0` when `m = 0`). -/
def first {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  if h : 0 < m then x ⟨0, h⟩ else 0

/-- `(s, 0, …, 0)ᵀ ∈ ℝ^m`. Footnote 6, p. 11: `K(s)` for a scalar `s` means `K(s, 0, …, 0)`. -/
def axisVec (m : ℕ) (s : ℝ) : Fin m → ℝ :=
  fun j => if j.val = 0 then s else 0

/-- The time-invariant field `(t, x) ↦ f(x)` on the Euclidean space `ℝ^m` associated with a
vector field `f` on `ℝ^m`. -/
def euclidField {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ)) :
    ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
  fun _ x => WithLp.toLp 2 (f (WithLp.ofLp x))

/-- No finite escape time: every solution of `ẋ = f(x)` defined on a bounded interval
`[0, T)` (in integral form, as in `ChitourPrescribedTime.FixedTime.IsSol`) is bounded there.
For a continuous field this says that every solution extends to `[0, ∞)`. -/
def NoFiniteEscape {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ)) : Prop :=
  ∀ (T : ℝ) (x : ℝ → EuclideanSpace ℝ (Fin m)), 0 < T →
    (∀ t : ℝ, 0 ≤ t → t < T →
      IntervalIntegrable (fun τ => euclidField f τ (x τ)) MeasureTheory.volume 0 t ∧
        x t = x 0 + ∫ τ in (0 : ℝ)..t, euclidField f τ (x τ)) →
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → ‖x t‖ ≤ M

/-- Global asymptotic stability of the origin of the autonomous system `ẋ = f(x)` on `ℝ^m`:
the published notion `ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable` (the
origin is an equilibrium, every initial state has a solution on `[0, ∞)`, Lyapunov stability
and uniform global attractivity over all solutions on `[0, ∞)`) applied to the time-invariant
field, together with `NoFiniteEscape` (no solution escapes in finite time, so every solution
is one of those on `[0, ∞)`). -/
def IsGAS {m : ℕ} (f : (Fin m → ℝ) → (Fin m → ℝ)) : Prop :=
  ChitourPrescribedTime.FixedTime.GloballyAsymptoticallyStable (euclidField f) ∧
    NoFiniteEscape f

/-- The observer-error system (3.4)–(3.6), (3.12) on `ℝ^m`: `Ė = S_m E + K(e)`, where `e` is
the first coordinate of `E` and `K(e)` means `K(e, 0, …, 0)` (footnote 6, p. 11). -/
def errorField {m : ℕ} (K : (Fin m → ℝ) → (Fin m → ℝ)) (E : Fin m → ℝ) : Fin m → ℝ :=
  shift m E + K (axisVec m (first E))

/-- The chain of integrators (4.1)–(4.4), (4.9) on `ℝ^m` in closed loop with the state
feedback `u = φ(𝔛)`: `𝔛̇ = S_m 𝔛 + B_m φ(𝔛)`. -/
def feedbackField {m : ℕ} (φ : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ) : Fin m → ℝ :=
  shift m x + lastInput m (φ x)

/-- The closed loop of the chain of integrators (5.1) with the output feedback (5.2), p. 20,
as an autonomous vector field on `ℝ^{2n}` with state `(x, 𝔛̂)`: the first `n` coordinates are
the plant state `x` and the last `n` are the observer state `𝔛̂`,
`ẋ = S_n x + B_n Lⁿ φ(𝔛̂)`,
`𝔛̂̇ = L (S_n 𝔛̂ + B_n φ(𝔛̂) + K(x₁ − x̂₁))`, with `K(s) = K(s, 0, …, 0)` (footnote 6). -/
def closedLoop (n : ℕ) (φ : (Fin n → ℝ) → ℝ) (K : (Fin n → ℝ) → (Fin n → ℝ)) (L : ℝ)
    (z : Fin (n + n) → ℝ) : Fin (n + n) → ℝ :=
  let x : Fin n → ℝ := fun i => z (Fin.castAdd n i)
  let xh : Fin n → ℝ := fun i => z (Fin.natAdd n i)
  Fin.append (shift n x + lastInput n (L ^ n * φ xh))
    (L • (shift n xh + lastInput n (φ xh) + K (axisVec n (first x - first xh))))

/-- Positive definite (p. 9): `V(0) = 0` and `V(x) > 0` for `x ≠ 0`. -/
def IsPosDef {m : ℕ} (V : (Fin m → ℝ) → ℝ) : Prop :=
  V 0 = 0 ∧ ∀ x, x ≠ 0 → 0 < V x

/-- Negative definite (p. 9): `g(0) = 0` and `g(x) < 0` for `x ≠ 0`. -/
def IsNegDef {m : ℕ} (g : (Fin m → ℝ) → ℝ) : Prop :=
  g 0 = 0 ∧ ∀ x, x ≠ 0 → g x < 0

/-- Proper (p. 9): `V(x) → +∞` as `‖x‖ → ∞` (preimages of bounded sets are bounded). -/
def IsProper {m : ℕ} (V : (Fin m → ℝ) → ℝ) : Prop :=
  Filter.Tendsto V (Filter.cocompact (Fin m → ℝ)) Filter.atTop

/-- The signed power (1.4), p. 2: `w^r = sign(w) |w|^r`. -/
def signedPow (w r : ℝ) : ℝ :=
  Real.sign w * |w| ^ r

/-- The partial derivative `∂g/∂x_j (x)` (index `j` from 0), as the Fréchet derivative of `g`
at `x` applied to the `j`-th basis vector. -/
def partialDeriv {m : ℕ} (g : (Fin m → ℝ) → ℝ) (j : Fin m) (x : Fin m → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single j 1)

/-- The two properties of Theorem 4.1, p. 16, for a state feedback `φ_k : ℝ^k → ℝ` of the
chain of integrators of length `k` (`1 ≤ k ≤ n`), with weights and degrees (3.2) of the chain
of length `n`, and with exponent `α`:
* `φ_k` is homogeneous in the bi-limit with triples `((r_{0,1},…,r_{0,k}), 𝔡₀ + r_{0,k}, φ_{k,0})`
  and `((r_{∞,1},…,r_{∞,k}), 𝔡∞ + r_{∞,k}, φ_{k,∞})`;
* (property 1) `ψ_k = φ_k^{α}` (signed power) is `C¹` and there are `C¹` functions `ψ_{k,0}`,
  `ψ_{k,∞}` such that for each `j ≤ k` the function `∂ψ_k/∂𝓍_j` is homogeneous in the
  bi-limit with weights `(r_{0,1},…,r_{0,k})`, `(r_{∞,1},…,r_{∞,k})`, degrees
  `α(r_{0,k} + 𝔡₀) − r_{0,j}`, `α(r_{∞,k} + 𝔡∞) − r_{∞,j}` and approximating functions
  `∂ψ_{k,0}/∂𝓍_j`, `∂ψ_{k,∞}/∂𝓍_j`;
* (property 2) the origin is globally asymptotically stable for `𝔛̇ = S_k 𝔛 + B_k φ_k(𝔛)`,
  `𝔛̇ = S_k 𝔛 + B_k φ_{k,0}(𝔛)` and `𝔛̇ = S_k 𝔛 + B_k φ_{k,∞}(𝔛)`. -/
def BacksteppingProps (n : ℕ) (𝔡₀ 𝔡inf : ℝ) (k : ℕ) (φ φ₀ φinf : (Fin k → ℝ) → ℝ) (α : ℝ) :
    Prop :=
  IsHomogBiLimit φ (weights n 𝔡₀ 0 k) (𝔡₀ + weight n 𝔡₀ (k - 1)) φ₀
      (weights n 𝔡inf 0 k) (𝔡inf + weight n 𝔡inf (k - 1)) φinf ∧
    (ContDiff ℝ 1 (fun x => signedPow (φ x) α) ∧
      ∃ ψ₀ ψinf : (Fin k → ℝ) → ℝ, ContDiff ℝ 1 ψ₀ ∧ ContDiff ℝ 1 ψinf ∧
        ∀ j : Fin k,
          IsHomogBiLimit (partialDeriv (fun x => signedPow (φ x) α) j)
            (weights n 𝔡₀ 0 k) (α * (weight n 𝔡₀ (k - 1) + 𝔡₀) - weight n 𝔡₀ j.val)
            (partialDeriv ψ₀ j)
            (weights n 𝔡inf 0 k) (α * (weight n 𝔡inf (k - 1) + 𝔡inf) - weight n 𝔡inf j.val)
            (partialDeriv ψinf j)) ∧
    (IsGAS (feedbackField φ) ∧ IsGAS (feedbackField φ₀) ∧ IsGAS (feedbackField φinf))

end HomogBiLimit.OutputFeedback


