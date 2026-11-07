-- Prove2me | Definitions.Def_PackingLPAccel_Proxy
-- name    : PackingLPAccel_Proxy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:42:43.328529+00:00
-- url     : https://prove2.me/theorems/fb699614-2ba1-4a51-aa35-4a20f7506f32
-- title:
--   The $\ell_{q,p}$ proxy: Bregman divergences, $\mu$, $M$, $\mathcal E^\lambda_{q,p}$ and the corrected residual $\mathcal F$
-- statement:
--   For $x\ge0$ the module writes out the Bregman divergences
--
--   $$V^{\|\cdot\|_q^q}_x(x+y)=\sum_i\bigl(|x_i+y_i|^q-x_i^q-qx_i^{q-1}y_i\bigr),\qquad V^{\|\cdot\|_q^{pq}}_x(x+y)=(\|x+y\|_q^q)^p-(\|x\|_q^q)^p-p(\|x\|_q^q)^{p-1}\sum_iqx_i^{q-1}y_i,$$
--
--   the positive movement $\mu(y;x)=\sum_i[(x_i+|y_i|)^q-x_i^q]$, and the proxy
--
--   $$M(y;x)=p\|x\|_q^{(p-1)q}V^{\|\cdot\|_q^q}_x(x+y)+2p^2\|x\|_q^{(p-2)q}\mu(y;x)^2+p^p\mu(y;x)^p.$$
--
--   It also defines the energy $\mathcal E^\lambda_{q,p}(X)=\psi(X)+\lambda\sum_i(\sum_j|X_{ij}|^q)^p$ and the residual
--
--   $$\mathcal F(\Delta;X)=\psi(X+\Delta)-\psi(X)+\sum_{i,j}c_{ij}(\Delta_{ij})+\sum_i\Bigl[v^{(2)}_i\Bigl(\sum_j\phi_{ij}(\Delta_{ij})\Bigr)^2+v^{(p)}_i\Bigl(\sum_j\phi_{ij}(\Delta_{ij})\Bigr)^p\Bigr],$$
--
--   with $\phi_{ij}(t)=(X_{ij}+|t|)^q-X_{ij}^q$, $c_{ij}(t)=\lambda pq_i^{p-1}[|X_{ij}+t|^q-X_{ij}^q]$, $v^{(2)}_i=2\lambda p^2q_i^{p-2}$, $v^{(p)}_i=\lambda p^p$ and $q_i=\sum_jX_{ij}^q$.
--
--   **Formalization Note** This residual corrects (18)–(22) of the paper in two symbols: (21) prints $(X_{ij}+|t|)^q$ in $c_{ij}$ and (22) prints $\lambda p^2$. As printed the residual is nonnegative, with minimum $0$ at $\Delta=0$, so iterative refinement would never move on $E(x)=x^4$. With `Real.rpow`, $0^0=1$ at $p=2$, $x=0$.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), §5.2, pp.23–25 (pdf 24–26), displays (16)–(22); Problem 5.1, p.18 (pdf 19); Bregman divergence, p.7 (pdf 8)

import Mathlib
import Definitions.Def_PackingLPAccel_CompositeL1Inf

namespace PackingLPAccel

/-!
# The `ℓ_{q,p}` proxy and the corrected residual

Chen, Chen, Graur, Sidford, *Accelerated Parallel Algorithms for Packing Linear Programming*,
STOC 2027 submission (manuscript sha256 1dac7711…), §5.2, pp.23–25, Problem 5.1 (p.18), and the
Bregman divergence (p.7).

**Formalization Note.**
* The gradients are written out for `x ≥ 0`, as Bregman divergences of `∥·∥_q^q` and
  `∥·∥_q^{pq} = (∥·∥_q^q)^p`. `|x + y|^q` keeps the absolute value, since `x + y` may be negative.
* `∥x∥_q^{(p-1)q}` is `(∥x∥_q^q)^(p-1)` and `∥x∥_q^{(p-2)q}` is `(∥x∥_q^q)^(p-2)`, with `Real.rpow`.
  At `p = 2`, `x = 0` Lean gives `0^0 = 1`.
* `correctedF` is the residual of (18)–(22) with two corrections: `c_ij(t)` holds `|X_ij + t|^q`, not
  `(X_ij + |t|)^q`, and `v^{(2)}_i = 2λp² q_i^{p-2}`, not `λp² q_i^{p-2}`. As printed, the residual is
  nonnegative with minimum `0` at `∆ = 0`, and iterative refinement never moves on `E(x) = x⁴`.
  `(18)`'s `F(∆/ω; X)` is also read at `∆`, as (41) needs.
-/

variable {n m k : ℕ}

/-- `∥x∥_q^q = ∑ |x_i|^q`. -/
noncomputable def qPow (q : ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, |x i| ^ q

/-- `V^{∥·∥_q^q}_x(x + y)`, for `x ≥ 0`. -/
noncomputable def bregQ (q : ℝ) (x y : Fin n → ℝ) : ℝ :=
  ∑ i, (|x i + y i| ^ q - x i ^ q - q * x i ^ (q - 1) * y i)

/-- `V^{∥·∥_q^{pq}}_x(x + y)`, for `x ≥ 0`. -/
noncomputable def bregPQ (p q : ℝ) (x y : Fin n → ℝ) : ℝ :=
  qPow q (fun i => x i + y i) ^ p - qPow q x ^ p -
    p * qPow q x ^ (p - 1) * ∑ i, q * x i ^ (q - 1) * y i

/-- The positive movement `µ(y; x) = ∑ [(x_i + |y_i|)^q - x_i^q]`, display (16). -/
noncomputable def mu (q : ℝ) (y x : Fin n → ℝ) : ℝ := ∑ i, ((x i + |y i|) ^ q - x i ^ q)

/-- The proxy `M(y; x)` of Lemma 5.13. -/
noncomputable def proxyM (p q : ℝ) (y x : Fin n → ℝ) : ℝ :=
  p * qPow q x ^ (p - 1) * bregQ q x y + 2 * p ^ 2 * qPow q x ^ (p - 2) * mu q y x ^ 2 +
    p ^ p * mu q y x ^ p

/-- `V^{|·|^p}_x(x + y)` on the line. -/
noncomputable def bregAbs (p x y : ℝ) : ℝ :=
  |x + y| ^ p - |x| ^ p - p * |x| ^ (p - 1) * Real.sign x * y

/-- `E^λ_{q,p}(X) = ψ(X) + λ ∑_i (∑_j |X_ij|^q)^p`, displays (9), (13). -/
noncomputable def qpEnergy (I : CompositeInstance m k) (lam p q : ℝ)
    (X : Matrix (Fin m) (Fin k) ℝ) : ℝ :=
  I.psi X + lam * ∑ i, qPow q (X i) ^ p

/-- `ϕ^{(X)}_{ij}(t) = (X_ij + |t|)^q - X_ij^q`, display (21). -/
noncomputable def phiX (q x t : ℝ) : ℝ := (x + |t|) ^ q - x ^ q

/-- The corrected `c^{(X)}_{ij}(t) = λ p q_i^{p-1} [|X_ij + t|^q - X_ij^q]`. -/
noncomputable def cX (lam p q qi x t : ℝ) : ℝ := lam * p * qi ^ (p - 1) * (|x + t| ^ q - x ^ q)

/-- The corrected residual objective `F(∆; X)`, with `v^{(2)}_i = 2λp² q_i^{p-2}`, `v^{(p)}_i = λp^p`. -/
noncomputable def correctedF (I : CompositeInstance m k) (lam p q : ℝ)
    (X Δ : Matrix (Fin m) (Fin k) ℝ) : ℝ :=
  I.psi (X + Δ) - I.psi X + ∑ i, ∑ j, cX lam p q (qPow q (X i)) (X i j) (Δ i j) +
    ∑ i, (2 * lam * p ^ 2 * qPow q (X i) ^ (p - 2) * (∑ j, phiX q (X i j) (Δ i j)) ^ 2 +
      lam * p ^ p * (∑ j, phiX q (X i j) (Δ i j)) ^ p)

end PackingLPAccel


