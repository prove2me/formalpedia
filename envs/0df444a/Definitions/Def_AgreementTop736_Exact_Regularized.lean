-- Prove2me | Definitions.Def_AgreementTop736_Exact_Regularized
-- name    : AgreementTop736_Exact_Regularized
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:56.871197+00:00
-- url     : https://prove2.me/theorems/880b1f49-77f7-4ae7-8b47-0a92733e32e6
-- title:
--   Proof objects of Theorem 7: error counts, regularizer $f(u)=(u+a)^{-1/2}$, $V$, $\varphi$, $E$, $\psi$ and $R$
-- statement:
--   This file fixes the auxiliary quantities of the proof of Theorem 7 (§3.1, pp.9–11). Fix local functions $F_K:K\to\Sigma$, a function $g:V\to\Sigma$ and a regularization parameter $a>0$.
--
--   1. The **error count** $m_K=\#\{x\in K:F_K(x)\ne g(x)\}$ and, for $H$, the **local error count** $Z(K,H)=\#\{x\in H:F_K(x)\ne g(x)\}$.
--   2. The **regularizer** $f(u)=(u+a)^{-1/2}$ and the **regularized disagreement**
--   $$V=\mathbb E_{K\sim\mu}\frac{m_K}{m_K+a}.$$
--   3. For an element $x$ and a label $s\ne g(x)$, $\varphi_{x,s}(K)=\mathbf 1[F_K(x)=s]\,f(m_K)$ for $K\ni x$ and $0$ otherwise.
--   4. The **weighted non-polarity** of eq. (4),
--   $$E=\mathbb E_{H,K,K'}\sum_{x\in H}\sum_{s\ne g(x)}\big(\varphi_{x,s}(K)-\varphi_{x,s}(K')\big)^2,$$
--   under the joint law of the agreement test.
--   5. The **local witness vector** $\psi_{x,s}(K,H)=\mathbf 1[F_K(x)=s]\,f(Z/\rho)$ for $x\in H$, $s\ne g(x)$, and the **residual** $R(K,H)=\varphi(K)|_H-\psi(K,H)$; the squared norms $\|\psi(K,H)-\psi(K',H)\|_2^2$ and $\|R(K,H)\|_2^2$ are sums over the coordinates $(x,s)$ with $x\in H$, $s\ne g(x)$.
--
--   These quantities connect the spectral-gap lower bound (5) with the upper bound by the rejection probability.
--
--   **Formalization Note** $f(u)$ is written $1/\sqrt{u+a}$; it is only evaluated at $u\ge0$, $a>0$. The witness vector is given by its closed form $\mathbf 1[F_K(x)=s]f(Z/\rho)$ (the paper's right-hand side of the definition of $\psi$), without the auxiliary witness distribution $\nu_{K,H}$.
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), pp.9–10, §3.1, proof of Theorem 7 (definitions of e_K, m_K, f, V, φ_{x,s}, eq. (4), Z, ψ_{x,s}, R(K,H))

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Model

/-!
The proof-internal objects of the proof of Theorem 7 (Kaufman–Pham, STOC 2027 submission #736,
§3.1, pp.9–11): the error count `m_K`, the regularizer `f(u) = (u + a)^{-1/2}`, the regularized
disagreement `V`, the vectors `φ(K)`, the weighted non-polarity `E` of eq. (4), the local error count
`Z`, the local witness vectors `ψ(K, H)` and the residual `R(K, H) = φ(K)|_H − ψ(K, H)`.
Vectors are indexed by coordinates `(x, s)` with `x ∈ H` and `s ≠ g x`.
-/

namespace AgreementTop736.Exact

open Finset

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `m_K = #{x ∈ K : F_K(x) ≠ g(x)}` (p.9). -/
def errCount (F : Finset V → V → α) (g : V → α) (K : Finset V) : ℕ :=
  (K.filter (fun x => F K x ≠ g x)).card

/-- `Z(K, H) = ∑_{x ∈ H} e_K(x) = #{x ∈ H : F_K(x) ≠ g(x)}` (p.10). -/
def localErr (F : Finset V → V → α) (g : V → α) (K H : Finset V) : ℕ :=
  (H.filter (fun x => F K x ≠ g x)).card

/-- The regularizer `f(u) = (u + a)^{-1/2}` (p.10), written `1 / √(u + a)`; used only with
`u ≥ 0`, `a > 0`. -/
def fReg (a u : ℝ) : ℝ := 1 / Real.sqrt (u + a)

/-- The labels other than `g x`. -/
def offLabels (g : V → α) (x : V) : Finset α := univ.filter (fun s => s ≠ g x)

namespace Scheme

/-- `V = E_K [m_K / (m_K + a)]` (p.10). -/
def Vreg (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) : ℝ :=
  ∑ K, S.μ K * ((errCount F g K : ℝ) / ((errCount F g K : ℝ) + a))

end Scheme

/-- `φ_{x,s}(K) = 1[F_K(x) = s] f(m_K)` for `K` containing `x`, and `0` otherwise (p.10). -/
def phi (F : Finset V → V → α) (g : V → α) (a : ℝ) (x : V) (s : α) (K : Finset V) : ℝ :=
  if x ∈ K ∧ F K x = s then fReg a (errCount F g K) else 0

/-- `‖φ(K)|_H − φ(K')|_H‖²₂ = ∑_{x ∈ H} ∑_{s ≠ g(x)} (φ_{x,s}(K) − φ_{x,s}(K'))²`. -/
def phiDistSq (F : Finset V → V → α) (g : V → α) (a : ℝ) (H K K' : Finset V) : ℝ :=
  ∑ x ∈ H, ∑ s ∈ offLabels g x, (phi F g a x s K - phi F g a x s K') ^ 2

namespace Scheme

/-- The weighted non-polarity `E = E_{H,K,K'} ∑_{x∈H} ∑_{s≠g(x)} (φ_{x,s}(K) − φ_{x,s}(K'))²` of
eq. (4) (p.10), under the joint law of the agreement test. -/
def Enp (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) : ℝ :=
  ∑ H, ∑ K, ∑ K', S.testWeight H K K' * phiDistSq F g a H K K'

/-- `ψ_{x,s}(K, H) = 1[F_K(x) = s] f(Z/ρ)` for `x ∈ H`, and `0` otherwise (p.10). -/
def psi (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (x : V) (s : α)
    (K H : Finset V) : ℝ :=
  if x ∈ H ∧ F K x = s then fReg a ((localErr F g K H : ℝ) / S.ρ) else 0

/-- `‖ψ(K, H) − ψ(K', H)‖²₂`, over coordinates `x ∈ H`, `s ≠ g(x)`. -/
def psiDistSq (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (H K K' : Finset V) : ℝ :=
  ∑ x ∈ H, ∑ s ∈ offLabels g x, (S.psi F g a x s K H - S.psi F g a x s K' H) ^ 2

/-- `‖R(K, H)‖²₂` for the residual `R(K, H) = φ(K)|_H − ψ(K, H)` (p.10), over coordinates
`x ∈ H`, `s ≠ g(x)`. -/
def residualSq (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (K H : Finset V) : ℝ :=
  ∑ x ∈ H, ∑ s ∈ offLabels g x, (phi F g a x s K - S.psi F g a x s K H) ^ 2

end Scheme

end

end AgreementTop736.Exact


