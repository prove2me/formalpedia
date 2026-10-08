-- Prove2me | Definitions.Def_RobustUncLP_Ellipsoidal_SystemC
-- name    : RobustUncLP_Ellipsoidal_SystemC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:08:09.082794+00:00
-- url     : https://prove2.me/theorems/f807e6d5-49be-49b5-8340-2d3a36411447
-- title:
--   Appendix, pp. 15–16 — the feasible set of (P_i[x]), the Frobenius pairing, and the conic quadratic system (𝒞_i)
-- statement:
--   Fix an ellipsoidal uncertainty $\mathcal U = \bigcap_{\ell=0}^k U(\Pi_\ell, Q_\ell)$ with $\Pi_\ell(u) = P^0_\ell + \sum_j u_j P^j_\ell$. Write $a_i[A]$ for the $i$-th row of a matrix $A$.
--
--   **The problem $(P_i[x])$.** For a row $i$ and a point $x \in \mathbb R^n$, the Appendix considers
--   $$a_i[\Pi_0(u^0)]^Tx \to \min \quad \text{s.t.}\quad \Pi_\ell(u^\ell) = \Pi_0(u^0),\ \ell = 1,\dots,k;\qquad \|Q_\ell u^\ell\| \le 1,\ \ell = 0,\dots,k,$$
--   with design variables $u^0, \dots, u^k$. Its feasible set does not depend on $i$ or $x$; this file defines it.
--
--   **Frobenius pairing.** $\langle X, Y\rangle = \sum_{a,b} X_{ab} Y_{ab}$ for $X, Y \in \mathbb R^{m\times n}$. It pairs the matrix multiplier $\lambda_\ell$ with the matrix equation $\Pi_\ell(u^\ell) = \Pi_0(u^0)$.
--
--   **The system $(\mathcal C_i)$.** The unknowns are matrices $\lambda_1,\dots,\lambda_k \in \mathbb R^{m\times n}$, vectors $\mu_\ell \in \mathbb R^{M_\ell}$ and scalars $\nu_\ell$, $\ell = 0,\dots,k$. They must satisfy:
--
--   1. $\displaystyle (P^0_0 x)_i + \sum_{\ell=1}^k \langle \lambda_\ell, P^0_0 - P^0_\ell\rangle - \sum_{\ell=0}^k \nu_\ell \ \ge\ 0;$
--   2. $\displaystyle -\sum_{\ell=1}^k \langle \lambda_\ell, P^j_0\rangle + (Q_0^T\mu_0)_j = (P^j_0 x)_i$ for every $j$;
--   3. $\displaystyle \langle \lambda_\ell, P^j_\ell\rangle + (Q_\ell^T\mu_\ell)_j = 0$ for every $\ell = 1,\dots,k$ and every $j$;
--   4. $\|\mu_\ell\| \le \nu_\ell$ for $\ell = 0,\dots,k$.
--
--   This is the dual $(D_i[x])$ of $(P_i[x])$, written as a conic quadratic problem with the requirement that its objective be nonnegative. In the generic data of $(\mathcal C_i)$ on p. 16: $r^{(i)}$ collects $P^0_0 - P^0_\ell$, $R^{(i)}$ encodes $\Pi_\ell(u^\ell) - \Pi_0(u^0)$, $A_\ell^{(i)}z - b_\ell^{(i)} = Q_\ell u^\ell$, $c^{(i)}_\ell = 0$, $d^{(i)}_\ell = -1$, $e^{(i)}[x]$ is the $u^0$-gradient of the objective, and $\varphi^{(i)}[x] = (P^0_0x)_i$. Lines 1–3 are linear in $(x, \lambda, \mu, \nu)$; line 4 is a family of second-order cone constraints. The system is the building block of the conic quadratic program (CQP) of Theorem 3.1.
--
--   **Formalization Note** $\lambda_\ell$ is indexed by `Fin k` (`Λ ℓ'` multiplies the equation for $\ell = \ell' + 1$), and $\mu, \nu$ by `Fin (k + 1)`. The page writes $f^{(i)}[x]$ in the first line of $(\mathcal C_i)$ for the $\varphi^{(i)}[x]$ of $(D_i[x])$; the formula above uses $\varphi^{(i)}[x]$.
-- source:
--   Ben-Tal & Nemirovski, Robust solutions of uncertain linear programs, Oper. Res. Lett. 25 (1999); authors' manuscript, Appendix, p. 15 (P_i[x]), (D_i[x]), p. 16 (𝒞_i)

import Mathlib
import Definitions.Def_RobustUncLP_Ellipsoidal_Setting

namespace RobustUncLP.Ellipsoidal

open Matrix

open EllipsoidalData

variable {m n k : ℕ}

/-- Feasible set of the problem `(P_i[x])`, Appendix, p. 15: tuples `(u⁰, …, u^k)` with
`Π_ℓ(u^ℓ) = Π_0(u⁰)` and `‖Q_ℓ u^ℓ‖ ≤ 1` for all `ℓ` (it depends neither on `i` nor on `x`). -/
def PFeas (D : EllipsoidalData m n k) : Set ((ℓ : Fin (k + 1)) → Fin (D.L ℓ) → ℝ) :=
  {u | (∀ ℓ, D.Pi ℓ (u ℓ) = D.Pi 0 (u 0)) ∧ ∀ ℓ, euclidNorm (D.Q ℓ *ᵥ u ℓ) ≤ 1}

/-- Frobenius pairing `⟨X, Y⟩ = ∑_{a,b} X_{ab} Y_{ab}` of two `m × n` matrices. -/
def frob (X Y : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ a, ∑ b, X a b * Y a b

/-- The system `(𝒞_i)`, Appendix, p. 16, for row `i` at the point `x`, written out for the data of
`(P_i[x])`. `Λ ℓ'` is the multiplier `λ^{(i)}` of the equality `Π_{ℓ'+1}(u^{ℓ'+1}) = Π_0(u⁰)`,
`μ ℓ`, `ν ℓ` are `μ_ℓ^{(i)}`, `ν_ℓ^{(i)}` (`ℓ = 0, …, k`). -/
def SystemC (D : EllipsoidalData m n k) (x : Fin n → ℝ) (i : Fin m)
    (Λ : Fin k → Matrix (Fin m) (Fin n) ℝ) (μ : (ℓ : Fin (k + 1)) → Fin (D.M ℓ) → ℝ)
    (ν : Fin (k + 1) → ℝ) : Prop :=
  -- first line of (𝒞_i): the dual objective is nonnegative
  0 ≤ (D.P0 0 *ᵥ x) i + ∑ ℓ' : Fin k, frob (Λ ℓ') (D.P0 0 - D.P0 ℓ'.succ) - ∑ ℓ, ν ℓ ∧
  -- second line, `u⁰`-block
  (∀ j, -(∑ ℓ' : Fin k, frob (Λ ℓ') (D.P 0 j)) + ((D.Q 0)ᵀ *ᵥ μ 0) j = (D.P 0 j *ᵥ x) i) ∧
  -- second line, `u^ℓ`-blocks, `ℓ = 1, …, k`
  (∀ ℓ' : Fin k, ∀ j, frob (Λ ℓ') (D.P ℓ'.succ j) + ((D.Q ℓ'.succ)ᵀ *ᵥ μ ℓ'.succ) j = 0) ∧
  -- third line
  ∀ ℓ, euclidNorm (μ ℓ) ≤ ν ℓ

end RobustUncLP.Ellipsoidal


