-- Prove2me | Definitions.Def_MFGPlanning_Existence_Duality
-- name    : MFGPlanning_Existence_Duality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:39:16.156534+00:00
-- url     : https://prove2.me/theorems/fcd15a57-857a-48a8-a785-385f8bc35787
-- title:
--   The duality functionals $(W+\chi)^*$, $\Theta$, $\Theta^*$, $\mathcal F$, $\Lambda$, $\Sigma$, $\Sigma^*$ and the constraint of (26)
-- statement:
--   Let $\chi$ be the indicator of $\{m \ge 0\}$ ($0$ there, $+\infty$ elsewhere). Its sum with $W$ has the Legendre–Fenchel transform
--   $$(W+\chi)^*(a) = \sup_{m\ge 0}\,[a m - W(m)].$$
--   The dual variables are $\alpha = (\alpha^n_{i,j})$ and $\beta = ([\beta^n]_{i,j})$ with $[\beta^n]_{i,j}\in\mathbb R^4$, $n = 1,\dots,N_T$; the primal variables are $M = (M^n_{i,j})$ and $Z = ([Z^n]_{i,j})$, $n = 0,\dots,N_T-1$. Define
--   $$\Theta(\alpha,\beta) = \sum_{n=1}^{N_T}\sum_{i,j}(W+\chi)^*\big(\alpha^n_{i,j} + g(x_{i,j},[\beta^n]_{i,j})\big),$$
--   $$\Theta^*(M,Z) = \sup_{\alpha,\beta}\Big(\sum_{n=1}^{N_T}\sum_{i,j} M^{n-1}_{i,j}\alpha^n_{i,j} + \langle[Z^{n-1}]_{i,j},[\beta^n]_{i,j}\rangle - (W+\chi)^*\big(\alpha^n_{i,j} + g(x_{i,j},[\beta^n]_{i,j})\big)\Big).$$
--   For $\Psi = (\Psi^n_{i,j})$, $n = 0,\dots,N_T$,
--   $$\mathcal F(\Psi) = \frac1{\Delta t}\Big(\sum_{i,j}(m_0)_{i,j}\Psi^0_{i,j} - \sum_{i,j}(m_T)_{i,j}\Psi^{N_T}_{i,j}\Big),$$
--   and $(\alpha,\beta) = \Lambda(\Psi)$ means $\alpha^{n+1}_{i,j} = \frac{\Psi^{n+1}_{i,j}-\Psi^n_{i,j}}{\Delta t} - \nu(\Delta_h\Psi^{n+1})_{i,j}$ and $[\beta^{n+1}]_{i,j} = [D_h\Psi^{n+1}]_{i,j}$ for $0\le n<N_T$. Then $\Sigma(\alpha,\beta) = \mathcal F(\Psi)$ if some $\Psi$ has $(\alpha,\beta) = \Lambda(\Psi)$ and $\sum_{i,j}\Psi^0_{i,j} = 0$, and $\Sigma(\alpha,\beta) = +\infty$ otherwise. Its transform is
--   $$\Sigma^*(M,Z) = \sup_{\alpha,\beta}\Big(\sum_{n=0}^{N_T-1}\sum_{i,j} M^n_{i,j}\alpha^{n+1}_{i,j} + \langle [Z^n]_{i,j},[\beta^{n+1}]_{i,j}\rangle - \Sigma(\alpha,\beta)\Big).$$
--   Finally, the constraint of the control problem (26) on $(M,Z)$, with $M^{N_T} := m_T$, is
--   $$\frac{M^{n+1}_{i,j}-M^n_{i,j}}{\Delta t} + \nu(\Delta_hM^n)_{i,j} + \mathrm{div}_h(Z^n)_{i,j} = 0\quad(0\le n<N_T),\qquad M^0 = m_0.$$
--
--   The primal problem of the mission is the minimization of $\Theta^*(M,Z) + \Sigma^*(-M,-Z)$ and the dual one the minimization of $\Theta(\alpha,\beta) + \Sigma(\alpha,\beta)$.
--
--   **Formalization Note** All of $(W+\chi)^*$, $W+\chi$, $\Theta$, $\Theta^*$, $\Sigma$, $\Sigma^*$ take values in the extended reals `EReal`, and every supremum and infimum is the lattice one, so an unbounded supremum is $+\infty$ (not a junk $0$). $\Sigma$ is written as the infimum of $\mathcal F(\Psi)$ over the admissible $\Psi$ (an empty infimum is $+\infty$; $\Psi$ is unique when it exists). Time indices follow Remark 2: the index $k \in \{0,\dots,N_T-1\}$ of $\alpha,\beta$ is the paper's $n = k+1$, the index $k$ of $M,Z$ is the paper's $n = k$, so $M^k$ is paired with $\alpha^{k+1}$. Components of $\beta$, $Z$ are `Fin 4` indices `0..3` for $1..4$. Mathlib's `EReal` has $\bot + \top = \bot$; real minus $\top$ is $\bot$, which is exactly how inadmissible $(\alpha,\beta)$ drop out of the supremum defining $\Sigma^*$.
-- source:
--   Achdou, Camilli, Capuzzo-Dolcetta, Mean field games: numerical methods for the planning problem, hal-00465404v1 (2010), §3.1, pp. 7–8, (W+χ)*, Θ, (25), (26), (27)–(29), Remark 2, Lemma 2 (Σ*)

import Mathlib
import Definitions.Def_MFGPlanning_Existence_Grid

namespace MFGPlanning.Existence

variable (d : Data)

/-- `(W + χ)^*(a) = sup_{m ≥ 0} [a m − W(m)]` (p. 7), with `χ` the indicator of `{m ≥ 0}`; an
`EReal` supremum, so an unbounded supremum is `+∞`. -/
noncomputable def conjWchi (a : ℝ) : EReal :=
  ⨆ (m : ℝ) (_ : 0 ≤ m), ((a * m - d.W m : ℝ) : EReal)

/-- `(W + χ)(m)`: `W(m)` if `m ≥ 0`, `+∞` otherwise. -/
noncomputable def Wchi (m : ℝ) : EReal := if 0 ≤ m then (d.W m : EReal) else ⊤

/-- `Θ(α, β) = ∑_{n=1}^{N_T} ∑_{i,j} (W + χ)^*(α^n_{i,j} + g(x_{i,j}, [β^n]_{i,j}))` (p. 7). The index
`k : Fin N_T` of `α`, `β` is the paper's `n = k + 1`. -/
noncomputable def Theta (α : Fin d.NT → d.Pt → ℝ) (β : Fin d.NT → d.Pt → Fin 4 → ℝ) : EReal :=
  ∑ k, ∑ p, conjWchi d (α k p + d.g p (β k p))

/-- The pairing of (25): `∑_{n=1}^{N_T} ∑_{i,j} M^{n−1}_{i,j} α^n_{i,j} + ⟨[Z^{n−1}]_{i,j}, [β^n]_{i,j}⟩`.
With `M k = M^k` and `α k = α^{k+1}`, index `k` pairs `M^k` with `α^{k+1}` (Remark 2's lag). -/
def pair (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ)
    (α : Fin d.NT → d.Pt → ℝ) (β : Fin d.NT → d.Pt → Fin 4 → ℝ) : ℝ :=
  ∑ k, ∑ p, (M k p * α k p + ∑ l, Z k p l * β k p l)

/-- The Legendre–Fenchel transform `Θ^*(M, Z)` of (25), p. 7, as an `EReal` supremum. -/
noncomputable def ThetaStar (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ) : EReal :=
  ⨆ (α : Fin d.NT → d.Pt → ℝ) (β : Fin d.NT → d.Pt → Fin 4 → ℝ),
    (pair d M Z α β : EReal) - Theta d α β

/-- `𝓕(Ψ) = (1/Δt)(∑_{i,j} (m_0)_{i,j} Ψ^0_{i,j} − ∑_{i,j} (m_T)_{i,j} Ψ^{N_T}_{i,j})` ((27), p. 8). -/
noncomputable def F (Ψ : Fin (d.NT + 1) → d.Pt → ℝ) : ℝ :=
  (1 / d.dt) * (∑ p, d.m0 p * Ψ 0 p - ∑ p, d.mT p * Ψ (Fin.last d.NT) p)

/-- `Λ(Ψ) = (α, β)` ((28), p. 8): `α^{n+1} = (Ψ^{n+1} − Ψ^n)/Δt − ν Δ_h Ψ^{n+1}` and
`[β^{n+1}] = [D_h Ψ^{n+1}]`, `0 ≤ n < N_T`; index `k : Fin N_T` of the output is `n + 1 = k + 1`. -/
noncomputable def Lam (Ψ : Fin (d.NT + 1) → d.Pt → ℝ) :
    (Fin d.NT → d.Pt → ℝ) × (Fin d.NT → d.Pt → Fin 4 → ℝ) :=
  (fun k p => (Ψ k.succ p - Ψ k.castSucc p) / d.dt - d.ν * lap d (Ψ k.succ) p,
   fun k p => Dh d (Ψ k.succ) p)

/-- `Σ(α, β)` ((29), p. 8): `𝓕(Ψ)` if some `Ψ` has `(α, β) = Λ(Ψ)` and `∑_{i,j} Ψ^0_{i,j} = 0`,
`+∞` otherwise; written as an infimum over the admissible `Ψ` (empty infimum `= ⊤`). -/
noncomputable def SigmaF (α : Fin d.NT → d.Pt → ℝ) (β : Fin d.NT → d.Pt → Fin 4 → ℝ) : EReal :=
  ⨅ (Ψ : Fin (d.NT + 1) → d.Pt → ℝ) (_ : Lam d Ψ = (α, β) ∧ ∑ p, Ψ 0 p = 0), (F d Ψ : EReal)

/-- The Legendre–Fenchel transform `Σ^*(M, Z) = sup_{α,β} (pairing − Σ(α, β))` (Lemma 2, p. 8), with
the pairing of (25). -/
noncomputable def SigmaStar (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ) : EReal :=
  ⨆ (α : Fin d.NT → d.Pt → ℝ) (β : Fin d.NT → d.Pt → Fin 4 → ℝ),
    (pair d M Z α β : EReal) - SigmaF d α β

/-- The constraint of the control problem (26), p. 7, with `M^{N_T} = m_T` appended:
`(M^{n+1} − M^n)/Δt + ν Δ_h M^n + div_h(Z^n) = 0` for `0 ≤ n < N_T`, and `M^0 = m_0`. -/
def PlanningConstraint (M : Fin d.NT → d.Pt → ℝ) (Z : Fin d.NT → d.Pt → Fin 4 → ℝ) : Prop :=
  (∀ (n : Fin d.NT) (p : d.Pt),
      ((Fin.snoc (α := fun _ => d.Pt → ℝ) M d.mT n.succ p) - M n p) / d.dt
        + d.ν * lap d (M n) p + divh d (Z n) p = 0) ∧
  M 0 = d.m0

end MFGPlanning.Existence


