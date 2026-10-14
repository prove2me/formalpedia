-- Prove2me | Definitions.Def_ProgCorrMFG_Approx_CondValue
-- name    : ProgCorrMFG_Approx_CondValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:31.974686+00:00
-- url     : https://prove2.me/theorems/e1b93b37-cb21-4630-be04-6c63d49efb7d
-- title:
--   §5.2, pp. 10–11, (5.9)–(5.10) — the conditional cost $J_\varphi(t,x^{(t)},m^{(t)},w)$ and value function $V_\varphi(t,x^{(t)},m^{(t)})$
-- statement:
--   These definitions set up the conditional optimisation problem of the representative player who has received the restricted strategy $\varphi\in\mathcal R$ from the mediator, as in §5.2 of Bonesini, Campi and Fischer.
--
--   Let $\rho\in\mathcal P(\mathcal R\times\mathcal P(\mathcal X)^{T+1})$ be the law of the pair $(\Phi,\mu)$ and write $\mathbb P_\varphi=\mathbb P(\cdot\mid\Phi=\varphi)$.
--
--   1. **Conditional flow law.** For a time $t\in[\![0,T]\!]$ and flows $m,m'\in\mathcal P(\mathcal X)^{T+1}$,
--   $$\mathbb P_\varphi\big(\mu=m'\,\big|\,\mu^{(t)}=m^{(t)}\big)=\frac{\rho(\{(\varphi,m')\})}{\rho\big(\{\varphi\}\times\{l: l^{(t)}=m^{(t)}\}\big)}\quad\text{if }m'^{(t)}=m^{(t)},$$
--   and $0$ otherwise. It is meaningful when the denominator is positive, that is, for $m^{(t)}\in\mathcal P_\varphi^{(t)}$ (Remark 5.4).
--   2. **Policies from time $t$.** $\widehat{\mathcal R}_t$ is the set of maps $w(s,x,m)\in\Gamma$, $s\in[\![t,T-1]\!]$, that depend only on the histories $x^{(s)}$ and $m^{(s)}$.
--   3. **Conditional cost.** Given a state history $x^{(t)}$, a flow $m'$ and noises $z=(z_{s+1})_s\in\mathcal Z^T$, the path $X$ starts from $x^{(t)}$ and follows $X_{s+1}=\Psi(s,X_s,m'_s,w(s,X^{(s)},m'^{(s)}),z_{s+1})$ for $s\in[\![t,T-1]\!]$. The conditional cost is
--   $$J_\varphi(t,x^{(t)},m^{(t)},w)=\sum_{m'}\mathbb P_\varphi\big(\mu=m'\,\big|\,\mu^{(t)}=m^{(t)}\big)\int_{\mathcal Z^T}\Big[\sum_{s=t}^{T-1}f\big(s,X_s,m'_s,w(s,X^{(s)},m'^{(s)})\big)+F(X_T,m'_T)\Big]\nu^{\otimes T}(dz).$$
--   4. **Value function.**
--   $$V_\varphi(t,x^{(t)},m^{(t)})=\inf_{w\in\widehat{\mathcal R}_t}J_\varphi(t,x^{(t)},m^{(t)},w),\qquad t\in[\![0,T]\!],$$
--   so that $V_\varphi(T,x^{(T)},m^{(T)})=F(x_T,m_T)$.
--
--   The value function is the object of the conditional dynamic programming principle (Proposition 5.5), which in turn is the step that shows that closed-loop correlated solutions are open-loop solutions (Proposition 5.6).
--
--   **Formalization Note** The paper defines $J_\varphi$ as the conditional expectation $\mathbb E_\varphi[\,\cdot\mid X^{(t)}=x^{(t)},\mu^{(t)}=m^{(t)}]$ of the cost from time $t$ on and shows in (5.10) (p. 11) that it equals the explicit sum-integral above, because $X^{(t)}$ and the future flow are $\mathbb P_\varphi$-conditionally independent given $\mu^{(t)}$ and the noises are independent of everything else. The explicit form is used as the definition: it avoids conditioning on events of probability zero. The sum over $m'$ is a `tsum`; under (R1) only finitely many terms are nonzero. Histories are stored as full vectors `x : Fin (T+1) → X` and flows `m : Flow T X`; the definitions read only the entries up to time $t$ (the path overwrites the later entries of $x$, and the weight vanishes unless $m'^{(t)}=m^{(t)}$). Integrals are over $\nu^{\otimes T}$; the coordinates before $t$ are unused. Policies in $\widehat{\mathcal R}_t$ are not required to be measurable: the paper restricts them to the finite set $\mathcal P_\varphi$ of flows, where every map is Borel.
-- source:
--   Bonesini, Campi & Fischer, Correlated Equilibria for Mean Field Games with Progressive Strategies, arXiv:2212.01656v1, pp. 10–11, (5.9), the definition of J_φ(t, x^{(t)}, m^{(t)}, w), (5.10) and the definition of V_φ and ℛ̂_t

import Mathlib
import Definitions.Def_ProgCorrMFG_Approx_Model

namespace ProgCorrMFG.Approx

open MeasureTheory ProbabilityTheory unitInterval

/-- The conditional flow law `ℙ_φ(μ = m' | μ^{(t)} = m^{(t)})` of §5.2 (pp. 10–11), computed from `ρ`
for `(Φ, μ) ∼ ρ` and `ℙ_φ := ℙ(· | Φ = φ)`: it is `ρ{(φ, m')} / ρ({φ} × {l : l^{(t)} = m^{(t)}})`
when `m'^{(t)} = m^{(t)}`, and `0` otherwise. Only meaningful when the denominator is positive,
i.e. for `m^{(t)} ∈ 𝒫^{(t)}_φ` (Remark 5.4). -/
noncomputable def condFlowWeight {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace G]
    (ρ : Measure (Strat T X G × Flow T X)) (φ : Strat T X G) (t : Fin (T + 1))
    (m m' : Flow T X) : ℝ :=
  if ∀ s : Fin (T + 1), s ≤ t → m' s = m s then
    (ρ {(φ, m')}).toReal /
      (ρ ({φ} ×ˢ {l : Flow T X | ∀ s : Fin (T + 1), s ≤ t → l s = m s})).toReal
  else 0

/-- `ℛ̂_t` (p. 11): progressive policies used from time `t` on, `w(s, x, m) ∈ Γ` for
`s ∈ ⟦t, T−1⟧`, depending only on the histories `x^{(s)}`, `m^{(s)}` (the values at times `s < t`
play no role). -/
def ProgFrom (T : ℕ) (X G : Type) [Fintype X] (t : Fin (T + 1)) : Type :=
  {w : (s : Fin T) → (Fin (T + 1) → X) → Flow T X → G //
    ∀ s : Fin T, t ≤ s.castSucc → NonAnt s (w s)}

/-- The state path from time `t` on: starting from the history `x^{(t)}` (the entries of `x` after
`t` are overwritten), along the flow `m` and the noises `z_{s+1}` (`z s`), with
`X_{s+1} = Ψ(s, X_s, m_s, w(s, X^{(s)}, m^{(s)}), z_{s+1})` for `s ∈ ⟦t, T−1⟧`; `runPath … k x` is the
path after `k` steps of the recursion over `s = 0, 1, …` (steps with `s < t` change nothing). -/
def runPath {T : ℕ} {X G : Type} [Fintype X] (M : Model T X G)
    (w : (s : Fin T) → (Fin (T + 1) → X) → Flow T X → G) (t : Fin (T + 1))
    (m : Flow T X) (z : Fin T → I) : ℕ → (Fin (T + 1) → X) → (Fin (T + 1) → X)
  | 0, x => x
  | k + 1, x =>
    if h : t.1 ≤ k ∧ k < T then
      Function.update (runPath M w t m z k x) ⟨k + 1, by omega⟩
        (M.Ψ ⟨k, h.2⟩ (runPath M w t m z k x ⟨k, by omega⟩) (m ⟨k, by omega⟩)
          (w ⟨k, h.2⟩ (runPath M w t m z k x) m) (z ⟨k, h.2⟩))
    else runPath M w t m z k x

/-- The conditional cost `J_φ(t, x^{(t)}, m^{(t)}, w)` of §5.2 (p. 10), in the explicit form of the third
line of (5.10) (p. 11):
`∑_{m'} ℙ_φ(μ = m' | μ^{(t)} = m^{(t)}) ∫_{𝒵^T} [∑_{s=t}^{T−1} f(s, X_s, m'_s, w(s, X^{(s)}, m'^{(s)})) + F(X_T, m'_T)] ν^{⊗T}(dz)`,
where `X` is the path `runPath` from `x^{(t)}` along `m'` and `z`. -/
noncomputable def condCost {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace G]
    (M : Model T X G) (ρ : Measure (Strat T X G × Flow T X)) (φ : Strat T X G)
    (t : Fin (T + 1)) (x : Fin (T + 1) → X) (m : Flow T X) (w : ProgFrom T X G t) : ℝ :=
  ∑' m' : Flow T X, condFlowWeight ρ φ t m m' *
    ∫ z, ((∑ s : Fin T, if t ≤ s.castSucc then
          M.f s (runPath M w.1 t m' z T x s.castSucc) (m' s.castSucc)
            (w.1 s (runPath M w.1 t m' z T x) m') else 0) +
        M.F (runPath M w.1 t m' z T x (Fin.last T)) (m' (Fin.last T)))
      ∂(Measure.pi fun _ : Fin T => (volume : Measure I))

/-- The conditional value function `V_φ(t, x^{(t)}, m^{(t)}) := inf_{w ∈ ℛ̂_t} J_φ(t, x^{(t)}, m^{(t)}, w)`
(p. 11), for `t ∈ ⟦0, T⟧`; `V_φ(T, x, m) = F(x_T, m_T)`. -/
noncomputable def condValue {T : ℕ} {X G : Type} [Fintype X] [MeasurableSpace G]
    (M : Model T X G) (ρ : Measure (Strat T X G × Flow T X)) (φ : Strat T X G)
    (t : Fin (T + 1)) (x : Fin (T + 1) → X) (m : Flow T X) : ℝ :=
  ⨅ w : ProgFrom T X G t, condCost M ρ φ t x m w

end ProgCorrMFG.Approx


