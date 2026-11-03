-- Prove2me | Definitions.Def_OnDemandCoord_Coordinates
-- name    : OnDemandCoord_Coordinates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:17.057444+00:00
-- url     : https://prove2.me/theorems/8ec30928-269b-41c3-a572-7bbafd6242fd
-- title:
--   The contract (11)–(12), payoffs (2)–(3), Nash equilibrium, coordination, (14), (16′), (17)
-- statement:
--   **The contract** (§5.2, p. 18). For membership fees $r_i$, parameters $m_i$ and target fill rates $\beta_i$, firm $i$ pays the **fixed rate** (11) $w^F_i=p(1-m_i/\beta_i)$ per unit allocated and the **contingent payment** (12) $$w^C_i(A_i,\hat X_i)=\frac{p\,m_i\,(A_i-\beta_i\hat X_i)}{\beta_i},$$ so that its total transfer is $w_i(A,\hat X)=r_i+w^F_iA_i+w^C_i(A_i,\hat X_i)$.
--
--   **Payoffs** (p. 9), with $\hat X=(X-Q)^+$, $S=NG(\eta)$ and $A\sim\kappa(\hat X,S)$:
--   1. the platform's expected profit (2), $\Pi(\eta,\kappa\mid Q)=\sum_i\mathbb E[w_i(A,\hat X)]-\eta NG(\eta)$;
--   2. firm $i$'s expected cost (3), $h_i(Q_i\mid Q_{-i},\kappa,\eta)=\mathbb E[p(\hat X_i-A_i)^++w_i(A,\hat X)]+cQ_i$.
--
--   **Nash equilibrium** (p. 10): given $Q$, $(\eta,\kappa)$ maximizes $\Pi(\cdot,\cdot\mid Q)$ over all $\eta'\in\mathbb R$ and all $\kappa'\in\mathcal A$; and for every firm $i$, $Q_i$ minimizes $h_i(\cdot\mid Q_{-i},\kappa,\eta)$ over $Q_i'\ge0$, with the policy unchanged.
--
--   **Coordination** (p. 18): $\kappa\in\mathcal A$, $(Q,\eta,\kappa)$ is a Nash equilibrium, $\Pi(\eta,\kappa\mid Q)\ge0$, and $h_i(Q_i)\le h^p_i$ for every firm.
--
--   The module also defines the parameter (14), $m_i=(p\bar F_i(Q_i)-c)/(p\bar F_i(Q_i))$, the fee conditions
--   $$\text{(16′)}\quad \sum_i r_i\ \ge\ C(Q^*,\eta^*)-c\sum_iQ^*_i-p\sum_i(1-m_i)\,\mathbb E[(X_i-Q^*_i)^+],$$
--   $$\text{(17)}\quad r_i\ \le\ h^p_i-\big(p(1-m_i)\,\mathbb E[(X_i-Q^*_i)^+]+cQ^*_i\big).$$
--
--   **Formalization Note** The three contract terms are kept apart as printed; the contract is not defined by its sum $r_i+p(A_i-m_i\hat X_i)$. (16′) corrects the printed (16), which omits $-c\sum_iQ^*_i$ (the derivation on p. 20 has it); printed (16) implies (16′). Payoffs are integrals of a policy's inner integral against the law of $X$.
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), §5.2 pp. 18–22: (2)–(3) p. 9, Nash equilibrium p. 10, (11)–(12) and coordination p. 18, (14) p. 21, (16)–(17) pp. 21–22

import Mathlib
import Definitions.Def_OnDemandCoord_tfrbPolicy

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- The parameters of the contract of §5.2, p. 18: membership fees `r_i`, parameters `m_i`, and
target fill rates `β_i`. -/
structure Contract (n : ℕ) where
  /-- The membership fee `r_i`. -/
  r : Fin n → ℝ
  /-- The contract parameter `m_i`. -/
  m : Fin n → ℝ
  /-- The target fill rate `β_i`. -/
  β : Fin n → ℝ

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)

/-- **The fixed rate (11)**, p. 18: `w_i^F = p (1 − m_i / β_i)`. -/
noncomputable def fixedRate (K : Contract n) (i : Fin n) : ℝ := M.p * (1 - K.m i / K.β i)

/-- **The contingent payment (12)**, p. 18: `w_i^C(a, x̂) = p m_i (a − β_i x̂) / β_i`. -/
noncomputable def contingentPayment (K : Contract n) (i : Fin n) (a x : ℝ) : ℝ :=
  M.p * K.m i * (a - K.β i * x) / K.β i

/-- **The transfer payment** of firm `i` to the platform, pp. 18–19: the membership fee, the fixed
rate per unit allocated, and the contingent payment, kept apart as printed:
`w_i(a, x̂) = r_i + w_i^F a_i + w_i^C(a_i, x̂_i)`. -/
noncomputable def payment (K : Contract n) (i : Fin n) (a x : Fin n → ℝ) : ℝ :=
  K.r i + M.fixedRate K i * a i + M.contingentPayment K i (a i) (x i)

/-- **The platform's expected profit (2)**, p. 9, unreduced:
`Π(η, κ | Q) = ∑_i E[w_i(A, X̂)] − η N G(η)`, with `A ∼ κ (X̂, S)`, `S = N G(η)`. -/
noncomputable def platformProfit (K : Contract n) (η : ℝ)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) (Q : Fin n → ℝ) : ℝ :=
  ∑ i, ∫ ω, ∫ a, M.payment K i a (M.vacVec Q ω) ∂κ (M.vacVec Q ω, M.S η) ∂P - η * M.S η

/-- **Firm `i`'s expected staffing cost (3)**, p. 9, unreduced:
`h_i(Q_i | Q_{−i}, κ, η) = E[p (X̂_i − A_i)⁺ + w_i(A, X̂)] + c Q_i`, with `A ∼ κ (X̂, S)`. The argument
`Q` is the whole profile, `Q_i` and `Q_{−i}` together. -/
noncomputable def firmCost (K : Contract n) (i : Fin n) (Q : Fin n → ℝ)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) (η : ℝ) : ℝ :=
  (∫ ω, ∫ a, (M.p * max (M.vac Q i ω - a i) 0 + M.payment K i a (M.vacVec Q ω))
      ∂κ (M.vacVec Q ω, M.S η) ∂P) + M.c * Q i

/-- **The parameter (14)**, p. 21: `m_i = (p F̄_i(Q_i) − c) / (p F̄_i(Q_i))`, at the staffing level `Q`.
At a system optimum `F̄_i(Q_i) > 0` is a theorem (`system_optimum_interior`), not an assumption. -/
noncomputable def mParam (Q : Fin n → ℝ) (i : Fin n) : ℝ :=
  (M.p * M.Fbar i (Q i) - M.c) / (M.p * M.Fbar i (Q i))

/-- **The Nash equilibrium** of p. 10 under the contract `K`: (i) given `Q`, the pair `(η, κ)`
maximizes (2) over every compensation rate and every policy in `𝒜`; (ii) for every firm `i`, given
`(η, κ)` and `Q_{−i}`, `Q_i` minimizes (3) over `q ≥ 0`. Under deviation `κ` is unchanged. -/
def IsNashEquilibrium (K : Contract n) (Q : Fin n → ℝ) (η : ℝ)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) : Prop :=
  (∀ (η' : ℝ) (κ' : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)), IsPolicy κ' →
      M.platformProfit K η' κ' Q ≤ M.platformProfit K η κ Q) ∧
    ∀ (i : Fin n) (q : ℝ), 0 ≤ q →
      M.firmCost K i Q κ η ≤ M.firmCost K i (Function.update Q i q) κ η

/-- **Coordination**, p. 18: (i) `κ ∈ 𝒜` and `(Q, η, κ)` is a Nash equilibrium under `K`; (ii) the
platform's expected profit is nonnegative and no firm is worse off than its stand-alone cost
`h_i^p` (at the permanent-only level `Qp`). The theorems apply this at a system optimum `(Q, η)`. -/
def Coordinates (K : Contract n) (Qp Q : Fin n → ℝ) (η : ℝ)
    (κ : Kernel ((Fin n → ℝ) × ℝ) (Fin n → ℝ)) : Prop :=
  (IsPolicy κ ∧ M.IsNashEquilibrium K Q η κ) ∧
    0 ≤ M.platformProfit K η κ Q ∧ ∀ i, M.firmCost K i Q κ η ≤ M.hp Qp i

/-- **(16′)**, the corrected form of (16), p. 21 (cf. the display on p. 20):
`∑_i r_i ≥ C(Q, η) − c ∑_i Q_i − p ∑_i (1 − m_i) E[(X_i − Q_i)⁺]`. -/
def FeeLower (Q : Fin n → ℝ) (η : ℝ) (m r : Fin n → ℝ) : Prop :=
  M.C Q η - M.c * ∑ i, Q i - M.p * ∑ i, (1 - m i) * M.mean Q i ≤ ∑ i, r i

/-- **(17)**, p. 22, for firm `i`:
`r_i ≤ h_i^p − (p (1 − m_i) E[(X_i − Q_i)⁺] + c Q_i)`. -/
def FeeUpper (Qp Q : Fin n → ℝ) (m r : Fin n → ℝ) (i : Fin n) : Prop :=
  r i ≤ M.hp Qp i - (M.p * (1 - m i) * M.mean Q i + M.c * Q i)

end Model

end OnDemandCoord


