-- Prove2me | Definitions.Def_ResAllocGaps_arrivals
-- name    : ResAllocGaps_arrivals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:12.375382+00:00
-- url     : https://prove2.me/theorems/2d01b65a-68bd-4995-aa03-5b5127cd13f9
-- title:
--   Proof objects of Theorem 1: partition (EC.2), counts (EC.3), (EC.11), events (EC.4)–(EC.12)
-- statement:
--   Fix $\beta>0$, $T\ge1$, the law $F_\beta$ (so $\ell=\tfrac14$, $u=\tfrac34$) and the budget $B=\lfloor T/2\rfloor$. Let
--   $$\Delta_\beta=T^{-1/(2(1+\beta))}(1-u),\quad c_0=(129/128)^{1/(1+\beta)},\quad \alpha_0=c_0-1,$$
--   $\ell_1=\ell-\Delta_\beta$, $\ell_2=\ell-c_0\Delta_\beta$, $u_1=u+\Delta_\beta$, $u_2=u+c_0\Delta_\beta$ (EC.2), and partition $[0,\ell]\cup[u,1]$ into
--   $I_L=[0,\ell_2)$, $I_{M_1}=[\ell_2,\ell_1)$, $I_{M_2}=[\ell_1,\ell]$, $I_{M_3}=[u,u_1)$, $I_{M_4}=[u_1,u_2)$, $I_H=[u_2,1]$, with $I_{M_c}=I_{M_2}\cup I_{M_3}$ and $I_{M_p}=I_{M_1}\cup I_{M_4}$.
--
--   $N(\mathcal A,t_1,t_2)$ is the number of arrivals at times $t_1,\dots,t_2$ with ability in $\mathcal A$ (EC.3), and $N^\pi(\mathcal A,t_1,t_2)$ the number of those accepted by the policy $\pi$ (EC.11). The events are
--   1. $\mathcal H_1=\{T/4-\sqrt T/2\le N(I_H,1,B)\le T/4\}$,
--   2. $\mathcal H_2=\{T/4-4\sqrt T\le N(I_H,B+1,T)\le T/4-3\sqrt T\}$,
--   3. $\tilde{\mathcal H}_2=\{T/4+\sqrt T/2\le N(I_H,B+1,T)\le T/4+3\sqrt T/2\}$,
--   4. $\mathcal C_1=\{\sqrt T/4\le N(I_{M_c},1,B)\le\sqrt T\}$, $\mathcal C_2=\{\sqrt T/4\le N(I_{M_c},B+1,T)\le\sqrt T\}$,
--   5. (corrected) $\mathcal P_1=\{N(I_{M_p},1,B)\le\sqrt T/64\}$, $\mathcal P_2=\{N(I_{M_p},B+1,T)\le\sqrt T/64\}$,
--   6. $\mathcal H=\mathcal H_1\cap\mathcal H_2$, $\tilde{\mathcal H}=\mathcal H_1\cap\tilde{\mathcal H}_2$, $\mathcal C=\mathcal C_1\cap\mathcal C_2$, $\mathcal P=\mathcal P_1\cap\mathcal P_2$,
--   7. $\mathcal E_\pi=\{N^\pi(I_{M_c},1,B)\ge N(I_{M_c},1,B)/8\}$ (EC.12).
--
--   These are the objects of the milestones that make up the proof of Theorem 1 for $\beta>0$.
--
--   **Formalization Note** The paper's (EC.9), (EC.10) also require $\sqrt T/256\le N(I_{M_p},\cdot)$; that lower bound sits at the mean of the count, which makes Lemma EC.4 false, and it is used nowhere, so it is dropped. $\mathcal E$ is defined for any online policy (the paper uses the DP policy). Times are $1$-based as in the paper; `halfBudget T` is $\lfloor T/2\rfloor$ in $\mathbb N$.
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, Appendix EC.1, pp.ec1–ec3, (EC.2)–(EC.12)

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy

open MeasureTheory

namespace ResAllocGaps

/-! The objects of the proof of Theorem 1 for `β > 0` (Besbes, Kanoria & Kumar,
arXiv:2205.09078v2, Appendix EC.1, pp.ec1–ec3), for the law `F_β` of (1), i.e. `g = 1/2`,
`ℓ = 1/4`, `u = 3/4`, and the budget `B = ⌊T/2⌋`. -/

/-- `ℓ = 1/2 − g/2 = 1/4`, the lower edge of the gap (p.ec1, `g = 1/2`). -/
noncomputable def gapLo : ℝ := 1 / 4

/-- `u = 1/2 + g/2 = 3/4`, the upper edge of the gap (p.ec1, `g = 1/2`). -/
noncomputable def gapHi : ℝ := 3 / 4

/-- The budget `B ≜ ⌊T/2⌋` of the proof (p.ec1), natural-number division. -/
def halfBudget (T : ℕ) : ℕ := T / 2

/-- `Δ_β ≜ T^{−1/(2(1+β))}(1 − u) = T^{−1/(2(1+β))} ℓ` (p.ec1), with `Real.rpow`. -/
noncomputable def deltaBeta (β : ℝ) (T : ℕ) : ℝ :=
  (T : ℝ) ^ (-(1 / (2 * (1 + β)))) * (1 - gapHi)

/-- `c₀ ≜ (129/128)^{1/(1+β)} > 1` (p.ec1). -/
noncomputable def c0 (β : ℝ) : ℝ := (129 / 128 : ℝ) ^ (1 / (1 + β))

/-- `α₀ ≜ c₀ − 1 > 0` (EC.2), p.ec1. -/
noncomputable def alpha0 (β : ℝ) : ℝ := c0 β - 1

/-- `ℓ₁ ≜ ℓ − Δ_β` (EC.2). -/
noncomputable def ell1 (β : ℝ) (T : ℕ) : ℝ := gapLo - deltaBeta β T

/-- `ℓ₂ ≜ ℓ − c₀Δ_β` (EC.2). -/
noncomputable def ell2 (β : ℝ) (T : ℕ) : ℝ := gapLo - c0 β * deltaBeta β T

/-- `u₁ ≜ u + Δ_β` (EC.2). -/
noncomputable def u1 (β : ℝ) (T : ℕ) : ℝ := gapHi + deltaBeta β T

/-- `u₂ ≜ u + c₀Δ_β` (EC.2). -/
noncomputable def u2 (β : ℝ) (T : ℕ) : ℝ := gapHi + c0 β * deltaBeta β T

/-- `I_L = [0, ℓ₂)` (p.ec2). -/
noncomputable def IL (β : ℝ) (T : ℕ) : Set ℝ := Set.Ico 0 (ell2 β T)

/-- `I_{M1} = [ℓ₂, ℓ₁)` (p.ec2). -/
noncomputable def IM1 (β : ℝ) (T : ℕ) : Set ℝ := Set.Ico (ell2 β T) (ell1 β T)

/-- `I_{M2} = [ℓ₁, ℓ]` (p.ec2). -/
noncomputable def IM2 (β : ℝ) (T : ℕ) : Set ℝ := Set.Icc (ell1 β T) gapLo

/-- `I_{M3} = [u, u₁)` (p.ec2). -/
noncomputable def IM3 (β : ℝ) (T : ℕ) : Set ℝ := Set.Ico gapHi (u1 β T)

/-- `I_{M4} = [u₁, u₂)` (p.ec2). -/
noncomputable def IM4 (β : ℝ) (T : ℕ) : Set ℝ := Set.Ico (u1 β T) (u2 β T)

/-- `I_H = [u₂, 1]` (p.ec2). -/
noncomputable def IH (β : ℝ) (T : ℕ) : Set ℝ := Set.Icc (u2 β T) 1

/-- `I_{Mc} ≜ I_{M2} ∪ I_{M3}` (p.ec2). -/
noncomputable def IMc (β : ℝ) (T : ℕ) : Set ℝ := IM2 β T ∪ IM3 β T

/-- `I_{Mp} ≜ I_{M1} ∪ I_{M4}` (p.ec2). -/
noncomputable def IMp (β : ℝ) (T : ℕ) : Set ℝ := IM1 β T ∪ IM4 β T

open Classical in
/-- `N(A, t₁, t₂) ≜ Σ_{k=t₁}^{t₂} 1{θ_k ∈ A}` (EC.3), p.ec2: the number of candidate abilities in
`A` arriving at times `t₁, …, t₂` (paper's times; index `t : Fin T` is time `t + 1`). -/
noncomputable def arrivals {T : ℕ} (A : Set ℝ) (t₁ t₂ : ℕ) (ω : Sample T) : ℕ :=
  (Finset.univ.filter (fun t : Fin T => t₁ ≤ t.val + 1 ∧ t.val + 1 ≤ t₂ ∧ (ω t).1 ∈ A)).card

open Classical in
/-- `N^π(A, t₁, t₂) ≜ Σ_{k=t₁}^{t₂} 1{θ_k ∈ A, a^π_k = accept}`, the number of accepted candidates
with ability in `A` arriving at times `t₁, …, t₂`: (EC.11), p.ec3, written there for the DP policy
and here for any online policy `π`. -/
noncomputable def accepted {μ : Measure ℝ} {T B : ℕ} (π : OnlinePolicy μ T B) (A : Set ℝ)
    (t₁ t₂ : ℕ) (ω : Sample T) : ℕ :=
  (Finset.univ.filter (fun t : Fin T =>
    t₁ ≤ t.val + 1 ∧ t.val + 1 ≤ t₂ ∧ (ω t).1 ∈ A ∧ π.decision ω t = true)).card

/-- `H₁ ≜ {T/4 − √T/2 ≤ N(I_H, 1, B) ≤ T/4}` (EC.4), p.ec2, `B = ⌊T/2⌋`. -/
noncomputable def eventH1 (β : ℝ) (T : ℕ) : Set (Sample T) :=
  {ω | (T : ℝ) / 4 - √(T : ℝ) / 2 ≤ (arrivals (IH β T) 1 (halfBudget T) ω : ℝ) ∧
    (arrivals (IH β T) 1 (halfBudget T) ω : ℝ) ≤ (T : ℝ) / 4}

/-- `H₂ ≜ {T/4 − 4√T ≤ N(I_H, B + 1, T) ≤ T/4 − 3√T}` (EC.5), p.ec2. -/
noncomputable def eventH2 (β : ℝ) (T : ℕ) : Set (Sample T) :=
  {ω | (T : ℝ) / 4 - 4 * √(T : ℝ) ≤ (arrivals (IH β T) (halfBudget T + 1) T ω : ℝ) ∧
    (arrivals (IH β T) (halfBudget T + 1) T ω : ℝ) ≤ (T : ℝ) / 4 - 3 * √(T : ℝ)}

/-- `H̃₂ ≜ {T/4 + √T/2 ≤ N(I_H, B + 1, T) ≤ T/4 + 3√T/2}` (EC.6), p.ec2. -/
noncomputable def eventH2t (β : ℝ) (T : ℕ) : Set (Sample T) :=
  {ω | (T : ℝ) / 4 + √(T : ℝ) / 2 ≤ (arrivals (IH β T) (halfBudget T + 1) T ω : ℝ) ∧
    (arrivals (IH β T) (halfBudget T + 1) T ω : ℝ) ≤ (T : ℝ) / 4 + 3 * √(T : ℝ) / 2}

/-- `C₁ ≜ {√T/4 ≤ N(I_{Mc}, 1, B) ≤ √T}` (EC.7), p.ec2. -/
noncomputable def eventC1 (β : ℝ) (T : ℕ) : Set (Sample T) :=
  {ω | √(T : ℝ) / 4 ≤ (arrivals (IMc β T) 1 (halfBudget T) ω : ℝ) ∧
    (arrivals (IMc β T) 1 (halfBudget T) ω : ℝ) ≤ √(T : ℝ)}

/-- `C₂ ≜ {√T/4 ≤ N(I_{Mc}, B + 1, T) ≤ √T}` (EC.8), p.ec2. -/
noncomputable def eventC2 (β : ℝ) (T : ℕ) : Set (Sample T) :=
  {ω | √(T : ℝ) / 4 ≤ (arrivals (IMc β T) (halfBudget T + 1) T ω : ℝ) ∧
    (arrivals (IMc β T) (halfBudget T + 1) T ω : ℝ) ≤ √(T : ℝ)}

/-- The **corrected** event `P₁ ≜ {N(I_{Mp}, 1, B) ≤ √T/64}`: (EC.9), p.ec2, without its lower
bound `√T/256 ≤ N(I_{Mp}, 1, B)`.

**Formalization Note (correction).** As printed, (EC.9) has the lower bound `√T/256` at (or above)
the mean of `N(I_{Mp}, 1, B) ∼ Bin(⌊T/2⌋, T^{−1/2}/128)`, so `P(P₁ᶜ) → 1/2` and Lemma EC.4 fails;
no step of the proof uses the lower bound. -/
noncomputable def eventP1 (β : ℝ) (T : ℕ) : Set (Sample T) :=
  {ω | (arrivals (IMp β T) 1 (halfBudget T) ω : ℝ) ≤ √(T : ℝ) / 64}

/-- The **corrected** event `P₂ ≜ {N(I_{Mp}, B + 1, T) ≤ √T/64}`: (EC.10), p.ec2, without its
lower bound `√T/256`, for the same reason as `eventP1`. -/
noncomputable def eventP2 (β : ℝ) (T : ℕ) : Set (Sample T) :=
  {ω | (arrivals (IMp β T) (halfBudget T + 1) T ω : ℝ) ≤ √(T : ℝ) / 64}

/-- `H ≜ H₁ ∩ H₂` (p.ec2). -/
noncomputable def eventH (β : ℝ) (T : ℕ) : Set (Sample T) := eventH1 β T ∩ eventH2 β T

/-- `H̃ ≜ H₁ ∩ H̃₂` (p.ec2). -/
noncomputable def eventHt (β : ℝ) (T : ℕ) : Set (Sample T) := eventH1 β T ∩ eventH2t β T

/-- `C ≜ C₁ ∩ C₂` (p.ec2). -/
noncomputable def eventC (β : ℝ) (T : ℕ) : Set (Sample T) := eventC1 β T ∩ eventC2 β T

/-- `P ≜ P₁ ∩ P₂` (p.ec2), with the corrected `P₁`, `P₂`. -/
noncomputable def eventP (β : ℝ) (T : ℕ) : Set (Sample T) := eventP1 β T ∩ eventP2 β T

/-- `E ≜ {N^π(I_{Mc}, 1, B) ≥ N(I_{Mc}, 1, B)/8}` (EC.12), p.ec3, for an online policy `π` with
budget `B` (in the paper `π` is the DP policy and `B = ⌊T/2⌋`): by time `B` the policy has accepted
at least one eighth of the arrivals in `I_{Mc}`. -/
noncomputable def eventE {μ : Measure ℝ} {T B : ℕ} (π : OnlinePolicy μ T B) (β : ℝ) :
    Set (Sample T) :=
  {ω | (arrivals (IMc β T) 1 B ω : ℝ) / 8 ≤ (accepted π (IMc β T) 1 B ω : ℝ)}

end ResAllocGaps


