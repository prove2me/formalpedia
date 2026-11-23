-- Prove2me | Definitions.Def_DynamicOnlineLP_DLA_Supplement_MultiAlgorithm
-- name    : DynamicOnlineLP_DLA_Supplement_MultiAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:08:04.648967+00:00
-- url     : https://prove2.me/theorems/0ea8b93a-a2b8-4ca2-983a-64f241b28e27
-- title:
--   Multidimensional dynamic learning algorithm: prefix-only prices, surplus proposals, executed decisions, rounding
-- statement:
--   Section 5.1 runs the dynamic learning algorithm (DLA) of §3 with the vector allocation rule $x_t(p)$. Section 3 analyses it for $\varepsilon=2^{-E}$ with $\varepsilon n$ an integer. The definition below also fixes what it does for every real $\varepsilon>0$ and every horizon $n$.
--
--   Let $E=\max\{1,\lceil\log_2(1/\varepsilon)\rceil\}$, $\delta=2^{-E}$, $\ell_r=\lceil2^r\delta n\rceil$ and $h_\ell=\delta\sqrt{n/\ell}$. Thus $\ell_E=n$.
--
--   1. **Learned prices.** A dual-selection rule sees only the first $\ell$ blocks and returns an optimal dual resource price $\hat p^{\ell}$ of
--   $$\max\sum_{t=1}^{\ell}f_t^{\top}x_t\quad\text{s.t.}\quad\sum_{t=1}^{\ell}g_{it}^{\top}x_t\le(1-h_\ell)\frac{\ell}{n}b_i,\qquad x_t\in K .$$
--   2. **Ties.** A tie-breaking rule sees only the blocks up to the current one and returns a choice allowed by the surplus rule.
--   3. **Proposal, case $\delta n\ge1$.** The proposal is $0$ for $t\le\ell_0$. For $t>\ell_0$ it is $x_t(\hat p^{\ell_r})$, where $r<E$ is the largest index with $\ell_r<t$.
--   4. **Proposal, case $\delta n<1$.** The learning window is shorter than one arrival. The proposal is $x_t(0)$, that is, an option of largest reward, or $0$ if no reward is positive.
--   5. **Execution.** The proposal $\hat x_t$ is executed if $g_{it}^{\top}\hat x_t$ is at most the remaining amount $b_i-\sum_{s<t}g_{is}^{\top}x_s$ for every $i$. Otherwise $x_t=0$.
--
--   The **value** of the algorithm in order $\sigma$ is the reward $\sum_tf_{\sigma(t)}^{\top}x_t$ of the executed decisions, which may differ from the proposals.
--
--   When $\varepsilon=2^{-E}$, $E\ge1$, and $\varepsilon n$ is a positive integer, $\delta=\varepsilon$ and $\ell_r=2^r\varepsilon n$, so this is exactly Algorithm DLA with the vector rule. The ceilings and case 4 are boundary conventions for the parameters on which the paper assumes integrality without loss of generality.
--
--   **Formalization Note** The dual and tie-breaking rules are parameters with validity predicates, so that theorems cover every valid selection. A dual rule must return an optimum for every $\ell\le n$ and every $d\ge0$; one exists because that dual program is feasible and bounded below by $0$. Lean time $\tau$ is the paper's time $\tau+1$. The quantities $\delta$ and $h_\ell$ reuse `eps` and `slack` of the published algorithm file.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 886, §5.1; pp. 883–884, Eq. (13) and Algorithm DLA; p. 881, integrality convention

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_DynamicOnlineLP_DLA_Algorithm
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SimplexPackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SurplusRule
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_MultiInstance

namespace DynamicOnlineLP.DLA.Supplement

/-- A dual-selection rule: from a learning time `ℓ`, the arrival sequence and a right-hand side,
it returns a resource price vector. -/
def MultiDualRule (m n k : ℕ) : Type :=
  ℕ → (Fin n → Fin k → ℝ) → (Fin n → Fin m → Fin k → ℝ) → (Fin m → ℝ) → (Fin m → ℝ)

/-- A valid dual-selection rule sees only the first `ℓ` blocks and, for `ℓ ≤ n` and `d ≥ 0`,
returns an optimal dual resource price of the simplex packing LP on these blocks. -/
def IsValidMultiDualRule {m n k : ℕ} (rule : MultiDualRule m n k) : Prop :=
  (∀ (ℓ : ℕ) (f f' : Fin n → Fin k → ℝ) (g g' : Fin n → Fin m → Fin k → ℝ) (d : Fin m → ℝ),
      (∀ t : Fin n, t.val < ℓ → f t = f' t ∧ g t = g' t) → rule ℓ f g d = rule ℓ f' g' d) ∧
  ∀ (ℓ : ℕ) (f : Fin n → Fin k → ℝ) (g : Fin n → Fin m → Fin k → ℝ) (d : Fin m → ℝ),
    ℓ ≤ n → (∀ i : Fin m, 0 ≤ d i) → IsBlockOptimalPrice (firstTimes n ℓ) f g d (rule ℓ f g d)

/-- A tie-breaking rule: from the current time, the arrival sequence and a price, it returns
rejection or one of the `k` options. -/
def TieRule (m n k : ℕ) : Type :=
  Fin n → (Fin n → Fin k → ℝ) → (Fin n → Fin m → Fin k → ℝ) → (Fin m → ℝ) → Option (Fin k)

/-- A valid tie-breaking rule sees only the blocks that arrived up to and including the current
time and always returns an allowed choice of the surplus rule for the current block. -/
def IsValidTieRule {m n k : ℕ} (tie : TieRule m n k) : Prop :=
  (∀ (t : Fin n) (f f' : Fin n → Fin k → ℝ) (g g' : Fin n → Fin m → Fin k → ℝ) (p : Fin m → ℝ),
      (∀ u : Fin n, u ≤ t → f u = f' u ∧ g u = g' u) → tie t f g p = tie t f' g' p) ∧
  ∀ (t : Fin n) (f : Fin n → Fin k → ℝ) (g : Fin n → Fin m → Fin k → ℝ) (p : Fin m → ℝ),
    IsSurplusChoice (f t) (g t) p (tie t f g p)

/-- The exponent `E` of the accuracy `δ = 2^{-E}` used for a real `ε > 0`: the least natural
`E ≥ 1` with `2^{-E} ≤ ε`, i.e. `E = max 1 ⌈log₂(1/ε)⌉`. -/
noncomputable def accuracyExp (ε : ℝ) : ℕ :=
  max 1 ⌈Real.logb 2 (1 / ε)⌉₊

/-- The learning time `ℓ_r = ⌈2^r δ n⌉`, with `δ = 2^{-E}`. -/
noncomputable def learnTime (n E r : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ r * eps E * (n : ℝ)⌉₊

/-- For a 0-based time `τ ≥ ℓ_0`, the largest `r < E` with `ℓ_r ≤ τ` (equivalently `ℓ_r < t` for
the paper's time `t = τ + 1`). -/
noncomputable def phaseIndex (n E τ : ℕ) : ℕ :=
  ((Finset.range E).filter (fun r => learnTime n E r ≤ τ)).sup id

/-- The price learned at time `ℓ` in arrival order `σ`: an optimal dual resource price of the LP
on the first `ℓ` blocks with right-hand side `(1 - h_ℓ)(ℓ/n) b`, where `h_ℓ = δ √(n/ℓ)`. -/
noncomputable def multiLearnedPrice {m n k : ℕ} (I : MultiInstance m n k)
    (rule : MultiDualRule m n k) (E : ℕ) (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) : Fin m → ℝ :=
  rule ℓ (I.arrF σ) (I.arrG σ) (fun i => (1 - slack n E ℓ) * ((ℓ : ℝ) / (n : ℝ)) * I.b i)

/-- The proposed decision at 0-based time `t`. If the learning window `δ n` is shorter than one
arrival, it is the surplus choice at price zero (a best-reward option). Otherwise it is zero
during the first `ℓ_0` arrivals and afterwards the surplus choice at the price learned at the
start of the current phase. -/
noncomputable def multiProposal {m n k : ℕ} (I : MultiInstance m n k) (rule : MultiDualRule m n k)
    (tie : TieRule m n k) (ε : ℝ) (σ : Equiv.Perm (Fin n)) (t : Fin n) : Fin k → ℝ :=
  let E := accuracyExp ε
  if eps E * (n : ℝ) < 1 then
    choiceVec (tie t (I.arrF σ) (I.arrG σ) (fun _ => 0))
  else if t.val < learnTime n E 0 then
    fun _ => 0
  else
    choiceVec (tie t (I.arrF σ) (I.arrG σ)
      (multiLearnedPrice I rule E σ (learnTime n E (phaseIndex n E t.val))))

/-- Given the resources `used` by the earlier decisions, the proposal is executed if it fits the
remaining amount of every resource, and the zero vector is executed otherwise. -/
noncomputable def multiDecision {m n k : ℕ} (I : MultiInstance m n k) (rule : MultiDualRule m n k)
    (tie : TieRule m n k) (ε : ℝ) (σ : Equiv.Perm (Fin n)) (used : Fin m → ℝ) (t : Fin n) :
    Fin k → ℝ :=
  by classical exact
    if ∀ i : Fin m, ∑ j : Fin k, I.arrG σ t i j * multiProposal I rule tie ε σ t j ≤ I.b i - used i
    then multiProposal I rule tie ε σ t else fun _ => 0

/-- Resources consumed by the executed decisions at the first `τ` times. -/
noncomputable def multiUsed {m n k : ℕ} (I : MultiInstance m n k) (rule : MultiDualRule m n k)
    (tie : TieRule m n k) (ε : ℝ) (σ : Equiv.Perm (Fin n)) : ℕ → Fin m → ℝ
  | 0 => fun _ => 0
  | τ + 1 => fun i =>
      if h : τ < n then
        multiUsed I rule tie ε σ τ i +
          ∑ j : Fin k, I.arrG σ ⟨τ, h⟩ i j *
            multiDecision I rule tie ε σ (multiUsed I rule tie ε σ τ) ⟨τ, h⟩ j
      else multiUsed I rule tie ε σ τ i

/-- The executed decision vector at 0-based time `t` in arrival order `σ`. -/
noncomputable def multiX {m n k : ℕ} (I : MultiInstance m n k) (rule : MultiDualRule m n k)
    (tie : TieRule m n k) (ε : ℝ) (σ : Equiv.Perm (Fin n)) (t : Fin n) : Fin k → ℝ :=
  multiDecision I rule tie ε σ (multiUsed I rule tie ε σ t.val) t

/-- The reward `∑_t f_{σ(t)}ᵀ x_t` of the executed decisions. -/
noncomputable def multiValue {m n k : ℕ} (I : MultiInstance m n k) (rule : MultiDualRule m n k)
    (tie : TieRule m n k) (ε : ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ t : Fin n, ∑ j : Fin k, I.arrF σ t j * multiX I rule tie ε σ t j

end DynamicOnlineLP.DLA.Supplement


