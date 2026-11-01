-- Prove2me | Definitions.Def_OLPRegret_regret
-- name    : OLPRegret_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:42.661233+00:00
-- url     : https://prove2.me/theorems/1aaf1c4e-3aca-4b69-83a0-b82f379d1640
-- title:
--   Offline integer and linear programs and the expected regret
-- statement:
--   For $t$ customers and $b\in\mathbb R^m_+$, the **offline integer program** and its **linear relaxation** are
--   $$
--   V_t^b=\max_{x\in\{0,1\}^t}\sum_{s=1}^t x_su_s\quad\text{s.t.}\quad\sum_{s=1}^t x_sa_s\le tb,
--   \qquad
--   \bar V_t^b=\max_{x\in[0,1]^t}\sum_{s=1}^t x_su_s\quad\text{s.t.}\quad\sum_{s=1}^t x_sa_s\le tb.
--   $$
--   The expected **regret** of a policy is $\mathrm E(R_n)=\mathrm E(V_n^\beta)-\mathrm E(\text{online value})$, and its regret against the linear program is $\mathrm E(\underline R_n)=\mathrm E(\bar V_n^\beta)-\mathrm E(\text{online value})$.
--
--   The regret is the mission's central quantity. The relaxation is the benchmark of the proof.
--
--   **Formalization Note** $V$ is a finite maximum over feasible subsets. $\bar V$ is the supremum of a set that is nonempty and bounded above when $b\ge0$; the mission evaluates both only at $b\ge0$. The integrands of the regret lie in $[0,\sum_s u_s]$ almost surely, so the Bochner integrals are not junk values.
-- source:
--   Bray, arXiv:1912.08917v6, (16)–(18), pp.18–19; (38), p.31

import Mathlib
import Definitions.Def_OLPRegret_Policy

set_option autoImplicit false

open MeasureTheory

namespace OLPRegret

open scoped Classical in
/-- The subsets of the `t` customers feasible for the integer program (16) at endowment `tb`. -/
noncomputable def ipFeasible {m t : ℕ} (s : Sample m t) (b : E m) : Finset (Finset (Fin t)) :=
  Finset.univ.filter fun S => VLe (∑ i ∈ S, (s i).2) ((t : ℝ) • b)

open scoped Classical in
/-- The offline integer program `Vₜᵇ = max_{x ∈ {0,1}ᵗ} Σ xₛuₛ` s.t. `Σ xₛaₛ ≤ tb`
(Bray, arXiv:1912.08917v6, (16), p.18).

**Formalization Note** A finite maximum over feasible subsets. The empty subset is feasible when
`b ≥ 0`, the only case the mission uses; the value `0` on an empty feasible family is unreachable
there. -/
noncomputable def offlineIP {m t : ℕ} (s : Sample m t) (b : E m) : ℝ :=
  if h : (ipFeasible s b).Nonempty then (ipFeasible s b).sup' h fun S => ∑ i ∈ S, (s i).1
  else 0

/-- The objective values of the feasible points of the linear program (18). -/
def lpValues {m t : ℕ} (s : Sample m t) (b : E m) : Set ℝ :=
  {v | ∃ x : Fin t → ℝ, (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧
    VLe (∑ i, x i • (s i).2) ((t : ℝ) • b) ∧ v = ∑ i, x i * (s i).1}

/-- The offline linear program `V̄ₜᵇ = max_{x ∈ [0,1]ᵗ} Σ xₛuₛ` s.t. `Σ xₛaₛ ≤ tb`
(Bray, arXiv:1912.08917v6, (18), p.19).

**Formalization Note** `lpValues` is nonempty when `b ≥ 0` (take `x = 0`) and bounded above by
`Σ |uₛ|`, and the feasible set is compact, so this `sSup` is the printed maximum; the mission uses
it only at `b ≥ 0`. The dual identity (19) is a fact about this value, not its definition. -/
noncomputable def offlineLP {m t : ℕ} (s : Sample m t) (b : E m) : ℝ :=
  sSup (lpValues s b)

/-- The expected regret `E(Rₙ) = E(Vₙᵝ) − E(online value)` of a policy
(Bray, arXiv:1912.08917v6, (17), p.18).

**Formalization Note** Both integrands are integrable under Assumptions 2–3: they lie in
`[0, Σ uₛ]` almost surely. -/
noncomputable def regret {m n : ℕ} (μ : Measure (Customer m)) [SigmaFinite μ] (β : E m)
    (π : Policy m n) : ℝ :=
  ∫ ω, offlineIP ω β ∂sampleLaw μ n - ∫ ω, onlineValue π.scheme β ω ∂sampleLaw μ n

/-- The expected regret against the linear program, `E(R̲ₙ) = E(V̄ₙᵝ) − E(online value)`
(Bray, arXiv:1912.08917v6, (38), p.31). -/
noncomputable def regretLP {m n : ℕ} (μ : Measure (Customer m)) [SigmaFinite μ] (β : E m)
    (π : Policy m n) : ℝ :=
  ∫ ω, offlineLP ω β ∂sampleLaw μ n - ∫ ω, onlineValue π.scheme β ω ∂sampleLaw μ n

end OLPRegret


