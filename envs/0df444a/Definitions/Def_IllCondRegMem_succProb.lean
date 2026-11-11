-- Prove2me | Definitions.Def_IllCondRegMem_succProb
-- name    : IllCondRegMem_succProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:57:36.979564+00:00
-- url     : https://prove2.me/theorems/11966578-7282-455c-92a1-d7c63dd1b769
-- title:
--   Success probability $\mathbb P(\|\hat x-x^\star\|\le\epsilon)$ in non-i.i.d. regression
-- statement:
--   Fix a learner with $M$ bits and $T$ samples and an adaptive adversary. The interaction is:
--
--   1. the target is drawn as $x^\star\sim\mathcal N(0,I/d)$;
--   2. on each round $t=1,\dots,T$ the adversary selects $\Sigma_t=A_tA_t^\top$ from its seed, $x^\star$, the past samples and $\mathrm{Memory}_{t-1}$, the covariate is $a_t=A_tg_t$ with $g_t\sim\mathcal N(0,I_d)$, the response is $b_t=a_t^\top x^\star$, and the learner updates $\mathrm{Memory}_t=B_t(\mathrm{Memory}_{t-1},(a_t,b_t))$ with fresh randomness;
--   3. the learner predicts $\hat x=\hat x(\mathrm{Memory}_T)$.
--
--   The **success probability at accuracy $\epsilon$** is
--   $$
--   \mathbb P\big(\|\hat x-x^\star\|\le\epsilon\big),
--   $$
--   and a learner **succeeds against every adaptive $\kappa$-conditioned adversary** at accuracy $\epsilon$ when this probability is at least $1/3$ for each such adversary. This is the hypothesis of Theorem 1.
--
--   **Formalization Note** All randomness is a deterministic function of independent seeds: $x^\star$, a uniform adversary seed, i.i.d. standard Gaussians $g_1,\dots,g_T$, i.i.d. uniform learner seeds and a uniform output seed. $\|\cdot\|$ is the Euclidean norm.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), §2, pp.5–6 (PDF pp.6–7); Theorem 1, p.3 (PDF p.4); event $S_\epsilon$, p.36 (PDF p.37)

import Mathlib
import Definitions.Def_IllCondRegMem_Adversary

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- The random inputs of one run of the interaction: the target `x⋆`, the adversary's seed `ω`,
the Gaussian vectors `g_t`, the learner's per-round seeds `u_t` and its output seed. -/
abbrev Seeds (d T : ℕ) :=
  Vec d × unitInterval × (Fin T → Vec d) × (Fin T → unitInterval) × unitInterval

/-- One round `t` of the interaction: from (memory `Memory_{t−1}`, past samples) to
(memory `Memory_t`, past samples with `(a_t, b_t)` recorded). -/
noncomputable def interStep {d M T : ℕ} {κ : ℝ} (alg : Learner d M T) (adv : Adversary d M T κ)
    (x : Vec d) (ω : unitInterval) (g : Fin T → Vec d) (u : Fin T → unitInterval) (t : Fin T)
    (s : Mem M × (Fin T → Vec d × ℝ)) : Mem M × (Fin T → Vec d × ℝ) :=
  let A := adv.choose t ω x s.2 s.1
  let a := Matrix.toEuclideanLin A (g t)
  let b := inner ℝ a x
  (alg.upd t s.1 (a, b) (u t), Function.update s.2 t (a, b))

/-- The trajectory of (memory, history) after `n` rounds; `Memory₀` is all-zero and the history
starts at `0`. Rounds beyond `T` do nothing. -/
noncomputable def interTraj {d M T : ℕ} {κ : ℝ} (alg : Learner d M T) (adv : Adversary d M T κ)
    (x : Vec d) (ω : unitInterval) (g : Fin T → Vec d) (u : Fin T → unitInterval) :
    ℕ → Mem M × (Fin T → Vec d × ℝ)
  | 0 => (fun _ => false, fun _ => 0)
  | n + 1 =>
    if h : n < T then interStep alg adv x ω g u ⟨n, h⟩ (interTraj alg adv x ω g u n)
    else interTraj alg adv x ω g u n

/-- The learner's prediction `x̂ = x̂(Memory_T)` at the end of the interaction. -/
noncomputable def estimate {d M T : ℕ} {κ : ℝ} (alg : Learner d M T) (adv : Adversary d M T κ)
    (s : Seeds d T) : Vec d :=
  alg.out (interTraj alg adv s.1 s.2.1 s.2.2.1 s.2.2.2.1 T).1 s.2.2.2.2

/-- The law of the random inputs: `x⋆ ∼ N(0, I/d)`, the adversary's seed uniform on `[0,1]`,
`g_1, …, g_T` i.i.d. `N(0, I_d)`, and the learner's seeds i.i.d. uniform on `[0,1]`, all
independent. -/
noncomputable def seedLaw (d T : ℕ) : Measure (Seeds d T) :=
  (multivariateGaussian (0 : Vec d) ((1 / (d : ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ))).prod
    ((volume : Measure unitInterval).prod
      ((Measure.pi fun _ : Fin T => stdGaussian (Vec d)).prod
        ((Measure.pi fun _ : Fin T => (volume : Measure unitInterval)).prod
          (volume : Measure unitInterval))))

/-- **Success probability** `P(‖x̂ − x⋆‖ ≤ ε)` of a learner against an adversary in non-i.i.d.
linear regression.
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), §2,
pp.5–6, and Theorem 1, p.3: the target is drawn as `x⋆ ∼ N(0, I/d)`; on each round
`t = 1, …, T` the adversary selects `Σ_t` and the learner receives `(a_t, a_tᵀx⋆)` with
`a_t ∼ N(0, Σ_t)`; the memory is updated by `Memory_t = B_t(Memory_{t−1}, (a_t, b_t))` from
`Memory₀ = 0`; the prediction is `x̂ = x̂(Memory_T)`, and it recovers `x⋆` to accuracy `ε` when
`‖x̂ − x⋆‖ ≤ ε` (the event `S_ε` of p.36).

**Formalization Note.** On round `t` (indexed `0, …, T−1`) the adversary's factor `A_t` is chosen
from its seed, `x⋆`, the past samples and `Memory_{t−1}`, the covariate is `a_t = A_t g_t`, the
response is `b_t = ⟨a_t, x⋆⟩`, and the learner updates with its fresh seed `u_t`. All randomness
is a function of the independent seeds of `seedLaw`. The probability is the measure of the
success set (which is measurable by the measurability fields of `Learner` and `Adversary`). -/
noncomputable def succProb {d M T : ℕ} {κ : ℝ} (alg : Learner d M T) (adv : Adversary d M T κ)
    (ε : ℝ) : ENNReal :=
  seedLaw d T {s | ‖estimate alg adv s - s.1‖ ≤ ε}

/-- A learner **recovers `x⋆` to accuracy `ε` with probability at least `1/3` against every
adaptive κ-conditioned adversary** (the hypothesis of Theorem 1, p.3). -/
def SucceedsAgainstAll {d M T : ℕ} (alg : Learner d M T) (κ ε : ℝ) : Prop :=
  ∀ adv : Adversary d M T κ, (1 / 3 : ENNReal) ≤ succProb alg adv ε

end IllCondRegMem


