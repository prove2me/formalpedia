-- Prove2me | Definitions.Def_GapAgnosticGS_vgttStopProb
-- name    : GapAgnosticGS_vgttStopProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:40.71277+00:00
-- url     : https://prove2.me/theorems/e4b985bd-259d-45f3-b9a1-1dc1390e9ee2
-- title:
--   Stopping probabilities of the branches of VGTT
-- statement:
--   For an environment, a family of threshold tests and arm $j$, run Algorithm 2 on $|\phi_j\rangle_I$. Branch $j$ **stops after stage $r$** if $C_r$ is the first flag set to $1$, or, for the last stage $r=m$, if none of $C_1,\dots,C_{m-1}$ is set. The stopping probability is the squared norm of the corresponding component of the output.
--
--   These are the probabilities $p_1,\dots,p_m$ of the stopping times $t_1,\dots,t_m$ in the variable-time framework (Theorem A.4), used to define $t_{\rm avg}$ in Lemma A.5. Since Algorithm 2 acts on $I$ only, branch $j$ of an input $\sum_j c_j|\zeta_j\rangle_R|\phi_j\rangle_I$ stops with these probabilities.
--
--   **Formalization Note** Stages are 0-based; with unitary tests the probabilities sum to $1$.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma A.5, p.29 (PDF p.30); Theorem A.4 and Eq. (26), p.28 (PDF p.29); §A.3, p.28 (PDF p.29)

import Definitions.Def_GapAgnosticGS_HidEnv
import Definitions.Def_GapAgnosticGS_vgtt
import Definitions.Def_GapAgnosticGS_vgttInit
open QAlgorithms

namespace GapAgnosticGS

open Classical in
/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma A.5, p.29 (PDF p.30), and Theorem A.4, p.28 (PDF p.29): "stopping times
t_1, t_2, …, t_m and probabilities p_1, p_2, …, p_m of stopping at each respective time"; §A.3:
"Algorithm 2 stops at different times for each branch". The probability that branch `j` (input
`|ϕ_j⟩_I`) of Algorithm 2 stops after stage `r`: the squared norm of the component of the output
in which `C_r` is the first flag set to `1`, or, for the last stage, in which no earlier flag is
set (a branch that is never rejected runs all `m` stages).

**Formalization Note.** Stages are 0-based (`r = m − 1` is the last). Since each stage is
controlled on the earlier flags being `0`, at most one flag is set, and for unitary tests these
probabilities sum to `1`. Branch `j` of an input `Σ_j c_j |ζ_j⟩_R|ϕ_j⟩_I` (Algorithm 2 acts on
`I`, leaving the reference `R` untouched) has exactly these stopping probabilities. -/
noncomputable def vgttStopProb {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) {P : Type} [Fintype P] [DecidableEq P]
    (gtt : ℝ → ℝ → Matrix ((Fin n × A) × Bool × P) ((Fin n × A) × Bool × P) ℂ) (m : ℕ)
    (ℓ₁ : ℝ) (p₀ : P) (j : Fin n) (r : Fin m) : ℝ :=
  ∑ x : (Fin n × A) × (Fin m → Bool × P) × Bool × Bool,
    if (∀ i : Fin m, i < r → (x.2.1 i).1 = false) ∧ ((r : ℕ) + 1 = m ∨ (x.2.1 r).1 = true) then
      ‖act (vgtt Env.E gtt m ℓ₁) (vgttInit m a₀ p₀ (Env.φ j)) x‖ ^ 2
    else 0

end GapAgnosticGS


