-- Prove2me | Definitions.Def_GapAgnosticGS_armComplexity
-- name    : GapAgnosticGS_armComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:46.941725+00:00
-- url     : https://prove2.me/theorems/16b09f12-ff51-4502-b92c-1119cf5d1160
-- title:
--   Gap complexity $\Gamma=\sum_{j\ne j_\star}(p_\star-p_j)^{-2}$
-- statement:
--   For a hidden-basis environment with a unique best arm $j_\star$, the **gap complexity** is
--
--   $$\Gamma:=\sum_{j\ne j_\star}\frac{1}{(p_\star-p_j)^2}.$$
--
--   It charges every arm by the inverse square of its distance to the best reward and governs the $\widetilde O(\sqrt\Gamma)$ query bounds of Lemma 3.7 and Theorems 3.8 and 3.10.
--
--   **Formalization Note** The sum is over the arms with $p_j<p_\star$; under a unique best arm these are exactly the arms $j\ne j_\star$.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.4 (PDF p.5); Lemma 3.7, p.12 (PDF p.13): "Γ = Σ_{j≠j⋆} 1/(p⋆ − p_j)²"

import Definitions.Def_GapAgnosticGS_pStar

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.4 (PDF p.5): "Γ := Σ_{j≠j⋆} 1/(p_{j⋆} − p_j)²"; Lemma 3.7, p.12 (PDF p.13):
"Γ = Σ_{j≠j⋆} 1/(p⋆ − p_j)²". The gap-dependent instance complexity of the bandit.

**Formalization Note.** The sum is over the arms whose reward is below `p⋆`. When the best arm
`j⋆` is unique (the only case in which the paper uses `Γ`), these are exactly the arms `j ≠ j⋆`,
and every denominator is positive. -/
noncomputable def armComplexity {n : ℕ} {A : Type} [Fintype A] [DecidableEq A] {a₀ : A}
    {Prj : Matrix A A ℂ} (Env : HidEnv n A a₀ Prj) : ℝ :=
  ∑ j : Fin n, if reward Env j < pStar Env then 1 / (pStar Env - reward Env j) ^ 2 else 0

end GapAgnosticGS


