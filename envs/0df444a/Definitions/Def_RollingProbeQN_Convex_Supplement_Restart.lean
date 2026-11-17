-- Prove2me | Definitions.Def_RollingProbeQN_Convex_Supplement_Restart
-- name    : RollingProbeQN_Convex_Supplement_Restart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:44:41.6446+00:00
-- url     : https://prove2.me/theorems/5d87638d-69b9-4d1d-b955-67a6023161d8
-- title:
--   The restart scheme of Appendix G.1 built on Algorithm 1
-- statement:
--   The **restart scheme** runs Algorithm 1 (RP-QNPE) in stages $s=0,\dots,S-1$ with
--   $$S=\max\Big\{0,\Big\lceil\log_2\big(R\sqrt{L_1/(2\varepsilon)}\big)\Big\rceil\Big\}.$$
--   Stage $s$ starts from $w_s$ ($w_0=x_0$) with $R_s=2^{-s}R$, $\varepsilon_s=\mu R_s^2/8$ and $b=L_2R_s$ in place of $R$, $\varepsilon$ and $b$, with $A_0=0$ and a fresh model; it stops at its first return (a zero gradient, or $A_{k+1}\ge R_s^2/(2\varepsilon_s)=4/\mu$), and its returned point is $w_{s+1}$. The scheme's queries are the concatenation of the stages' oracle queries, each stage counted up to and including its first return and starting with its initial query at $w_s$.
--
--   This is the scheme whose guarantee is Theorem G.1.
--
--   **Formalization Note** Each stage is the published run of Algorithm 1 with the published return rule `epsReturns`, returned point `epsOutput` and query list `allQueries`. The first return is the least index at which `epsReturns` holds; if a run never returned this would be $0$, and Theorem G.1 asserts that every stage returns.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Appendix G.1, p. 63; Appendix G.3, p. 65

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_Config
import Definitions.Def_RollingProbeQN_Convex_epsReturns
import Definitions.Def_RollingProbeQN_Convex_epsOutput
import Definitions.Def_RollingProbeQN_Convex_allQueries

namespace RollingProbeQN.Convex.Supplement

/-- **The first return of a run of Algorithm 1.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Algorithm 1, p. 9 (Steps 1 and 5), as used
by each stage of the restart scheme of Appendix G.1, p. 63.

`firstReturn cfg G w R ε` is the least `k` at which the published `epsReturns cfg G w R ε k` holds.

**Formalization Note.** When the run never returns this is `sInf ∅ = 0`, a value no statement uses
without first asserting that a return exists (Theorem G.1 asserts it for every stage). -/
noncomputable def firstReturn {d χ : ℕ} (cfg : Config d χ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (w : EuclideanSpace ℝ (Fin d))
    (R ε : ℝ) : ℕ :=
  sInf {k : ℕ | epsReturns cfg G w R ε k}

/-- **The number of stages `S` of the restart scheme.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Appendix G.1, p. 63: "The number of stages
is `S = max{0, ⌈log2(R√(L1/(2ε)))⌉}`".

**Formalization Note.** `⌈t⌉₊` is `max{0, ⌈t⌉}` for real `t`. -/
noncomputable def restartStages (L₁ R ε : ℝ) : ℕ :=
  ⌈Real.logb 2 (R * Real.sqrt (L₁ / (2 * ε)))⌉₊

/-- **The restart points `w_s` of the restart scheme.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Appendix G.1, p. 63: "The restart scheme runs
Algorithm 1 in stages `s = 0, . . . , S − 1`. Stage `s` starts from `ws`, with `w0 = x0`, uses
`Rs = 2^{−s}R`, `εs = μR²s/8` and `b = L2Rs` wherever the convex method uses `R`, `ε` and `b`, starts
with `A0 = 0` and a fresh model (`M−1 = 0`), and returns `ws+1` once `Ak+1 ≥ 4/μ`."

`restartPt cfg R μ G x₀ s` is `w_s`: stage `s` is the published run of Algorithm 1 from `w_s` with the
configuration `cfg` whose allowance is replaced by `b = L₂R_s`, stopped at its first return for
`(R_s, ε_s)` (mass target `R_s²/(2ε_s) = 4/μ`), and `w_{s+1}` is the published `epsOutput` there.

**Formalization Note.** The field `cfg.b` is not used: every stage sets its own `b = cfg.L₂ · R_s`. A
stage also returns at a zero gradient (Step 1 of Algorithm 1), as the paper's run does. -/
noncomputable def restartPt {d χ : ℕ} (cfg : Config d χ) (R μ : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d)) :
    ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => x₀
  | s + 1 =>
    epsOutput { cfg with b := cfg.L₂ * (R / 2 ^ s) } G (restartPt cfg R μ G x₀ s)
      (firstReturn { cfg with b := cfg.L₂ * (R / 2 ^ s) } G (restartPt cfg R μ G x₀ s)
        (R / 2 ^ s) (μ * (R / 2 ^ s) ^ 2 / 8))

/-- **All oracle queries of the first `S` stages of the restart scheme.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Appendix G.3, p. 65: "Summing `Gs` over
`s < S`", `Gs` the number of gradient queries of stage `s`.

The concatenation over `s < S` of the published `allQueries` of stage `s` up to and including its first
return `k_s`, i.e. `allQueries cfg_s G w_s (k_s + 1)`; each includes the stage's initial query at `w_s`.

**Formalization Note.** Reading R4 of the base mission: a stage's count includes its initial query. -/
noncomputable def restartQueries {d χ : ℕ} (cfg : Config d χ) (R μ : ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x₀ : EuclideanSpace ℝ (Fin d))
    (S : ℕ) : List (EuclideanSpace ℝ (Fin d)) :=
  (List.range S).flatMap (fun s =>
    allQueries { cfg with b := cfg.L₂ * (R / 2 ^ s) } G (restartPt cfg R μ G x₀ s)
      (firstReturn { cfg with b := cfg.L₂ * (R / 2 ^ s) } G (restartPt cfg R μ G x₀ s)
        (R / 2 ^ s) (μ * (R / 2 ^ s) ^ 2 / 8) + 1))

end RollingProbeQN.Convex.Supplement


