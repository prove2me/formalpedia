-- Prove2me | Definitions.Def_GaussProcSparsify_Optimal_Gaussian
-- name    : GaussProcSparsify_Optimal_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:50:58.238556+00:00
-- url     : https://prove2.me/theorems/87de7ced-170a-4338-89db-254a00851929
-- title:
--   Canonical Gaussian process and Gaussian width
-- statement:
--   Let $E_n=\mathbb R^n$ with its Euclidean inner product, and let $\gamma_n=N(0,I_n)$ be its standard Gaussian probability measure. The canonical process on $T\subseteq E_n$ is $X_t(g)=\langle g,t\rangle$. For nonempty bounded $T$, its sample supremum and Gaussian width are
--   $$M_T(g)=\sup_{t\in T}\langle g,t\rangle,\qquad w(T)=\mathbb E_{\gamma_n} M_T(g).$$
--   The width is represented in extended reals by the published expected-supremum definition: the supremum of $\mathbb E\max_{t\in T_0}X_t$ over finite nonempty $T_0\subseteq T$. This also represents $w(T)=+\infty$ for unbounded nonempty $T$. No measurability or integrability assumption is bundled into the definition. On nonempty bounded sets the finite-marginal convention equals the displayed expectation by continuity in the index and Gaussian integrability.
--
--   For nonempty finite $S$ and real shifts $c_s$, the shifted maximum is $F_{S,c}(g)=\max_{s\in S}(\langle g,s\rangle+c_s)$. This module supplies the common objects for the width milestone and the goal. The real sample supremum is used only for bounded nonempty sets; its total-function default outside that domain is not an extended supremum.
-- source:
--   Shivam Nadimpalli, Optimal Sparsification of Gaussian Processes, STOC 2027 submission #163 (October 2026), §1, PDF p. 2 (printed p. 1); §2.1–2.2, PDF pp. 12–13 (printed pp. 11–12); Theorem 1, PDF p. 3 (printed p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/163.pdf

import Mathlib
import Definitions.Def_HighDimProb_RandomProcesses_ProcessESup

open MeasureTheory ProbabilityTheory

namespace GaussProcSparsify.Optimal

/-- Euclidean R^n, including dimension zero; §2, PDF p. 12. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The standard Gaussian law γ_n of §2.1, PDF p. 12. -/
noncomputable def gaussian (n : ℕ) : Measure (Vec n) := stdGaussian (Vec n)

/-- Canonical sample supremum; used only on bounded nonempty sets. PDF pp. 2, 13. -/
noncomputable def processSup {n : ℕ} (T : Set (Vec n)) (g : Vec n) : ℝ :=
  sSup ((fun t => inner ℝ g t) '' T)

/-- Gaussian width via finite nonempty marginals (§2.2, PDF p. 13).
For nonempty bounded T this is the finite real expectation of processSup T.
The extended value also represents unbounded sets, without a real-supremum default. -/
noncomputable def gaussianWidth {n : ℕ} (T : Set (Vec n)) : EReal :=
  HighDimProb.RandomProcesses.processESup (gaussian n)
    (fun (t : T) g => inner ℝ g (t : Vec n))

/-- Maximum of the shifted subprocess in Theorem 1, PDF p. 3. -/
noncomputable def shiftedMax {n : ℕ} (S : Finset (Vec n)) (hS : S.Nonempty)
    (c : Vec n → ℝ) (g : Vec n) : ℝ :=
  S.sup' hS (fun s => inner ℝ g s + c s)

end GaussProcSparsify.Optimal


