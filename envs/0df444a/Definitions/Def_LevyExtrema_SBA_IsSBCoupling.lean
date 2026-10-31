-- Prove2me | Definitions.Def_LevyExtrema_SBA_IsSBCoupling
-- name    : LevyExtrema_SBA_IsSBCoupling
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:40:53.168745+00:00
-- url     : https://prove2.me/theorems/99c6c2cd-86ef-4adb-b153-7bc086d3e70c
-- title:
--   The stick-breaking coupling $(X,\ell,Y)$ on $[0,T]$ satisfying (1.1) almost surely
-- statement:
--   Let $X$ be a Lévy process with generating triplet $(\sigma^2,\nu,b)$ and let $T>0$. A **stick-breaking coupling** of $X$ on $[0,T]$ is a pair $(\ell,Y)$ on the same probability space such that
--
--   1. $Y$ is a Lévy process with the same generating triplet as $X$ (so $Y$ has the law of $X$);
--   2. $\ell$ is the uniform stick-breaking process on $[0,T]$ driven by an i.i.d. $\mathrm U(0,1)$ sequence $(V_n)$;
--   3. the path of $Y$ is independent of the sequence $(V_n)$;
--   4. almost surely,
--   $$\chi=(X_T,\overline X_T,\tau_T)=\sum_{k=1}^\infty\Big(Y_{L_{k-1}}-Y_{L_k},(Y_{L_{k-1}}-Y_{L_k})^+,\ell_k\cdot\mathbb 1_{\{Y_{L_{k-1}}-Y_{L_k}>0\}}\Big).\tag{1.1}$$
--
--   The paper constructs such a coupling in its Subsection 4.1 from the faces of the concave majorant of $X$ taken in size-biased order; its existence is the milestone `exists_sbCoupling`.
--
--   **Formalization Note** The coupling is encoded by the four properties above, which are the ones the paper's proofs use. Independence is between the whole path (product σ-algebra on functions $\mathbb R_{\ge0}\to\mathbb R$) and the whole sequence $(V_n)$. The series in (1.1) converges unconditionally (`HasSum`), which in $\mathbb R$ is absolute convergence, as the paper notes on p. 17.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (1.1), p. 2; §4.1, pp. 17–18

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_LevyExtrema_SBA_supTime
import Definitions.Def_LevyExtrema_SBA_StickBreaking
import Definitions.Def_LevyExtrema_SBA_stickSummand

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **The stick-breaking coupling (X, ℓ, Y) on [0, T].**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, (1.1), p. 2, and §4.1, pp. 17–18:
"χ = (X_T, X̄_T, τ_T) = Σ_{k=1}^∞ (Y_{L_{k−1}} − Y_{L_k}, (Y_{L_{k−1}} − Y_{L_k})^+,
ℓ_k · 1{Y_{L_{k−1}}−Y_{L_k}>0}), where the Lévy process Y has the same law as X and is independent
of the stick-breaking process ℓ = (ℓ_n)_{n∈N} on [0, T], based on the uniform law U(0, 1)".

The fields are: the horizon is positive; `X` and `Y` are Lévy processes with the same generating
triplet `Tr` (hence the same law); `V` is a U(0,1)-iid sequence; the path of `Y` is independent of
the sequence `V`; and (1.1) holds almost surely.

**Formalization Note.** The coupling of Subsection 4.1 is encoded by the properties the paper uses,
not by its construction; that such a triple exists (on an extension of the probability space) is
the milestone `LevyExtrema.SBA.exists_sbCoupling`. Independence is between the whole path
`ω ↦ (t ↦ Y_t ω)` (product σ-algebra on `ℝ≥0 → ℝ`) and the whole sequence `ω ↦ (k ↦ V_k ω)`.
(1.1) is a `HasSum` in `ℝ × ℝ × ℝ`, i.e. unconditional (= absolute, in `ℝ`) convergence of each
coordinate; the paper notes (p. 17) that the heights are absolutely summable. -/
structure IsSBCoupling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (Tr : Triplet) (T : ℝ≥0) : Prop where
  pos : 0 < T
  levyX : IsLevyWith P X Tr
  levyY : IsLevyWith P Y Tr
  sticks : IsUniformSticks P V
  indep : IndepFun (fun ω => fun t => Y t ω) (fun ω => fun k => V k ω) P
  rep : ∀ᵐ ω ∂P, HasSum (fun k => stickSummand T Y V k ω)
    (X T ω, runSup (fun s => X s ω) T, ((supTime (fun s => X s ω) T : ℝ≥0) : ℝ))

end LevyExtrema.SBA


