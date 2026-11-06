-- Prove2me | Definitions.Def_BianchiIX_Dynamics_FlowComposition
-- name    : BianchiIX_Dynamics_FlowComposition
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T22:15:32.99665+00:00
-- url     : https://prove2.me/theorems/e2691f4c-602c-4cb8-9257-9cd36db11542
-- title:
--   Retiming and rebasing a normalized solution
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Let $X=\mathbb R^5$ with coordinates $x=(p,s,a,b,c)$ and the sup norm. Write
--   $$F(x)=(P,Q,r_1a,r_2b,r_3c),\qquad \mathcal C(x)=C(p,s,a,b,c),$$
--   and let $W=\{(p,s,a,b,c)\in X:a>0,\ b>0,\ c>0\}$.
--
--   Write $N_1(x)=a$, $N_2(x)=b$, and $N_3(x)=c$. For initial data $(x_0,t_0)$,
--   let $I_{\max}(x_0,t_0)$ be the union of all open convex domains of solutions
--   with these initial data, and let $\alpha_{x_0,t_0}$ be their compatible curve.
--   A solution $S$ has such a domain $I_S$, a curve $\alpha_S$, and
--   $\alpha_S(t_0)=x_0$.
--
--   Retiming a solution $S$ from $t_0$ to $t_1$ gives the curve
--   $t\mapsto\alpha_S(t+t_0-t_1)$ on
--   $\{t:t+t_0-t_1\in I_S\}$, with the same initial state.
--   For $s\in I_S$, rebasing $S$ at $s$ retains its curve and domain and
--   uses the initial data $(\alpha_S(s),s)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/FlowComposition.lean

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- Translate the initial time of a solution of the autonomous equation. -/
def NormalizedSolution.retime {x : NormalizedState} {t₀ : ℝ}
    (S : NormalizedSolution x t₀) (t₁ : ℝ) : NormalizedSolution x t₁ where
  domain := (fun t => t + t₀ - t₁) ⁻¹' S.domain
  isOpen_domain := S.isOpen_domain.preimage (by fun_prop)
  convex_domain := convex_iff_ordConnected.mpr
    (S.convex_domain.ordConnected.preimage_mono (fun a b hab => by linarith))
  initial_mem := by simpa using S.initial_mem
  curve := fun t => S.curve (t + t₀ - t₁)
  initial_eq := by simpa using S.initial_eq
  hasDerivAt := by
    intro t ht
    convert! (S.hasDerivAt (t + t₀ - t₁) ht).scomp t
      (((hasDerivAt_id t).add_const t₀).sub_const t₁) using 1
    simp





def NormalizedSolution.rebase {x : NormalizedState} {t₀ s : ℝ}
    (S : NormalizedSolution x t₀) (hs : s ∈ S.domain) : NormalizedSolution (S.curve s) s :=
  ⟨S.domain, S.isOpen_domain, S.convex_domain, hs, S.curve, rfl, S.hasDerivAt⟩







end BianchiIX


