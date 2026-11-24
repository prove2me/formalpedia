-- Prove2me | Definitions.Def_SRAudit_TwoPhase_Supplement_Heterogeneous
-- name    : SRAudit_TwoPhase_Supplement_Heterogeneous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:24:08.486813+00:00
-- url     : https://prove2.me/theorems/195f3806-908c-483e-84dd-6d0bd5148f87
-- title:
--   Appendix F, OA-29 — tier-dependent penalties z1, z2: ζ(γ), V*, optimal policies and the ar/pp-restricted value
-- statement:
--   Appendix F: the buyer pays $z_1\ge0$ for an exposed violation at a tier-1 supplier and $z_2\ge0$ at a tier-2 supplier; all else is the base model ($a,r\ge0$, $u\in(0,1)$, $w\in(0,1]$). Then
--   $$\zeta(\gamma)=|U_\gamma\cap S(1)|\,uwz_1+|U_\gamma\cap S(2)|\,uwz_2,$$
--   $\widetilde V^*(\gamma,\mathrm{pp})=\pi(\gamma)-\zeta(\gamma)$, and $V^*$, $\widetilde V^*$, optimal policies and the $\mathrm{ar}/\mathrm{pp}$-restricted value are those of the auditing MDP with $p=u$, $c=ur$.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-29, Appendix F

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP

/-! Appendix F (OA-29): the auditing model with tier-dependent penalties `z1` (tier 1) and `z2`
(tier 2). Network, states, actions and transitions are those of the base model. -/

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

/-- Auditing parameters of Appendix F: audit cost `a`, rectification cost `r`, probability of
noncompliance `u`, exposure probability `w`, and penalties `z1`, `z2` per exposed noncompliant
supplier in tier 1 and tier 2. -/
structure ParamsF where
  a : ℝ
  r : ℝ
  u : ℝ
  w : ℝ
  z1 : ℝ
  z2 : ℝ

/-- Standing assumptions (pp. 9–10 and OA-29): `a, r ≥ 0`, `u ∈ (0,1)`, `w ∈ (0,1]`, `z1, z2 ≥ 0`. -/
def ParamsF.Standing (P : ParamsF) : Prop :=
  0 ≤ P.a ∧ 0 ≤ P.r ∧ 0 < P.u ∧ P.u < 1 ∧ 0 < P.w ∧ P.w ≤ 1 ∧ 0 ≤ P.z1 ∧ 0 ≤ P.z2

variable {ι : Type} [DecidableEq ι]

/-- Supplier `i` is in tier 1 (`i ∈ S(1)`). -/
def IsTier1 : Supplier ι → Prop
  | .t1 _ => True
  | .t2 _ => False

instance : DecidablePred (IsTier1 (ι := ι)) := fun i => by cases i <;> simp [IsTier1] <;> infer_instance

/-- The penalty `z_k` of the tier `k` of supplier `i`. -/
def ParamsF.zOf (P : ParamsF) : Supplier ι → ℝ
  | .t1 _ => P.z1
  | .t2 _ => P.z2

/-- `ζ(γ) = |U_γ ∩ S(1)| u w z1 + |U_γ ∩ S(2)| u w z2` (OA-29). -/
def zetaF (P : ParamsF) (γ : State ι) : ℝ :=
  (γ.U.filter IsTier1).card * (P.u * P.w * P.z1) +
    (γ.U.filter (fun i => ¬ IsTier1 i)).card * (P.u * P.w * P.z2)

/-- `Ṽ*(γ, pp) = π(γ) − ζ(γ)` in Appendix F. -/
def ppValueF (P : ParamsF) (π : Network ι → ℝ) (γ : State ι) : ℝ := π γ.g - zetaF P γ

/-- `V*` of Appendix F: the recursion (1)–(5) with the penalty `ζ` above. -/
noncomputable def VstarF (P : ParamsF) (π : Network ι → ℝ) : State ι → ℝ :=
  Vgen P.a (P.u * P.r) P.u (ppValueF P π)

/-- `Ṽ*(γ, x)` of Appendix F. -/
noncomputable def QstarF (P : ParamsF) (π : Network ι → ℝ) : State ι → Action ι → ℝ :=
  Qgen P.a (P.u * P.r) P.u (ppValueF P π)

/-- An optimal auditing policy of Appendix F (argmax at every state). -/
def IsOptimalF (P : ParamsF) (π : Network ι → ℝ) (ξ : Policy ι) : Prop :=
  IsOptimalGen P.a (P.u * P.r) P.u (ppValueF P π) ξ

/-- `V*` of Appendix F when the buyer's actions are limited to `ar` and `pp` (Proposition F.1). -/
noncomputable def VarF (P : ParamsF) (π : Network ι → ℝ) : State ι → ℝ :=
  Vargen P.a (P.u * P.r) (ppValueF P π)

/-- Action values of the `ar`/`pp`-restricted problem of Appendix F. -/
noncomputable def QarF (P : ParamsF) (π : Network ι → ℝ) : State ι → Action ι → ℝ :=
  Qargen P.a (P.u * P.r) (ppValueF P π)

end SRAudit.TwoPhase.Supplement


