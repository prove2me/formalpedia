-- Prove2me | Definitions.Def_SRAudit_TwoPhase_Supplement_Inaccurate
-- name    : SRAudit_TwoPhase_Supplement_Inaccurate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:24:42.168875+00:00
-- url     : https://prove2.me/theorems/a3e5a375-62b3-4cc1-8090-424bbafcb79f
-- title:
--   Appendix G, (G.1)–(G.8), (G.43)–(G.44), OA-37–OA-40 — inaccurate audits: û, ζ, V*, policy values, ĉrp and the rp value
-- statement:
--   Appendix G: an audit detects an existing noncompliance with probability $d\in[0,1]$. A supplier that passed an audit, or was rectified, is still noncompliant with probability
--   $$\hat u=\frac{u(1-d)}{(1-u)+u(1-d)}\qquad\text{(G.1)}.$$
--   Let $C$ be a set of suppliers that are perfectly compliant once vetted ($\hat S_g=S_g\setminus C$ are the others; $C=\emptyset$ in §G.1, $C=S(1)$ in §G.2). Then
--   $$\zeta(\gamma)=wz\bigl(\hat u\,|(S_g\setminus U)\setminus C|+u|U|\bigr)\qquad\text{((G.2), (G.44))},$$
--   an audit fails with probability $ud$, an $\mathrm{ar}$ action costs $a+udr$ in expectation ((G.3)–(G.8)), and $V^*$, $\widetilde V^*$, optimal policies, policy values $V(\xi,\gamma)$ and the $\mathrm{ar}/\mathrm{pp}$-restricted value are those of the auditing MDP with $p=ud$, $c=udr$, $T=\pi-\zeta$. Further $\hat c_{rp}=(a+udr)\wedge[(u-\hat u)wz]$ and $\widetilde V^*(\gamma,\mathrm{rp})=\pi(\gamma)-\hat uwz|\hat S_g|-\hat c_{rp}|U_\gamma|$ ((G.43)–(G.44)).
--
--   **Formalization Note** Unaudited suppliers are charged probability $u$; the set $C$ only removes the residual penalty $\hat u$ of vetted suppliers in $C$.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), OA-37 (G.1)–(G.8), OA-40 (ĉrp, (G.43), (G.44))

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP

/-! Appendix G (OA-37): audits detect an existing noncompliance only with probability `d`. A supplier
that passed an audit, or was rectified, is still noncompliant with probability `û` (G.1). The set `C`
collects the suppliers that are perfectly compliant once vetted (`S_g \ Ŝ_g` of OA-40); `C = ∅` is
the model of §G.1. -/

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

/-- Standing assumptions of Appendix G: the base ones and `d ∈ [0, 1]`. -/
def StandingG (P : Params) (d : ℝ) : Prop := P.Standing ∧ 0 ≤ d ∧ d ≤ 1

/-- `û = u(1 − d) / ((1 − u) + u(1 − d))` (G.1). -/
noncomputable def uhat (P : Params) (d : ℝ) : ℝ := P.u * (1 - d) / ((1 - P.u) + P.u * (1 - d))

/-- `ĉ_rp = (a + udr) ∧ [(u − û) w z]` (OA-40). -/
noncomputable def crpHat (P : Params) (d : ℝ) : ℝ :=
  min (P.a + P.u * d * P.r) ((P.u - uhat P d) * P.w * P.z)

variable {ι : Type} [DecidableEq ι]

/-- `ζ(γ) = w z (û |Ŝ_g \ U| + u |U|)` ((G.2), (G.44)): each vetted supplier outside `C` is noncompliant
with probability `û`, each unaudited supplier with probability `u`. -/
noncomputable def zetaG (P : Params) (d : ℝ) (C : Finset (Supplier ι)) (γ : State ι) : ℝ :=
  P.w * P.z * (uhat P d * ((γ.g.suppliers \ γ.U) \ C).card + P.u * γ.U.card)

/-- `Ṽ*(γ, pp) = π(γ) − ζ(γ)` in Appendix G. -/
noncomputable def ppValueG (P : Params) (d : ℝ) (C : Finset (Supplier ι)) (π : Network ι → ℝ)
    (γ : State ι) : ℝ :=
  π γ.g - zetaG P d C γ

/-- `V*` of Appendix G: (1), (2) with (G.2), (G.6)–(G.8) (failure probability `ud`, expected
rectification cost `udr`). -/
noncomputable def VstarG (P : Params) (d : ℝ) (C : Finset (Supplier ι)) (π : Network ι → ℝ) :
    State ι → ℝ :=
  Vgen P.a (P.u * d * P.r) (P.u * d) (ppValueG P d C π)

/-- `Ṽ*(γ, x)` of Appendix G. -/
noncomputable def QstarG (P : Params) (d : ℝ) (C : Finset (Supplier ι)) (π : Network ι → ℝ) :
    State ι → Action ι → ℝ :=
  Qgen P.a (P.u * d * P.r) (P.u * d) (ppValueG P d C π)

/-- An optimal auditing policy of Appendix G. -/
def IsOptimalG (P : Params) (d : ℝ) (C : Finset (Supplier ι)) (π : Network ι → ℝ)
    (ξ : Policy ι) : Prop :=
  IsOptimalGen P.a (P.u * d * P.r) (P.u * d) (ppValueG P d C π) ξ

/-- `V(ξ, γ)` of Appendix G ((D.1), (G.3)–(G.5)). -/
noncomputable def VpolG (P : Params) (d : ℝ) (C : Finset (Supplier ι)) (π : Network ι → ℝ)
    (ξ : Policy ι) : State ι → ℝ :=
  Vpolgen P.a (P.u * d * P.r) (P.u * d) (ppValueG P d C π) ξ

/-- `V*` of Appendix G with the actions limited to `ar` and `pp` (Proposition G.2). -/
noncomputable def VarG (P : Params) (d : ℝ) (C : Finset (Supplier ι)) (π : Network ι → ℝ) :
    State ι → ℝ :=
  Vargen P.a (P.u * d * P.r) (ppValueG P d C π)

/-- Action values of the `ar`/`pp`-restricted problem of Appendix G. -/
noncomputable def QarG (P : Params) (d : ℝ) (C : Finset (Supplier ι)) (π : Network ι → ℝ) :
    State ι → Action ι → ℝ :=
  Qargen P.a (P.u * d * P.r) (ppValueG P d C π)

/-- `Ṽ*(γ, rp) = π(γ) − û w z |Ŝ_g| − ĉ_rp |U_γ|` ((G.43)–(G.44)), with `Ŝ_g = S_g \ C`. -/
noncomputable def rpValueG (P : Params) (d : ℝ) (C : Finset (Supplier ι)) (π : Network ι → ℝ)
    (γ : State ι) : ℝ :=
  π γ.g - uhat P d * P.w * P.z * (γ.g.suppliers \ C).card - crpHat P d * γ.U.card

/-- The tier-1 firms, perfectly compliant once vetted in §G.2 (OA-40). -/
def tier1Set : Finset (Supplier ι) := Finset.univ.image Supplier.t1

end SRAudit.TwoPhase.Supplement


