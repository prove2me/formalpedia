-- Prove2me | Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
-- name    : SRAudit_TwoPhase_Supplement_AuditMDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:23:20.478803+00:00
-- url     : https://prove2.me/theorems/9ea8227e-030d-45fe-8d2f-a917b1da72b2
-- title:
--   (1)–(5), (D.1)–(D.4) — the buyer's auditing MDP with audit cost, failure probability, rectification cost and terminal reward as parameters
-- statement:
--   The auditing Markov decision process of §3.2 on the published states $\gamma=(g,U)$ with the published operators $\oplus,\ominus$, written once with four parameters: audit cost $a$, probability $p$ that an audited supplier fails, expected rectification cost $c$ of an $\mathrm{ar}$ action, and a terminal reward $T(\gamma)$ for proceeding to production.
--
--   1. **Optimal value.** $V(\gamma)=T(\gamma)$ if $U_\gamma=\emptyset$, and otherwise
--   $$V(\gamma)=\max\Bigl\{T(\gamma),\ \max_{i\in U_\gamma}\max\{-a-c+V(\gamma\oplus i),\ -a+(1-p)V(\gamma\oplus i)+pV(\gamma\ominus i)\}\Bigr\}.$$
--   2. **Action values** $\widetilde V(\gamma,x)$ for $x=\mathrm{pp},\mathrm{ar}(i),\mathrm{ad}(i)$, and **optimal policies**: admissible $\xi$ with $\xi(\gamma)\in\arg\max_x\widetilde V(\gamma,x)$ at every state.
--   3. **Policy value** $V(\xi,\gamma)$: the same recursion with the action $\xi(\gamma)$ in place of the maximum.
--   4. **Restricted value**: the optimal value when only $\mathrm{ar}$ and $\mathrm{pp}$ are allowed, with its action values.
--
--   With $p=u$, $c=ur$, $T=\pi-\zeta$ this is (1)–(5) and (D.1)–(D.4). Appendix F changes $\zeta$; Appendix G takes $p=ud$, $c=udr$ and changes $\zeta$.
--
--   **Formalization Note** The recursion is well founded because $|U|$ strictly decreases under $\oplus$ and $\ominus$. Action values at inadmissible actions are a junk $0$, and a policy value at an inadmissible action is $T(\gamma)$; they are only used for admissible actions.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), pp. 10–11, (1)–(5); OA-11, (D.1)–(D.4); OA-13 (Proposition D.2's restricted problem)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting

/-!
The buyer's auditing Markov decision process of §3.2 on the states `(g, U)` of the base model, with the
three ingredients the appendices vary left as parameters: the audit cost `a`, the probability `p` that
an audited supplier fails the audit, the expected rectification cost `c` of an `ar` action, and the
terminal reward `term γ` of proceeding to production (`pp`). With `p = u`, `c = ur` and
`term γ = π(γ) − ζ(γ)` this is the recursion (1)–(5); Appendix F changes `ζ`, Appendix G sets
`p = ud`, `c = udr` and changes `ζ`.
-/

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

variable {ι : Type} [DecidableEq ι]

theorem vet_U_card_lt (γ : State ι) (i : Supplier ι) (hi : i ∈ γ.U) :
    (vet γ i).U.card < γ.U.card := by
  simpa [vet] using Finset.card_erase_lt_of_mem hi

theorem drop_U_card_lt (γ : State ι) (i : Supplier ι) (hi : i ∈ γ.U) :
    (drop γ i).U.card < γ.U.card := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (Finset.sdiff_subset)).2
  have hD : i ∈ γ.g.dependents i := by cases i <;> simp [Network.dependents]
  exact ⟨i, hi, by simp [hD]⟩

/-- Optimal value: `V(γ) = max(term γ, max_{i ∈ U} max(−a − c + V(γ ⊕ i),
−a + (1 − p) V(γ ⊕ i) + p V(γ ⊖ i)))`, and `V(γ) = term γ` at terminal states. -/
noncomputable def Vgen (a c p : ℝ) (term : State ι → ℝ) (γ : State ι) : ℝ :=
  if h : γ.U.Nonempty then
    max (term γ)
      (γ.U.attach.sup' (by simpa using h) (fun i =>
        max (-a - c + Vgen a c p term (vet γ i.val))
            (-a + (1 - p) * Vgen a c p term (vet γ i.val) + p * Vgen a c p term (drop γ i.val))))
  else term γ
termination_by γ.U.card
decreasing_by
  all_goals
    first | exact vet_U_card_lt γ i.val i.property | exact drop_U_card_lt γ i.val i.property

/-- `Ṽ*(γ, x)`: the value of action `x` at `γ` followed by an optimal policy (junk `0` for an
inadmissible `ar`/`ad`). -/
noncomputable def Qgen (a c p : ℝ) (term : State ι → ℝ) (γ : State ι) : Action ι → ℝ
  | .pp => term γ
  | .ar i => if i ∈ γ.U then -a - c + Vgen a c p term (vet γ i) else 0
  | .ad i => if i ∈ γ.U then
      -a + (1 - p) * Vgen a c p term (vet γ i) + p * Vgen a c p term (drop γ i) else 0

/-- An optimal auditing policy: admissible, and `ξ(γ) ∈ argmax_{x ∈ X_γ} Ṽ*(γ, x)` at every state. -/
def IsOptimalGen (a c p : ℝ) (term : State ι → ℝ) (ξ : Policy ι) : Prop :=
  IsAdmissible ξ ∧ ∀ γ, Qgen a c p term γ (ξ γ) = Vgen a c p term γ

/-- The value `V(ξ, γ)` of following policy `ξ` from `γ` (junk: `term γ` at an inadmissible action). -/
noncomputable def Vpolgen (a c p : ℝ) (term : State ι → ℝ) (ξ : Policy ι) (γ : State ι) : ℝ :=
  match ξ γ with
  | .pp => term γ
  | .ar i => if i ∈ γ.U then -a - c + Vpolgen a c p term ξ (vet γ i) else term γ
  | .ad i => if i ∈ γ.U then
      -a + (1 - p) * Vpolgen a c p term ξ (vet γ i) + p * Vpolgen a c p term ξ (drop γ i)
      else term γ
termination_by γ.U.card
decreasing_by
  all_goals
    first | exact vet_U_card_lt γ i ‹i ∈ γ.U› | exact drop_U_card_lt γ i ‹i ∈ γ.U›

/-- Optimal value when the buyer's actions are limited to `ar` and `pp`. -/
noncomputable def Vargen (a c : ℝ) (term : State ι → ℝ) (γ : State ι) : ℝ :=
  if h : γ.U.Nonempty then
    max (term γ)
      (γ.U.attach.sup' (by simpa using h) (fun i => -a - c + Vargen a c term (vet γ i.val)))
  else term γ
termination_by γ.U.card
decreasing_by
  exact vet_U_card_lt γ i.val i.property

/-- Action values in the `ar`/`pp`-restricted problem (junk `0` for `ad` and inadmissible `ar`). -/
noncomputable def Qargen (a c : ℝ) (term : State ι → ℝ) (γ : State ι) : Action ι → ℝ
  | .pp => term γ
  | .ar i => if i ∈ γ.U then -a - c + Vargen a c term (vet γ i) else 0
  | .ad _ => 0

end SRAudit.TwoPhase.Supplement


