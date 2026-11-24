-- Prove2me | Definitions.Def_SRAudit_TwoPhase_Supplement_LVUS
-- name    : SRAudit_TwoPhase_Supplement_LVUS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:22:54.699377+00:00
-- url     : https://prove2.me/theorems/7f2cf647-5a87-4f22-b568-d3173175f3e6
-- title:
--   p. 10 ∇, Definition 1, OA-11 rp and R+, Definition D.1, Assumptions D.1–D.2, Condition 1 — production value, LVUS, reachable states, symmetry and the decreasing-differences assumptions
-- statement:
--   Objects of §5.2 and Appendix D.2 for a production profit $\pi$ (a function of the network) and the published base auditing model.
--
--   1. **Production value** (p. 10): $\nabla(\gamma,i)=\pi(\gamma)-\pi(\gamma\ominus i)$.
--   2. **LVUS** (Definition 1): $i\in U_\gamma$ with $\nabla(\gamma,i)\le\nabla(\gamma,i')$ for every $i'\in U_\gamma$.
--   3. **Value of rp** (OA-11): $\widetilde V^*(\gamma,\mathrm{rp})=\pi(\gamma)-c_{rp}|U_\gamma|$, $c_{rp}=(uwz)\wedge(a+ur)$.
--   4. **Reachable states** $R^+(\gamma)$ (OA-11): the states reached from $\gamma$, including $\gamma$, through finitely many transitions $\gamma\mapsto\gamma\oplus i$ or $\gamma\mapsto\gamma\ominus i$ with $i\in U_\gamma$.
--   5. **Symmetry** (Definition D.1): unaudited $i,i'$ are symmetric if both are tier-2 suppliers of the same class $S_a$, $S_b$ or $S_{ab}$, or, when $|S_a|=|S_b|$ and $|S_a\cap U|=|S_b\cap U|$, one lies in $S_a$ and the other in $S_b$, or they are the two tier-1 firms.
--   6. **Assumption D.1** (D.34): for every $\gamma\in\Gamma$ and $i,i'\in U_\gamma$ with $i'\notin D_\gamma(i)$, $\nabla(\gamma,i')\le\nabla(\gamma\ominus i,i')$.
--   7. **Assumption D.2** (D.35): if $i$ is an LVUS in $\gamma$, $i'\in U_\gamma$ is not symmetric with $i$ and $i\notin D_\gamma(i')$, then $\nabla(\gamma\ominus i',i)\le\nabla(\gamma\ominus i',i'')$ for all $i''\in U_{\gamma\ominus i'}$.
--   8. **Condition 1** (15): for every $\gamma\in\Gamma\setminus\{\gamma_1\}$ with every tier-1 firm vetted and distinct $i,i'\in U_\gamma$, $\nabla(\gamma,i')\le\nabla(\gamma\ominus i,i')$.
--
--   **Formalization Note** $\Gamma$ is the set of states with a well-formed network. The symmetry relation is read symmetrically in $i,i'$ (the page lists the pairs $(S_a,S_b)$ and $(a,b)$ in one order). Condition 1 is read for distinct $i,i'$: for $i=i'$ the right side is $\nabla(\gamma\ominus i,i)=0$ and the condition would fail for every profit that increases with suppliers. Reachability through any chain of transitions equals reachability under some policy, because $|U|$ strictly decreases along a chain.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), p. 10, p. 21 (Condition 1, fn. 9), p. 22 (Definition 1); OA-11 (rp, R+), OA-14 (Assumptions D.1, D.2, Definition D.1)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_Networks

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

variable {ι : Type} [DecidableEq ι]

/-- The production value of supplier `i` at state `γ` (p. 10): `∇(γ, i) = π(γ) − π(γ ⊖ i)`. -/
def nabla (π : Network ι → ℝ) (γ : State ι) (i : Supplier ι) : ℝ := π γ.g - π (drop γ i).g

/-- Definition 1 (p. 22): `i ∈ U_γ` is a least valuable unaudited supplier (LVUS) in `γ`. -/
def IsLVUS (π : Network ι → ℝ) (γ : State ι) (i : Supplier ι) : Prop :=
  i ∈ γ.U ∧ ∀ i' ∈ γ.U, nabla π γ i ≤ nabla π γ i'

/-- The value of the shorthand action `rp` (OA-11): `Ṽ*(γ, rp) = π(γ) − c_rp |U_γ|`. -/
def rpValue (P : Params) (π : Network ι → ℝ) (γ : State ι) : ℝ := π γ.g - crp P * γ.U.card

/-- One transition with positive probability under some admissible action: `γ' = γ ⊕ i` or
`γ' = γ ⊖ i` for some `i ∈ U_γ`. -/
def Step (γ γ' : State ι) : Prop := ∃ i ∈ γ.U, γ' = vet γ i ∨ γ' = drop γ i

/-- `γ' ∈ R+(γ)` (OA-11): `γ'` is reached from `γ` (including `γ` itself) with positive probability
under some policy, i.e. through a finite chain of transitions. -/
def Reach (γ γ' : State ι) : Prop := Relation.ReflTransGen Step γ γ'

/-- Definition D.1 (OA-14): unaudited `i, i'` are symmetric in `γ` if (1) both are tier-2 suppliers of
the same class `Sa`, `Sb` or `Sab`; or (2) when `|Sa| = |Sb|` and `|Sa ∩ U| = |Sb ∩ U|`, one is in `Sa` and
the other in `Sb`, or they are the two tier-1 firms (the relation is read symmetrically in `i, i'`). -/
def Symmetric (γ : State ι) (i i' : Supplier ι) : Prop :=
  i ∈ γ.U ∧ i' ∈ γ.U ∧
  ((∃ j j' : ι, i = .t2 j ∧ i' = .t2 j' ∧
      ((j ∈ γ.g.Sa ∧ j' ∈ γ.g.Sa) ∨ (j ∈ γ.g.Sb ∧ j' ∈ γ.g.Sb) ∨
        (j ∈ γ.g.Sab ∧ j' ∈ γ.g.Sab))) ∨
   (γ.g.Sa.card = γ.g.Sb.card ∧
     (γ.g.Sa.filter (fun j => Supplier.t2 j ∈ γ.U)).card =
       (γ.g.Sb.filter (fun j => Supplier.t2 j ∈ γ.U)).card ∧
     ((∃ j j' : ι, i = .t2 j ∧ i' = .t2 j' ∧
        ((j ∈ γ.g.Sa ∧ j' ∈ γ.g.Sb) ∨ (j ∈ γ.g.Sb ∧ j' ∈ γ.g.Sa))) ∨
      (i = .t1 .a ∧ i' = .t1 .b) ∨ (i = .t1 .b ∧ i' = .t1 .a))))

/-- Assumption D.1 (OA-14, (D.34)), on every state of `Γ`: for `i, i' ∈ U_γ` with `i' ∉ D_γ(i)`,
`∇(γ, i') ≤ ∇(γ ⊖ i, i')`. -/
def AssumptionD1 (π : Network ι → ℝ) : Prop :=
  ∀ γ : State ι, WellFormedState γ → ∀ i ∈ γ.U, ∀ i' ∈ γ.U, i' ∉ γ.g.dependents i →
    nabla π γ i' ≤ nabla π (drop γ i) i'

/-- Assumption D.2 (OA-14, (D.35)), on every state of `Γ`: if `i` is an LVUS in `γ`, `i' ∈ U_γ` is not
symmetric with `i`, and `i ∉ D_γ(i')`, then `∇(γ ⊖ i', i) ≤ ∇(γ ⊖ i', i'')` for all `i'' ∈ U_{γ⊖i'}`. -/
def AssumptionD2 (π : Network ι → ℝ) : Prop :=
  ∀ γ : State ι, WellFormedState γ → ∀ i, IsLVUS π γ i → ∀ i' ∈ γ.U, ¬ Symmetric γ i' i →
    i ∉ γ.g.dependents i' → ∀ i'' ∈ (drop γ i').U, nabla π (drop γ i') i ≤ nabla π (drop γ i') i''

/-- Condition 1 (p. 21, (15)): for every state `γ ∈ Γ \ {γ1}` in which every tier-1 firm is vetted and
any two distinct `i, i' ∈ U_γ`, `∇(γ, i') ≤ ∇(γ ⊖ i, i')`. -/
def Condition1 (π : Network ι → ℝ) : Prop :=
  ∀ γ : State ι, WellFormedState γ → Tier1Vetted γ → ¬ IsGamma1 γ →
    ∀ i ∈ γ.U, ∀ i' ∈ γ.U, i ≠ i' → nabla π γ i' ≤ nabla π (drop γ i) i'

end SRAudit.TwoPhase.Supplement


