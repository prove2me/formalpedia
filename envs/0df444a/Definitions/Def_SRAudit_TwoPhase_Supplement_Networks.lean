-- Prove2me | Definitions.Def_SRAudit_TwoPhase_Supplement_Networks
-- name    : SRAudit_TwoPhase_Supplement_Networks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T07:20:42.498177+00:00
-- url     : https://prove2.me/theorems/d7348fa9-d01c-4d60-9f0d-f7271cb4a096
-- title:
--   §3.1, fn. 4, fn. 6, (C.36), fn. 9 — well-formed supply networks, the null network, adding a tier-2 supplier, vetted tier 1, the state γ1
-- statement:
--   Objects on the published three-tier supply networks $g=(S(1),S_a,S_b,S_{ab})$ of the base mission (tier-1 firms $a,b$, tier-2 suppliers labelled by a type $\iota$), used by the production-phase and the LVUS results.
--
--   1. **Well-formed networks (the set $G$).** $g$ is well formed if an absent tier-1 firm has no exclusive suppliers, shared suppliers exist only when both tier-1 firms are present, and every present tier-1 firm $i$ has a supplier: $S_i\cup S_{ab}\neq\emptyset$. These are the networks of the count representation (C.36), and the base operators $\oplus,\ominus$ map well-formed states to well-formed states.
--   2. **Null network.** $g$ is null ($g=g_\emptyset$) if $S(1)=\emptyset$ or $S(2)=\emptyset$.
--   3. **Adding a tier-2 supplier.** $g'$ arises from $g$ by adding a fresh supplier $j\notin S(2)$ as an exclusive supplier of firm $x$ (then $S'_x=S_x\cup\{j\}$, $S'(1)=S(1)\cup\{x\}$, the other two classes unchanged), or as a shared supplier (then $S'_{ab}=S_{ab}\cup\{j\}$, $S'(1)=\{a,b\}$). A firm that was absent joins the network, as in (C.36).
--   4. **Vetted tier 1.** Every tier-1 firm is vetted at $\gamma=(g,U)$: $S(1)\cap U=\emptyset$.
--   5. **The state $\gamma_1$** (fn. 9, p. 21): $g=(\{a,b\},\{1\},\{2\},\emptyset)$, both tier-1 firms vetted, $U=\{1,2\}$, up to the labels of the two tier-2 suppliers.
--
--   **Formalization Note** The published `Network` type admits tuples outside $G$; the production-phase results quantify over well-formed networks only.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), pp. 8, 10 (fn. 4), 15 (fn. 6), 21 (fn. 9), OA-9 (C.36)

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting

namespace SRAudit.TwoPhase.Supplement
open SRAudit.TwoPhase

variable {ι : Type} [DecidableEq ι]

/-- The other tier-1 firm: `−i ∈ {a, b} \ {i}`. -/
def otherFirm : Firm → Firm
  | .a => .b
  | .b => .a

/-- The networks of the paper's set `G` (pp. 8, 15 fn. 6, OA-9 (C.36)): an absent tier-1 firm has no
exclusive suppliers, shared suppliers exist only when both tier-1 firms are present, and every present
tier-1 firm has at least one tier-2 supplier. -/
def WellFormedNet (g : Network ι) : Prop :=
  (∀ x : Firm, x ∉ g.T1 → g.excl x = ∅) ∧
  (g.Sab.Nonempty → g.T1 = Finset.univ) ∧
  (∀ x ∈ g.T1, (g.excl x ∪ g.Sab).Nonempty)

/-- The null network `g∅`: no tier-1 firm or no tier-2 supplier (p. 8). -/
def IsNullNet (g : Network ι) : Prop := g.T1 = ∅ ∨ g.S2 = ∅

/-- A state of `Γ`: its network lies in `G`. -/
def WellFormedState (γ : State ι) : Prop := WellFormedNet γ.g

/-- `g'` is `g` with the fresh tier-2 supplier `j` added as an exclusive supplier of tier-1 firm `x`
(firm `x` joins the network if it was absent, as in (C.36)). -/
def AddsExclusive (x : Firm) (g g' : Network ι) (j : ι) : Prop :=
  j ∉ g.S2 ∧ g'.T1 = insert x g.T1 ∧ g'.excl x = insert j (g.excl x) ∧
  g'.excl (otherFirm x) = g.excl (otherFirm x) ∧ g'.Sab = g.Sab

/-- `g'` is `g` with the fresh tier-2 supplier `j` added as a shared supplier of both tier-1 firms
(both firms are then present, as in (C.36)). -/
def AddsShared (g g' : Network ι) (j : ι) : Prop :=
  j ∉ g.S2 ∧ g'.T1 = Finset.univ ∧ g'.Sa = g.Sa ∧ g'.Sb = g.Sb ∧ g'.Sab = insert j g.Sab

/-- Every tier-1 firm is vetted: `S(1) ∩ U_γ = ∅`. -/
def Tier1Vetted (γ : State ι) : Prop := ∀ x : Firm, Supplier.t1 x ∉ γ.U

/-- The boundary state `γ1` of footnote 9 (p. 21), up to the labels of its two tier-2 suppliers:
`g = ({a, b}, {1}, {2}, ∅)`, both tier-1 firms vetted, `U = {1, 2}`. -/
def IsGamma1 (γ : State ι) : Prop :=
  ∃ j₁ j₂ : ι, j₁ ≠ j₂ ∧ γ.g.T1 = Finset.univ ∧ γ.g.Sa = {j₁} ∧ γ.g.Sb = {j₂} ∧
    γ.g.Sab = ∅ ∧ γ.U = {Supplier.t2 j₁, Supplier.t2 j₂}

end SRAudit.TwoPhase.Supplement


