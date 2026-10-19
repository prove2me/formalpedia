-- Prove2me | Definitions.Def_SRAudit_TwoPhase_Setting
-- name    : SRAudit_TwoPhase_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:02.041187+00:00
-- url     : https://prove2.me/theorems/258a5c0f-78e5-4187-ab4b-c10cc8682734
-- title:
--   §3.1–§3.2 and Appendix D — three-tier auditing network and its finite decision process
-- statement:
--   A network $g=(S^{(1)},S_a,S_b,S_{ab})$ has a set of active tier-1 firms, exclusive tier-2 suppliers for each firm, and tier-2 suppliers shared by the firms. The tier-2 sets are pairwise disjoint. A state $\gamma=(g,U_\gamma)$ records the unaudited suppliers in the current network. Dropping supplier $i$ removes $i$ and its dependents $D_g(i)$; when a tier-1 firm is dropped, formerly shared tier-2 suppliers become exclusive to the other firm.
--
--   At each state, the buyer may proceed to production ($pp$), audit and rectify an unaudited supplier ($ar(i)$), or audit and drop it on failure ($ad(i)$). The expected penalty and rectification threshold are
--
--   $$
--   \zeta(\gamma)=|U_\gamma|uwz,\qquad c_{rp}=\min\{uwz,a+ur\}.
--   $$
--
--   The optimal value $V^*$ is the finite Bellman recursion in (1)–(5). The policy value $V(\xi,\gamma)$ follows (D.1)–(D.4), and $V_{ar}$ restricts the available actions to $pp$ and $ar$. These definitions provide the common model for the structural policy theorem and its two appendix propositions.
--
--   **Formalization Note** Tier-2 suppliers have labels in an arbitrary type. Production profit is a function of the network. The transition operators are total, but their values on suppliers outside the network are unused. Action values on inadmissible supplier actions are set to zero; a policy's value uses the production value for such an action and the theorems require admissible policies.
-- source:
--   Zhang, Aydin, Parker, Social Responsibility Auditing in Supply Chain Networks, Management Science (2021), doi:10.1287/mnsc.2020.3950, authors' accepted manuscript (sha256 d043d8d5…6b), pp. 8–11 and OA-11, §3.1–§3.2, fns. 3–4, (1)–(5), (D.1)–(D.4)

import Mathlib

namespace SRAudit.TwoPhase

inductive Firm | a | b
  deriving DecidableEq

instance : Fintype Firm := ⟨{.a, .b}, by intro x; cases x <;> simp⟩

inductive Supplier (ι : Type) | t1 (x : Firm) | t2 (j : ι)
  deriving DecidableEq

structure Network (ι : Type) [DecidableEq ι] where
  T1 : Finset Firm
  Sa : Finset ι
  Sb : Finset ι
  Sab : Finset ι
  hab : Disjoint Sa Sb
  hac : Disjoint Sa Sab
  hbc : Disjoint Sb Sab

variable {ι : Type} [DecidableEq ι]

instance : Inhabited (Network ι) := ⟨⟨∅, ∅, ∅, ∅, by simp, by simp, by simp⟩⟩

def Network.excl (g : Network ι) : Firm → Finset ι
  | .a => g.Sa
  | .b => g.Sb

def Network.S2 (g : Network ι) : Finset ι := g.Sa ∪ g.Sb ∪ g.Sab

def Network.suppliers (g : Network ι) : Finset (Supplier ι) :=
  g.T1.image Supplier.t1 ∪ g.S2.image Supplier.t2

def Network.dependents (g : Network ι) : Supplier ι → Finset (Supplier ι)
  | .t1 x => insert (.t1 x) ((g.excl x).image Supplier.t2)
  | .t2 j => insert (.t2 j)
      ((Finset.univ.filter (fun x : Firm => g.excl x ∪ g.Sab = {j})).image Supplier.t1)

structure State (ι : Type) [DecidableEq ι] where
  g : Network ι
  U : Finset (Supplier ι)
  hU : U ⊆ g.suppliers

def State.Terminal (γ : State ι) : Prop := γ.U = ∅

def vet (γ : State ι) (i : Supplier ι) : State ι :=
  ⟨γ.g, γ.U.erase i, Finset.erase_subset i γ.U |>.trans γ.hU⟩

private def dropNetwork (g : Network ι) (i : Supplier ι) : Network ι := by
  classical
  let D := g.dependents i
  cases i with
  | t1 x =>
      cases x with
      | a =>
          refine ⟨g.T1.erase .a, ∅, (g.Sb ∪ g.Sab).filter (fun j => Supplier.t2 j ∉ D), ∅, ?_, ?_, ?_⟩
          all_goals simp
      | b =>
          refine ⟨g.T1.erase .b, (g.Sa ∪ g.Sab).filter (fun j => Supplier.t2 j ∉ D), ∅, ∅, ?_, ?_, ?_⟩
          all_goals simp
  | t2 j =>
      refine ⟨g.T1.filter (fun x => Supplier.t1 x ∉ D),
        g.Sa.filter (fun k => Supplier.t2 k ∉ D),
        g.Sb.filter (fun k => Supplier.t2 k ∉ D),
        g.Sab.filter (fun k => Supplier.t2 k ∉ D), ?_, ?_, ?_⟩
      · exact g.hab.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      · exact g.hac.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      · exact g.hbc.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

def drop (γ : State ι) (i : Supplier ι) : State ι := by
  classical
  let g' := dropNetwork γ.g i
  refine ⟨g', γ.U \ γ.g.dependents i, ?_⟩
  intro s hs
  have hsU : s ∈ γ.U := (Finset.mem_sdiff.mp hs).1
  have hsD : s ∉ γ.g.dependents i := (Finset.mem_sdiff.mp hs).2
  have hsg : s ∈ γ.g.suppliers := γ.hU hsU
  cases i with
  | t1 x =>
      cases x <;> cases s <;>
        simp_all [g', dropNetwork, Network.suppliers, Network.S2,
          Network.dependents, Network.excl]
  | t2 j =>
      cases s <;>
        simp_all [g', dropNetwork, Network.suppliers, Network.S2,
          Network.dependents, Network.excl]

inductive Action (ι : Type) | pp | ar (i : Supplier ι) | ad (i : Supplier ι)
  deriving DecidableEq

def Admissible (γ : State ι) : Action ι → Prop
  | .pp => True
  | .ar i => i ∈ γ.U
  | .ad i => i ∈ γ.U

def Policy (ι : Type) [DecidableEq ι] := State ι → Action ι

def IsAdmissible (ξ : Policy ι) : Prop := ∀ γ, Admissible γ (ξ γ)

structure Params where
  a : ℝ
  r : ℝ
  u : ℝ
  w : ℝ
  z : ℝ

def Params.Standing (P : Params) : Prop :=
  0 ≤ P.a ∧ 0 ≤ P.r ∧ 0 < P.u ∧ P.u < 1 ∧ 0 < P.w ∧ P.w ≤ 1 ∧ 0 ≤ P.z

def zeta (P : Params) (γ : State ι) : ℝ := γ.U.card * (P.u * P.w * P.z)

def crp (P : Params) : ℝ := min (P.u * P.w * P.z) (P.a + P.u * P.r)

def ppValue (P : Params) (π : Network ι → ℝ) (γ : State ι) : ℝ :=
  π γ.g - zeta P γ

private theorem vet_card_lt (γ : State ι) (i : Supplier ι) (hi : i ∈ γ.U) :
    (vet γ i).U.card < γ.U.card := by
  simpa [vet] using Finset.card_erase_lt_of_mem hi

private theorem drop_card_lt (γ : State ι) (i : Supplier ι) (hi : i ∈ γ.U) :
    (drop γ i).U.card < γ.U.card := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (Finset.sdiff_subset)).2
  have hD : i ∈ γ.g.dependents i := by cases i <;> simp [Network.dependents]
  exact ⟨i, hi, by simp [hD]⟩

noncomputable def Vstar (P : Params) (π : Network ι → ℝ) (γ : State ι) : ℝ :=
  if h : γ.U.Nonempty then
    max (ppValue P π γ)
      (γ.U.attach.sup' (by simpa using h) (fun i =>
        max (-P.a - P.u * P.r + Vstar P π (vet γ i.val))
            (-P.a + (1 - P.u) * Vstar P π (vet γ i.val) +
              P.u * Vstar P π (drop γ i.val))))
  else ppValue P π γ
termination_by γ.U.card
decreasing_by
  all_goals
    first | exact vet_card_lt γ i.val i.property | exact drop_card_lt γ i.val i.property

noncomputable def Qstar (P : Params) (π : Network ι → ℝ) (γ : State ι) : Action ι → ℝ
  | .pp => ppValue P π γ
  | .ar i => if i ∈ γ.U then -P.a - P.u * P.r + Vstar P π (vet γ i) else 0
  | .ad i => if i ∈ γ.U then
      -P.a + (1 - P.u) * Vstar P π (vet γ i) + P.u * Vstar P π (drop γ i) else 0

def IsOptimal (P : Params) (π : Network ι → ℝ) (ξ : Policy ι) : Prop :=
  IsAdmissible ξ ∧ ∀ γ, Qstar P π γ (ξ γ) = Vstar P π γ

noncomputable def Vpol (P : Params) (π : Network ι → ℝ) (ξ : Policy ι)
    (γ : State ι) : ℝ :=
  match ξ γ with
  | .pp => ppValue P π γ
  | .ar i => if i ∈ γ.U then -P.a - P.u * P.r + Vpol P π ξ (vet γ i)
      else ppValue P π γ
  | .ad i => if i ∈ γ.U then
      -P.a + (1 - P.u) * Vpol P π ξ (vet γ i) + P.u * Vpol P π ξ (drop γ i)
      else ppValue P π γ
termination_by γ.U.card
decreasing_by
  all_goals
    first | exact vet_card_lt γ i ‹i ∈ γ.U› | exact drop_card_lt γ i ‹i ∈ γ.U›

noncomputable def Qpol (P : Params) (π : Network ι → ℝ) (ξ : Policy ι)
    (γ : State ι) : Action ι → ℝ
  | .pp => ppValue P π γ
  | .ar i => if i ∈ γ.U then -P.a - P.u * P.r + Vpol P π ξ (vet γ i) else 0
  | .ad i => if i ∈ γ.U then
      -P.a + (1 - P.u) * Vpol P π ξ (vet γ i) + P.u * Vpol P π ξ (drop γ i) else 0

noncomputable def Var (P : Params) (π : Network ι → ℝ) (γ : State ι) : ℝ :=
  if h : γ.U.Nonempty then
    max (ppValue P π γ)
      (γ.U.attach.sup' (by simpa using h) (fun i =>
        -P.a - P.u * P.r + Var P π (vet γ i.val)))
  else ppValue P π γ
termination_by γ.U.card
decreasing_by
  exact vet_card_lt γ i.val i.property

noncomputable def Qar (P : Params) (π : Network ι → ℝ) (γ : State ι) : Action ι → ℝ
  | .pp => ppValue P π γ
  | .ar i => if i ∈ γ.U then -P.a - P.u * P.r + Var P π (vet γ i) else 0
  | .ad _ => 0

end SRAudit.TwoPhase


