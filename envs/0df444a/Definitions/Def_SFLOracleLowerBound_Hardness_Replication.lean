-- Prove2me | Definitions.Def_SFLOracleLowerBound_Hardness_Replication
-- name    : SFLOracleLowerBound_Hardness_Replication
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:28:07.578148+00:00
-- url     : https://prove2.me/theorems/c36919d2-3e50-47fb-a4dc-6113943241bc
-- title:
--   Public blocks, hidden partitions and replicated facility costs
-- statement:
--   For a symmetric base instance and positive integer $R$, the public client positions are $\mathcal C_0\times[R]$. The block over an orbit $P_i$ has $R|P_i|$ positions. A hidden labelling $\pi$ stays inside each block and assigns exactly $R$ positions to each input client. The probability of an event is the fraction of all such labellings satisfying it, giving independent uniform choices in distinct blocks. The public position's first coordinate is an index, not its hidden label.
--
--   With $\lambda>0$, define
--   $$
--   \psi(S)=\sum_i\min\{|S\cap P_i|,|P_i\setminus S|\},\quad
--   g_\pi(T)=\min_S\{|T\setminus\pi^{-1}(S)|+Rg(S)+\lambda\psi(S)\},
--   $$
--   $$
--   g_{\rm ref}(T)=\min_{S\text{ invariant}}\{|T\setminus(S\times[R])|+Rg(S)\}.
--   $$
--   The reference formula through $\pi$ uses the same invariant witnesses and permits the independence clause to be stated explicitly. Every replicated client's public connection costs are those of its public orbit. Define $\xi_u(T)=|T\cap\pi^{-1}(u)|-|T\cap B(\omega(u))|/|P_{\omega(u)}|$; a query is well-balanced when $|\xi_u(T)|\le\lambda$ for every $u$.
--
--   All minima and partition probabilities are computed from these finite objects. Under a permutation group and positive $R$ their ranges are nonempty; no oracle agreement or hardness is assumed.
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), §§3.2–3.3, pp.10–13, equations (5)–(6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_Symmetry
import Definitions.Def_SFLOracleLowerBound_Hardness_Oracle

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- §3.2, p.10: public carrier, canonically labelled for indexing only. -/
abbrev Copies (C : Type) (R : ℕ) := C × Fin R

def publicBlock {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (R : ℕ) (u : C) : Finset (Copies C R) :=
  univ.filter (fun c => c.1 ∈ orbit Γ u)

/-- Balanced labellings within the public blocks; this entire finite set is sampled uniformly. -/
def HiddenPartition {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (R : ℕ) (π : Copies C R → C) : Prop :=
  (∀ c, π c ∈ orbit Γ c.1) ∧ ∀ u, (univ.filter (fun c => π c = u)).card = R

def partitions {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (R : ℕ) : Finset (Copies C R → C) :=
  univ.filter (HiddenPartition Γ R)

def partitionProbability {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (R : ℕ) (event : (Copies C R → C) → Prop) : ℝ :=
  ((partitions Γ R).filter event).card / (partitions Γ R).card

def splitPenalty {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (S : Finset C) : ℝ :=
  ∑ P ∈ orbits Γ, (min (S ∩ P).card (P \ S).card : ℕ)

/-- Equation (5), computed from its witnesses. -/
def hiddenCost {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (R : ℕ) (lam : ℝ) (g : Finset C → ℝ)
    (π : Copies C R → C) (T : Finset (Copies C R)) : ℝ :=
  ⨅ S : Finset C, ((T.filter (fun c => π c ∉ S)).card : ℝ) + R * g S + lam * splitPenalty Γ S

/-- Equation (6), equivalently minimizing over invariant subsets; no π argument. -/
def referenceCost {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (R : ℕ) (g : Finset C → ℝ)
    (T : Finset (Copies C R)) : ℝ :=
  sInf {v : ℝ | ∃ S : Finset C, InvariantSet Γ S ∧
    v = ((T.filter (fun c => c.1 ∉ S)).card : ℝ) + R * g S}

def replicatedData {C F : Type} (D : PublicData C F) (R : ℕ) : PublicData (Copies C R) F :=
  fun c f => D c.1 f

def imbalance {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (R : ℕ) (π : Copies C R → C)
    (T : Finset (Copies C R)) (u : C) : ℝ :=
  ((T.filter (fun c => π c = u)).card : ℝ) -
    ((T ∩ publicBlock Γ R u).card : ℝ) / (orbit Γ u).card

def WellBalanced {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (R : ℕ) (lam : ℝ) (π : Copies C R → C)
    (T : Finset (Copies C R)) : Prop := ∀ u, |imbalance Γ R π T u| ≤ lam

/-- Same restricted-witness formula written using π; equals the public reference. -/
def referenceViaPartition {C : Type} [Fintype C] [DecidableEq C]
    (Γ : Finset (Equiv.Perm C)) (R : ℕ) (g : Finset C → ℝ)
    (π : Copies C R → C) (T : Finset (Copies C R)) : ℝ :=
  sInf {v : ℝ | ∃ S : Finset C, InvariantSet Γ S ∧
    v = ((T.filter (fun c => π c ∉ S)).card : ℝ) + R * g S}

end SFLOracleLowerBound.Hardness


