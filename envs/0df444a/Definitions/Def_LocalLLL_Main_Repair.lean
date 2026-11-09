-- Prove2me | Definitions.Def_LocalLLL_Main_Repair
-- name    : LocalLLL_Main_Repair
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:12.796821+00:00
-- url     : https://prove2.me/theorems/fff63dbe-3532-412e-a038-5af62768bb8d
-- title:
--   Danger centers and the repair LLL
-- statement:
--   For centers $S$, erase $W=\bigcup_{u\in B_G(S,4)}V_u$. An event is affected when its coordinate set meets $W$. Assign it to the smallest-identifier center in $S\cap B_G(v,5)$. The repair event $E_s$ is the union of assigned original events, with coordinates outside $W$ fixed to $x$:
--
--   $$E_s=\{z:\ \exists v\text{ assigned to }s,\ \mathrm{splice}_W(x,z)\in A_v\}.$$
--
--   Its variable set is $W\cap\bigcup_{v\text{ assigned to }s}V_v$, and the repair graph is $G^{11}[S]$. The center conditions require bounded danger, $S\subseteq D$, 2-independence of $S$ in $G$, and $D\subseteq B_G(S,4)$. They contain no assumed algorithm, ruling-set oracle or target probability estimate. These definitions express the repair problem over the same variables as the original instance.
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §3.2 Part III, p. 6 (PDF 7), closing claim p. 7 (PDF 8); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Danger

noncomputable section

namespace LocalLLL.Main

open MeasureTheory

variable {ι V : Type} {α : ι → Type} [∀ z, MeasurableSpace (α z)]

def erased (G : SimpleGraph V) (vars : V → Set ι) (S : Set V) : Set ι :=
  variablesOf vars (balls G S 4)

def affected (G : SimpleGraph V) (vars : V → Set ι) (S : Set V) (v : V) : Prop :=
  (vars v ∩ erased G vars S).Nonempty

/-- Smallest-ID center within five hops, among the eligible centers. -/
def assignedTo (G : SimpleGraph V) (id : V → ℕ) (vars : V → Set ι)
    (S : Set V) (v s : V) : Prop :=
  affected G vars S v ∧ s ∈ S ∧ s ∈ ball G v 5 ∧
    ∀ t ∈ S, t ∈ ball G v 5 → id s ≤ id t

/-- A section of the union of events assigned to s, over just the erased coordinates. -/
def repairEvent (G : SimpleGraph V) (id : V → ℕ) (vars : V → Set ι)
    (events : V → Set (Assignment α)) (S : Set V) (x : Assignment α) (s : S) :
    Set (Assignment α) :=
  {z | ∃ v, assignedTo G id vars S v s.1 ∧ splice x z (erased G vars S) ∈ events v}

def repairVars (G : SimpleGraph V) (id : V → ℕ) (vars : V → Set ι)
    (S : Set V) (s : S) : Set ι :=
  erased G vars S ∩ variablesOf vars {v | assignedTo G id vars S v s.1}

def repairGraph (G : SimpleGraph V) (S : Set V) : SimpleGraph S :=
  (graphPower G 11).induce S

/-- These are exactly the geometric hypotheses on centers, not an assumed algorithm. -/
def centerConditions (μ : ∀ z, Measure (α z)) (G : SimpleGraph V) (vars : V → Set ι)
    (events : V → Set (Assignment α)) (d : ℕ) (lam : ℝ) (x : Assignment α)
    (S : Set V) : Prop :=
  boundedDanger μ G vars events d lam x ∧
  (∀ s ∈ S, x ∈ dangerous μ G vars events d lam s) ∧ separated G 2 S ∧
  {v | x ∈ dangerous μ G vars events d lam v} ⊆ balls G S 4
end LocalLLL.Main


