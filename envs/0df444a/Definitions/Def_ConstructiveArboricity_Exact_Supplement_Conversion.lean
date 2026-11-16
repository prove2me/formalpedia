-- Prove2me | Definitions.Def_ConstructiveArboricity_Exact_Supplement_Conversion
-- name    : ConstructiveArboricity_Exact_Supplement_Conversion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:14:07.020308+00:00
-- url     : https://prove2.me/theorems/4b376004-fdba-4ecb-b227-7ce8f3f9067d
-- title:
--   Surplus sets, path swaps and cycle exchanges in pseudoforest conversion
-- statement:
--   A conversion state records the current color of each edge and the set $Y$ of surplus edges. Its color-$i$ forest consists of the edges of color $i$ outside $Y$. Initially, exactly one edge of each cyclic input component is removed into $Y$. A swap exchanges the colors of incident surplus edges, placing an edge into its new forest if it joins two different trees. Repeated colors are removed by swaps along a simple path, stopping when an edge leaves $Y$.
--
--   When $Y$ is colorful, a cycle attempt chooses a color present in the cyclic component whose forest has no edge from the chosen vertex back into that component. Swaps move this color to a cycle edge. If no edge leaves $Y$, that edge is exchanged with the first forest-path edge leading outside the component. A finite execution stops when $Y$ is acyclic and projects to the $k+1$ color classes. These are actual edge operations; the RAM execution in the theorem charges the implementation, scheduling, memory and output work.
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. §§2–5 and Appendix A, definition interface, PDF/printed p.12.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Extraction

/-! Surplus-edge semantics of the Blumenstock–Fischer conversion, §3.2 and
Appendix A, pp.12–13,36–38. Swaps and cycle exchanges change actual edge sets;
there is no native dynamic-tree operation or uncharged execution oracle. -/
namespace ConstructiveArboricity.Exact.Supplement
noncomputable section
open Classical

structure BFState (G : Graph) (k : ℕ) where
  color : Fin G.m → Fin k
  surplus : Finset (Fin G.m)

def BFState.forest {G : Graph} {k : ℕ} (s : BFState G k) (i : Fin k) : Finset (Fin G.m) :=
  Finset.univ.filter fun e => s.color e = i ∧ e ∉ s.surplus

def BFState.Colorful {G : Graph} {k : ℕ} (s : BFState G k) : Prop :=
  ∀ e ∈ s.surplus, ∀ f ∈ s.surplus,
    (G.onEdges (↑s.surplus)).Reachable (G.ends e).1 (G.ends f).1 →
    s.color e = s.color f → e = f

def BFInitial (G : Graph) {k : ℕ} (c : Fin G.m → Fin k) (s : BFState G k) : Prop :=
  s.color = c ∧ ∀ i, ∀ C : (G.onEdges {e | c e = i}).ConnectedComponent,
    let R := s.surplus.filter fun e => c e = i ∧ (G.ends e).1 ∈ C.supp
    (↑R : Set (Fin G.m)) ⊆ {e | c e = i} ∩ G.edgesIn C.supp ∧
    G.IsForest (({e | c e = i} ∩ G.edgesIn C.supp) \ ↑R) ∧
    R.card = if G.IsForest ({e | c e = i} ∩ G.edgesIn C.supp) then 0 else 1

/-- The two incident surplus edges exchange colors; each goes into its new
forest precisely when it joins different trees of that forest. -/
def BFSwap (G : Graph) {k : ℕ} (s : BFState G k) (e f : Fin G.m) : BFState G k :=
  let connected := fun a i => (G.onEdges (↑(s.forest i))).Reachable (G.ends a).1 (G.ends a).2
  { color := Function.update (Function.update s.color e (s.color f)) f (s.color e)
    surplus := ((s.surplus.erase e).erase f) ∪
      (if connected e (s.color f) then {e} else ∅) ∪
      (if connected f (s.color e) then {f} else ∅) }

/-- One allowed swap, or one cycle exchange. Cycle exchanges replace a surplus
cycle edge uv by the first forest-path edge vw, with w outside the surplus
component. The scheduler and the data structures must be implemented in RAM. -/
inductive BFStep (G : Graph) {k : ℕ} : BFState G k → BFState G k → Prop
  | swap (s : BFState G k) (e f : Fin G.m)
      (he : e ∈ s.surplus) (hf : f ∈ s.surplus) (hne : s.color e ≠ s.color f)
      (incident : ∃ v, v ∈ ({(G.ends e).1, (G.ends e).2} : Finset _) ∧
        v ∈ ({(G.ends f).1, (G.ends f).2} : Finset _)) :
      BFStep G s (BFSwap G s e f)
  | exchange (s : BFState G k) (e f : Fin G.m) (v w : Fin G.n)
      (colorful : s.Colorful) (he : e ∈ s.surplus)
      (cycle : (G.onEdges (↑(s.surplus.erase e))).Reachable (G.ends e).1 (G.ends e).2)
      (path : f ∈ s.forest (s.color e) ∧
        ¬ (G.onEdges (↑((s.forest (s.color e)).erase f))).Reachable (G.ends e).1 (G.ends e).2)
      (at_v : v = (G.ends e).1 ∨ v = (G.ends e).2)
      (ends_f : G.edge f = s(v,w))
      (outside : ¬ (G.onEdges (↑s.surplus)).Reachable v w) :
      BFStep G s { s with surplus := insert f (s.surplus.erase e) }

/-- A simple surplus path, encoded with its actual edge identities. -/
def SurplusPath (G : Graph) {k : ℕ} (s : BFState G k)
    (es : List (Fin G.m)) : Prop :=
  ∃ vs : List (Fin G.n), vs.Nodup ∧ ∃ hlen : vs.length = es.length + 1,
    (∀ e ∈ es, e ∈ s.surplus) ∧
    ∀ j : Fin es.length, G.edge es[j] =
      s(vs[j.val]'(by omega), vs[j.val+1]'(by omega))

/-- Consecutive edges share an endpoint; identities are not collapsed. -/
def IncidentSequence (G : Graph) (es : List (Fin G.m)) : Prop :=
  ∀ j : Fin (es.length - 1),
    let e := es[j.val]'(by omega)
    let f := es[j.val+1]'(by omega)
    ∃ v, v ∈ ({(G.ends e).1, (G.ends e).2} : Finset _) ∧
      v ∈ ({(G.ends f).1, (G.ends f).2} : Finset _)

/-- Move the first edge's color down an incident-edge sequence, stopping at
once when an edge leaves Y. An illegal swap is not an execution. -/
def swapChain (G : Graph) {k : ℕ} : BFState G k → List (Fin G.m) → Option (BFState G k)
  | s, [] => some s
  | s, [_] => some s
  | s, e :: f :: rest =>
    if e ∈ s.surplus ∧ f ∈ s.surplus ∧ s.color e ≠ s.color f ∧
        (∃ v, v ∈ ({(G.ends e).1, (G.ends e).2} : Finset _) ∧
          v ∈ ({(G.ends f).1, (G.ends f).2} : Finset _)) then
      let s' := BFSwap G s e f
      if s'.surplus.card < s.surplus.card then some s'
      else swapChain G s' (f :: rest)
    else none

/-- The two kinds of attempts in §3.2/Appendix A. Repeated-color attempts
follow a simple path; cycle attempts follow distinct incident edges to the
chosen cycle edge. Each attempt either loses an edge or performs the specified
cycle exchange, after which repeated colors are removed before another cycle
attempt. Nothing here prescribes a running time or assumes an output partition. -/
inductive BFAttempt (G : Graph) {k : ℕ} : BFState G k → BFState G k → Prop
  | repeated (s s' : BFState G k) (e f : Fin G.m) (middle : List (Fin G.m))
      (path : SurplusPath G s (e :: middle ++ [f]))
      (same : s.color e = s.color f)
      (inner : ∀ a ∈ middle, s.color a ≠ s.color e)
      (run : swapChain G s (e :: middle ++ [f]) = some s')
      (lost : s'.surplus.card < s.surplus.card) : BFAttempt G s s'
  | cycle (s s' out : BFState G k) (es : List (Fin G.m)) (a e : Fin G.m) (v : Fin G.n)
      (colorful : s.Colorful) (first : es.head? = some a) (last : es.getLast? = some e)
      (distinct : es.Nodup) (incident : IncidentSequence G es) (surplus : ∀ f ∈ es, f ∈ s.surplus)
      (onCycle : (G.onEdges (↑(s.surplus.erase e))).Reachable (G.ends e).1 (G.ends e).2)
      (at_v : v = (G.ends e).1 ∨ v = (G.ends e).2)
      (choice : ∀ f ∈ s.forest (s.color a),
        (G.ends f).1 = v → ¬ (G.onEdges (↑s.surplus)).Reachable v (G.ends f).2)
      (choice' : ∀ f ∈ s.forest (s.color a),
        (G.ends f).2 = v → ¬ (G.onEdges (↑s.surplus)).Reachable v (G.ends f).1)
      (run : swapChain G s es = some s')
      (finish : (s'.surplus.card < s.surplus.card ∧ out = s') ∨
        (s'.surplus.card = s.surplus.card ∧ ∃ f w,
          f ∈ s'.forest (s'.color e) ∧
          G.edge f = s(v,w) ∧
          ¬ (G.onEdges (↑((s'.forest (s'.color e)).erase f))).Reachable (G.ends e).1 (G.ends e).2 ∧
          ¬ (G.onEdges (↑s'.surplus)).Reachable v w ∧
          out = { s' with surplus := insert f (s'.surplus.erase e) })) : BFAttempt G s out

/-- A terminating conversion run, projected to its output coloring. The last
class is the surplus graph. Correctness and RAM time are theorem conclusions. -/
def BFResult (G : Graph) {k : ℕ} (c : Fin G.m → Fin k)
    (out : Fin G.m → Fin (k+1)) : Prop :=
  ∃ s₀ s : BFState G k, BFInitial G c s₀ ∧
    Relation.ReflTransGen (BFAttempt G) s₀ s ∧ G.IsForest (↑s.surplus) ∧
    ∀ e, out e = if e ∈ s.surplus then ⟨k, Nat.lt_succ_self k⟩ else (s.color e).castSucc

end
end ConstructiveArboricity.Exact.Supplement


