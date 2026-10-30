-- Prove2me | Definitions.Def_VehicleRoutingSurvey_Routing_MixedAlgorithms
-- name    : VehicleRoutingSurvey_Routing_MixedAlgorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:12:23.587673+00:00
-- url     : https://prove2.me/theorems/9b1345aa-f9cd-47cd-9f85-1eaaa6842d31
-- title:
--   Edmonds–Johnson, reversed and combined mixed-postman runs
-- statement:
--   Mixed-postman runs retain distinct copies and directions. The first procedure performs undirected parity augmentation, minimum-cost integral flow balancing, alternating-path parity adjustment, and Euler traversal. The reversed procedure performs flow balancing followed by matching odd vertices through original undirected links. The combined procedure returns the cheaper of these two outputs. The flow has explicit additional-copy variables and two unit orientation choices for each undirected link. No ratio or optimal-tour premise defines a run. This combined procedure does not identify the different planar mixed strategy.
-- source:
--   Lenstra and Rinnooy Kan, Complexity of vehicle routing and scheduling problems, Econometric Institute Report 7919/O (1979), Table 3, p. 5 [9]; algorithms as in Frederickson (1979), §§3–5, pp. 540–547, https://www.scribd.com/document/930249049/322139-322150

import Definitions.Def_VehicleRoutingSurvey_Routing_RuralAlgorithm

open Classical

namespace VehicleRoutingSurvey.Routing

def forgetDirections (G : Network) : Network := {G with directed := fun _ => false}

def orientationValid (G : Network) (t : Traversal G) : Prop :=
  G.directed t.1 = false ∨ t.2 = true

def balanced (G : Network) (M : List (Traversal G)) : Prop :=
  ∀ v, (M.filter (fun t => start G t = v)).length =
    (M.filter (fun t => finish G t = v)).length

/-- The integral flow variables of INOUTDEGREE, retaining the two unit-capacity
orientation variables for every undirected edge copy. -/
structure InOutFlow (G : Network) where
  extraForward : Fin G.q → ℕ
  extraBackward : Fin G.q → ℕ
  orientForward : Fin G.q → Bool
  orientBackward : Fin G.q → Bool

def flowExtra (G : Network) (f : InOutFlow G) : List (Traversal G) :=
  (List.finRange G.q).flatMap (fun e =>
    List.replicate (f.extraForward e) (e, true) ++
      List.replicate (f.extraBackward e) (e, false))

def flowBase (G : Network) (f : InOutFlow G) : List (Traversal G) :=
  (List.finRange G.q).flatMap (fun e =>
    if G.directed e then [(e, true)] else
      if f.orientForward e ≠ f.orientBackward e then [(e, f.orientForward e)] else [])

def flowUnoriented (G : Network) (f : InOutFlow G) : List (Fin G.q) :=
  (List.finRange G.q).filter (fun e =>
    G.directed e = false ∧ f.orientForward e = f.orientBackward e)

def FlowFeasible (G : Network) (f : InOutFlow G) : Prop :=
  (∀ e, G.directed e = true → f.extraBackward e = 0) ∧
  balanced G (flowBase G f ++ flowExtra G f)

def MinimumFlow (G : Network) (f : InOutFlow G) : Prop :=
  FlowFeasible G f ∧ ∀ g, FlowFeasible G g →
    pathCost G (flowExtra G f) ≤ pathCost G (flowExtra G g)

def undirectedPath (G : Network) (u v : Fin G.n) (ts : List (Traversal G)) : Prop :=
  IsPath (forgetDirections G) u ts v

def noInteriorOdd (G : Network) (O : Finset (Fin G.n)) (ts : List (Traversal G)) : Prop :=
  ∀ t ∈ ts.dropLast, finish G t ∉ O

/-- A parity-adjustment state; `extra` is the not-yet-used M-double-prime list. -/
structure ParityState (G : Network) where
  extra : List (Traversal G)
  unoriented : List (Fin G.q)
  oriented : List (Traversal G)
  odd : Finset (Fin G.n)

/-- The alternating M-double-prime/U cycle of ADJUSTCYCLES is performed
as whole path pairs. Occurrences, not just edge membership, are removed. -/
def AdjustPair (G : Network) (root v w : Fin G.n)
    (s s' : ParityState G) : Prop :=
  ∃ z mp up consumed mleft uleft,
    undirectedPath G v z mp ∧ mp ≠ [] ∧ z ∈ s.odd ∧
    noInteriorOdd G s.odd mp ∧
    List.Forall₂ (fun a b : Traversal G => a.1 = b.1) consumed mp ∧
    s.extra.Perm (consumed ++ mleft) ∧
    undirectedPath G z w up ∧ up ≠ [] ∧
    (up.map Prod.fst ++ uleft).Perm s.unoriented ∧
    (w = root ∨ w ∈ s.odd.erase z) ∧
    noInteriorOdd G (insert root (s.odd.erase z)) up ∧
    s'.extra = mleft ∧ s'.unoriented = uleft ∧
    s'.odd = (s.odd.erase z).erase w ∧
    s'.oriented = (consumed.zip mp).foldl
      (fun M p => if p.1.2 = p.2.2 then p.1 :: M else M.erase p.1) s.oriented ++ up

inductive AdjustCycle (G : Network) (root : Fin G.n) :
    Fin G.n → ParityState G → ParityState G → Prop
  | close (v : Fin G.n) (s s' : ParityState G)
      (h : AdjustPair G root v root s s') : AdjustCycle G root v s s'
  | next (v w : Fin G.n) (s s' s'' : ParityState G)
      (h : AdjustPair G root v w s s') (hne : w ≠ root)
      (rest : AdjustCycle G root w s' s'') : AdjustCycle G root v s s''

def ParityRound (G : Network) (s s' : ParityState G) : Prop :=
  ∃ root ∈ s.odd, AdjustCycle G root root {s with odd := s.odd.erase root} s'

def ParityCorrection (G : Network) (f : InOutFlow G)
    (M : List (Traversal G)) (U : List (Fin G.q)) : Prop :=
  let initial : ParityState G :=
    ⟨flowExtra G f, flowUnoriented G f, flowBase G f ++ flowExtra G f,
      Finset.univ.filter (fun v => Odd (degree G
        ((flowBase G f ++ flowExtra G f).map Prod.fst ++ flowUnoriented G f) v))⟩
  ∃ final : ParityState G, Relation.ReflTransGen (ParityRound G) initial final ∧
    final.odd = ∅ ∧ M = final.oriented ∧ U = final.unoriented

/-- Euler traversal of the oriented and unoriented copies. -/
def MixedEuler (G : Network) (M : List (Traversal G)) (U : List (Fin G.q))
    (u : Fin G.n) (ts : List (Traversal G)) : Prop :=
  IsPath G u ts u ∧ ∃ orientations : List (Traversal G),
    (orientations.map Prod.fst).Perm U ∧ (∀ t ∈ orientations, G.directed t.1 = false) ∧
    ts.Perm (M ++ orientations)

def copies (G : Network) (es : List (Fin G.q)) : Network where
  n := G.n
  q := es.length
  tail e := G.tail es[e]
  head e := G.head es[e]
  directed e := G.directed es[e]
  weight e := G.weight es[e]

def liftCopies (G : Network) (es : List (Fin G.q))
    (ts : List (Traversal (copies G es))) : List (Traversal G) :=
  ts.map (fun t => (es[t.1], t.2))

/-- EVENDEGREE uses distances with all directions forgotten. -/
def EvenDegreeAugmentation (G : Network) (es : List (Fin G.q)) : Prop :=
  ∃ (matching : List (Fin G.n × Fin G.n)) (paths : List (List (Traversal G))),
    MinimumMatching (forgetDirections G) (List.finRange G.q) matching ∧
    Expands (forgetDirections G) matching paths ∧
    es = List.finRange G.q ++ paths.flatten.map Prod.fst

def MixedOneRun (G : Network) (u : Fin G.n) (ts : List (Traversal G)) : Prop :=
  ∃ es, EvenDegreeAugmentation G es ∧
    ∃ f : InOutFlow (copies G es), ∃ M U output,
      MinimumFlow (copies G es) f ∧ ParityCorrection (copies G es) f M U ∧
      MixedEuler (copies G es) M U u output ∧ ts = liftCopies G es output

/-- LARGECYCLES pairs odd vertices of U using only original undirected edges. -/
def LargeCyclesAugmentation (G : Network) (U extra : List (Fin G.q)) : Prop :=
  ∃ (pairs : List (Fin G.n × Fin G.n)) (paths : List (List (Traversal G))),
    PerfectMatching G U pairs ∧
    List.Forall₂ (fun p ts => IsPath G p.1 ts p.2 ∧
      ∀ t ∈ ts, G.directed t.1 = false) pairs paths ∧
    (∀ qs ps, PerfectMatching G U qs →
      List.Forall₂ (fun p ts => IsPath G p.1 ts p.2 ∧
        ∀ t ∈ ts, G.directed t.1 = false) qs ps →
      pathCost G paths.flatten ≤ pathCost G ps.flatten) ∧
    extra = paths.flatten.map Prod.fst

def MixedTwoRun (G : Network) (u : Fin G.n) (ts : List (Traversal G)) : Prop :=
  ∃ f extra, MinimumFlow G f ∧ LargeCyclesAugmentation G (flowUnoriented G f) extra ∧
    MixedEuler G (flowBase G f ++ flowExtra G f) (flowUnoriented G f ++ extra) u ts

def GeneralMixedRun (G : Network) (u : Fin G.n) (ts : List (Traversal G)) : Prop :=
  ∃ v ws, (MixedOneRun G u ts ∧ MixedTwoRun G v ws ∧ pathCost G ts ≤ pathCost G ws) ∨
    (MixedTwoRun G u ts ∧ MixedOneRun G v ws ∧ pathCost G ts ≤ pathCost G ws)

def MixedPostman (I : Service) : Prop :=
  Connected I.graph ∧ Nonnegative I.graph ∧ I.vertices = ∅ ∧ I.links = Finset.univ

end VehicleRoutingSurvey.Routing


