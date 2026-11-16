-- Prove2me | Definitions.Def_GreedyRegionGrowing_Layouts_Supplement_Routing
-- name    : GreedyRegionGrowing_Layouts_Supplement_Routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:25:11.713384+00:00
-- url     : https://prove2.me/theorems/6e0aeca7-07a4-43d1-bd62-7bc99d1ea70b
-- title:
--   Pair-commodity routing, node-weighted flow expansion and the operational weighted carver
-- statement:
--   Pair-commodity routing, node-weighted flow expansion and the operational weighted carver. A demand is a symmetric nonnegative function, zero on the diagonal and outside its carrier. Each unordered pair has nonnegative flows in both orientations of the component edges. Conservation holds at every vertex; the sum of the two orientations over commodities is bounded by the congestion. Flow expansion quantifies over all demands with incident totals bounded by the node weights. Shortest-path distances are minima of lengths of paths with at most n vertices; connected nonnegative instances guarantee these minima exist. The definitions include (5.1), (5.3), the exact weighted volumes and deficits, annuli and persistent pointers. Algorithm 2 traces record only stability searches, maximum keys and the exact event-free radius inequality. No termination or performance guarantee is a field. Fixed binary codes specify node weights, deleted edges and the certificate-or-set output.
-- source:
--   Aditya Anand, Greedy Region Growing: Improved Approximations for Cutwidth, Pathwidth, Flow-Expander Decomposition, and More, STOC 2027 submission #506 (October 2026). Citation basis: published (canonical held submission); 46 pages; printed page = PDF page throughout (offset 0); no arXiv version. §3.1 p.17; §5 pp.24–28, Eqs. (5.1),(5.3), Algorithm 2; Appendix D.3 p.44

import Mathlib
import Definitions.Def_GreedyRegionGrowing_Layouts_Foundation

noncomputable section
open Finset QAlgorithms.Complexity

namespace GreedyRegionGrowing.Layouts.Supplement
attribute [local instance] Classical.propDecidable

/-- §3.1 and Appendix D.3: exactly one commodity for each unordered pair. -/
def pairs {n : ℕ} (U : Finset (Fin n)) := (U ×ˢ U).filter (fun p => p.1 < p.2)

def IsDemand {n : ℕ} (U : Finset (Fin n)) (D : Fin n → Fin n → ℝ) : Prop :=
  (∀ u v, 0 ≤ D u v ∧ D u v = D v u) ∧ (∀ u, D u u = 0) ∧
  ∀ u v, u ∉ U ∨ v ∉ U → D u v = 0

def Respects {n : ℕ} (U : Finset (Fin n)) (A : Fin n → ℚ)
    (D : Fin n → Fin n → ℝ) : Prop :=
  IsDemand U D ∧ ∀ u ∈ U, ∑ v ∈ U, D u v ≤ (A u : ℝ)

/-- Nonnegative flows in both edge orientations, with per-commodity conservation and total load.
No edge outside the induced component can carry a commodity. -/
def Routable {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (D : Fin n → Fin n → ℝ) (q : ℝ) : Prop :=
  ∃ f : (Fin n × Fin n) → Fin n → Fin n → ℝ,
    (∀ p x y, 0 ≤ f p x y) ∧
    (∀ p x y, ¬ (x ∈ U ∧ y ∈ U ∧ G.Adj x y) → f p x y = 0) ∧
    (∀ p ∈ pairs U, ∀ x ∈ U,
      (∑ y ∈ U, (f p x y - f p y x)) =
        if x = p.1 then D p.1 p.2 else if x = p.2 then -D p.1 p.2 else 0) ∧
    ∀ e ∈ edges G U, ∑ p ∈ pairs U, (f p e.1 e.2 + f p e.2 e.1) ≤ q

def FlowExpanding {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    (A : Fin n → ℚ) (phi : ℚ) : Prop :=
  ∀ D, Respects U A D → Routable G U D (1/(phi : ℝ))

def degreeWeight {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (u : Fin n) : ℚ :=
  (U.filter (fun v => G.Adj u v)).card

def FlowExpander {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (phi : ℚ) :=
  FlowExpanding G U (degreeWeight G U) phi

def weight {n : ℕ} (A : Fin n → ℚ) (U : Finset (Fin n)) : ℚ := ∑ v ∈ U, A v

def productDemand {n : ℕ} (A : Fin n → ℚ) : Fin n → Fin n → ℝ := fun u v =>
  if u = v then 0 else (A u : ℝ) * (A v : ℝ) / (weight A univ : ℝ)

/-- Delete exactly the sorted unordered pairs of C. -/
def remaining {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n × Fin n)) :
    SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ (u,v) ∉ C ∧ (v,u) ∉ C
  symm := ⟨by intro u v h; exact ⟨G.symm.symm u v h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro u h; exact G.loopless.irrefl u h.1⟩

def nodeWeightCode {n : ℕ} (A : Fin n → ℚ) : Str :=
  (List.finRange n).flatMap (fun v => ratCode (A v))

def edgeSetCode {n : ℕ} (C : Finset (Fin n × Fin n)) : Str :=
  listCode (fun e => natCode e.1.val ++ natCode e.2.val) (((List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => (u,v)))).filter (fun e => decide (e ∈ C)))

/-- Output tag true certifies expansion; tag false carries the selected vertex set. -/
def certificateCode {n : ℕ} (S : Option (Finset (Fin n))) : Str :=
  match S with
  | none => [true]
  | some X => [false] ++ setCode X

def loglog (x : ℝ) : ℝ := max 1 (Real.log (Real.log x))

/-- Lengths of simple candidate walks, enumerated on the finite vertex set. -/
def pathLength {n : ℕ} (ell : Fin n → Fin n → ℚ) : List (Fin n) → ℚ
  | [] => 0
  | [_] => 0
  | u::v::xs => ell u v + pathLength ell (v::xs)

def pathLengths {n : ℕ} (G : SimpleGraph (Fin n)) (ell : Fin n → Fin n → ℚ)
    (u v : Fin n) : Finset ℚ :=
  ((range (n+1)).biUnion (fun k =>
    (univ : Finset (Fin k → Fin n)).image (fun f => List.ofFn f))).filter
      (fun p => p.head? = some u ∧ p.getLast? = some v ∧ p.IsChain G.Adj) |>.image (pathLength ell)

/-- Nonnegative shortest-path metric. The minimum is over paths with at most n vertices;
zero is used only if no path exists, a case excluded by LengthInstance. -/
def shortest {n : ℕ} (G : SimpleGraph (Fin n)) (ell : Fin n → Fin n → ℚ)
    (u v : Fin n) : ℚ :=
  let P := pathLengths G ell u v
  if h : P.Nonempty then P.min' h else 0

/-- Section 5 standing assumptions and (5.1); no rounding conclusion is assumed. -/
def LengthInstance {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (phi : ℚ) (ell : Fin n → Fin n → ℚ) : Prop :=
  G.Connected ∧ (∀ v, 1 ≤ A v) ∧ 0 < phi ∧
  (∀ u v, 0 ≤ ell u v ∧ ell u v = ell v u) ∧
  (∑ e ∈ edges G univ, ell e.1 e.2) ≤ 1 ∧
  (1/(2*(phi : ℝ))) < ∑ p ∈ pairs (univ : Finset (Fin n)),
    productDemand A p.1 p.2 * (shortest G ell p.1 p.2 : ℝ)

def radiusR {n : ℕ} (A : Fin n → ℚ) (phi : ℚ) : ℚ := 1/(16*phi*weight A univ)

def SmallBalls {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (phi : ℚ) (ell : Fin n → Fin n → ℚ) : Prop :=
  ∀ u, weight A (ball (shortest G ell) univ u (radiusR A phi : ℝ)) < weight A univ / 3

def weightedVolume {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (ell : Fin n → Fin n → ℚ) (U : Finset (Fin n)) (u : Fin n) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else
  let B := ball (shortest G ell) U u r
  (weight A B : ℝ)/(weight A univ : ℝ) +
    (∑ e ∈ edges G B, (ell e.1 e.2 : ℝ)) +
    ∑ e ∈ cut G U B, if e.1 ∈ B then r-(shortest G ell u e.1 : ℝ)
      else r-(shortest G ell u e.2 : ℝ)

def deficitF {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (ell : Fin n → Fin n → ℚ) (U : Finset (Fin n)) (u : Fin n) (r : ℝ) : ℝ :=
  Real.log (2*Real.exp 1 / weightedVolume G A ell U u r)

def gamma {n : ℕ} (A : Fin n → ℚ) (S : Finset (Fin n)) : ℝ :=
  Real.log (Real.exp 1 * (weight A univ : ℝ)/(weight A S : ℝ))

def kappa {n : ℕ} (A : Fin n → ℚ) : ℕ :=
  2 * (Int.ceil (Real.logb 2 (Real.log (2*Real.exp 1*(weight A univ : ℝ))))).toNat + 1

def annulus {n : ℕ} (A : Fin n → ℚ) (phi : ℚ) (j : ℕ) : ℝ :=
  (radiusR A phi : ℝ) - j*(radiusR A phi : ℝ)/(2*kappa A)

def Stable {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ) (phi : ℚ)
    (ell : Fin n → Fin n → ℚ) (U : Finset (Fin n)) (u : Fin n) (j : ℕ) : Prop :=
  deficitF G A ell U u (annulus A phi j) ≤ 2*deficitF G A ell U u (annulus A phi (j-1)) ∧
  gamma A (ball (shortest G ell) U u (annulus A phi j)) ≤
    2*gamma A (ball (shortest G ell) U u (annulus A phi (j-1)))

structure WeightedFrame (n : ℕ) where
  U : Finset (Fin n)
  pointer : Fin n → ℕ
  center : Fin n
  radius : ℝ

namespace WeightedFrame
variable {n : ℕ}
def X (f : WeightedFrame n) (G : SimpleGraph (Fin n)) (ell : Fin n → Fin n → ℚ) :=
  ball (shortest G ell) f.U f.center f.radius

def V (f : WeightedFrame n) (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (ell : Fin n → Fin n → ℚ) := weightedVolume G A ell f.U f.center f.radius

/-- The while-loop increases a pointer through precisely the unstable annuli; no bound κ is imposed. -/
def Operational (f : WeightedFrame n) (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (phi : ℚ) (ell : Fin n → Fin n → ℚ) (old : Fin n → ℕ) : Prop :=
  f.center ∈ f.U ∧
  (∀ u ∈ f.U, old u ≤ f.pointer u ∧ Stable G A phi ell f.U u (f.pointer u) ∧
    ∀ j, old u ≤ j → j < f.pointer u → ¬ Stable G A phi ell f.U u j) ∧
  (∀ u ∈ f.U,
    weight A (ball (shortest G ell) f.U u (annulus A phi (f.pointer u-1))) ≤
    weight A (ball (shortest G ell) f.U f.center (annulus A phi (f.pointer f.center-1)))) ∧
  (let a := annulus A phi (f.pointer f.center)
   let b := annulus A phi (f.pointer f.center-1)
   a < f.radius ∧ f.radius < b ∧
   f.radius ∉ (f.U.image (fun v => (shortest G ell f.center v : ℝ))) ∧
   ((cut G f.U (f.X G ell)).card : ℝ) ≤ 4/(b-a)*f.V G A ell*
     deficitF G A ell f.U f.center f.radius)
end WeightedFrame

def WeightedRunFrom {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ) (phi : ℚ)
    (ell : Fin n → Fin n → ℚ) : Finset (Fin n) → (Fin n → ℕ) → List (WeightedFrame n) → Prop
  | _, _, [] => True
  | U, old, f::fs => f.U = U ∧ f.Operational G A phi ell old ∧
    WeightedRunFrom G A phi ell (U \ f.X G ell) f.pointer fs

def WeightedRun {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ) (phi : ℚ)
    (ell : Fin n → Fin n → ℚ) (fs : List (WeightedFrame n)) :=
  WeightedRunFrom G A phi ell univ (fun _ => 1) fs

def WeightedComplete {n : ℕ} (G : SimpleGraph (Fin n)) (ell : Fin n → Fin n → ℚ)
    (fs : List (WeightedFrame n)) : Prop :=
  match fs.getLast? with
  | none => n = 0
  | some f => f.U \ f.X G ell = ∅

/-- Line 7 of Algorithm 2: every minimizing piece is an allowed returned set. -/
def WeightedOutput {n : ℕ} (G : SimpleGraph (Fin n)) (A : Fin n → ℚ)
    (ell : Fin n → Fin n → ℚ) (fs : List (WeightedFrame n)) (S : Finset (Fin n)) : Prop :=
  (∃ f ∈ fs, S = f.X G ell) ∧
  ∀ f ∈ fs, ((cut G univ S).card : ℝ)/((weight A S : ℝ)*gamma A S) ≤
    ((cut G univ (f.X G ell)).card : ℝ)/((weight A (f.X G ell) : ℝ)*gamma A (f.X G ell))

/-- Coded promise input for Lemmas 5.3 and 5.4, lengths included. -/
structure RoundingInput where
  n : ℕ
  G : SimpleGraph (Fin n)
  A : Fin n → ℚ
  phi : ℚ
  ell : Fin n → Fin n → ℚ
  valid : LengthInstance G A phi ell

def roundingCode (I : RoundingInput) : Str :=
  graphCode I.G ++ nodeWeightCode I.A ++ ratCode I.phi ++
    (List.finRange I.n).flatMap (fun u => (List.finRange I.n).flatMap (fun v => ratCode (I.ell u v)))

structure HeavyInput extends RoundingInput where
  Y : Finset (Fin n)
  heavy : weight A univ / 3 ≤ weight A Y
  diameter : ∀ u ∈ Y, ∀ v ∈ Y, shortest G ell u v ≤ 2*radiusR A phi

end GreedyRegionGrowing.Layouts.Supplement


