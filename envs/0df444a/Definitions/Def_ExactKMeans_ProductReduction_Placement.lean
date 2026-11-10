-- Prove2me | Definitions.Def_ExactKMeans_ProductReduction_Placement
-- name    : ExactKMeans_ProductReduction_Placement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:16:44.421649+00:00
-- url     : https://prove2.me/theorems/27ebe191-8b09-4ab3-b586-866b6d62b2b0
-- title:
--   Placed selectors and key-position equations
-- statement:
--   Selector i has origin Oᵢ=4i ê. Its averaged vectors are ēᵢ=cosθᵢ ē−sinθᵢ ē⊥ and ēᵢ⊥=sinβ(sinθᵢ ē+cosθᵢ ē⊥)+cosβ ê. Local basis vectors are exactly those of equation (9) and its following displayed formulas. Equation (10) places every selector occurrence at Oᵢ plus its local displacement, and equation (11) gives its two reference centers. Colors are pairs (i,j), and vertices add one of the t states.
--
--   Candidate pairs are ordered by distinct colors in lexicographic order. The designated centers are the negative center of the first selector and the positive center of the second. In defining a key pair, the two target mini-selectors have their prescribed states and every other mini-selector has state zero. The target perpendicular readings at y,z are respectively δ,−δ for the first target and −tδ−4(i″−i′)√b cosβ for the second. All other perpendicular readings in these selectors are zero. Both positions are equidistant from their two designated reference centers. Their horizontal norms are at most N³(δ+i″−i′), and their heights differ from 2(i′+i″) by at most 1/N.
--
--   For one selector the key positions are the explicit vectors in the proof of Lemma 17; for different selectors they are selected from the equations (12)–(14), whose unique solution is established in that proof. The norm bounds are predicates to prove, not assumed properties of the chosen positions. All actual selector indices are source indices i=i.val+1. State zero is the middle index because t is odd.
-- source:
--   Bai, Fomin, Xu (2026), Exact Euclidean k-Means: Faster in the Plane, Hard Beyond It, held STOC 2027 submission; SHA-256 89f18334320ba73627305c6f8870ae70fef423ca012f8b71a3052e407c7e62ec, printed pp. 34–38 (PDF 35–39), equations (9)–(15), Definition 5

import Definitions.Def_ExactKMeans_ProductReduction_Selector

noncomputable section
open scoped Classical
open scoped BigOperators
open Finset

namespace ExactKMeans.ProductReduction

def origin (p : Parameters) (i : Fin p.a) : E p.d := (4 * ((i.val : ℝ) + 1)) • axis p
def localBar (p : Parameters) (i : Fin p.a) : E p.d :=
  Real.cos (p.theta i) • ebar p - Real.sin (p.theta i) • epbar p
def localBarP (p : Parameters) (i : Fin p.a) : E p.d :=
  Real.sin p.beta • (Real.sin (p.theta i) • ebar p + Real.cos (p.theta i) • epbar p) +
    Real.cos p.beta • axis p
def localE (p : Parameters) (i : Fin p.a) (j : Fin p.b) : E p.d :=
  Real.cos (p.theta i) • (e p j - (1 / Real.sqrt p.b) • ebar p) +
  Real.sin (p.theta i) • (ep p j - (1 / Real.sqrt p.b) • epbar p) +
  (1 / Real.sqrt p.b) • localBar p i
def localEP (p : Parameters) (i : Fin p.a) (j : Fin p.b) : E p.d :=
  (-Real.sin (p.theta i)) • (e p j - (1 / Real.sqrt p.b) • ebar p) +
  Real.cos (p.theta i) • (ep p j - (1 / Real.sqrt p.b) • epbar p) +
  (1 / Real.sqrt p.b) • localBarP p i

def reference (p : Parameters) (i : Fin p.a) (s : State p) (sg : Bool) : E p.d :=
  origin p i + (sign sg * p.r / Real.sqrt p.b) •
    ∑ j, rot p.alpha (stateValue p (s j)) (localE p i j) (localEP p i j)
def centers (p : Parameters) (S : States p) : Fin p.a × Bool → E p.d :=
  fun (i, sg) => reference p i (S i) sg

def placedPoint (p : Parameters) (i : Fin p.a) : Occ p → E p.d
  | .inl (sg, _) => origin p i + (sign sg / Real.sqrt p.b) • localBar p i
  | .inr (sg, j, l) => origin p i + sign sg •
      rotp p.alpha (arcValue p l) (localE p i j) (localEP p i j)
def selectorPoints (p : Parameters) : List (E p.d) :=
  (List.ofFn fun i : Fin p.a => (List.ofFn fun j : Fin (p.b * p.lam) => placedPoint p i (.inl (true,j))) ++
    (List.ofFn fun j : Fin (p.b * p.lam) => placedPoint p i (.inl (false,j))) ++
    ((List.ofFn fun j : Fin p.b => (List.ofFn fun l : Fin (p.t-1) =>
      [placedPoint p i (.inr (true,j,l)), placedPoint p i (.inr (false,j,l))]).flatten).flatten)).flatten
abbrev Color (p : Parameters) := Fin p.a × Fin p.b
abbrev Vertex (p : Parameters) := Color p × Fin p.t
def colorRank (p : Parameters) (c : Color p) : ℕ := c.1.val * p.b + c.2.val
abbrev Candidate (p : Parameters) :=
  {v : Vertex p × Vertex p // colorRank p v.1.1 < colorRank p v.2.1}
def targetStates (p : Parameters) (v : Candidate p) : States p := fun i j =>
  if (i, j) = v.1.1.1 then v.1.1.2 else
  if (i, j) = v.1.2.1 then v.1.2.2 else (zeroState p) j

def designated (p : Parameters) (v : Candidate p) (S : States p) (sg : Bool) : E p.d :=
  if sg then reference p v.1.2.1.1 (S v.1.2.1.1) true
  else reference p v.1.1.1.1 (S v.1.1.1.1) false
/-- Equations (12)--(14), separately for y (true) and z (false). -/
def KeyEquations (p : Parameters) (v : Candidate p) (sg : Bool) (x : E p.d) : Prop :=
  let c := v.1.1.1; let c' := v.1.2.1
  inner ℝ (x - origin p c.1)
      (rotp p.alpha (stateValue p v.1.1.2) (localE p c.1 c.2) (localEP p c.1 c.2)) = sign sg * p.delta ∧
  inner ℝ (x - origin p c'.1)
      (rotp p.alpha (stateValue p v.1.2.2) (localE p c'.1 c'.2) (localEP p c'.1 c'.2)) =
      -(p.t : ℝ) * p.delta - 4 * ((c'.1.val : ℝ) - c.1.val) * Real.sqrt p.b * Real.cos p.beta ∧
  (∀ i j, (i = c.1 ∨ i = c'.1) → (i,j) ≠ c → (i,j) ≠ c' →
    inner ℝ (x - origin p i) (localEP p i j) = 0) ∧
  ‖x - designated p v (targetStates p v) false‖^2 =
    ‖x - designated p v (targetStates p v) true‖^2

def KeyBounds (p : Parameters) (v : Candidate p) (x : E p.d) : Prop :=
  ‖x - (inner ℝ x (axis p)) • axis p‖ ≤ (p.N : ℝ)^3 *
    (p.delta + (v.1.2.1.1.val : ℝ) - v.1.1.1.1.val) ∧
  |inner ℝ x (axis p) - 2 * ((v.1.1.1.1.val : ℝ) + 1 + (v.1.2.1.1.val : ℝ) + 1)| ≤ 1 / p.N

def KeyPair (p : Parameters) (v : Candidate p) (y z : E p.d) : Prop :=
  KeyEquations p v true y ∧ KeyEquations p v false z ∧ KeyBounds p v y ∧ KeyBounds p v z
/-- The explicit same-selector solution and the unique linear-system solution otherwise.
No existence or bound from Lemma 17 is assumed. -/
def key (p : Parameters) (v : Candidate p) (sg : Bool) : E p.d :=
  if v.1.1.1.1 = v.1.2.1.1 then
    origin p v.1.1.1.1 + (sign sg * p.delta) •
      rotp p.alpha (stateValue p v.1.1.2) (localE p v.1.1.1.1 v.1.1.1.2) (localEP p v.1.1.1.1 v.1.1.1.2) -
    ((p.t : ℝ) * p.delta) •
      rotp p.alpha (stateValue p v.1.2.2) (localE p v.1.2.1.1 v.1.2.1.2) (localEP p v.1.2.1.1 v.1.2.1.2)
  else Classical.epsilon (KeyEquations p v sg)
end ExactKMeans.ProductReduction


