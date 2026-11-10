-- Prove2me | Definitions.Def_ExactKMeans_ProductReduction_Construction
-- name    : ExactKMeans_ProductReduction_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:17:27.805208+00:00
-- url     : https://prove2.me/theorems/7fc6e8bd-0eb8-470c-af19-b48acd3c001e
-- title:
--   Adjacency and balance points and the final decision budget
-- statement:
--   A normalized graph is a simple graph on the abt vertices indexed by color and state. For each distinct color pair and each candidate pair of states, the four adjacency points are y±=y±D and z±=z±D, where D is zero on a nonedge and γ(μ⁺−μ⁻)/(4‖μ⁺−μ⁻‖²) on an edge. The center difference in this formula is evaluated at the prescribed target states; subsequent nearest-center evaluations use the chosen states S. Coincident pairs use consistent negative-center tie breaking.
--
--   The balance vector xᵢ† is the closed formula on printed p.47, including the terms with 4tb²i(i−1)cosβ/2, δ√b[b(a−i)+t²b(i−1)+2(b−1)], 2δ(t²−1)Σⱼ(j−1)eᵢⱼ, and the two signed sums of y+z−2Oᵢ over pairs in different selectors, with their displayed λα and 2λ denominators. There are λ copies at each of Oᵢ±xᵢ†. The final occurrence list X consists of N⁴² copies of each selector occurrence, all adjacency occurrences, and all balance occurrences.
--
--   M(S) is the family of 2a reference centers. E(S) consists of graph edges between the vertices selected by S, each unordered edge counted once. C_adj is the adjacency-plus-balance cost at zero state plus γ|E(0)|. C_bas=aN⁴²B₂+C_adj, and C_tot=C_bas−γ binom(ab,2)+γ/2. The common error expression is 32a⁵b²t⁴α². A multicolored clique selects one state per color with all distinct selected colors adjacent. These definitions contain the construction, not its asserted assignment, gap or complexity properties.
-- source:
--   Bai, Fomin, Xu (2026), Exact Euclidean k-Means: Faster in the Plane, Hard Beyond It, held STOC 2027 submission; SHA-256 89f18334320ba73627305c6f8870ae70fef423ca012f8b71a3052e407c7e62ec, printed pp. 42–53 (PDF 43–54), equations (16)–(20)

import Definitions.Def_ExactKMeans_ProductReduction_Placement

noncomputable section
open scoped Classical
open scoped BigOperators
open Finset

namespace ExactKMeans.ProductReduction

abbrev NormalGraph (p : Parameters) := SimpleGraph (Vertex p)
def selectedEdges (p : Parameters) (G : NormalGraph p) (S : States p) : ℕ :=
  (univ.filter fun cc : Color p × Color p => colorRank p cc.1 < colorRank p cc.2 ∧
    G.Adj (cc.1, S cc.1.1 cc.1.2) (cc.2, S cc.2.1 cc.2.2)).card
def HasMCC (p : Parameters) (G : NormalGraph p) : Prop :=
  ∃ S : States p, ∀ c c' : Color p, c ≠ c' → G.Adj (c, S c.1 c.2) (c', S c'.1 c'.2)
def vertices (p : Parameters) : List (Vertex p) :=
  (((List.ofFn (id : Fin p.a → Fin p.a)).product
    (List.ofFn (id : Fin p.b → Fin p.b))).product (List.ofFn (id : Fin p.t → Fin p.t)))
def candidates (p : Parameters) : List (Candidate p) :=
  ((vertices p).product (vertices p)).filterMap fun v =>
    if h : colorRank p v.1.1 < colorRank p v.2.1 then some ⟨v,h⟩ else none

def displacement (p : Parameters) (G : NormalGraph p) (v : Candidate p) : E p.d :=
  let D := designated p v (targetStates p v) true - designated p v (targetStates p v) false
  if G.Adj v.1.1 v.1.2 then (p.gamma / (4 * ‖D‖^2)) • D else 0
def adjacentPoint (p : Parameters) (G : NormalGraph p) (v : Candidate p)
    (yz sg : Bool) : E p.d := key p v yz + sign sg • displacement p G v
def adjacencyPoints (p : Parameters) (G : NormalGraph p) : List (E p.d) :=
  (candidates p).flatMap fun v => [adjacentPoint p G v true false, adjacentPoint p G v true true,
    adjacentPoint p G v false false, adjacentPoint p G v false true]
/-- The closed form on printed p.47, with source i = i.val + 1. -/
def balanceVector (p : Parameters) (i : Fin p.a) : E p.d :=
  ((4 * p.t * (p.b : ℝ)^2 * ((i.val : ℝ) + 1) * i.val * Real.cos p.beta / 2 +
    p.delta * Real.sqrt p.b * ((p.b : ℝ) * ((p.a : ℝ) - (i.val + 1)) +
      (p.t : ℝ)^2 * p.b * i.val + 2 * ((p.b : ℝ) - 1))) / ((p.lam : ℝ) * p.alpha)) • localBar p i +
  (2 * p.delta * ((p.t : ℝ)^2 - 1) / ((p.lam : ℝ) * p.alpha)) •
    (∑ j : Fin p.b, (j.val : ℝ) • localE p i j) +
  (1 / (2 * (p.lam : ℝ))) •
    (∑ v : Candidate p, if v.1.1.1.1 = i ∧ v.1.1.1.1 < v.1.2.1.1 then
      key p v true + key p v false - 2 • origin p i else 0) -
  (1 / (2 * (p.lam : ℝ))) •
    (∑ v : Candidate p, if v.1.2.1.1 = i ∧ v.1.1.1.1 < v.1.2.1.1 then
      key p v true + key p v false - 2 • origin p i else 0)

def balancePoints (p : Parameters) : List (E p.d) :=
  (List.ofFn fun i : Fin p.a =>
    List.replicate p.lam (origin p i + balanceVector p i) ++
    List.replicate p.lam (origin p i - balanceVector p i)).flatten
def allPoints (p : Parameters) (G : NormalGraph p) : List (E p.d) :=
  (selectorPoints p).flatMap (List.replicate (p.N^42)) ++ adjacencyPoints p G ++ balancePoints p

def Cadj (p : Parameters) (G : NormalGraph p) : ℝ :=
  cost (adjacencyPoints p G ++ balancePoints p) (centers p (fun _ => zeroState p)) +
    p.gamma * selectedEdges p G (fun _ => zeroState p)
def Cbas (p : Parameters) (G : NormalGraph p) : ℝ := (p.a : ℝ) * (p.N : ℝ)^42 * B2 p + Cadj p G
def Ctot (p : Parameters) (G : NormalGraph p) : ℝ :=
  Cbas p G - p.gamma * (Nat.choose (p.a * p.b) 2 : ℝ) + p.gamma / 2
def errorBound (p : Parameters) : ℝ := 32 * (p.a : ℝ)^5 * (p.b : ℝ)^2 * (p.t : ℝ)^4 * p.alpha^2
/-- Consistent tie breaking at the two designated centers; true selects the positive center. -/
def assigned (p : Parameters) (v : Candidate p) (S : States p) (x : E p.d) : Bool :=
  decide (‖x - designated p v S true‖^2 < ‖x - designated p v S false‖^2)
def designatedIndex (p : Parameters) (v : Candidate p) (sg : Bool) : Fin p.a × Bool :=
  if sg then (v.1.2.1.1,true) else (v.1.1.1.1,false)
end ExactKMeans.ProductReduction


