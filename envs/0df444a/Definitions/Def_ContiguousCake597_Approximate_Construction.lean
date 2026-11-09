-- Prove2me | Definitions.Def_ContiguousCake597_Approximate_Construction
-- name    : ContiguousCake597_Approximate_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:15.806163+00:00
-- url     : https://prove2.me/theorems/7fa514f5-92a2-4426-8e4f-13d4ce5e9e5d
-- title:
--   The explicit threshold-game cake construction and normalized target
-- statement:
--   Let $G$ be a directed graph on $s$ vertices. The published graph convention is $G(u,v)$ for an arc $u\to v$; the paper's matrix is its transpose, $A_{vu}=1$ for that arc. Loops and sinks are allowed. The definitions are total on raw graphs; the lemmas assume $s\ge1$ and indegree at most two, with no outdegree restriction.
--
--   The construction sets
--   $$R=32(s+1),\quad N=32(s+1)^2,\quad B=40N,\quad L=NB,\quad a_v=vR.$$
--   In bin $u$, the block for $S_v$ has integer size $32+12A_{uv}-12A_{u-1,v}$, with sentinel rows $A_{0v}=A_{s+1,v}=0$. Blocks fill the right end. They are ordered increasingly except that $S_u$ is last when $u\le s$. The cyclic list concatenates $a_v+1$, the increasing list $S_v\setminus\{a_v\}$, and $a_v$, for each player, then the unlisted indices increasingly; its next-element permutation is $\pi$.
--
--   The core bonus of length $d$ in slot $j$ is centered at $jB-B/2$. Each density is 1 plus the indicator of the union of its bonuses. Agent $a_v+1$ has own/next/boundary lengths $(2,3,1)$; agent $a_v$ has $(5/2,5/2,1)$; all others have $(3,3,0)$. The boundary interval is $J_v=[a_vB-13/2,a_vB-11/2]$. Define $U_i([x,y])$ as $y-x$ plus the sum of the bonus-overlap lengths; the disjointness and integral agreement are conclusions, not hypotheses.
--
--   The actual normalized finite density data are computed by sorting and deduplicating all scaled bonus endpoints, adding 0 and 1, and sampling each intervening interval at its midpoint. The target parameters are
--   $$\lambda=\frac L{L+6},\quad \rho_i(t)=\lambda f_i(Lt),\quad \varepsilon=\frac1{8000N^4},\quad\eta=\frac1{100N^2}.$$
--   This provides concrete rational input data, not a density chosen by an existential specification.
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 5 (PDF 6), §3.1, continuing pp.6–8 (PDF 7–9)

import Definitions.Def_ContiguousCake597_Approximate_Model
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_IsThresholdSol

namespace ContiguousCake597.Approximate

def R (G : HZTractability.ThrGraph) : ℕ := 32 * (G.n+1)
def N (G : HZTractability.ThrGraph) : ℕ := 32 * (G.n+1)^2
def B (G : HZTractability.ThrGraph) : ℕ := 40 * N G
def L (G : HZTractability.ThrGraph) : ℕ := N G * B G
def a (G : HZTractability.ThrGraph) (v : Fin G.n) : ℕ := (v.val+1) * R G

/-- One-based matrix A_uv: the published graph has the opposite argument order.
Rows 0 and s+1 are zero. Natural subtraction occurs only under a strict bound. -/
def entry (G : HZTractability.ThrGraph) (u v : ℕ) : ℤ :=
  if hu : 0 < u ∧ u ≤ G.n then
    if hv : 0 < v ∧ v ≤ G.n then
      if G.adj ⟨v-1, by omega⟩ ⟨u-1, by omega⟩ then 1 else 0
    else 0
  else 0

def blockSizeZ (G : HZTractability.ThrGraph) (u v : ℕ) : ℤ :=
  32 + 12 * entry G u v - 12 * entry G (u-1) v

/-- Increasing order, except that player u is last in bin u. -/
def binOrder (G : HZTractability.ThrGraph) (u : ℕ) : List ℕ :=
  let vs := List.range' 1 G.n
  if 1 ≤ u ∧ u ≤ G.n then vs.filter (· ≠ u) ++ [u] else vs

/-- Blocks fill the RIGHT end of a bin. Offsets are computed in integers first. -/
def block (G : HZTractability.ThrGraph) (u v : ℕ) : List ℕ :=
  let order := binOrder G u
  let later := (order.drop (order.idxOf v + 1)).map (blockSizeZ G u)
  let right : ℤ := (u * R G : ℕ) - later.sum
  let size := blockSizeZ G u v
  (List.range size.toNat).map fun k => (right - size + 1 + (k : ℤ)).toNat

def setList (G : HZTractability.ThrGraph) (v : Fin G.n) : List ℕ :=
  ((List.range' 1 (G.n+1)).flatMap fun u => block G u (v.val+1)).mergeSort (· ≤ ·)

def S (G : HZTractability.ThrGraph) (v : Fin G.n) : Finset ℕ := (setList G v).toFinset

/-- The printed cyclic list, with increasing order inside each S_v minus a_v. -/
def cyclePrefix (G : HZTractability.ThrGraph) : List ℕ :=
  (List.finRange G.n).flatMap fun v =>
    [a G v + 1] ++ (setList G v).filter (· ≠ a G v) ++ [a G v]

def cycleList (G : HZTractability.ThrGraph) : List ℕ :=
  cyclePrefix G ++ (List.range' 1 (N G)).filter (fun j => j ∉ cyclePrefix G)

/-- Dropping invalid indices is irrelevant on every valid construction; the
S1/S2 obligations below assert that no such indices occur. -/
def cycleIndices (G : HZTractability.ThrGraph) : List (Fin (N G)) :=
  (cycleList G).filterMap fun j =>
    if h : 0 < j ∧ j ≤ N G then some ⟨j-1, by omega⟩ else none

def pi (G : HZTractability.ThrGraph) : Equiv.Perm (Fin (N G)) :=
  (cycleIndices G).formPerm

def ownBonus (G : HZTractability.ThrGraph) (i : Fin (N G)) : ℚ :=
  if ∃ v : Fin G.n, i.val+1 = a G v + 1 then 2 else
    if ∃ v : Fin G.n, i.val+1 = a G v then 5/2 else 3

def nextBonus (G : HZTractability.ThrGraph) (i : Fin (N G)) : ℚ :=
  if ∃ v : Fin G.n, i.val+1 = a G v then 5/2 else 3

def centered (G : HZTractability.ThrGraph) (j : ℕ) (d : ℚ) : ℚ × ℚ :=
  ((j : ℚ) * B G - (B G : ℚ)/2 - d/2,
   (j : ℚ) * B G - (B G : ℚ)/2 + d/2)

def boundary (G : HZTractability.ThrGraph) (v : Fin G.n) : ℚ × ℚ :=
  ((a G v : ℚ) * B G - 13/2, (a G v : ℚ) * B G - 11/2)

def bonuses (G : HZTractability.ThrGraph) (i : Fin (N G)) : List (ℚ × ℚ) :=
  [centered G (i.val+1) (ownBonus G i),
   centered G ((pi G i).val+1) (nextBonus G i)] ++
    ((List.finRange G.n).filter (fun v => i.val+1 = a G v ∨ i.val+1 = a G v+1)).map
      (boundary G)

/-- Indicator of the UNION of half-open bonuses. Endpoints never create density 3. -/
def fRat (G : HZTractability.ThrGraph) (i : Fin (N G)) (t : ℚ) : ℚ :=
  if (bonuses G i).any (fun ab => decide (ab.1 ≤ t ∧ t < ab.2)) then 2 else 1

noncomputable def f (G : HZTractability.ThrGraph) (i : Fin (N G)) (t : ℝ) : ℝ :=
  if ∃ ab ∈ bonuses G i, (ab.1 : ℝ) ≤ t ∧ t < (ab.2 : ℝ) then 2 else 1

noncomputable def overlap (a b c d : ℝ) : ℝ := max 0 (min b d - max a c)

/-- On the constructed (disjoint) bonuses this is exactly the interval integral
of f. No integrability hypothesis is needed for these finite step functions. -/
noncomputable def U (G : HZTractability.ThrGraph) (i : Fin (N G)) (x y : ℝ) : ℝ :=
  (y-x) + ((bonuses G i).map fun ab => overlap x y (ab.1 : ℝ) (ab.2 : ℝ)).sum

def epsilon (G : HZTractability.ThrGraph) : ℚ := 1 / (8000 * (N G : ℚ)^4)
noncomputable def eta (G : HZTractability.ThrGraph) : ℝ := 1 / (100 * (N G : ℝ)^2)
def lambda (G : HZTractability.ThrGraph) : ℚ := (L G : ℚ) / ((L G : ℚ)+6)

/-- Explicit sorted finite rational data for the NORMALIZED density. -/
def targetKnots (G : HZTractability.ThrGraph) (i : Fin (N G)) : List ℚ :=
  (([0,1] : List ℚ) ++ (bonuses G i).flatMap (fun (ab : ℚ × ℚ) =>
    [ab.1 / (L G : ℚ), ab.2 / (L G : ℚ)])).mergeSort (· ≤ ·) |>.dedup

def targetDensity (G : HZTractability.ThrGraph) (i : Fin (N G)) : StepDensity :=
  let ks := targetKnots G i
  ⟨ks, (List.range (ks.length-1)).map fun k =>
    lambda G * fRat G i ((L G : ℚ) * (ks[k]?.getD 0 + ks[k+1]?.getD 0) / 2)⟩

def targetCake (G : HZTractability.ThrGraph) : CakeData :=
  ⟨N G, targetDensity G⟩

end ContiguousCake597.Approximate


