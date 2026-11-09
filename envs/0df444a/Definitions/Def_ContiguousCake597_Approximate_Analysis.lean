-- Prove2me | Definitions.Def_ContiguousCake597_Approximate_Analysis
-- name    : ContiguousCake597_Approximate_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:22.688723+00:00
-- url     : https://prove2.me/theorems/c3903e60-9db8-4565-90fa-91231e685fa3
-- title:
--   Real-cut decoder, constructed prices and explicit construction obligations
-- statement:
--   For any complete allocation on $[0,L]$, with real cuts and arbitrary assignment, define
--   $$z_v=\min\{1,\max\{0,\theta_{a_v}-a_vB+13/2\}\},\qquad q_j=\ell_j+\sum_{v:j\in S_v}z_v.$$
--   Here $\ell_j=\theta_j-\theta_{j-1}$. The sets are proved disjoint, so this price is $\ell_j+z_v$ on $S_v$ and $\ell_j$ elsewhere. The incoming sum is $(Az)_u=\sum_{v:v\to u}z_v$. The normalized rational-cut decoder first multiplies the cuts by $L$ and then applies the same clipping formula in rational arithmetic. The target string uses unary numerator 1 and denominator $8000N^4$.
--
--   A single-cycle permutation means that, from every index, iterating the permutation reaches every other index; the singleton identity is included. A function has at most $m$ breakpoints if some set of at most $m$ real thresholds partitions the real line into cells on which it is constant, with the right-hand value at a threshold.
--
--   The construction-obligation predicate explicitly lists the block lower bound 20, total bin occupancy at most $R-8$, (S1), disjointness, the full cyclic list and (S2). The target-obligation predicate lists validity, the common positive scale, six-breakpoint restriction, normalized interval-value identity and preservation of approximate envy-freeness for every real-cut normalized allocation under cut scaling. These are conclusions bundled with Lemma 5, never assumptions of another theorem. This separates the source's proved construction properties from the source's graph hypotheses.
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 6 (PDF 7), §3.1 (S1)/(S2), §3.2 pp.8–10 (PDF 9–11), equations (2)–(3)

import Definitions.Def_ContiguousCake597_Approximate_Construction
import Definitions.Def_ContiguousCake597_Approximate_Search

namespace ContiguousCake597.Approximate

/-- The special cut number lies strictly between 0 and N. -/
def specialPiece (G : HZTractability.ThrGraph) (v : Fin G.n) : Fin (N G) :=
  ⟨a G v - 1, by
    have hR : 0 < R G := by unfold R; positivity
    have ha : a G v < N G := by
      have h := Nat.mul_lt_mul_of_pos_right (show v.val+1 < G.n+1 by omega) hR
      dsimp [a, R, N] at *
      nlinarith
    omega⟩

def followingPiece (G : HZTractability.ThrGraph) (v : Fin G.n) : Fin (N G) :=
  ⟨a G v, by
    have hR : 0 < R G := by unfold R; positivity
    have h := Nat.mul_lt_mul_of_pos_right (show v.val+1 < G.n+1 by omega) hR
    dsimp [a, R, N] at *
    nlinarith⟩

noncomputable def clip (t : ℝ) : ℝ := min 1 (max 0 t)

noncomputable def z (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (v : Fin G.n) : ℝ :=
  clip (T.cuts (specialPiece G v).succ - (a G v : ℝ) * B G + 13/2)

noncomputable def price (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (j : Fin (N G)) : ℝ :=
  T.length j + ∑ v : Fin G.n, if j.val+1 ∈ S G v then z G T v else 0

noncomputable def core (G : HZTractability.ThrGraph) (j : Fin (N G)) : Set ℝ :=
  Set.Icc ((j.val : ℝ) * B G + 10 * N G)
    (((j.val+1 : ℕ) : ℝ) * B G - 10 * N G)

noncomputable def boundarySet (G : HZTractability.ThrGraph) (v : Fin G.n) : Set ℝ :=
  Set.Icc ((boundary G v).1 : ℝ) ((boundary G v).2 : ℝ)

noncomputable def pieceValue (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (i j : Fin (N G)) : ℝ := U G i (T.cuts j.castSucc) (T.cuts j.succ)

def AnalyticAnswer (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G)) : Prop :=
  T.Complete (L G : ℝ) ∧ EnvyFree (U G) (eta G) T

/-- One orbit traverses every index, including the singleton identity cycle. -/
def SingleCycle {n : ℕ} (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, ∃ k : ℕ, (p^[k]) i = j

/-- The paper's A z, with rows = incoming neighbors. -/
noncomputable def incoming (G : HZTractability.ThrGraph) (T : Allocation ℝ (N G))
    (u : Fin G.n) : ℝ :=
  ∑ v : Fin G.n, if G.adj v u then z G T v else 0

/-- S2 in literal cyclic-list form: a_v+1, all S_v ending in a_v,
then its successor outside every set. No construction fact is assumed. -/
def ConstructionFacts (G : HZTractability.ThrGraph) : Prop :=
  (∀ u ∈ List.range' 1 (G.n+1), ∀ v : Fin G.n,
    20 ≤ blockSizeZ G u (v.val+1)) ∧
  (∀ u ∈ List.range' 1 (G.n+1),
    ((binOrder G u).map (blockSizeZ G u)).sum ≤ (R G : ℤ)-8) ∧
  (∀ v, (S G v).card = R G) ∧
  (∀ u v : Fin G.n,
    ((S G v).filter (fun j => j ≤ a G u)).card =
      32 * (u.val+1) + 12 * (entry G (u.val+1) (v.val+1)).toNat) ∧
  (∀ v w : Fin G.n, v ≠ w → Disjoint (S G v) (S G w)) ∧
  (cycleList G).Nodup ∧
  (cycleList G).toFinset = Finset.Icc 1 (N G) ∧
  SingleCycle (pi G) ∧
  (∀ v : Fin G.n,
    a G v ∈ S G v ∧
    (∃ before after : List ℕ,
      cycleList G = before ++ [a G v+1] ++
        ((setList G v).filter (· ≠ a G v)) ++ [a G v] ++ after) ∧
    (∀ w : Fin G.n, a G v+1 ∉ S G w ∧ (pi G (specialPiece G v)).val+1 ∉ S G w) ∧
    pi G (specialPiece G v) ≠ followingPiece G v ∧
    pi G (followingPiece G v) ≠ specialPiece G v)

/-- §3.1 normalization and scaling obligations, separate from all hypotheses. -/
def TargetFacts (G : HZTractability.ThrGraph) : Prop :=
  (targetCake G).Valid ∧ (targetCake G).Restricted ∧ 0 < lambda G ∧
  (∀ i t, 0 ≤ t → t < 1 →
    (targetDensity G i).density t = (lambda G : ℝ) * f G i ((L G : ℝ)*t)) ∧
  (∀ i x y, 0 ≤ x → x ≤ y → y ≤ 1 →
    (targetDensity G i).value x y = U G i ((L G : ℝ)*x) ((L G : ℝ)*y) /
      ((L G : ℝ)+6)) ∧
  (∀ T : Allocation ℝ (N G), T.Complete 1 →
    EnvyFree (fun i => (targetDensity G i).value) (epsilon G : ℝ) T →
    AnalyticAnswer G ⟨fun j => (L G : ℝ) * T.cuts j, T.assign⟩)

/-- A step function with at most m genuine breakpoints, on the whole real line.
The half-open convention assigns each breakpoint its right-hand level. -/
def HasAtMostBreakpoints (g : ℝ → ℝ) (m : ℕ) : Prop :=
  ∃ ks : Finset ℝ, ks.card ≤ m ∧
    ∀ x y : ℝ, (∀ k ∈ ks, x < k ↔ y < k) → g x = g y

/-- The decoder applied to normalized rational cuts, including length rescaling. -/
def decodeRational (G : HZTractability.ThrGraph) (T : Allocation ℚ (N G))
    (v : Fin G.n) : ℚ :=
  min 1 (max 0 ((L G : ℚ) * T.cuts (specialPiece G v).succ -
    (a G v : ℚ) * B G + 13/2))

/-- No rounding of precision: both numerator and denominator are unary. -/
def targetCode (G : HZTractability.ThrGraph) : List Bool :=
  encInput .unary (targetCake G) 1 (8000 * (N G)^4)

end ContiguousCake597.Approximate


