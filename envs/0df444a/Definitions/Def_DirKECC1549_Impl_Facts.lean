-- Prove2me | Definitions.Def_DirKECC1549_Impl_Facts
-- name    : DirKECC1549_Impl_Facts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T23:43:44.147038+00:00
-- url     : https://prove2.me/theorems/23368620-5180-454e-af65-dfecd1ccdf6a
-- title:
--   Graph-theoretic facts used by the verified implementation of Algorithm 3
-- statement:
--   The proposition `Facts` bundles, as hypotheses, the graph-theoretic results of the mission on which the verification of the word-RAM implementation of Algorithm 3 relies: the max-flow/min-cut characterization of $\lambda_D(u,v)$ (§2, p.9), the facts that walks between vertices of a strongly connected component stay in it and lift to the induced subgraph, the hitting-set guarantee of Lemma 2 (1) (p.14) and Lemma 4 (Algorithm 3 returns $P_k(G)$, p.17). The final assembly of `lemma_5_impl` supplies them from the corresponding platform theorems.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.3, Algorithm 3 (p.17) and proof of Lemma 5 (pp.18–19); word-RAM model (p.25). Definitions of the verified word-RAM implementation of Algorithm 3.

import Mathlib
import Definitions.Def_DirKECC1549_Main_Alg3
import Definitions.Def_DirKECC1549_Main_HittingSet

set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main

/-- The graph-theoretic results of the mission that the verification of the implementation of
Algorithm 3 relies on, as hypotheses: the max-flow/min-cut characterization of `λ` (§2, p.9),
the two facts on walks inside strongly connected components and induced subgraphs, part (1) of
Lemma 2 (the hitting set guarantee, p.14) and Lemma 4 (correctness of Algorithm 3, p.17). The
final assembly supplies them from the corresponding platform theorems. -/
structure Facts : Prop where
  maxflow : ∀ {n m : ℕ} (D : Fin m → Fin n × Fin n) (u v : Fin n), u ≠ v →
    IsGreatest {q : ℕ | ∃ F : Finset (Fin m), IsUnitFlow D F u v q} (lam D u v) ∧
    IsLeast ((fun S => outCount D S) '' {S : Finset (Fin n) | IsCut S u v}) (lam D u v)
  walks : ∀ {n m : ℕ} (G : Fin m → Fin n × Fin n) (a x y : Fin n),
    StronglyConn G a x → StronglyConn G a y →
    ∀ p, IsWalk G x p y → ∀ e ∈ p, (G e).1 ∈ sccOf G a ∧ (G e).2 ∈ sccOf G a
  lift : ∀ {n m : ℕ} (G : Fin m → Fin n × Fin n) (S : Finset (Fin n)) (x y : Fin n)
    (hx : x ∈ S) (hy : y ∈ S) (p : List (Fin m)), IsWalk G x p y →
    (∀ e ∈ p, (G e).1 ∈ S ∧ (G e).2 ∈ S) →
    ∃ q : List (Fin (inducedEdges G S).card),
      q.map (fun i ↦ ((inducedEdges G S).orderIsoOfFin rfl i).1) = p ∧
      IsWalk (induced G S) (posIn S x hx) q (posIn S y hy)
  l2 : ∀ (n m : ℕ) (G : Fin m → Fin n × Fin n) (k Δ : ℕ) (r : Fin n) (par : Fin n → Fin n),
    2 ≤ k → 1 ≤ Δ → 2 ≤ n → IsSpanningInTree G r par →
    Lemma2Guarantee G r k Δ (hittingSet r par (outDeg G) (Δ / (k - 1)))
  l4 : ∀ {n m : ℕ} (G : Fin m → Fin n × Fin n) (k : ℕ), 1 ≤ k →
    ∀ (P : Fin n → Fin n → Prop), Alg3Run n m G k P → ∀ u v, P u v ↔ KEdgeConnected k G u v

end DirKECC1549.Asm


