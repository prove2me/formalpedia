-- Prove2me | Definitions.Def_KikuchiMoore_Moore_Bundles
-- name    : KikuchiMoore_Moore_Bundles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:59.622623+00:00
-- url     : https://prove2.me/theorems/92eab47d-346e-4889-9de2-eb741fd6c85e
-- title:
--   Spread bundles and simultaneous maximal packing
-- statement:
--   For $1\le q\le k-1$, let $h_q=\max(2,\lceil(n/\ell)^{q-k/2}\rceil)$. A spread bundle has exactly $h_q$ edges sharing a center of cardinality $k-q$. Its residuals are $R_F=F\setminus U_B$, each of cardinality $q$. For each nonempty proper subset $T$ of a residual, strictly fewer than $h_{q-|T|}$ bundle members have residual containing $T$. A packing is a finite collection of such bundles whose edge families are pairwise disjoint, and it is maximal under inclusion among all such collections over all residual sizes. Packed edges, edges at size $q$, and unabsorbed edges define $m_+$, $m_q$, and $m_0$. Dominance records $m_+>0$ and $m_q\ge m_+/(k-1)$. Residual-disjoint pairs are unordered two-element subfamilies. No parity or central-range assumption is built into this object.
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Definitions and constructions, Sections 3–5, printed p. 16 = PDF p. 16, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Definitions.Def_KikuchiMoore_Moore_Core

noncomputable section
open scoped BigOperators

namespace KikuchiMoore.Moore

def bundleSize (n k l q : ℕ) : ℕ :=
  max 2 ⌈Real.rpow ((n : ℝ) / l) ((q : ℝ) - (k : ℝ) / 2)⌉₊

structure Bundle (n : ℕ) where
  center : Finset (Fin n)
  members : Finset (Finset (Fin n))
  deriving DecidableEq, Fintype

def residual {n : ℕ} (B : Bundle n) (F : Finset (Fin n)) := F \ B.center

def SpreadBundle {n : ℕ} (H : Hypergraph n) (k l q : ℕ) (B : Bundle n) : Prop :=
  1 ≤ q ∧ q ≤ k - 1 ∧ B.center.card = k - q ∧
  B.members ⊆ edges H ∧ B.members.card = bundleSize n k l q ∧
  (∀ F ∈ B.members, B.center ⊆ F ∧ (residual B F).card = q) ∧
  ∀ F ∈ B.members, ∀ T ⊆ residual B F, 1 ≤ T.card → T.card < q →
    (B.members.filter (fun J => T ⊆ residual B J)).card < bundleSize n k l (q - T.card)

def Packing {n : ℕ} (H : Hypergraph n) (k l : ℕ) (P : Finset (Bundle n)) : Prop :=
  (∀ B ∈ P, ∃ q, SpreadBundle H k l q B) ∧
  ∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B.members C.members

def MaximalPacking {n : ℕ} (H : Hypergraph n) (k l : ℕ) (P : Finset (Bundle n)) : Prop :=
  Packing H k l P ∧ ∀ Q, Packing H k l Q → P ⊆ Q → Q = P

def packed {n : ℕ} (P : Finset (Bundle n)) := P.biUnion Bundle.members

def packedAt {n : ℕ} (k q : ℕ) (P : Finset (Bundle n)) :=
  (P.filter (fun B => B.center.card = k - q)).biUnion Bundle.members

def remainder {n : ℕ} (H : Hypergraph n) (P : Finset (Bundle n)) : ℕ :=
  (edges H \ packed P).card

def Dominant {n : ℕ} (k q : ℕ) (P : Finset (Bundle n)) : Prop :=
  1 ≤ q ∧ q ≤ k - 1 ∧ 0 < (packed P).card ∧
  ((packed P).card : ℝ) / ((k : ℝ) - 1) ≤ (packedAt k q P).card

def disjointPairs {n : ℕ} (B : Bundle n) : Finset (Finset (Finset (Fin n))) := by
  classical
  exact (B.members.powersetCard 2).filter fun Q =>
    ∀ F ∈ Q, ∀ J ∈ Q, F ≠ J → Disjoint (residual B F) (residual B J)

end KikuchiMoore.Moore


