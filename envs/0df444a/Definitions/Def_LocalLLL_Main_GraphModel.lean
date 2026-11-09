-- Prove2me | Definitions.Def_LocalLLL_Main_GraphModel
-- name    : LocalLLL_Main_GraphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:46.499786+00:00
-- url     : https://prove2.me/theorems/b3def7a6-0aae-47a5-94bb-c8fdde5d6a47
-- title:
--   Graph balls, powers, independence and ruling sets
-- statement:
--   Let $G$ be a simple graph. Its closed ball $B_G(v,r)$ consists of vertices reachable from $v$ in at most $r$ edges; $B_G(S,r)$ is the union over centers in $S$. The power $G^r$ joins distinct vertices at distance at most $r$. An independent set has no adjacent distinct pair, an $r$-independent set is independent in $G^r$, and an $r$-ruling set is within distance $r$ of every vertex. Bounded local independence means
--
--   $$\forall v,\ \forall S\subseteq B_G(v,4),\quad S\text{ independent in }G\Longrightarrow |S|\le k.$$
--
--   These objects describe both the original communication network and the graphs used in the reductions. Extended distance excludes vertices in different components from every finite-radius ball. Degree is the cardinality of the neighbor set; finite graphs are supplied by the theorems.
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §2 graph notations and Lemma 2.1, p. 2 (PDF 3); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib

noncomputable section

namespace LocalLLL.Main

/-- Closed balls use extended distance: disconnected vertices are never at finite distance. -/
def ball {V : Type} (G : SimpleGraph V) (v : V) (r : ℕ) : Set V :=
  {u | G.edist v u ≤ r}

def balls {V : Type} (G : SimpleGraph V) (S : Set V) (r : ℕ) : Set V :=
  {u | ∃ s ∈ S, u ∈ ball G s r}

def graphPower {V : Type} (G : SimpleGraph V) (r : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.edist u v ≤ r
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by simpa only [G.edist_comm] using h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

def independent {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v

def separated {V : Type} (G : SimpleGraph V) (r : ℕ) (S : Set V) : Prop :=
  independent (graphPower G r) S

def ruling {V : Type} (G : SimpleGraph V) (r : ℕ) (S : Set V) : Prop :=
  ∀ v, ∃ s ∈ S, v ∈ ball G s r

/-- Cardinality of the neighbor set; on finite graphs this is the usual degree. -/
def degree {V : Type} (G : SimpleGraph V) (v : V) : ℕ := Nat.card {u // G.Adj v u}

def localIndependence {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ v S, S ⊆ ball G v 4 → independent G S → S.ncard ≤ k
end LocalLLL.Main


