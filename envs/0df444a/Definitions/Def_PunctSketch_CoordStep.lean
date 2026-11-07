-- Prove2me | Definitions.Def_PunctSketch_CoordStep
-- name    : PunctSketch_CoordStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:35.328295+00:00
-- url     : https://prove2.me/theorems/ecb0b313-8d2d-4dfc-8a4b-f4fc49a19f5b
-- title:
--   The coordinator procedure of §5.4
-- statement:
--   The certificate procedure is a transition relation over an arbitrary oracle $\mathcal T$, whose value $\mathcal T(F)$ is a set of pairs or FAIL. A state consists of the current graph $H$, the pairs left, the number of oracle evaluations, and whether failure was reported. For the current pair $\{u,v\}$:
--
--   1. if $u,v$ are adjacent in $H$, or no set of fewer than $k$ vertices separates them in $H$, move on;
--   2. otherwise take a minimum set $F$ separating them in $H$ (so $|F|<k$) and evaluate $\mathcal T(F)$;
--   3. if $\mathcal T(F)$ is FAIL or not a forest on $V\setminus F$, report failure;
--   4. if $u,v$ lie in different trees of $\mathcal T(F)$, move on;
--   5. otherwise add to $H$ an edge on the path from $u$ to $v$ in $\mathcal T(F)$ that joins two components of $H\setminus F$, and return to the same pair.
--
--   The run starts from the empty graph and from a list holding each unordered pair once, in any order. Any minimum separator and any suitable edge may be chosen.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.4, pp.21–22 (PDF pp.22–23)

import Mathlib
import Definitions.Def_PunctSketch_forestGraph

namespace PunctSketch

/-- `F` separates `u` and `v` in `H`: neither lies in `F` and they are disconnected in `H ∖ F`. Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…),
§5.4, p.21. -/
def Separates {V : Type*} (H : SimpleGraph V) (F : Finset V) (u v : V) : Prop :=
  u ∉ F ∧ v ∉ F ∧ ¬ ConnAvoid H F u v

/-- `F` is a minimum set separating `u` and `v` in `H`. Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4, p.21, step 2. -/
def IsMinSeparator {V : Type*} (H : SimpleGraph V) (F : Finset V) (u v : V) : Prop :=
  Separates H F u v ∧ ∀ F' : Finset V, Separates H F' u v → F.card ≤ F'.card

/-- `T` is a forest on `V ∖ F`: its pairs are non-diagonal, avoid `F`, and have no cycle. Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4,
p.22: "if 𝒯(F) is not a forest on V ⧵ F". -/
def IsForestOn {V : Type*} (F : Finset V) (T : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ T, ¬ e.IsDiag ∧ ∀ x ∈ e, x ∉ F) ∧ (forestGraph T).IsAcyclic

/-- **State of the §5.4 procedure:** the current certificate `H`, the pairs still to process, the
number of evaluations of the oracle so far, and whether the run has reported failure. -/
structure CoordState (n : ℕ) where
  H : SimpleGraph (Fin n)
  pairs : List (Fin n × Fin n)
  queries : ℕ
  failed : Bool

/-- A list holding every unordered pair of distinct vertices exactly once: "all pairs of vertices
{u, v} in some fixed order" (Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4, p.21). -/
def IsPairOrder {n : ℕ} (l : List (Fin n × Fin n)) : Prop :=
  l.Nodup ∧ (∀ p ∈ l, p.1 ≠ p.2) ∧ ∀ u v, u ≠ v → (((u, v) ∈ l) ↔ ¬ ((v, u) ∈ l))

/-- **One step of the coordinator's procedure.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4, p.21, steps 1–4, and p.22 for the failure
report, over an arbitrary oracle `𝒯`, where `none` is FAIL. Any minimum separating set and any
suitable edge in step 4 may be chosen.

* `next` — step 1: `u`, `v` adjacent in `H`, or no set of fewer than `k` vertices separates them.
* `fail` — p.22: `𝒯(F)` is FAIL or not a forest on `V ∖ F`.
* `apart` — step 3: `u`, `v` lie in different trees of `𝒯(F)`.
* `add` — step 4: an edge on the path from `u` to `v` in `𝒯(F)` joins two components of `H ∖ F`.

The last three evaluate `𝒯` once, on a minimum separator `F` of `u`, `v` in `H` with `|F| < k`. -/
inductive CoordStep {n : ℕ} (𝒯 : Finset (Fin n) → Option (Finset (Sym2 (Fin n)))) (k : ℕ) :
    CoordState n → CoordState n → Prop
  | next {H : SimpleGraph (Fin n)} {u v : Fin n} {ps : List (Fin n × Fin n)} {q : ℕ}
      (h : H.Adj u v ∨ ∀ F : Finset (Fin n), F.card < k → ¬ Separates H F u v) :
      CoordStep 𝒯 k ⟨H, (u, v) :: ps, q, false⟩ ⟨H, ps, q, false⟩
  | fail {H : SimpleGraph (Fin n)} {u v : Fin n} {ps : List (Fin n × Fin n)} {q : ℕ}
      {F : Finset (Fin n)} (hAdj : ¬ H.Adj u v) (hF : F.card < k) (hmin : IsMinSeparator H F u v)
      (hT : ∀ T, 𝒯 F = some T → ¬ IsForestOn F T) :
      CoordStep 𝒯 k ⟨H, (u, v) :: ps, q, false⟩ ⟨H, (u, v) :: ps, q + 1, true⟩
  | apart {H : SimpleGraph (Fin n)} {u v : Fin n} {ps : List (Fin n × Fin n)} {q : ℕ}
      {F : Finset (Fin n)} {T : Finset (Sym2 (Fin n))} (hAdj : ¬ H.Adj u v) (hF : F.card < k)
      (hmin : IsMinSeparator H F u v) (hT : 𝒯 F = some T) (hforest : IsForestOn F T)
      (hapart : ¬ ConnAvoid (forestGraph T) F u v) :
      CoordStep 𝒯 k ⟨H, (u, v) :: ps, q, false⟩ ⟨H, ps, q + 1, false⟩
  | add {H : SimpleGraph (Fin n)} {u v : Fin n} {ps : List (Fin n × Fin n)} {q : ℕ}
      {F : Finset (Fin n)} {T : Finset (Sym2 (Fin n))} {x y : Fin n} (hAdj : ¬ H.Adj u v)
      (hF : F.card < k) (hmin : IsMinSeparator H F u v) (hT : 𝒯 F = some T)
      (hforest : IsForestOn F T) (w : (forestGraph T).Walk u v) (hw : w.IsPath)
      (hxy : s(x, y) ∈ w.edges) (hjoin : ¬ ConnAvoid H F x y) :
      CoordStep 𝒯 k ⟨H, (u, v) :: ps, q, false⟩
        ⟨H ⊔ SimpleGraph.edge x y, (u, v) :: ps, q + 1, false⟩

/-- The start of the procedure: "The coordinator starts with the empty graph H = (V, ∅)" (p.21). -/
def coordInit {n : ℕ} (pairs : List (Fin n × Fin n)) : CoordState n := ⟨⊥, pairs, 0, false⟩

end PunctSketch


