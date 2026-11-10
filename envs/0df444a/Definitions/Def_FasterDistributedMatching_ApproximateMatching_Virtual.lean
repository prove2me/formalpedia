-- Prove2me | Definitions.Def_FasterDistributedMatching_ApproximateMatching_Virtual
-- name    : FasterDistributedMatching_ApproximateMatching_Virtual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:10:14.774209+00:00
-- url     : https://prove2.me/theorems/dbb0a224-16c0-4ab5-a9ce-9fd68453a018
-- title:
--   Paired active edges, virtual blocks and cut cost
-- statement:
--   At an active value $q$, each physical vertex partitions its incident $q$-edges into pairs and at most one singleton. Every group member must be an active graph neighbor; inactive neighbors and nonedges are excluded. A virtual copy represents each group, and each active edge joins its two assigned copies. Copy identities consist of a creator and a local group index. A creator may occur several times in a virtual path or block. Blocks are connected disjoint sets with internal leaders, covering precisely components of at least $\ell$ copies, and have sizes between $\ell$ and $65\ell+1$.
--
--   For one cut copy per block, let $k_v$ count selected copies created by $v$ and let $r_v$ be the active degree modulo two. The cost is
--
--   $$F=2q^2\sum_v(2k_v+r_v)^2.$$
--
--   A finite joint law describes arbitrary real probabilities on cut assignments. Uniform marginal and two-block joint probabilities specify pairwise independence, including blocks with repeated creators. No load constraint is built into this data. Short components receive no blocks or cuts.
--
--   These definitions retain both true endpoints and selected copies in the source's quadratic loss bound.
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), §3.1, printed p.8, PDF p.10; §3.2 equation (2) and Lemma 3.4, printed pp.9–10, PDF pp.11–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local

namespace FasterDistributedMatching.ApproximateMatching

/-! §§3.1--3.3: locally paired incident active edges, and actual copy graphs.
A copy's index is local to its creator; the creator map need not be injective. -/
abbrev Pairing (N : ℕ) := Fin N → List (Finset (Fin N))
abbrev Copy {N : ℕ} (p : Pairing N) := Σ v : Fin N, Fin (p v).length

def creator {N : ℕ} {p : Pairing N} (a : Copy p) : Fin N := a.1

def group {N : ℕ} (p : Pairing N) (a : Copy p) : Finset (Fin N) :=
  (p a.1).get a.2

def copyKey {N : ℕ} {p : Pairing N} (ids : Fin N → ℕ) (a : Copy p) : ℕ × ℕ :=
  (ids a.1, a.2.val)

/- Nonempty groups of size one or two partition each active neighborhood; at most one singleton. -/
open Classical in
noncomputable def ValidPairing {N : ℕ} (G : SimpleGraph (Fin N))
    (x : Sym2 (Fin N) → ℝ) (q : ℝ) (p : Pairing N) : Prop :=
  (∀ a : Copy p, (group p a).card = 1 ∨ (group p a).card = 2) ∧
  (∀ v w, (G.Adj v w ∧ x s(v,w) = q) ↔
    ∃! i : Fin (p v).length, w ∈ (p v).get i) ∧
  (∀ a : Copy p, ∀ w ∈ group p a, G.Adj a.1 w ∧ x s(a.1,w) = q) ∧
  (∀ v, (Finset.univ.filter (fun i : Fin (p v).length => ((p v).get i).card = 1)).card ≤ 1)

def virtualGraph {N : ℕ} (p : Pairing N) : SimpleGraph (Copy p) where
  Adj a b := a.1 ≠ b.1 ∧ b.1 ∈ group p a ∧ a.1 ∈ group p b
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

/- A finite walk of length at most r. Includes distance zero; unreachable pairs are never close. -/
def Close {V : Type} (H : SimpleGraph V) (r : ℕ) (a b : V) : Prop :=
  ∃ w : H.Walk a b, w.length ≤ r

def Separates {V : Type} (H : SimpleGraph V) (r zeta : ℕ) (col : V → ℕ) : Prop :=
  (∀ a, col a < zeta) ∧ ∀ a b, a ≠ b → Close H r a b → col a ≠ col b

/- Each vertex names its block by its leader. None is reserved for short components. -/
abbrev BlockAssignment {N : ℕ} (p : Pairing N) := Copy p → Option (Copy p)

open Classical in
noncomputable def block {N : ℕ} {p : Pairing N} (B : BlockAssignment p) (a : Copy p) : Finset (Copy p) :=
  Finset.univ.filter (fun b => B b = some a)

open Classical in
noncomputable def component {N : ℕ} (p : Pairing N) (a : Copy p) : Finset (Copy p) :=
  Finset.univ.filter (fun b => (virtualGraph p).Reachable a b)

/- Complete partition of precisely the long components, with connected blocks and internal leaders. -/
def ValidBlocks {N : ℕ} {p : Pairing N} (ell : ℕ) (B : BlockAssignment p) : Prop :=
  (∀ a, B a = none ↔ (component p a).card < ell) ∧
  ∀ a leader, B a = some leader →
    B leader = some leader ∧ ell ≤ (block B leader).card ∧
    (block B leader).card ≤ 65 * ell + 1 ∧
    ∀ b ∈ block B leader, ∃ w : (virtualGraph p).Walk a b,
      ∀ c ∈ w.support, c ∈ block B leader

/- One actual selected copy per block; ignored values at nonleaders are not cuts. -/
def ValidCuts {N : ℕ} {p : Pairing N} (B : BlockAssignment p) (s : Copy p → Copy p) : Prop :=
  ∀ a, B a = some a → s a ∈ block B a

open Classical in
noncomputable def activeDegree {N : ℕ} (G : SimpleGraph (Fin N))
    (x : Sym2 (Fin N) → ℝ) (q : ℝ) (v : Fin N) : ℕ :=
  ((G.neighborFinset v).filter (fun w => x s(v,w) = q)).card

open Classical in
noncomputable def cutCount {N : ℕ} {p : Pairing N} (B : BlockAssignment p)
    (s : Copy p → Copy p) (v : Fin N) : ℕ :=
  (Finset.univ.filter (fun a => B a = some a ∧ (s a).1 = v)).card

noncomputable def cutCost {N : ℕ} (G : SimpleGraph (Fin N))
    (x : Sym2 (Fin N) → ℝ) (q : ℝ) {p : Pairing N}
    (B : BlockAssignment p) (s : Copy p → Copy p) : ℝ :=
  2 * q ^ 2 * ∑ v, (2 * (cutCount B s v : ℝ) + (activeDegree G x q v % 2 : ℕ)) ^ 2

/- Finite joint law on all valid cut assignments. The finite range represents every possible
joint law of the finite labels, not merely product laws or rational probabilities. -/
open Classical in
noncomputable def PairwiseUniformCuts {N : ℕ} {p : Pairing N} (B : BlockAssignment p)
    (mu : (Copy p → Copy p) → ℝ) : Prop :=
  (∀ s, 0 ≤ mu s) ∧ (∑ s, mu s) = 1 ∧
  (∀ s, mu s ≠ 0 → ValidCuts B s) ∧
  (∀ a, B a = some a → ∀ c ∈ block B a,
    (∑ s, if s a = c then mu s else 0) = 1 / ((block B a).card : ℝ)) ∧
  (∀ a b, B a = some a → B b = some b → a ≠ b →
    ∀ c ∈ block B a, ∀ d ∈ block B b,
      (∑ s, if s a = c ∧ s b = d then mu s else 0) =
        1 / (((block B a).card : ℝ) * (block B b).card))

end FasterDistributedMatching.ApproximateMatching


