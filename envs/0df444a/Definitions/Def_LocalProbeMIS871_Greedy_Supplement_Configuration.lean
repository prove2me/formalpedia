-- Prove2me | Definitions.Def_LocalProbeMIS871_Greedy_Supplement_Configuration
-- name    : LocalProbeMIS871_Greedy_Supplement_Configuration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:02:13.8192+00:00
-- url     : https://prove2.me/theorems/e4c6d8ab-2104-4b2e-9c5c-4d1c7d653875
-- title:
--   §4.1 — Exact finite D₀ and D₁ graph experiments
-- statement:
--   For an integer degree bound $\Delta$, put $\ell=\lceil(\ln\Delta)^2\rceil$ and $k=\Delta-\ell+1$. A positive integer $m$ is admissible when $7\le\ell<\Delta/4$, $N=mk\ell/\Delta$ is integral and divisible by eight. Let $n=N+mk$ and $H=mk\ell=N\Delta$. Start with $N$ hidden vertices $A$ and $m$ disjoint prescribed $k$-cliques forming $B$. Each vertex of $B$ has $\ell$ numbered external half-edges.
--
--   A uniform permutation $\pi$ of the $H$ half-edges supplies the connections. In $D_0$, slot $x$ belongs to vertex $\lfloor x/\Delta\rfloor$ of $A$ and is matched to half-edge $\pi(x)$ of $B$. In $D_1$, the first $7N$ permuted half-edges are paired consecutively, and the remaining slots are matched to $A$ in groups of $\Delta-7$. An independent uniform permutation of $A$, grouped in consecutive eights, supplies its prescribed $K_8$ partition. Hence
--
--   $$D_0:\ A\text{ independent};\qquad D_1:\ A\text{ partitioned into }N/8\text{ copies of }K_8.$$
--
--   Delete loops and collapse parallel edges while retaining every prescribed clique edge. Independently relabel by a uniform permutation of all $n$ vertices. At each labeled vertex, filter an independent uniform permutation of all labels to its actual neighbors; this produces an independent uniform ordering of the distinct neighbors. Finally, query an independent uniform vertex of hidden $A$. The latent sets $A,B,C_j$ are retained for mathematical statements and are never given to the policy.
--
--   The whole experiment is uniform counting on a finite product of permutation types and one uniform hidden query label. `finiteProb` computes an event's exact cardinality divided by the seed cardinality. The neighborhood $N_G(S)$ is the union of open neighborhoods and
--
--   $$\eta_c(\Delta,m)=\exp\bigl(m\ln(k+1)-cN\bigr).$$
--
--   These objects fix the input laws for the structural and transcript lemmas. The actual graph degrees can decrease upon simplification; regularity is not assumed.
--
--   **Formalization Note** Stub, slot, clique and vertex labels use zero-based indices. A-partition permutations unused in $D_0$ are redundant independent coordinates with constant fibers. In $D_1$, every fixed selected subset, perfect matching and complementary bijection has exactly $(7N/2)!2^{7N/2}$ permutation preimages. Every fixed eight-set partition has $(N/8)!(8!)^{N/8}$ preimages. Filtering label permutations gives $n!/d!$ preimages per list of $d$ neighbors. Thus these redundant samplers preserve the exact laws. Outside admissible parameters functions are total, but no supporting lemma invokes their probabilities there.
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), pp. 23–26, PDF pp. 25–28, §4.1–§4.2, Eqs. (36)–(40)

import Definitions.Def_LocalProbeMIS871_Greedy_Supplement_Oracle

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy.Supplement

def ell (Δ : ℕ) : ℕ := ⌈(Real.log (Δ : ℝ)) ^ (2 : ℕ)⌉₊
def cliqueSize (Δ : ℕ) : ℕ := Δ - ell Δ + 1
def aSize (Δ m : ℕ) : ℕ := m * cliqueSize Δ * ell Δ / Δ
def graphSize (Δ m : ℕ) : ℕ := aSize Δ m + m * cliqueSize Δ
def stubSize (Δ m : ℕ) : ℕ := m * cliqueSize Δ * ell Δ

def Admissible (Δ m : ℕ) : Prop :=
  2 ≤ Δ ∧ 7 ≤ ell Δ ∧ 4 * ell Δ < Δ ∧ 0 < m ∧
    Δ ∣ stubSize Δ m ∧ 8 ∣ aSize Δ m

/-- Independent uniform permutations encode all construction choices. A permutation of
all labels per vertex, filtered to its neighbors, gives a uniform neighbor ordering.
Unused A-permutations in D0 merely give equal multiplicity to every D0 outcome. -/
abbrev Seed (Δ m : ℕ) :=
  Equiv.Perm (Fin (stubSize Δ m)) × Equiv.Perm (Fin (aSize Δ m)) ×
    Equiv.Perm (Fin (graphSize Δ m)) ×
    (Fin (graphSize Δ m) → Equiv.Perm (Fin (graphSize Δ m))) × Fin (aSize Δ m)

def stubPerm {Δ m : ℕ} (s : Seed Δ m) := s.1
def aPerm {Δ m : ℕ} (s : Seed Δ m) := s.2.1
def labelPerm {Δ m : ℕ} (s : Seed Δ m) := s.2.2.1
def listPerm {Δ m : ℕ} (s : Seed Δ m) := s.2.2.2.1
def hiddenQuery {Δ m : ℕ} (s : Seed Δ m) := s.2.2.2.2

def bOwner (Δ m : ℕ) (x : Fin (stubSize Δ m)) : ℕ := aSize Δ m + x.val / ell Δ

/-- Oriented raw edges. Symmetrization and loop deletion below implement simplification. -/
def rawEdge (one : Bool) {Δ m : ℕ} (s : Seed Δ m)
    (u v : Fin (graphSize Δ m)) : Prop :=
  (aSize Δ m ≤ u.val ∧ aSize Δ m ≤ v.val ∧
    (u.val - aSize Δ m) / cliqueSize Δ = (v.val - aSize Δ m) / cliqueSize Δ) ∨
  (if one then
    (∃ x y : Fin (aSize Δ m), (aPerm s x).val / 8 = (aPerm s y).val / 8 ∧
      u.val = x.val ∧ v.val = y.val) ∨
    (∃ x y : Fin (stubSize Δ m), x.val < 7 * aSize Δ m ∧ x.val % 2 = 0 ∧
      y.val = x.val + 1 ∧ u.val = bOwner Δ m (stubPerm s x) ∧
      v.val = bOwner Δ m (stubPerm s y)) ∨
    (∃ x : Fin (stubSize Δ m), 7 * aSize Δ m ≤ x.val ∧
      u.val = (x.val - 7 * aSize Δ m) / (Δ - 7) ∧
      v.val = bOwner Δ m (stubPerm s x))
   else
    ∃ x : Fin (stubSize Δ m), u.val = x.val / Δ ∧
      v.val = bOwner Δ m (stubPerm s x))

def unlabelledGraph (one : Bool) {Δ m : ℕ} (s : Seed Δ m) :
    SimpleGraph (Fin (graphSize Δ m)) where
  Adj u v := u ≠ v ∧ (rawEdge one s u v ∨ rawEdge one s v u)
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

def sampleGraph (one : Bool) {Δ m : ℕ} (s : Seed Δ m) :
    SimpleGraph (Fin (graphSize Δ m)) :=
  (unlabelledGraph one s).comap (labelPerm s).symm

def sampleA {Δ m : ℕ} (s : Seed Δ m) : Finset (Fin (graphSize Δ m)) :=
  Finset.univ.filter (fun v => ((labelPerm s).symm v).val < aSize Δ m)

def sampleB {Δ m : ℕ} (s : Seed Δ m) : Finset (Fin (graphSize Δ m)) :=
  Finset.univ \ sampleA s

def sampleClique {Δ m : ℕ} (s : Seed Δ m) (j : Fin m) :
    Finset (Fin (graphSize Δ m)) :=
  (sampleB s).filter (fun v =>
    (((labelPerm s).symm v).val - aSize Δ m) / cliqueSize Δ = j.val)

def sampleRoot {Δ m : ℕ} (s : Seed Δ m) : Fin (graphSize Δ m) :=
  labelPerm s ⟨(hiddenQuery s).val,
    lt_of_lt_of_le (hiddenQuery s).isLt (Nat.le_add_right (aSize Δ m) (m * cliqueSize Δ))⟩

def sampleLists (one : Bool) {Δ m : ℕ} (s : Seed Δ m) : AdjacencyLists (sampleGraph one s) where
  lists v := (List.ofFn (listPerm s v)).filter (fun w => (sampleGraph one s).Adj v w)
  perm v := by
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_ofFn.mpr (listPerm s v).injective).filter _)
      (Finset.nodup_toList _)).mpr
    intro w
    simp only [List.mem_filter, List.mem_ofFn, Finset.mem_toList,
      SimpleGraph.mem_neighborFinset, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨⟨(listPerm s v).symm w, by simp⟩, h⟩⟩

/-- Uniform finite probability. All legal construction seed types are nonempty. -/
def finiteProb {α : Type*} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

def eta (c : ℝ) (Δ m : ℕ) : ℝ :=
  Real.exp ((m : ℝ) * Real.log ((cliqueSize Δ : ℝ) + 1) - c * aSize Δ m)

def neighborhood {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ u ∈ S, G.Adj u v)

def selectionGood {Δ m : ℕ} (s : Seed Δ m) : Prop :=
  ∀ S : Finset (Fin (graphSize Δ m)), S ⊆ sampleB s →
    (∀ j : Fin m, (S ∩ sampleClique s j).card ≤ 1) →
      (aSize Δ m : ℝ) / 4 ≤ ((sampleA s \ neighborhood (sampleGraph false s) S).card : ℝ)

end LocalProbeMIS871.Greedy.Supplement


