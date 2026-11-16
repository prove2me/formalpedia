-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_HardInputs
-- name    : GreedyColoringLCA969_LowerBound_Supplement_HardInputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:33:40.322055+00:00
-- url     : https://prove2.me/theorems/54edb88b-ae5c-4def-9734-edcd2a073d59
-- title:
--   Uniform biclique-group inputs, light vertices and bad pairs
-- statement:
--   For integers $\Delta\ge3$, $\lambda\ge2$ and $\tau\ge1$, set $b=2\Delta\lambda$ and $n=b\tau$. A hard input is an arbitrary adjacency-list representation on the fixed identifiers $0,\ldots,n-1$ whose $i$th block consists of $\lambda$ disjoint copies of $K_{\Delta,\Delta}$. An existential bijection witnesses this shape while preserving the block index $\lfloor v/b\rfloor$. The witness is not stored, so identical represented graphs are counted once. All neighbor-list orders are permitted.
--
--   The finite set of these inputs is sampled uniformly. Restricting to blocks identifies it with the product of $\tau$ one-group configuration sets, so this is exactly the independent uniform group distribution. Let $\kappa(\Delta,\lambda)$ be the number of one-group configurations. Expectations are finite arithmetic means over distinct inputs.
--
--   Fix a deterministic algorithm/tape pair $B$. A vertex is light exactly when its actual execution terminates in at most $q_\star=\lfloor\Delta/50\rfloor$ graph queries. The number of light vertices is $X$, and the success-weighted count is $XY$, where $Y$ indicates global MIS success under Boolean coding. A bad pair consists of distinct light vertices in one biclique whose return codes differ on the same side or agree on opposite sides. It is recognized intrinsically by adjacency or equality of neighbor sets, without choosing a decomposition witness. Fixing other groups fixes their entire ordered lists.
--
--   $$D=b\sum_{h=0}^{q_\star-1}b^h,\qquad C=2D+1.$$
--
--   The sum is empty at $q_\star=0$. All configuration spaces are finite and nonempty; the separate verification module proves nonemptiness and positivity of both denominators and $\kappa$. No correctness or efficiency premise is built into an input or algorithm.
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), pp.27–30 (PDF 28–31), §5.1, Definitions 5.2–5.3, Lemmas 5.4 and 5.7

import Definitions.Def_GreedyColoringLCA969_LowerBound_Supplement_LabelPerformance

open scoped ENNReal BigOperators
open MeasureTheory Classical
set_option autoImplicit false

namespace GreedyColoringLCA969.LowerBound.Supplement

/-- Every arbitrary adjacency-list representation on a fixed finite carrier is finite data.
The injection retains the graph and each list with its no-repetition certificate. -/
instance finiteRepresentations (n : ℕ) : Finite (Representation n) := by
  classical
  let enc : Representation n → SimpleGraph (Fin n) ×
      (Fin n → {l : List (Fin n) // l.Nodup}) := fun R =>
    (R.graph, fun v => ⟨R.val v, (R.2.perm v).nodup_iff.mpr (Finset.nodup_toList _)⟩)
  apply Finite.of_injective enc
  intro R S h
  have hg : R.1 = S.1 := congrArg Prod.fst h
  obtain ⟨G, L⟩ := R
  obtain ⟨H, M⟩ := S
  dsimp at hg
  subst H
  have hl : L.lists = M.lists := by
    funext v
    exact congrArg Subtype.val (congrFun (congrArg Prod.snd h) v)
  cases L
  cases M
  dsimp at hl
  cases hl
  rfl

def groupSize (Δ lam : ℕ) : ℕ := 2 * Δ * lam

def hardSize (Δ lam τ : ℕ) : ℕ := groupSize Δ lam * τ

/-- Exactly lam disjoint bicliques per fixed contiguous identifier block. The witness
is not part of a configuration: permuting bicliques or swapping sides does not duplicate it.
Neighbor-list orders remain completely arbitrary in the inherited representation. -/
def HardShape (Δ lam τ : ℕ) (R : Representation (hardSize Δ lam τ)) : Prop :=
  ∃ e : Fin (hardSize Δ lam τ) ≃ Fin τ × (Fin lam × (Bool × Fin Δ)),
    (∀ v, (e v).1.val = v.val / groupSize Δ lam) ∧
    ∀ u v, R.graph.Adj u v ↔
      (e u).1 = (e v).1 ∧ (e u).2.1 = (e v).2.1 ∧ (e u).2.2.1 ≠ (e v).2.2.1

abbrev HardInput (Δ lam τ : ℕ) :=
  {R : Representation (hardSize Δ lam τ) // HardShape Δ lam τ R}

noncomputable instance hardInputFintype (Δ lam τ : ℕ) : Fintype (HardInput Δ lam τ) :=
  Fintype.ofFinite _

/-- Number of distinct represented configurations of ONE group, including list orders. -/
noncomputable def kappa (Δ lam : ℕ) : ℕ := Fintype.card (HardInput Δ lam 1)

/-- Uniform average over distinct represented inputs. The Cartesian decomposition into
fixed blocks makes this the independent uniform group law of §5.1. The valid parameter
range has nonempty configuration spaces, so the denominator is nonzero. -/
noncomputable def hardExpectation (Δ lam τ : ℕ) (f : HardInput Δ lam τ → ℝ) : ℝ :=
  (∑ R, f R) / (Fintype.card (HardInput Δ lam τ) : ℝ)

def lightBudget (Δ : ℕ) : ℕ := Δ / 50

def Light {n : ℕ} (B : DeterministicLCA .standard) (R : Representation n)
    (Δ : ℕ) (v : Fin n) : Prop := queryCost B.1 R B.2 v ≤ (lightBudget Δ : ℝ≥0∞)

noncomputable def lightCount {n : ℕ} (B : DeterministicLCA .standard)
    (R : Representation n) (Δ : ℕ) : ℕ := (Finset.univ.filter (Light B R Δ)).card

noncomputable def groupLightCount {n : ℕ} (B : DeterministicLCA .standard)
    (R : Representation n) (Δ lam i : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => v.val / groupSize Δ lam = i ∧ Light B R Δ v)).card

/-- On the hard graphs, two distinct vertices are in the same biclique iff they are
adjacent (opposite sides) or have equal neighbor sets (same side). Compare raw return
codes; never coerce an invalid code to a default Boolean value. -/
def BadPair {n : ℕ} (B : DeterministicLCA .standard) (R : Representation n)
    (Δ : ℕ) (v w : Fin n) : Prop :=
  v ≠ w ∧ Light B R Δ v ∧ Light B R Δ w ∧
  (R.graph.Adj v w ∨ R.graph.neighborFinset v = R.graph.neighborFinset w) ∧
  ∃ c d : ℕ+, Returns B.1 R B.2 v c ∧ Returns B.1 R B.2 w d ∧
    ((R.graph.Adj v w ∧ c = d) ∨ (¬ R.graph.Adj v w ∧ c ≠ d))

/-- Fixing every other group fixes its entire ordered lists, not merely its edges. -/
def SameOutside {n : ℕ} (R S : Representation n) (Δ lam i : ℕ) : Prop :=
  ∀ v, v.val / groupSize Δ lam ≠ i → R.val v = S.val v

noncomputable def successWeightedLight {n : ℕ} (B : DeterministicLCA .standard)
    (R : Representation n) (Δ : ℕ) : ℝ :=
  if B.2 ∈ labelingSuccess MIS boolCode B.1 R then (lightCount B R Δ : ℝ) else 0

def decisionD (Δ lam : ℕ) : ℕ :=
  groupSize Δ lam * ∑ h ∈ Finset.range (lightBudget Δ), (groupSize Δ lam)^h

def decisionC (Δ lam : ℕ) : ℕ := 2 * decisionD Δ lam + 1

end GreedyColoringLCA969.LowerBound.Supplement


