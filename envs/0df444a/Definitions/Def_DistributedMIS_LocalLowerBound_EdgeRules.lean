-- Prove2me | Definitions.Def_DistributedMIS_LocalLowerBound_EdgeRules
-- name    : DistributedMIS_LocalLowerBound_EdgeRules
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:36.508128+00:00
-- url     : https://prove2.me/theorems/21805308-9663-4a98-84e0-4b23fb81a6c2
-- title:
--   Edge-input rules, finite cylinder laws, entropy and truncation
-- statement:
--   Let G be the countably infinite D-regular tree and let each clique have k named coordinates. One fair bit is assigned to each entry of each undirected edge matrix; reverse orientation transposes the matrix. The view at radius s includes exactly edges with both endpoints in the closed s-ball. A rule assigns a real probability vector to each view, unchanged by rooted coordinate-preserving isomorphisms; final draws are independent conditional on the matrices.
--
--   $$p(A)=\Pr[A_v\ne0],\qquad \epsilon(A)=\Pr[A_u,A_v\ne0,\ G_{uv}(A_u,A_v)=1].$$
--
--   This interface defines finite conditional laws, Shannon entropy, shared views, resampling, coordinate-ordered short lists, and kept/deleted probability vectors. Each cylinder average uses all assignments, including the unique assignment on the empty view. No occupancy or information inequality is part of the definition. The list sizes are the paper's exact ℓ, M and m.
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; §4.1–4.3, pp. 11–14; Eq. (7), p. 16; §6, p. 17; §8.3, pp. 22–23 (printed = PDF)

import Mathlib

noncomputable section

namespace DistributedMIS.LocalLowerBound

abbrev BitIndex (k : ℕ) := ℕ × ℕ × Fin k × Fin k
abbrev Matrices (k : ℕ) := BitIndex k → Bool
abbrev Output (k : ℕ) := Option (Fin k)
abbrev RawRule (k : ℕ) := ℕ → Matrices k → Output k → ℝ

/-- One independent bit at the lower-numbered endpoint; reversing an edge transposes it. -/
def edgeBit {k : ℕ} (ω : Matrices k) (u v : ℕ) (a b : Fin k) : Bool :=
  if u < v then ω (u, v, a, b) else ω (v, u, b, a)

def ball (G : SimpleGraph ℕ) [G.LocallyFinite] : ℕ → ℕ → Finset ℕ
  | 0, v => {v}
  | s + 1, v => (ball G s v).biUnion (fun u => insert u (G.neighborFinset u))

def viewBits (G : SimpleGraph ℕ) [G.LocallyFinite] (k s v : ℕ) : Finset (BitIndex k) := by
  classical
  exact ((ball G s v ×ˢ ball G s v) ×ˢ (Finset.univ ×ˢ Finset.univ)).filterMap
    (fun z => if z.1.1 < z.1.2 ∧ G.Adj z.1.1 z.1.2 then
      some (z.1.1, z.1.2, z.2.1, z.2.2) else none)
    (by intros a b ha hb hab; simp_all; aesop)

def centralBits (k u v : ℕ) : Finset (BitIndex k) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).image
    (fun z : Fin k × Fin k => if u < v then (u,v,z.1,z.2) else (v,u,z.2,z.1))

def sharedBits (G : SimpleGraph ℕ) [G.LocallyFinite] (k t u v : ℕ) :=
  centralBits k u v ∪ viewBits G k t u ∪ viewBits G k t v

def fill {k : ℕ} (S : Finset (BitIndex k)) (b : S → Bool) : Matrices k :=
  fun i => if h : i ∈ S then b ⟨i,h⟩ else false

/-- Exact fair product cylinder marginal, including the unique empty assignment. -/
def average {k : ℕ} (S : Finset (BitIndex k)) (f : Matrices k → ℝ) : ℝ :=
  (∑ b : S → Bool, f (fill S b)) / (2 : ℝ) ^ S.card

def overwrite {k : ℕ} (F : Finset (BitIndex k)) (ω ξ : Matrices k) : Matrices k :=
  fun i => if i ∈ F then ω i else ξ i

def conditional {k : ℕ} (S F : Finset (BitIndex k)) (f : Matrices k → ℝ)
    (ω : Matrices k) : ℝ :=
  average (S \ F) (fun ξ => f (overwrite F ω ξ))

def pullMatrices {k : ℕ} (e : ℕ ≃ ℕ) (ω : Matrices k) : Matrices k :=
  fun i => edgeBit ω (e i.1) (e i.2.1) i.2.2.1 i.2.2.2

/-- Only stochasticity, local dependence and anonymity; no correctness or bounds. -/
def IsRule (G : SimpleGraph ℕ) [G.LocallyFinite] (k r : ℕ) (A : RawRule k) : Prop :=
  (∀ v ω a, 0 ≤ A v ω a) ∧
  (∀ v ω, ∑ a, A v ω a = 1) ∧
  (∀ v ω ξ, (∀ i ∈ viewBits G k r v, ω i = ξ i) → A v ω = A v ξ) ∧
  (∀ e : G ≃g G, ∀ v ω, A (e v) ω = A v (pullMatrices e.toEquiv ω))

def IsRegularTree (G : SimpleGraph ℕ) [G.LocallyFinite] (D : ℕ) : Prop :=
  G.IsTree ∧ ∀ v, G.degree v = D

def condLaw (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ} (r : ℕ)
    (A : RawRule k) (v : ℕ) (F : Finset (BitIndex k)) (ω : Matrices k) (a : Output k) :=
  conditional (viewBits G k r v) F (fun ξ => A v ξ a) ω

def occupancy (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r : ℕ) (A : RawRule k) (v : ℕ) :=
  average (viewBits G k r v) (fun ω => ∑ a : Fin k, A v ω (some a))

def conflict (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r : ℕ) (A : RawRule k) (u v : ℕ) :=
  average (viewBits G k r u ∪ viewBits G k r v ∪ centralBits k u v)
    (fun ω => ∑ a : Fin k, ∑ b : Fin k,
      if edgeBit ω u v a b then A u ω (some a) * A v ω (some b) else 0)

def entropy {α : Type} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, if 0 < p a then p a * Real.log (1 / p a) else 0

def condEntropy (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r : ℕ) (A : RawRule k) (v : ℕ) (F : Finset (BitIndex k)) :=
  average F (fun ω => entropy (condLaw G r A v F ω))

def jointCondEntropy (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r : ℕ) (A : RawRule k) (u v : ℕ) (F : Finset (BitIndex k)) :=
  average F (fun ω => entropy (fun ab : Output k × Output k =>
    conditional (viewBits G k r u ∪ viewBits G k r v) F
      (fun ξ => A u ξ ab.1 * A v ξ ab.2) ω))

/-- Conditional resampling uses genuinely averaged matrix probabilities. -/
def resample (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r t : ℕ) (A : RawRule k) : RawRule k :=
  fun v ω a => condLaw G r A v (viewBits G k t v) ω a

def shortList {k : ℕ} (m : ℕ) (p : Output k → ℝ) : Finset (Fin k) := by
  classical
  exact ((Finset.univ.toList.mergeSort (fun a b : Fin k =>
    if p (some a) = p (some b) then a ≤ b else p (some b) < p (some a))).take m).toFinset

def keepBy {k : ℕ} (A : RawRule k) (P : ℕ → Matrices k → Finset (Fin k)) : RawRule k :=
  fun v ω a => match a with
    | some b => if b ∈ P v ω then A v ω (some b) else 0
    | none => A v ω none + ∑ b : Fin k, if b ∈ P v ω then 0 else A v ω (some b)

def deleteBy {k : ℕ} (A : RawRule k) (P : ℕ → Matrices k → Finset (Fin k)) : RawRule k :=
  fun v ω a => match a with
    | some b => if b ∈ P v ω then 0 else A v ω (some b)
    | none => A v ω none + ∑ b : Fin k, if b ∈ P v ω then A v ω (some b) else 0

def truncationList (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (s m : ℕ) (A : RawRule k) (v : ℕ) (ω : Matrices k) :=
  shortList m (condLaw G s A v (viewBits G k (s-1) v) ω)

def SupportedOn (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r : ℕ) (A : RawRule k) (F : ℕ → Finset (BitIndex k))
    (P : ℕ → Matrices k → Finset (Fin k)) : Prop :=
  ∀ v ω a, 0 < condLaw G r A v (F v) ω (some a) → a ∈ P v ω

def ShortSupport (G : SimpleGraph ℕ) [G.LocallyFinite] {k : ℕ}
    (r t m : ℕ) (A : RawRule k) : Prop :=
  ∀ v ω, (Finset.univ.filter (fun a : Fin k =>
    0 < condLaw G r A v (viewBits G k t v) ω (some a))).card ≤ m

def ell (k : ℕ) : ℕ := ⌈100 * Real.log (k + 1 : ℝ)⌉₊
def mergedSize (k : ℕ) : ℕ := 1000 * ell k
def retainedSize (D k : ℕ) : ℕ := D * mergedSize k
def lossBase (D : ℕ) : ℝ := 2100 * Real.log D / D

def massEntropy (m : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.log (Real.exp 1 * m / x)

end DistributedMIS.LocalLowerBound


