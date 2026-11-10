-- Prove2me | Definitions.Def_BirthdayEntropy_Soundness_Biclique
-- name    : BirthdayEntropy_Soundness_Biclique
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:51:02.777409+00:00
-- url     : https://prove2.me/theorems/6da8d32d-bcfc-46eb-8ecb-4bbc72230d9c
-- title:
--   Accepted labelled bicliques, signed flattenings and obstruction energy
-- statement:
--   For a selected vertex set $H$, a tuple consists of $r$ left and $r$ right vertices sampled independently and uniformly with replacement. It is accepted if all $r^2$ cross pairs are edges. Repetitions within a side are allowed; a cross equality rejects. The probability is computed as the number of accepted tuples divided by $|H|^{2r}$.
--
--   A vertex contributes its signed points $(i,a(i))$. The flattening $F=(A,B)$ is the actual union of these points on each side. Cross consistency forbids $(i,b)\in A$ and $(i,1-b)\in B$. Bad-left variables have both signed bits in $A$, bad-right variables both in $B$, good variables have a common signed bit on both sides, and terrible variables have neither a bad nor a good role. On cross-consistent cells these are exactly the source classes. Write $b_{\mathrm{bad}}=|B_L|+|B_R|$ and $t_{\mathrm{terr}}=|T|$. Then
--   $$R(A,B)=\max\{t_{\mathrm{terr}},xb_{\mathrm{bad}},nx\,\mathbf1_{\{t_{\mathrm{terr}}<\beta n,\ b_{\mathrm{bad}}<\beta n\}}\}.$$
--   The accepted cell is the fiber of this flattening map within the accepted tuples from $H$; equivalently it is the full graph's accepted cell intersected with $H^{2r}$.
--
--   Everything is computed from the CSP and the selected set. No cell suppression, energy floor or entropy estimate is built into the model.
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, §4, PDF pp8–10 / printed pp7–9, equations (4)–(5)

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Graph
import Definitions.Def_BirthdayEntropy_Soundness_Counting

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

abbrev Tuple (n ℓ r : ℕ) := (Fin r → Vertex n ℓ) × (Fin r → Vertex n ℓ)
abbrev Flattening (n : ℕ) := Finset (Signed n) × Finset (Signed n)

/-- The accepted labelled tuples, with replacement on both sides. Every
cross pair must be an edge, so a cross equality rejects. -/
def accepted {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) (r : ℕ) :
    Finset (Tuple n ℓ r) :=
  Finset.univ.filter (fun X =>
    (∀ i, X.1 i ∈ H) ∧ (∀ j, X.2 j ∈ H) ∧ ∀ i j, (graph φ).Adj (X.1 i) (X.2 j))

/-- The probability for independent samples from the uniform law on H;
used only with |H|=binom n ell and 1≤ell≤n. -/
def acceptanceProbability {n m ℓ : ℕ} (φ : CSP n m)
    (H : Finset (Vertex n ℓ)) (r : ℕ) : ℝ :=
  (accepted φ H r).card / (H.card : ℝ) ^ (2 * r)

/-- The actual signed union on each side, not an arbitrary cell parameter. -/
def flatten {n ℓ r : ℕ} (X : Tuple n ℓ r) : Flattening n :=
  (Finset.univ.biUnion (fun i => signed (X.1 i)),
   Finset.univ.biUnion (fun j => signed (X.2 j)))

/-- Cross consistency only; a within-side pair of opposite bits is allowed. -/
def CrossConsistent {n : ℕ} (F : Flattening n) : Prop :=
  ∀ i b, (i, b) ∈ F.1 → (i, !b) ∉ F.2

def badLeft {n : ℕ} (F : Flattening n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i, false) ∈ F.1 ∧ (i, true) ∈ F.1)

def badRight {n : ℕ} (F : Flattening n) : Finset (Fin n) :=
  badLeft (F.2, F.1)

def good {n : ℕ} (F : Flattening n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ b, (i, b) ∈ F.1 ∧ (i, b) ∈ F.2)

/-- On cross-consistent cells these are exactly the coordinates with at
most one signed occurrence across the two sides (the five source states). -/
def terrible {n : ℕ} (F : Flattening n) : Finset (Fin n) :=
  Finset.univ \ (badLeft F ∪ badRight F ∪ good F)

def badCount {n : ℕ} (F : Flattening n) : ℕ := (badLeft F).card + (badRight F).card

/-- Equation (5), retaining all three branches and the strict indicator. -/
def energy {n : ℕ} (ℓ : ℕ) (β : ℝ) (F : Flattening n) : ℝ :=
  max ((terrible F).card : ℝ)
    (max (ratio n ℓ * badCount F)
      (if ((terrible F).card : ℝ) < β * n ∧ (badCount F : ℝ) < β * n
       then (n : ℝ) * ratio n ℓ else 0))

/-- Lemma 4.5's full-graph accepted cell intersected with H^(2r).
Filtering the already accepted tuples computes exactly that intersection. -/
def acceptedCell {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) (r : ℕ)
    (F : Flattening n) : Finset (Tuple n ℓ r) := cell (accepted φ H r) flatten F

end BirthdayEntropy.Soundness


