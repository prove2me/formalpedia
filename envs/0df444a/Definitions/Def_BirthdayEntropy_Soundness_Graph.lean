-- Prove2me | Definitions.Def_BirthdayEntropy_Soundness_Graph
-- name    : BirthdayEntropy_Soundness_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:50:02.77506+00:00
-- url     : https://prove2.me/theorems/48577369-99b6-44e8-89d8-86db7042e853
-- title:
--   All-label birthday graph and maximum selected density
-- statement:
--   A coordinate view $S$ is an $\ell$-element subset of $[n]$. A vertex is every pair $(S,a)$ with $a:S\to\{0,1\}$, including labels that violate an internal constraint. Two distinct vertices are adjacent exactly when their labels agree on their intersection and their union assignment satisfies every source constraint whose complete scope is in the union.
--
--   For an arbitrary set $H$ of distinct vertices define
--   $$K=\binom n\ell,\qquad \rho(H)=\frac{|E(H)|}{\binom{|H|}{2}},\qquad \rho^*(K)=\max_{|H|=K}\rho(H).$$
--   Edges are counted as unordered two-element subsets. The selection family is explicitly finite and nonempty: the restrictions of the constant false assignment provide $K$ distinct vertices. Structural cardinality lemmas give $K$ views and $2^\ell K$ vertices. The maximum is computed over that family, with no optimizing selection assumed as input. A target clique is a set of $K$ pairwise adjacent distinct vertices, including a singleton when $K=1$.
--
--   This graph and density interface is shared by the soundness and completeness statements. Density is totalized to zero when its denominator vanishes; the soundness range forces $K\ge2$, and completeness makes no density assertion.
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, §2, PDF pp3–4 / printed pp2–3; Appendix B.1, PDF p22 / printed p21, equation (27)

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Source

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- All coordinate views and all their Boolean labels, §2 and Appendix B.1.
Locally invalid labels are retained. -/
abbrev View (n ℓ : ℕ) := {S : Finset (Fin n) // S.card = ℓ}
abbrev Vertex (n ℓ : ℕ) := (S : View n ℓ) × (S.val → Bool)

abbrev Signed (n : ℕ) := Fin n × Bool

/-- The signed points of a vertex. -/
def signed {n ℓ : ℕ} (v : Vertex n ℓ) : Finset (Signed n) :=
  Finset.univ.image (fun i : v.1.val => (i.val, v.2 i))

def consistent {n : ℕ} (A : Finset (Signed n)) : Prop :=
  ∀ i, ¬ ((i, false) ∈ A ∧ (i, true) ∈ A)

def support {n : ℕ} (A : Finset (Signed n)) : Finset (Fin n) := A.image Prod.fst

/-- The assignment reads true precisely at a signed true point; outside the
support it is false. In adjacency it is read only on consistent exposed scopes. -/
def assignment {n : ℕ} (A : Finset (Signed n)) (i : Fin n) : Bool := decide ((i, true) ∈ A)

/-- A loopless, undirected union-constraint graph. -/
def graph {n m ℓ : ℕ} (φ : CSP n m) : SimpleGraph (Vertex n ℓ) where
  Adj v w := v ≠ w ∧ consistent (signed v ∪ signed w) ∧
    ∀ j, φ.H.verts j ⊆ support (signed v ∪ signed w) →
      φ.f j (assignment (signed v ∪ signed w) ∘ φ.H.M j) = true
  symm := ⟨by
    intro v w h
    simpa only [Finset.union_comm, ne_comm] using h⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

/-- The source density uses unordered two-element edges, not sampling with replacement. -/
def edges {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) : Finset (Finset (Vertex n ℓ)) :=
  (H.powersetCard 2).filter (fun e => ∃ v ∈ e, ∃ w ∈ e, (graph φ).Adj v w)

def density {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ)) : ℝ :=
  (edges φ H).card / (Nat.choose H.card 2 : ℝ)

/-- The actual finite family of all K distinct-vertex selections. -/
def selections (n ℓ : ℕ) : Finset (Finset (Vertex n ℓ)) :=
  Finset.univ.powersetCard (Nat.choose n ℓ)

/-- Structural cardinality of the coordinate-view type. -/
theorem card_view (n ℓ : ℕ) : Fintype.card (View n ℓ) = Nat.choose n ℓ := by
  have h : Fintype.card (View n ℓ) = (Finset.univ.powersetCard ℓ : Finset (Finset (Fin n))).card := by
    rw [← Fintype.card_coe]
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun S => by simp)
  simpa using h

/-- Exact vertex count, including isolated locally invalid labels, (27). -/
theorem card_vertex (n ℓ : ℕ) :
    Fintype.card (Vertex n ℓ) = 2^ℓ * Nat.choose n ℓ := by
  have h : ∀ S : View n ℓ, S.val.card = ℓ := fun S => S.property
  simp [Vertex, Fintype.card_sigma, h, card_view, Nat.mul_comm]

/-- Distinct views give distinct vertices by labelling every coordinate false. -/
def zeroLabel {n ℓ : ℕ} (S : View n ℓ) : Vertex n ℓ := ⟨S, fun _ => false⟩

/-- Structural witness: the family of K-vertex selections is nonempty,
including K=0 outside the graph domain and K=1 at ell=n. -/
theorem selections_nonempty (n ℓ : ℕ) : (selections n ℓ).Nonempty := by
  let H : Finset (Vertex n ℓ) := Finset.univ.image zeroLabel
  have hinj : Function.Injective (@zeroLabel n ℓ) := by
    intro S T h
    exact congrArg Sigma.fst h
  refine ⟨H, ?_⟩
  simp only [selections, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  simpa [H, Finset.card_image_of_injective _ hinj] using card_view n ℓ

/-- The source optimum is a maximum of an explicitly nonempty finite family;
there is no default supremum and no assumed optimizing selection. -/
def maxDensity {n m : ℕ} (φ : CSP n m) (ℓ : ℕ) : ℝ :=
  (selections n ℓ).sup' (selections_nonempty n ℓ) (density φ)

/-- A K-clique, including a singleton clique when K=1. -/
def HasTargetClique {n m : ℕ} (φ : CSP n m) (ℓ : ℕ) : Prop :=
  ∃ H : Finset (Vertex n ℓ), H.card = Nat.choose n ℓ ∧
    ∀ v ∈ H, ∀ w ∈ H, v ≠ w → (graph φ).Adj v w

end BirthdayEntropy.Soundness


