-- Prove2me | Definitions.Def_TwoReLULayers_DepthCollapse_Supplement_Polytopes
-- name    : TwoReLULayers_DepthCollapse_Supplement_Polytopes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T22:24:44.441775+00:00
-- url     : https://prove2.me/theorems/85dc1c44-98e4-42cf-99e5-7eb845930e7c
-- title:
--   Rational oriented polytope quotient and facet boundary
-- statement:
--   Let $n,k\ge0$ be ambient dimension and degree. Rational points are elements of $\mathbb Q^n$, embedded coordinatewise in the published real Euclidean carrier. An oriented polytope generator consists of a rational ordered $k$-frame and a finite rational vertex set. Its polytope is the real convex hull of those vertices. The frame spans its direction space; changing the frame changes the sign exactly when its determinant is negative.
--
--   For positive degree the geometric rational vector space is the quotient
--   $$P_k^n=\left(\bigoplus_{\dim S=k}\widetilde V_S\otimes\operatorname{or}(S)\right),\qquad
--   \widetilde V_S=V_S/(\text{translations}+\sum_{S'<S}V_{S'}).$$
--   The finite presentation imposes equality of convex hulls, Minkowski additivity, nonnegative rational dilation, translation invariance, lower-dimensional vanishing, and the orientation-sign relation. These are precisely the geometric relations, with no paramid-generation relation. Negative coefficients are formal differences, not reflection of a polytope. In degree zero only point generators and global translation relations survive; positive-degree Minkowski relations are omitted there.
--
--   The boundary is the finite sum of exposed facets, with outward-normal-first orientation. Facets are detected by rational supporting normals and their entire vertex sets. Rational facet frames and normals are selected by choice; the quotient representative is also selected by choice before evaluating the facet sum. These selections do not impose any injectivity, homology, generation, or filling condition. Independence from these choices, linearity and the chain identity remain the standard well-definedness proof obligations of the geometric construction. The boundary in degree zero is zero; in degree one it is the endpoint difference modulo global translations.
--
--   The standard simplex class is the class of $\operatorname{conv}(0,e_1,\ldots,e_n)$ with the standard orientation. Finally $\Lambda_k^n$ is the rational linear span of all $k$-dimensional paramid classes, using the published box geometry and actual rational apex, base point and independent edge witnesses. There is no lattice or apex restriction. This definition layer supplies the geometric target for every added result.
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026). Use this pinned PDF and its own labels; no arXiv version is asserted. pp. 10–11 and 14, Sections 2.1 and 3.1.

import Definitions.Def_TwoReLULayers_DepthCollapse_Geometry

namespace TwoReLULayers.DepthCollapse.Supplement

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev QSpace (n : ℕ) := Fin n → ℚ

def realPoint {n : ℕ} (x : QSpace n) : E n :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

def hull {n : ℕ} (v : Finset (QSpace n)) : Set (E n) :=
  convexHull ℝ (realPoint '' (v : Set (QSpace n)))

def direction {n : ℕ} (v : Finset (QSpace n)) : Submodule ℚ (QSpace n) :=
  Submodule.span ℚ {z | ∃ a ∈ v, ∃ b ∈ v, z = a - b}

/-- A presentation generator. Invalid frames and lower-dimensional terms are killed
by explicit relations, rather than restricting the vector space to paramids. -/
structure PolyGenerator (n k : ℕ) where
  frame : Fin k → QSpace n
  vertices : Finset (QSpace n)

abbrev PolyFree (n k : ℕ) := PolyGenerator n k →₀ ℚ

def gen {n k : ℕ} (g : PolyGenerator n k) : PolyFree n k := Finsupp.single g 1

def Valid {n k : ℕ} (g : PolyGenerator n k) : Prop :=
  LinearIndependent ℚ g.frame ∧ g.vertices.Nonempty ∧
    direction g.vertices ≤ Submodule.span ℚ (Set.range g.frame)

def translate {n k : ℕ} (g : PolyGenerator n k) (t : QSpace n) : PolyGenerator n k :=
  ⟨g.frame, g.vertices.image (fun x => x + t)⟩

def minkowskiVertices {n : ℕ} (v w : Finset (QSpace n)) : Finset (QSpace n) :=
  (v ×ˢ w).image (fun p => p.1 + p.2)

def signQ (q : ℚ) : ℚ := if 0 < q then 1 else -1

/-- A simultaneous presentation of the direct sum of reduced Minkowski spaces.
Only the positive-degree relations impose Minkowski additivity and dilation.
In degree zero the surviving singleton generators are identified by translations,
exactly as in the source's separate definition of P₀. -/
inductive PolyRelation (n k : ℕ) : PolyFree n k → Prop
  | invalid (g : PolyGenerator n k) (h : ¬ Valid g) : PolyRelation n k (gen g)
  | lower (g : PolyGenerator n k) (h : Module.finrank ℚ (direction g.vertices) < k) :
      PolyRelation n k (gen g)
  | translation (g : PolyGenerator n k) (t : QSpace n) :
      PolyRelation n k (gen (translate g t) - gen g)
  | orientation (g h : PolyGenerator n k) (A : Matrix (Fin k) (Fin k) ℚ)
      (hA : A.det ≠ 0) (hf : ∀ j, h.frame j = ∑ i, A i j • g.frame i)
      (hp : hull g.vertices = hull h.vertices) :
      PolyRelation n k (gen h - signQ A.det • gen g)
  | minkowski (hk : 0 < k) (g h : PolyGenerator n k)
      (hg : Valid g) (hh : Valid h) (hf : g.frame = h.frame) :
      PolyRelation n k
        (gen ⟨g.frame, minkowskiVertices g.vertices h.vertices⟩ - gen g - gen h)
  | dilation (hk : 0 < k) (g : PolyGenerator n k) (hg : Valid g)
      (q : ℚ) (hq : 0 ≤ q) :
      PolyRelation n k
        (gen ⟨g.frame, g.vertices.image (fun x => q • x)⟩ - q • gen g)

def polyRelations (n k : ℕ) : Submodule ℚ (PolyFree n k) :=
  Submodule.span ℚ {r | PolyRelation n k r}

/-- Genuine rational geometric quotient; it has generators for every rational polytope
and every oriented rational direction space, not only the paramid generators. -/
abbrev P (n k : ℕ) := PolyFree n k ⧸ polyRelations n k

def polyClass {n k : ℕ} (g : PolyGenerator n k) : P n k :=
  (polyRelations n k).mkQ (gen g)

def dotQ {n : ℕ} (x y : QSpace n) : ℚ := ∑ i, x i * y i

/-- Rational outward normals. An exposed face includes every supplied hull vertex
on its supporting hyperplane, so a facet occurs exactly once in the powerset sum. -/
def Exposes {n k : ℕ} (g : PolyGenerator n (k + 1))
    (w : Finset (QSpace n)) (v : QSpace n) : Prop :=
  v ∈ Submodule.span ℚ (Set.range g.frame) ∧ v ≠ 0 ∧
    ∃ c : ℚ, (∀ x ∈ g.vertices, dotQ v x ≤ c) ∧
      ∀ x, x ∈ w ↔ x ∈ g.vertices ∧ dotQ v x = c

def IsFacetVertices {n k : ℕ} (g : PolyGenerator n (k + 1))
    (w : Finset (QSpace n)) : Prop :=
  w.Nonempty ∧ Module.finrank ℚ (direction w) = k ∧ ∃ v, Exposes g w v

/-- Choice only selects a rational frame of the known k-dimensional direction space.
Its existence on a qualifying facet is finite-dimensional linear algebra. -/
def facetFrame {n k : ℕ} (w : Finset (QSpace n)) : Fin k → QSpace n :=
  Classical.epsilon (fun A => LinearIndependent ℚ A ∧
    Submodule.span ℚ (Set.range A) = direction w)

def facetNormal {n k : ℕ} (g : PolyGenerator n (k + 1))
    (w : Finset (QSpace n)) : QSpace n := Classical.epsilon (Exposes g w)

/-- Coordinate matrix of an ordered frame in a spanning frame. On the valid
full-dimensional inputs below this matrix exists uniquely. -/
def frameCoordinates {n k : ℕ} (B A : Fin k → QSpace n) : Matrix (Fin k) (Fin k) ℚ :=
  Classical.epsilon (fun M => ∀ j, A j = ∑ i, M i j • B i)

def facetSign {n k : ℕ} (g : PolyGenerator n (k + 1))
    (w : Finset (QSpace n)) : ℚ :=
  signQ (frameCoordinates g.frame
    (Fin.cons (facetNormal g w) (facetFrame w))).det

/-- Outward-normal-first facet boundary, before descent. Lower-dimensional and
invalid generators are zero already; in dimension one this is the endpoint difference. -/
def generatorBoundary {n k : ℕ} (g : PolyGenerator n (k + 1)) : P n k :=
  if Valid g ∧ Module.finrank ℚ (direction g.vertices) = k + 1 then
    ∑ w ∈ g.vertices.powerset,
      if IsFacetVertices g w then
        facetSign g w • polyClass ⟨facetFrame w, w⟩
      else 0
  else 0

/-- Evaluate the geometric boundary on a representative of the specified quotient.
The representative is selected, never an assumed boundary or a filling certificate.
Independence of the representative, linearity, and d²=0 are the well-definedness
proof obligations of this geometric construction, not hypotheses of any milestone. -/
def dP (n : ℕ) : (k : ℕ) → P n k → P n (k - 1)
  | 0, _ => 0
  | k + 1, x => (Quotient.out x).sum (fun g q => q • generatorBoundary g)

def standardFrame (n : ℕ) : Fin n → QSpace n := fun i j => if i = j then 1 else 0

def simplexVertices (n : ℕ) : Finset (QSpace n) :=
  insert 0 (Finset.univ.image (standardFrame n))

/-- Part 1 simplex conv(0,e₁,...,eₙ), with its standard n-dimensional orientation. -/
def simplexClass (n : ℕ) : P n n := polyClass ⟨standardFrame n, simplexVertices n⟩

/-- Published paramid geometry, with actual rational apex, base point and edges. -/
def RationalParamid {n : ℕ} (v : Finset (QSpace n)) : Prop :=
  ∃ m : ℕ, ∃ a apex : QSpace n, ∃ e : Fin m → QSpace n,
    LinearIndependent ℝ (fun j => realPoint (e j)) ∧
      hull v = convexHull ℝ (insert (realPoint apex)
        (box (realPoint a) (fun j => realPoint (e j))))

/-- All rational k-dimensional paramids in all direction spaces and orientations.
In particular no lattice, simplex-edge or apex-zero restriction is present. -/
def Lambda (n k : ℕ) : Submodule ℚ (P n k) :=
  Submodule.span ℚ {x | ∃ g : PolyGenerator n k, Valid g ∧
    Module.finrank ℚ (direction g.vertices) = k ∧ RationalParamid g.vertices ∧
    x = polyClass g}

end
end TwoReLULayers.DepthCollapse.Supplement


