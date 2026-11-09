-- Prove2me | Definitions.Def_MixedCloning_Optimal_Schur
-- name    : MixedCloning_Optimal_Schur
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:00:16.558083+00:00
-- url     : https://prove2.me/theorems/44fc8943-acc4-4723-8d33-7d14578e448d
-- title:
--   Sections 2.4 and 3.4 — Schur modules, tableaux, integrals and Lift
-- statement:
--   A Young diagram is a finite downward-closed set of cells $(i,j)\in\mathbb N^2$. Its height is its first-column length, and its size is its number of cells. Diagram union is cell union; deleting the first row shifts the remaining rows up one position. Interlacing means $\lambda_{i+1}\le\lambda'_i\le\lambda_i$. Adding $k$ top-row boxes gives $\lambda+ke_1$. The function $s_\lambda(1^t)$ counts semistandard tableaux with alphabet of size $t$, with weak row order and strict column order, including $t=0$. Standard tableaux count $\dim P_\lambda$.
--
--   The concrete Schur module $Q^d_\lambda$ is the image of the row symmetrizer times the column antisymmetrizer in tensor space, with its inherited Hilbert inner product. The polynomial action $q^d_\lambda(A)$ is tensor action restricted to this image, including singular $A$. Its matrices are given in explicitly specified orthonormal bases. Let $P=UP_0U^\dagger$, where $P_0$ projects onto the last $r$ coordinates and $U$ is Haar distributed. Then
--
--   $$S^{(d,r)}_{\lambda\mu}=\int q_\lambda(P)\otimes q_\mu(P)\,dP,\qquad
--   \Delta_{\lambda\mu}=\frac{s_{\lambda\cup\mu}(1^r)}{s_{\lambda\cup\mu}(1^d)}I-S^{(d,r)}_{\lambda\mu}.$$
--
--   The partially transposed integral, Hilbert-space operator norm, finite cone of positive product operators, and the Haar-averaged embedding operation Lift are defined explicitly. A branching family consists only of isometries intertwining the first-coordinate $U(d-1)$ action; completeness is a theorem, not a condition. Weak Schur sampling expectation is the actual finite sum
--
--   $$\mathbb E[f(\lambda)]=\sum_{\lambda\vdash n,\,\ell(\lambda)\le r}\frac{\dim(P_\lambda)s_\lambda(1^r)}{r^n}f(\lambda).$$
--
--   These definitions supply concrete representation-theoretic objects, rather than uninterpreted dimensions or an assumed probability law.
-- source:
--   Dmitry Grinko, Marco Fanizza, Thilo Scharnhorst, Jack Spilecki, Optimal cloning of mixed states, STOC 2027 submission #243 (October 2026), pp. 12–15, 18–25

import Definitions.Def_MixedCloning_Optimal_Model

noncomputable section

namespace MixedCloning.Optimal

open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Cell (L : YoungDiagram) := {c : ℕ × ℕ // c ∈ L.cells}

def height (L : YoungDiagram) : ℕ := L.colLen 0

/-- All Young diagrams fitting in a finite rectangle. -/
def diagramsInBox (h w : ℕ) : Finset YoungDiagram :=
  ((Finset.range h ×ˢ Finset.range w).powerset).biUnion fun S =>
    if hs : IsLowerSet (S : Set (ℕ × ℕ)) then {⟨S,hs⟩} else ∅

def partitions (n d : ℕ) : Finset YoungDiagram :=
  (diagramsInBox d n).filter fun L => L.card = n

def branches (d : ℕ) (L : YoungDiagram) : Finset YoungDiagram :=
  (diagramsInBox d (L.rowLen 0)).filter fun M =>
    ∀ i : ℕ, L.rowLen (i+1) ≤ M.rowLen i ∧ M.rowLen i ≤ L.rowLen i

def Interlaces (M L : YoungDiagram) : Prop :=
  ∀ i : ℕ, L.rowLen (i+1) ≤ M.rowLen i ∧ M.rowLen i ≤ L.rowLen i

/-- Delete the top row, shifting every remaining row up by one. -/
def tailDiagram (L : YoungDiagram) : YoungDiagram where
  cells := (L.cells.filter fun c => 0 < c.1).image fun c => (c.1-1,c.2)
  isLowerSet := by
    intro b a hab hb
    obtain ⟨c,hc,hcb⟩ := Finset.mem_image.mp hb
    obtain ⟨hcL,hcpos⟩ := Finset.mem_filter.mp hc
    apply Finset.mem_image.mpr
    refine ⟨(a.1+1,a.2),Finset.mem_filter.mpr ⟨?_,by omega⟩,by simp⟩
    apply L.isLowerSet (show (a.1+1,a.2) ≤ c from ?_) hcL
    change a.1+1 ≤ c.1 ∧ a.2 ≤ c.2
    have h1 := hab.1
    have h2 := hab.2
    have e1 := congrArg Prod.fst hcb
    have e2 := congrArg Prod.snd hcb
    simp only at e1 e2
    omega

def addTop (L : YoungDiagram) (k : ℕ) : YoungDiagram :=
  L ⊔ YoungDiagram.ofRowLens [L.rowLen 0 + k] (by rw [List.sortedGE_iff_pairwise]; exact List.pairwise_singleton _ _)

/-- Semistandard tableaux: weak along rows, strict down columns. -/
def IsSSYT (L : YoungDiagram) (t : ℕ) (T : Cell L → Fin t) : Prop :=
  (∀ a b : Cell L, a.val.1 = b.val.1 → a.val.2 ≤ b.val.2 → T a ≤ T b) ∧
  (∀ a b : Cell L, a.val.2 = b.val.2 → a.val.1 < b.val.1 → T a < T b)

def schurCount (L : YoungDiagram) (t : ℕ) : ℕ :=
  Fintype.card {T : Cell L → Fin t // IsSSYT L t T}

/-- Standard tableaux give dim P_lambda. -/
def spechtDim (L : YoungDiagram) : ℕ :=
  Fintype.card {T : Cell L → Fin L.card // Function.Bijective T ∧
    (∀ a b : Cell L, a.val.1 = b.val.1 → a.val.2 < b.val.2 → T a < T b) ∧
    (∀ a b : Cell L, a.val.2 = b.val.2 → a.val.1 < b.val.1 → T a < T b)}

def ratio (L : YoungDiagram) (r d : ℕ) : ℝ := (schurCount L r : ℝ) / schurCount L d

def content (c : ℕ × ℕ) : ℤ := (c.2 : ℤ) - c.1

def hook (L : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  (L.cells.filter fun x => (x.1 = c.1 ∧ c.2 ≤ x.2) ∨ (x.2 = c.2 ∧ c.1 < x.1)).card

/-- Tensor permutation on the cells; this is the public Young-symmetrizer body
with cells used directly as tensor labels instead of numbering them by Fin n. -/
def cellPermutation (L : YoungDiagram) (d : ℕ) (p : Equiv.Perm (Cell L)) :
    Op (Cell L → Fin d) := fun i j => if i = j ∘ p.symm then 1 else 0

def youngOperator (L : YoungDiagram) (d : ℕ) : Op (Cell L → Fin d) :=
  ∑ a ∈ Finset.univ.filter (fun p : Equiv.Perm (Cell L) => ∀ c, (p c).val.1 = c.val.1),
    ∑ b ∈ Finset.univ.filter (fun p : Equiv.Perm (Cell L) => ∀ c, (p c).val.2 = c.val.2),
      ((((Equiv.Perm.sign b : ℤˣ) : ℤ) : ℂ)) • cellPermutation L d (a*b)

/-- Image of row symmetrizer times column antisymmetrizer with inherited inner product. -/
def schurModule (L : YoungDiagram) (d : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Cell L → Fin d)) :=
  LinearMap.range (Matrix.toEuclideanLin (youngOperator L d))

def cellTensor (L : YoungDiagram) {d : ℕ} (A : Op (Fin d)) : Op (Cell L → Fin d) :=
  fun i j => ∏ c : Cell L, A (i c) (j c)

/-- Same polynomial action on singular matrices as on unitaries. -/
def polynomialRepresentation (L : YoungDiagram) {d : ℕ} (A : Op (Fin d)) :
    schurModule L d →ₗ[ℂ] schurModule L d :=
  (schurModule L d).orthogonalProjectionOnto.toLinearMap.comp
    ((Matrix.toEuclideanLin (cellTensor L A)).comp (schurModule L d).subtype)

abbrev SchurIndex (L : YoungDiagram) (d : ℕ) := Fin (Module.finrank ℂ (schurModule L d))
abbrev SchurBasis (L : YoungDiagram) (d : ℕ) :=
  OrthonormalBasis (SchurIndex L d) ℂ (schurModule L d)

def schurBasis (L : YoungDiagram) (d : ℕ) : SchurBasis L d := stdOrthonormalBasis ℂ (schurModule L d)

def q (L : YoungDiagram) {d : ℕ} (b : SchurBasis L d) (A : Op (Fin d)) : Op (SchurIndex L d) :=
  LinearMap.toMatrix b.toBasis b.toBasis (polynomialRepresentation L A)

/-- Matrix of the integral in any specified orthonormal bases. -/
def schurIntegral {d : ℕ} (r : ℕ) (L M : YoungDiagram)
    (b : SchurBasis L d) (c : SchurBasis M d) : Op (SchurIndex L d × SchurIndex M d) :=
  ∫ U, Matrix.kronecker (q L b (rotatedProjector r U)) (q M c (rotatedProjector r U)) ∂haar d

def transposedIntegral {d : ℕ} (r : ℕ) (L M : YoungDiagram)
    (b : SchurBasis L d) (c : SchurBasis M d) : Op (SchurIndex L d × SchurIndex M d) :=
  ∫ U, Matrix.kronecker (q L b (rotatedProjector r U)).transpose (q M c (rotatedProjector r U)) ∂haar d

/-- Operator norm induced by the Hilbert-space norm, not an entrywise matrix norm. -/
def operatorNorm {a : Type} [Fintype a] [DecidableEq a] (A : Op a) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- Finite nonnegative combinations of positive product matrices. -/
def Separable {a b : Type} [Fintype a] [Fintype b] (X : Op (a × b)) : Prop :=
  ∃ (N : ℕ) (w : Fin N → ℝ) (A : Fin N → Op a) (B : Fin N → Op b),
    (∀ j, 0 ≤ w j ∧ (A j).PosSemidef ∧ (B j).PosSemidef) ∧
    X = ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (B j)

def delta {d : ℕ} (r : ℕ) (L M : YoungDiagram) (b : SchurBasis L d) (c : SchurBasis M d) :
    Op (SchurIndex L d × SchurIndex M d) :=
  (ratio (L ⊔ M) r d : ℂ) • 1 - schurIntegral r L M b c

/-- U(d-1) acts on the first coordinates and fixes the last. -/
def embedMatrix (d : ℕ) (V : Op (Fin d)) : Op (Fin (d+1)) :=
  fun i j => if hi : i.val < d then
    if hj : j.val < d then V ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0
    else if j.val = d then 1 else 0

/-- Branching embeddings for every interlacing pair, without assuming completeness. -/
def BranchFamily (d : ℕ) (L : YoungDiagram) :=
  (M : {M : YoungDiagram // M ∈ branches d L}) →
    Matrix (SchurIndex L (d+1)) (SchurIndex M.val d) ℂ

def IsBranchFamily (d : ℕ) (L : YoungDiagram) (E : BranchFamily d L) : Prop :=
  ∀ M, (E M)ᴴ * E M = 1 ∧
    ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
      E M * q M.val (schurBasis M.val d) (V : Op (Fin d)) =
        q L (schurBasis L (d+1)) (embedMatrix d (V : Op (Fin d))) * E M

/-- Lift is concrete conjugation, embedding, and normalized Haar integration. -/
def lift {d : ℕ} {L M : YoungDiagram} (E : BranchFamily d L) (G : BranchFamily d M)
    (L' : {L' : YoungDiagram // L' ∈ branches d L})
    (M' : {M' : YoungDiagram // M' ∈ branches d M})
    (X : Op (SchurIndex L'.val d × SchurIndex M'.val d)) :
    Op (SchurIndex L (d+1) × SchurIndex M (d+1)) :=
  ∫ U : Matrix.unitaryGroup (Fin (d+1)) ℂ,
    let V := Matrix.kronecker (q L (schurBasis L (d+1)) (U : Op (Fin (d+1))))
      (q M (schurBasis M (d+1)) (U : Op (Fin (d+1))))
    let H := Matrix.kronecker (E L') (G M')
    V * H * X * Hᴴ * Vᴴ ∂haar (d+1)

/-- WSS expectation as the actual finite tableau-weighted sum. -/
def wssExpectation (n r : ℕ) (f : YoungDiagram → ℝ) : ℝ :=
  ∑ L ∈ partitions n r, (spechtDim L : ℝ) * schurCount L r / (r : ℝ)^n * f L

def extraProduct (d r k : ℕ) (L : YoungDiagram) : ℝ :=
  ∏ j : Fin k, ((r : ℝ) + L.rowLen 0 + j.val) / ((d : ℝ) + L.rowLen 0 + j.val)

end MixedCloning.Optimal


