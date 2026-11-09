-- Prove2me | Definitions.Def_MultipleUnicast_Counterexample_LocalSpace
-- name    : MultipleUnicast_Counterexample_LocalSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:30.828034+00:00
-- url     : https://prove2.me/theorems/e16b8bf0-b619-4215-ba61-9c940c1d60af
-- title:
--   Exact quartic local images, compatible spaces, and restriction
-- statement:
--   At a vertex $v$, take the first two normalized triples orthogonal to its representative as the ordered basis $u,w$. Express a neighboring triple as $\lambda u+\mu w$, without renormalizing the coordinates. With coefficients $a_0,\ldots,a_4\in\mathbb F_9$, the allowed incident values are
--   $$Q(\lambda,\mu)=\sum_{r=0}^4a_r\lambda^{4-r}\mu^r$$
--   on the point side, and $Q(\lambda^3,\mu^3)$ on the line side. The compatible-assignment space $W$ imposes these actual local image conditions at every vertex. Define
--   $$W_C=\{w\in W:w|_C=0\},\qquad \operatorname{restriction}(w)=w|_B.$$
--
--   The available positions at $v$ are incoming physical edges, incoming artificial $B$ edges, and all incident $C$ edges. Interpolation solves the local evaluation equations on these positions, with a zero fallback if unsolvable. Its uniqueness, solvability and linearity are theorem conclusions.
--
--   These definitions expose the mathematical spaces needed for the Appendix B dimension bound and §4's extension assertion. In particular, neither the dimension bound nor surjectivity is built into $W$.
--
--   **Formalization Note** Local evaluation is masked to zero on nonincident coordinates, and compatibility is the intersection of preimages of its image under the incident-coordinate projections. This is exactly the source's restriction condition. Coordinate solving and interpolation use classical choice; the uniqueness conclusions ensure that this choice does not alter a value on the source's domain.
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, §3, PDF p. 6 / printed p. 5; §4, PDF pp. 11–12 / printed pp. 10–11; Appendix B, PDF pp. 15–16 / printed pp. 14–15

import Definitions.Def_MultipleUnicast_Counterexample_Graph

set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample
noncomputable section
open scoped Classical

abbrev Coefficients := Fin 5 → F9

def vertexTriple (v : Vertex) : Fin 91 := ⟨v.val % 91, Nat.mod_lt _ (by decide)⟩
def neighborTriples (v : Vertex) : List (Fin 91) :=
  (List.finRange 91).filter fun j => dot (triple (vertexTriple v)) (triple j) = 0

def basisU (v : Vertex) : Triple := triple ((neighborTriples v).getD 0 0)
def basisW (v : Vertex) : Triple := triple ((neighborTriples v).getD 1 0)
def neighborOn (v : Vertex) (q : Edge) : Triple :=
  triple (if v.val < 91 then (edgePair q).2 else (edgePair q).1)

/-- Solve the exact vector equation, with a total default outside its domain.
Uniqueness on incident positions is a mathematical obligation, never an assumption. -/
def coordinates (v : Vertex) (q : Edge) : F9 × F9 :=
  if h : ∃ c : F9 × F9, neighborOn v q = c.1 • basisU v + c.2 • basisW v
  then Classical.choose h else (0, 0)

def localWeight (v : Vertex) (q : Edge) (r : Fin 5) : F9 :=
  let c := coordinates v q
  let x := if v.val < 91 then c.1 else c.1 ^ 3
  let y := if v.val < 91 then c.2 else c.2 ^ 3
  x ^ (4 - r.val) * y ^ r.val

/-- The local image, masked to zero away from the incident positions. -/
def localEvaluation (v : Vertex) : Coefficients →ₗ[F9] (Edge → F9) where
  toFun a q := if incident v q then ∑ r, a r * localWeight v q r else 0
  map_add' a b := by funext q; simp only [Pi.add_apply]; split_ifs <;> simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    funext q
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Finset.mul_sum, mul_assoc]

def incidentValues (v : Vertex) : (Edge → F9) →ₗ[F9] (Edge → F9) where
  toFun x q := if incident v q then x q else 0
  map_add' a b := by funext q; simp; split_ifs <;> simp
  map_smul' c a := by funext q; simp

/-- Actual simultaneous local compatibility, rather than a dimension assumption. -/
def W : Submodule F9 (Edge → F9) :=
  ⨅ v : Vertex, Submodule.comap (incidentValues v) (LinearMap.range (localEvaluation v))

def WC : Submodule F9 (Edge → F9) :=
  W ⊓ ⨅ q : {q : Edge // q ∈ C}, LinearMap.ker (LinearMap.proj q.val)

def restriction : WC →ₗ[F9] (Session → F9) where
  toFun w q := w.val q.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The five positions available when v is processed, as specified in §4. -/
def knownPositions (v : Vertex) : Finset Edge :=
  Finset.univ.filter fun q =>
    (q ∈ physical ∧ head q = v) ∨ (q ∈ B ∧ head q = v) ∨ (q ∈ C ∧ incident v q)

/-- Local interpolation uses only supplied values on the available positions.
A nonsolvable input has a declared zero default, to be excluded by conclusions. -/
def interpolate (v : Vertex) (y : Edge → F9) : Coefficients :=
  if h : ∃ a : Coefficients, ∀ q ∈ knownPositions v, localEvaluation v a q = y q
  then Classical.choose h else 0

end
end MultipleUnicast.Counterexample


