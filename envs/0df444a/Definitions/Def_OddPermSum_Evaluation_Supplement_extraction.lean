-- Prove2me | Definitions.Def_OddPermSum_Evaluation_Supplement_extraction
-- name    : OddPermSum_Evaluation_Supplement_extraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:37:54.750597+00:00
-- url     : https://prove2.me/theorems/81ce18c8-60b9-4720-a94c-caf31950f96a
-- title:
--   The deterministic extraction procedure of §6.1
-- statement:
--   Fix a graph, arbitrary arc weights $\beta$, a candidate length $r$, and complete orders of vertices and arcs. Form $A=I+zW_\beta$ and choose the first arc $e=(u,v)$ with $\alpha_e=[z^r](z\beta_eG(A)_{v,u})\ne0$. Force row $u$ to that single arc, deleting its diagonal. At endpoint $i$, choose the first $j\ne i$ with $[z^r](\widehat A_{i,j}G(\widehat A)_{j,i})\ne0$, retain the diagonal and this arc in row $i$, and append $j$. Returning to $u$ triggers verification of a simple directed cycle of length $r$. Missing choices, failed verification, or exceeding $r-1$ extensions return failure.
--
--   The function returns an optional explicit closed vertex list and the actual extension count. Full polynomials represent its pure semantics: every test depends only on coefficients through degree $r$, so reduction modulo $z^{r+1}$ gives identical choices. The efficient implementation is asserted separately.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 16–17, §6.1

import Definitions.Def_OddPermSum_Evaluation_Supplement_digraph
import Definitions.Def_OddPermSum_Evaluation_gradient

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

/-- Fixed total orders, represented by lists without omissions or repetitions. -/
structure ExtractionOrders {n : ℕ} (D : Digraph n) where
  vertices : List (Fin n)
  arcs : List D.Arc
  vertexOrder : vertices.Nodup
  arcOrder : arcs.Nodup
  allVertices : ∀ v, v ∈ vertices
  allArcs : ∀ e, e ∈ arcs

noncomputable def weightedMatrix {F : Type*} [Field F] {n : ℕ} (D : Digraph n)
    (β : D.Arc → F) : Matrix (Fin n) (Fin n) (Polynomial F) := by
  classical
  exact fun i j => (if i = j then 1 else 0) +
    if h : (i,j) ∈ D.arcs then Polynomial.X * Polynomial.C (β ⟨(i,j),h⟩) else 0

noncomputable def initialCoefficient {F : Type*} [Field F] {n : ℕ} (D : Digraph n)
    (β : D.Arc → F) (r : ℕ) (e : D.Arc) : F :=
  (Polynomial.X * Polynomial.C (β e) * gradient (weightedMatrix D β) e.val.2 e.val.1).coeff r

noncomputable def firstArc {F : Type*} [Field F] {n : ℕ} (D : Digraph n)
    (ord : ExtractionOrders D) (β : D.Arc → F) (r : ℕ) : Option D.Arc := by
  classical
  exact ord.arcs.find? (fun e => decide (initialCoefficient D β r e ≠ 0))

/-- Pure §6.1 extension loop; count includes every selected extension, also on failure.
Full polynomials are used here: reducing modulo z^(r+1) preserves every query. -/
noncomputable def extendPath {F : Type*} [Field F] {n : ℕ} (D : Digraph n)
    (ord : ExtractionOrders D) (r : ℕ) (u : Fin n) :
    ℕ → Matrix (Fin n) (Fin n) (Polynomial F) → List (Fin n) → Fin n →
      Option (List (Fin n)) × ℕ
  | 0, _, _, _ => (none,0)
  | fuel+1, A, p, i => by
    classical
    let g := fun j => gradient A j i
    let branch := ord.vertices.find? (fun j => decide (j ≠ i ∧ (A i j * g j).coeff r ≠ 0))
    exact match branch with
    | none => (none,0)
    | some j =>
      let A' := fun a b => if a = i then (if b = i then 1 else 0) +
        (if b = j then A i j else 0) else A a b
      let p' := p ++ [j]
      if j = u then (if ValidCycle D r p' then some p' else none,1)
      else let result := extendPath D ord r u fuel A' p' j
           (result.1,result.2+1)

noncomputable def extract {F : Type*} [Field F] {n : ℕ} (D : Digraph n)
    (ord : ExtractionOrders D) (β : D.Arc → F) (r : ℕ) : Option (List (Fin n)) × ℕ := by
  classical
  exact match firstArc D ord β r with
  | none => (none,0)
  | some e =>
    let u := e.val.1
    let v := e.val.2
    let A := weightedMatrix D β
    let A' := fun i j => if i = u then
      (if j = v then Polynomial.X * Polynomial.C (β e) else 0) else A i j
    extendPath D ord r u (r-1) A' [u,v] v

end OddPermSum.Evaluation.Supplement


