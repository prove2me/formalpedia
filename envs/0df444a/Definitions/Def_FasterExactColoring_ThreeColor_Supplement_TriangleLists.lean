-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TriangleLists
-- name    : FasterExactColoring_ThreeColor_Supplement_TriangleLists
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:47:17.354109+00:00
-- url     : https://prove2.me/theorems/f9d18fe0-591e-468d-9d54-b05cefe30b4f
-- title:
--   Triangle two-list assignments and the explicit sublinear envelope
-- statement:
--   Label the vertices of $n$ disjoint triangles by $(i,v)$, with $i\in\{0,\ldots,n-1\}$ and $v\in\{0,1,2\}$. A two-list assignment gives each vertex a two-element subset of the four colors. Compatibility means membership at every vertex. The covered colorings are injective on each triangle and use the distinguished fourth color on every triangle. For $c\in[3]$ and a triangle vertex $x$, the nine local candidates give $[3]\setminus\{c\}$ at $x$ and $\{c,4\}$ elsewhere.
--
--   For $n>0$, put $m=\lceil\ln(n+2)\rceil$, $b=\lceil n/m\rceil$, and
--   $$B_j=\lceil(9/2)^j j\ln18\rceil,\qquad h(n)=b\ln(m\ln18+1),\qquad h(0)=0.$$
--
--   The predicate of sublinearity requires $h\ge0$ and, for every $\epsilon>0$, a threshold $N$ such that $h(n)\le\epsilon n$ for all $n\ge N$. Finite list families and their complete encodings allow construction, coverage, size, and enumeration work to be asserted together in Lemma 5.3.
--
--   **Formalization Note** Natural ceilings and division implement the block sizes. The expression for $m$ is guarded by $\max(1,\cdot)$, which changes no value because $\lceil\ln(n+2)\rceil\ge1$. The argument $n$ counts triangles in this module.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.3 and its proof, pp. 11–12 (PDF pp. 13–14)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Execution

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

abbrev TriangleVertex (n : ℕ) := Fin n × Fin 3
abbrev TwoLists (n : ℕ) := TriangleVertex n → Finset (Fin 4)

def localChoice (c x : Fin 3) (v : Fin 3) : Finset (Fin 4) :=
  if v = x then (Finset.univ.filter (fun a : Fin 4 => a.val < 3 ∧ a.val ≠ c.val))
  else {⟨c.val, Nat.lt_trans c.isLt (by decide)⟩, 3}

def triangleColoring {n : ℕ} (f : TriangleVertex n → Fin 4) : Prop :=
  ∀ i, Function.Injective (fun v => f (i,v)) ∧ ∃ v, f (i,v) = 3

def twoListsValid {n : ℕ} (L : TwoLists n) : Prop := ∀ v, (L v).card = 2
def compatible {n : ℕ} (f : TriangleVertex n → Fin 4) (L : TwoLists n) : Prop :=
  ∀ v, f v ∈ L v

def twoListsCode {n : ℕ} (L : TwoLists n) : List ℕ :=
  ((List.finRange n).flatMap (fun i => (List.finRange 3).flatMap (fun v =>
    vertexList (L (i,v)))))
where vertexList (X : Finset (Fin 4)) := X.card :: (X.sort (· ≤ ·)).map Fin.val

def triangleFamilyCode {n : ℕ} (F : List (TwoLists n)) : List ℕ :=
  F.length :: F.flatMap twoListsCode

noncomputable def coverBlockSize (n : ℕ) : ℕ := max 1 ⌈Real.log (n+2 : ℕ)⌉₊
noncomputable def coverBlockCount (n : ℕ) : ℕ :=
  (n + coverBlockSize n - 1) / coverBlockSize n
noncomputable def greedyBlockBound (j : ℕ) : ℕ :=
  ⌈(9/2 : ℝ)^j * j * Real.log 18⌉₊

/-- Explicit logarithmic envelope from the block construction, with its empty case. -/
noncomputable def coverEnvelope (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    coverBlockCount n * Real.log ((coverBlockSize n : ℝ)*Real.log 18 + 1)

def sublinear (h : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ h n) ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, h n ≤ ε*n

end FasterExactColoring.ThreeColor.Supplement


