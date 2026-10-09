-- Prove2me | Definitions.Def_Octonion_normSq
-- name    : Octonion_normSq
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-09-23T13:25:48.240965+00:00
-- url     : https://prove2.me/theorems/a5430fa5-269b-43a1-9908-80a383c1172e
-- title:
--   The octonion squared norm
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Write $N(x)=\sum_{i=0}^7 x_i^2$ for the squared norm in the coordinate order $(a_0,a_1,a_2,a_3,b_0,b_1,b_2,b_3)$. Explicitly, $$N(a,b)=N_{\mathbb H}(a)+N_{\mathbb H}(b).$$ This quadratic form is defined over any commutative base ring.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Def_Octonion_normSq.lean; SHA-256 3f929ff5eb16f3571cd1948c149fc1f4f592d509d75eaeeba430bcd68a9a4f52.

import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Quaternion

namespace Octonion
variable {R : Type*} [CommRing R]

/-- Squared norm: `N (a, b) = N a + N b`, the sum of the two quaternion norms,
valued in the base ring. -/
def normSq (x : octonions R) : R := Quaternion.normSq x.fst + Quaternion.normSq x.snd

@[simp] theorem normSq_mk (a b : ℍ[R]) :
    normSq ⟨a, b⟩ = Quaternion.normSq a + Quaternion.normSq b := rfl

@[simp] theorem normSq_conj (x : octonions R) : normSq (conj x) = normSq x := by
  obtain ⟨a, b⟩ := x
  show normSq (conj ⟨a, b⟩) = normSq ⟨a, b⟩
  simp [normSq_mk, conj]

end Octonion


