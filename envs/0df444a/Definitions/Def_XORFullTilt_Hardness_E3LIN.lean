-- Prove2me | Definitions.Def_XORFullTilt_Hardness_E3LIN
-- name    : XORFullTilt_Hardness_E3LIN
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:53:39.254221+00:00
-- url     : https://prove2.me/theorems/0c7685ba-be13-46ae-81ab-0dfb66028d7d
-- title:
--   E3-LIN games and the exact shared cube gadget
-- statement:
--   An E3-LIN system has variables $1,\ldots,m$ and a finite set of tagged equations $v_i\oplus v_j\oplus v_k=c$, where $i<j<k$ and $c\in\{0,1\}$. Its equation law is arbitrary. The referee samples an equation, chooses one of its three variables uniformly, and accepts a three-bit Alice answer and one-bit Bob answer precisely when Alice's parity is $c$ and their queried bits agree.
--
--   The tilted cube reduction samples an equation and a uniformly random cube pair. Alice's three nonzero even vertices are identified with the equation's global variables and all $000$ vertices are identified with a common $\bot$. Bob's four odd vertices retain separate equation tags. Only the bottom row's signs are flipped for parity-one equations:
--   $$f(\bot,(r,y))=f_{\square}(000,y)\oplus c_r.$$
--   All other sampled signs are the original cube signs. Indices $0,\ldots,m-1$ encode the source's $1,\ldots,m$.
--
--   The gadget is a concrete construction. No classical assignment, operator solution or transfer estimate is assumed.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), pp.12–15, Definition 2.9 and §2.5; p.28, proof of Theorem 4.2

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_FiniteLaws

namespace XORFullTilt.Hardness

/-- Increasing triples use indices 0,...,m-1, corresponding to the source's 1,...,m. -/
abbrev IncreasingTriple (m : ℕ) := {v : Fin 3 → Fin m // v 0 < v 1 ∧ v 1 < v 2}
abbrev E3Equation (m : ℕ) := Bool × IncreasingTriple m

structure E3System (m : ℕ) where
  relations : Finset (E3Equation m)

abbrev E3Question {m : ℕ} (S : E3System m) := {r : E3Equation m // r ∈ S.relations}

noncomputable def e3Game {m : ℕ} (S : E3System m) (π : PMF (E3Question S)) :
    MIPRE.Game (E3Question S) (Fin m) Triple Bool := by
  classical
  let law := π.bind (fun r => (PMF.uniformOfFintype (Fin 3)).map (fun i => (r,r.val.2.val i)))
  exact gameOfPMF law (fun r y a b => decide (parity a = r.val.1 ∧
    ∃ i : Fin 3, r.val.2.val i = y ∧ a i = b))

def localVertex {m : ℕ} (r : E3Equation m) (x : Fin 4) : Option (Fin m) :=
  if h : x = 0 then none else some (r.2.val ⟨x.val-1, by omega⟩)

/-- The exact source gadget: shared variables and bottom, separately tagged odd vertices,
    equation law then a uniform cube pair, and only the bottom row sign flipped for parity one. -/
noncomputable def cubeReduction {m : ℕ} (S : E3System m) (π : PMF (E3Question S)) :
    TiltedGame (Option (Fin m)) (E3Question S × Fin 4) := by
  classical
  let law := π.bind (fun r => (PMF.uniformOfFintype (Fin 4 × Fin 4)).map
    (fun xy => (localVertex r.val xy.1,(r,xy.2))))
  exact tiltedOfPMF law none (fun x ry =>
    if x = none then Bool.xor (cube.f 0 ry.2) ry.1.val.1
    else cube.f (if x = some (ry.1.val.2.val 0) then 1 else
      if x = some (ry.1.val.2.val 1) then 2 else 3) ry.2)

end XORFullTilt.Hardness


