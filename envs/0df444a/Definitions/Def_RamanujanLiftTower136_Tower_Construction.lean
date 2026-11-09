-- Prove2me | Definitions.Def_RamanujanLiftTower136_Tower_Construction
-- name    : RamanujanLiftTower136_Tower_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:30:58.191075+00:00
-- url     : https://prove2.me/theorems/6461c542-3683-4a20-a5b6-eb973036802d
-- title:
--   Deterministic generators, dyadic neighbors, residues, and lift bits
-- statement:
--   Let $\alpha,z\in\mathbb Z_2$ be the even roots of $X^2+3X-2$ and $X^2+X+2$. Embed $F$ in $\mathbb Q_2$ by $r\mapsto2\alpha+3$, and define $\psi$ by the two matrices in (3.8). For an admissible prime $p$, let $s_p$ be the smaller root of $X^2-X-4$ modulo $p$, and choose $\pi=a+b\omega$ by the lexicographically first solution of (7.2) in the specified box.
--
--   The list of labels consists of the vectors $m\in\mathbb Z^8$ with $|m_s|\le\lceil21p^{1/4}\rceil$, reduced norm $\pi$, and first nonzero coordinate positive, sorted lexicographically. Thus its length is a genuine quantity, not prescribed to be $p+1$. Conjugation determines the reverse label by locating its sign class in this list.
--
--   For $g_j=\psi(\overline{x_j})=\left(\begin{smallmatrix}a&b\\c&e\end{smallmatrix}\right)$, the neighbor is
--   $$f_j(t)=(at+b/2)(2ct+e)^{-1}\pmod {2^n}.$$
--   Vertices are $\mathbb Z/2^n\mathbb Z$. The lift bit is the integer quotient of the difference of the least nonnegative residues at levels $n+1$ and $n$, divided by $2^n$. The global order $E_n$ is defined by (3.9), using the prescribed upper-right and lower-left divisibilities in $\psi(O)$.
--
--   **Formalization Note** Pair and vector orders use usual signed-integer lexicographic order. Failed root searches, absent reverse labels, and nonintegral dyadic results have total defaults. No correctness property is assumed; the theorem targets supply correctness and nondegeneracy.
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.9 (PDF p.10), §3.2–§3.5, (3.3), (3.8)–(3.10); §4, (4.1)–(4.4); §6, (6.2)–(6.3); §7.1, (7.2)–(7.5). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Definitions.Def_RamanujanLiftTower136_Tower_Arithmetic

noncomputable section

namespace RamanujanLiftTower136.Tower
open scoped Quaternion
open Classical

/-- Defaults are deliberately total; their validity is a conclusion of the mission. -/
def selectedRoot (P : ℤ_[2] → Prop) : ℤ_[2] := if h : ∃ x, P x then h.choose else 0
def alpha : ℤ_[2] := selectedRoot (fun x => x^2 + 3*x - 2 = 0 ∧ x ∈ Ideal.span {(2 : ℤ_[2])})
def zeta : ℤ_[2] := selectedRoot (fun x => x^2 + x + 2 = 0 ∧ x ∈ Ideal.span {(2 : ℤ_[2])})
def embedDyadic (x : F) : ℚ_[2] := (x.re : ℚ_[2]) + (x.im : ℚ_[2]) * (2*(alpha : ℚ_[2]) + 3)
def matI : Matrix (Fin 2) (Fin 2) ℚ_[2] := !![1, 1+(zeta : ℚ_[2]); (zeta : ℚ_[2]), -1]
def matJ : Matrix (Fin 2) (Fin 2) ℚ_[2] := !![-1, -2; 2, 1]
def psi (x : D) : Matrix (Fin 2) (Fin 2) ℚ_[2] :=
  embedDyadic x.re • 1 + embedDyadic x.imI • matI +
    embedDyadic x.imJ • matJ + embedDyadic x.imK • (matI * matJ)
def toPadicInt (x : ℚ_[2]) : ℤ_[2] := if h : ‖x‖ ≤ 1 then ⟨x, h⟩ else 0
def phi (g : Matrix (Fin 2) (Fin 2) ℚ_[2]) (t : ℤ_[2]) : ℤ_[2] :=
  toPadicInt ((g 0 0 * (t : ℚ_[2]) + g 0 1 / 2) / (2*g 1 0*(t : ℚ_[2]) + g 1 1))
def admissible (p : ℕ) : Prop := p.Prime ∧ p % 17 = 1

def smallerRoot (p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun (s : ℕ) => ((s : ℤ)^2 - (s : ℤ) - 4) % (p : ℤ) = 0)).min.untopD 0

def pairLex (x y : ℤ × ℤ) : Bool := decide (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2))
def generatorTest (p s : ℕ) (x : ℤ × ℤ) : Prop :=
  x.1^2 + x.1*x.2 - 4*x.2^2 = (p : ℤ) ∧ 0 < 2*x.1+x.2 ∧
  (2*x.1+x.2)^2 ≤ 68*(p : ℤ) ∧ (x.1+x.2*(s : ℤ)) % (p : ℤ) = 0
def balancedCoordinates (p s : ℕ) : ℤ × ℤ :=
  let B : ℤ := 20 * ⌈Real.sqrt p⌉
  let pairs := ((Finset.Icc (-B) B).product (Finset.Icc (-B) B)).filter (generatorTest p s)
  (pairs.toList.mergeSort pairLex).headD (0,0)
def primeGenerator (p : ℕ) : F :=
  let ab := balancedCoordinates p (smallerRoot p)
  (ab.1 : F) + (ab.2 : F)*omega

def coefficientBound (p : ℕ) : ℕ := ⌈21 * Real.sqrt (Real.sqrt p)⌉₊
def coordinateBox (p : ℕ) : Finset (Fin 8 → ℤ) :=
  (Finset.univ : Finset (Fin 8 → Fin (2*coefficientBound p + 1))).image
    (fun v s => ((v s).val : ℤ) - (coefficientBound p : ℤ))
def positiveSign (m : Fin 8 → ℤ) : Prop :=
  ∃ s : Fin 8, 0 < m s ∧ ∀ k : Fin 8, k < s → m k = 0
def vectorLex (m l : Fin 8 → ℤ) : Bool :=
  decide (m = l ∨ ∃ s : Fin 8, m s < l s ∧ ∀ k : Fin 8, k < s → m k = l k)
def labels (p : ℕ) : List (Fin 8 → ℤ) :=
  (((coordinateBox p).filter (fun m => nrd (fromCoordinates m) = primeGenerator p ∧ positiveSign m)).toList).mergeSort vectorLex
abbrev Label (p : ℕ) := Fin (labels p).length
def generator (p : ℕ) (j : Label p) : D := fromCoordinates ((labels p).get j)
def reverse (p : ℕ) (j : Label p) : Label p :=
  let k := (labels p).findIdx (fun m => fromCoordinates m = conjugate (generator p j) ∨
    fromCoordinates m = -conjugate (generator p j))
  if h : k < (labels p).length then ⟨k,h⟩ else j

def neighborMatrix (p : ℕ) (j : Label p) := psi (conjugate (generator p j))
abbrev Vertex (n : ℕ) := ZMod (2^n)
instance vertexNeZero (n : ℕ) : NeZero (2^n) := ⟨pow_ne_zero _ (by decide)⟩
def neighbor (p n : ℕ) (t : Vertex n) (j : Label p) : Vertex n :=
  PadicInt.toZModPow n (phi (neighborMatrix p j) (t.val : ℤ_[2]))
def reduction (n : ℕ) (t : Vertex (n+1)) : Vertex n := (t.val : Vertex n)
def sheet (n : ℕ) (t : Vertex n) (b : Bool) : Vertex (n+1) :=
  ((t.val + (if b then 1 else 0)*2^n : ℕ) : Vertex (n+1))
def liftBit (p n : ℕ) (t : Vertex n) (j : Label p) : Bool :=
  let w := PadicInt.toZModPow (n+1) (phi (neighborMatrix p j) (t.val : ℤ_[2]))
  decide ((((w.val : ℤ) - ((neighbor p n t j).val : ℤ)) / (2^n : ℤ)) = 1)
def signing (p n : ℕ) (t : Vertex n) (j : Label p) : ℝ := if liftBit p n t j then -1 else 1

def levelOrder (n : ℕ) : Set D := {x | x ∈ orderLattice ∧
  (∃ b : ℤ_[2], psi x 0 1 = (2 : ℚ_[2])^(n+1)*(b : ℚ_[2])) ∧
  (∃ c : ℤ_[2], psi x 1 0 = 2*(c : ℚ_[2]))}

end RamanujanLiftTower136.Tower


