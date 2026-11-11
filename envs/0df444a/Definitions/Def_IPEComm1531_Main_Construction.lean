-- Prove2me | Definitions.Def_IPEComm1531_Main_Construction
-- name    : IPEComm1531_Main_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:48.419201+00:00
-- url     : https://prove2.me/theorems/2eef9d6b-d498-4bff-a6f7-dd40ef8e4e5c
-- title:
--   Certificates $a_c,b_c$, the test $\mathrm{Check}$ and the Indexed Product Equality function $\mathrm{IPE}_n$
-- statement:
--   Fix a family of spaces with listed bases, an extractor family and an assignment $x\mapsto p_x$. At level $j$ with $r=r_j$, let $f_1,\dots,f_h$ be the listed basis of $V_{3\delta r}$ and $\ell=2h\log_2q=48h$. A certificate $c\in\{0,1\}^\ell$ is cut into $2h$ blocks of 24 bits, decoded to $c_1,\dots,c_{2h}\in\mathbb F_q$, and
--   $$a_c=\sum_{i=1}^h c_if_i,\qquad b_c=\sum_{i=1}^h c_{i+h}f_i .$$
--   For $x,z\in\{0,1\}^r$,
--   $$\mathrm{Check}(x,z,c)=1\iff a_c\neq0\ \text{ and }\ p_x\cdot a_c=p_z\cdot b_c\ \text{ on all of }[2r].$$
--   With $d$ the extractor's seed length for $(r,\ell)$ and $c_\sigma=\mathrm{Ext}(u,\sigma)\oplus\mathrm{Ext}(v,\sigma)$,
--   $$\mathrm{IPE}(x,u;y,v)=1\iff\exists\sigma\in\{0,1\}^d:\ \mathrm{Check}(x,\,y\oplus w_\sigma,\,c_\sigma)=1 .$$
--   On $n$-bit inputs, with $r$ the largest $r_j$ such that $2r_j\le n$, Alice's first $r$ bits are $x$ and her next $r$ bits are $u$, Bob's are $y$ and $v$, and the remaining bits are ignored. This is a total Boolean function on all pairs of $n$-bit strings.
--
--   **Formalization Note** For $n<2r_0=2^{23}$ no level exists and the function is defined to be constant $0$; every theorem about the family is asymptotic in $n$. The function depends on the chosen data; Theorems 4.1 and 5.1 hold for every choice satisfying the conclusions of Fact 2.3, Theorem 3.2 and Lemma 3.3.
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, §3 Steps 1–2, eqs. (3.2)–(3.4) and Definition 3.5, pp.8–9

import Mathlib
import Definitions.Def_IPEComm1531_Main_Spaces
import Definitions.Def_IPEComm1531_Main_Extractor
import Definitions.Def_IPEComm1531_Main_Addresses

set_option autoImplicit false

namespace IPEComm1531.Main

/-- `h = dim V_{3δr}`: the number of listed basis functions `f_1, …, f_h` of `V_{3δr}`. -/
def certificateDim (S : Spaces) (j : ℕ) : ℕ := S.size j (3 * slack j)

/-- `ℓ = 2 h log₂ q = 48 h`. -/
def certificateLength (S : Spaces) (j : ℕ) : ℕ := 2 * certificateDim S j * 24

/-- The `a`-th block of 24 bits of a certificate (zero-based). -/
def certBlock (S : Spaces) (j a : ℕ) (c : Bits (certificateLength S j)) : Bits 24 :=
  fun i => if h : a * 24 + i.val < certificateLength S j
    then c ⟨a * 24 + i.val, h⟩ else 0

/-- `a_c = ∑_{i=1}^h c_i f_i` (eq. (3.2), p.8). -/
noncomputable def certA (S : Spaces) (j : ℕ) (c : Bits (certificateLength S j)) :
    Fin (2 * radius j) → F :=
  ∑ a : Fin (certificateDim S j), decodeField (certBlock S j a.val c) • S.row j (3 * slack j) a

/-- `b_c = ∑_{i=1}^h c_{i+h} f_i` (eq. (3.2), p.8). -/
noncomputable def certB (S : Spaces) (j : ℕ) (c : Bits (certificateLength S j)) :
    Fin (2 * radius j) → F :=
  ∑ a : Fin (certificateDim S j),
    decodeField (certBlock S j (a.val + certificateDim S j) c) • S.row j (3 * slack j) a

/-- `Check(x, z, c) = 1{a_c ≠ 0 and p_x · a_c = p_z · b_c}` (eq. (3.4), p.9). -/
def Check (S : Spaces) (p : Prescribed) (j : ℕ) (x z : Bits (radius j))
    (c : Bits (certificateLength S j)) : Prop :=
  certA S j c ≠ 0 ∧ p j x * certA S j c = p j z * certB S j c

/-- Seed length `d` of the extractor used at level `j`. -/
def seedLength (S : Spaces) (E : Extractors) (j : ℕ) : ℕ :=
  E.seedLength (radius j) (certificateLength S j)

/-- `c_σ = Ext(u, σ) ⊕ Ext(v, σ)` (eq. (3.3), p.8). -/
def certificate (S : Spaces) (E : Extractors) (j : ℕ) (u v : Bits (radius j))
    (s : Bits (seedLength S E j)) : Bits (certificateLength S j) :=
  E.eval (radius j) (certificateLength S j) u s + E.eval (radius j) (certificateLength S j) v s

/-- Definition 3.5 (p.9) on `(x, u; y, v) ∈ ({0,1}^r)^4`, `r = r_j`:
`IPE = 1` iff some address `σ ∈ {0,1}^d` has `Check(x, y ⊕ w_σ, c_σ) = 1`. -/
noncomputable def nativeIPE (S : Spaces) (E : Extractors) (p : Prescribed) (j : ℕ)
    (x u y v : Bits (radius j)) : Bool := by
  classical
  exact decide (∃ s : Bits (seedLength S E j),
    Check S p j x (y + address (radius j) (seedLength S E j) s) (certificate S E j u v s))

/-- `IPE_n` on all pairs of `n`-bit strings (§3, p.8): with `r` the largest `r_j` such that
`2 r_j ≤ n`, Alice's first `2r` bits are `(x, u)`, Bob's are `(y, v)`, and the remaining bits
are ignored. Lengths `n < 2 r_0` (no admissible `r_j`) get the constant function `0`. -/
noncomputable def family (S : Spaces) (E : Extractors) (p : Prescribed) (n : ℕ)
    (a b : Fin n → Bool) : Bool :=
  if 2 * radius 0 ≤ n then
    nativeIPE S E p (level n) (slice (radius (level n)) 0 a)
      (slice (radius (level n)) (radius (level n)) a)
      (slice (radius (level n)) 0 b) (slice (radius (level n)) (radius (level n)) b)
  else false

end IPEComm1531.Main


