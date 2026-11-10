-- Prove2me | Definitions.Def_MatMulPolyBarrier_Operational_OpPreorder
-- name    : MatMulPolyBarrier_Operational_OpPreorder
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:07:32.216341+00:00
-- url     : https://prove2.me/theorems/b573aa4e-886c-4171-85b4-ead8f630506c
-- title:
--   The operational preorder $\preceq$ on formal expressions (Definition 5.3)
-- statement:
--   The **operational preorder** $\preceq$ on $\mathcal F$ (Definition 5.3) is the smallest preorder on $\mathcal F$ that is compatible with $\oplus$ and $\otimes$ (if $T_1\preceq S_1$ and $T_2\preceq S_2$ then $T_1\oplus T_2\preceq S_1\oplus S_2$ and $T_1\otimes T_2\preceq S_1\otimes S_2$) — but not required to be compatible with $\oplus_1,\oplus_2,\oplus_3$ — and that contains the following relations, for all expressions $C,S,T,U,S_1,\dots,S_n,T_1,\dots,T_m$ and all positive integers $a,b,m,n,t,x,y,z$, whenever every triple of a $P$ is admissible and both sides lie in $\mathcal F$, each also with the legs renumbered by any of the six permutations:
--
--   - (D1) $P_{x,y,z}\preceq\langle\max(x,y,z)\rangle$.
--   - (D2) $(T_1\oplus\cdots\oplus T_m)\otimes P_{1,t,t}\preceq(T_1\oplus_1\cdots\oplus_1 T_m)\otimes P_{m,t,m+t-1}$.
--   - (D3) $P_{x,y+1,z+1}\oplus_1 P_{x,y-1,z-1}\preceq P_{x,y,z}\oplus_1 P_{x,y,z}$, and the same with a further summand $\oplus_1 C$ on both sides.
--   - (D4) $P_{x,y,z}\oplus_1 P_{x,z,y}\oplus_1 P_{x,y,z}\preceq P_{x,2y+z,y+2z}$, and the same with a further summand $\oplus_1 C$ on both sides.
--   - (R1) $T_1\preceq T_1\oplus T_2$, $T_1\preceq T_1\oplus_1 T_2$ and $T_1\oplus_1 T_2\preceq T_1\oplus T_2$.
--   - (R2) $P_{x,y-1,z-1}\preceq P_{x,y,z}$.
--   - (R3) $P_{a,b,a+b-1}\preceq P_{a,1,a}\otimes P_{1,b,b}$.
--   - (I) $T\preceq S$ and $S\preceq T$ whenever $T,S$ are the two sides of: (I1) associativity and commutativity of $\oplus$ and of $\otimes$, distributivity of $\otimes$ over $\oplus$, and $T\otimes\langle1\rangle\cong T$; (I2) any two orders and bracketings of a partial direct sum $T_1\oplus_1\cdots\oplus_1 T_m$, and $(T_1\oplus_1\cdots\oplus_1T_m)\otimes(S_1\oplus_1\cdots\oplus_1S_n)$ versus the partial direct sum of the $mn$ expressions $T_i\otimes S_j$; (I3) $\langle n_1,n_2,n_3\rangle\otimes\langle m_1,m_2,m_3\rangle\cong\langle n_1m_1,n_2m_2,n_3m_3\rangle$ for all positive integers; (I4) the partial direct sum of $r$ copies of $U$ and $U\otimes P_{1,r,r}$, for every integer $r\ge1$.
--
--   **Formalization Note.** `Iso` lists (I1)–(I4) and `Gen` lists (D1)–(D4), (R1)–(R3) and both directions of every `Iso`, with the paper's first leg as `0`. `OpLe T S` ($T\preceq S$) is the inductive closure under reflexivity on $\mathcal F$, transitivity, compatibility with `dsum` and `tens`, and `gen π`: every `Gen T S` with $T,S\in\mathcal F$, renumbered by every `π : Equiv.Perm (Fin 3)`. In (D3) and (R2) the paper's $y,z$ are written $y+1,z+1$ (so $y-1,z-1$ become $y,z$), which ranges over the same instances without natural-number subtraction. Iterated sums $T_1\oplus\cdots\oplus T_m$ and $T_1\oplus_1\cdots\oplus_1T_m$ in (D2), (I2), (I4) are any bracketing of the list in its order (`IsSumTree`), and $m=$ the list length; the further summand $C$ of (D3), (D4) is added at the outermost level, and the three-fold sum in (D4) is bracketed $(P\oplus_1P')\oplus_1P$ — other orders and bracketings are equivalent through (I2). Distributivity in (I1) is $T\otimes(S\oplus U)\cong(T\otimes S)\oplus(T\otimes U)$; the $mn$ products in (I2) are listed as $T_1\otimes S_1,\dots,T_1\otimes S_n,T_2\otimes S_1,\dots$.
-- source:
--   Amanov, van den Berg, Zuiddam, Multiplying matrices via polynomials: operational asymptotic spectrum barrier, STOC 2027 submission (manuscript sha256 38bd5183…), pp. 36–37, Definition 5.3

import Mathlib
import Definitions.Def_MatMulPolyBarrier_Operational_FExpr

set_option autoImplicit false

/-!
# The operational preorder `⪯` on formal expressions (Definition 5.3)

Amanov, van den Berg, Zuiddam, *Multiplying matrices via polynomials: operational asymptotic
spectrum barrier*, STOC 2027 submission, pp. 36–37, Definition 5.3.

Conventions.
* `Gen T S` lists the generating properties of Definition 5.3 *as printed*, with the shared leg of
  `⊕₁` being leg `0`. `OpLe` closes them under all six leg renumberings (`FExpr.perm π`) and
  requires both sides to lie in `F` (`WF`), as Definition 5.3 does ("whenever the triples … are
  admissible and the expressions lie in F").
* Integer parameters that the paper writes as `y − 1`, `z − 1` are shifted: (D3) and (R2) are
  stated for `y + 1`, `z + 1` in place of the paper's `y`, `z`; this ranges over the same
  instances.
* `T₁ ⊕ ⋯ ⊕ T_m` and `T₁ ⊕₁ ⋯ ⊕₁ T_m` are any bracketing of the sum of the list in its order
  (`IsSumTree`); the "further summand `⊕₁ C`" of (D3), (D4) is added at the outermost level.
* `OpLe` is compatible with `⊕` and `⊗` only, not with `⊕ᵢ`.
-/

namespace MatMulPolyBarrier.Operational

open FExpr

/-- The isomorphisms (I1)–(I4) of Definition 5.3 (p. 37), with leg `0` the shared leg of `⊕₁`.
Each is used in both directions. -/
inductive Iso : FExpr → FExpr → Prop
  /-- (I1) associativity of `⊕`. -/
  | dsum_assoc (T U S : FExpr) : Iso (dsum (dsum T U) S) (dsum T (dsum U S))
  /-- (I1) commutativity of `⊕`. -/
  | dsum_comm (T S : FExpr) : Iso (dsum T S) (dsum S T)
  /-- (I1) associativity of `⊗`. -/
  | tens_assoc (T U S : FExpr) : Iso (tens (tens T U) S) (tens T (tens U S))
  /-- (I1) commutativity of `⊗`. -/
  | tens_comm (T S : FExpr) : Iso (tens T S) (tens S T)
  /-- (I1) distributivity of `⊗` over `⊕`. -/
  | distrib (T S U : FExpr) : Iso (tens T (dsum S U)) (dsum (tens T S) (tens T U))
  /-- (I1) `T ⊗ ⟨1⟩ ≅ T`. -/
  | tens_one (T : FExpr) : Iso (tens T unitOne) T
  /-- (I2) any two orders and bracketings of a partial direct sum `T₁ ⊕₁ ⋯ ⊕₁ T_m`. -/
  | psum_reorder {E E' : FExpr} {L L' : List FExpr} :
      IsSumTree (psum 0) E L → IsSumTree (psum 0) E' L' → L.Perm L' → Iso E E'
  /-- (I2) `(T₁ ⊕₁ ⋯ ⊕₁ T_m) ⊗ (S₁ ⊕₁ ⋯ ⊕₁ S_n)` and the partial direct sum of the `mn`
  expressions `Tᵢ ⊗ Sⱼ`. -/
  | psum_distrib {E E' G : FExpr} {L L' : List FExpr} :
      IsSumTree (psum 0) E L → IsSumTree (psum 0) E' L' →
      IsSumTree (psum 0) G (L.flatMap fun T => L'.map fun S => tens T S) →
      Iso (tens E E') G
  /-- (I3) `⟨n₁, n₂, n₃⟩ ⊗ ⟨m₁, m₂, m₃⟩ ≅ ⟨n₁m₁, n₂m₂, n₃m₃⟩`. -/
  | mm_mul (n₁ n₂ n₃ m₁ m₂ m₃ : ℕ) :
      Iso (tens (mm n₁ n₂ n₃) (mm m₁ m₂ m₃)) (mm (n₁ * m₁) (n₂ * m₂) (n₃ * m₃))
  /-- (I4) the partial direct sum of `r` copies of `U` and `U ⊗ P_{1,r,r}`. -/
  | copies {E U : FExpr} (r : ℕ) :
      IsSumTree (psum 0) E (List.replicate r U) → Iso E (tens U (P 1 r r))

/-- The generating properties (D1)–(D4), (R1)–(R3), (I) of Definition 5.3 (pp. 36–37), as printed
(leg `0` is the paper's first leg). `Gen T S` means `T ⪯ S` is required. -/
inductive Gen : FExpr → FExpr → Prop
  /-- (D1) `P_{x,y,z} ⪯ ⟨max(x, y, z)⟩`. -/
  | d1 (x y z : ℕ) : Gen (P x y z) (unitR (max (max x y) z))
  /-- (D2) `(T₁ ⊕ ⋯ ⊕ T_m) ⊗ P_{1,t,t} ⪯ (T₁ ⊕₁ ⋯ ⊕₁ T_m) ⊗ P_{m,t,m+t−1}`, `m` the length of the
  (nonempty) list. -/
  | d2 {E E' : FExpr} {L : List FExpr} (t : ℕ) :
      IsSumTree dsum E L → IsSumTree (psum 0) E' L →
      Gen (tens E (P 1 t t)) (tens E' (P L.length t (L.length + t - 1)))
  /-- (D3) `P_{x,y+1,z+1} ⊕₁ P_{x,y−1,z−1} ⪯ P_{x,y,z} ⊕₁ P_{x,y,z}`, written for `y + 1`, `z + 1`
  in place of the paper's `y`, `z`. -/
  | d3 (x y z : ℕ) :
      Gen (psum 0 (P x (y + 2) (z + 2)) (P x y z))
        (psum 0 (P x (y + 1) (z + 1)) (P x (y + 1) (z + 1)))
  /-- (D3) with a further summand `⊕₁ C` on both sides. -/
  | d3C (x y z : ℕ) (C : FExpr) :
      Gen (psum 0 (psum 0 (P x (y + 2) (z + 2)) (P x y z)) C)
        (psum 0 (psum 0 (P x (y + 1) (z + 1)) (P x (y + 1) (z + 1))) C)
  /-- (D4) `P_{x,y,z} ⊕₁ P_{x,z,y} ⊕₁ P_{x,y,z} ⪯ P_{x,2y+z,y+2z}`. -/
  | d4 (x y z : ℕ) :
      Gen (psum 0 (psum 0 (P x y z) (P x z y)) (P x y z)) (P x (2 * y + z) (y + 2 * z))
  /-- (D4) with a further summand `⊕₁ C` on both sides. -/
  | d4C (x y z : ℕ) (C : FExpr) :
      Gen (psum 0 (psum 0 (psum 0 (P x y z) (P x z y)) (P x y z)) C)
        (psum 0 (P x (2 * y + z) (y + 2 * z)) C)
  /-- (R1) `T₁ ⪯ T₁ ⊕ T₂`. -/
  | r1_dsum (T₁ T₂ : FExpr) : Gen T₁ (dsum T₁ T₂)
  /-- (R1) `T₁ ⪯ T₁ ⊕₁ T₂`. -/
  | r1_psum (T₁ T₂ : FExpr) : Gen T₁ (psum 0 T₁ T₂)
  /-- (R1) `T₁ ⊕₁ T₂ ⪯ T₁ ⊕ T₂`. -/
  | r1_psum_dsum (T₁ T₂ : FExpr) : Gen (psum 0 T₁ T₂) (dsum T₁ T₂)
  /-- (R2) `P_{x,y−1,z−1} ⪯ P_{x,y,z}`, written for `y + 1`, `z + 1` in place of `y`, `z`. -/
  | r2 (x y z : ℕ) : Gen (P x y z) (P x (y + 1) (z + 1))
  /-- (R3) `P_{a,b,a+b−1} ⪯ P_{a,1,a} ⊗ P_{1,b,b}`. -/
  | r3 (a b : ℕ) : Gen (P a b (a + b - 1)) (tens (P a 1 a) (P 1 b b))
  /-- (I) `T ⪯ S` for the two sides of an isomorphism … -/
  | iso_fwd {T S : FExpr} : Iso T S → Gen T S
  /-- … and `S ⪯ T`. -/
  | iso_bwd {T S : FExpr} : Iso T S → Gen S T

/-- The operational preorder `⪯` of Definition 5.3 (pp. 36–37): the smallest preorder on `F`
compatible with `⊕` and `⊗` that contains every generating property, each also with the legs
renumbered, whenever both sides lie in `F`. `OpLe T S` reads `T ⪯ S`. -/
inductive OpLe : FExpr → FExpr → Prop
  | refl {T : FExpr} : T.WF → OpLe T T
  | trans {T U S : FExpr} : OpLe T U → OpLe U S → OpLe T S
  | dsum {T₁ T₂ S₁ S₂ : FExpr} : OpLe T₁ S₁ → OpLe T₂ S₂ → OpLe (dsum T₁ T₂) (dsum S₁ S₂)
  | tens {T₁ T₂ S₁ S₂ : FExpr} : OpLe T₁ S₁ → OpLe T₂ S₂ → OpLe (tens T₁ T₂) (tens S₁ S₂)
  | gen (π : Equiv.Perm (Fin 3)) {T S : FExpr} :
      Gen T S → T.WF → S.WF → OpLe (T.perm π) (S.perm π)

end MatMulPolyBarrier.Operational


