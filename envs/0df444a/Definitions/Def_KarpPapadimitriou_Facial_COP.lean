-- Prove2me | Definitions.Def_KarpPapadimitriou_Facial_COP
-- name    : KarpPapadimitriou_Facial_COP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:04:24.175542+00:00
-- url     : https://prove2.me/theorems/ff8b140d-0a89-4dc8-a91f-46734340f539
-- title:
--   Definition 1 — combinatorial optimization problems, the decision problem D(C), and CH(S(z))
-- statement:
--   Strings and tuples are written over the four-letter alphabet $\Sigma=\{0,1,-,\#\}$, every integer in binary. A string $z\in\{0,1\}^*$ is coded by its bits followed by $\#$; an integer vector $v\in\mathbb Z^m$ by its length $m$ in binary followed by its entries in binary; a pair $\langle z,x\rangle$ and a triple $\langle z,v,a\rangle$ by the concatenation of the codes of their components.
--
--   A **combinatorial optimization problem** (c.o.p.) $C$ is specified by
--
--   1. a set $L\subseteq\{0,1\}^*$;
--   2. a function $n$ from $L$ into the nonnegative integers;
--   3. for each $z\in L$, a set $S(z)\subseteq(\mathbb Z^+)^{n(z)}$ of nonnegative integer vectors (the feasible solutions),
--
--   such that each of the three languages
--   $$L,\qquad \{\langle z,y\rangle : z\in L,\ y\in\{0,1\}^*,\ |y|=n(z)\},\qquad \{\langle z,x\rangle : z\in L,\ x\in S(z)\}$$
--   is recognizable in polynomial time, i.e. its set of codes belongs to Cook's class $\mathrm P$ over $\Sigma$.
--
--   An instance $\langle z,c\rangle$ of $C$ has $z\in L$ and $c\in\mathbb Z^{n(z)}$. The **decision problem** of $C$ is the language
--   $$D(C)=\{\langle z,c,k\rangle : z\in L,\ c\in\mathbb Z^{n(z)},\ k\in\mathbb Z,\ \exists x\in S(z)\ \ c\cdot x\ge k\}.$$
--   Finally $\mathrm{CH}(S(z))\subseteq\mathbb Q^{n(z)}$ denotes the convex hull of $S(z)$ in the rational space.
--
--   These are the objects about which Theorem 1 of Karp and Papadimitriou is stated: every classical combinatorial optimization problem (matching, set covering, integer programming, the traveling salesman problem) fits the definition, and $D(C)$ is its decision version.
--
--   **Formalization Note** The paper writes $R$ for the rationals (footnote, p. 3), so convex hulls are taken over $\mathbb Q$. A code is a string over $\Sigma$, and $D(C)$ is the set of codes of the yes-triples, so a string that encodes no triple lies outside $D(C)$. The code of an integer vector carries its length so that the tuple codes are uniquely decodable. The values of $n$ and $S$ outside $L$ are irrelevant. The display (3) of the paper prints "min" for the instance's objective, while $D(C)$, (1), (2) and the proof of Theorem 1 maximize; $D(C)$ is formalized as printed, with $c\cdot x\ge k$.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), pp. 3–4, Definition 1, footnote p. 3, Definitions (instances, D(C))

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace KarpPapadimitriou.Facial

open CookPvsNP ProjSchedTW.Complexity

/-! # Combinatorial optimization problems and their decision problems

Karp & Papadimitriou, *On linear characterizations of combinatorial optimization problems*,
MIT/LCS/TM-154 (Feb. 1980), §2, pp. 3–4: Definition 1 (combinatorial optimization problems),
instances, and the decision problem `D(C)`.

Strings and tuples are written over the four-letter alphabet `BSym = {0, 1, −, #}` of the
published definition file `ProjSchedTW_Complexity_Encoding`; every integer is written in binary
(`encInt`), so the length of a code is the size of the tuple it encodes. -/

/-- The code of a string `z ∈ {0,1}*`: its bits (`false ↦ 0`, `true ↦ 1`), closed by `#`. -/
def encBits (z : List Bool) : List BSym :=
  z.map (fun b => if b then BSym.one else BSym.zero) ++ [BSym.sep]

/-- The code of an integer vector `v ∈ ℤᵐ`: its length `m` in binary, then each entry in binary. -/
def encVec {m : ℕ} (v : Fin m → ℤ) : List BSym :=
  encNat m ++ encInts (List.ofFn v)

/-- The code `⟨z, x⟩` of a string `z` and an integer vector `x`. -/
def encPair {m : ℕ} (z : List Bool) (x : Fin m → ℤ) : List BSym :=
  encBits z ++ encVec x

/-- The code `⟨z, v, a⟩` of a string `z`, an integer vector `v` and an integer `a`. It is used
both for the inputs `⟨z, c, k⟩` of the decision problem and for the triples `⟨z, f, g⟩` of a
facial description. -/
def encTriple {m : ℕ} (z : List Bool) (v : Fin m → ℤ) (a : ℤ) : List BSym :=
  encBits z ++ encVec v ++ encInt a

/-- **Definition 1** (pp. 3–4). A combinatorial optimization problem (c.o.p.) `C` is specified by
(i) a set `L ⊆ {0,1}*`; (ii) a function `n` from `L` into the nonnegative integers (its values
off `L` are irrelevant); (iii) for each `z ∈ L` a set `S(z)` of nonnegative integer vectors of
length `n(z)`; such that the three languages `L`, `{⟨z,y⟩ | |y| = n(z)}` and
`{⟨z,x⟩ | x ∈ S(z)}` are recognizable in polynomial time (Cook's class `P` over `BSym`). -/
structure COP where
  /-- The set `L ⊆ {0,1}*` of problem inputs. -/
  L : Set (List Bool)
  /-- The number of variables `n(z)` of the input `z`. -/
  n : List Bool → ℕ
  /-- The set `S(z)` of feasible solutions of the input `z`. -/
  S : (z : List Bool) → Set (Fin (n z) → ℤ)
  /-- `S(z) ⊆ (ℤ⁺)ⁿ⁽ᶻ⁾`: feasible solutions are nonnegative integer vectors. -/
  S_nonneg : ∀ z ∈ L, ∀ x ∈ S z, ∀ j, 0 ≤ x j
  /-- The language `L` is recognizable in polynomial time. -/
  L_poly : {w : List BSym | ∃ z ∈ L, w = encBits z} ∈ P BSym
  /-- The language `{⟨z,y⟩ | |y| = n(z)}` (with `z ∈ L`, `y ∈ {0,1}*`) is recognizable in
  polynomial time. -/
  len_poly : {w : List BSym | ∃ z ∈ L, ∃ y : List Bool, y.length = n z ∧
    w = encBits z ++ encBits y} ∈ P BSym
  /-- The language `{⟨z,x⟩ | x ∈ S(z)}` (with `z ∈ L`) is recognizable in polynomial time. -/
  S_poly : {w : List BSym | ∃ z ∈ L, ∃ x ∈ S z, w = encPair z x} ∈ P BSym

/-- The decision problem `D(C)` (p. 4): the codes of the triples `⟨z, c, k⟩` with `z ∈ L`,
`c ∈ ℤⁿ⁽ᶻ⁾`, `k ∈ ℤ` such that some `x ∈ S(z)` has `c · x ≥ k`. -/
def DLang (C : COP) : Lang BSym :=
  {w | ∃ z ∈ C.L, ∃ (c : Fin (C.n z) → ℤ) (k : ℤ),
    (∃ x ∈ C.S z, k ≤ c ⬝ᵥ x) ∧ w = encTriple z c k}

/-- The convex hull `CH(S(z)) ⊆ ℚⁿ⁽ᶻ⁾` of the feasible set (the paper's `R` is the rationals,
footnote p. 3). -/
def hull (C : COP) (z : List Bool) : Set (Fin (C.n z) → ℚ) :=
  convexHull ℚ ((fun x : Fin (C.n z) → ℤ => fun j => (x j : ℚ)) '' C.S z)

end KarpPapadimitriou.Facial


