-- Prove2me | Definitions.Def_TernarySync_Alphabet_Brinkhuis
-- name    : TernarySync_Alphabet_Brinkhuis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:52:48.346302+00:00
-- url     : https://prove2.me/theorems/8aff33d8-bcff-4fd4-8010-14b72490c951
-- title:
--   Brinkhuis triples (Definition 1.3), the six Ekhad–Zeilberger codewords (Eq. (7)) and the substitution $W(T,R)$ (Eq. (8))
-- statement:
--   An **$m$-Brinkhuis $K$-triple** (Definition 1.3) consists of three sets $C_0, C_1, C_2 \subseteq \{0,1,2\}^m$, each of size $K$, such that for every ternary square-free word $abc$ of length three and every independent choice $U \in C_a$, $V \in C_b$, $Z \in C_c$, the concatenation $UVZ$ is square-free; the choices of $U$ and $Z$ are independent even when $a = c$.
--
--   The six codewords of Ekhad and Zeilberger (Equation (7)) are the blocks $B_{a,r}$ of length 18, one row per outer letter $a \in \{0,1,2\}$ and one column per choice $r \in \{0,1\}$:
--
--   $$\begin{aligned} B_{0,0} &= 210201202120102012, & B_{0,1} &= 210201021202102012,\\ B_{1,0} &= 021012010201210120, & B_{1,1} &= 021012102010210120,\\ B_{2,0} &= 102120121012021201, & B_{2,1} &= 102120210121021201. \end{aligned}$$
--
--   For an outer word $T = T_1 \cdots T_N$ over $\{0,1,2\}$ and a choice vector $R \in \{0,1\}^N$ (one choice per occurrence, also for repeated letters), Equation (8) defines
--
--   $$W(T,R) = B_{T_1,R_1} B_{T_2,R_2} \cdots B_{T_N,R_N} \in \{0,1,2\}^{18N}.$$
--
--   This is the random source of the paper's construction: it replaces each letter of a ternary square-free word by one of two length-18 blocks.
--
--   **Formalization Note.** `IsBrinkhuisTriple m K C` takes `C : Fin 3 → Finset (List (Fin 3))`; "$C_a \subseteq \{0,1,2\}^m$ of size $K$" is "card $= K$ and every member has length $m$". `codeword a r` is $B_{a,r}$, digit for digit; `ezTriple a = {B_{a,0}, B_{a,1}}`. `W T R` takes `T : List (Fin 3)` and `R : Fin T.length → Fin 2` and concatenates `codeword (T.get i) (R i)` over $i = 0, \dots, N-1$; occurrences are indexed from $0$, so macroblock $i$ occupies positions $18i, \dots, 18i+17$.
-- source:
--   Xu, Fu, Qiao, Tao, Synchronization Strings over a Ternary Alphabet, STOC 2027 submission (manuscript sha256 1b74ae6d…), pp. 4–5 (PDF 5–6), Definition 1.3; p. 14 (PDF 15), Eqs. (7)–(8)

import Mathlib
import Definitions.Def_TernarySync_Alphabet_SyncString

set_option autoImplicit false

namespace TernarySync.Alphabet

/-- Definition 1.3 (Xu, Fu, Qiao, Tao, pp. 4–5): an `m`-Brinkhuis `K`-triple is three sets
`C 0, C 1, C 2` of words of length `m` over `{0, 1, 2}`, each of size `K`, such that for every
ternary square-free word `abc` of length three and every independent choice `U ∈ C a`,
`V ∈ C b`, `Z ∈ C c` (independent also when `a = c`), the concatenation `UVZ` is square-free. -/
def IsBrinkhuisTriple (m K : ℕ) (C : Fin 3 → Finset (List (Fin 3))) : Prop :=
  (∀ a : Fin 3, (C a).card = K ∧ ∀ U ∈ C a, U.length = m) ∧
    ∀ a b c : Fin 3, IsSquareFree [a, b, c] →
      ∀ U ∈ C a, ∀ V ∈ C b, ∀ Z ∈ C c, IsSquareFree (U ++ V ++ Z)

/-- The six Ekhad–Zeilberger codewords of Equation (7) (p. 14): `codeword a r` is `B_{a,r}`,
the block of length 18 assigned to the outer letter `a` under the choice `r`.
`B_{0,0} = 210201202120102012`, `B_{0,1} = 210201021202102012`,
`B_{1,0} = 021012010201210120`, `B_{1,1} = 021012102010210120`,
`B_{2,0} = 102120121012021201`, `B_{2,1} = 102120210121021201`. -/
def codeword (a : Fin 3) (r : Fin 2) : List (Fin 3) :=
  ![![[2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 2, 0, 1, 0, 2, 0, 1, 2],
      [2, 1, 0, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2]],
    ![[0, 2, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2, 0],
      [0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 2, 1, 0, 1, 2, 0]],
    ![[1, 0, 2, 1, 2, 0, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 0, 1],
      [1, 0, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 0, 2, 1, 2, 0, 1]]] a r

/-- The two blocks of each outer letter, `C a = {B_{a,0}, B_{a,1}}` (Section 3, p. 14). -/
def ezTriple (a : Fin 3) : Finset (List (Fin 3)) :=
  {codeword a 0, codeword a 1}

/-- The occurrence-wise substitution of Equation (8) (p. 14): for an outer word
`T = T_1 ⋯ T_N` over `{0, 1, 2}` and a choice vector `R ∈ {0, 1}^N`,
`W(T, R) = B_{T_1,R_1} B_{T_2,R_2} ⋯ B_{T_N,R_N}`, a word of length `18 N`. Occurrences are
indexed from `0`, so the `i`-th macroblock occupies positions `18 i, …, 18 i + 17`. -/
def W (T : List (Fin 3)) (R : Fin T.length → Fin 2) : List (Fin 3) :=
  (List.ofFn fun i : Fin T.length => codeword (T.get i) (R i)).flatten

end TernarySync.Alphabet


