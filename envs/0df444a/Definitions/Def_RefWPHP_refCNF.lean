-- Prove2me | Definitions.Def_RefWPHP_refCNF
-- name    : RefWPHP_refCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:01:53.541813+00:00
-- url     : https://prove2.me/theorems/4d0d305d-225d-4de5-abf8-3dabe8507e6f
-- title:
--   The formula $\mathrm{Ref}_s(\varphi)$: variables and clauses (Ref-1)–(Ref-11)
-- statement:
--   For a CNF $\varphi$ over $n$ variables with $m$ clauses and a size parameter $s$, the formula $\mathrm{Ref}_s(\varphi)$ says that $\varphi$ has a Resolution refutation with at most $s+1$ clauses. Its variables are grouped into $s+1$ blocks $B$: $\mathrm{enable}^B$, $\mathrm{derived}^B$, $\mathrm{weak}^B_A$, $\mathrm{lit}^B_\ell$, $\mathrm{res}^B_{x_i}$, and the pointers $\mathrm{lpoint}^B_{B'}$, $\mathrm{rpoint}^B_{B'}$ with $B' < B$. Block $s+1$ is the empty clause. Its clauses are:
--
--   1. (Ref-1) $(\mathrm{enable}^B \wedge \mathrm{res}^B_{x_i} \wedge \mathrm{lpoint}^B_{B'} \wedge \mathrm{lit}^{B'}_\ell) \to \mathrm{lit}^B_\ell$ for $B' < B$, $\ell \ne x_i$;
--   2. (Ref-2) the same with $\mathrm{rpoint}$ and $\ell \ne \neg x_i$;
--   3. (Ref-3) $(\mathrm{enable}^B \wedge \mathrm{weak}^B_A) \to \mathrm{lit}^B_\ell$ for $\ell \in C_A$;
--   4. (Ref-4) $(\mathrm{enable}^B \wedge \mathrm{derived}^B) \to \bigvee_i \mathrm{res}^B_{x_i}$;
--   5. (Ref-5) $(\mathrm{enable}^B \wedge \neg\mathrm{derived}^B) \to \bigvee_A \mathrm{weak}^B_A$;
--   6. (Ref-6), (Ref-7) $(\mathrm{enable}^B \wedge \mathrm{derived}^B) \to \bigvee_{B'<B} \mathrm{lpoint}^B_{B'}$, and the same with $\mathrm{rpoint}$;
--   7. (Ref-8), (Ref-9) $(\mathrm{enable}^B \wedge \mathrm{lpoint}^B_{B'}) \to \mathrm{enable}^{B'}$, and the same with $\mathrm{rpoint}$, for $B' < B$;
--   8. (Ref-10) $\neg\mathrm{lit}^{s+1}_\ell$ for every literal $\ell$;
--   9. (Ref-11) $\mathrm{enable}^{s+1}$.
--
--   A refutation of $\mathrm{Ref}_s(\varphi)$ for unsatisfiable $\varphi$ is a proof of a Resolution length lower bound for $\varphi$.
--
--   **Formalization Note** The variables $\text{a-lit}^A_\ell$ are not variables here: for a fixed $\varphi$ they are constants (p.22), so the instances of (Ref-3) with $\ell \notin C_A$ are satisfied and omitted, and the false literal is dropped from the others. Each clause is the cedent of its literals, so every axiom has depth $0$. Blocks are `Fin (s+1)`, with block $s+1$ as `Fin.last s`. Pointer variables exist for every pair of blocks, but only $B' < B$ occurs in the clauses.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.3, pp.16–17 (PDF pp.18–19); a-lit constants p.22 (PDF p.24)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation
import Definitions.Def_RefWPHP_LayeredRef

namespace RefWPHP

open PKFormula

/-- The variables of `Ref_s(φ)` for a CNF `φ` over `n` variables with `m` clauses, N. Arteche,
*Resolution Lower Bounds versus the Weak Pigeonhole Principle*, STOC 2027 submission (held
manuscript, sha256 ee75d7f1…), §2.1.3, p.16 (PDF 18). Blocks are `Fin (s+1)`: index `j` is the
paper's block `j+1`, and the root block `s+1` is `Fin.last s`.

**Formalization Note.** The variables `a-lit^A_ℓ` are not variables here: for a fixed `φ` they are
constants (p.22). `lpoint B B'` and `rpoint B B'` exist for every pair; only `B' < B` occurs in the
clauses. -/
inductive RefVar (n m s : ℕ) : Type
  | enable (B : Fin (s + 1)) : RefVar n m s
  | derived (B : Fin (s + 1)) : RefVar n m s
  | weak (B : Fin (s + 1)) (A : Fin m) : RefVar n m s
  | lit (B : Fin (s + 1)) (ℓ : Lit n) : RefVar n m s
  | res (B : Fin (s + 1)) (i : Fin n) : RefVar n m s
  | lpoint (B B' : Fin (s + 1)) : RefVar n m s
  | rpoint (B B' : Fin (s + 1)) : RefVar n m s

/-- The CNF `Ref_s(φ)`, §2.1.3, pp.16–17 (PDF 18–19), as the set of cedents of its clauses
(Ref-1)–(Ref-11), each written as the cedent of its literals:

* (Ref-1) `¬enable^B, ¬res^B_{x_i}, ¬lpoint^B_{B'}, ¬lit^{B'}_ℓ, lit^B_ℓ` for `B' < B`,
  `ℓ ∈ Lit_n \ {x_i}`;
* (Ref-2) the same with `rpoint` and `ℓ ∈ Lit_n \ {¬x_i}`;
* (Ref-3) `¬enable^B, ¬weak^B_A, lit^B_ℓ` for `ℓ ∈ C_A`;
* (Ref-4) `¬enable^B, ¬derived^B, res^B_{x_1}, …, res^B_{x_n}`;
* (Ref-5) `¬enable^B, derived^B, weak^B_1, …, weak^B_m`;
* (Ref-6) `¬enable^B, ¬derived^B, lpoint^B_{B'}` over all `B' < B`;
* (Ref-7) the same with `rpoint`;
* (Ref-8) `¬enable^B, ¬lpoint^B_{B'}, enable^{B'}` for `B' < B`;
* (Ref-9) the same with `rpoint`;
* (Ref-10) `¬lit^{s+1}_ℓ` for every literal `ℓ`;
* (Ref-11) `enable^{s+1}`.

**Formalization Note.** With `a-lit^A_ℓ` the constant `1{ℓ ∈ C_A}` (p.22), the clauses (Ref-3) with
`ℓ ∉ C_A` are satisfied and are omitted, and the false literal `¬a-lit^A_ℓ` is dropped from the
others. A clause is a cedent of literals (p.15: a CNF is collected into a set of cedents), so
every axiom has depth 0 and is available in PK_0. -/
def refCNF {n m : ℕ} (φ : Fin m → Finset (Lit n)) (s : ℕ) : Set (Cedent (RefVar n m s)) :=
  open RefVar in
  {Γ |
    -- (Ref-1)
    (∃ (B B' : Fin (s + 1)) (i : Fin n) (ℓ : Lit n), B' < B ∧ ℓ ≠ (i, true) ∧
      Γ = [neg (enable B), neg (res B i), neg (lpoint B B'), neg (lit B' ℓ), pos (lit B ℓ)]) ∨
    -- (Ref-2)
    (∃ (B B' : Fin (s + 1)) (i : Fin n) (ℓ : Lit n), B' < B ∧ ℓ ≠ (i, false) ∧
      Γ = [neg (enable B), neg (res B i), neg (rpoint B B'), neg (lit B' ℓ), pos (lit B ℓ)]) ∨
    -- (Ref-3)
    (∃ (B : Fin (s + 1)) (A : Fin m) (ℓ : Lit n), ℓ ∈ φ A ∧
      Γ = [neg (enable B), neg (weak B A), pos (lit B ℓ)]) ∨
    -- (Ref-4)
    (∃ B : Fin (s + 1),
      Γ = neg (enable B) :: neg (derived B) :: (List.finRange n).map fun i => pos (res B i)) ∨
    -- (Ref-5)
    (∃ B : Fin (s + 1),
      Γ = neg (enable B) :: pos (derived B) :: (List.finRange m).map fun A => pos (weak B A)) ∨
    -- (Ref-6)
    (∃ B : Fin (s + 1),
      Γ = neg (enable B) :: neg (derived B) ::
        ((List.finRange (s + 1)).filter (· < B)).map fun B' => pos (lpoint B B')) ∨
    -- (Ref-7)
    (∃ B : Fin (s + 1),
      Γ = neg (enable B) :: neg (derived B) ::
        ((List.finRange (s + 1)).filter (· < B)).map fun B' => pos (rpoint B B')) ∨
    -- (Ref-8)
    (∃ (B B' : Fin (s + 1)), B' < B ∧
      Γ = [neg (enable B), neg (lpoint B B'), pos (enable B')]) ∨
    -- (Ref-9)
    (∃ (B B' : Fin (s + 1)), B' < B ∧
      Γ = [neg (enable B), neg (rpoint B B'), pos (enable B')]) ∨
    -- (Ref-10)
    (∃ ℓ : Lit n, Γ = [neg (lit (Fin.last s) ℓ)]) ∨
    -- (Ref-11)
    Γ = [pos (enable (Fin.last s))]}

end RefWPHP


