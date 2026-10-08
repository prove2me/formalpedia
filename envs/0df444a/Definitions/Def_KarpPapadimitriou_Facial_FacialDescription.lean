-- Prove2me | Definitions.Def_KarpPapadimitriou_Facial_FacialDescription
-- name    : KarpPapadimitriou_Facial_FacialDescription
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:16:15.406996+00:00
-- url     : https://prove2.me/theorems/64cb9e0b-dc83-404c-9bd6-fa4d8e8f00a6
-- title:
--   Facial descriptions and small facial descriptions of a c.o.p.
-- statement:
--   Let $C=(L,n,S)$ be a combinatorial optimization problem. A **facial description** of $C$ is a set $F(C)$ of triples $\langle z,f,g\rangle$ such that
--
--   1. each element of $F(C)$ has $z\in L$, $f\in\mathbb Z^{n(z)}$ and $g\in\mathbb Z$;
--   2. for each $z\in L$ and every $x\in\mathbb Q^{n(z)}$,
--   $$x\in\mathrm{CH}(S(z))\iff f\cdot x\le g\ \text{ for every triple }\langle z,f,g\rangle\in F(C).$$
--
--   Thus $F(C)$ describes $\mathrm{CH}(S(z))$ by linear inequalities, for each $z\in L$.
--
--   The facial description is **small** if there is a polynomial $p$ such that for every $\langle z,f,g\rangle\in F(C)$ each component of $f$ and $g$ has absolute value at most $2^{p(|z|+n(z))}$.
--
--   Finally, "$F(C)\in\mathrm{NP}$" means that the language of codes $\langle z,f,g\rangle$ of the triples of $F(C)$ belongs to Cook's class $\mathrm{NP}$.
--
--   These notions make precise what a "satisfactory" linear characterization of a combinatorial polytope would be: coefficients of polynomial bit length, and short proofs that a given inequality belongs to the list.
--
--   **Formalization Note** The polynomial $p$ is taken in the form $m\mapsto m^k+k$ with $k\in\mathbb N$ fixed before all triples; every polynomial is eventually dominated by such a function, so this is equivalent. Triples are elements of the dependent type $\Sigma z,\ \mathbb Z^{n(z)}\times\mathbb Z$, coded over the alphabet $\{0,1,-,\#\}$ as in the definition of a c.o.p.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), p. 4 (facial description) and p. 5 (small facial description)

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_COP

namespace KarpPapadimitriou.Facial

open CookPvsNP ProjSchedTW.Complexity

/-! # Facial descriptions and small facial descriptions

Karp & Papadimitriou, MIT/LCS/TM-154 (Feb. 1980), §2, pp. 4–5. -/

/-- A set of triples `⟨z, f, g⟩` with `z ∈ {0,1}*`, `f ∈ ℤⁿ⁽ᶻ⁾` and `g ∈ ℤ`. -/
abbrev Triples (C : COP) : Type := Set (Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ)

/-- **Facial description** (p. 4). `F` is a facial description of `C` if (i) every triple
`⟨z, f, g⟩ ∈ F` has `z ∈ L`, and (ii) for each `z ∈ L` and every `x ∈ ℚⁿ⁽ᶻ⁾`,
`x ∈ CH(S(z))` iff `f · x ≤ g` for every triple `⟨z, f, g⟩ ∈ F`. -/
def IsFacialDescription (C : COP) (F : Triples C) : Prop :=
  (∀ t ∈ F, t.1 ∈ C.L) ∧
    ∀ z ∈ C.L, ∀ x : Fin (C.n z) → ℚ,
      x ∈ hull C z ↔
        ∀ (f : Fin (C.n z) → ℤ) (g : ℤ), (⟨z, (f, g)⟩ : Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ) ∈ F →
          (fun j => (f j : ℚ)) ⬝ᵥ x ≤ (g : ℚ)

/-- **Small** (p. 5). There is a polynomial, here `m ↦ m ^ k + k`, such that for every triple
`⟨z, f, g⟩ ∈ F` each component of `f` and `g` has absolute value at most `2 ^ p(|z| + n(z))`. -/
def IsSmall (C : COP) (F : Triples C) : Prop :=
  ∃ k : ℕ, ∀ t ∈ F,
    (∀ i, |t.2.1 i| ≤ (2 : ℤ) ^ ((t.1.length + C.n t.1) ^ k + k)) ∧
      |t.2.2| ≤ (2 : ℤ) ^ ((t.1.length + C.n t.1) ^ k + k)

/-- The language of codes `⟨z, f, g⟩` of the triples of `F`; "`F(C) ∈ NP`" means that this
language is in `NP`. -/
def tripleLang (C : COP) (F : Triples C) : Lang BSym :=
  {w | ∃ t ∈ F, w = encTriple t.1 t.2.1 t.2.2}

end KarpPapadimitriou.Facial


