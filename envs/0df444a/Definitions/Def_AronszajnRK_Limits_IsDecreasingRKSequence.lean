-- Prove2me | Definitions.Def_AronszajnRK_Limits_IsDecreasingRKSequence
-- name    : AronszajnRK_Limits_IsDecreasingRKSequence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:48:39.202077+00:00
-- url     : https://prove2.me/theorems/6c6ea61e-f3bd-4b80-9850-3b4c62a68933
-- title:
--   Standing assumptions of §9 A — a decreasing sequence of classes with increasing norms
-- statement:
--   Let $X$ be a set, $E_1\subset E_2\subset\cdots$ subsets of $X$, and for each $n$ let $F_n$ be a complex Hilbert space of functions on $E_n$ with norm $\|\cdot\|_n$. For $f_n\in F_n$ and $m\le n$ write $f_{nm}$ for the restriction of $f_n$ to $E_m$. The sequence satisfies the **standing assumptions of §9 A** if
--
--   1. $E = E_1 + E_2 + \cdots$ (the union) is all of $X$, and $E_1\subset E_2\subset\cdots$;
--   2. the classes decrease: for every $f_n\in F_n$ and every $m\le n$, $f_{nm}\in F_m$;
--   3. the norms increase: for every $f_n\in F_n$ and every $m\le n$,
--   $$\|f_{nm}\|_m \le \|f_n\|_n .$$
--
--   Together with the existence of a reproducing kernel $K_n$ of every $F_n$, these are the hypotheses of every result of the mission.
--
--   **Formalization Note** The sequence is indexed from $0$ instead of $1$. "$g\in F_m$ is the restriction of $f\in F_n$" is written pointwise: $g(x)=f(x)$ for all $x\in E_m$. The existence of the kernels is not part of this predicate; it is supplied by the `RKHS` and `CompleteSpace` instances of the statements that use it.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 362, §9 A, (1)–(3)

import Mathlib

namespace AronszajnRK.Limits

/-- The standing assumptions of Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math.
Soc. 68 (1950), §9 A, (1)–(3), p. 362, PDF p. 26, on a sequence of sets `E n ⊆ X` and a sequence
of complex Hilbert spaces `H n` of functions on `E n` (the classes `Fₙ` with norms `‖ ‖ₙ`):

* (1) `E₁ ⊂ E₂ ⊂ ⋯` and `E = E₁ + E₂ + ⋯` (the union) is the whole ambient set `X`;
* (2) for every `fₙ ∈ Fₙ` and every `m ≤ n`, the restriction `fₙₘ` of `fₙ` to `Eₘ` belongs to
  `Fₘ`;
* (3) for every `fₙ ∈ Fₙ` and every `m ≤ n`, `‖fₙₘ‖ₘ ≤ ‖fₙ‖ₙ`.

"`g : H m` is the restriction of `f : H n`" is written pointwise: `g x = f x` for every point
`x ∈ E m` (which lies in `E n` by (1)). The sequence is indexed from `0` rather than `1`. The
existence of the reproducing kernels `Kₙ` is not part of this predicate: it is the
`[RKHS ℂ (H n) (E n) ℂ]` and `[CompleteSpace (H n)]` instances of the statements using it. -/
structure IsDecreasingRKSequence {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] : Prop where
  /-- (1): the sets increase. -/
  mono : Monotone E
  /-- (1): their union is the whole set `X`. -/
  iUnion_eq : (⋃ n, E n) = Set.univ
  /-- (2): the restriction to `E m` of an element of `H n` (`m ≤ n`) is an element of `H m`. -/
  restrict_mem : ∀ {m n : ℕ}, m ≤ n → ∀ f : H n, ∃ g : H m,
    ∀ (x : X) (hm : x ∈ E m) (hn : x ∈ E n), g ⟨x, hm⟩ = f ⟨x, hn⟩
  /-- (3): restriction does not increase the norm. -/
  norm_restrict_le : ∀ {m n : ℕ}, m ≤ n → ∀ (f : H n) (g : H m),
    (∀ (x : X) (hm : x ∈ E m) (hn : x ∈ E n), g ⟨x, hm⟩ = f ⟨x, hn⟩) → ‖g‖ ≤ ‖f‖

end AronszajnRK.Limits


