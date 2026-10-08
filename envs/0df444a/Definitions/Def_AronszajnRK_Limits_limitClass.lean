-- Prove2me | Definitions.Def_AronszajnRK_Limits_limitClass
-- name    : AronszajnRK_Limits_limitClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:49:17.015338+00:00
-- url     : https://prove2.me/theorems/c59c8780-94c1-486d-96b0-f11664ef6e3e
-- title:
--   The limit class $F_0$ of §9, Theorem I
-- statement:
--   Under the setting of §9 A (sets $E_n$ increasing to $E$, classes $F_n$ of functions on $E_n$), the **limit class** $F_0$ is the set of all functions $f_0$ defined in $E$ such that
--
--   1. (1°) for every $n$, the restriction $f_{0n}$ of $f_0$ to $E_n$ belongs to $F_n$;
--   2. (2°) the limit
--   $$\lim_{n\to\infty}\|f_{0n}\|_n$$
--   exists and is finite.
--
--   Theorem I of §9 identifies $F_0$, normed by this limit, as the class whose reproducing kernel is the limit of the kernels $K_n$.
--
--   **Formalization Note** Condition 1° is the existence of a sequence $g_n\in F_n$ with $g_n(x)=f_0(x)$ for $x\in E_n$; this $g_n$ is unique because elements of $F_n$ are functions. Condition 2° is convergence of the real sequence $\|g_n\|_n$ to a real number, not a supremum: no junk value is involved.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), pp. 362–363, §9, Theorem I (definition of F₀)

import Mathlib

namespace AronszajnRK.Limits

open Filter Topology

/-- The limit class `F₀` of Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68
(1950), §9, Theorem I, pp. 362–363, PDF pp. 26–27: the set of all functions `f₀` defined in
`E = X` such that

* 1° for every `n`, the restriction `f₀ₙ` of `f₀` to `E n` belongs to `Fₙ` (here: there is
  `g n : H n` with `g n x = f₀ x` for all `x ∈ E n`), and
* 2° `lim_{n→∞} ‖f₀ₙ‖ₙ < ∞` (here: the real sequence `‖g n‖` converges to a real number `L`).

Since each `H n` is a space of functions (`RKHS` coercions are injective), `g n` is the unique
element of `H n` with the restricted function, so the existential over `g` loses nothing. -/
def limitClass {X : Type*} (E : ℕ → Set X) (H : ℕ → Type*)
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
    [∀ n, RKHS ℂ (H n) (E n) ℂ] : Set (X → ℂ) :=
  {f₀ | ∃ g : ∀ n, H n, (∀ (n : ℕ) (x : E n), g n x = f₀ x) ∧
    ∃ L : ℝ, Tendsto (fun n => ‖g n‖) atTop (𝓝 L)}

end AronszajnRK.Limits


