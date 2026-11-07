-- Prove2me | Definitions.Def_GenTuranHard_AddApproxNPHard
-- name    : GenTuranHard_AddApproxNPHard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:45.51668+00:00
-- url     : https://prove2.me/theorems/234d0091-4e0e-49df-8d64-428ff98cc39d
-- title:
--   NP-hardness of additive approximation on a class of inputs
-- statement:
--   Let $\Phi$ be a real-valued parameter of inputs, $\mathrm{err}$ a real-valued error bound and $\mathcal D$ a class of inputs, with inputs coded as binary strings. **Approximating $\Phi$ within the additive error $\mathrm{err}$ on $\mathcal D$ is NP-hard** if for every language $L$ in NP over a finite nonempty alphabet there are
--
--   1. a polynomial-time computable map $f$ from strings to inputs in $\mathcal D$ (polynomial time measured on the code of $f(x)$), and
--   2. a polynomial-time computable answer map $g$,
--
--   such that for every string $x$ and **every** rational number $q$ with $|q - \Phi(f(x))| \le \mathrm{err}(f(x))$, the map $g$ applied to $x$ and $q$ outputs "yes" exactly when $x \in L$.
--
--   An approximation within error $E$ is a number $x$ with $|x - \Phi(G)| \le E$ (proof of Theorem 3.2, p.11). With $\mathrm{err} \equiv 0$ the notion is NP-hardness of computing $\Phi$ exactly. The definition expresses every "is NP-hard" of the mission.
--
--   **Formalization Note** The reduction queries an approximation once and post-processes the answer, which is the form of the reductions of Theorem 3.2 and Corollary 3.3; it implies hardness under polynomial-time oracle (Cook) reductions. Turing machines, NP and polynomial time are those of the published `CookPvsNP` definitions (one-tape machines, time $|x|^k + k$). The verification file checks that a larger error gives a weaker hardness claim and that the notion fails for an empty class.
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), p.2 (complexity statements), proof of Theorem 3.2, p.11 (approximation within an additive error)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_GenTuranHard_encGraph

set_option autoImplicit false

namespace GenTuranHard

/-- **Approximating `Φ` within the additive error `err` on the inputs satisfying `Dom` is NP-hard**
(Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, p.2 and the proof of Theorem 3.2, p.11: an
approximation within error `E` returns a number `x` with `|x − Φ(G)| ≤ E`). For every language `L` in
NP over any finite nonempty alphabet there are a polynomial-time instance map `f` (with values in
`Dom`, its output measured through the code `enc`) and a polynomial-time answer map `g` such that for
every string `x` and **every** rational `q` with `|q − Φ(f x)| ≤ err(f x)`, the map `g`, reading `x`
and `q`, outputs `[true]` exactly when `x ∈ L`. With `err ≡ 0` this is NP-hardness of computing `Φ`
exactly.

**Formalization Note** "NP-hard" is read as a polynomial-time reduction from every NP language that
queries an approximation **once** and post-processes the answer (the reductions of Theorem 3.2 and
Corollary 3.3 have this form). It implies hardness under polynomial-time oracle (Cook) reductions.
Correctness is required for every admissible rational answer. Machines, `NP` and polynomial time are
those of the published `CookPvsNP` definitions (one-tape Turing machines, time `|x|^k + k`). -/
def AddApproxNPHard {α : Type} (enc : α → List Bool) (Dom : α → Prop) (Φ : α → ℝ)
    (err : α → ℝ) : Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym] (L : CookPvsNP.Lang Sym), L ∈ CookPvsNP.NP Sym →
    ∃ (f : List Sym → α) (g : List (Option (Sym ⊕ Bool)) → List Bool),
      CookPvsNP.PolyTimeComputable (fun x => enc (f x)) ∧
      CookPvsNP.PolyTimeComputable g ∧
      (∀ x, Dom (f x)) ∧
      ∀ (x : List Sym) (q : ℚ), |(q : ℝ) - Φ (f x)| ≤ err (f x) →
        (g (pairInput x q) = [true] ↔ x ∈ L)

end GenTuranHard


