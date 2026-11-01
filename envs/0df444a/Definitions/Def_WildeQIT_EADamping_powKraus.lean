-- Prove2me | Definitions.Def_WildeQIT_EADamping_powKraus
-- name    : WildeQIT_EADamping_powKraus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:53.570351+00:00
-- url     : https://prove2.me/theorems/1bf8d07f-f4b9-4a50-a925-86a230a1c406
-- title:
--   Kraus operators of the tensor power $\mathcal N^{\otimes n}$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel with Kraus operators $\{K_i\}_{i\in\iota}$. The channel $\mathcal N_{A'^n\to B^n}\equiv(\mathcal N_{A'\to B})^{\otimes n}$ describing $n$ independent uses of $\mathcal N$ has the Kraus operators
--
--   $$
--   K_{i_1}\otimes\cdots\otimes K_{i_n},\qquad (i_1,\dots,i_n)\in\iota^n,
--   $$
--
--   with matrix entries $(K_{i_1}\otimes\cdots\otimes K_{i_n})_{y^n,x^n}=\prod_{j=1}^n (K_{i_j})_{y_j,x_j}$.
--
--   **Formalization Note** The $n$ inputs $A'^n$ are indexed by sequences `Fin n → a` and the outputs $B^n$ by `Fin n → b`; coordinate $j$ is the $j$-th channel use.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §21.1, p. 589, (21.5)

import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.1, p. 589, (21.5)
(`N_{A′ⁿ→Bⁿ} ≡ (N_{A′→B})^{⊗n}`, `n` independent uses of the channel).
-/

namespace WildeQIT.EADamping

/-- **Kraus operators of the `n`-fold tensor power `N^{⊗n}`** (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, §21.1, p. 589, (21.5)): for a channel `N` with Kraus operators
`Kᵢ`, the channel `(N_{A′→B})^{⊗n}` has the Kraus operators `K_{i₁} ⊗ ⋯ ⊗ K_{iₙ}`, indexed by
sequences `i : Fin n → ι`, with entries `(K_{i₁} ⊗ ⋯ ⊗ K_{iₙ})_{yⁿ, xⁿ} = ∏ⱼ (K_{iⱼ})_{yⱼ, xⱼ}`.

**Formalization Note.** The `n` channel inputs `A′ⁿ` are indexed by `Fin n → a` and the outputs `Bⁿ`
by `Fin n → b`; coordinate `j` is the `j`-th channel use. -/
def powKraus {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] (N : QChannel a b) (n : ℕ)
    (i : Fin n → N.ι) : Matrix (Fin n → b) (Fin n → a) ℂ :=
  Matrix.of fun y x => ∏ j, N.K (i j) (y j) (x j)

end WildeQIT.EADamping


