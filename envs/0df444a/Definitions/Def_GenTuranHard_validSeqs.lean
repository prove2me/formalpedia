-- Prove2me | Definitions.Def_GenTuranHard_validSeqs
-- name    : GenTuranHard_validSeqs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:19.497079+00:00
-- url     : https://prove2.me/theorems/d2f7d9fd-1b95-4987-a711-51d101fa5753
-- title:
--   Sequences $(I_1,\dots,I_s)$ satisfying (4.1), terminal graphs $T_s$, monomials and exponent vectors
-- statement:
--   For a graph $T$ and $s \ge 0$, a sequence $(I_1, \dots, I_s)$ of vertex sets and graphs $(T_0, \dots, T_s)$ **satisfy (4.1)** (p.14) if
--
--   $$
--   T_0 = T, \qquad I_i \text{ is an independent set of } T_{i-1}, \qquad T_i = (T_{i-1})_{I_i} \qquad (i = 1, \dots, s).
--   $$
--
--   The empty set is allowed at every step. $T_s$ is the **terminal graph** of the sequence. For $\mathbf x = (x_1, \dots, x_s)$ the sequence contributes the **monomial** $\prod_{i=1}^{s} x_i^{|I_i|}$, whose **exponent vector** is $(|I_1|, \dots, |I_s|)$ (p.15).
--
--   These sequences index the expansion of $\hom(T, L_{\mathbf x}(G))$ (Lemma 4.3).
--
--   **Formalization Note** A sequence is a list of finite sets of vertex indices, each read against the current graph $T_{i-1}$ (numbered on $\{0,\dots,v(T_{i-1})-1\}$). The set of all sequences of length exactly $s$ is built step by step from the independent subsets of the current graph, so it is finite and contains exactly the sequences of (4.1).
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), (4.1), p.14; p.15 (exponent vectors)

import Mathlib
import Definitions.Def_GenTuranHard_quotGraph

set_option autoImplicit false

namespace GenTuranHard

/-- `I ⊆ {0, …, v(Q) − 1}` is an independent set of `Q`. -/
def IsIndepN (Q : FinGraph) (I : Finset ℕ) : Prop :=
  I ⊆ Finset.range Q.1 ∧
    ∀ a ∈ I, ∀ b ∈ I, ∀ (ha : a < Q.1) (hb : b < Q.1), ¬ Q.2.Adj ⟨a, ha⟩ ⟨b, hb⟩

open scoped Classical in
/-- The **sequences `(I₁, …, I_s)` satisfying (4.1)** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256
dc85633a…, (4.1), p.14) starting from `T₀ = Q`, of length exactly `s`: `I_i` is an independent set of
`T_{i−1}` and `T_i = (T_{i−1})_{I_i}`. Each `I_i` is a set of vertex indices of `T_{i−1}`; the empty set
is allowed at every step. -/
noncomputable def validSeqs : ℕ → FinGraph → Finset (List (Finset ℕ))
  | 0, _ => {[]}
  | s + 1, Q =>
      ((Finset.range Q.1).powerset.filter (IsIndepN Q)).biUnion
        (fun I => (validSeqs s (quotN Q I)).image (I :: ·))

/-- The terminal graph `T_s` of a sequence `(I₁, …, I_s)` started at `T₀ = Q` ((4.1), p.14). -/
noncomputable def termGraph : FinGraph → List (Finset ℕ) → FinGraph
  | Q, [] => Q
  | Q, I :: Is => termGraph (quotN Q I) Is

/-- The monomial `∏_{i=1}^s x_i^{|I_i|}` of a sequence (p.14) for `x = [x₁, …, x_s]`. -/
def monoWeight (x : List ℕ) (Is : List (Finset ℕ)) : ℕ :=
  (List.zipWith (fun xi I => xi ^ I.card) x Is).prod

/-- The exponent vector `(|I₁|, …, |I_s|)` of a sequence (p.15). -/
def expVec (Is : List (Finset ℕ)) : List ℕ := Is.map Finset.card

end GenTuranHard


