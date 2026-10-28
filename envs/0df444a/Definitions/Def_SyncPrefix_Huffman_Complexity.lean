-- Prove2me | Definitions.Def_SyncPrefix_Huffman_Complexity
-- name    : SyncPrefix_Huffman_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:08.641796+00:00
-- url     : https://prove2.me/theorems/b8f31150-6008-4a23-a1fb-a59efbcfa3c3
-- title:
--   pp. 3–5 — P = NP, value-form approximability of Short Sync Word and of Set Cover, minimum cover size, and the Set Cover hardness of [4]
-- statement:
--   This file states the complexity notions in which the paper's inapproximability results are phrased.
--
--   1. **P = NP** means that every language in NP over a finite nonempty alphabet is in P, for one-tape deterministic Turing machines.
--   2. Short Sync Word is **approximable in polynomial time within $\rho(n)$** on a class $\mathcal C$ of complete automata if there are a polynomial-time algorithm and a threshold $n_0$ such that, on the encoding of every synchronizing automaton $A \in \mathcal C$ with $n \ge n_0$ states, the algorithm outputs a number $v$ (written in unary) with
--   $$\ell(A) \le v \le \rho(n)\,\ell(A).$$
--   3. For a Set Cover instance with points $X$, $|X| = p$, and a family $C$ of subsets of $X$, $\mathrm{OPT}$ denotes the minimum size of a subfamily covering $X$. Set Cover is **approximable within $\rho(p)$** on a class of instances if a polynomial-time algorithm and a threshold $n_0$ give, on every instance of the class that has a cover and has $p \ge n_0$, a number $v$ with $\mathrm{OPT} \le v \le \rho(p)\,\mathrm{OPT}$.
--   4. The **Set Cover hardness of [4]**, as quoted on p. 5 of the paper: for every $\gamma > 0$ there is $c' > 0$ such that, if Set Cover restricted to instances with $|C| \le |X|^{1+\gamma}$ is approximable in polynomial time within $c' \log p$, then P = NP.
--
--   The last item is the one result from the literature the paper's proof of Corollary 8 rests on; the theorems of the mission take it as a hypothesis.
--
--   **Formalization Note** Polynomial time, P and NP are those of the published definitions `CookPvsNP_defs`; Set Cover instances, covers and their encoding are those of the published `SetCoverThreshold.SetCover.Instance`. Approximability is in value form with the threshold $n_0$ chosen before the instance, as in the published definition of Feige's set-cover threshold; logarithms are natural (the base is absorbed in the constants). `minCover` is `0` (junk) on an instance without a cover, and every statement assumes a cover exists.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 3 (Short Sync Word), p. 5 (Set Cover and the hardness result of [4])

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Automata
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Instance

namespace SyncPrefix.Huffman

open SetCoverThreshold.SetCover

/-- `P = NP`: every NP language over every finite nonempty alphabet is in P. -/
def PEqNP : Prop :=
  ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym], CookPvsNP.NP Sym ⊆ CookPvsNP.P Sym

/-- Short Sync Word can be approximated in polynomial time within `ρ(n)` on the class `C`
(value form): a polynomial-time `Alg` and a threshold `n₀` such that, on every synchronizing
automaton `A` of the class with `n₀ ≤ n` states, the output length `v` satisfies
`syncLength ≤ v ≤ ρ(n) · syncLength`. -/
def SSWApproxWithin (C : Automaton → Prop) (ρ : ℕ → ℝ) : Prop :=
  ∃ Alg : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg ∧
    ∃ n₀ : ℕ, ∀ A : Automaton, C A → IsSynchronizing A.δ → n₀ ≤ A.n →
      syncLength A.δ ≤ (Alg A.encode).length ∧
        ((Alg A.encode).length : ℝ) ≤ ρ A.n * syncLength A.δ

/-- The minimum size of a set cover. Junk value `0` when the instance is not coverable. -/
noncomputable def minCover (I : SCInstance) : ℕ :=
  sInf {c | ∃ C, I.IsCover C ∧ C.card = c}

/-- Set Cover can be approximated in polynomial time within `ρ(p)` on the class `C` (value
form, `p = I.n` points): a polynomial-time `Alg` and a threshold `n₀` such that, on every
coverable instance of the class with `n₀ ≤ p`, the output length `v` satisfies
`minCover ≤ v ≤ ρ(p) · minCover`. -/
def SCApproxWithinOn (C : SCInstance → Prop) (ρ : ℕ → ℝ) : Prop :=
  ∃ Alg : List (Option Bool) → List Unit, CookPvsNP.PolyTimeComputable Alg ∧
    ∃ n₀ : ℕ, ∀ I : SCInstance, C I → I.Coverable → n₀ ≤ I.n →
      minCover I ≤ (Alg I.encode).length ∧
        ((Alg I.encode).length : ℝ) ≤ ρ I.n * minCover I

/-- The Set Cover hardness of [4] quoted on p. 5: for every `γ > 0` there is `c' > 0` such that
a polynomial-time `c' log p`-approximation of Set Cover on instances with `|C| ≤ |X|^{1+γ}`
implies `P = NP`. -/
def SetCoverHardness : Prop :=
  ∀ γ : ℝ, 0 < γ → ∃ c' : ℝ, 0 < c' ∧
    (SCApproxWithinOn (fun I => (I.sets.length : ℝ) ≤ (I.n : ℝ) ^ (1 + γ))
      (fun p => c' * Real.log p) → PEqNP)

end SyncPrefix.Huffman


