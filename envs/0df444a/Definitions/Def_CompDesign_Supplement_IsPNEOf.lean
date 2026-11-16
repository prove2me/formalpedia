-- Prove2me | Definitions.Def_CompDesign_Supplement_IsPNEOf
-- name    : CompDesign_Supplement_IsPNEOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:48:34.289783+00:00
-- url     : https://prove2.me/theorems/e3fd1191-dd20-4e33-a64d-15f27eeb7057
-- title:
--   Pure, strict and principal-favoring pure Nash equilibria of a general payment rule
-- statement:
--   Let $N=\{1,\dots,n\}$ be the agents, $c_i\ge 0$ their private costs and $p:2^N\to\mathbb R^N$ a payment rule, $p_i(S)$ being the payment to agent $i$ when the set of participating agents is $S$. Agent $i$'s utility is $u_i(S)=p_i(S)-c_i$ if $i\in S$ and $u_i(S)=0$ otherwise.
--
--   1. $S\subseteq N$ is a **pure Nash equilibrium** if no agent strictly gains by switching its participation decision:
--   $$p_i(S)-c_i\ge 0\ \ (i\in S),\qquad p_i(S\cup\{i\})-c_i\le 0\ \ (i\notin S).$$
--   2. $S$ is a **strict** pure Nash equilibrium if both inequalities are strict, so every agent strictly prefers its action.
--   3. $S$ is a **principal-favoring** pure Nash equilibrium if it is a pure Nash equilibrium and an indifferent agent takes the action maximizing the principal's value $v$: if $i\in S$ and $p_i(S)=c_i$ then $v(S\setminus\{i\})\le v(S)$, and if $i\notin S$ and $p_i(S\cup\{i\})=c_i$ then $v(S\cup\{i\})\le v(S)$.
--
--   These are the equilibrium notions of Theorems 4.2, 5.2–5.4, 6.2, B.1 and C.1 for rules other than the marginal-contribution rule.
--
--   **Formalization Note** A payment rule is a function `Finset (Fin n) → Fin n → ℝ`; nonnegativity and budget feasibility are hypotheses of the theorems. For $p=p^{mc}$ item 1 is the published `CompDesignBFM.IsPNE`.
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Definition 3.1, p.14 (PDF 17); utility §3.1, p.13 (PDF 16); strict equilibria Theorems 5.3, 6.2, pp.31, 50 (PDF 34, 53); principal-favoring tie-breaking pp.30–32 (PDF 33–35)

import Mathlib

namespace CompDesign.Supplement

/-- The utility of agent `i` at the participating set `S` under a general payment rule `p`
(Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…), §3.1, p.13, PDF 16): `u_i(S) = p_i(S) − c_i` if `i ∈ S`, and `u_i(S) = 0` otherwise. -/
def utilOf {n : ℕ} (p : Finset (Fin n) → Fin n → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n))
    (i : Fin n) : ℝ :=
  if i ∈ S then p S i - c i else 0

/-- A pure Nash equilibrium of the binary participation game induced by a general payment rule `p`
at costs `c` (Definition 3.1, p.14, PDF 17, of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)):
`p_i(S) − c_i ≥ 0` for `i ∈ S` and `p_i(S ∪ {i}) − c_i ≤ 0` for `i ∉ S`.

**Formalization Note.** A payment rule is a function `p : 2^N → ℝ^N` (`Finset (Fin n) → Fin n → ℝ`);
its nonnegativity and budget feasibility are hypotheses of the theorems that use it. For
`p = p^mc` this is the published `CompDesignBFM.IsPNE`. -/
def IsPNEOf {n : ℕ} (p : Finset (Fin n) → Fin n → ℝ) (c : Fin n → ℝ) (S : Finset (Fin n)) :
    Prop :=
  (∀ i ∈ S, 0 ≤ p S i - c i) ∧ ∀ i, i ∉ S → p (insert i S) i - c i ≤ 0

/-- A strict pure Nash equilibrium (Theorems 5.3 and 6.2, pp.31 and 50, PDF 34 and 53, of
Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)): both equilibrium inequalities of Definition 3.1 are strict, so every agent strictly prefers
its action ("no matter how ties are handled", proof of Theorem 5.3, p.31). -/
def IsStrictPNEOf {n : ℕ} (p : Finset (Fin n) → Fin n → ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S, 0 < p S i - c i) ∧ ∀ i, i ∉ S → p (insert i S) i - c i < 0

/-- A principal-favoring pure Nash equilibrium (§5.2.3 and §5.3, pp.30–32, PDF 33–35, of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…)):
an indifferent agent takes the action that maximizes the principal's value. `S` is a pure Nash
equilibrium, and no zero-gain switch raises `v` strictly: for `i ∈ S` with `p_i(S) = c_i`,
`v(S ∖ {i}) ≤ v(S)`; for `i ∉ S` with `p_i(S ∪ {i}) = c_i`, `v(S ∪ {i}) ≤ v(S)`. -/
def IsPFPNEOf {n : ℕ} (p : Finset (Fin n) → Fin n → ℝ) (v : Finset (Fin n) → ℝ)
    (c : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  IsPNEOf p c S ∧ (∀ i ∈ S, p S i = c i → v (S.erase i) ≤ v S) ∧
    ∀ i, i ∉ S → p (insert i S) i = c i → v (insert i S) ≤ v S

end CompDesign.Supplement


