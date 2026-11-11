-- Prove2me | Definitions.Def_LooseHamHitting_Main_Entropy
-- name    : LooseHamHitting_Main_Entropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:17:20.187634+00:00
-- url     : https://prove2.me/theorems/51c4f926-2a3b-4419-8244-d4a02e6538bd
-- title:
--   Entropy and relative entropy of finite laws (natural logarithm, 0 log 0 = 0)
-- statement:
--   For a finite set $S$ and $p:S\to\mathbb R$ (a law: $p\ge0$, $\sum_S p=1$), the **entropy** is
--   $$H(p)=-\sum_{z\in S}p(z)\log p(z),$$
--   with the natural logarithm and $0\log0=0$. For a map $X$ on $S$, $P[X=b]=\sum_{z\in S:\,X(z)=b}p(z)$ and $H[X]$ is the entropy of this law on $X(S)$. For laws $P,Q$ on $S$ the **relative entropy** is
--   $$D_{KL}[P\,\|\,Q]=\sum_{z\in S}P(z)\log\frac{P(z)}{Q(z)},$$
--   where terms with $P(z)=0$ are zero, and $D_{KL}=+\infty$ if $P(z)>0=Q(z)$ for some $z$.
--
--   **Formalization Note.** `Real.log 0 = 0` makes $0\log 0=0$ automatic. `klDiv` takes values in `EReal` so that the infinite case is $\top$.
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 12 (entropy and relative entropy)

import Mathlib

set_option autoImplicit false

/-!
# Entropy and relative entropy of finite laws (natural logarithm)

León, Liu, arXiv:2610.29894v1, p. 12. A law on a finite set `S` is a function `μ` with
`μ ≥ 0` on `S` and `∑_{z ∈ S} μ z = 1`; only its values on `S` are used.
-/

namespace LooseHamHitting.Main

noncomputable section

open Classical

/-- `H := −∑_{z ∈ S} p z log p z`, natural log; `Real.log 0 = 0` gives `0 log 0 = 0`. -/
def entropyOn {β : Type*} (S : Finset β) (p : β → ℝ) : ℝ :=
  -∑ z ∈ S, p z * Real.log (p z)

/-- `P[X = b]` for `X : ω → β` under the law `μ` on `S`. -/
def lawProb {ω β : Type*} (S : Finset ω) (μ : ω → ℝ) (X : ω → β) (b : β) : ℝ :=
  ∑ z ∈ S.filter (fun z => X z = b), μ z

/-- `H[X]`: the entropy of the law of `X : ω → β` under `μ` on `S`. -/
def lawEntropy {ω β : Type*} (S : Finset ω) (μ : ω → ℝ) (X : ω → β) : ℝ :=
  entropyOn (S.image X) (lawProb S μ X)

/-- `D_KL[P ‖ Q] := ∑_{z ∈ S} P z log (P z / Q z)` with terms `P z = 0` equal to zero, and `+∞`
when some `P z > 0 = Q z`. -/
def klDiv {β : Type*} (S : Finset β) (P Q : β → ℝ) : EReal :=
  if ∃ z ∈ S, 0 < P z ∧ Q z = 0 then ⊤
  else ((∑ z ∈ S, if P z = 0 then 0 else P z * Real.log (P z / Q z) : ℝ) : EReal)

end

end LooseHamHitting.Main


