-- Prove2me | Definitions.Def_AgnosticTNS_ptrace
-- name    : AgnosticTNS_ptrace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:10.35955+00:00
-- url     : https://prove2.me/theorems/1aba34fc-e1cc-469d-b6e6-f5d8b71aea71
-- title:
--   Reduced operator $\mathrm{tr}_{[n]\setminus A}(X)$
-- statement:
--   For an operator $X$ on $(\mathbb C^d)^{\otimes n}$ and a subsystem $A\subseteq[n]$, the partial trace over the complement of $A$ is the operator on the qudits of $A$ with entries
--   $$
--   \big(\mathrm{tr}_{[n]\setminus A}X\big)_{a,b}=\sum_{z}X_{(a,z),(b,z)},
--   $$
--   the sum running over the labels $z$ of the qudits outside $A$. It gives $\sigma_{K,A}(\rho)=\mathrm{tr}_{[n]\setminus A}(K\rho K^\dagger)$ of Section 2.3.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 2.3, p.14; Claim 2.2, p.12; Eqs. (3.36), (3.44)

import Mathlib

namespace AgnosticTNS

/-- **The reduced operator `tr_{[n]∖A}(X)`** on a subsystem `A ⊆ [n]`, used in §2.3, p.14
(`σ_{K,A}(ρ) := tr_{[n]∖A}(KρK†)`), Claim 2.2 (p.12) and Eqs. (3.36), (3.44) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
`(tr_{[n]∖A} X)_{a,b} = Σ_z X_{(a,z),(b,z)}`, the sum over the labels `z` of the qudits outside `A`.

**Formalization Note** The qudits of `A` are indexed by the subtype `↥A` (in the order of `Fin n`); a
configuration `x : Fin n → Fin d` has `A`-part `x|_A` and the sum runs over all pairs `x, y` with
`x|_A = a`, `y|_A = b` and `x = y` outside `A`. -/
def ptrace {n d : ℕ} (A : Finset (Fin n)) (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    Matrix (↥A → Fin d) (↥A → Fin d) ℂ :=
  Matrix.of fun a b => ∑ x, ∑ y,
    if (∀ i : ↥A, x i = a i) ∧ (∀ i : ↥A, y i = b i) ∧ (∀ i, i ∉ A → x i = y i) then X x y else 0

end AgnosticTNS


