-- Prove2me | Definitions.Def_RobustObedientPersuasion_Saddle_FarkasMinkowski
-- name    : RobustObedientPersuasion_Saddle_FarkasMinkowski
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:14.520197+00:00
-- url     : https://prove2.me/theorems/4edb3d05-77c8-4979-b554-7e1266c439e5
-- title:
--   Appendix A — polyhedral sets, the characteristic cone of a linear system, and the Farkas–Minkowski property
-- statement:
--   Let $\Omega$ be a finite set and identify $\mathbb R^{|\Omega|}$ with the functions $x:\Omega\to\mathbb R$. A finite linear system $S=\{\langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ with $a_i\in\mathbb R^{|\Omega|}$, $b_i\in\mathbb R$ has solution set
--   $$\{x\in\mathbb R^{|\Omega|}:\ \langle a_i,x\rangle\le b_i\ \text{for } i=1,\dots,n\},$$
--   and a set is **polyhedral** when it is the solution set of some such finite system.
--
--   The **characteristic cone** of $S$ is the convex conic hull of the epigraphs of the conjugates of $f_i(x)=\langle a_i,x\rangle-b_i$ together with $\{(0,r):r\ge0\}$; explicitly
--   $$K=\Big\{\Big(\sum_{i=1}^n\lambda_i a_i,\ \sum_{i=1}^n\lambda_i b_i+t\Big):\ \lambda_i\ge0,\ t\ge0\Big\}\subseteq\mathbb R^{|\Omega|}\times\mathbb R .$$
--   The system has the **Farkas–Minkowski (FM) property** when $K$ is closed.
--
--   These notions are the vocabulary of Lemma 2.1, which asserts that the identified set of priors is polyhedral and that its representing system is FM.
--
--   **Formalization Note** The cone is defined as the set of nonnegative combinations itself, with no topological closure taken, so the FM property is a genuine closedness statement. In finite dimensions the weak-star topology of the source coincides with the product (Euclidean) topology used here.
-- source:
--   Shabab Neel, Robustly Obedient Data Driven Persuasion under State-dependent Sender Payoffs, STOC 2027 submission #51 (October 2026), PDF SHA-256 c8d16d8d566dd78eea1f7db42ce72f49000256f933311c4daac2de1df952b40d, Appendix A (Proof of Lemma 2.1), PDF p. 8; Lemma 2.1, PDF p. 3

import Mathlib

namespace RobustObedientPersuasion.Saddle

/-- The solution set `{x ∈ ℝ^Ω : ⟨a_i, x⟩ ≤ b_i for every i}` of a finite system of linear
inequalities indexed by `Fin n`. -/
def systemSet {Ω : Type*} [Fintype Ω] {n : ℕ} (a : Fin n → Ω → ℝ) (b : Fin n → ℝ) :
    Set (Ω → ℝ) :=
  {x | ∀ i, ∑ ω, a i ω * x ω ≤ b i}

/-- A set `S ⊆ ℝ^Ω` is polyhedral when it is the solution set of finitely many linear
inequalities. -/
def IsPolyhedral {Ω : Type*} [Fintype Ω] (S : Set (Ω → ℝ)) : Prop :=
  ∃ (n : ℕ) (a : Fin n → Ω → ℝ) (b : Fin n → ℝ), S = systemSet a b

/-- The characteristic cone of the system `{⟨a_i, x⟩ ≤ b_i}`: the convex conic hull of the
epigraphs of the conjugates `f_i^*` of `f_i(x) = ⟨a_i, x⟩ - b_i` (that is, of the rays
`{(a_i, r) : r ≥ b_i}`) together with `{(0, r) : r ≥ 0}`. Explicitly,
`K = {(∑ λ_i a_i, ∑ λ_i b_i + t) : λ_i ≥ 0, t ≥ 0}`; no topological closure is taken. -/
def characteristicCone {Ω : Type*} [Fintype Ω] {n : ℕ} (a : Fin n → Ω → ℝ) (b : Fin n → ℝ) :
    Set ((Ω → ℝ) × ℝ) :=
  {p | ∃ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) ∧ ∃ t : ℝ, 0 ≤ t ∧
    p = (∑ i, lam i • a i, ∑ i, lam i * b i + t)}

/-- The Farkas–Minkowski (FM) property of a linear system: its characteristic cone is closed
(in finite dimensions the weak-star topology is the Euclidean product topology). -/
def HasFarkasMinkowski {Ω : Type*} [Fintype Ω] {n : ℕ} (a : Fin n → Ω → ℝ) (b : Fin n → ℝ) :
    Prop :=
  IsClosed (characteristicCone a b)

end RobustObedientPersuasion.Saddle


