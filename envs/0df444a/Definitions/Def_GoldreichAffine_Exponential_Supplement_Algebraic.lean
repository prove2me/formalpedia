-- Prove2me | Definitions.Def_GoldreichAffine_Exponential_Supplement_Algebraic
-- name    : GoldreichAffine_Exponential_Supplement_Algebraic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:11.495284+00:00
-- url     : https://prove2.me/theorems/4453caad-a70c-49fd-aebc-0ce43a74ae47
-- title:
--   Symmetric predicates, algebraic degree and algebraic immunity (Definition 3)
-- statement:
--   A predicate $P:\{0,1\}^d\to\{0,1\}$ is **symmetric** if its value depends only on the Hamming weight of its input.
--
--   Every $P$ has a unique algebraic normal form $P(x)=\bigoplus_{A\subseteq[d]}\lambda_A\prod_{j\in A}x_j$ over $\mathbb F_2$. Its **algebraic degree** is
--
--   $$\deg(P)=\max\big(\{0\}\cup\{|A|:\lambda_A=1\}\big).$$
--
--   A Boolean function $f\not\equiv0$ on $d$ inputs **annihilates** $P$ if $fP\equiv0$ (pointwise product). The **algebraic immunity** of $P$ is
--
--   $$\mathrm{AI}(P)=\min\{\deg(f): f\not\equiv0,\ fP\equiv0\ \text{or}\ f(P\oplus1)\equiv0\}.$$
--
--   The set of candidate degrees is never empty: $1\oplus P$ annihilates $P$ unless $P\equiv1$, and then $P$ annihilates $P\oplus1$. These notions state Theorems 4 and 5 and Lemmas 9 and 10.
--
--   **Formalization Note** The ANF coefficients are the published Möbius coefficients $\lambda_A=\bigoplus_{B\subseteq A}P(\mathbf 1_B)$ (`ParityCubes.anfCoeff`), which are the unique ANF coefficients. The minimum is a natural-number infimum; a sorry-free lemma in the file proves the candidate set nonempty, so the empty-set default of the infimum never applies.
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, Affine Advantage in Guess-type Attacks on Goldreich’s PRGs: Generalization, Characterization and Countermeasures, STOC 2027 submission #579 (October 2026), PDF SHA-256 c6e5f1bfbc08adde62b9863b4417adb47a894635ef9e887e40be2e7fcd8c0594, p. 3 (PDF p. 4) symmetric predicates; p. 5 (PDF p. 6), Definition 3

import Definitions.Def_GoldreichAffine_Exponential_BooleanCore
import Definitions.Def_ParityCubes_anfCoeff
open scoped BigOperators
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential.Supplement

/-- A predicate is symmetric if its value depends only on the Hamming weight (printed p.3 / PDF p.4). -/
def IsSymmetric {d : ℕ} (P : Predicate d) : Prop :=
  ∀ x y : Word d, weight x = weight y → P x = P y

/-- Definition 3 (printed p.5 / PDF p.6): deg(P) = max({0} ∪ {|A| : λ_A = 1}).
    The ANF coefficients λ_A are the published Möbius coefficients `ParityCubes.anfCoeff`;
    the sup of the empty family is 0, which is the {0} in the definition. -/
def algebraicDegree {d : ℕ} (P : Predicate d) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin d))).filter
    (fun A => ParityCubes.anfCoeff P A = true)).sup Finset.card

/-- f ≢ 0 and f annihilates P (f·P ≡ 0) or P ⊕ 1 (f·(P ⊕ 1) ≡ 0). -/
def IsAnnihilatorOf {d : ℕ} (P f : Predicate d) : Prop :=
  f ≠ (fun _ => false) ∧
    ((∀ x, (f x && P x) = false) ∨ (∀ x, (f x && !P x) = false))

/-- Degrees of all annihilators of P or of P ⊕ 1. -/
def annihilatorDegrees {d : ℕ} (P : Predicate d) : Set ℕ :=
  {k | ∃ f : Predicate d, IsAnnihilatorOf P f ∧ algebraicDegree f = k}

/-- The candidate set is never empty, so the infimum below is an attained minimum
    and never the `sInf ∅ = 0` default. -/
theorem annihilatorDegrees_nonempty {d : ℕ} (P : Predicate d) :
    (annihilatorDegrees P).Nonempty := by
  by_cases h : ∀ x, P x = true
  · refine ⟨_, P, ⟨?_, Or.inr ?_⟩, rfl⟩
    · intro hP
      have := congrFun hP (fun _ => false)
      simp [h] at this
    · intro x
      simp [h x]
  · push Not at h
    obtain ⟨x0, hx0⟩ := h
    refine ⟨_, fun x => !P x, ⟨?_, Or.inl ?_⟩, rfl⟩
    · intro hf
      have := congrFun hf x0
      simp_all
    · intro x
      show (!P x && P x) = false
      cases P x <;> rfl

/-- Definition 3: AI(P) = min{deg f : f ≢ 0, f P ≡ 0 or f (P ⊕ 1) ≡ 0}. -/
noncomputable def algebraicImmunity {d : ℕ} (P : Predicate d) : ℕ :=
  sInf (annihilatorDegrees P)

end GoldreichAffine.Exponential.Supplement


