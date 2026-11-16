-- Prove2me | Definitions.Def_IQPForrelation832_SingleQuery_Supplement_OracleFourier
-- name    : IQPForrelation832_SingleQuery_Supplement_OracleFourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:52:06.557818+00:00
-- url     : https://prove2.me/theorems/5a6979db-dba8-4cae-900a-746f37d0a50e
-- title:
--   Restrictions and normalized oracle-bit Fourier coefficients
-- statement:
--   A restriction $\rho$ assigns a fixed sign or a free marker to each of the original $N=2^n$ addresses. Write $\Gamma$ for its free set and $x\in\{-1,1\}^{\Gamma}$ for a free assignment; $x\rho$ denotes its extension. For every $S\subseteq\Gamma$, define
--   $$
--   \chi_S(x)=\prod_{a\in S}x_a,\qquad
--   \widehat{p|\rho}(S)=2^{-|\Gamma|}\sum_x p(x\rho)\chi_S(x).
--   $$
--   Total mass sums $|\widehat{p|\rho}(S)|$ over all $S$, including the empty set; level mass $L_{1,\ell}$ sums over $|S|=\ell$. Multilinear degree at most $k$ asserts both reconstruction by these characters and vanishing for $|S|>k$. The restriction vectors are computed by
--   $$
--   \epsilon_A(\rho)=\prod_{a\in A\setminus\Gamma}\rho_a,\qquad
--   v_C^\rho=\sum_{A\cap\Gamma=C}\epsilon_A(\rho)v_A.
--   $$
--   The binomial bound is the exact sum, over $0\le a,b\le d$ with $a+b=\ell$, of $\sqrt{\min\{\binom da\binom Nb,\binom db\binom Na\}}$. These definitions allow empty free sets, empty accepting sets, zero queries and zero address dimension. Boolean true encodes $+1$ and false encodes $-1$; the free-coordinate subtype contains exactly $\Gamma$. This normalized average on oracle bits is distinct from the published orthonormal address-space Fourier transform.
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), p. 12, Definitions 1–2; pp. 25–30, restriction notation, Lemma 5, Theorems 5–6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_IQPForrelation832_SingleQuery_Supplement_PhaseCircuits

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery.Supplement

open QAlgorithms

/-- true is +1, false is -1. This finite type avoids adding sign hypotheses to each sum. -/
def signValue (b : Bool) : ℝ := if b then 1 else -1

abbrev Restriction (n : ℕ) := Cube n → Option Bool

noncomputable def freeSet {n : ℕ} (ρ : Restriction n) : Finset (Cube n) := by
  classical
  exact Finset.univ.filter (fun a => ρ a = none)

abbrev FreeAssignment {n : ℕ} (ρ : Restriction n) := {a : Cube n // a ∈ freeSet ρ} → Bool

noncomputable def extendRestriction {n : ℕ} (ρ : Restriction n) (x : FreeAssignment ρ) :
    Cube n → ℝ := fun a =>
  if h : a ∈ freeSet ρ then signValue (x ⟨a,h⟩) else signValue ((ρ a).getD false)

noncomputable def oracleCharacter {n : ℕ} (ρ : Restriction n)
    (S : Finset {a : Cube n // a ∈ freeSet ρ}) (x : FreeAssignment ρ) : ℝ :=
  ∏ a ∈ S, signValue (x a)

/-- Normalized AVERAGE on remaining oracle signs, not the address-space orthonormal transform. -/
noncomputable def oracleHat {n : ℕ} (p : (Cube n → ℝ) → ℝ) (ρ : Restriction n)
    (S : Finset {a : Cube n // a ∈ freeSet ρ}) : ℝ :=
  ((2 : ℝ) ^ (freeSet ρ).card)⁻¹ *
    ∑ x : FreeAssignment ρ, p (extendRestriction ρ x) * oracleCharacter ρ S x

noncomputable def totalMass {n : ℕ} (p : (Cube n → ℝ) → ℝ) (ρ : Restriction n) : ℝ :=
  ∑ S : Finset {a : Cube n // a ∈ freeSet ρ}, |oracleHat p ρ S|

noncomputable def levelMass {n : ℕ} (p : (Cube n → ℝ) → ℝ) (ρ : Restriction n) (ell : ℕ) : ℝ :=
  ∑ S : Finset {a : Cube n // a ∈ freeSet ρ}, if S.card = ell then |oracleHat p ρ S| else 0

/-- The actual multilinear character expansion, AND vanishing above the asserted degree. -/
def MultilinearDegreeLE {n : ℕ} (p : (Cube n → ℝ) → ℝ) (ρ : Restriction n) (k : ℕ) : Prop :=
  (∀ x : FreeAssignment ρ, p (extendRestriction ρ x) =
    ∑ S : Finset {a : Cube n // a ∈ freeSet ρ}, oracleHat p ρ S * oracleCharacter ρ S x) ∧
  ∀ S : Finset {a : Cube n // a ∈ freeSet ρ}, k < S.card → oracleHat p ρ S = 0

noncomputable def fixedSign {n : ℕ} (ρ : Restriction n) (A : Finset (Cube n)) : ℝ :=
  ∏ a ∈ A \ freeSet ρ, signValue ((ρ a).getD false)

noncomputable def restrictedVector {n m : ℕ} (c : PhaseMiddle n m) (ρ : Restriction n)
    (C : Finset {a : Cube n // a ∈ freeSet ρ}) : EuclideanSpace ℂ (Qubits m) := by
  classical
  exact ∑ A : Finset (Cube n), if A ∩ freeSet ρ = C.image Subtype.val then
    (fixedSign ρ A : ℂ) • parityVector c A else 0

noncomputable def binomialBound (d N ell : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (d+1), ∑ b ∈ Finset.range (d+1), if a+b = ell then
    Real.sqrt (min ((Nat.choose d a : ℝ) * Nat.choose N b)
      ((Nat.choose d b : ℝ) * Nat.choose N a)) else 0

end IQPForrelation832.SingleQuery.Supplement


