-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes
-- name    : SymmetricDepthHierarchy_ConstantDepth_Supplement_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:54:23.924208+00:00
-- url     : https://prove2.me/theorems/7abeb9cc-9838-42cc-a550-1a2b67d0f3f9
-- title:
--   Matrix families, invariance, formula and skew predicates, and symmetric classes
-- statement:
--   Let $K$ be a field and $X_n=\{x_{i,j}:i,j\in[n]\}$ for $n\ge1$. A family consists of polynomials $p_n\in K[X_n]$. Matrix invariance means equality after every independent row and column permutation, defined without a circuit witness. A p-family has polynomially bounded degree (the variable count $n^2$ is already polynomial).
--
--   A formula has no parallel wires and each internal gate has at most one parent; input gates may be shared. A skew circuit has at most one internal incoming wire at each multiplication gate. On well-formed circuits these are the source's syntactic restrictions.
--
--   The classes $\mathrm{symVP},\mathrm{symVS},\mathrm{symVF}$ require invariant families and eventual polynomial orbit bounds, with the corresponding syntax. Their bounded-support-depth analogues satisfy
--   $$\mathrm{symVAC}^0=\bigcup_{\Delta\ge0}\mathrm{symVAC}^0_\Delta,\qquad \mathrm{symVAC}=\bigcup_{k\ge1}\mathrm{symVAC}^k.$$
--   Here level $\Delta$ bounds support depth by $\Delta$; positive level $k$ bounds it by $c(\log_2 n)^k$, with orbit size at most $n^c$ for one fixed $c$. These definitions use the published rigidification and support depth and impose no degree or total-size cap. Natural-number exponents are cofinal in the allowed polynomial bounds; index zero is unused. This shared interface prevents class equalities from being encoded into their definitions.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 2, 7–9 (PDF p. 5, 10–12), §§1.1, 2.1–2.5; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Rigidification

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement


/-- Matrix polynomial families, indexed at positive n; index zero is unused. §2.1–2.5. -/
abbrev Family (K : Type) [Field K] := (n : ℕ) → MvPolynomial (Fin n × Fin n) K

def invariant {K : Type} [Field K] {n : ℕ} (p : MvPolynomial (Fin n × Fin n) K) : Prop :=
  ∀ γ : Circuit.Gamma n, MvPolynomial.rename (fun ij => (γ.1 ij.1, γ.2 ij.2)) p = p

def invariantFamily {K : Type} [Field K] (p : Family K) : Prop :=
  ∀ n, 1 ≤ n → invariant (p n)

/-- Polynomial boundedness; finitely many initial values do not affect this condition. -/
def pBounded (d : ℕ → ℕ) : Prop := ∃ c N : ℕ, ∀ n, N ≤ n → d n ≤ n ^ c

def pFamily {K : Type} [Field K] (p : Family K) : Prop :=
  pBounded (fun n => (p n).totalDegree)

/-- §2.1: internal gates have at most one parent, inputs may be shared, no parallel wires.
For a well-formed circuit this is precisely the internal-tree formula condition. -/
def isFormula {K : Type} [Field K] {n : ℕ} {V : Type} [Fintype V]
    (C : Circuit K n V) : Prop :=
  (∀ g h, C.mult g h ≤ 1) ∧
  ∀ h, ¬ C.IsInput h → (∑ g, C.mult g h) ≤ 1

def isSkew {K : Type} [Field K] {n : ℕ} {V : Type} [Fintype V]
    (C : Circuit K n V) : Prop :=
  ∀ g, C.label g = .op .mul →
    (∑ h, if C.IsInput h then 0 else C.mult g h) ≤ 1

/-- Finite ordinal gate sets represent all finite circuits up to relabelling. -/
def hasCircuit {K : Type} [Field K] (n : ℕ) (p : MvPolynomial (Fin n × Fin n) K)
    (P : {V : Type} → [Fintype V] → Circuit K n V → Prop) : Prop :=
  ∃ m : ℕ, ∃ C : Circuit K n (Fin m), C.WellFormed ∧ C.MatrixSymmetric ∧ C.Computes p ∧ P C

def symVP (K : Type) [Field K] : Set (Family K) :=
  {p | invariantFamily p ∧ ∃ c N : ℕ, ∀ n, 1 ≤ n → N ≤ n →
    hasCircuit n (p n) (fun C => C.maxOrb ≤ n ^ c)}

def symVF (K : Type) [Field K] : Set (Family K) :=
  {p | invariantFamily p ∧ ∃ c N : ℕ, ∀ n, 1 ≤ n → N ≤ n →
    hasCircuit n (p n) (fun C => isFormula C ∧ C.maxOrb ≤ n ^ c)}

def symVS (K : Type) [Field K] : Set (Family K) :=
  {p | invariantFamily p ∧ ∃ c N : ℕ, ∀ n, 1 ≤ n → N ≤ n →
    hasCircuit n (p n) (fun C => isSkew C ∧ C.maxOrb ≤ n ^ c)}

def symVAC0Level (K : Type) [Field K] (Δ : ℕ) : Set (Family K) :=
  {p | invariantFamily p ∧ ∃ c N : ℕ, ∀ n, 1 ≤ n → N ≤ n →
    hasCircuit n (p n) (fun C => C.maxOrb ≤ n ^ c ∧ C.supportDepth ≤ Δ)}

def symVAC0 (K : Type) [Field K] : Set (Family K) := {p | ∃ Δ, p ∈ symVAC0Level K Δ}

/-- Definition 1.2, for k≥1; base two and integral c are cofinal choices of constants. -/
def symVACK (K : Type) [Field K] (k : ℕ) : Set (Family K) :=
  {p | invariantFamily p ∧ ∃ c N : ℕ, ∀ n, 1 ≤ n → N ≤ n →
    hasCircuit n (p n) (fun C => C.maxOrb ≤ n ^ c ∧
      (C.supportDepth : ℝ) ≤ c * (Real.logb 2 n) ^ k)}

def symVAC (K : Type) [Field K] : Set (Family K) := {p | ∃ k, 1 ≤ k ∧ p ∈ symVACK K k}

end SymmetricDepthHierarchy.ConstantDepth.Supplement


