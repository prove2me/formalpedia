-- Prove2me | Definitions.Def_WitnessIsolation_AffineCollapse_model
-- name    : WitnessIsolation_AffineCollapse_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:55.186828+00:00
-- url     : https://prove2.me/theorems/2c77367b-1c29-40fc-86aa-5fa3f6ca06d2
-- title:
--   Pruning families, affine guarantees, SAT complexity, and the collapse
-- statement:
--   For a binary language L, membership in P/poly means that there are fixed natural numbers c,k such that at every length n some Boolean circuit with at most c(n+2)^k gates decides L on all n-bit inputs. Write NPCollapse for the assertion that every language with a uniform polynomial-time binary checking relation and polynomially bounded binary certificates has this property.
--
--   For caps s,v, let S(s,v) be the least gate count of a circuit deciding satisfiability of padded descriptions of actual length at most s and with at most v declared witness variables. Malformed encodings and descriptions over the variable cap are rejected. A promise separator instead need only accept uniquely satisfiable inputs and reject unsatisfiable ones; its answers on other inputs are unrestricted.
--
--   A pruning family I has an implementing multi-output circuit at every description length L. A fixed polynomial bounds the actual gate count, random-tape length, output length, and full serialized implementing circuit length. The latter charges hardwired nonuniform advice. Its operational contract requires a well-formed output on the same ordered variables and
--
--   $$\operatorname{Sol}(I(H;\rho))\subseteq\operatorname{Sol}(H)$$
--
--   for every well-formed H and every tape. The affine promise means exactly that the solution set is b+V for a vector b and a linear subspace V over F₂. A guarantee from n₀ requires
--
--   $$\Pr_\rho[|\operatorname{Sol}(I(H;\rho))|=1]\ge p(n)$$
--
--   for every n≥n₀ and every description length L with this promise. The tape is uniform over all binary vectors of its declared length. No affine basis enters the circuit's input.
--
--   These definitions express the hypothesis and conclusion of Theorem 1.1 independently. Verifier compilation and the relationship between S and NP are theorem work. The exact goal scale is 2^{-C(log₂ log₂(n+4))^a} for real a,C.
--
--   **Formalization Note** S takes values in extended naturals, avoiding a false zero on an empty decider set. Equation (2.2) separately asserts finite attainment, including caps outside 1≤v≤s. NP uses the P and checking-language definitions of CookPvsNP_defs: actual uniform finite-alphabet deterministic Turing machines decide binary checking relations. Both language inputs and certificates here are binary strings, with an existential uniform bound c(n+2)^k on certificate length. Hardwired advice is part of the implementing circuit description, not an input-dependent oracle.
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), Definition 2.1, §2 and Theorem 1.1; printed pp. 2, 6–7, PDF pp. 3, 7–8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/346.pdf; PDF SHA256 969057d4c1837a5ebf1d45c70a14c1d66f0d76610c6233f151e2402e7611f42e

import Definitions.Def_WitnessIsolation_AffineCollapse_circuits
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse

/-- Ordinary nonuniform polynomial-size Boolean circuits for a language. -/
def InPpoly (L : Set (List Bool)) : Prop :=
  ∃ c k : ℕ, ∀ n : ℕ, ∃ C : Circuit n 1,
    C.size ≤ c*(n+2)^k ∧ ∀ x : Bits n, C.accepts x ↔ List.ofFn x ∈ L

/-- Standard NP via one uniform deterministic polynomial-time checking relation
and polynomially bounded binary certificates. The published P definition uses actual TMs. -/
def InNP (L : Set (List Bool)) : Prop :=
  ∃ (R : List Bool → List Bool → Prop) (c k : ℕ),
    CookPvsNP.checkLang R ∈ CookPvsNP.P (Option (Bool ⊕ Bool)) ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ w : List Bool, w.length ≤ c*(x.length+2)^k ∧ R x w

def NPCollapse : Prop := ∀ L : Set (List Bool), InNP L → InPpoly L

/-- Exact SAT predicate on padded strings, including rejection over either cap. -/
def CappedSAT (s v : ℕ) (x : Bits (paddedWidth s)) : Prop :=
  ∃ d, decodedPadded s x = some d ∧ d.inputs ≤ v ∧ d.sol.Nonempty

def DecidesSAT (s v : ℕ) (C : Circuit (paddedWidth s) 1) : Prop :=
  ∀ x, C.accepts x ↔ CappedSAT s v x

/-- The actual least gate count, with infinity if there were no decider.
For every finite cap a truth-table circuit exists; that fact is proof work. -/
def satComplexity (s v : ℕ) : ℕ∞ :=
  ⨅ C : {C : Circuit (paddedWidth s) 1 // DecidesSAT s v C}, (C.val.size : ℕ∞)

def SeparatesUnique (s v : ℕ) (C : Circuit (paddedWidth s) 1) : Prop :=
  ∀ x d, decodedPadded s x = some d → d.inputs ≤ v →
    (d.sol.card = 1 → C.accepts x) ∧ (d.sol.card = 0 → ¬C.accepts x)

/-- The F₂ affine promise is a property, and supplies the pruner with no data. -/
def Description.Affine (d : Description) : Prop :=
  ∃ b : Fin d.inputs → ZMod 2, ∃ V : Submodule (ZMod 2) (Fin d.inputs → ZMod 2),
    ∀ x : Fin d.inputs → ZMod 2,
      d.eval (fun i => decide (x i = 1)) = true ↔ x-b ∈ V

/-- Data of a randomized, nonuniform, multi-output circuit family.
Advice is incorporated in the length-specific circuit; no uniform generator is required. -/
structure PruningFamily where
  randomLength : ℕ → ℕ
  outputLength : ℕ → ℕ
  implementation : (L : ℕ) → Circuit (L + randomLength L) (outputLength L)

def PruningFamily.run (I : PruningFamily) (L : ℕ) (h : Bits L)
    (r : Bits (I.randomLength L)) : List Bool :=
  List.ofFn ((I.implementation L).eval (concatBits h r))

/-- Polynomial bounds apply to actual syntax and all length-specific resources. -/
def PruningFamily.Polynomial (I : PruningFamily) : Prop :=
  ∃ c k : ℕ, ∀ L,
    (I.implementation L).size ≤ c*(L+2)^k ∧
    I.randomLength L ≤ c*(L+2)^k ∧ I.outputLength L ≤ c*(L+2)^k ∧
    (I.implementation L).encode.length ≤ c*(L+2)^k

/-- Every well-formed input is pruned, on every tape, without any affine promise. -/
def PruningFamily.Prunes (I : PruningFamily) : Prop :=
  ∀ L (h : Bits L) d, decode (List.ofFn h) = some d →
    ∀ r : Bits (I.randomLength L), ∃ e,
      decode (I.run L h r) = some e ∧ e.inputs = d.inputs ∧
      ∀ x : List Bool, x.length = d.inputs →
        e.eval (word x e.inputs) = true → d.eval (word x d.inputs) = true

def IsPruner (I : PruningFamily) : Prop := I.Polynomial ∧ I.Prunes

/-- Uniform finite-tape probability is a real ratio, with a positive denominator even at zero bits. -/
def uniformProb {n : ℕ} (E : Bits n → Prop) : ℝ := by
  classical
  exact (Finset.univ.filter (fun x => E x)).card / (2:ℝ)^n

/-- One witness threshold applies at every description length. -/
def GuaranteeFrom (I : PruningFamily) (p : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  ∀ L (h : Bits L) d, decode (List.ofFn h) = some d → n₀ ≤ d.inputs →
    d.Affine → uniformProb (fun r : Bits (I.randomLength L) =>
      ∃ e, decode (I.run L h r) = some e ∧ e.sol.card = 1) ≥ p d.inputs

def HasGuarantee (I : PruningFamily) (p : ℕ → ℝ) : Prop :=
  ∃ n₀, GuaranteeFrom I p n₀

def isolationScale (a C : ℝ) (n : ℕ) : ℝ :=
  (2:ℝ) ^ (-C * (Real.logb 2 (Real.logb 2 ((n:ℝ)+4))) ^ a)

end WitnessIsolation.AffineCollapse


