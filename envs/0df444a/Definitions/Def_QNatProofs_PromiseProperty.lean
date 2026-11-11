-- Prove2me | Definitions.Def_QNatProofs_PromiseProperty
-- name    : QNatProofs_PromiseProperty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:43.19522+00:00
-- url     : https://prove2.me/theorems/7b0765da-08e1-4d9a-ba78-272942ab7e07
-- title:
--   Promise properties of quantum states: natural properties and usefulness against $\mathcal C_{\mathrm{poly}}$
-- statement:
--   A **promise property** assigns to every $n$ two sets $P^{\mathrm{yes}}_n, P^{\mathrm{no}}_n$ of $n$-qubit vectors.
--
--   It is **natural** (Definition 2.2) if for every $n$ the two sets are disjoint subsets of the unit sphere $S(\mathbb C^{2^n})$, both invariant under every global phase $u$, $|u|=1$, and:
--
--   1. *Constructivity:* there are a polynomial-time deterministic classical algorithm $F$ and a polynomial $\tau$ such that for every $T\ge\tau(n)$,
--   $$|\psi\rangle\in P^{\mathrm{yes}}_n\Rightarrow F(1^n,\mathrm{al}_T(\psi))=1,\qquad |\psi\rangle\in P^{\mathrm{no}}_n\Rightarrow F(1^n,\mathrm{al}_T(\psi))=0,$$
--   with running time measured in the total input length; and $P^{\mathrm{yes}}_n$ is Haar-measurable.
--   2. *Largeness:* there is $c>0$ such that for all sufficiently large $n$, $\Pr_{\phi\sim\mathrm{Haar}_n}[\phi\in P^{\mathrm{yes}}_n]\ge 2^{-cn}$.
--
--   For a circuit class $\mathcal C$ and $\varepsilon:\mathbb N\to\mathbb R$, the property is **$\varepsilon$-useful against $\mathcal C_{\mathrm{poly}}$** if for every family of pure states $(|\psi_n\rangle)_n$: whenever there are a polynomial $q$ and, for every $n$, a circuit $C_n\in\mathcal C$ of size at most $q(n)$ whose reduced output state $\sigma_n$ satisfies $\tfrac12\||\psi_n\rangle\langle\psi_n|-\sigma_n\|_1\le\varepsilon(n)$, then $|\psi_n\rangle\in P^{\mathrm{no}}_n$ for all sufficiently large $n$.
--
--   These are the quantum analogues of Razborov–Rudich natural properties: a natural useful property would be a "natural proof" of state-preparation lower bounds against $\mathcal C$.
--
--   **Formalization Note** $F$ is a polynomial-time computable function on bit strings (`PolyTimeComputable`, Mathlib's multi-stack Turing machines); its input $(1^n,s)$ is the string $1^n0\,s$ and its outputs are `[true]`, `[false]`. Haar-measurability is measurability for the completion of $\mathrm{Haar}_n$. A circuit for $\psi_n$ may use any number of further wires, which start in $|0\rangle$ and are traced out; its size is its number of gates.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 2.2, p.9; C_poly, p.8

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QNatProofs_haar
import Definitions.Def_QNatProofs_al
import Definitions.Def_QNatProofs_reducedOutput

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms QAlgorithms.Complexity MeasureTheory Filter Polynomial

/-- A **promise property** of quantum states: for every `n` a pair of sets `P^yes_n, P^no_n` of
`n`-qubit state vectors (Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…),
Definition 2.2, p.9). The conditions of the definition (disjoint subsets of the unit sphere,
invariant under global phase) are part of `IsNatural`. -/
structure PromiseProperty where
  /-- The YES-states `P^yes_n`. -/
  yes : (n : ℕ) → Set (EuclideanSpace ℂ (Qubits n))
  /-- The NO-states `P^no_n`. -/
  no : (n : ℕ) → Set (EuclideanSpace ℂ (Qubits n))

/-- **Natural promise property** (Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…),
Definition 2.2, p.9): for every `n`, `P^yes_n` and `P^no_n` are disjoint subsets of the unit
sphere `S(ℂ^{2ⁿ})`, both invariant under global phase, and

1. *Constructivity*: there are a polynomial-time deterministic classical algorithm `F` and a
   polynomial `τ` such that for every `T ≥ τ(n)`, `ψ ∈ P^yes_n ⇒ F(1ⁿ, al_T(ψ)) = 1` and
   `ψ ∈ P^no_n ⇒ F(1ⁿ, al_T(ψ)) = 0` (running time in the total input length), and `P^yes_n` is
   Haar-measurable;
2. *Largeness*: there is a constant `c > 0` such that for all sufficiently large `n`,
   `Pr_{ϕ∼Haar_n}[ϕ ∈ P^yes_n] ≥ 2^{-cn}`.

**Formalization Note** `F` is a polynomial-time computable function on bit strings (Mathlib's
multi-stack Turing machines, `PolyTimeComputable`); its input `(1ⁿ, s)` is the string `1ⁿ0 s`
and the outputs `1`, `0` are the strings `[true]`, `[false]`. "Haar-measurable" is measurability
for the completion of `Haar_n` (`NullMeasurableSet`), so that every Borel set and every set
differing from one by a Haar-null set qualifies. -/
def PromiseProperty.IsNatural (P : PromiseProperty) : Prop :=
  (∀ n, Disjoint (P.yes n) (P.no n)) ∧
  (∀ n, P.yes n ⊆ Metric.sphere 0 1 ∧ P.no n ⊆ Metric.sphere 0 1) ∧
  (∀ n (u : ℂ), ‖u‖ = 1 → ∀ ψ : EuclideanSpace ℂ (Qubits n), (ψ ∈ P.yes n → u • ψ ∈ P.yes n) ∧ (ψ ∈ P.no n → u • ψ ∈ P.no n)) ∧
  (∀ n, NullMeasurableSet (((↑) : sphere n → EuclideanSpace ℂ (Qubits n)) ⁻¹' P.yes n) (haar n)) ∧
  (∃ F : Str → Str, PolyTimeComputable F ∧ ∃ τ : ℕ[X], ∀ n T : ℕ, τ.eval n ≤ T →
      (∀ ψ ∈ P.yes n, F (encNat n ++ al T ψ) = [true]) ∧
      (∀ ψ ∈ P.no n, F (encNat n ++ al T ψ) = [false])) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal ((2 : ℝ) ^ (-(c * (n : ℝ)))) ≤
        haar n (((↑) : sphere n → EuclideanSpace ℂ (Qubits n)) ⁻¹' P.yes n))

/-- **Usefulness against the polynomial-size restriction `C_poly` of a circuit class `C`** (Li,
Parham, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 2.2 item 3 and the definition of
`C_poly`, p.8–9): for every family of pure states `(ψ_n)_n`, if there are a polynomial `q` and for
every `n` a circuit `C_n ∈ C` of size at most `q(n)` whose reduced state `σ_n` on its output
register satisfies `½‖|ψ_n⟩⟨ψ_n| − σ_n‖₁ ≤ ε(n)`, then `ψ_n ∈ P^no_n` for all sufficiently large
`n`.

**Formalization Note** A circuit for `ψ_n` may use any number `w` of further wires, which start
in `|0⟩` and are traced out; its size is its number of gates. The error `ε` is any real
function. -/
def PromiseProperty.IsUseful {S : Set Gate} (P : PromiseProperty) (C : CircuitClass S)
    (ε : ℕ → ℝ) : Prop :=
  ∀ ψ : (n : ℕ) → sphere n,
    (∃ q : ℕ[X], ∀ n, ∃ (w : ℕ) (c : Circuit S (n + w)), c ∈ C (n + w) ∧
        c.size ≤ q.eval n ∧ ApproxPrepares c (ψ n : EuclideanSpace ℂ (Qubits n)) (ε n)) →
    ∀ᶠ n in atTop, (ψ n : EuclideanSpace ℂ (Qubits n)) ∈ P.no n

end QNatProofs


