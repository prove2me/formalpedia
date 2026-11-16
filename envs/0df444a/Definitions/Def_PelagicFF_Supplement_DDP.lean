-- Prove2me | Definitions.Def_PelagicFF_Supplement_DDP
-- name    : PelagicFF_Supplement_DDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:27:05.074418+00:00
-- url     : https://prove2.me/theorems/6c3570bd-dfa1-4345-9066-773323bc01c6
-- title:
--   The Directional Derivative Problem $\mathrm{DDP}_{n,d}$ (Problem 6.1)
-- statement:
--   For $f:\mathbb F_2^n\to\mathbb F_2$ and $a\in\mathbb F_2^n$, the **directional derivative** is $D_af(x)=f(x+a)+f(x)$. Let $V_{n,d}=P^0_{\le d}(\mathbb F_2^n)$ be the set of zero-constant-term multilinear polynomials of degree at most $d$,
--
--   $$
--   q(x)=\sum_{S\subseteq[n],\ 1\le|S|\le d} q_S\prod_{i\in S}x_i,\qquad q_S\in\mathbb F_2.
--   $$
--
--   In $\mathrm{DDP}_{n,d}$ Alice receives $q\in V_{n,d}$ and Bob receives a nonzero direction $a\in\mathbb F_2^n\setminus\{0\}$. After one message from Alice, Bob must output $(x,b)\in\mathbb F_2^n\times\mathbb F_2$ with
--
--   $$
--   b=D_aq(x)=q(x+a)+q(x).
--   $$
--
--   Equivalently, Bob outputs an edge $\{x,x+a\}$ of the perfect matching $M_a$ together with the parity of $q$ on its endpoints. This is the problem of Theorems 6.2 and 6.4.
--
--   **Formalization Note** A polynomial is its coefficient vector $(q_S)_{1\le|S|\le d}$. Distinct coefficient vectors give distinct functions, so the uniform law on coefficient vectors is the uniform law on $V_{n,d}$.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §6, p.42 (directional derivative, V_{n,d}); Problem 6.1, p.42

import Mathlib

namespace PelagicFF.Supplement

/-- The monomials `x_S = ∏_{i∈S} xᵢ` with `1 ≤ |S| ≤ d` (nonconstant, degree at most `d`). -/
abbrev Mono (n d : ℕ) : Type := {S : Finset (Fin n) // 1 ≤ S.card ∧ S.card ≤ d}

/-- `V_{n,d} = P⁰_{≤d}(F₂ⁿ)`: zero-constant-term multilinear polynomials `q : F₂ⁿ → F₂` of degree
at most `d`, as their coefficient vectors `(q_S)_{1 ≤ |S| ≤ d}`.
arXiv:2610.05585 (held version, sha256 4564aef3…), §6, p.42. -/
abbrev Vnd (n d : ℕ) : Type := Mono n d → ZMod 2

/-- The value `q(x) = ∑_S q_S ∏_{i∈S} xᵢ` of `q ∈ V_{n,d}` at `x ∈ F₂ⁿ`. -/
def polyEval {n d : ℕ} (q : Vnd n d) (x : Fin n → ZMod 2) : ZMod 2 :=
  ∑ S : Mono n d, q S * ∏ i ∈ S.1, x i

/-- Bob's inputs in `DDP_{n,d}`: nonzero directions `a ∈ F₂ⁿ \ {0}`. -/
abbrev Dir (n : ℕ) : Type := {a : Fin n → ZMod 2 // a ≠ 0}

/-- Bob's outputs in `DDP_{n,d}`: pairs `(x, b) ∈ F₂ⁿ × F₂`. -/
abbrev DDPOut (n : ℕ) : Type := (Fin n → ZMod 2) × ZMod 2

/-- **The Directional Derivative Problem `DDP_{n,d}` (Problem 6.1)** as a two-party search
relation: Alice holds `q ∈ V_{n,d}`, Bob holds `a ∈ F₂ⁿ \ {0}`, and `(x, b)` is correct exactly when
`b = D_a q(x) = q(x + a) + q(x)`.

arXiv:2610.05585 (held version, sha256 4564aef3…), §6, p.42: "For a function f : F₂ⁿ → F₂ and a
direction a ∈ F₂ⁿ, define the directional derivative of f in direction a by D_a f(x) = f(x+a)+f(x).
For integers n, d ≥ 1, let V_{n,d} := P⁰_{≤d}(F₂ⁿ) denote the set of zero-constant-term multilinear
polynomials q : F₂ⁿ → F₂ of degree at most d." Problem 6.1: "Alice receives a polynomial q ∈ V_{n,d},
and Bob receives a nonzero direction a ∈ F₂ⁿ \ {0}. After receiving a message from Alice, Bob must
output a pair (x, b) ∈ F₂ⁿ × F₂ such that b = D_a q(x)."

**Formalization Note.** Distinct coefficient vectors give distinct functions on `F₂ⁿ`
(multilinear representation), so the uniform law on `Vnd n d` is the uniform law on `V_{n,d}`. -/
def DDP (n d : ℕ) (q : Vnd n d) (a : Dir n) (o : DDPOut n) : Prop :=
  o.2 = polyEval q (o.1 + a.1) + polyEval q o.1

end PelagicFF.Supplement


