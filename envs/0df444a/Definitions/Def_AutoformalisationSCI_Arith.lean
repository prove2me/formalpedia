-- Prove2me | Definitions.Def_AutoformalisationSCI_Arith
-- name    : AutoformalisationSCI_Arith
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T14:38:15.124575+00:00
-- url     : https://prove2.me/theorems/b01661d0-87f3-43b4-8710-5d7fbefe3bd9
-- title:
--   Arithmetical hierarchy and many-one completeness
-- statement:
--   This file defines the **arithmetical hierarchy** for predicates on the natural numbers and the associated completeness notions, following the standard presentation (Soare, *Turing Computability*, Ch. 4).
--
--   For $n\in\mathbb N$ and a predicate $p$ on $\mathbb N$:
--   - $\Sigma^0_0$ is the class of **computable** (decidable) predicates.
--   - $\Sigma^0_{n+1}$ consists of the predicates obtained by projecting a $\Pi^0_n$ predicate along one extra natural-number coordinate: $p\in\Sigma^0_{n+1}$ iff there is a predicate $q$ with $\neg q\in\Sigma^0_n$ and $p(a)\iff\exists b,\,q(\langle a,b\rangle)$, where $\langle a,b\rangle$ is a fixed computable pairing of $\mathbb N^2$ with $\mathbb N$.
--   - $\Pi^0_n$ is the class of complements of $\Sigma^0_n$ predicates, and $\Delta^0_n=\Sigma^0_n\cap\Pi^0_n$.
--
--   A set $A\subseteq\mathbb N$ is **$\Sigma^0_n$-complete** if $A\in\Sigma^0_n$ and every $\Sigma^0_n$ set $C$ is many-one reducible to $A$ (a total computable $f$ with $a\in C\iff f(a)\in A$); **$\Pi^0_n$-complete** is defined analogously. These are the completeness notions used in Theorems A.3 and A.4.
--
--   **Formalization Note.** Many-one reducibility is Mathlib's `ManyOneReducible` (`≤₀`). The extra quantified variable is encoded with `Nat.pair`, a computable bijection $\mathbb N^2\to\mathbb N$, so the classes are the usual arithmetical classes.
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), Appendix A (pp. 17–23); https://arxiv.org/abs/2610.08144. Standard background: R. I. Soare, Turing Computability, Springer 2016, Ch. 4.

import Mathlib.Computability.RE
import Mathlib.Computability.Reduce

open Encodable

namespace AutoformalisationSCI

def ArithSigma : ℕ → (ℕ → Prop) → Prop
  | 0, p => ComputablePred p
  | n + 1, p => ∃ q : ℕ → Prop, ArithSigma n (fun a => ¬ q a) ∧ ∀ a, p a ↔ ∃ b, q (Nat.pair a b)

def ArithPi (n : ℕ) (p : ℕ → Prop) : Prop := ArithSigma n (fun a => ¬ p a)

def ArithDelta (n : ℕ) (p : ℕ → Prop) : Prop := ArithSigma n p ∧ ArithPi n p

def SigmaComplete (n : ℕ) (A : Set ℕ) : Prop :=
  ArithSigma n (fun a => a ∈ A) ∧
    ∀ C : Set ℕ, ArithSigma n (fun a => a ∈ C) → (fun a => a ∈ C) ≤₀ (fun a => a ∈ A)

def PiComplete (n : ℕ) (A : Set ℕ) : Prop :=
  ArithPi n (fun a => a ∈ A) ∧
    ∀ C : Set ℕ, ArithPi n (fun a => a ∈ C) → (fun a => a ∈ C) ≤₀ (fun a => a ∈ A)

end AutoformalisationSCI


