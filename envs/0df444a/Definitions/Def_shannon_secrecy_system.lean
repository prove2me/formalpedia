-- Prove2me | Definitions.Def_shannon_secrecy_system
-- name    : shannon_secrecy_system
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-22T18:29:50.951183+00:00
-- url     : https://prove2.me/theorems/82a0753c-f2ba-45ac-b23f-cd6dd099b1ff
-- title:
--   Finite secrecy systems, perfect secrecy, and the cyclic system of Fig. 5
-- statement:
--   This file fixes the model of a **finite secrecy system** used throughout the mission, following Shannon's *Communication Theory of Secrecy Systems* (1949), §2 and §10.
--
--   A secrecy system consists of three finite sets: the messages $M$, the keys $K$ and the cryptograms $E$. Enciphering is a family of maps $T_k : M \to E$, one for each key $k$, and each $T_k$ is required to be **non-singular** (injective), so that a receiver who knows the key recovers the message uniquely. Each key carries an a priori probability $P(k) \ge 0$ with $\sum_{k} P(k) = 1$; these are the enemy cryptanalyst's a priori probabilities for the key choice.
--
--   An a priori message distribution is any $p : M \to \mathbb{R}$ with $p(m) \ge 0$ and $\sum_m p(m) = 1$. The message and the key are chosen independently. From these data the file defines the four quantities Shannon uses on p. 680:
--
--   1. $P_M(E) = \sum_{k \,:\, T_k M = E} P(k)$, the probability of the cryptogram $E$ given that the message $M$ was chosen — the total probability of all keys carrying $M$ to $E$;
--   2. $P(E) = \sum_{M} \sum_{k \,:\, T_k M = E} p(M) P(k)$, the probability of obtaining the cryptogram $E$ from any cause;
--   3. $P_E(M) = \dfrac{\sum_{k \,:\, T_k M = E} p(M) P(k)}{P(E)}$, the a posteriori probability of the message $M$ once $E$ has been intercepted;
--   4. **perfect secrecy**: for *every* a priori message distribution $p$ and every cryptogram $E$ of positive probability, $P_E(M) = p(M)$ for all $M$. Quantifying over all $p$ is how Shannon's clause "independently of the values of $P(M)$" is rendered.
--
--   The file also defines the Shannon entropy $H(p) = -\sum_a p(a)\log p(a)$ of a finite distribution, and the cyclic system of Fig. 5 on p. 681: messages, keys and cryptograms are the residues modulo $n$, key $i$ sends message $j$ to the cryptogram $i + j \pmod n$, and the $n$ keys are equally likely.
--
--   **Formalization Note** Probabilities are plain real numbers together with explicit non-negativity and normalization hypotheses, rather than `PMF`, so that sums stay finite `Finset` sums. $P_E(M)$ is a quotient of real numbers, so it evaluates to $0$ by Lean's convention when $P(E) = 0$; every statement about it therefore carries the hypothesis $P(E) \neq 0$, exactly the cryptograms that can occur. Entropy is taken with the natural logarithm ($\log$ in nats) via `Real.negMulLog`; Shannon leaves the base unspecified, and a change of base only rescales every entropy by the same positive constant.
-- source:
--   C. E. Shannon, "Communication Theory of Secrecy Systems", Bell System Technical Journal 28(4):656-715, 1949; https://doi.org/10.1002/j.1538-7305.1949.tb00928.x, pp. 656-660 (Part I, §2) and pp. 679-682 (Part II, §10)

import Mathlib

namespace ShannonSecrecy

open Finset

/-- A finite probability distribution on a finite type. -/
def IsPMF {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a : α, 0 ≤ p a) ∧ ∑ a : α, p a = 1

/-- A finite secrecy system in the sense of Shannon (1949), §2 and §10:
finitely many messages `M`, keys `K` and cryptograms `E`; enciphering with key `k`
is the map `m ↦ encipher k m`, which is non-singular (injective), so that unique
deciphering is possible when the key is known; every key carries an a priori
probability. -/
structure Cipher (M K E : Type*) [Fintype M] [Fintype K] [Fintype E] [DecidableEq E] where
  /-- `encipher k m` is the cryptogram obtained from the message `m` with the key `k`. -/
  encipher : K → M → E
  /-- Enciphering with a fixed key is non-singular, so deciphering is unique. -/
  encipher_injective : ∀ k : K, Function.Injective (encipher k)
  /-- The a priori probability of each key. -/
  keyProb : K → ℝ
  keyProb_nonneg : ∀ k : K, 0 ≤ keyProb k
  keyProb_sum : ∑ k : K, keyProb k = 1

variable {M K E : Type*} [Fintype M] [Fintype K] [Fintype E] [DecidableEq E]

/-- `P_M(E)`: the conditional probability of the cryptogram `e` given that the message
`m` was chosen, i.e. the total probability of all keys that transform `m` into `e`. -/
def msgToCrypto (C : Cipher M K E) (m : M) (e : E) : ℝ :=
  ∑ k : K, if C.encipher k m = e then C.keyProb k else 0

/-- `P(E)`: the probability of obtaining the cryptogram `e` from any cause, when the
a priori message distribution is `p` and the key is chosen independently. -/
def cryptoProb (C : Cipher M K E) (p : M → ℝ) (e : E) : ℝ :=
  ∑ m : M, ∑ k : K, if C.encipher k m = e then p m * C.keyProb k else 0

/-- `P_E(M)`: the a posteriori probability of the message `m` after the cryptogram `e`
has been intercepted, i.e. the joint probability of `(m, e)` divided by the probability
of `e`. -/
noncomputable def postProb (C : Cipher M K E) (p : M → ℝ) (e : E) (m : M) : ℝ :=
  (∑ k : K, if C.encipher k m = e then p m * C.keyProb k else 0) / cryptoProb C p e

/-- Perfect secrecy (Shannon 1949, §10): for every a priori message distribution, and
for every cryptogram that can actually occur, the a posteriori probability of each
message equals its a priori probability. Quantifying over all a priori distributions
renders Shannon's requirement that the equality hold "independently of the values of
`P(M)`". -/
def PerfectSecrecy (C : Cipher M K E) : Prop :=
  ∀ p : M → ℝ, IsPMF p → ∀ e : E, cryptoProb C p e ≠ 0 → ∀ m : M, postProb C p e m = p m

/-- Shannon entropy `H = -∑ p log p` of a finite distribution, in nats. -/
noncomputable def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a : α, Real.negMulLog (p a)

/-- The cyclic system of Shannon (1949), §10, Fig. 5: messages, keys and cryptograms are
the residues mod `n`, the key `i` sends the message `j` to the cryptogram `i + j (mod n)`,
and all `n` keys are equally likely. -/
noncomputable def cyclicCipher (n : ℕ) [NeZero n] : Cipher (ZMod n) (ZMod n) (ZMod n) where
  encipher k m := k + m
  encipher_injective k := fun _ _ h => by simpa using h
  keyProb _ := (n : ℝ)⁻¹
  keyProb_nonneg _ := by positivity
  keyProb_sum := by
    have hn : (Fintype.card (ZMod n) : ℝ) = (n : ℝ) := by
      simp [ZMod.card]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hn]
    field_simp

end ShannonSecrecy


