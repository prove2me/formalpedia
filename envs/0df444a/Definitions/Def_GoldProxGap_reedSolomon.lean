-- Prove2me | Definitions.Def_GoldProxGap_reedSolomon
-- name    : GoldProxGap_reedSolomon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:46.904387+00:00
-- url     : https://prove2.me/theorems/934b0ca1-3a40-4b7d-86dd-49d8e04e5bdf
-- title:
--   Reed–Solomon codes $C_K(D;\mathbb F)$, agreement $\mathrm{agr}_K$, common agreement $\mathrm{CA}_K$, exceptional challenges $\mathrm{Bad}_T$ and decoding lists $\mathcal L_T$
-- statement:
--   Let $\mathbb F$ be a finite field and $D\subseteq\mathbb F$ a finite set of $N$ points. For a message length $K$, the **Reed–Solomon code** on $D$ is
--   $$
--   C_K(D;\mathbb F)=\{(P(x))_{x\in D}: P\in\mathbb F[X],\ \deg P<K\}.
--   $$
--   A **received word** is any function $f:D\to\mathbb F$. Its **individual agreement** and the **common agreement** of two words $f,g$ are
--   $$
--   \mathrm{agr}_K(f)=\max_{\deg P<K}|\{x\in D: f(x)=P(x)\}|,\qquad
--   \mathrm{CA}_K(f,g)=\max_{\deg P,\deg Q<K}|\{x\in D: f(x)=P(x),\ g(x)=Q(x)\}|.
--   $$
--   For a threshold $T$, the **exceptional challenges** of the received line $\{f+zg\}$ are $\mathrm{Bad}_T(f,g)=\{z\in\mathbb F:\mathrm{agr}_K(f+zg)\ge T\}$, and the **decoding list** of $f$ is $\mathcal L_T(f)=\{c\in C_K(D;\mathbb F): |\{x\in D: f(x)=c(x)\}|\ge T\}$.
--
--   These are the objects every statement of the mission is about: a proximity-gap counterexample is a pair $(f,g)$ with small $\mathrm{CA}_K(f,g)$ and a large set $\mathrm{Bad}_T(f,g)$ at a threshold $T>\mathrm{CA}_K(f,g)$.
--
--   **Formalization Note** The domain is a `Finset` of the field and words are functions on it. Maxima are taken over the finite set of codewords (pairs of codewords); the zero word is always a codeword, so the maximum is over a nonempty set, and maximizing over codewords is the same as maximizing over polynomials of degree $<K$. Degrees are in `WithBot ℕ`, so the zero polynomial has degree $<K$ for every $K$. `polyAgree f P` counts the points of $D$ where $f$ agrees with a polynomial $P$ (used for witnesses, Definition 3.4).
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), §3.1, Definitions 3.1–3.4, pp.17–18

import Mathlib

open Polynomial

open scoped Classical

namespace GoldProxGap

/-!
# Reed–Solomon codes, agreement, exceptional challenges and decoding lists

Dao, Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary
Fields*, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), §3.1,
Definitions 3.1–3.4, pp.17–18.

**Formalization Note.**
* The domain is a finite set `D : Finset F` of field elements; a received word is any function
  `f : D → F` (Definition 3.1).
* A codeword of message length `K` is the evaluation `x ↦ P(x)` on `D` of a polynomial with
  `degree P < K` (degrees in `WithBot ℕ`, so `P = 0` is allowed for every `K`).
* `agr D K f` and `CA D K f g` are maxima over the finite set of codewords (pairs of codewords),
  computed as `Finset.sup`; the code always contains the zero word, so the maximum is over a
  nonempty set. Maximizing over codewords is the same as maximizing over polynomials of degree
  `< K`, since every such polynomial gives a codeword.
* `Bad D K T f g` is the finite set of challenges `z ∈ F` with `agr_K(f + z g) ≥ T`.
* `decodingList D K T f` is the set of codewords (functions `D → F`) agreeing with `f` on at least
  `T` points, so its cardinality is the list size `|L_T(f)|`.
* `polyAgree f P` counts the points of `D` where `f` agrees with the polynomial `P`; an explaining
  polynomial of degree `< K` on at least `T` coordinates is a witness (Definition 3.4).
* The field is finite throughout (the paper's standing assumption, §3.1: "All fields in this
  paper are finite").
-/

variable {F : Type*} [Field F]

/-- Definition 3.1: the Reed–Solomon code `C_K(D; F)`, the set of words `D → F` that are the
evaluation of some polynomial `P ∈ F[X]` with `deg P < K`. -/
def reedSolomon (D : Finset F) (K : ℕ) : Set (D → F) :=
  {c | ∃ P : F[X], P.degree < (K : WithBot ℕ) ∧ ∀ x : D, c x = P.eval (x : F)}

/-- The codewords of `C_K(D; F)` as a finite set (the field is finite). -/
noncomputable def codewords [Fintype F] (D : Finset F) (K : ℕ) : Finset (D → F) :=
  Finset.univ.filter (fun c => c ∈ reedSolomon D K)

/-- `|{x ∈ D : f(x) = c(x)}|`, the number of agreements of two words. -/
noncomputable def agreeCount {D : Finset F} (f c : D → F) : ℕ :=
  (Finset.univ.filter (fun x : D => f x = c x)).card

/-- `|{x ∈ D : f(x) = P(x)}|`, the number of points where a word agrees with a polynomial. -/
noncomputable def polyAgree {D : Finset F} (f : D → F) (P : F[X]) : ℕ :=
  (Finset.univ.filter (fun x : D => f x = P.eval (x : F))).card

/-- Definition 3.2: the individual agreement `agr_K(f) = max_{deg P < K} |{x ∈ D : f(x) = P(x)}|`. -/
noncomputable def agr [Fintype F] (D : Finset F) (K : ℕ) (f : D → F) : ℕ :=
  (codewords D K).sup (fun c => agreeCount f c)

/-- Definition 3.2: the common agreement
`CA_K(f, g) = max_{deg P, deg Q < K} |{x ∈ D : f(x) = P(x), g(x) = Q(x)}|`. -/
noncomputable def CA [Fintype F] (D : Finset F) (K : ℕ) (f g : D → F) : ℕ :=
  (codewords D K ×ˢ codewords D K).sup
    (fun p => (Finset.univ.filter (fun x : D => f x = p.1 x ∧ g x = p.2 x)).card)

/-- Definition 3.3: the exceptional challenges `Bad_T(f, g) = {z ∈ F : agr_K(f + z g) ≥ T}`. -/
noncomputable def Bad [Fintype F] (D : Finset F) (K T : ℕ) (f g : D → F) : Finset F :=
  Finset.univ.filter (fun z : F => T ≤ agr D K (f + z • g))

/-- Definition 3.4: the decoding list
`L_T(f) = {c ∈ C_K(D; F) : |{x ∈ D : f(x) = c(x)}| ≥ T}`, as a finite set of codewords. -/
noncomputable def decodingList [Fintype F] (D : Finset F) (K T : ℕ) (f : D → F) : Finset (D → F) :=
  (codewords D K).filter (fun c => T ≤ agreeCount f c)

end GoldProxGap


