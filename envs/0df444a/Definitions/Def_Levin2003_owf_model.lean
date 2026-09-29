-- Prove2me | Definitions.Def_Levin2003_owf_model
-- name    : Levin2003_owf_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T21:52:11.889137+00:00
-- url     : https://prove2.me/theorems/fa876789-da2f-4a14-904f-1caaaea822e0
-- title:
--   One-way functions on bit strings
-- statement:
--   The model in which Levin's one-way functions are stated. Instances are finite bit strings. A function $f$ on bit strings is *length-preserving* if $|f(w)| = |w|$ for every $w$, and *polynomial-time computable* if some multi-tape Turing machine outputs $f(w)$ within $p(|w|)$ steps for a fixed polynomial $p$.
--
--   An inverter is a function $A$ that is handed the instance $f(w)$ followed by a string $r$ of random coins and outputs a candidate preimage. Its success probability at input length $n$ with $m$ coins is
--
--   $$\mathrm{succ}_{f,A}(n,m) = \frac{\#\{(w,r) \in \{0,1\}^n \times \{0,1\}^m : f(A(f(w)\,\Vert\,r)) = f(w)\}}{2^{\,n+m}},$$
--
--   the fraction of pairs on which $A$ returns *some* preimage of $f(w)$.
--
--   $f$ is a **one-way function** when it is polynomial-time computable, length-preserving, and for every polynomial-time computable inverter $A$, every coin budget $n^{c}$ and every $k$, there is an $N$ with $\mathrm{succ}_{f,A}(n, n^{c}) < n^{-k}$ for all $n \ge N$.
--
--   This is the standard asymptotic strong form of one-wayness for length-preserving functions, as discussed in Section 4.2 of the paper ('the simplest one is to define owfs as hard on average problems of inverting length-preserving functions'). It does not reproduce the paper's own apparatus of Las Vegas algorithms in $L$ (Definition 1), multimedian time (Definition 2) or security (Section 4.1).
-- source:
--   L. A. Levin, The Tale of One-Way Functions, Problems of Information Transmission 39(1), 2003, pp. 92-103 (translated from Problemy Peredachi Informatsii, No. 1, 2003, pp. 103-117); preprint https://arxiv.org/abs/cs/0012023, Sections 3.1-4.2 (definition of owf discussed on p. 100)

import Mathlib

/-!
# Levin 2003, "The Tale of One-Way Functions" — basic model

Core notions used by the mission: bit strings, polynomial-time computability
(via Mathlib's two-tape Turing machine model), length preservation, the
inversion success probability of a probabilistic inverter, and the resulting
notion of a (strong) one-way function on length-preserving functions, as in
Section 4.2 of the paper.
-/

namespace Levin2003

/-- Finite bit strings. -/
abbrev Bits := List Bool

/-- `f` is computable in polynomial time by a multi-tape Turing machine,
bit strings being written on the tape symbol by symbol. -/
def PolyTimeComputable (f : Bits → Bits) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : Bits → List Bool) (id : Bits → List Bool) f)

/-- `f` preserves the length of its argument. -/
def LengthPreserving (f : Bits → Bits) : Prop :=
  ∀ w : Bits, (f w).length = w.length

/-- The set of all bit strings of length `n`. -/
def cube (n : ℕ) : Finset Bits :=
  Finset.image (fun v : Fin n → Bool => List.ofFn v) Finset.univ

/-- The number of pairs `(w, r)` with `w` of length `n` and `r` of length `m`
for which the inverter `A`, run on the instance `f w` together with the random
string `r`, returns a preimage of `f w` under `f`. -/
def invSuccessCount (f A : Bits → Bits) (n m : ℕ) : ℕ :=
  ((cube n ×ˢ cube m).filter (fun p => f (A (f p.1 ++ p.2)) = f p.1)).card

/-- The probability that `A` inverts `f` on a uniformly random instance `f w`,
`w` of length `n`, using `m` uniformly random coins. -/
def invSuccessProb (f A : Bits → Bits) (n m : ℕ) : ℚ :=
  (invSuccessCount f A n m : ℚ) / (2 : ℚ) ^ (n + m)

/-- A (strong) one-way function: a length-preserving, polynomial-time computable
function that every polynomial-time probabilistic inverter inverts with
negligible probability on uniformly random inputs. -/
def OneWay (f : Bits → Bits) : Prop :=
  PolyTimeComputable f ∧ LengthPreserving f ∧
    ∀ A : Bits → Bits, PolyTimeComputable A → ∀ c k : ℕ,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → invSuccessProb f A n (n ^ c) < 1 / (n : ℚ) ^ k

end Levin2003


